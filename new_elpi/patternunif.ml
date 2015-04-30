(* GC off
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.space_overhead = max_int;
  } in
  Gc.set tweaked_control
;;
*)

type constant = int (* De Brujin levels *)

(* Invariant: a Heap term never points to a Query term *)
type term =
  (* Pure terms *)
  | Const of constant
  (* Clause terms *)
  | Struct of constant * term * term list
  | Arg of int * constant list
  | CLam of term
  (* Heap terms *)
  | App of constant * term * term list
  | UVar of term ref * constant list
  | Lam of term

let rec dummy = App (-9999,dummy,[])

module F = Parser.ASTFuncS
module AST = Parser

(* Hash re-consing :-( *)
let funct_of_ast, constant_of_dbl, string_of_constant =
 let h = Hashtbl.create 37 in
 let h' = Hashtbl.create 37 in
 let h'' = Hashtbl.create 17 in
 let fresh = ref 0 in
 (function x ->
  try Hashtbl.find h x
  with Not_found ->
   decr fresh;
   let n = !fresh in
   let xx = Const n in
   let p = n,xx in
   Hashtbl.add h' n (F.pp x);
   Hashtbl.add h x p; p),
 (function x ->
  try Hashtbl.find h'' x
  with Not_found ->
   let xx = Const x in
   Hashtbl.add h' x (string_of_int x);
   Hashtbl.add h'' x xx; xx),
 Hashtbl.find h'

let ppterm f t =
  let rec ppapp hd a c1 c2 = 
    Format.fprintf f "%c@[<hov 1>" c1;
    ppconstant hd;
    Format.fprintf f "@ ";
    List.iter (fun x -> aux x; Format.fprintf f "@ ") a;
    Format.fprintf f "@]%c" c2
  and ppconstant c = Format.fprintf f "%s" (string_of_constant c)
  and aux = function
      t when t == dummy -> Format.fprintf f "dummy"
    | App (hd,x,xs)-> ppapp hd (x::xs) '(' ')'
    | Struct (hd,x,xs) -> ppapp hd (x::xs) '{' '}'
    | UVar ({ contents = t },args) ->
       Format.fprintf f "(<@[<hov 1>";
       aux t;
       Format.fprintf f ">";
       List.iter (fun x -> ppconstant x; Format.fprintf f "@ ") args;
       Format.fprintf f "@])"
    | Const s -> ppconstant s
    | Arg (i,args) ->
       Format.fprintf f "{@[<hov 1>";
       Format.fprintf f "A%d" i;
       List.iter (fun x -> ppconstant x; Format.fprintf f "@ ") args;
       Format.fprintf f "@]}"
    | Lam t ->
       Format.fprintf f "\\(";
       aux t;
       Format.fprintf f ")";
    | CLam t ->
       Format.fprintf f "\\[";
       aux t;
       Format.fprintf f "]";
  in
    aux t
;;

type key1 = int
type key2 = int
type key = key1 * key2

type clause = { hd : term; hyps : term list; vars : int; key : key }

(******* Reduction & friends ********)

let deref args t =
 match args with
    [] -> t
  | _ -> assert false (* TODO: delta-beta *)

(****** Indexing ******)

let variablek =    -99999999
let abstractionk = -99999998

let rec skey_of = function
   Const k -> k
 | UVar ({contents=t},args) when t != dummy -> skey_of (deref args t)
 | Struct (k,_,_)
 | App (k,_,_) -> k
 | Lam _ | CLam _ -> abstractionk
 | Arg _ | UVar _ -> variablek

let rec key_of = function
   Const k -> k, variablek
 | UVar ({contents=t},args) when t != dummy -> key_of (deref args t)
 | App (k,arg2,_)
 | Struct (k,arg2,_) -> k, skey_of arg2
 | Arg _ | Lam _ | CLam _ | UVar _ -> raise (Failure "Not a predicate")

let clause_match_key j k =
  (j == variablek || k == variablek || j == k)

module IndexData =
 struct
  (* Note: we tried (c79d0e3007f66eb553b6d50338faca1e09d8d064) replacing
     string with string*int in Const to index only the (unique) integer and
     speed up comparison w.r.t. String.compare. But it seems that always
     projecting out the integer from the pair during indexing for clause
     retrieval makes the example program slower. *)
  type t = key1
  let equal = (==)
  let compare = compare
end
module ClauseMap = Map.Make(IndexData)

let get_clauses a m =
 let ind,app = key_of a in
 let l = List.rev (ClauseMap.find ind m) in
 let rec filter_map =
  function
     [] -> []
   | (a',cl)::tl when clause_match_key app a' ->
       cl::filter_map tl
   | _::tl -> filter_map tl in
 filter_map l
   
let add_clauses clauses p =       
  List.fold_left (fun m clause -> 
    let ind,app = clause.key in
    try 
      let l = ClauseMap.find ind m in
      ClauseMap.add ind ((app,clause) :: l) m
    with Not_found -> 
      ClauseMap.add ind [app,clause] m
    ) p clauses

let make p = add_clauses p ClauseMap.empty

(****** End of Indexing ******)

(* The environment of a clause and stack frame *)

let to_heap e t =
  let rec aux = function
    | UVar ({contents = t},args) when t != dummy -> aux (deref args t)
    | (Const _ | UVar _ | App _ | Lam _) as x -> x (* heap term *)
    | Struct(hd,b,bs) -> App (hd, aux b, List.map aux bs)
    | CLam t -> Lam (aux t)
    | Arg (i,args) ->
        let a = e.(i) in
        if a == dummy then
            let r = ref dummy in
            let v = UVar(r,[]) in
            e.(i) <- v;
            UVar(r,args)
        else aux a
  in aux t
;;

(* Unification *)

(* This for_all2 is tail recursive when the two lists have length 1.
   It also raises no exception. *)
let rec for_all2 p l1 l2 =
  match (l1, l2) with
    ([], []) -> true
  | ([a1], [a2]) -> p a1 a2
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> false

(* Invariant: LSH is a heap term, the RHS is a query in env e *)
let unif trail last_call a e b =
 let rec unif a b =
   Format.eprintf "unif %b: %a = %a\n%!" last_call ppterm a ppterm b;
   a == b || match a,b with
(* TODO OOOOOOOOOOOOOOOOOOOOOOOOOOO *)
   | _, Arg (i,[]) when e.(i) != dummy -> unif a e.(i)
   | UVar ({ contents = t },[]), _ when t != dummy -> unif t b
   | _, UVar ({ contents = t },[]) when t != dummy -> unif a t
   | UVar _, Arg (j,[]) -> e.(j) <- a; true
   | t, Arg (i,[]) -> e.(i) <- t; true
   | UVar (r,[]), t ->
       if not last_call then trail := r :: !trail;
       r := to_heap e t;
       true
   | t, UVar (r,[]) ->
       if not last_call then trail := r :: !trail;
       r := t;
       true
   | UVar (_,_),_ | _, UVar (_,_) | _, Arg (_,_) -> assert false
   | App (x1,x2,xs), (Struct (y1,y2,ys) | App (y1,y2,ys)) ->
       x1 == y1 && (x2 == y2 || unif x2 y2) && for_all2 unif xs ys
   | Lam t1, (Lam t2 | CLam t2) -> unif t1 t2
   | _ -> false in
 unif a b
;;

(* Enrico's partially tail recursive but slow unification.
   The tail recursive version is even slower.
(* Invariant: LSH is a heap term, the RHS is a query in env e *)
let unif trail last_call a e b =
  let rec next l1 l2 =
    match l1,l2 with
    | [],[] -> true
    | [] :: xs, [] :: ys -> next xs ys
    | (x :: xs) :: l1, (y :: ys) :: l2 -> unif x y (xs :: l1) (ys :: l2)
    | _ -> false
 and unif a b todo1 todo2 =
   (* Format.eprintf "unif %b: %a = %a\n%!" last_call ppterm a ppterm b; *)
   if a == b then next todo1 todo2
   else match a,b with
   | _, Arg i when e.(i) != dummy -> unif a e.(i) todo1 todo2
   | UVar { contents = t }, _ when t != dummy -> unif t b todo1 todo2
   | _, UVar { contents = t } when t != dummy -> unif a t todo1 todo2
   | UVar _, Arg j -> e.(j) <- a; next todo1 todo2
   | t, Arg i -> e.(i) <- t; next todo1 todo2
   | UVar r, t ->
       if not last_call then trail := r :: !trail;
       r := to_heap e t;
       next todo1 todo2
   | t, UVar r ->
       if not last_call then trail := r :: !trail;
       r := t;
       next todo1 todo2
   | App (x1,x2,xs), (Struct (y1,y2,ys) | App (y1,y2,ys)) ->
       (x1 == y1 || unif x1 y1 [] []) &&
       (x2 == y2 || unif x2 y2 [] []) &&
       next (xs :: todo1) (ys :: todo2)
         
   | _ -> false in
 unif a b [] []
;;*)

(* Backtracking *)

let undo_trail old_trail trail =
  while !trail != old_trail do
    match !trail with
    | r :: rest -> r := dummy; trail := rest
    | _ -> assert false
  done
;;

(* Loop *)
type program = (key1 * clause) list ClauseMap.t
(* The activation frames point to the choice point that
   cut should backtrack to, i.e. the first one not to be
   removed. For bad reasons, we call it lvl in the code. *)
type frame =
 | FNil
 | FCons of (*lvl:*)alternative * (program * term) list * frame
and alternative = {
  lvl : alternative;
  program : program;
  goal : term;
  goals : (program * term) list;
  stack : frame;
  trail : term ref list;
  clauses : clause list;
  next : alternative
}

let emptyalts = Obj.magic 0

let cutc = snd (funct_of_ast F.cutf)
let truec = snd (funct_of_ast F.truef)
let andc = fst (funct_of_ast F.andf)
let implc = fst (funct_of_ast F.implf)

let rec chop =
 function
    Struct(c,hd2,tl) when c == andc ->
     chop hd2 @ List.flatten (List.map chop tl)
  | f when f==truec -> []
  | _ as f -> [ f ]

let rec clausify =
 function
    App(c, g, gs) when c == andc ->
     clausify g @ List.flatten (List.map clausify gs)
  | App(c, g1, [g2]) when c == implc ->
     [ { hd=g2 ; hyps=chop g1 ; vars=0 ; key = key_of g2 } ]
  | UVar ({ contents=g },_) when g == dummy ->
     raise (Failure "Not a predicate in clausify")
  | UVar ({ contents=g },args) -> clausify (deref args g)
  | g -> [ { hd=g ; hyps=[] ; vars=0 ; key = key_of g } ]
;;

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : ('a -> 'b -> 'k) * ('k -> 'k) =
  let trail = ref [] in

  (* Input to be read as the orl (((p,g)::gs)::next)::alts *)
  let rec run p g gs (next : frame) alts lvl =
    (*Format.eprintf "goal: %a\n%!" ppterm g; *)
    (*Format.eprintf "<";
    List.iter (Format.eprintf "goal: %a\n%!" ppterm) stack.goals;
    Format.eprintf ">";*)
    match g with
    | c when c == cutc ->
         (* We filter out from the or list until we find the
            last frame not to be removed (called lvl). *)
         let alts =
          let rec prune alts =
           if alts == lvl then alts
           else prune alts.next
          in
           prune alts in
         if alts==emptyalts then trail := [] ;
         (match gs with
             [] -> pop_andl alts next
           | (p,g)::gs -> run p g gs next alts lvl)
    | App(c, g, gs') when c == andc ->
       run p g (List.map(fun x -> p,x) gs'@gs) next alts lvl
    (* We do not check the case of implication applied to
       multiple arguments *)
    | App(c, g1, [g2]) when c == implc ->
       let clauses = clausify g1 in
       run (add_clauses clauses p) g2 gs next alts lvl
    | UVar ({ contents=g },_) when g == dummy ->
       raise (Failure "Not a predicate")
    | UVar ({ contents=g },args) -> run p (deref args g) gs next alts lvl
    | Lam _ -> raise (Failure "Not a predicate")
    | Const _ | App _ -> (* Atom case *)
        let cp = get_clauses g p in
        backchain p g gs cp next alts lvl
    | CLam _ | Struct _ | Arg _ -> assert false (* Not an heap term *)

  and backchain p g gs cp next alts lvl =
    (*Format.eprintf "BACKCHAIN %a @ %d\n%!" ppterm g lvl;
List.iter (fun (_,g) -> Format.eprintf "GS %a\n%!" ppterm g) gs;*)
    let last_call = alts == emptyalts in
    let rec select = function
    | [] -> next_alt alts
    | c :: cs ->
        let old_trail = !trail in
        let last_call = last_call && cs = [] in
        let env = Array.create c.vars dummy in
        match unif trail last_call g env c.hd with
        | false -> undo_trail old_trail trail; select cs
        | true ->
(* TODO: make to_heap lazy adding the env to unify and making the env
   survive longer. It may be slower or faster, who knows *)
            let oldalts = alts in
            let alts =
             if cs = [] then alts
             else
              { program=p; goal=g; goals=gs; stack=next;
                trail=old_trail; clauses=cs; lvl=lvl ;
                next=alts} in
            (match c.hyps with
               [] ->
                (match gs with
                    [] -> pop_andl alts next
                  | (p,g)::gs -> run p g gs next alts lvl)
             | g'::gs' ->
                let next =
                 if gs = [] then next
                 else FCons (lvl,gs,next) in
                let g' = to_heap env g' in
                let gs'=List.map (fun x->p,to_heap env x) gs' in
                run p g' gs' next alts oldalts)
    in
      select cp

  and pop_andl alts =
   function
      FNil -> alts
    | FCons (_,[],_) -> assert false
    | FCons(lvl,(p,g)::gs,next) -> run p g gs next alts lvl

  and next_alt alts =
   if alts == emptyalts then raise (Failure "no clause")
   else begin
    let { program = p; goal = g; goals = gs; stack=next;
          trail = old_trail; clauses; lvl ; next=alts} = alts in
    undo_trail old_trail trail;
    backchain p g gs clauses next alts lvl
   end
  in
   (fun p q -> run p q [] FNil emptyalts emptyalts), next_alt
;;
  
let heap_var_of_ast l n =
 try l,List.assoc n l
 with Not_found ->
  let n' = UVar (ref dummy,[]) in
  (n,n')::l,n'

let rec heap_term_of_ast lvl l l' =
 function
    AST.Var v -> let l,v = heap_var_of_ast l v in l,l',v
  | AST.App(AST.Const f,[]) when F.eq f F.andf ->
     l,l',truec
  | AST.Const f ->
     (try l,l',List.assoc f l'
      with Not_found -> l,l',snd (funct_of_ast f))
  | AST.App(AST.Const f,tl) ->
     let l,l',rev_tl =
       List.fold_left
        (fun (l,l',tl) t ->
          let l,l',t = heap_term_of_ast lvl l l' t in (l,l',t::tl))
        (l,l',[]) tl in
     let f = fst (funct_of_ast f) in
     (match List.rev rev_tl with
         hd2::tl -> l,l',App(f,hd2,tl)
       | _ -> assert false)
  | AST.Lam (x,t) ->
     let c = constant_of_dbl lvl in
     let l,l',t' = heap_term_of_ast (lvl+1) l ((x,c)::l') t in
     l,l',Lam t'
  | AST.App (AST.Var _,_) -> assert false  (* TODO *)
  | AST.App (AST.App (f,l1),l2) ->
     heap_term_of_ast lvl l l' (AST.App (f, l1@l2))
  | AST.App (AST.Lam _,_) ->
     (* Beta-redexes not in our language *) assert false

let stack_var_of_ast (f,l) n =
 try (f,l),List.assoc n l
 with Not_found ->
  let n' = Arg (f,[]) in
  (f+1,(n,n')::l),n'

let rec stack_term_of_ast lvl l l' =
 function
    AST.Var v ->
     let l,v = stack_var_of_ast l v in
     l,l',v
  | AST.App(AST.Const f,[]) when F.eq f F.andf ->
     l,l',truec
  | AST.Const f ->
     (try l,l',List.assoc f l'
      with Not_found -> l,l',snd (funct_of_ast f))
  | AST.App(AST.Const f,tl) ->
     let l,l',rev_tl =
       List.fold_left
        (fun (l,l',tl) t ->
          let l,l',t = stack_term_of_ast lvl l l' t in (l,l',t::tl))
        (l,l',[]) tl in
     let f = fst (funct_of_ast f) in
     (match List.rev rev_tl with
         hd2::tl -> l,l',Struct(f,hd2,tl)
       | _ -> assert false)
  | AST.Lam (x,t) ->
     let c = constant_of_dbl lvl in
     let l,l',t' = stack_term_of_ast (lvl+1) l ((x,c)::l') t in
     l,l',CLam t'
  | AST.App (AST.Var _,_) -> assert false  (* TODO *)
  | AST.App (AST.App (f,l1),l2) -> stack_term_of_ast lvl l l' (AST.App (f, l1@l2))
  | AST.App (AST.Lam _,_) ->
     (* Beta-redexes not in our language *) assert false

let query_of_ast t = let _,_,t = heap_term_of_ast 0 [] [] t in t

let program_of_ast p =
 let clauses =
  List.map (fun (a,f) ->
   let l,_,a = stack_term_of_ast 0 (0,[]) [] a in
   let (max,_),_,f = stack_term_of_ast 0 l [] f in
Format.eprintf "%a :- " ppterm a;
List.iter (Format.eprintf "%a, " ppterm) (chop f);
Format.eprintf ".\n%!";
   { hd = a
   ; hyps = chop f
   ; vars = max
   ; key = key_of a
   }) p
 in
  make clauses

let impl =
 (module struct
  (* RUN with non indexed engine *)
  type query = term
  type program_ = program
  type program = program_
  let query_of_ast = query_of_ast
  let program_of_ast = program_of_ast

  let msg q =
   Format.fprintf Format.str_formatter "Pattern unification only: %a" ppterm q ;
   Format.flush_str_formatter ()

  let execute_once p q =
   let run, cont = make_runtime in
   try ignore (run p q) ; true
   with Failure _ -> false

  let execute_loop p q =
   let run, cont = make_runtime in
   let time0 = Unix.gettimeofday() in
   let k = ref (run p q) in
   let time1 = Unix.gettimeofday() in
   prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
   Format.eprintf "Result: %a\n%!" ppterm q ;
   while !k != emptyalts do
     let time0 = Unix.gettimeofday() in
     k := cont !k;
     let time1 = Unix.gettimeofday() in
     prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
     Format.eprintf "Result: %a\n%!" ppterm q ;
  done
 end : Parser.Implementation)
