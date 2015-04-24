(* GC off
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.space_overhead = max_int;
  } in
  Gc.set tweaked_control
;;
*)

(* Invariant: a Heap term never points to a Query term *)
type term =
  (* Pure terms *)
  | Const of string
  (* Query terms *)
  | Struct of term * term * term list
  | Arg of int
  (* Heap terms *)
  | App of term * term * term list
  | UVar of term ref

let rec dummy = App (dummy,dummy,[])

let ppterm f t =
  let rec ppapp a c1 c2 = 
    Format.fprintf f "%c@[<hov 1>" c1;
    List.iter (fun x -> aux x; Format.fprintf f "@ ") a;
    Format.fprintf f "@]%c" c2
  and aux = function
      t when t == dummy -> Format.fprintf f "dummy"
    | App (hd,x,xs)-> ppapp (hd::x::xs) '(' ')'
    | Struct (hd,x,xs) -> ppapp (hd::x::xs) '{' '}'
    | UVar { contents = t } -> ppapp [t] '<' '>'
    | Const s -> Format.fprintf f "%s" s
    | Arg i -> Format.fprintf f "A%d" i
  in
    aux t
;;

type key = string * string

type clause = { hd : term; hyps : term list; vars : int; key : key }

let dummyk = "dummy"

let rec skey_of = function
   Const k -> k
 | UVar {contents=t} when t != dummy -> skey_of t
 | Struct (arg1,_,_)
 | App (arg1,_,_) -> skey_of arg1
 | _ -> dummyk

let rec key_of = function
   Const k -> k, dummyk
 | UVar {contents=t} when t != dummy -> key_of t
 | App (arg1,arg2,_)
 | Struct (arg1,arg2,_) -> skey_of arg1, skey_of arg2
 | _ -> dummyk,dummyk

let clause_match_key (j1,j2) { key = (k1,k2) } =
  j1 == dummyk || k1 == dummyk ||
  (j1 == k1 && (j2 == dummyk || k2 == dummyk || j2 == k2))

(* The environment of a clause and stack frame *)

let to_heap e t =
  let rec aux = function
    | UVar {contents = t} when t != dummy -> aux t
    | (Const _ | UVar _ | App _) as x -> x (* heap term *)
    | Struct(hd,b,bs) -> App (aux hd, aux b, List.map aux bs)
    | Arg i ->
        let a = e.(i) in
        if a == dummy then
            let v = UVar(ref dummy) in
            e.(i) <- v;
            v
        else aux a
  in aux t
;;

(* Unification *)

(* Invariant: LSH is a heap term, the RHS is a query in env e *)
let unif trail last_call a e b =
 let rec unif a b =
    (* Format.eprintf "unif %b: %a = %a\n%!" last_call ppterm a ppterm b; *)
   a == b || match a,b with
   | _, Arg i when e.(i) != dummy -> unif a e.(i)
   | UVar { contents = t }, _ when t != dummy -> unif t b
   | _, UVar { contents = t } when t != dummy -> unif a t
   | UVar _, Arg j -> e.(j) <- a; true
   | t, Arg i -> e.(i) <- t; true
   | UVar r, t ->
       if not last_call then trail := r :: !trail;
       r := to_heap e t;
       true
   | t, UVar r ->
       if not last_call then trail := r :: !trail;
       r := t;
       true
   | App (x1,x2,xs), (Struct (y1,y2,ys) | App (y1,y2,ys)) ->
       (x1 == y1 || unif x1 y1) && (x2 == y2 || unif x2 y2) &&
       List.for_all2 unif xs ys
   | _ -> false in
 unif a b
;;

(* Backtracking *)

let undo_trail old_trail trail =
  while !trail != old_trail do
    match !trail with
    | r :: rest -> r := dummy; trail := rest
    | _ -> assert false
  done
;;

(* Loop *)
type program = clause list
type frame = (program * term) list list
type alternative = { lvl : int;
  program : program;
  goal : term;
  goals : (program * term) list;
  stack : frame;
  trail : term ref list;
  clauses : clause list
}

let truef = Const (Lprun2.ASTFuncS.pp Lprun2.ASTFuncS.truef)
let andf = Const (Lprun2.ASTFuncS.pp Lprun2.ASTFuncS.andf)
let implf = Const (Lprun2.ASTFuncS.pp Lprun2.ASTFuncS.implf)

let rec chop =
 function
    Struct(Const f,hd2,tl) when
     Lprun2.ASTFuncS.eq (Lprun2.ASTFuncS.from_string f) Lprun2.ASTFuncS.andf
     -> chop hd2 @ List.flatten (List.map chop tl)
  | f when f == truef -> []
  | f -> [ f ]

let rec clausify =
 function
    App(c, g, gs) when c == andf ->
     clausify g @ List.flatten (List.map clausify gs)
  | App(c, g1, [g2]) when c == implf ->
     [ { hd=g2 ; hyps=chop g1 ; vars=0 ; key = key_of g2 } ]
  | UVar { contents=g } when g == dummy ->
     assert false (* Flexible axiom, we give up *)
  | UVar { contents=g } -> clausify g
  | g -> [ { hd=g ; hyps=[] ; vars=0 ; key = key_of g } ]
;;

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : ('a -> 'b -> 'k) * ('k -> 'k) =
  let trail = ref [] in

  let rec run p g gs (next : frame) alts lvl =
    (*Format.eprintf "<";
    List.iter (Format.eprintf "goal: %a\n%!" ppterm) stack.goals;
    Format.eprintf ">";*)
    match g with
    | App(c, g, gs') when c == andf ->
       run p g (List.map(fun x -> p,x) gs'@gs) next alts lvl
    (* We do not check the case of implication applied to
       multiple arguments *)
    | App(c, g1, [g2]) when c == implf ->
       let clauses = clausify g1 in
       run (clauses@p) g2 gs next alts lvl
    | UVar { contents=g } when g == dummy ->
       assert false (* Flexible goal, we give up *)
    | UVar { contents=g } ->
       run p g gs next alts lvl
    | _ -> (* Atom case *)
        let cp =
         List.filter (clause_match_key (key_of g)) p in
        backchain p g gs cp next alts lvl

  and backchain p g gs cp next alts lvl =
    (*Format.eprintf "BACKCHAIN %a\n%!" ppterm g;*)
    let last_call = alts = [] in
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
            let alts = if cs = [] then alts else
              { program=p; goal=g; goals=gs; stack=next; trail=old_trail; clauses=cs; lvl=lvl } :: alts in
            let next = if gs = [] then next else gs::next in
            match c.hyps with
               [] -> pop_andl alts (lvl-1) next
             | g::gs ->
                let g = to_heap env g in
                let gs=List.map (fun x -> p,to_heap env x) gs in
                run p g gs next alts lvl
    in
      select cp

  and pop_andl alts lvl =
   function
      [] -> alts
    | []::_next -> assert false (* run next alts (lvl - 1) *)
    | ((p,g)::gs)::next -> run p g gs next alts lvl

  and next_alt = function
    | [] -> raise (Failure "no clause")
    | { program = p; goal = g; goals = gs; stack=next; trail = old_trail; clauses; lvl } :: alts ->
        undo_trail old_trail trail;
        backchain p g gs clauses next alts lvl
  in
   (fun p q -> run p q [] [] [] 0), next_alt
;;
  
(* Hash re-consing :-( *)
let funct_of_ast =
 let h = Hashtbl.create 37 in
 function x ->
  try Hashtbl.find h x
  with Not_found ->
   let xx = Const (Lprun2.ASTFuncS.pp x) in
   Hashtbl.add h x xx ; xx

let heap_var_of_ast l n =
 try l,List.assoc n l
 with Not_found ->
  let n' = UVar (ref dummy) in
  (n,n')::l,n'

let rec heap_term_of_ast l =
 function
    Lprun2.FOAST.Var v ->
     let l,v = heap_var_of_ast l v in
     l, v
  | Lprun2.FOAST.App(f,[]) when Lprun2.ASTFuncS.eq f Lprun2.ASTFuncS.andf ->
     l, truef
  | Lprun2.FOAST.App(f,[]) ->
     l, funct_of_ast f
  | Lprun2.FOAST.App(f,tl) ->
     let l,rev_tl =
       List.fold_left
        (fun (l,tl) t -> let l,t = heap_term_of_ast l t in (l,t::tl))
        (l,[]) tl in
     match funct_of_ast f :: List.rev rev_tl with
        hd1::hd2::tl -> l, App(hd1,hd2,tl)
      | _ -> assert false

let stack_var_of_ast (f,l) n =
 try (f,l),List.assoc n l
 with Not_found ->
  let n' = Arg f in
  (f+1,(n,n')::l),n'

let rec stack_term_of_ast l =
 function
    Lprun2.FOAST.Var v ->
     let l,v = stack_var_of_ast l v in
     l, v
  | Lprun2.FOAST.App(f,[]) when Lprun2.ASTFuncS.eq f Lprun2.ASTFuncS.andf ->
     l, truef
  | Lprun2.FOAST.App(f,[]) ->
     l, funct_of_ast f
  | Lprun2.FOAST.App(f,tl) ->
     let l,rev_tl =
       List.fold_left
        (fun (l,tl) t -> let l,t = stack_term_of_ast l t in (l,t::tl))
        (l,[]) tl in
     match funct_of_ast f :: List.rev rev_tl with
        hd1::hd2::tl -> l, Struct(hd1,hd2,tl)
      | _ -> assert false

let query_of_ast t = snd (heap_term_of_ast [] t)

let program_of_ast p =
 List.map (fun (a,f) ->
  let l,a = stack_term_of_ast (0,[]) a in
  let (max,_),f = stack_term_of_ast l f in
Format.eprintf "%a :- " ppterm a;
List.iter (Format.eprintf "%a, " ppterm) (chop f);
Format.eprintf ".\n%!";
  { hd = a
  ; hyps = chop f
  ; vars = max
  ; key = key_of a
  }) p

let impl =
 (module struct
  (* RUN with non indexed engine *)
  type query = term
  type program = clause list
  let query_of_ast = query_of_ast
  let program_of_ast = program_of_ast

  let msg q =
   Format.fprintf Format.str_formatter "Desperate HO + Impl: %a" ppterm q ;
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
   while !k <> [] do
     let time0 = Unix.gettimeofday() in
     k := cont !k;
     let time1 = Unix.gettimeofday() in
     prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
     Format.eprintf "Result: %a\n%!" ppterm q ;
  done
 end : Lprun2.Implementation)
