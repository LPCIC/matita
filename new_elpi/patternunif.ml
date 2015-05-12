(* GC off
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.space_overhead = max_int;
  } in
  Gc.set tweaked_control
;;
*)

let rec smart_map f =
 function
    [] -> []
  | (hd::tl) as l ->
     let hd' = f hd in
     let tl' = smart_map f tl in
     if hd==hd' && tl==tl' then l else hd'::tl'

(* TODOS:
   - Do the TODO: optimization for indexing
   - There are a few TODOs with different implementative choices to
     be benchmarked *)

type constant = int (* De Brujin levels *)

(* Invariant: a Heap term never points to a Query term *)
type term =
  (* Pure terms *)
  | Const of constant
  (* Clause terms *)
  | Arg of int * constant list
  (* Heap terms *)
  | App of constant * term * term list
  | UVar of term ref * (*depth:*)int * constant list
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
 (function n ->
   try Hashtbl.find h' n
   with Not_found -> string_of_int n)

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
    | UVar ({ contents = t },depth,args) ->
       Format.fprintf f "(<@[<hov 1>";
       aux t;
       Format.fprintf f ">_%d " depth;
       List.iter (fun x -> ppconstant x; Format.fprintf f "@ ") args;
       Format.fprintf f "@])"
    | Const s -> ppconstant s
    | Arg (i,args) ->
       Format.fprintf f "{@[<hov 1>";
       Format.fprintf f "A%d " i;
       List.iter (fun x -> ppconstant x; Format.fprintf f "@ ") args;
       Format.fprintf f "@]}"
    | Lam t ->
       Format.fprintf f "\\(";
       aux t;
       Format.fprintf f ")";
  in
    aux t
;;

type key1 = int
type key2 = int
type key = key1 * key2

type clause =
 { depth : int; hd : term; hyps : term list; vars : int; key : key }

(************************* to_heap/restrict/deref ******************)

exception RestrictionFailure

(* eat_args n [n ; ... ; n+k] (Lam_0 ... (Lam_k t)...) = n+k+1,[],t
   eat_args n [n ; ... ; n+k]@l (Lam_0 ... (Lam_k t)...) =
     n+k+1,l,t if t != Lam or List.hd l != n+k+1 *)
let rec eat_args from l t =
 match l,t with
    hd::tl,Lam t' when hd=from -> eat_args (from+1) tl t'
  | _,_ -> from,l,t

(* To_heap performs at once:
   1) refreshing of the arguments into variables (heapifycation)
      (and Structs/CLam into App/Lam)
   2) restriction (see restrict function below)

   when from = to, i.e. delta = 0:
     (-infty,+infty) -> (-infty,+infty)
   when from < to, i.e. delta < 0:
     (-infty,from) -> (-infty,from)   free variables
     [from,+infty) -> [to,+infty)     bound variables
   when from > to, i.e. delta > 0:
     (-infty,to)   -> (-infty,to)     free variables
     [to,from)     -> error           free restricted variables
     [from,+infty) -> [to,+infty)     bound variables *)
(* when from=to, to_heap is to be called only for terms that are not in the heap*)
let rec to_heap argsdepth last_call trail ~from ~to_ e t =
  let delta = from - to_ in
  let rec aux depth x =
   match x with
      Const c ->
        if delta=0 then x else (* optimization *)
        if c >= from then constant_of_dbl (c - delta)
        else if c < to_ then x
        else raise RestrictionFailure
    | Lam f ->
       let f' = aux (depth+1) f in
       if f==f' then x else Lam f'
    | App (c,t,l) when delta=0 || c < from && c < to_ ->
       let t' = aux depth t in
       let l' = smart_map (aux depth) l in
       if t==t' && l==l' then x else App (c,t',l')
    | App (c,t,l) when c >= from ->
       App(c-delta,aux depth t,smart_map (aux depth) l)
    | App _ -> raise RestrictionFailure
    | UVar _ when delta=0 -> x
    | UVar ({contents=t},depth,args) when t != dummy ->
       full_deref argsdepth last_call trail ~from:depth ~to_:(to_+depth)
        args e t
    | UVar (r,depth,[]) when delta > 0 ->
       let fresh = UVar(ref dummy,to_,[]) in
       if not last_call then trail := r :: !trail;
       r := fresh;
       (* TODO: test if it is more efficient here to return fresh or
          the original, imperatively changed, term. The current solution
          avoids dereference chains, but puts more pressure on the GC. *)
       fresh
    | UVar (_,_,_) when delta < 0 -> x
    | UVar (_,depth,_) -> assert false (* TO BE IMPLEMENTED *)
    | Arg (i,args) when argsdepth >= to_ ->
        let args =
         smart_map (fun c ->
          if c >= from then (c - delta)
          else if c < to_ then c
          else raise RestrictionFailure
         ) args in
        let a = e.(i) in
        if a == dummy then
            let r = ref dummy in
            let v = UVar(r,to_,[]) in
            e.(i) <- v;
            UVar(r,to_,args)
        else
         full_deref argsdepth last_call trail ~from:argsdepth
          ~to_:(to_+depth) args e a
    | Arg _ -> assert false (* I believe this case to be impossible *)
  in aux 0 t

(* full_deref is to be called only on heap terms and with from <= to *)
and full_deref argsdepth last_call trail ~from ~to_ args e t =
 (* TODO: Remove the assertion when we are sure *)
 assert (from <= to_);
 if args = [] then
  if from=to_ then t
  else to_heap argsdepth last_call trail ~from ~to_ e t
 else (* O(1) reduction fragment tested here *)
begin
  (*Format.eprintf "betaXX ^%d:%a\n%!" from ppterm t;
  List.iter (Format.eprintf "betaArg: %d\n%!") args;*)
  match eat_args from args t with
     from,[],t -> full_deref argsdepth last_call trail ~from ~to_ [] e t
   | _,_,Lam _ -> assert false (* TODO: Implement beta-reduction here *)
   | _,_,_ -> assert false (* TODO: not a beta-redex *)
end
;;

(* Restrict is to be called only on heap terms *)
let restrict argsdepth last_call trail ~from ~to_ e t =
 if from=to_ then t
 else to_heap argsdepth last_call trail ~from ~to_ e t

(* Deref is to be called only on heap terms and with from <= to *)
let deref ~from ~to_ args t =
 (* TODO: Remove the assertion when we are sure *)
 assert (from <= to_);
 (* Dummy trail, argsdepth and e: they won't be used *)
 full_deref 0 false (ref []) ~from ~to_ args [||] t
;;


(****** Indexing ******)

let variablek =    -99999999
let abstractionk = -99999998

let key_of depth =
 let rec skey_of = function
    Const k -> k
  | UVar ({contents=t},origdepth,args) when t != dummy ->
     skey_of (deref ~from:origdepth ~to_:depth args t)
  | App (k,_,_) -> k
  | Lam _ -> abstractionk
  | Arg _ | UVar _ -> variablek in
 let rec key_of_depth = function
   Const k -> k, variablek
 | UVar ({contents=t},origdepth,args) when t != dummy ->
    (* TODO: optimization: avoid dereferencing *)
    key_of_depth (deref ~from:origdepth ~to_:depth args t)
 | App (k,arg2,_) -> k, skey_of arg2
 | Arg _ | Lam _ | UVar _ -> raise (Failure "Not a predicate")
 in
  key_of_depth

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
  let compare (x:int) (y:int) = y - x
end
module ClauseMap = Map.Make(IndexData)

let get_clauses depth a m =
 let ind,app = key_of depth a in
 try
  let l = List.rev (ClauseMap.find ind m) in
  let rec filter_map =
   function
      [] -> []
    | (a',cl)::tl when clause_match_key app a' ->
        cl::filter_map tl
    | _::tl -> filter_map tl in
  filter_map l
 with Not_found -> []
   
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

(* Unification *)

(* This for_all2 is tail recursive when the two lists have length 1.
   It also raises no exception. *)
let rec for_all2 p l1 l2 =
  match (l1, l2) with
    ([], []) -> true
  | ([a1], [a2]) -> p a1 a2
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> false

(* Invariants:
   adepth is the depth of a (the query), which is an heap term
   bdepth is the depth of b (the clause hd), which is a stack term in env e
   adepth >= bdepth

   Let cdepth = min{adepth,bdepth}
   (-infy,cdepth) = (-infty,cdepth)   common free variables
   [cdepth,adepth)                    free variable only visible by one:fail
                     [cdepth,bdepth)  free variable only visible by one:fail
   [adepth,+infty) = [bdepth,+infy)   bound variables *)
let unif trail last_call adepth a e bdepth b =
 let rec unif depth a bdepth b heap =
   (*Format.eprintf "unif %b: ^%d:%a =%d= ^%d:%a\n%!" last_call adepth ppterm a depth bdepth ppterm b;*)
   let cdepth = if adepth < bdepth then adepth else bdepth (*min adepth bdepth*) in
   let delta = adepth - bdepth in
   (delta=0 && a == b) || match a,b with
   | _, Arg (i,[]) when e.(i) == dummy ->
     e.(i) <-
      restrict adepth last_call trail ~from:(adepth+depth) ~to_:adepth e a;
     (*Format.eprintf "<- %a\n%!" ppterm e.(i);*)
     true
   | UVar (r,origdepth,[]), _ when !r == dummy ->
       if not last_call then trail := r :: !trail;
       (* TODO: are exceptions efficient here? *)
       (try r :=
         if heap && depth=0 then b else
          to_heap adepth last_call trail ~from:(bdepth+depth)
           ~to_:origdepth e b;
         true
        with RestrictionFailure -> false)
   | _, UVar (r,origdepth,[]) when !r == dummy ->
       if not last_call then trail := r :: !trail;
       (* TODO: are exceptions efficient here? *)
       (try r :=
         restrict adepth last_call trail ~from:(adepth+depth)
          ~to_:origdepth e a;
         true
        with RestrictionFailure -> false)
   | _, Arg (i,args) ->
      unif depth a adepth (deref ~from:adepth ~to_:(adepth+depth) args e.(i))
       true
   | _, UVar ({ contents = t },origdepth,args) ->
      unif depth a bdepth (deref ~from:origdepth ~to_:(bdepth+depth) args t)
       true
   | UVar ({ contents = t },origdepth,args), _ ->
      unif depth (deref ~from:origdepth ~to_:(adepth+depth) args t) bdepth b
       true
   | App (c1,x2,xs), App (c2,y2,ys) ->
      (* Compressed cut&past from Const vs Const case below +
         delta=0 optimization for <c1,c2> and <x2,y2> *)
      ((delta=0 || c1 < cdepth) && c1=c2
       || c1 >= adepth && c2 >= bdepth && c1 = c2 + delta)
       &&
       (delta=0 && x2 == y2 || unif depth x2 bdepth y2 heap) &&
       for_all2 (fun x y -> unif depth x bdepth y heap) xs ys
   | Lam t1, Lam t2 -> unif (depth+1) t1 bdepth t2 heap
   | Const c1, Const c2 when c1=c2 && c1 < cdepth -> true
   | Const c, _ when c >= cdepth && c < adepth -> false
   | _,Const c  when c >= cdepth && c < bdepth -> false
   | Const c1, Const c2 when c1 = c2 + delta -> true
   | _ -> false in
 unif 0 a bdepth b false
;;

(* Look in Git for Enrico's partially tail recursive but slow unification.
   The tail recursive version is even slower. *)

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
(* TODO: to save memory, introduce a list of triples *)
 | FCons of (*lvl:*)alternative * ((*depth:*)int * program * term) list * frame
and alternative = {
  lvl : alternative;
  program : program;
  depth : int;
  goal : term;
  goals : ((*depth:*)int * program * term) list;
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
let pic = fst (funct_of_ast F.pif)

let rec chop =
 function
    App(c,hd2,tl) when c == andc ->
     chop hd2 @ List.flatten (List.map chop tl)
  | f when f==truec -> []
  | _ as f -> [ f ]

let rec clausify depth =
 function
    App(c, g, gs) when c == andc ->
     clausify depth g @ List.flatten (List.map (clausify depth) gs)
(* TODO: BUG the semantics of implc is wrong when g2 is not an atom. *)
  | App(c, g1, [g2]) when c == implc ->
     [ { depth ; hd=g2 ; hyps=chop g1 ; vars=0 ; key = key_of depth g2 } ]
  | App(c, Lam b, []) when c == pic ->
     (* TODO: this should be allowed! But the parser needs to be
        fixed to parse pis in positive position correctly, binding
        the UVars as Constants *)
     assert false
  | UVar ({ contents=g },_,_) when g == dummy ->
     raise (Failure "Not a predicate in clausify")
  | UVar ({ contents=g },origdepth,args) ->
     clausify depth (deref ~from:origdepth ~to_:depth args g)
  | g -> [ { depth ; hd=g ; hyps=[] ; vars=0 ; key = key_of depth g } ]
;;

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : ('a -> 'b -> 'k) * ('k -> 'k) =
  let trail = ref [] in

  (* Input to be read as the orl (((p,g)::gs)::next)::alts
     Depth >= 0 is the number of variables in the context.
  *)
  let rec run depth p g gs (next : frame) alts lvl =
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
           | (depth,p,g)::gs -> run depth p g gs next alts lvl)
    | App(c, g, gs') when c == andc ->
       run depth p g (List.map(fun x -> depth,p,x) gs'@gs) next alts lvl
    (* We do not check the case of implication applied to
       multiple arguments *)
    | App(c, g1, [g2]) when c == implc ->
       let clauses = clausify depth g1 in
       run depth (add_clauses clauses p) g2 gs next alts lvl
    | App(c, Lam f, []) when c == pic ->
       run (depth+1) p f gs next alts lvl
    | UVar ({ contents=g },_,_) when g == dummy ->
       raise (Failure "Not a predicate")
    | UVar ({ contents=g },origdepth,args) ->
       run depth p (deref ~from:origdepth ~to_:origdepth args g)
        gs next alts lvl
    | Lam _ -> raise (Failure "Not a predicate")
    | Const _ | App _ -> (* Atom case *)
        let cp = get_clauses depth g p in
        backchain depth p g gs cp next alts lvl
    | Arg _ -> assert false (* Not an heap term *)

  and backchain depth p g gs cp next alts lvl =
    (*Format.eprintf "BACKCHAIN %a @ %d\n%!" ppterm g lvl;
List.iter (fun (_,g) -> Format.eprintf "GS %a\n%!" ppterm g) gs;*)
    let last_call = alts == emptyalts in
    let rec select = function
    | [] -> next_alt alts
    | c :: cs ->
        let old_trail = !trail in
        let last_call = last_call && cs = [] in
        let env = Array.create c.vars dummy in
        match unif trail last_call depth g env c.depth c.hd with
        | false -> undo_trail old_trail trail; select cs
        | true ->
(* TODO: make to_heap lazy adding the env to unify and making the env
   survive longer. It may be slower or faster, who knows *)
            let oldalts = alts in
            let alts =
             if cs = [] then alts
             else
              { program=p; depth; goal=g; goals=gs; stack=next;
                trail=old_trail; clauses=cs; lvl ;
                next=alts} in
            (match c.hyps with
               [] ->
                (match gs with
                    [] -> pop_andl alts next
                  | (depth,p,g)::gs -> run depth p g gs next alts lvl)
             | g'::gs' ->
                let next =
                 if gs = [] then next
                 else FCons (lvl,gs,next) in
                let g' =
                 (*Format.eprintf "to_heap ~from:%d ~to:%d %a\n%!" depth depth ppterm g';*)
                 to_heap depth last_call trail ~from:c.depth ~to_:depth
                  env g' in
                let gs' =
                 List.map
                  (fun x->
                    depth,p,
                     to_heap depth last_call trail ~from:c.depth ~to_:depth
                      env x) gs'
                in
                 run depth p g' gs' next alts oldalts)
    in
      select cp

  and pop_andl alts =
   function
      FNil -> alts
    | FCons (_,[],_) -> assert false
    | FCons(lvl,(depth,p,g)::gs,next) -> run depth p g gs next alts lvl

  and next_alt alts =
   if alts == emptyalts then raise (Failure "no clause")
   else begin
    let { program = p; depth; goal = g; goals = gs; stack=next;
          trail = old_trail; clauses; lvl ; next=alts} = alts in
    undo_trail old_trail trail;
    backchain depth p g gs clauses next alts lvl
   end
  in
   (fun p q -> run 0 p q [] FNil emptyalts emptyalts), next_alt
;;
 
let heap_var_of_ast l n =
 try l,List.assoc n l
 with Not_found ->
  let n' = UVar (ref dummy,0,[]) in
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
         hd2::tl -> l,l',App(f,hd2,tl)
       | _ -> assert false)
  | AST.Lam (x,t) ->
     let c = constant_of_dbl lvl in
     let l,l',t' = stack_term_of_ast (lvl+1) l ((x,c)::l') t in
     l,l',Lam t'
  | AST.App (AST.Var v,tl) ->
     let l,l',rev_tl =
       List.fold_left
        (fun (l,l',tl) t ->
          let l,l',t = stack_term_of_ast lvl l l' t in (l,l',t::tl))
        (l,l',[]) tl in
     let tl = List.rev rev_tl in
     let tl =
      let rec aux =
       function
         [] -> []
       | Const c::tl -> c::aux tl
       | _ -> assert false (* Not in Pattern Fragment *)
      in
       aux tl in
     (match stack_var_of_ast l v with
         l,Arg (v,[]) -> l,l',Arg(v,tl)
       | _,_ -> assert false)
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
   { depth = 0
   ; hd = a
   ; hyps = chop f
   ; vars = max
   ; key = key_of 0 a
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
   try ignore (run p q) ; false
   with Failure _ -> true

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
