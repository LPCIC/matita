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
(* TODO: go back as it used to be, with the depth not stored in Arg
   because all Args at the same depth share the same depth. Therefore
   one can pass the argsdepth around in run/to_heap/restrict/unif/...
   Is the memory saving really worth it? *)
  | Arg of int * constant list
  (* Heap terms *)
  | App of constant * term * term list
  | Custom of constant * term list
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

let ppterm env f t =
  let rec ppapp hd a c1 c2 = 
    Format.fprintf f "%c@[<hov 1>" c1;
    ppconstant hd;
    Format.fprintf f "@ ";
    List.iter (fun x -> aux x; Format.fprintf f "@ ") a;
    Format.fprintf f "@]%c" c2
  and ppconstant c = Format.fprintf f "%s" (string_of_constant c)
  and aux = function
      t when t == dummy -> Format.fprintf f "dummy"
    | App (hd,x,xs) -> ppapp hd (x::xs) '(' ')'
    | Custom (hd,xs) -> ppapp hd xs '(' ')'
    | UVar ({ contents = t },depth,args) ->
       Format.fprintf f "(<@[<hov 1>";
       aux t;
       Format.fprintf f ">_%d " depth;
       List.iter (fun x -> ppconstant x; Format.fprintf f "@ ") args;
       Format.fprintf f "@])"
    | Const s -> ppconstant s
    | Arg (i,args) ->
       Format.fprintf f "{@[<hov 1>";
       if env.(i) == dummy then
        Format.fprintf f "A%d " i
       else begin
        Format.fprintf f "≪";
        aux env.(i);
        Format.fprintf f "≫ ";
       end;
       List.iter (fun x -> ppconstant x; Format.fprintf f "@ ") args;
       Format.fprintf f "@]}"
    | Lam t ->
       Format.fprintf f "\\(";
       aux t;
       Format.fprintf f ")";
  in
    aux t
;;

let m = ref [];;
let n = ref 0;;

let uppterm names env f t =
  let rec pp_uvar r =
   if !r == dummy then begin
    let s =
     try (List.assq r !m)
     with Not_found ->
      let s = "X" ^ string_of_int !n in
      incr n;
      m := (r,s)::!m;
      s
    in
     Format.fprintf f "%s" s 
   (* TODO: (potential?) bug here, the variable is not lifted
      from origdepth (currently not even passed to the function)
      to depth (not passed as well) *)
   end else aux !r
  and ppapp hd a c1 c2 = 
    Format.fprintf f "%c@[<hov 1>" c1;
    ppconstant hd;
    Format.fprintf f "@ ";
    let args,last =
     match List.rev a with
        [] -> assert false
      | last::l_rev -> List.rev l_rev,last in
    List.iter (fun x -> aux x; Format.fprintf f "@ ") args;
    aux last;
    Format.fprintf f "@]%c" c2
  and ppconstant c = Format.fprintf f "%s" (string_of_constant c)
  and nth_name n =
   try List.nth names n with Not_found -> "A" ^ string_of_int n
  and aux = function
      App (hd,x,xs) -> ppapp hd (x::xs) '(' ')'
    | Custom (hd,xs) -> ppapp hd xs '(' ')'
    | UVar (r,_,[]) -> pp_uvar r;
    | UVar (r,_,args) ->
       Format.fprintf f "(@[<hov 1>";
       pp_uvar r;
       let args,last =
        match List.rev args with
           [] -> assert false
         | last::l_rev -> List.rev l_rev,last in
       List.iter (fun x -> ppconstant x; Format.fprintf f "@ ") args;
       ppconstant last;
       Format.fprintf f "@])"
    | Const s -> ppconstant s
    | Arg (n,args) ->
       if args = [] then
        if env.(n) == dummy then Format.fprintf f "%s" (nth_name n)
        (* TODO: (potential?) bug here, the argument is not lifted
           from g_depth (currently not even passed to the function)
           to depth (not passed as well) *)
        else aux env.(n)
       else begin
        Format.fprintf f "(@[<hov 1>";
        if env.(n) == dummy then Format.fprintf f "%s" (nth_name n)
        (* TODO: (potential?) bug here, the argument is not lifted
           from g_depth (currently not even passed to the function)
           to depth (not passed as well) *)
        else aux env.(n);
         let args,last =
          match List.rev args with
             [] -> assert false
           | last::l_rev -> List.rev l_rev,last in
         List.iter (fun x -> ppconstant x; Format.fprintf f "@ ") args;
         ppconstant last;
        Format.fprintf f "@])"
       end
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

(************************* to_heap/restrict/full_deref ******************)

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
  (*Format.eprintf "to_heap: from=%d, to=%d %a\n%!" from to_ ppterm t;*)
  let delta = from - to_ in
  let rec aux depth x =
   (*Format.eprintf "to_heap(%d,%d): %a\n%!" depth delta ppterm x;*)
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
    | Custom (c,l) ->
       let l' = smart_map (aux depth) l in
       if l==l' then x else Custom (c,l')
    | App (c,t,l) when c >= from ->
       App(c-delta,aux depth t,smart_map (aux depth) l)
    | App _ -> raise RestrictionFailure
    | UVar _ when delta=0 -> x
    | UVar ({contents=t},vardepth,args) when t != dummy ->
       if depth = 0 then
        full_deref argsdepth last_call trail ~from:vardepth ~to_ args e t
       else
        (* First phase: from vardepth to from+depth *)
        let t =
         full_deref argsdepth last_call trail ~from:vardepth
          ~to_:(from+depth) args e t in
        (* Second phase: from from to to *)
        aux depth t
    | UVar (r,_,[]) when delta > 0 ->
       let fresh = UVar(ref dummy,to_,[]) in
       if not last_call then trail := r :: !trail;
       r := fresh;
       (* TODO: test if it is more efficient here to return fresh or
          the original, imperatively changed, term. The current solution
          avoids full_dereference chains, but puts more pressure on the GC. *)
       fresh
    | UVar (_,_,_) when delta < 0 -> x
    | UVar (_,_,_) -> assert false (* TO BE IMPLEMENTED *)
    | Arg (i,args) ->
        let args =
         smart_map (fun c ->
          if c >= from then (c - delta)
          else if c < to_ then c
          else raise RestrictionFailure
         ) args in
        let a = e.(i) in
        (*Format.eprintf "%a = %a\n%!" ppterm (Arg(i,argsdepth,[])) ppterm a;*)
        if a == dummy then
            let r = ref dummy in
            let v = UVar(r,to_,[]) in
            e.(i) <- v;
            UVar(r,to_,args)
        else
         full_deref argsdepth last_call trail ~from:argsdepth
          ~to_:(to_+depth) args e a
  in aux 0 t

(* Note: when full_deref is called inside restrict, it may be from > to_ *)
(* full_deref is always called on terms on the heap *)
and full_deref argsdepth last_call trail ~from ~to_ args e t =
 if args = [] then
  if from=to_ then t
  else to_heap argsdepth last_call trail ~from ~to_ e t
 else (* O(1) reduction fragment tested here *)
  let from,args,t = eat_args from args t in
  let t =
   match args,t with
      [],t -> t
    | _,Lam _ -> assert false (* TODO: Implement beta-reduction here *)
    | hd::args,Const c ->
       (App (c,constant_of_dbl hd,List.map constant_of_dbl args))
    | args,App (c,arg,args2) ->
       (App (c,arg,args2 @ List.map constant_of_dbl args))
    | args,Custom (c,args2) ->
       (Custom (c,args2@List.map constant_of_dbl args))
    (* TODO: when the UVar/Arg is not dummy, we call full_deref that
       will call to_heap that will call_full_deref again. Optimize the
       path *)
    | args,UVar(t,depth,args2) -> UVar(t,depth,args2@args)
    | args,Arg(i,args2) -> Arg(i,args2@args)
   in
    full_deref argsdepth last_call trail ~from ~to_ [] e t
;;

let restrict argsdepth last_call trail ~from ~to_ heap e t =
 if from=to_ && heap then t
 else to_heap argsdepth last_call trail ~from ~to_ e t
;;

(* Deref is to be called only on heap terms and with from <= to *)
let deref ~from ~to_ args t =
 (* TODO: Remove the assertion when we are sure *)
 assert (from <= to_);
 (* Dummy trail: it won't be used because from <= to, hence no restriction*)
 (* Dummy env and argsdepth: they won't be used because the term is on the
    heap *)
 full_deref 0 false (ref []) ~from ~to_ args [||] t
;;

(****** Indexing ******)

let variablek =    -99999999
let abstractionk = -99999998

let key_of argsdepth g_env g_depth =
 let rec skey_of = function
    Const k -> k
(* TODO: optimization: avoid full_dereferencing *)
  | UVar ({contents=t},origdepth,args) when t != dummy ->
     skey_of (deref ~from:origdepth ~to_:g_depth args t)
  | Arg (i,args) when g_env.(i) != dummy ->
     skey_of (deref ~from:argsdepth ~to_:g_depth args g_env.(i))
  | App (k,_,_)
  | Custom (k,_) -> k
  | Lam _ -> abstractionk
  | Arg _
  | UVar _ -> variablek in
 let rec key_of_depth = function
   Const k -> k, variablek
(* TODO: optimization: avoid full_dereferencing *)
 | UVar ({contents=t},origdepth,args) when t != dummy ->
    key_of_depth (deref ~from:origdepth ~to_:g_depth args t)
 | Arg (i,args) when g_env.(i) != dummy ->
    key_of_depth (deref ~from:argsdepth ~to_:g_depth args g_env.(i))
 | App (k,arg2,_) -> k, skey_of arg2
 | Custom _ | Arg _ | Lam _ | UVar _ -> raise (Failure "Not a predicate")
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

let get_clauses a_env a_depth a m =
 (* TODO: here we are full_dereferencing the term for computing the key
    and then we throw it away to full_dereference it again multiple times
    during unification. Does the other choice improves performance? *)
 let ind,app = key_of a_depth a_env a_depth a in
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

let rec make_lambdas destdepth depth =
 function
    hd::tl when hd=depth ->
     let args,body = make_lambdas (destdepth+1) (depth+1) tl in
      args,Lam body
  | args -> args,UVar(ref dummy,destdepth,[])

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
   argsdepth is the depth of the Args that occur in the query (l.h.s.)
   adepth    is the depth of the Args that occur in the head  (r.h.s.)

   (-infy,bdepth) = (-infty,bdepth)   common free variables
   [bdepth,adepth)                    free variable only visible by one:fail
   [adepth,+infty) = [bdepth,+infy)   bound variables *)
let unif trail last_call argsdepth ae adepth a be bdepth b =
 let rec unif depth a aheap bdepth b bheap =
   (*Format.eprintf "unif %b,%b: ^%d:%a =%d= ^%d:%a\n%!" last_call bheap adepth (ppterm ae) a depth bdepth (ppterm be) b;*)
   let delta = adepth - bdepth in
   match a,b with
(* TODO: test if it is better to full_deref first or not, i.e. the relative order
   of the clauses below *)
   | _, Arg (i,[]) when be.(i) == dummy ->
(* TODO: check all places where RestrictionFailure should be captured,
   in patternunif.ml as well *)
     (try
       be.(i) <-
        restrict argsdepth last_call trail ~from:(adepth+depth)
         ~to_:adepth aheap ae a;
       (*Format.eprintf "<- %a\n%!" (ppterm be) be.(i);*)
       true
     with RestrictionFailure -> false)
   | _, Arg (i,args) when be.(i) == dummy ->
      (*Format.eprintf "%a %d===%d %a\n%!" ppterm a adepth bdepth ppterm b;*)
      (* Here I am doing for the O(1) unification fragment *)
      let args,body = make_lambdas adepth bdepth args in
      be.(i) <- body;
      if args = [] then
       (* TODO: unif goes into the UVar when !r != dummy case below.
          Rewrite the code to do the job directly? *)
       unif depth a aheap bdepth b bheap
      else assert false (* TODO: h.o. unification not implemented *)
   | _, Arg (i,args) ->
      (* The arguments live in bdepth+depth; the variable lives in adepth
         that can be larger than bdepth+depth, but is smaller than
         adepth+depth; everything leaves in adepth+depth after full_derefercing.       *)
      let args = List.map (fun c -> if c < bdepth then c else c+delta) args in
      unif depth a aheap adepth (deref ~from:adepth ~to_:(adepth+depth)
       args be.(i)) true
   | Arg (i,[]),_ when ae.(i) == dummy ->
     (* TODO: factorize the code *)
     (try
      ae.(i) <-
       if depth=0 then
        if argsdepth = bdepth && bheap then b else
         restrict adepth last_call trail ~from:(bdepth+depth)
          ~to_:argsdepth bheap be b
       else (
        (* First step: we lift the r.h.s. to the l.h.s. level *)
        let b =
         to_heap adepth last_call trail ~from:bdepth ~to_:adepth be b in
        (* Second step: we restrict the r.h.s. *)
        restrict adepth last_call trail ~from:(adepth+depth) ~to_:argsdepth
         true be b);
      true
     with RestrictionFailure -> false)
   | Arg (i,args),_ when ae.(i) == dummy ->
      (*Format.eprintf "%a %d===%d %a\n%!" ppterm a adepth bdepth ppterm b;*)
      (* Here I am doing for the O(1) unification fragment *)
      let args,body = make_lambdas argsdepth adepth args in
      ae.(i) <- body;
      if args = [] then
       (* TODO: unif goes into the UVar when !r != dummy case below.
          Rewrite the code to do the job directly? *)
       unif depth a aheap bdepth b bheap
      else assert false (* TODO: h.o. unification not implemented *)
   | UVar (r,origdepth,[]), _ when !r == dummy ->
       if not last_call then trail := r :: !trail;
       (* TODO: are exceptions efficient here? *)
       (try
         r :=
          (* TODO *)
          if depth=0 then
           if origdepth = bdepth && bheap then b else
            to_heap adepth last_call trail ~from:bdepth ~to_:origdepth be b
          else (
           (* First step: we lift the r.h.s. to the l.h.s. level *)
           let b =
            to_heap adepth last_call trail ~from:bdepth ~to_:adepth be b in
           (* Second step: we restrict the r.h.s. *)
           restrict adepth last_call trail ~from:(adepth+depth)
            ~to_:origdepth true be b);
         true
       with RestrictionFailure -> false)
   | UVar (r,origdepth,args), _ when !r == dummy ->
      if not last_call then trail := r :: !trail;
      (* Here I am doing for the O(1) unification fragment *)
      let args,body = make_lambdas origdepth origdepth args in
      r := body;
      if args = [] then
       (* TODO: unif goes into the UVar when !r != dummy case below.
          Rewrite the code to do the job directly? *)
       unif depth a aheap bdepth b bheap
      else assert false (* TODO: h.o. unification not implemented *)
   | _, UVar (r,origdepth,[]) when !r == dummy ->
       if not last_call then trail := r :: !trail;
       (* TODO: are exceptions efficient here? *)
       (try
         r :=
          (* TODO *)
          if depth = 0 then
           restrict argsdepth last_call trail ~from:adepth ~to_:origdepth
            aheap ae a
          else (
           (* First step: we restrict the l.h.s. to the r.h.s. level *)
           let a =
            to_heap argsdepth last_call trail ~from:adepth ~to_:bdepth ae a
           in
           (* Second step: we restrict the l.h.s. *)
           restrict argsdepth last_call trail ~from:(bdepth+depth)
            ~to_:origdepth true ae a);
         true
       with RestrictionFailure -> false)
   | _, UVar (r,origdepth,args) when !r == dummy ->
      if not last_call then trail := r :: !trail;
      (* Here I am doing for the O(1) unification fragment *)
      let args,body = make_lambdas origdepth origdepth args in
      r := body;
      if args = [] then
       (* TODO: unif goes into the UVar when !r != dummy case below.
          Rewrite the code to do the job directly? *)
       unif depth a aheap bdepth b bheap
      else assert false (* TODO: h.o. unification not implemented *)
   | _, UVar ({ contents = t },origdepth,args) ->
      (* The arguments live in bdepth+depth; the variable lives in origdepth;
         everything leaves in bdepth+depth after full_derefercing. *)
      unif depth a aheap bdepth
       (deref ~from:origdepth ~to_:(bdepth+depth) args t) true
   | Arg (i,args),_ ->
      (* The arguments live in adepth+depth; the variable lives in argsdepth;
         everything leaves in adepth+depth after full_derefercing. *)
      unif depth (deref ~from:argsdepth ~to_:(adepth+depth) args ae.(i))
       true bdepth b bheap
   | UVar ({ contents = t },origdepth,args), _ ->
      (* The arguments live in adepth+depth; the variable lives in origdepth;
         everything leaves in adepth+depth after full_derefercing. *)
      unif depth (deref ~from:origdepth ~to_:(adepth+depth) args t)
       true bdepth b bheap
   | App (c1,x2,xs), App (c2,y2,ys) ->
      (* Compressed cut&past from Const vs Const case below +
         delta=0 optimization for <c1,c2> and <x2,y2> *)
      ((delta=0 || c1 < bdepth) && c1=c2
       || c1 >= adepth && c1 = c2 + delta)
       &&
       (delta=0 && x2 == y2 || unif depth x2 aheap bdepth y2 bheap) &&
       for_all2 (fun x y -> unif depth x aheap bdepth y bheap) xs ys
   | Custom (c1,xs), Custom (c2,ys) when c1=c2 ->
       (* Inefficient comparison *)
       for_all2 (fun x y -> unif depth x aheap bdepth y bheap) xs ys
   | Lam t1, Lam t2 -> unif (depth+1) t1 aheap bdepth t2 bheap
   | Const c1, Const c2 when c1=c2 && c1 < bdepth -> true
   | Const c, _ when c >= bdepth && c < adepth -> false
   | Const c1, Const c2 when c1 = c2 + delta -> true
   | _ -> false in
 unif 0 a false bdepth b false
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
 | FCons of (*lvl:*)alternative * (*argsdepth:*)int * (program * (*env:*)term array * (*g_depth:*) int * term) list * frame
and alternative = {
  lvl : alternative;
  program : program;
  argsdepth : int;
  g_env : term array;
  g_depth : int;
  goal : term;
  goals : (program * (*env:*) term array * (*g_depth:*) int * term) list;
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

(* The input of clausify must be an heap term *)
let rec clausify env depth =
 function
    App(c, g, gs) when c == andc ->
     clausify env depth g @ List.flatten (List.map (clausify env depth) gs)
(* TODO: BUG the semantics of implc is wrong when g2 is not an atom. *)
  | App(c, g1, [g2]) when c == implc ->
     [ { depth ; hd=g2 ; hyps=chop g1 ; vars=0 ;
         key = key_of depth env depth g2}]
  | App(c, Lam b, []) when c == pic ->
     (* TODO: this should be allowed! But the parser needs to be
        fixed to parse pis in positive position correctly, binding
        the UVars as Constants *)
     assert false
  | UVar ({ contents=g },_,_) when g == dummy -> assert false
  | UVar ({ contents=g },origdepth,args) ->
     clausify env depth (deref ~from:origdepth ~to_:depth args g)
  | Arg _ -> assert false
  | Lam _ | Custom _ -> assert false
  | (Const _ | App _) as g ->
      [ { depth ; hd=g ; hyps=[] ; vars=0 ; key = key_of depth env depth g}]
;;

let register_custom,lookup_custom =
 let (customs : ('a,(*env:*)term array -> term list -> unit) Hashtbl.t) = Hashtbl.create 17 in
 Hashtbl.add customs,Hashtbl.find customs
;;

let _ =
 register_custom (fst (funct_of_ast (Parser.ASTFuncS.from_string "$print")))
  (fun env args ->
   Format.printf "@[<hov 1>" ;
   List.iter (Format.printf "%a@ " (uppterm [] env)) args;
   Format.printf "@]\n%!")
;;

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : ('a -> 'b -> 'k) * ('k -> 'k) =
  let trail = ref [] in

  (* Input to be read as the orl (((p,g)::gs)::next)::alts
     Depth >= 0 is the number of variables in the context.

     <env,g_depth,g> means that the Args in the formula g are
       bound in env, and that g lives at lvl g_depth
  *)
  let rec run p argsdepth g_env g_depth g gs (next : frame) alts lvl =
    (*Format.eprintf "goal^%d: %a\n%!" g_depth (ppterm g_env) g;*)
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
           | (p,g_env,g_depth,g)::gs ->
               run p argsdepth g_env g_depth g gs next alts lvl)
    | App(c, g, gs') when c == andc ->
       run p argsdepth g_env g_depth g
        (List.map(fun x -> p,g_env,g_depth,x) gs'@gs) next alts lvl
    (* We do not check the case of implication applied to
       multiple arguments *)
    | App(c, g1, [g2]) when c == implc ->
       let g1 =
        to_heap argsdepth false trail ~from:g_depth ~to_:g_depth g_env g1 in
       let clauses = clausify g_env g_depth g1 in
       run (add_clauses clauses p) argsdepth g_env g_depth g2 gs next alts
        lvl
    | App(c, Lam f, []) when c == pic ->
       run p argsdepth g_env (g_depth+1) f gs next alts lvl
    | UVar ({ contents=g },_,_) when g == dummy -> assert false
    | UVar ({ contents=g },origdepth,args) ->
       run p argsdepth g_env g_depth
        (deref ~from:origdepth ~to_:g_depth args g) gs next alts lvl
    | Arg (i,_) when g_env.(i) == dummy -> assert false
    | Arg (i,args) ->
       run p argsdepth g_env g_depth
        (deref ~from:argsdepth ~to_:g_depth args g_env.(i)) gs next alts lvl
    | Lam _ -> assert false
    | Const _ | App _ -> (* Atom case *)
        let cp = get_clauses g_env g_depth g p in
        backchain p argsdepth g_env g_depth g gs cp next alts lvl
    | Custom(c,gs') ->
       (try lookup_custom c g_env gs'
        with Not_found -> assert false) ;
       (match gs with
           [] -> pop_andl alts next
         | (p,g_env,g_depth,g)::gs ->
             run p argsdepth g_env g_depth g gs next alts lvl)

  and backchain p argsdepth g_env g_depth g gs cp next alts lvl =
    (*Format.eprintf "BACKCHAIN %a @ %d\n%!" (ppterm g_env) g lvl;
List.iter (fun (_,g) -> Format.eprintf "GS %a\n%!" ppterm g) gs;*)
    let last_call = alts == emptyalts in
    let rec select = function
    | [] -> next_alt alts
    | c :: cs ->
        let old_trail = !trail in
        let last_call = last_call && cs = [] in
        let c_env = Array.create c.vars dummy in
        match
         unif trail last_call argsdepth g_env g_depth g c_env c.depth c.hd
        with
        | false -> undo_trail old_trail trail; select cs
        | true ->
            let oldalts = alts in
            let alts =
             if cs = [] then alts
             else
              { program=p; argsdepth; g_env; g_depth; goal=g; goals=gs;
                stack=next; trail=old_trail; clauses=cs; lvl ; next=alts} in
            (match c.hyps with
               [] ->
                (match gs with
                    [] -> pop_andl alts next
                  | (p,g_env,g_depth,g)::gs ->
                      run p argsdepth g_env g_depth g gs next alts lvl)
             | g'::gs' ->
                let next =
                 if gs = [] then next
                 else FCons (lvl,argsdepth,gs,next) in
                let gs' = List.map (fun x-> p,c_env,c.depth,x) gs' in
                 run p g_depth c_env c.depth g' gs' next alts oldalts)
    in
      select cp

  and pop_andl alts =
   function
      FNil -> alts
    | FCons (_,_,[],_) -> assert false
    | FCons(lvl,argsdepth,(p,g_env,g_depth,g)::gs,next) ->
       run p argsdepth g_env g_depth g gs next alts lvl

  and next_alt alts =
   if alts == emptyalts then raise (Failure "no clause")
   else begin
    let { program = p; argsdepth; g_env; g_depth; goal = g; goals = gs;
          stack=next; trail = old_trail; clauses; lvl ; next=alts} = alts in
    undo_trail old_trail trail;
    backchain p argsdepth g_env g_depth g gs clauses next alts lvl
   end
  in
   (fun p (_,q_env,q) -> run p 0 q_env 0 q [] FNil emptyalts emptyalts),
     next_alt
;;
 
let stack_var_of_ast (f,l) n =
 try (f,l),List.assoc n l
 with Not_found ->
  let n' = Arg (f,[]) in
  (f+1,(n,n')::l),n'

let stack_funct_of_ast l' f =
 (try l',List.assoc f l'
  with Not_found -> l',funct_of_ast f)

let rec stack_term_of_ast lvl l l' =
 function
    AST.Var v ->
     let l,v = stack_var_of_ast l v in
     l,l',v
  | AST.App(AST.Const f,[]) when F.eq f F.andf ->
     l,l',truec
  | AST.Const f -> let l',c=stack_funct_of_ast l' f in l,l',snd c
  | AST.Custom f -> l,l',Custom (fst (funct_of_ast f),[])
  | AST.App(AST.Const f,tl) ->
     let l,l',rev_tl =
       List.fold_left
        (fun (l,l',tl) t ->
          let l,l',t = stack_term_of_ast lvl l l' t in (l,l',t::tl))
        (l,l',[]) tl in
     let l',c = stack_funct_of_ast l' f in
     (match List.rev rev_tl with
         hd2::tl -> l,l',App(fst c,hd2,tl)
       | _ -> assert false)
  | AST.App (AST.Custom f,tl) ->
     let l,l',rev_tl =
       List.fold_left
        (fun (l,l',tl) t ->
          let l,l',t = stack_term_of_ast lvl l l' t in (l,l',t::tl))
        (l,l',[]) tl in
     l,l',Custom(fst (funct_of_ast f),List.rev rev_tl)
  | AST.Lam (x,t) ->
     let c = constant_of_dbl lvl in
     let l,l',t' = stack_term_of_ast (lvl+1) l ((x,(lvl,c))::l') t in
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

let query_of_ast t =
 let (max,l),_,t = stack_term_of_ast 0 (0,[]) [] t in
  List.rev_map fst l,Array.create max dummy,t

let program_of_ast p =
 let clauses =
  List.map (fun (a,f) ->
   let l,_,a = stack_term_of_ast 0 (0,[]) [] a in
   let (max,l),_,f = stack_term_of_ast 0 l [] f in
   let names = List.rev_map fst l in
   let env = Array.create max dummy in
Format.eprintf "%a :- " (uppterm names env) a;
List.iter (Format.eprintf "%a, " (uppterm names env)) (chop f);
Format.eprintf ".\n%!";
   { depth = 0
   ; hd = a
   ; hyps = chop f
   ; vars = max
   ; key = key_of 0 env 0 a
   }) p
 in
  make clauses

let impl =
 (module struct
  (* RUN with non indexed engine *)
  type query = string list * term array * term
  type program_ = program
  type program = program_
  let query_of_ast = query_of_ast
  let program_of_ast = program_of_ast

  let msg (q_names,q_env,q) =
   Format.fprintf Format.str_formatter "Pattern unification only, lazy refresh: %a" (uppterm q_names q_env) q ;
   Format.flush_str_formatter ()

  let execute_once p q =
   let run, cont = make_runtime in
   try ignore (run p q) ; false
   with Failure _ -> true

  let execute_loop p ((q_names,q_env,q) as qq) =
   let run, cont = make_runtime in
   let time0 = Unix.gettimeofday() in
   let k = ref (run p qq) in
   let time1 = Unix.gettimeofday() in
   prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
   Format.eprintf "Raw Result: %a\n%!" (ppterm q_env) q ;
   Format.eprintf "Result: \n%!" ;
   List.iteri (fun i name -> Format.eprintf "%s=%a\n%!" name
    (uppterm q_names q_env) q_env.(i)) q_names;
   while !k != emptyalts do
     prerr_endline "More? (Y/n)";
     if read_line() = "n" then k := emptyalts else
      try
       let time0 = Unix.gettimeofday() in
       k := cont !k;
       let time1 = Unix.gettimeofday() in
       prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
       Format.eprintf "Raw Result: %a\n%!" (ppterm q_env) q ;
       Format.eprintf "Result: \n%!" ;
       List.iteri (fun i name -> Format.eprintf "%s=%a\n%!" name
        (uppterm q_names q_env) q_env.(i)) q_names;
      with
       Failure "no clause" -> prerr_endline "Fail"; k := emptyalts
  done
 end : Parser.Implementation)
