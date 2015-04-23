(***** real code *****)

module type ASTT =
  sig  
    (* TODO: The Struct vs App is just to save a boolean like Enrico does.
       Is that important? *)
    type term =
      (* Query terms *)
      | Struct of Lprun2.FuncS.t * term list
      | Arg of int
      (* Heap terms *)
      | App of Lprun2.FuncS.t * term list
      | Var of term ref

    type vart = term ref (* Can be hidden merging bindings with ASTT *)

    val dummy: term (* TODO: hide this detail? *)

    val mkAnd : term list -> term

    val pp: term -> string
  end;;

module AST : ASTT = 
  struct

    (* Invariant: a Heap term never points to a Query term *)
    type term =
      (* Query terms *)
      | Struct of Lprun2.FuncS.t * term list
      | Arg of int
      (* Heap terms *)
      | App of Lprun2.FuncS.t * term list
      | Var of term ref

    let dummy = Obj.magic ()

    type vart = term ref

    let mkAnd = function [f] -> f | l -> App(Lprun2.FuncS.andf,l)

    let rec pp =
      function
        t when t == dummy -> "dummy"
      | Var { contents = t } -> "<" ^ pp t ^ ">"
      | Arg i -> "A" ^ string_of_int i
      | App (f,l) | Struct (f,l) -> 
          if f = Lprun2.FuncS.andf then
          String.concat ", " (List.map pp l)
         else if f = Lprun2.FuncS.orf then
           "(" ^ String.concat "; " (List.map pp l) ^ ")"                 
           else if f = Lprun2.FuncS.cutf then
             "!" 
             else "(" ^ String.concat " " (Lprun2.FuncS.pp f :: List.map pp l) ^ ")"
  end;;

module Formula(Bind: Lprun2.BindingsT with type term = AST.term) : Lprun2.FormulaT 
    with type term = AST.term
    and  type bindings = Bind.bindings
 = 
  struct
    type term = AST.term
    type bindings = Bind.bindings

    let pp = AST.pp

    type formula =
       Cut
     | Atom of term
     | And of term list

    let mkAnd = AST.mkAnd
    
    let as_formula binds t =
     (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
     match Bind.deref binds t with
        AST.Var _ -> raise (Lprun2.NotFormula (lazy "Trying to prove a variable"))
      | AST.App(f,l) as x->
         (* And [] is interpreted as false *)
         if Lprun2.FuncS.eq f Lprun2.FuncS.andf then And l
         (* TODO: implement implication *)
         else if Lprun2.FuncS.eq f Lprun2.FuncS.implf then assert false
         (* Or [] is interpreted as true *)
         else if Lprun2.FuncS.eq f Lprun2.FuncS.cutf then Cut
         else Atom x
      | _ -> assert false (* A query is always an heap term *)
  end;;

module Parsable: Lprun2.ParsableT
 with type term := AST.term
 and  type clause = int * AST.term * AST.term =
 struct

  type clause = int * AST.term * AST.term

  let heap_var_of_ast l n =
   try l,List.assoc n l
   with Not_found ->
    let n' = AST.Var (ref AST.dummy) in
    (n,n')::l,n'
  
  let rec heap_term_of_ast l =
   function
      Lprun2.FOAST.Var v ->
       let l,v = heap_var_of_ast l v in
       l, v
    | Lprun2.FOAST.App(f,tl) ->
       let l,rev_tl =
         List.fold_left
          (fun (l,tl) t -> let l,t = heap_term_of_ast l t in (l,t::tl))
          (l,[]) tl in
       l, AST.App(Lprun2.FuncS.funct_of_ast f,List.rev rev_tl)
  
  let stack_var_of_ast (f,l) n =
   try (f,l),List.assoc n l
   with Not_found ->
    let n' = AST.Arg f in
    (f+1,(n,n')::l),n'
  
  let rec stack_term_of_ast l =
   function
      Lprun2.FOAST.Var v ->
       let l,v = stack_var_of_ast l v in
       l, v
    | Lprun2.FOAST.App(f,tl) ->
       let l,rev_tl =
         List.fold_left
          (fun (l,tl) t -> let l,t = stack_term_of_ast l t in (l,t::tl))
          (l,[]) tl in
       l, AST.Struct(Lprun2.FuncS.funct_of_ast f,List.rev rev_tl)
  
  let query_of_ast t = snd (heap_term_of_ast [] t)

  let program_of_ast p =
   List.map (fun (a,f) ->
    let l,a = stack_term_of_ast (0,[]) a in
    let (max,_),f = stack_term_of_ast l f in
     max,a,f
    ) p

 end

module ImpBindings : 
 Lprun2.BindingsT 
  with type var = AST.vart
  and type term = AST.term
  =
   struct
     type var = AST.vart
     type term = AST.term

     let imperative = true

     type bindings = var list (* This is the trail *)

     let empty_bindings = []

     let clean_trail _ = empty_bindings
        
     (* TODO: Enrico would return the term and test it against dummy
        later. Is that important? *)
     (* Yes, this way you allocate "Some" (in memory are 2 words, 1 for the
      * pointer to the contents of Some and one for tag + gc infos), also you
      * need to follow 2 pointers to get to the term *)
     let lookup _ k = if !k == AST.dummy then None else Some !k

     let bind ~deterministic binds k v =
      k := v ;
      if deterministic then binds else k::binds

     let cardinal binds = binds, (-1)

     let pp_bindings _ = "<< no way to print >>"
        
     let filter f _ = assert false (* TODO assign None *)

     let deref _ =
      let rec deref i =
        match i with
          AST.Var v ->
            (* Inlining of lookup! *)
            if !v == AST.dummy then i else deref !v
        | _ -> i
     in
      deref

     let backtrack ~current ~previous =
      let rec aux current =
       if current == previous then previous
       else
        match current with
           [] -> [](*assert false*)
         | v::tl ->
            v := AST.dummy;
            aux tl
      in
       aux current
   end;;

module RefreshableTerm : Lprun2.RefreshableTermT
 with type term = AST.term
 and  type refresher = AST.term array
 and  type clause = int * AST.term * AST.term
 and  type bindings = ImpBindings.bindings =
 struct
   include AST
   type clause = int * term * term
   type refresher = AST.term array
   type bindings = ImpBindings.bindings

   let to_heap e t =
     let rec aux = function
      | (AST.Var _ | AST.App _) as x -> x (* heap term *)
      | AST.Struct(hd,bs) -> App (hd, List.map aux bs)
      | Arg i ->
          let a = e.(i) in
          if a == dummy then
              let v = AST.Var(ref AST.dummy) in
              e.(i) <- v;
              v
          else aux a
    in aux t

   let refresh_head_of_clause (varsno,a,f) =
    let e = Array.create varsno AST.dummy in
    let a = to_heap e a in
     e,(varsno,a,f)
    
   let refresh_body_of_clause _ e f = e,to_heap e f
 end

module MapableTerm(Bind:Lprun2.BindingsT with type term = AST.term) : Lprun2.MapableTermT
  with type term = AST.term 
  and  type bindings = Bind.bindings
  and type clause = int * AST.term * AST.term
=
 struct
  type term = AST.term
  type clause = int * AST.term * AST.term
  let head (_,h,_) = h
  let body (_,_,b) = b
  module IndexData =
   struct
    type t = Lprun2.FuncS.t
    let equal = Lprun2.FuncS.eq
    let compare n1 n2 = String.compare (Lprun2.FuncS.pp n1) (Lprun2.FuncS.pp n2)
   end

  type bindings = Bind.bindings

  let index bind t =
    (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
    match Bind.deref bind t with
       AST.App(f,_) | AST.Struct(f,_) -> f
     | AST.Arg _ | AST.Var _ -> raise (Failure "Ill formed program")  
 end;;

module DoubleMapIndexableTerm(Bind: Lprun2.BindingsT with type var = AST.vart and type term = AST.term) : Lprun2.DoubleMapIndexableTermT
  with type term = AST.term 
  and type bindings = Bind.bindings
  and type clause = MapableTerm(Bind).clause
=
 struct
   include MapableTerm(Bind)
   module AST = AST

   (* TODO: Enrico is using a dummyt in place of option. Is that
      important? *)
   type approx = Lprun2.FuncS.t option

   let approx bind =
     function
       AST.App(_,[]) | AST.Struct(_,[]) -> None
     | AST.App(_,hd::_) | AST.Struct(_,hd::_) ->
         (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
        (match Bind.deref bind hd with
            AST.Var _ | AST.Arg _ -> None
          | AST.App(g,_) | AST.Struct(g,_) -> Some g)
     | AST.Arg _ | AST.Var _ -> raise (Failure "Ill formed program")

   let matchp app1 app2 =
     match app1,app2 with
       None,_
     | _,None-> true
     | Some g1,Some g2 -> g1=g2

 end;;

module Unify(Term: Lprun2.RefreshableTermT with type term = AST.term and type refresher = AST.term array)(Bind: Lprun2.BindingsT with type term = AST.term and type var = AST.vart and type bindings = Term.bindings) : Lprun2.UnifyT
   with type term := AST.term
   and type bindings = Term.refresher * Bind.bindings
=
  struct
    type bindings = Term.refresher * Bind.bindings

    (* Invariant: LSH is a heap term, the RHS is a query in env e *)
    let rec unify ~deterministic (e,sub) t1 t2 = 
      if t1 == t2 then e,sub else
      match t1,t2 with
      (*  (AST.Var v1, AST.Var v2) when Var.eq v1 v2 -> sub*)
      | _, AST.Arg i when e.(i) != AST.dummy -> unify ~deterministic (e,sub) t1 e.(i)
      | (AST.Var v1, _) ->
          (match Bind.lookup sub v1 with
             None ->
              (match t2 with
                  AST.Arg i -> e.(i) <- t1; e,sub
                      (* TODO: Enrico is more aggressive in dereferencing.
                         It dereferences t2 as well before binding it *)
                | _ ->
                 let e,t2 = Term.refresh_body_of_clause sub e t2 in
                  e,Bind.bind ~deterministic sub v1 t2)
           | Some t -> unify ~deterministic (e,sub) t t2)
      | (_,AST.Var v2) ->
          (match Bind.lookup sub v2 with
             None -> e,Bind.bind ~deterministic sub v2 t1 
           | Some t -> unify ~deterministic (e,sub) t1 t)
      | _, AST.Arg i -> e.(i) <- t1; e,sub
      | (AST.App (f1,l1), (AST.App (f2,l2) | AST.Struct (f2,l2))) -> 
          if Lprun2.FuncS.eq f1 f2 && List.length l1 = List.length l2 then
            List.fold_left2 (unify ~deterministic) (e,sub) l1 l2
          else
            raise (Lprun2.NotUnifiable (lazy "Terms are not unifiable!"))
      | AST.Arg _,_ | AST.Struct _,_ -> assert false (* Invariant violation *)
   end;;

(* implement the rest of the cases *)
let implementations = 
 let impl1 =
  (* RUN with indexed engine *)
  let module IBind = ImpBindings in
  let module IFormula = Formula(IBind) in
  let module IParsable = Parsable in
  let module ITerm = RefreshableTerm in
  let module IIndTerm = DoubleMapIndexableTerm(IBind) in
  let module IProgram = Lprun2.ProgramDoubleInd(IIndTerm)(IBind) in
  let module IRun = Lprun2.Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(ITerm)(IBind))(Lprun2.NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with desperate two level efficient index " end in
  (module Lprun2.Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in

  [impl1]
