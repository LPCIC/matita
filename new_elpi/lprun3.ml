(***** library functions *****)
        
(* precondition: the length of the two arrays must be the same *)
let array_fold_left2 f a a1 a2 =
 let a = ref a in
 for i=0 to Array.length a1 - 1 do
  a := f !a a1.(i) a2.(i)
 done ;
 !a

(***** real code *****)

module type ASTT =
  sig  
    type funct
    type term =
       Var of vart
     | App of funct * term array
    and vart = term array * int

    val eq_var : vart -> vart -> bool

    val mkCut : term
    val mkAnd : term list -> term
    val mkOr : term list -> term
    val mkEq : term -> term -> term

    type refresher
    val empty_refresher : refresher
    val refresh_var : refresher -> vart -> term array -> refresher * vart

    val deref : vart -> term
    val assign : vart -> term -> unit
  end;;

module AST(Func: Parser.ASTFuncT) : ASTT
 with type funct = Func.t = 
 struct
    type funct = Func.t

    type term =
       Var of vart
     | App of Func.t * term array
    and vart = term array * int

    let deref (args,i) = args.(i)
    let assign (args,i) t = args.(i) <- t

    let eq_var = (==);;

    (* TODO: mkAnd/mkOr is bugged when the array l is made of variables! *)
    let mkAnd = function [f] -> f | l -> App(Func.andf,Array.of_list l)
    let mkOr  = function [f] -> f | l -> App(Func.orf,Array.of_list l)
    (* Next two never called: *)
    let mkCut = App(Func.cutf,[||])
    let mkEq _ _ = assert false

    type refresher = (vart * vart) list
    let empty_refresher = []
 
    let refresh_var l ((_,i0) as v) args =
     try l,List.assq v l
     with Not_found ->
      let v' = args,i0 in
      (v,v')::l, v'
 end

module Formula(Func: Parser.ASTFuncT)(Bind: Lprun2.BindingsT with type term = AST(Func).term) : Lprun2.FormulaT 
    with type term = AST(Func).term
    and  type bindings = Bind.bindings
 = 
  struct
    module AST = AST(Func)

    type term = AST.term
    type bindings = Bind.bindings

    type formula =
      Cut
    | Atom of term
    | And of term list

    let mkAnd = AST.mkAnd
    let mkOr  = AST.mkOr

     (* raise NotAFormula *)
    let as_formula binds t =
     (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
     match Bind.deref binds t with
        AST.Var _ -> raise (Lprun2.NotFormula (lazy "Trying to prove a variable"))
      | AST.App(f,l) as x->
         (* And [] is interpreted as false *)
         if Func.eq f Func.andf then And (Array.to_list l)
         (* TODO: implement implication *)
         else if Func.eq f Func.implf then assert false
         (* Or [] is interpreted as true *)
         else if Func.eq f Func.cutf then Cut
         else Atom x

    let rec pp = 
      function 
        AST.Var (_,i) -> "X" ^ string_of_int i
      | AST.App(f, args) -> 
          Func.pp f ^ "(" ^ String.concat " " (List.map pp (Array.to_list args)) ^ ")"
  end

module Parsable(Func: Lprun2.FuncT) : Lprun2.ParsableT
 with type term := AST(Func).term
 and  type clause = AST(Func).term * AST(Func).term =
 struct
  module AST = AST(Func)

  type clause = AST.term * AST.term

  let var_of_ast l v args i =
   try l,List.assoc v l
   with Not_found ->
    let v' = args,i in
    (v,v')::l, v'


   let rec term_of_ast l =
    let rec aux args i l =
     function
       Parser.Var v ->
        let l,v = var_of_ast l v args i in
        l, AST.Var v
     | Parser.Const f -> l, AST.App(Func.funct_of_ast f,[||])
     | Parser.Custom _ -> assert false
     | Parser.App(Parser.Const f,tl) ->
        let tl' = Array.make (List.length tl) (Obj.magic ()) (* dummy *) in
        let l = ref l in
        List.iteri (fun i t -> let l',t' = aux tl' i !l t in l := l' ; tl'.(i) <- t') tl ;
        !l, AST.App(Func.funct_of_ast f,tl')
     | Parser.Lam _ | Parser.App(_,_) -> (* Not in Prolog *) assert false
    in
     aux [||] (-999) l

  let query_of_ast t = snd (term_of_ast [] t)

  let program_of_ast p =
   List.map (fun (a,f) ->
    let l,a = term_of_ast [] a in
    let _,f = term_of_ast l f in
    a,f) p
 end;;


module Bindings(Func: Lprun2.FuncT) : Lprun2.BindingsT 
  with type var = AST(Func).vart
  and type term = AST(Func).term
  =
   struct
    module T = AST(Func)
    type var = T.vart
    type term = T.term

    let imperative = true

    type bindings = var list (* Trail *)

    let empty_bindings = []

    let clean_trail _ = empty_bindings
        
    let lookup _ v =
     match T.deref v with
        T.Var v' when T.eq_var v v' -> None
      | t -> Some t

    let bind ~deterministic binds v t = T.assign v t; v::binds

    let cardinal binds = binds, (-1)

    let pp_bindings _ = "<< no way to print >>"
        
    let filter f _ = assert false (* TODO assign None *)

    (* TODO Cut&paste code :-( *)
    let deref _ =
     let rec deref i =
       match i with
         (T.Var v) ->
           (* Inlining of lookup! *)
           (match T.deref v with
              T.Var v' when T.eq_var v v' -> i
            | t -> deref t)
       | T.App(_,_) -> i
    in
     deref

    let backtrack ~current ~previous =
     let rec aux current =
      if current == previous then previous
      else
       match current with
          [] -> assert false        
        | (args,i)::tl ->
           args.(i) <- T.Var (args,i);
           aux tl
     in
      aux current
 end;;


module RefreshableTerm(Func:Lprun2.FuncT) : Lprun2.RefreshableTermT
  with type term = AST(Func).term 
  and  type clause = AST(Func).term * AST(Func).term
  and  type bindings = Bindings(Func).bindings
=
 struct
   include AST(Func)

   type bindings = Bindings(Func).bindings
  
   let refresh bind l =
    let rec aux args l =
     function
       Var (a,i) as x when a.(i) != x ->
        (* Invariant: a variable never points to a variable *)
        aux [||] l a.(i)
     | Var v ->
        let l,v = refresh_var l v args in
        l, Var v
     | App(f,tl) ->
        let tl = Array.copy tl in
        let l = ref l in
        Array.iteri (fun i t -> let l',t' = aux tl !l t in l := l' ; tl.(i) <- t') tl ;
        !l, App(f,tl)
    in
     (* Invariant: a variable never points to a variable *)
     aux [||] l
   
   type clause = term * term

  (* let refresh_clause (hd,bo) =
     let l,hd = refresh empty_refresher hd in
     let _,bo = refresh l bo in
     (hd,bo)
*)
   let refresh_head_of_clause (hd,bo) =
     let l,hd = refresh [] empty_refresher hd in
     l,(hd,bo)

   let refresh_body_of_clause binds l bo =
     let _,bo = refresh [] l bo in
     l,bo

   let refresh_query q = snd (refresh [] empty_refresher q)

 end;;

module HashableTerm(Func:Lprun2.FuncT)(Bind:Lprun2.BindingsT with type term = AST(Func).term) : Lprun2.HashableTermT
  with type term = AST(Func).term
  and  type bindings = Bind.bindings
=
 struct
   module AST = AST(Func)
   type term = AST.term
   module IndexData =
     struct
       type t = Func.t
       let equal = Func.eq
       let hash = Hashtbl.hash
     end
   
   type bindings = Bind.bindings

   (* TODO: use the bindings here!*)
   let index binds =
   function
      AST.App(f,_) -> f
    | AST.Var _ -> raise (Failure "Ill formed program")
 end;;

module ApproximatableTerm(Func: Lprun2.FuncT)(Bind: Lprun2.BindingsT with type term = AST(Func).term and type var = AST(Func).vart) : Lprun2.ApproximatableTermT 
  with type term = AST(Func).term 
  and  type bindings = Bind.bindings
=
 struct
   module AST = AST(Func)

   type term = AST.term

   type approx = Func.t * (Func.t option)

   type bindings = Bind.bindings

   let approx bind =
    function
       AST.App(f,[||]) -> f,None
     | AST.Var _ -> raise (Failure "Ill formed program")
     | AST.App(f,a) ->
       (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
        match Bind.deref bind a.(0) with
           AST.Var _ -> f,None
         | AST.App(g,_) -> f, Some g

   let matchp app1 app2 =
    match app1,app2 with
       (f1,None),(f2,_)
     | (f1,_),(f2,None)-> f1=f2
     | (f1,Some g1),(f2,Some g2) -> f1=f2 && g1=g2
 end

module Unify(Func: Lprun2.FuncT)(R: sig type refresher end)(Bind: Lprun2.BindingsT with type term = AST(Func).term and type var = AST(Func).vart) : Lprun2.UnifyT
   with type term := AST(Func).term
   and  type bindings = R.refresher * Bind.bindings

=
  struct
    type bindings = R.refresher * Bind.bindings
    type term = AST(Func).term
    module T = AST(Func)
    (*module Bind = Bind*)

    let rec unify ~deterministic sub t1 t2 = 
      match t1,t2 with
        (T.Var v1, T.Var v2) when T.eq_var v1 v2 -> sub
      | (T.Var v1, _) ->
          (match Bind.lookup sub v1 with
             None -> Bind.bind ~deterministic sub v1 t2
           | Some t -> unify ~deterministic sub t t2)
      | (_, T.Var _) -> unify ~deterministic sub t2 t1
      | (T.App (f1,l1), T.App (f2,l2)) -> 
          if Func.eq f1 f2 && Array.length l1 = Array.length l2 then
            array_fold_left2 (unify ~deterministic) sub l1 l2
          else
            raise (Lprun2.NotUnifiable (lazy "Terms are not unifiable!"))

    (* TODO: find a better abstraction *)
    let unify ~deterministic (e,sub) t1 t2 =
     e, unify ~deterministic sub t1 t2
   end;;

let implementations = 
  let impl1 =
    (* RUN with non indexed engine *)
    let module IBind = Bindings(Lprun2.FuncS) in
    let module IFormula = Formula(Lprun2.FuncS)(IBind) in
    let module IParsable = Parsable(Lprun2.FuncS) in
    let module ITerm = RefreshableTerm(Lprun2.FuncS) in
    let module IProgram = Lprun2.Program(IBind) in
    let module IRun = Lprun2.Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(Lprun2.FuncS)(ITerm)(IBind))(Lprun2.NoGC(IBind)) in
    let module Descr = struct let descr = "Testing with no index, optimized imperative " end in
    (module Lprun2.Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
     : Parser.Implementation) in


  let impl2 =
    (* RUN with hashtbl *)
    let module IBind = Bindings(Lprun2.FuncS) in
    let module IFormula = Formula(Lprun2.FuncS)(IBind) in
    let module IParsable = Parsable(Lprun2.FuncS) in
    let module ITerm = RefreshableTerm(Lprun2.FuncS) in
    let module IIndTerm = HashableTerm(Lprun2.FuncS)(IBind) in
    let module IProgram = Lprun2.ProgramHash(IIndTerm)(IBind) in
    let module IRun = Lprun2.Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(Lprun2.FuncS)(ITerm)(IBind))(Lprun2.NoGC(IBind)) in
    let module Descr = struct let descr = "Testing with one level index, optimized imperative " end in
    (module Lprun2.Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
     : Parser.Implementation) in

  let impl3 =
    (* RUN with two level inefficient index *)
    let module IBind = Bindings(Lprun2.FuncS) in
    let module IFormula = Formula(Lprun2.FuncS)(IBind) in
    let module IParsable = Parsable(Lprun2.FuncS) in
    let module ITerm = RefreshableTerm(Lprun2.FuncS) in
    let module IIndTerm = ApproximatableTerm(Lprun2.FuncS)(IBind) in
    let module IProgram = Lprun2.ProgramIndexL(IIndTerm)(IBind) in
    let module IRun = Lprun2.Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(Lprun2.FuncS)(ITerm)(IBind))(Lprun2.NoGC(IBind)) in
    let module Descr = struct let descr = "Testing with two level inefficient index, optimized imperative " end in
    (module Lprun2.Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
     : Parser.Implementation) in

  [impl1; impl2; impl3]
