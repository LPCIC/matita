(***** library functions *****)
        
(*val filter_map : ('a -> 'b option) -> 'a list -> 'b list*)
let rec filter_map mapf =
 function
    [] -> []
  | hd::tl ->
     match mapf hd with
        None -> filter_map mapf tl
      | Some hd' -> hd'::filter_map mapf tl

(***** real code *****)

exception NotFormula of string Lazy.t;;

module type Refreshable =
  sig        
    type r
    type refresher
    val empty_refresher : refresher
    val refresh : refresher -> r -> refresher * r
  end;;

module type ASTFuncT =
  sig
    type t
    val pp : t -> string
    val eq : t -> t -> bool
    val andf : t
    val orf : t
    val cutf : t
    val eqf : t
    val from_string : string -> t
  end;;

module ASTFuncS : ASTFuncT = 
  struct
    type t = string

    (* Hash consing *)
    let from_string =
     let h = Hashtbl.create 37 in
     function x ->
      try Hashtbl.find h x
      with Not_found -> Hashtbl.add h x x ; x

    let pp n = n
    let eq = (==)
    let andf = from_string ","
    let orf = from_string ";"
    let cutf = from_string "!"
    let eqf = from_string "="

  end;;

module type FuncT =
 sig
  include ASTFuncT

  val funct_of_ast : ASTFuncS.t -> t
 end

module FuncS : FuncT = 
 struct
  include ASTFuncS

  let funct_of_ast x = x
 end

module type VarT =
  sig
    type t
    val pp : t -> string
    val compare : t -> t -> int
    val eq : t -> t -> bool
    include Refreshable with type r := t
    val fresh : unit -> t
  end;;

module Variable : VarT = 
  struct
    type t = int
    let pp n = "X" ^ string_of_int n
    let compare = compare
    let eq = (=)
    type refresher = (int * int) list
    let empty_refresher = []

    let fresh,refresh =
      let maxvar = ref 0 in
        let fresh () = incr maxvar; !maxvar in
          fresh,
          (fun l n ->
             try l,List.assoc n l
             with Not_found ->
              let n' = fresh () in
             (n,n')::l,n')
  end;;

module ImpVariable : VarT with type t = Obj.t option ref = 
   struct
        type t = Obj.t option ref

        (* Extremely dirt hack to implement the pp *)
        type term =
           Var of t 
         | App of FuncS.t * term list
        let rec pp_term =  (* cut&paste code *)
          function
            Var v -> pp v
          | App (f,l) -> 
              if f = FuncS.andf then
              String.concat ", " (List.map pp_term l)
             else if f = FuncS.orf then
               "(" ^ String.concat "; " (List.map pp_term l) ^ ")"
             else if f = FuncS.cutf then "!" 
             else "(" ^ String.concat " "
              (FuncS.pp f :: List.map pp_term l) ^ ")"
        and pp v =
         match !v with
            None -> "?" ^ string_of_int (Obj.magic v)
          | Some t -> "<" ^ pp_term (Obj.magic t) ^ ">"

        let compare x y = assert false
        let eq = (==)

        type refresher = (Obj.t option ref * Obj.t option ref) list
        let empty_refresher = []

        let fresh,refresh =
         let fresh () = ref None in
          fresh,
          (fun l n ->
            try l,List.assq n l
            with Not_found ->
             let n' = fresh () in
             (n,n')::l,n')
   end;;

module type WeakVarT =
   sig
        type t = Box of int
        val pp : t -> string
        (* Compare and eq are useless since we exposed
           the implementation of t. The alternative is to
           export another type t' and the bijection between
           t and t'. *)
        val compare : t -> t -> int
        val eq : t -> t -> bool
        include Refreshable with type r := t
        val fresh : unit -> t
        val to_be_dropped: int list ref
   end;;

module WeakVariable : WeakVarT = 
  struct
    type t = Box of int
    let pp (Box n) = "X" ^ string_of_int n
    let compare = compare
    let eq = (=)
    let to_be_dropped = ref [];;
  
    type refresher = (int * t) list
    let empty_refresher = []

    let fresh,refresh =
      let maxvar = ref 0 in
      let fresh () =
       incr maxvar;
(*prerr_endline ("Fresh variable: " ^ string_of_int !maxvar);*)
       let v = Box !maxvar in
       Gc.finalise (fun (Box n) ->
        (*prerr_endline ("#@@ " ^ string_of_int n);*)
        to_be_dropped := n::!to_be_dropped) v;
       v
      in
       fresh,
       (fun l (Box n) ->
         try l,List.assoc n l
         with Not_found ->
          let n' = fresh () in
(*prerr_endline ("Refresh variable: " ^ string_of_int n ^ " to " ^ string_of_int (let Box n = n' in n));*)
          (n,n')::l,n')
  end;;

module type ASTT =
  sig  
    type vart
    type funct
    type term = Var of vart 
              | App of funct * term list

    val mkCut : term
    val mkAnd : term list -> term
    val mkOr : term list -> term
    val mkEq : term -> term -> term

    val pp: term -> string
  end;;

module AST(Var: VarT)(Func: ASTFuncT) : ASTT 
    with type vart = Var.t and type funct = Func.t 
 = 
  struct
    type vart = Var.t
    type funct = Func.t

    type term = Var of Var.t 
              | App of Func.t * term list

    let mkAnd = function [f] -> f | l -> App(Func.andf,l)
    let mkOr  = function [f] -> f | l -> App(Func.orf, l)
    let mkCut = App(Func.cutf,[]) 
    let mkEq l r = App(Func.eqf,[l;r]) 

    
    let rec pp =
      function
        Var v -> Var.pp v
      | App (f,l) -> 
          if f = Func.andf then
          String.concat ", " (List.map pp l)
         else if f = Func.orf then
           "(" ^ String.concat "; " (List.map pp l) ^ ")"                 
           else if f = Func.cutf then
             "!" 
             else "(" ^ String.concat " " (Func.pp f :: List.map pp l) ^ ")"
  end;;

module FOAST = AST(Variable)(ASTFuncS)

module type FormulaT =
  sig  
    type term
    type bindings

    type formula =
       Cut
     | Atom of term
     | And of term list

    val mkAnd : term list -> term

    (* raise NotAFormula *)
    val as_formula: bindings -> term -> formula

    val pp: term -> string
  end;;


module type BindingsT =
  sig
    type var
    type term
    type bindings

    val imperative : bool

    val deref : bindings -> term -> term

    val pp_bindings : bindings -> string
    val cardinal : bindings -> bindings * int
    val empty_bindings: bindings

    (* clean_trail is called by cut when the orl becomes empty.
       If the bindings contain the trail, the trail can be forgot
       because no backtracking will occur. *)
    val clean_trail : bindings -> bindings

    val backtrack: current:bindings -> previous:bindings -> bindings

    (** For Unification *)
    (* bind deterministic sigma v t = sigma [v |-> t] *)
    val bind : deterministic:bool -> bindings -> var -> term -> bindings
    (* lookup sigma v = Some t   iff  [v |-> t] \in sigma *)
    val lookup : bindings -> var -> term option

    (** For GC *)
    val filter : (var -> bool) -> bindings -> bindings
  end;;

module Formula(Var: VarT)(Func: ASTFuncT)(Bind: BindingsT with type term = AST(Var)(Func).term) : FormulaT 
    with type term = AST(Var)(Func).term
    and  type bindings = Bind.bindings
 = 
  struct
    module AST = AST(Var)(Func)

    type term = AST.term
    type bindings = Bind.bindings

    let pp = AST.pp

    type formula =
       Cut
     | Atom of term
     | And of term list

    let mkAnd = AST.mkAnd
    
     (* raise NotAFormula *)
    let as_formula binds t =
     (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
     match Bind.deref binds t with
        AST.Var _ -> raise (NotFormula (lazy "Trying to prove a variable"))
      | AST.App(f,l) as x->
         (* And [] is interpreted as false *)
         if Func.eq f Func.andf then And l
         (* Or [] is interpreted as true *)
         else if Func.eq f Func.cutf then Cut
         else Atom x
  end;;


module Bindings(Vars: VarT)(Func: FuncT) : BindingsT 
  with type var = Vars.t
  and type term = AST(Vars)(Func).term
  =
   struct
     type var = Vars.t
     type term = AST(Vars)(Func).term

     let imperative = false

     module MapVars = Map.Make(Vars)
     module VarSet = Set.Make(Vars)
     module Terms = AST(Vars)(Func)
 
     type bindings = Terms.term MapVars.t
     let empty_bindings = MapVars.empty

     let clean_trail bind = bind
     
     let backtrack ~current ~previous = previous
        
     let lookup bind k =
       try Some (MapVars.find k bind)
       with Not_found -> None

     let bind ~deterministic bind k v = MapVars.add k v bind

     let cardinal bind = bind, MapVars.cardinal bind

     let pp_bindings bind =
      String.concat "\n"
       (MapVars.fold
         (fun k v s -> (Vars.pp k ^ " |-> " ^ Terms.pp v) :: s)
         bind [])

     let filter f bind = MapVars.filter (fun k _ -> f k) bind 

     (* TODO Cut&paste code :-( *)
     let rec deref bind i =
       match i with
         (Terms.Var v) ->
           (match lookup bind v with
              None -> i
           | Some t -> deref bind t)
       | Terms.App(_,_) -> i
   end;;

module type ParsableT =
 sig
  type term
  type clause
  val query_of_ast : FOAST.term -> term
  val program_of_ast : (FOAST.term * FOAST.term) list -> clause list
 end

module Parsable(Var: VarT)(Func: FuncT): ParsableT
 with type term := AST(Var)(Func).term
 and  type clause = AST(Var)(Func).term * AST(Var)(Func).term =
 struct
  module AST = AST(Var)(Func)

  type clause = AST.term * AST.term

  (* Note: converters from asts are the same as
     refreshers, but both have fixed types :-(
     Should be made parametric *)
  let var_of_ast l n =
   try l,List.assoc n l
   with Not_found ->
    let n' = Var.fresh () in
    (n,n')::l,n'

  let rec term_of_ast l =
   function
      FOAST.Var v ->
       let l,v = var_of_ast l v in
       l, AST.Var v
    | FOAST.App(f,tl) ->
       let l,rev_tl =
         List.fold_left
          (fun (l,tl) t -> let l,t = term_of_ast l t in (l,t::tl))
          (l,[]) tl
       in
       l, AST.App(Func.funct_of_ast f,List.rev rev_tl)

  let query_of_ast t = snd (term_of_ast [] t)

  let program_of_ast p =
   List.map (fun (a,f) ->
    let l,a = term_of_ast [] a in
    let _,f = term_of_ast l f in
    a,f) p
 end

module type RefreshableTermT =
  sig
    type term
    type clause
    type refresher

    val refresh_head_of_clause : clause -> refresher * clause
    val refresh_body_of_clause : refresher -> term -> refresher * term
  end

module RefreshableTerm(Var:VarT)(Func:FuncT) : RefreshableTermT
  with type term = AST(Var)(Func).term and type clause = AST(Var)(Func).term * AST(Var)(Func).term
=
 struct
   include AST(Var)(Func)
   type refresher = Var.refresher
   let empty_refresher = Var.empty_refresher
 
   let rec refresh l =
     function
       Var v ->
        let l,v = Var.refresh l v in
        l, Var v
     | App(f,tl) ->
        let l,rev_tl =
          List.fold_left
           (fun (l,tl) t -> let l,t = refresh l t in (l,t::tl))
           (l,[]) tl
        in
        l, App(f,List.rev rev_tl)
   
  
   type clause = term * term

   let refresh_head_of_clause (hd,bo) =
     let l,hd = refresh empty_refresher hd in
     l,(hd,bo)

   let refresh_body_of_clause l bo =
     let _,bo =  refresh l bo in
     l,bo

 end;;


module type HashableTermT =
  sig
    type term
    type bindings
    module IndexData : Hashtbl.HashedType 
    val index: bindings -> term -> IndexData.t
  end;;


module HashableTerm(Var:VarT)(Func:FuncT)(Bind:BindingsT with type term = AST(Var)(Func).term) : HashableTermT
  with type term = AST(Var)(Func).term 
  and  type bindings = Bind.bindings
=
 struct
   module AST = AST(Var)(Func)
   type term = AST.term
   module IndexData =
     struct
       type t = Func.t
       let equal = Func.eq
       let hash = Hashtbl.hash
     end
   
   type bindings = Bind.bindings

   let index bind t =
    (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
    match Bind.deref bind t with
       AST.App(f,_) -> f
     | AST.Var _ -> raise (Failure "Ill formed program")
 end;;



module type MapableTermT =
 sig
  type term
  type bindings

  type clause

  val head : clause -> term
  val body : clause -> term

  module IndexData : Map.OrderedType 
  val index: bindings -> term -> IndexData.t
 end;;


module MapableTerm(Var: VarT)(Func: FuncT)(Bind:BindingsT with type term = AST(Var)(Func).term) : MapableTermT
  with type term = AST(Var)(Func).term 
  and  type bindings = Bind.bindings
  and type clause = AST(Var)(Func).term * AST(Var)(Func).term
=
 struct
  module AST = AST(Var)(Func)
  type term = AST.term
  type clause = term * term

  let head = fst
  let body = snd

  module IndexData =
   struct
    type t = Func.t
    let equal = Func.eq
    let compare n1 n2 = String.compare (Func.pp n1) (Func.pp n2)
   end

  type bindings = Bind.bindings

  let index bind t =
    (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
    match Bind.deref bind t with
       AST.App(f,_) -> f
     | AST.Var _ -> raise (Failure "Ill formed program")  
 end;;


module ImpBindings(Func: FuncT) : 
 BindingsT 
  with type var = ImpVariable.t
  and type term = AST(ImpVariable)(Func).term
  =
   struct
     module T = AST(ImpVariable)(Func)
     type var = ImpVariable.t
     type term = T.term

     let imperative = true

     type bindings = var list (* This is the trail *)

     let empty_bindings = []

     let clean_trail _ = empty_bindings
        
     let lookup _ k = Obj.magic !k

     let bind ~deterministic binds k v =
      k := Some (Obj.magic v) ;
      if deterministic then binds else k::binds

     let cardinal binds = binds, (-1)

     let pp_bindings _ = "<< no way to print >>"
        
     let filter f _ = assert false (* TODO assign None *)

     let deref _ =
      let rec deref i =
        match i with
          (T.Var v) ->
            (match Obj.magic !v (* Inlining of lookup! *) with
               None -> i
            | Some t -> deref t)
        | T.App(_,_) -> i
     in
      deref

     let backtrack ~current ~previous =
      let rec aux current =
       if current == previous then previous
       else
        match current with
           [] -> [](*assert false*)
         | v::tl ->
            v := None;
            aux tl
      in
       aux current
   end;;



module type ApproximatableTermT =
  sig
    type term
    type approx
    type bindings
    val approx: bindings -> term -> approx
    val matchp: approx -> approx -> bool
  end;;

module ApproximatableTerm(Var: VarT)(Func: FuncT)(Bind: BindingsT with type var = Var.t and type term = AST(Var)(Func).term) :
 ApproximatableTermT 
  with type term = AST(Var)(Func).term 
  and  type bindings = Bind.bindings
=
 struct
   module AST = AST(Var)(Func)

   type term = AST.term

   type approx = Func.t * (Func.t option)

   type bindings = Bind.bindings

   let approx bind t =
    (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
    match Bind.deref bind t with
       AST.App(f,[]) -> f,None
     | AST.App(f,hd::_) -> 
         (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
         (match Bind.deref bind hd with
            AST.Var _-> f,None
          | AST.App(g,_) -> f,Some g)
     | AST.Var _ -> raise (Failure "Ill formed program")

   let matchp app1 app2 =
     match app1,app2 with
       (f1,None),(f2,_)
     | (f1,_),(f2,None)-> f1=f2
     | (f1,Some g1),(f2,Some g2) -> f1=f2 && g1=g2
  end;;


module type DoubleMapIndexableTermT =
 sig
  include MapableTermT
  type approx (* 2nd layer approximation *)
  val approx: bindings -> term -> approx
  val matchp: approx -> approx -> bool
 end
;;

module DoubleMapIndexableTerm(Var: VarT)(Func: FuncT)(Bind: BindingsT with type var = Var.t and type term = AST(Var)(Func).term) : DoubleMapIndexableTermT
  with type term = AST(Var)(Func).term 
  and type bindings = Bind.bindings
  and type clause = MapableTerm(Var)(Func)(Bind).clause
=
 struct
   include MapableTerm(Var)(Func)(Bind)
   module AST = AST(Var)(Func)

   type approx = Func.t option

   let approx bind t =
    (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
    match Bind.deref bind t with
       AST.App(_,[]) -> None
     | AST.App(_,hd::_) ->
         (* TODO: COMPARE WITH THE ETA-EXPANSION OF THE CODE BELOW *)
        (match Bind.deref bind hd with
            AST.Var _-> None
          | AST.App(g,_) -> Some g)
     | AST.Var _ -> raise (Failure "Ill formed program")

   let matchp app1 app2 =
     match app1,app2 with
       None,_
     | _,None-> true
     | Some g1,Some g2 -> g1=g2

 end;;




module WeakBindings(Vars: WeakVarT)(Func: FuncT) : BindingsT 
  with type var = Vars.t
  and  type term = AST(Vars)(Func).term
 =
  struct
    type var = Vars.t
    type term = AST(Vars)(Func).term

    let imperative = false

    module MapVars = Map.Make(struct type t = int let compare = compare let eq = (=) end)
    module Terms = AST(Vars)(Func)
    type bindings = Terms.term MapVars.t

    let empty_bindings = MapVars.empty

    let clean_trail bind = bind

    let backtrack ~current ~previous = previous

    let pp_bindings bind =
    (*Gc.compact();
      let bind = clean bind in*)
      String.concat "\n"
        (MapVars.fold
          (fun k v s -> (Vars.pp (Vars.Box k) ^ " |-> " ^ Terms.pp v) :: s)
            bind [])

    let rec clean bind =
      (* Gc.compact (); *)
      let tbr = !Vars.to_be_dropped in
        Vars.to_be_dropped := [];
         if tbr = [] then bind 
         else (
          (*prerr_endline ("Maps before removal:");
          prerr_endline (pp_bindings bind);*)
           let bind =
             List.fold_left (fun bind n ->
              MapVars.remove n bind) bind tbr in
            (*prerr_endline ("Maps after removal:");
            prerr_endline (pp_bindings bind);*)
               clean bind)

    let lookup bind (Vars.Box k) =
      (*let bind = clean bind in*)
      try Some (MapVars.find k bind)
        with Not_found -> None

    let bind ~deterministic bind (Vars.Box k) v = MapVars.add k v (clean bind)

    let cardinal bind =
      let bind = clean bind in
        bind,MapVars.cardinal bind

    let filter f bind = MapVars.filter (fun k _ -> f (Vars.Box k)) bind 

     (* TODO Cut&paste code :-( *)
     let rec deref bind i =
       match i with
         (Terms.Var v) ->
           (match lookup bind v with
              None -> i
           | Some t -> deref bind t)
       | Terms.App(_,_) -> i
  end;;



module type UnifyT =
  sig
   type term
   type bindings
   (* unify sub t1 t2 = sub'  iff  t1 sub' = t2 sub' and sub <= sub' *)
    val unify:
     deterministic:bool -> bindings -> term -> term -> bindings         
  end;;

exception NotUnifiable of string Lazy.t

module Unify(Var: VarT)(Func: FuncT)(R: sig type refresher end)(Bind: BindingsT with type term = AST(Var)(Func).term and type var = Var.t) : UnifyT
   with type term := AST(Var)(Func).term
   and type bindings = R.refresher * Bind.bindings
=
  struct
    module T = AST(Var)(Func)

    type bindings = R.refresher * Bind.bindings

    let rec unify ~deterministic sub t1 t2 = 
      match t1,t2 with
        (T.Var v1, T.Var v2) when Var.eq v1 v2 -> sub
      | (T.Var v1, _) ->
          (match Bind.lookup sub v1 with
             None -> Bind.bind ~deterministic sub v1 t2
           | Some t -> unify ~deterministic sub t t2)
      | (_, T.Var _) -> unify ~deterministic sub t2 t1
      | (T.App (f1,l1), T.App (f2,l2)) -> 
          if Func.eq f1 f2 && List.length l1 = List.length l2 then
            List.fold_left2 (unify ~deterministic) sub l1 l2
          else
            raise (NotUnifiable (lazy "Terms are not unifiable!"))

    (* TODO: find a better abstraction *)
    let unify ~deterministic (e,sub) t1 t2 =
     e, unify ~deterministic sub t1 t2
   end;;


module FlatUnify(Var: VarT)(Func: FuncT)(R: sig type refresher end)(Bind: BindingsT with type term = AST(Var)(Func).term and type var = Var.t) : UnifyT
  with type term := AST(Var)(Func).term
  and type bindings = R.refresher * Bind.bindings
=
   struct
     module T = AST(Var)(Func)

     type bindings = R.refresher * Bind.bindings

     let rec flatten sub i =
       match i with
         (T.Var _) -> Bind.deref sub i
       | T.App(f,l) ->
          let l' = List.map (flatten sub) l in
           if l'==l then i else T.App(f, l')

     (* unify sub pattern query
        the query is only dereferences
        the pattern is fully flattened, i.e. recursively dereferenced
        the rationale is that patterns are small, queries can be huge
        flattening queries leads to quadratic complexity on our example
        because the same input can be flattened multiple times *)
     let rec unify ~deterministic ~do_flatten sub t1 t2 = match t1,t2 with
       (T.Var v1, T.Var v2) when Var.eq v1 v2 -> sub
     | (T.App (f1,l1), T.App (f2,l2)) -> 
         if Func.eq f1 f2 && List.length l1 = List.length l2 then
           List.fold_left2 (unify ~deterministic ~do_flatten) sub l1 l2
         else
           raise (NotUnifiable (lazy "Terms are not unifiable!"))
     | (T.Var _, _)
     | (_, T.Var _) ->
       (* TODO: COMPARE WITH THE ETA-EXPANSION OF DEREF BELOW *)
       let t1 = (if do_flatten then flatten else Bind.deref) sub t1 in
       let t2 = (if do_flatten then flatten else Bind.deref) sub t2 in
       match t1,t2 with
         (T.Var v1, T.Var v2) when Var.eq v1 v2 -> sub
       | (T.Var v1, _) -> Bind.bind ~deterministic sub v1 t2
       | (_, T.Var v2) -> Bind.bind ~deterministic sub v2 t1
       | (T.App _, T.App _) -> unify ~deterministic ~do_flatten:false sub t1 t2

     (* TODO: find a better abstraction *)
     let unify ~deterministic (e,sub) t1 t2 =
      e, unify ~do_flatten:true ~deterministic sub t1 t2
   end;;

module type GCT =
 sig
  type bindings
  type term
  val gc: force:bool -> bindings -> term list -> bindings
 end;;

module NoGC(Bind: BindingsT) :
 GCT with type bindings := Bind.bindings
     and  type term := Bind.term =
 struct
  let gc ~force binds _ = binds
 end

module GC(Var: VarT)(Func: FuncT)(Bind: BindingsT with type term := AST(Var)(Func).term and type var := Var.t) :
 GCT with type bindings := Bind.bindings
     and type term := AST(Var)(Func).term 
=
 struct
  
  module Term = AST(Var)(Func);;
  open Term

  module VarSet = Set.Make(Var);;
    let rec findVarsTerm =
     function
      Var(x) -> VarSet.singleton x
    | App(_,args) -> 
        List.fold_left 
          (fun acc term -> 
             VarSet.union (findVarsTerm term) acc) VarSet.empty args

    let find_vars_fla = findVarsTerm

    let one_level_bind_chain binds ivars =
      let visited = ref VarSet.empty in
      let vars = ref ivars in
      while not (VarSet.is_empty !vars) do
        let v = VarSet.choose !vars in
        vars := VarSet.remove v !vars ;
        visited := VarSet.add v !visited ;
        match Bind.lookup binds v with
          Some t ->
           let vset = findVarsTerm t in
           VarSet.iter
            (fun x ->
              if not (VarSet.mem x !visited) then vars:= VarSet.add x !vars)
            vset
        | None -> ()
      done ;
      !visited

   let do_gc binds andl =
    let vars = 
     List.fold_left 
      (fun acc fla ->
        VarSet.union acc (find_vars_fla fla)) VarSet.empty andl in
    let reachable_vars = one_level_bind_chain binds vars in
    Bind.filter (fun x -> VarSet.mem x reachable_vars) binds

   let gc ~force =
    let do_it = ref false in
    ignore (Gc.create_alarm (fun () -> do_it := true));
    fun binds andl ->
     if !do_it || force then (
      do_it := false ;
      do_gc binds andl )
     else binds
  end



module type ProgramT =
 sig
  type term
  type bindings
  type t
  type clause

  val head : clause -> term
  val body : clause -> term

  val get_clauses: bindings -> term -> t -> clause list
  val make: clause list -> t
 end

(* No indexing at all; a program is a list and retrieving the clauses
   from the program is O(n) where n is the size of the program.
   Matching is done using unification directly. *)
module Program(Bind: BindingsT) : ProgramT
 with type term := Bind.term
 and  type bindings := Bind.bindings
 and  type clause = Bind.term * Bind.term =
  struct
    type clause = Bind.term * Bind.term
    type t = clause list

    let head = fst
    let body = snd

    let get_clauses _ _ l = l

    let make p = p;;
  end;;



(* One level indexing; a program is a hash-table indexed on the
   predicate that is the head of the clause. Unification is used
   eagerly on all the clauses with the good head. Retrieving the
   clauses is O(n) where n is the number of clauses with the
   good head. *)
module ProgramHash(Term: HashableTermT)(Bind : BindingsT with type term = Term.term and type bindings = Term.bindings) : ProgramT
 with type term := Term.term
 and  type bindings := Term.bindings
 and  type clause = Term.term*Term.term
 =   
   struct
     (* Atom.t -> (Atom.t*Form.formula) list *)
     module Hash = Hashtbl.Make(Term.IndexData)
     type clause = Term.term*Term.term
     type t = clause Hash.t

     let head = fst
     let body = snd
                      
     let get_clauses binds a h =
      List.rev (Hash.find_all h (Term.index binds a))
       
     let make p =
      let h = Hash.create 199 in
      List.iter
       (fun ((a,v) as clause) ->
         Hash.add h (Term.index Bind.empty_bindings a) clause) p;
      h
   end;; 


(* 2-level indexing; a program is a hash-table indexed on the
   predicate that is the head of the clause and an associative
   list on the first argument. Unification is used
   eagerly on all the clauses with the good head and first argument.
 *)
module ProgramDoubleInd(Term: DoubleMapIndexableTermT)(Bind : BindingsT with type term = Term.term and type bindings = Term.bindings) : ProgramT
 with type term := Term.term
 and  type bindings := Term.bindings
 and  type clause = Term.clause
 =   
   struct
     (* Atom.t -> (Atom.t*Form.formula) list *)
	  module ClauseMap = Map.Make(Term.IndexData)
     type clause = Term.clause
     type t = (Term.approx * clause) list ClauseMap.t

     let head = Term.head
     let body = Term.body

     let get_clauses binds a m =
      let app = Term.approx binds a in
      let l = List.rev (ClauseMap.find (Term.index binds a) m) in
       filter_map
        (fun (a',cl) -> if Term.matchp app a' then Some cl else None) l
        
     let make p =       
       List.fold_left (fun m clause -> 
         let a = head clause in
         let ind = Term.index Bind.empty_bindings a in
         let app = Term.approx Bind.empty_bindings a in
         try 
           let l = ClauseMap.find ind m in
           ClauseMap.add ind ((app,clause) :: l) m
         with Not_found -> 
           ClauseMap.add ind [app,clause] m
         ) ClauseMap.empty p

   end;; 



(* Two level inefficient indexing; a program is a list of clauses.
   Approximated matching is used to retrieve the candidates.
   Unification is then performed on the candidates.
   *** NOTE: this is probably redundant and more inefficient than
       just doing eager unification without approximated matching ***
   Retrieving the good clauses is O(n) where n is the size of the
   program. *)
module ProgramIndexL(Term: ApproximatableTermT)(Bind : BindingsT with type term = Term.term and type bindings = Term.bindings) : ProgramT
 with type term := Term.term
 and  type bindings := Term.bindings
 and  type clause = Term.term*Term.term
 =
   struct
     type clause = Term.term*Term.term
     (* triples (app,(a,f)) where app is the approximation of a *)
     type t = (Term.approx * clause) list

     let head = fst
     let body = snd

     let get_clauses binds a l =
      let app = Term.approx binds a in
       filter_map
        (fun (a',cl) -> if Term.matchp app a' then Some cl else None) l
        
     let make =
      List.map (fun ((a,_) as clause) ->
       Term.approx Bind.empty_bindings a,clause)
   end;;


(* One level indexing; a program is a Map indexed on the
   predicate that is the head of the clause. Unification is used
   eagerly on all the clauses with the good head. *)
module ProgramMap(Term: MapableTermT)(Bind : BindingsT with type term = Term.term and type bindings = Term.bindings) : ProgramT
 with type term := Term.term
 and  type bindings := Term.bindings
 and  type clause = Term.term*Term.term
 =
   struct
     (* Atom.t -> (Atom.t*Form.formula) list *)
	  module ClauseMap = Map.Make(Term.IndexData)
     type clause = Term.term*Term.term
     type t = clause list ClauseMap.t

     let head = fst
     let body = snd

     let get_clauses binds a m =
      List.rev (ClauseMap.find (Term.index binds a) m)
        
     let make p =       
       List.fold_left (fun m ((a,_) as clause) -> 
         let ind = Term.index Bind.empty_bindings a in
         try 
           let l = ClauseMap.find ind m in
           ClauseMap.add ind (clause :: l) m
         with Not_found -> 
           ClauseMap.add ind [clause] m
         ) ClauseMap.empty p
   end;;

module type RunT =
 sig
  type term
  type progT
  type cont (* continuation *)
  val run: progT -> term -> cont option
  val next: cont -> cont option
  val main_loop: progT -> term -> unit
 end

module Run(Term: RefreshableTermT)(Form: FormulaT with type term := Term.term)(Prog: ProgramT with type term := Term.term and type clause = Term.clause and type bindings := Form.bindings)(Bind : BindingsT with type term := Term.term and type bindings := Form.bindings)(Unify: UnifyT with type bindings = Term.refresher * Form.bindings and type term := Term.term)(GC : GCT with type term := Term.term and type bindings := Form.bindings) : RunT
 with type term := Term.term
 and type progT := Prog.t
 = 
  struct 
    (* A cont is just the program plus the or list,
       i.e. a list of level * bindings * head of and_list * tl of and_list 
       The level is incremented when there is a backchain. *)
    type cont = 
      Prog.t * Form.bindings *
       (int * Form.bindings * Term.term * Term.clause * Term.term list) list

        (* WARNING: bad non reentrant imperative code here
           At least query should go into the continuation for next
           to work!
        *)
    let query = ref (Form.mkAnd [] (* True *))

    (* run0 lvl binds andl orl f
      (lvl,binds,(f::andl))::orl) *)
    let rec run0 prog lvl binds andl orl f =
     let binds = GC.gc false binds (!query::f::andl) in
     match Form.as_formula binds f with
        Form.And [] ->                  (* (True::andl)::orl *)
         (match andl with
             [] ->
               let binds = GC.gc true binds (!query::f::andl) in
               Some (prog,binds,orl)       (* (binds,[])::orl *)
             (* lvl-1 is because the body of a clause like a :- b,c.
                is represented as And(b,c) in the and list and not like
                b::c. Therefore an entry in the and list always
                is a stack frame for the body of a clause.
                An or expression is also to be thought as an anonymous
                clause invocation.
                Thus hd is the stack frame of the parent call, that was
                done at level lvl-1. *) 
           | hd::tl ->run0 prog (lvl-1) binds tl orl hd) (* (hd::tl)::orl *) 
      | Form.Cut ->
         let orl =
          (* We filter out from the or list every frame whose lvl
             is >= then ours. *)
          let rec filter =
           function
              [] -> []
            | ((lvl',_,_,_,_)::_) as l when lvl' < lvl -> l
            | _::tl -> filter tl
          in
           filter orl in
         let binds= if orl=[] then Bind.clean_trail binds else binds in
         (* cut&paste from True case *)
         (match andl with
             [] -> Some (prog,binds,orl)       (* (binds,[])::orl *)
           | hd::tl-> run0 prog (lvl-1) binds tl orl hd) (* (hd::tl)::orl *)
      | Form.Atom q ->         (*A::and)::orl)*)                       
          let l = Prog.get_clauses binds q prog in
          let orl =
           List.map
            (fun clause -> lvl+1,binds,q,clause,andl) l
            @ orl in
          next prog binds orl
      
      (* TODO: OPTIMIZE AND UNIFY WITH TRUE *)   
      | Form.And (f1::f2) ->             (* ((f1,f2)::andl)::orl *)
         let f2 = Form.mkAnd f2 in
         run0 prog lvl binds (f2::andl) orl f1  (* (f1::(f2::andl))::orl *)

    and next prog binds =
     function
         [] -> None
       | (lvl,bnd,query,clause,andl)::tl_orl ->
           let bnd =
            Bind.backtrack ~current:binds ~previous:bnd in
           let refresher,c = Term.refresh_head_of_clause clause in
           let atom = Prog.head c in
           let f = Prog.body c in
           (match
             try
              let deterministic = tl_orl=[] in
              let refresher,bnd =
               Unify.unify ~deterministic (refresher,bnd) query atom in
              let _,f = Term.refresh_body_of_clause refresher f in
              Some (f,bnd)
             with
              NotUnifiable _ -> None
            with
               Some (f,bnd) -> run0 prog lvl bnd andl tl_orl f
             | None -> next prog bnd tl_orl)

    let run_next prog lvl binds andl orl f =
      let time0 = Unix.gettimeofday() in
        let res = run0 prog lvl binds andl orl f in
        let time1 = Unix.gettimeofday() in
        prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
        (match res with
          Some (prog,binds,orl) ->
            Gc.full_major() ; let binds,size = Bind.cardinal binds in
            prerr_endline ("Final bindings size: " ^ string_of_int size) ;
              Some (prog,binds,orl)
           | None -> None)

    let run prog f =
      query := f ;
      run_next prog 0 (Bind.empty_bindings) [] [] f

    let main_loop prog query =
      let rec aux =
        function
          None -> prerr_endline "Fail"
        | Some (prog,bind,orl) ->
            prerr_endline ("Query: " ^ Form.pp query) ;
            prerr_endline (Bind.pp_bindings bind) ;
            prerr_endline "More? (Y/n)";
              if read_line() <> "n" then
                aux (next prog bind orl)
          in
        aux (run prog query)

     let next (prog,bind,orl) = next prog bind orl

     end;;

module EagerRun(Term: RefreshableTermT)(Form: FormulaT with type term := Term.term)(Prog: ProgramT with type term := Term.term and type clause = Term.clause and type bindings := Form.bindings)(Bind : BindingsT with type term := Term.term and type bindings := Form.bindings)(Unify: UnifyT with type bindings = Term.refresher * Form.bindings and type term := Term.term)(GC : GCT with type term := Term.term and type bindings := Form.bindings) : RunT
 with type term := Term.term
 and type progT := Prog.t
 = 
  struct 

    if Bind.imperative then
     prerr_endline ("WARNING: imperative implementation + eager unification is unsound.\n The interpreter will crash on non deterministic programs.")

    (* A cont is just the program plus the or list,
       i.e. a list of level * bindings * head of and_list * tl of and_list 
       The level is incremented when there is a *)
    type cont = 
      Prog.t * Form.bindings *
       (int * Form.bindings * Term.term * Term.term list) list

        (* WARNING: bad non reentrant imperative code here
           At least query should go into the continuation for next
           to work!
        *)
    let query = ref (Form.mkAnd [] (* True *))

    (* run0 lvl binds andl orl f
      (lvl,binds,(f::andl))::orl) *)
    let rec run0 prog lvl binds andl orl f =
     let binds = GC.gc false binds (!query::f::andl) in
     match Form.as_formula binds f with
        Form.And [] ->                  (* (True::andl)::orl *)
         (match andl with
             [] ->
               let binds = GC.gc true binds (!query::f::andl) in
               Some (prog,binds,orl)       (* (binds,[])::orl *)
             (* lvl-1 is because the body of a clause like a :- b,c.
                is represented as And(b,c) in the and list and not like
                b::c. Therefore an entry in the and list always
                is a stack frame for the body of a clause.
                An or expression is also to be thought as an anonymous
                clause invocation.
                Thus hd is the stack frame of the parent call, that was
                done at level lvl-1. *) 
           | hd::tl -> run0 prog (lvl-1) binds tl orl hd) (* (hd::tl)::orl *) 
      | Form.Cut ->
         let orl =
          (* We filter out from the or list every frame whose lvl
             is >= then ours. *)
          let rec filter =
           function
              [] -> []
            | ((lvl',_,_,(*_,*)_)::_) as l when lvl' < lvl -> l
            | _::tl -> filter tl
          in
           filter orl in
         (* cut&paste from True case *)
         (match andl with
             [] -> Some (prog,binds,orl)       (* (binds,[])::orl *)
           | hd::tl -> run0 prog (lvl-1) binds tl orl hd) (* (hd::tl)::orl *)
      | Form.Atom q ->         (*A::and)::orl)*)                       
          let l = Prog.get_clauses binds q prog in
          let already_kept = ref false in
          let orl =
           filter_map
            (fun clause ->
              if Bind.imperative && !already_kept then assert false ;
              let refresher,c = Term.refresh_head_of_clause clause in
              let atom = Prog.head c in
              let f = Prog.body c in
              try
               let refresher,bnd =
                Unify.unify ~deterministic:true (refresher,binds) atom q in
               let _,f = Term.refresh_body_of_clause refresher f in
               if Bind.imperative then already_kept := true ;
               Some (lvl+1,bnd,f,andl)
              with
               NotUnifiable _ -> None
            ) l @ orl in
          next prog binds orl
      
      (* TODO: OPTIMIZE AND UNIFY WITH TRUE *)   
      | Form.And (f1::f2) ->             (* ((f1,f2)::andl)::orl *)
         let f2 = Form.mkAnd f2 in
         run0 prog lvl binds (f2::andl) orl f1  (* (f1::(f2::andl))::orl *)

     and next prog binds =
      function
          [] -> None
        | (lvl,bnd,f,andl)::tl_orl -> run0 prog lvl bnd andl tl_orl f

    let run_next prog lvl binds andl orl f =
      let time0 = Unix.gettimeofday() in
        let res = run0 prog lvl binds andl orl f in
        let time1 = Unix.gettimeofday() in
        prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
        (match res with
          Some (prog,binds,orl) ->
            Gc.full_major() ; let binds,size = Bind.cardinal binds in
            prerr_endline ("Final bindings size: " ^ string_of_int size) ;
              Some (prog,binds,orl)
           | None -> None)

    let run prog f =
      query := f ;
      run_next prog 0 (Bind.empty_bindings) [] [] f

    let main_loop prog query =
      let rec aux =
        function
          None -> prerr_endline "Fail"
        | Some (prog,binds,orl) ->
            prerr_endline ("Query: " ^ Form.pp query) ;
            prerr_endline (Bind.pp_bindings binds) ;
            prerr_endline "More? (Y/n)";
              if read_line() <> "n" then
                aux (next prog binds orl)
          in
        aux (run prog query)

     let next (prog,bind,orl) = next prog bind orl

     end;;

module type Implementation =
 sig
  type query
  type program
  val query_of_ast : FOAST.term -> query
  val program_of_ast : (FOAST.term * FOAST.term) list -> program
  val msg : query -> string
  val execute_once : program -> query -> bool
  val execute_loop : program -> query -> unit
 end

module
 Implementation
  (IFormula: FormulaT)
  (ITerm: ParsableT with type term := IFormula.term)
  (IProgram: ProgramT with type term := IFormula.term
                      and  type bindings := IFormula.bindings
                      and  type clause = ITerm.clause)
  (IRun: RunT with type progT := IProgram.t
              and  type term := IFormula.term)
  (Descr : sig val descr : string end)
 : Implementation
=
 struct
  (* RUN with non indexed engine *)
  type query = IFormula.term
  type program = IProgram.clause list
  let query_of_ast = ITerm.query_of_ast
  let program_of_ast = ITerm.program_of_ast
  let msg q = Descr.descr ^ IFormula.pp q
  let execute_once p q = IRun.run (IProgram.make p) q = None
  let execute_loop p q = IRun.main_loop (IProgram.make p) q
 end
;;

(* implement the rest of the cases *)
let implementations = 
  let impl1 =
    (* RUN with non indexed engine *)
    let module IBind = Bindings(Variable)(FuncS) in
    let module IFormula = Formula(Variable)(FuncS)(IBind) in
    let module IParsable = Parsable(Variable)(FuncS) in
    let module ITerm = RefreshableTerm(Variable)(FuncS) in
    let module IProgram = Program(IBind) in
    let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(Variable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
    let module Descr = struct let descr = "Testing with no index list " end in
    (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
     : Implementation) in

let impl2 =
  (* RUN with indexed engine *)
  let module IBind = Bindings(Variable)(FuncS) in
  let module IFormula = Formula(Variable)(FuncS)(IBind) in
  let module IParsable = Parsable(Variable)(FuncS) in
  let module ITerm = RefreshableTerm(Variable)(FuncS) in
  let module IIndTerm = HashableTerm(Variable)(FuncS)(IBind) in
  let module IProgram = ProgramHash(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(Variable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl3 =
  (* RUN with two levels inefficient indexed engine *)
  let module IBind = Bindings(Variable)(FuncS) in
  let module IFormula = Formula(Variable)(FuncS)(IBind) in
  let module IParsable = Parsable(Variable)(FuncS) in
  let module ITerm = RefreshableTerm(Variable)(FuncS) in
  let module IIndTerm = ApproximatableTerm(Variable)(FuncS)(IBind) in
  let module IProgram = ProgramIndexL(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(Variable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with two level inefficient index " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl4 =
  let module IBind = Bindings(WeakVariable)(FuncS) in
  let module IFormula = Formula(WeakVariable)(FuncS)(IBind) in
  let module IParsable = Parsable(WeakVariable)(FuncS) in
  let module ITerm = RefreshableTerm(WeakVariable)(FuncS) in
  let module IIndTerm = HashableTerm(WeakVariable)(FuncS)(IBind) in
  let module IProgram = ProgramHash(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(WeakVariable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl and automatic GC " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in


let impl5 =
  (* RUN with indexed engine and automatic GC *)
  let module IBind = WeakBindings(WeakVariable)(FuncS) in
  let module IFormula = Formula(WeakVariable)(FuncS)(IBind) in
  let module IParsable = Parsable(WeakVariable)(FuncS) in
  let module ITerm = RefreshableTerm(WeakVariable)(FuncS) in
  let module IIndTerm = HashableTerm(WeakVariable)(FuncS)(IBind) in
  let module IProgram = ProgramHash(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(FlatUnify(WeakVariable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening and automatic GC " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in


let impl6 =
  (* RUN with indexed engine *)
  let module IBind = Bindings(Variable)(FuncS) in
  let module IFormula = Formula(Variable)(FuncS)(IBind) in
  let module IParsable = Parsable(Variable)(FuncS) in
  let module ITerm = RefreshableTerm(Variable)(FuncS) in
  let module IIndTerm = HashableTerm(Variable)(FuncS)(IBind) in
  let module IProgram = ProgramHash(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(FlatUnify(Variable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in


let impl7 =
  let module IBind = Bindings(Variable)(FuncS) in
  let module IFormula = Formula(Variable)(FuncS)(IBind) in
  let module IParsable = Parsable(Variable)(FuncS) in
  let module ITerm = RefreshableTerm(Variable)(FuncS) in
  let module IIndTerm = HashableTerm(Variable)(FuncS)(IBind) in
  let module IProgram = ProgramHash(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(FlatUnify(Variable)(FuncS)(ITerm)(IBind))(GC(Variable)(FuncS)(IBind)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening + manual GC " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl8 =
  (* RUN with indexed engine and Map of clauses instead of Hash of clauses*)
  let module IBind = Bindings(Variable)(FuncS) in
  let module IFormula = Formula(Variable)(FuncS)(IBind) in
  let module IParsable = Parsable(Variable)(FuncS) in
  let module ITerm = RefreshableTerm(Variable)(FuncS) in
  let module IIndTerm = MapableTerm(Variable)(FuncS)(IBind) in
  let module IProgram = ProgramMap(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(Variable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with one level index map " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl9 =
  (* RUN with indexed engine *)
  let module IBind = ImpBindings(FuncS) in
  let module IFormula = Formula(ImpVariable)(FuncS)(IBind) in
  let module IParsable = Parsable(ImpVariable)(FuncS) in
  let module ITerm = RefreshableTerm(ImpVariable)(FuncS) in
  let module IIndTerm = HashableTerm(ImpVariable)(FuncS)(IBind) in
  let module IProgram = ProgramHash(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(ImpVariable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with imperative one level index hashtbl " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl10 =
  (* RUN with indexed engine *)
  let module IBind = ImpBindings(FuncS) in
  let module IFormula = Formula(ImpVariable)(FuncS)(IBind) in
  let module IParsable = Parsable(ImpVariable)(FuncS) in
  let module ITerm = RefreshableTerm(ImpVariable)(FuncS) in
  let module IIndTerm = DoubleMapIndexableTerm(ImpVariable)(FuncS)(IBind) in
  let module IProgram = ProgramDoubleInd(IIndTerm)(IBind) in
  let module IRun = Run(ITerm)(IFormula)(IProgram)(IBind)(Unify(ImpVariable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with imperative two level efficient index " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl11 =
  (* RUN with indexed engine *)
  let module IBind = ImpBindings(FuncS) in
  let module IFormula = Formula(ImpVariable)(FuncS)(IBind) in
  let module IParsable = Parsable(ImpVariable)(FuncS) in
  let module ITerm = RefreshableTerm(ImpVariable)(FuncS) in
  let module IIndTerm = DoubleMapIndexableTerm(ImpVariable)(FuncS)(IBind) in
  let module IProgram = ProgramDoubleInd(IIndTerm)(IBind) in
  let module IRun = EagerRun(ITerm)(IFormula)(IProgram)(IBind)(Unify(ImpVariable)(FuncS)(ITerm)(IBind))(NoGC(IBind)) in
  let module Descr = struct let descr = "Testing with eager imperative two level efficient index " end in
  (module Implementation(IFormula)(IParsable)(IProgram)(IRun)(Descr)
  : Implementation) in


  [impl1;impl2;impl3;impl4;impl5;impl6;impl7;impl8;impl9;impl10;impl11]

include FOAST
