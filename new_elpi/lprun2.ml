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

        let pp _ = "??"
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

    type formula =
       Cut
     | Atom of term
     | And of term list
     | Or of term list

    val mkCut : term
    val mkAnd : term list -> term
    val mkOr : term list -> term
    val mkEq : term -> term -> term

    (* raise NotAFormula *)
    val as_formula: term -> formula

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

    type formula =
       Cut
    | Atom of term
    | And of term list
    | Or of term list

    let rec pp_term = 
      function 
        Var v -> Var.pp v
      | App(f, args) -> 
          Func.pp f ^ "(" ^ String.concat " " (List.map pp_term args) ^ ")"

    let mkAnd = function [f] -> f | l -> App(Func.andf,l)
    let mkOr  = function [f] -> f | l -> App(Func.orf, l)
    let mkCut = App(Func.cutf,[]) 
    let mkEq l r = App(Func.eqf,[l;r]) 
    
    let rec pp =
      function
        Var v -> Var.pp v
      | App (f,l) -> 
          (*if f = Func.andf then
          else if f = Func.orf then
          else if f = Func.cut then*)
         (* TODO: formulae should be pp as such *)
         "(" ^ String.concat " " (Func.pp f :: List.map pp l) ^ ")"

     (* raise NotAFormula *)
    let as_formula =
      function
        Var _ -> raise (NotFormula (lazy "Trying to prove a variable"))
      | App(f,l) as x->
         (* And [] is interpreted as false *)
         if Func.eq f Func.andf then And l
         (* Or [] is interpreted as true *)
         else if Func.eq f Func.orf then Or l
         else if Func.eq f Func.cutf then Cut
         else Atom x
  end;;

module FOAST = AST(Variable)(ASTFuncS)
include FOAST

module type TermT =
 sig
  include ASTT

  val query_of_ast : FOAST.term -> term
  val program_of_ast : (FOAST.term * FOAST.term) list -> (term * term) list
 end

module Term(Var: VarT)(Func: FuncT) : TermT 
    with type vart = Var.t and type funct = Func.t =
 struct
  include AST(Var)(Func)

  (* Note: converters from asts are the same as
     refreshers, but both have fixed types :-(
     Should be made parametric *)
  let var_of_ast l n =
   try l,List.assoc n l
   with Not_found ->
    let n' = Var.fresh () in
    (n,n')::l,n'

  let empty_converter = []

  let rec term_of_ast l =
   function
      FOAST.Var v ->
       let l,v = var_of_ast l v in
       l, Var v
    | FOAST.App(f,tl) ->
       let l,rev_tl =
         List.fold_left
          (fun (l,tl) t -> let l,t = term_of_ast l t in (l,t::tl))
          (l,[]) tl
       in
       l, App(Func.funct_of_ast f,List.rev rev_tl)

  let query_of_ast t = snd (term_of_ast empty_converter t)

  let program_of_ast p =
   List.map (fun (a,f) ->
    let l,a = term_of_ast empty_converter a in
    let _,f = term_of_ast l f in
    a,f) p
 end

module type RefreshableTermT =
  sig
    include TermT
 (* How to distinguish Atom from formula? 
    type clause = atomT * formula *)
    type clause = term * term
    val refresh_query : term -> term
    val refresh_clause : clause -> clause
  end;;


module RefreshableTerm(Var:VarT)(Func:FuncT) : RefreshableTermT
  with type vart = Var.t
  and  type funct = Func.t
  and  type term = Term(Var)(Func).term 
  and  type formula = Term(Var)(Func).formula
=
 struct
   include Term(Var)(Func)
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

   let refresh_clause (hd,bo) =
     let l,hd = refresh empty_refresher hd in
     let _,bo =  refresh l bo in
     (hd,bo)

   let refresh_query q = snd (refresh empty_refresher q)

 end;;




(*------ being ------ *)

module type HashableRefreshableTermT =
  sig
    include RefreshableTermT
    module IndexData : Hashtbl.HashedType 
    val index: term -> IndexData.t
  end;;


module HashableRefreshableTerm(Var:VarT)(Func:FuncT) : HashableRefreshableTermT
  with type vart = Var.t
  and  type funct = Func.t
  and  type term = Term(Var)(Func).term 
  and  type formula = Term(Var)(Func).formula
=
 struct
   include RefreshableTerm(Var)(Func)
   module IndexData =
     struct
       type t = Func.t
       let equal = Func.eq
       let hash = Hashtbl.hash
     end
   
   module TermFO = Term(Var)(Func)

   let index =
   function
      TermFO.App(f,_) -> f
    | TermFO.Var _ -> raise (Failure "Ill formed program")
 end;;


module type ApproximatableRefreshableTermT =
  sig
    include RefreshableTermT
    type approx
    val approx: term -> approx
    val matchp: approx -> approx -> bool
  end;;


module ApproximatableRefreshableTerm(Var: VarT)(Func: FuncT) :
 ApproximatableRefreshableTermT 
  with type vart = Var.t
  and  type funct = Func.t
  and  type term = Term(Var)(Func).term 
  and  type formula = Term(Var)(Func).formula
=
 struct
   include RefreshableTerm(Var)(Func) 

   type approx = Func.t * (Func.t option)

   module TermFO = Term(Var)(Func)

   let approx =
     function
       TermFO.App(f,[])
     | TermFO.App(f,TermFO.Var _::_) -> f,None
     | TermFO.App(f,TermFO.App(g,_)::_) -> f, Some g
     | TermFO.Var _ -> raise (Failure "Ill formed program")

   let matchp app1 app2 =
     match app1,app2 with
       (f1,None),(f2,_)
     | (f1,_),(f2,None)-> f1=f2
     | (f1,Some g1),(f2,Some g2) -> f1=f2 && g1=g2
  end;;


module type MapableRefreshableTermT =
 sig
  include RefreshableTermT
  module IndexData : Map.OrderedType 
  val index: term -> IndexData.t
 end
;;


module MapableRefreshableTerm(Var: VarT)(Func: FuncT) : MapableRefreshableTermT
  with type vart = Var.t
  and  type funct = Func.t
  and  type term = Term(Var)(Func).term 
  and  type formula = Term(Var)(Func).formula
=
 struct
  include RefreshableTerm(Var)(Func)
  module IndexData =
   struct
    type t = Func.t
    let equal = Func.eq
    let compare n1 n2 = String.compare (Func.pp n1) (Func.pp n2)
   end

  module TermFO = Term(Var)(Func)

  let index =
   function
      TermFO.App(f,_) -> f
    | TermFO.Var _ -> raise (Failure "Ill formed program")
 end;;

(*------end-------*)

module type BindingsT =
  sig
    type varT
    type termT
    type bindings
    val pp_bindings : bindings -> string
    val cardinal : bindings -> bindings * int
    val empty_bindings: bindings

    (** For Unification *)
    (* bind sigma v t = sigma [v |-> t] *)
    val bind : bindings -> varT -> termT -> bindings
    (* lookup sigma v = Some t   iff  [v |-> t] \in sigma *)
    val lookup : bindings -> varT -> termT option

    (** For GC *)
    val filter : (varT -> bool) -> bindings -> bindings
  end;;

module ImpBindings(Func: FuncT) : 
 BindingsT 
  with type varT = ImpVariable.t
  and type termT = Term(ImpVariable)(Func).term
  =
   struct
     type varT = ImpVariable.t
     type termT = Term(ImpVariable)(Func).term

     (*module MapVars = Map.Make(Vars)
     module Terms = Term(Vars)(Func)
     module VarSet = Set.Make(Vars);;*)
     type bindings = unit (* TODO Trail goes here *)

     let empty_bindings = ()
        
     let lookup _ k = Obj.magic !k

     let bind _ k v = k := Some (Obj.magic v)

     let cardinal _ = (), (-1)

     let pp_bindings _ = "<< no way to print >>"
        
     let filter f _ = assert false (* TODO assign None *)
   end


module Bindings(Vars: VarT)(Func: FuncT) : BindingsT 
  with type varT = Vars.t
  and type termT = Term(Vars)(Func).term
  =
   struct
     type varT = Vars.t
     type termT = Term(Vars)(Func).term

     module MapVars = Map.Make(Vars)
     module VarSet = Set.Make(Vars)
     module Terms = Term(Vars)(Func)
     type bindings = Term(Vars)(Func).term MapVars.t
     let empty_bindings = MapVars.empty
        
     let lookup bind k =
       try Some (MapVars.find k bind)
       with Not_found -> None

     let bind bind k v = MapVars.add k v bind

     let cardinal bind = bind, MapVars.cardinal bind

     let pp_bindings bind =
      String.concat "\n"
       (MapVars.fold
         (fun k v s -> (Vars.pp k ^ " |-> " ^ Terms.pp v) :: s)
         bind [])

     let filter f bind = MapVars.filter (fun k _ -> f k) bind 
   end;;


module WeakBindings(Vars: WeakVarT)(Func: FuncT) : BindingsT 
  with type varT = Vars.t
  and  type termT = Term(Vars)(Func).term
 =
  struct
    type varT = Vars.t
    type termT = Term(Vars)(Func).term
    module MapVars = Map.Make(struct type t = int let compare = compare let eq = (=) end)
    module Terms = Term(Vars)(Func)
    type bindings = Terms.term MapVars.t

    let empty_bindings = MapVars.empty

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

    let bind bind (Vars.Box k) v = MapVars.add k v (clean bind)

    let cardinal bind =
      let bind = clean bind in
        bind,MapVars.cardinal bind

    let filter f bind = MapVars.filter (fun k _ -> f (Vars.Box k)) bind 
  end;;



module type UnifyT =
  sig
    module Bind : BindingsT
   (* unify sub t1 t2 = sub'  iff  t1 sub' = t2 sub' and sub <= sub' *)
    val unify:
     Bind.bindings -> Bind.termT -> Bind.termT -> Bind.bindings         
  end;;

exception NotUnifiable of string Lazy.t

(* DIFFERENCE BETWEEN = AND := IN MODULE TYPE CONSTRAINTS
module type T = sig type t val f : t -> t end
T with type t = int  sig type t = int val f : t -> t end
T with type t := int sig val f: int -> int end *)

module Unify(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT = Term(Var)(Func).term and type varT = Var.t) : UnifyT
   with module Bind = Bind
=
  struct
    module T = Term(Var)(Func)
    module Bind = Bind

    let rec unify sub t1 t2 = 
      match t1,t2 with
        (T.Var v1, T.Var v2) when Var.eq v1 v2 -> sub
      | (T.Var v1, _) ->
          (match Bind.lookup sub v1 with
             None -> Bind.bind sub v1 t2
           | Some t -> unify sub t t2)
      | (_, T.Var _) -> unify sub t2 t1
      | (T.App (f1,l1), T.App (f2,l2)) -> 
          if Func.eq f1 f2 && List.length l1 = List.length l2 then
            List.fold_left2 unify sub l1 l2
          else
            raise (NotUnifiable (lazy "Terms are not unifiable!"))
   end;;


module FlatUnify(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT = Term(Var)(Func).term and type varT = Var.t) : UnifyT
  with module Bind = Bind
=
   struct
     module Bind = Bind
     module T = Term(Var)(Func)

     let rec deref sub i =
       match i with
         (T.Var v) ->
           (match Bind.lookup sub v with
              None -> i
           | Some t -> deref sub t)
       | T.App(_,_) -> i

     let rec flatten sub i =
       match i with
         (T.Var _) -> deref sub i
       | T.App(f,l) ->
          let l' = List.map (flatten sub) l in
           if l'==l then i else T.App(f, l')

(*let flatten sub i =
prerr_endline ("F: " ^ T.pp i); flatten sub i*)

     (* unify sub pattern query
        the query is only dereferences
        the pattern is fully flattened, i.e. recursively dereferenced
        the rationale is that patterns are small, queries can be huge
        flattening queries leads to quadratic complexity on our example
        because the same input can be flattened multiple times *)
     let rec unify ~do_flatten sub t1 t2 = match t1,t2 with
       (T.Var v1, T.Var v2) when Var.eq v1 v2 -> sub
     | (T.App (f1,l1), T.App (f2,l2)) -> 
         if Func.eq f1 f2 && List.length l1 = List.length l2 then
           List.fold_left2 (unify ~do_flatten) sub l1 l2
         else
           raise (NotUnifiable (lazy "Terms are not unifiable!"))
     | (T.Var _, _)
     | (_, T.Var _) ->
       let t1 = (if do_flatten then flatten else deref) sub t1 in
       let t2 = (if do_flatten then flatten else deref) sub t2 in
       match t1,t2 with
         (T.Var v1, T.Var v2) when Var.eq v1 v2 -> sub
       | (T.Var v1, _) -> Bind.bind sub v1 t2
       | (_, T.Var v2) -> Bind.bind sub v2 t1
       | (T.App _, T.App _) -> unify ~do_flatten:false sub t1 t2

     let unify = unify ~do_flatten:true
   end;;


module RefreshableFlatTerm(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT = Term(Var)(Func).term and type varT = Var.t) :
 RefreshableTermT
  with type vart = Var.t
  and  type funct = Func.t
  and  type term = RefreshableTerm(Var)(Func).term
  and  type formula = RefreshableTerm(Var)(Func).formula
=
 struct
   include RefreshableTerm(Var)(Func)
   include Bind
   include FlatUnify(Var)(Func)(Bind)
 end;;


module HashableRefreshableFlatTerm(Var: VarT)(Func: FuncT)(Bind: BindingsT with type varT = Var.t and type termT = Term(Var)(Func).term) : HashableRefreshableTermT
  with type vart = Var.t
  and  type funct = Func.t
  and  type term = Term(Var)(Func).term 
  and  type formula = Term(Var)(Func).formula
=
 struct
   include RefreshableFlatTerm(Var)(Func)(Bind)
   module IndexData =
     struct
       type t = Func.t
       let equal = Func.eq
       let hash = Hashtbl.hash
     end

   module TermFO = Term(Var)(Func)

   let index =
     function
      TermFO.App(f,_) -> f
    | TermFO.Var _ -> raise (Failure "Ill formed program")
  end;;


module type GCT =
 sig
  type bindings
  type term
  val gc: force:bool -> bindings -> term list -> bindings
 end;;


module GC(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 GCT with type bindings := Bind.bindings
     and type term := Term(Var)(Func).term 
=
 struct
  
  module Term = Term(Var)(Func);;
  open Term

  module VarSet = Set.Make(Var);;
    let rec findVarsTerm =
     function
      Var(x) -> VarSet.singleton x
    | App(_,args) -> 
        List.fold_left 
          (fun acc term -> 
             VarSet.union (findVarsTerm term) acc) VarSet.empty args

    let rec find_vars_fla = findVarsTerm (*
     function
      True -> VarSet.empty
    | Cut -> VarSet.empty
    | Atom(t) -> findVarsTerm t 
    | And(f1,f2) -> VarSet.union (find_vars_fla f1) (find_vars_fla f2)
    | Or(f1,f2) -> VarSet.union (find_vars_fla f1) (find_vars_fla f2)
*)
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



exception NotAnAtom;;

module type ProgramT =
   sig
        module Bind : BindingsT
        type t

        (* may raise NotAnAtom *)
        val backchain:
         Bind.bindings -> Bind.termT -> t ->
          (Bind.bindings * Bind.termT) list
        val make: (Bind.termT*Bind.termT) list -> t
   end

(* No indexing at all; a program is a list and retrieving the clauses
   from the program is O(n) where n is the size of the program.
   Matching is done using unification directly. *)
module Program(Term: RefreshableTermT)(Unify: UnifyT with type Bind.termT = Term.term) : ProgramT with module Bind = Unify.Bind
 =
  struct
    module Bind = Unify.Bind

    type t = (Term.term*Term.term) list
     (* backchain: bindings -> termT -> 
                    (Term.term*Term.term) list -> 
                          (bindings * Term.term) list           *)
    let backchain binds a l =
      filter_map (fun clause -> 
        let atom,f = Term.refresh_clause clause in
          try
            let binds = Unify.unify binds atom a in 
            Some (binds,f)
          with NotUnifiable _ -> None) l                

    let make p = p;;
  end;;



(* One level indexing; a program is a hash-table indexed on the
   predicate that is the head of the clause. Unification is used
   eagerly on all the clauses with the good head. Retrieving the
   clauses is O(n) where n is the number of clauses with the
   good head. *)
module ProgramHash(Term: HashableRefreshableTermT)(Unify: UnifyT with type Bind.termT = Term.term) : ProgramT with module Bind = Unify.Bind 
 =   
   struct
     module Bind = Unify.Bind

     (* Atom.t -> (Atom.t*Form.formula) list *)
     module Hash = Hashtbl.Make(Term.IndexData)
     type t = (Term.term*Term.term) Hash.t
                      
   (* backchain: bindings -> atomT -> 
                         Form.formula Hash.t -> 
                            (bindings * formulaT) list           *)
     let backchain binds a h =
       let l = List.rev (Hash.find_all h (Term.index a)) in
       filter_map (fun clause -> 
         let atom,f = Term.refresh_clause clause in
         try
           let binds = Unify.unify binds atom a in 
             Some (binds,f)
           with NotUnifiable _ -> None) 
         l                       
       
     let make p =
       let h = Hash.create 199 in
       List.iter
         (fun ((a,v) as clause) -> Hash.add h (Term.index a) clause) p;
       h
   end;; 


(* Two level inefficient indexing; a program is a list of clauses.
   Approximated matching is used to retrieve the candidates.
   Unification is then performed on the candidates.
   *** NOTE: this is probably redundant and more inefficient than
       just doing eager unification without approximated matching ***
   Retrieving the good clauses is O(n) where n is the size of the
   program. *)
module ProgramIndexL(Term: ApproximatableRefreshableTermT)(Unify: UnifyT with type Bind.termT = Term.term) : ProgramT with module Bind = Unify.Bind  
 =
   struct
     module Bind = Unify.Bind
     (* triples (app,(a,f)) where app is the approximation of a *)
     type t = (Term.approx * (Term.term * Term.term)) list

     (* backchain: bindings -> atomT -> 
                         Form.formula Hash.t -> 
                            (bindings * formulaT) list           *)
     let backchain binds a l =
       let app = Term.approx a in
         let l = List.filter (fun (a',_) -> Term.matchp app a') l in
          filter_map (fun (_,clause) ->
           let atom,f = Term.refresh_clause clause in
           try
            let binds = Unify.unify binds atom a in 
            Some (binds,f)
           with NotUnifiable _ -> None
           ) l
        ;;
        
        let make =
          List.map (fun ((a,_) as clause) -> Term.approx a,clause)
   end;;


(* One level indexing; a program is a Map indexed on the
   predicate that is the head of the clause. Unification is used
   eagerly on all the clauses with the good head. *)
module ProgramMap(Term: MapableRefreshableTermT)(Unify: UnifyT with type Bind.termT = Term.term) : ProgramT with module Bind = Unify.Bind =
   struct
     module Bind = Unify.Bind

     (* Atom.t -> (Atom.t*Form.formula) list *)
	  module ClauseMap = Map.Make(Term.IndexData)
     type t = (Term.term*Term.term) list ClauseMap.t
   (* backchain: bindings -> atomT -> 
                         Form.formula ClauseMap.t -> 
                            (bindings * formulaT) list    *)
     let backchain binds a m =
       let l = List.rev (ClauseMap.find (Term.index a) m) in
       filter_map (fun clause -> 
         let atom,f = Term.refresh_clause clause in
         try
           let binds = Unify.unify binds atom a in 
             Some (binds,f)
           with NotUnifiable _ -> None) 
         l                       
        
     let make p =       
       List.fold_left (fun m ((a,_) as clause) -> 
         let ind = Term.index a in
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
  type bindingsT
  type progT
  type cont (* continuation *)
  val run: progT -> term -> (bindingsT * cont) option
  val next: cont -> (bindingsT * cont) option
  val main_loop: progT -> term -> unit
 end

module Run(Term: RefreshableTermT)(Prog: ProgramT with type Bind.termT = Term.term)(*(GC : GCT type formula := Term.formula)*)(*TODO : RESTORE*) :
 RunT with type term := Term.term and type bindingsT := Prog.Bind.bindings
           and type progT := Prog.t
 = 
  struct 
        (* A cont is just the program plus the or list,
           i.e. a list of level * bindings * head of and_list * tl of and_list 
           The level is incremented when there is a *)
    type cont = 
      Prog.t * (int * Prog.Bind.bindings * Term.term * Term.term list) list

        (* WARNING: bad non reentrant imperative code here
           At least query should go into the continuation for next
           to work!
        *)
        let query = ref (Term.mkAnd [] (* True *))

        let run0 prog =
         (* aux lvl binds andl orl f
           (lvl,binds,(f::andl))::orl) *)
         let rec aux lvl binds andl orl f =
          (*let binds = GC.gc (f = F.True && andl=[]) binds (!query::f::andl) in  TODO : RESTORE *)
          match Term.as_formula f with
             Term.And [] ->                  (* (True::andl)::orl *)
              (match andl with
                  [] -> Some (binds,orl)       (* (binds,[])::orl *)
                  (* lvl-1 is because the body of a clause like a :- b,c.
                     is represented as And(b,c) in the and list and not like
                     b::c. Therefore an entry in the and list always
                     is a stack frame for the body of a clause.
                     An or expression is also to be thought as an anonymous
                     clause invocation (with special handling of cut).
                     Thus hd is the stack frame of the parent call, that was
                     done at level lvl-1. *) 
                | hd::tl -> aux (lvl-1) binds tl orl hd) (* (hd::tl)::orl *) 
           | Term.Cut ->
              let orl =
               (* We filter out from the or list every frame whose lvl
                  is >= then ours. *)
               let rec filter =
                function
                   [] -> []
                 | ((lvl',_,_,_)::_) as l when lvl' < lvl -> l
                 | _::tl -> filter tl
               in
                filter orl
              in
              (* cut&paste from True case *)
              (match andl with
                  [] -> Some (binds,orl)       (* (binds,[])::orl *)
                | hd::tl -> aux (lvl-1) binds tl orl hd) (* (hd::tl)::orl *)
           | Term.Atom i ->         (*A::and)::orl)*)                       
               (match Prog.backchain binds i prog with              
                   [] ->
                    (match orl with
                        [] -> None
                      | (lvl,bnd,f,andl)::tl -> aux lvl bnd andl tl f)
                 | (bnd,f)::tl ->
                     aux (lvl+1) bnd andl
                      (List.append
                        (List.map (fun (bnd,f) -> lvl+1, bnd,f,andl) tl)
                        orl) f)
           
           (* TODO: OPTIMIZE AND UNIFY WITH TRUE *)   
           | Term.And (f1::f2) ->             (* ((f1,f2)::andl)::orl *)
              let f2 = Term.mkAnd f2 in
              aux lvl binds (f2::andl) orl f1  (* (f1::(f2::andl))::orl *)

           (* Because of the +2 vs +1, the semantics of (c,! ; d)
              is to kill the alternatives for c, preserving the d one.
              Note: this is incoherent with the semantics of ! w.r.t.
              backchaining, but that's what Tejyus implements. *)
           (* TODO: OPTIMIZE AND UNIFY WITH FALSE (maybe) *)
           | Term.Or (f1::f2) ->              (* ((f1;f2)::andl)::orl) *)
              let f2 = Term.mkOr f2 in
              aux (lvl+2) binds andl ((lvl+1,binds,f2,andl)::orl) f1
                                           (* (f1::andl)::(f2::andl)::orl *)
           | Term.Or [] -> assert false (* TODO, backtrack *)
         in
          aux


    let run_next prog lvl binds andl orl f =
      let time0 = Unix.gettimeofday() in
        let res =
          match run0 prog lvl binds andl orl f with
             Some (binds,orl) -> Some (binds,(prog,orl))
           | None -> None in
        let time1 = Unix.gettimeofday() in
        prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
        (match res with
          Some (binds,orl) ->
            (* TODO restore Gc.full_major() ;*) let binds,size = Prog.Bind.cardinal binds in
            prerr_endline ("Final bindings size: " ^ string_of_int size) ;
              Some (binds,orl)
           | None -> None)

    let run prog f =
      query := f ;
      run_next prog 0 (Prog.Bind.empty_bindings) [] [] f

    let next (prog,orl) =
      match orl with
        [] -> None
      | (lvl,binds,f,andl)::orl -> run_next prog lvl binds andl orl f

    let main_loop prog query =
      let rec aux =
        function
          None -> prerr_endline "Fail"
        | Some (l,cont) ->
            prerr_endline ("Query: " ^ Term.pp query) ;
            prerr_endline (Prog.Bind.pp_bindings l) ;
            prerr_endline "More? (Y/n)";
              if read_line() <> "n" then
                aux (next cont)
          in
        aux (run prog query)

     end;;


module RunGC(Term: RefreshableTermT)(Prog: ProgramT with type Bind.termT = Term.term)(GC : GCT with type term := Term.term and type bindings := Prog.Bind.bindings)(*TODO : RESTORE*) :
 RunT with type term := Term.term and type bindingsT := Prog.Bind.bindings
           and type progT := Prog.t
 = 
  struct 
        (* A cont is just the program plus the or list,
           i.e. a list of level * bindings * head of and_list * tl of and_list 
           The level is incremented when there is a *)
    type cont = 
      Prog.t * (int * Prog.Bind.bindings * Term.term * Term.term list) list

        (* WARNING: bad non reentrant imperative code here
           At least query should go into the continuation for next
           to work!
        *)
    let query = ref (Term.mkAnd [] (* True *))

    let run0 prog =
         (* aux lvl binds andl orl f
           (lvl,binds,(f::andl))::orl) *)
      let rec aux lvl binds andl orl f =
      let binds = GC.gc (f = Term.mkAnd [] && andl=[]) binds (!query::f::andl) in  
          match Term.as_formula f with
             Term.And [] ->                  (* (True::andl)::orl *)
              (match andl with
                  [] -> Some (binds,orl)       (* (binds,[])::orl *)
                  (* lvl-1 is because the body of a clause like a :- b,c.
                     is represented as And(b,c) in the and list and not like
                     b::c. Therefore an entry in the and list always
                     is a stack frame for the body of a clause.
                     An or expression is also to be thought as an anonymous
                     clause invocation (with special handling of cut).
                     Thus hd is the stack frame of the parent call, that was
                     done at level lvl-1. *) 
                | hd::tl -> aux (lvl-1) binds tl orl hd) (* (hd::tl)::orl *) 
           | Term.Cut ->
              let orl =
               (* We filter out from the or list every frame whose lvl
                  is >= then ours. *)
               let rec filter =
                function
                   [] -> []
                 | ((lvl',_,_,_)::_) as l when lvl' < lvl -> l
                 | _::tl -> filter tl
               in
                filter orl
              in
              (* cut&paste from True case *)
              (match andl with
                  [] -> Some (binds,orl)       (* (binds,[])::orl *)
                | hd::tl -> aux (lvl-1) binds tl orl hd) (* (hd::tl)::orl *)
           | Term.Atom i ->         (*A::and)::orl)*)                       
               (match Prog.backchain binds i prog with              
                   [] ->
                    (match orl with
                        [] -> None
                      | (lvl,bnd,f,andl)::tl -> aux lvl bnd andl tl f)
                 | (bnd,f)::tl ->
                     aux (lvl+1) bnd andl
                      (List.append
                        (List.map (fun (bnd,f) -> lvl+1, bnd,f,andl) tl)
                        orl) f)
           
           (* TODO: OPTIMIZE AND UNIFY WITH TRUE *)   
           | Term.And (f1::f2) ->             (* ((f1,f2)::andl)::orl *)
              let f2 = Term.mkAnd f2 in
              aux lvl binds (f2::andl) orl f1  (* (f1::(f2::andl))::orl *)

           (* Because of the +2 vs +1, the semantics of (c,! ; d)
              is to kill the alternatives for c, preserving the d one.
              Note: this is incoherent with the semantics of ! w.r.t.
              backchaining, but that's what Tejyus implements. *)
           (* TODO: OPTIMIZE AND UNIFY WITH FALSE (maybe) *)
           | Term.Or (f1::f2) ->              (* ((f1;f2)::andl)::orl) *)
              let f2 = Term.mkOr f2 in
              aux (lvl+2) binds andl ((lvl+1,binds,f2,andl)::orl) f1
                                           (* (f1::andl)::(f2::andl)::orl *)
           | Term.Or [] -> assert false (* TODO, backtrack *)
         in
          aux


    let run_next prog lvl binds andl orl f =
      let time0 = Unix.gettimeofday() in
        let res =
          match run0 prog lvl binds andl orl f with
             Some (binds,orl) -> Some (binds,(prog,orl))
           | None -> None in
        let time1 = Unix.gettimeofday() in
        prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
        (match res with
          Some (binds,orl) ->
            (* TODO restore Gc.full_major() ;*) let binds,size = Prog.Bind.cardinal binds in
            prerr_endline ("Final bindings size: " ^ string_of_int size) ;
              Some (binds,orl)
           | None -> None)

    let run prog f =
      query := f ;
      run_next prog 0 (Prog.Bind.empty_bindings) [] [] f

    let next (prog,orl) =
      match orl with
        [] -> None
      | (lvl,binds,f,andl)::orl -> run_next prog lvl binds andl orl f

    let main_loop prog query =
      let rec aux =
        function
          None -> prerr_endline "Fail"
        | Some (l,cont) ->
            prerr_endline ("Query: " ^ Term.pp query) ;
            prerr_endline (Prog.Bind.pp_bindings l) ;
            prerr_endline "More? (Y/n)";
              if read_line() <> "n" then
                aux (next cont)
          in
        aux (run prog query)
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
  (ITerm: TermT)
  (IProgram: ProgramT with type Bind.termT = ITerm.term
                      (*and type bindings := ITerm.bindings*))
  (IRun: RunT with type progT := IProgram.t
              and type bindingsT := IProgram.Bind.bindings
              and type term := ITerm.term)
  (Descr : sig val descr : string end)
 : Implementation
=
 struct
  (* RUN with non indexed engine *)
  type query = ITerm.term
  type program = (ITerm.term * ITerm.term) list
  let query_of_ast = ITerm.query_of_ast
  let program_of_ast = ITerm.program_of_ast
  let msg q = Descr.descr ^ ITerm.pp q
  let execute_once p q = IRun.run (IProgram.make p) q = None
  let execute_loop p q = IRun.main_loop (IProgram.make p) q
 end
;;

(* implement the rest of the cases *)
let implementations = 
  let impl1 =
    (* RUN with non indexed engine *)
    let module ITerm = RefreshableTerm(Variable)(FuncS) in
    let module IProgram = Program(ITerm)(Unify(Variable)(FuncS)(Bindings(Variable)(FuncS))) in
    let module IRun = Run(ITerm)(IProgram)(*(NoGC(FOAtomImpl))*) in
    let module Descr = struct let descr = "Testing with no index list " end in
    (module Implementation(ITerm)(IProgram)(IRun)(Descr)
     : Implementation) in

let impl2 =
  (* RUN with indexed engine *)
  let module ITerm = HashableRefreshableTerm(Variable)(FuncS) in
  let module IProgram = ProgramHash(ITerm)(Unify(Variable)(FuncS)(Bindings(Variable)(FuncS))) in
  let module IRun = Run(ITerm)(IProgram)(*(NoGC(IAtom))*) in
  let module Descr = struct let descr = "Testing with one level index hashtbl " end in
  (module Implementation(ITerm)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl3 =
  (* RUN with two levels inefficient indexed engine *)
  let module ITerm = ApproximatableRefreshableTerm(Variable)(FuncS) in
  let module IProgram = ProgramIndexL(ITerm)(Unify(Variable)(FuncS)(Bindings(Variable)(FuncS))) in
  let module IRun = Run(ITerm)(IProgram)(*(NoGC(IAtom))*) in
  let module Descr = struct let descr = "Testing with two level inefficient index " end in
  (module Implementation(ITerm)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl4 =
  let module ITerm = HashableRefreshableTerm(WeakVariable)(FuncS) in
let module IProgram = ProgramHash(ITerm)(Unify(WeakVariable)(FuncS)(Bindings(WeakVariable)(FuncS))) in
  let module IRun = Run(ITerm)(IProgram)(*(NoGC(IAtom))*) in
  let module Descr = struct let descr = "Testing with one level index hashtbl and automatic GC " end in
  (module Implementation(ITerm)(IProgram)(IRun)(Descr)
  : Implementation) in


let impl5 =
  (* RUN with indexed engine and automatic GC *)
  let module ITerm = HashableRefreshableFlatTerm(WeakVariable)(FuncS)(WeakBindings(WeakVariable)(FuncS)) in
  let module IProgram = ProgramHash(ITerm)(Unify(WeakVariable)(FuncS)(Bindings(WeakVariable)(FuncS))) in
  let module IRun = Run(ITerm)(IProgram)(*(NoGC(IAtom))*) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening and automatic GC " end in
  (module Implementation(ITerm)(IProgram)(IRun)(Descr)
  : Implementation) in


let impl6 =
  (* RUN with indexed engine *)
  let module ITerm = HashableRefreshableFlatTerm(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
  let module IProgram = ProgramHash(ITerm)(Unify(Variable)(FuncS)(Bindings(Variable)(FuncS))) in
  let module IRun = Run(ITerm)(IProgram)(*(NoGC(IAtom))*) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening " end in
  (module Implementation(ITerm)(IProgram)(IRun)(Descr)
  : Implementation) in


let impl7 =
  let module ITerm = HashableRefreshableFlatTerm(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
  let module IProgram = ProgramHash(ITerm)(Unify(Variable)(FuncS)(Bindings(Variable)(FuncS))) in
  let module IRun = RunGC(ITerm)(IProgram)(GC(Variable)(FuncS)(Bindings(Variable)(FuncS))) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening + manual GC " end in
  (module Implementation(ITerm)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl8 =
  (* RUN with indexed engine and Map of clauses instead of Hash of clauses*)
  let module ITerm = MapableRefreshableTerm(Variable)(FuncS) in
  let module IProgram = ProgramMap(ITerm)(Unify(Variable)(FuncS)(Bindings(Variable)(FuncS))) in
  let module IRun = Run(ITerm)(IProgram)(*(NoGC(IAtom))*) in
  let module Descr = struct let descr = "Testing with one level index map " end in
  (module Implementation(ITerm)(IProgram)(IRun)(Descr)
  : Implementation) in

let impl9 =
  (* RUN with indexed engine *)
  let module ITerm = HashableRefreshableTerm(ImpVariable)(FuncS) in
  let module IProgram = ProgramHash(ITerm)(Unify(ImpVariable)(FuncS)(ImpBindings(FuncS))) in
  let module IRun = Run(ITerm)(IProgram)(*(NoGC(IAtom))*) in
  let module Descr = struct let descr = "Testing with imperative one level index hashtbl " end in
  (module Implementation(ITerm)(IProgram)(IRun)(Descr)
  : Implementation) in

  [impl1;impl2;impl3;impl4;impl5;impl6;impl7;impl8;impl9]
