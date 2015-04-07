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

exception NotUnifiable of string Lazy.t;;

module type AtomT =
   sig        
        type t
        val pp : t -> string
        type bindings
        val cardinal: bindings -> bindings * int
        val pp_bindings : bindings -> string
        val empty_bindings : bindings
        (* raises NotUnifiable in case of failure *)
        val unify: bindings -> t -> t -> bindings

        type converter
        val empty_converter : converter
        val atom_of_ast : converter -> Lprun2.term -> converter * t
   end;;

module type Refreshable =
   sig        
        type r
        type refresher
        val empty_refresher : refresher
        val refresh : refresher -> r -> refresher * r
   end;;

module type RefreshableAtomT =
 sig include AtomT include Refreshable with type r := t end
;;

module AtomInt : RefreshableAtomT with type t = int =
   struct
        type t = int
        let pp n = "A" ^ string_of_int n

        type refresher = unit
        let empty_refresher = ()
        let refresh () n = (),n

        type bindings = unit
        let cardinal () = (),0
        let pp_bindings () = ""
        let empty_bindings = ()
        let unify () x y =
         if (x = y) then ()
         else
          raise (NotUnifiable
           (lazy (string_of_int x ^ " vs " ^ string_of_int y)))

        type converter = unit
        let empty_converter = ()
        let atom_of_ast _ = assert false
   end;;

module AtomString : RefreshableAtomT with type t = string =
   struct
        type t = string
        let pp x = x

        type refresher = unit
        let empty_refresher = ()
        let refresh () n = (),n

        type bindings = unit
        let cardinal () = (),0
        let pp_bindings () = ""
        let empty_bindings = ()
        let unify () x y =
         if (x = y) then ()
         else
          raise (NotUnifiable
           (lazy (x ^ " vs " ^ y)))

        type converter = unit
        let empty_converter = ()
        let atom_of_ast _ = assert false
   end;;

module type FormulaeT =
   sig
         type atomT
         type formula = 
            And of formula * formula
          | Or of formula * formula
          | True
          | Cut
          | Atom of atomT;;

         val pp : formula -> string

         val query_of_ast : Lprun2.term -> formula
         val program_of_ast :
          (Lprun2.term * Lprun2.term) list -> (atomT * formula) list
   end;;

module type RefreshableFormulaeT =
   sig
         include FormulaeT

         type clause = atomT * formula

         val refresh : clause -> clause
   end;;

module Formulae(Atom: AtomT) : FormulaeT with type atomT := Atom.t =
   struct
        type formula = 
                And of formula * formula
              | Or of formula * formula
              | True
              | Cut
              | Atom of Atom.t;;

        let rec pp =
         function
            And(f1,f2) -> "(" ^ pp f1 ^ "," ^ pp f2 ^ ")"
          | Or(f1,f2) -> "(" ^ pp f1 ^ ";" ^ pp f2 ^ ")"
          | True -> "true"
          | Cut -> "!"
          | Atom a -> Atom.pp a

        (* Note: converters from asts are the same as
           refreshers, but both have fixed types :-(
           Should be made parametric *)
        let rec formula_of_ast k t =
         match Lprun2.as_formula t with
            Lprun2.And(l) ->
             let rec aux k =
              function
                 [] -> k,True
               | [t] -> formula_of_ast k t
               | hd::tl ->
                  let k,hd = formula_of_ast k hd in
                  let k,tl = aux k tl in
                  k,And(hd,tl)
             in
              aux k l
          | Lprun2.Cut -> k,Cut
          | Lprun2.Or(l) ->
             let rec aux k =
              function
                 [] -> assert false (* TODO: add False *)
               | [t] -> formula_of_ast k t
               | hd::tl ->
                  let k,hd = formula_of_ast k hd in
                  let k,tl = aux k tl in
                  k,Or(hd,tl)
             in
              aux k l
          | Lprun2.Atom t ->
             let k,t = Atom.atom_of_ast k t in
             k,Atom t

        let query_of_ast t = snd (formula_of_ast Atom.empty_converter t)

        let program_of_ast p =
         List.map (fun (a,f) ->
          let l,a = Atom.atom_of_ast Atom.empty_converter a in
          let _,f = formula_of_ast l f in
          a,f) p
   end;;


module RefreshableFormulae(Atom: RefreshableAtomT) :
 RefreshableFormulaeT
  with type atomT := Atom.t
  and type formula = Formulae(Atom).formula
 =
   struct
        include Formulae(Atom)

        type clause = Atom.t * formula

        let refresh (hd,bo) =
         let l = Atom.empty_refresher in
         let l,hd = Atom.refresh l hd in
         let rec aux l =
          function
             And(f1,f2) ->
              let l,f1 = aux l f1 in
              let l,f2 = aux l f2 in
               l, And(f1,f2)
           | Or(f1,f2) ->
              let l,f1 = aux l f1 in
              let l,f2 = aux l f2 in
               l, Or(f1,f2)
           | True -> l, True
           | Cut -> l, Cut  
           | Atom a ->
              let l,a = Atom.refresh l a in
              l, Atom a in
          let _,bo = aux l bo in
          (hd,bo)
   end;;

module FormulaeInt = RefreshableFormulae(AtomInt);;
module FormualeString = RefreshableFormulae(AtomString);;

let test = FormulaeInt.And (FormulaeInt.Atom 0, FormulaeInt.Atom 1);;

(* --------------------------------------- *)

module type ProgramT =
   sig
        type t
        type atomT
        type formulaT
        type bindings
        val backchain: bindings -> atomT -> t -> 
                                        (bindings * formulaT) list
        val make: (atomT*formulaT) list -> t
   end

(* No indexing at all; a program is a list and retrieving the clauses
   from the program is O(n) where n is the size of the program.
   Matching is done using unification directly. *)
module Program(Atom: RefreshableAtomT) : ProgramT
    with type atomT := Atom.t
    and  type formulaT := RefreshableFormulae(Atom).formula
    and  type bindings := Atom.bindings =
   struct
        module Form = RefreshableFormulae(Atom)

        type t = (Atom.t*Form.formula) list
   
        (* backchain: bindings -> atomT -> 
                         (Atom.t*Form.formula) list -> 
                            (bindings * formulaT) list           *)
        let backchain binds a l =
          filter_map (fun clause -> 
            let atom,f = Form.refresh clause in
            try
                  let binds = Atom.unify binds atom a in 
                Some (binds,f)
            with NotUnifiable _ -> None) l                
        let make p = p;;
   end;;



module type HashableRefreshableAtomT =
 sig
  include RefreshableAtomT
  module IndexData : Hashtbl.HashedType 
  val index: t -> IndexData.t
 end
;;

module type MapableRefreshableAtomT =
 sig
  include RefreshableAtomT
  module IndexData : Map.OrderedType 
  val index: t -> IndexData.t
 end
;;

(* One level indexing; a program is a hash-table indexed on the
   predicate that is the head of the clause. Unification is used
   eagerly on all the clauses with the good head. Retrieving the
   clauses is O(n) where n is the number of clauses with the
   good head. *)
module ProgramHash(Atom: HashableRefreshableAtomT) : ProgramT
    with type atomT := Atom.t
    and  type formulaT := RefreshableFormulae(Atom).formula
    and  type bindings := Atom.bindings =
   struct
     module Form = RefreshableFormulae(Atom)

     (* Atom.t -> (Atom.t*Form.formula) list *)
     module Hash = Hashtbl.Make(Atom.IndexData)
     type t = Form.clause Hash.t
                  
   (* backchain: bindings -> atomT -> 
                         Form.formula Hash.t -> 
                            (bindings * formulaT) list           *)
     let backchain binds a h =
       let l = List.rev (Hash.find_all h (Atom.index a)) in
       filter_map (fun clause -> 
         let atom,f = Form.refresh clause in
         try
           let binds = Atom.unify binds atom a in 
             Some (binds,f)
           with NotUnifiable _ -> None) 
         l                       
        
     let make p =
       let h = Hash.create 199 in
       List.iter
         (fun ((a,v) as clause) -> Hash.add h (Atom.index a) clause) p;
       h
   end;;


(* One level indexing; a program is a Map indexed on the
   predicate that is the head of the clause. Unification is used
   eagerly on all the clauses with the good head. *)
module ProgramMap(Atom: MapableRefreshableAtomT) : ProgramT
    with type atomT := Atom.t
    and  type formulaT := RefreshableFormulae(Atom).formula
    and  type bindings := Atom.bindings =
   struct
     module Form = RefreshableFormulae(Atom)

     (* Atom.t -> (Atom.t*Form.formula) list *)
	  module ClauseMap = Map.Make(Atom.IndexData)
     type t = (Form.clause list)  ClauseMap.t
                  
   (* backchain: bindings -> atomT -> 
                         Form.formula ClauseMap.t -> 
                            (bindings * formulaT) list    *)
     let backchain binds a m =
       let l = List.rev (ClauseMap.find (Atom.index a) m) in
       filter_map (fun clause -> 
         let atom,f = Form.refresh clause in
         try
           let binds = Atom.unify binds atom a in 
             Some (binds,f)
           with NotUnifiable _ -> None) 
         l                       
        
     let make p =       
       List.fold_left (fun m ((a,_) as clause) -> 
         let ind = Atom.index a in
         try 
           let l = ClauseMap.find ind m in
           ClauseMap.add ind (clause :: l) m
         with Not_found -> 
           ClauseMap.add ind [clause] m
         ) ClauseMap.empty p
   end;;



module type ApproximatableRefreshableAtomT =
 sig
  include RefreshableAtomT
  type approx
  val approx: t -> approx
  val matchp: approx -> approx -> bool
 end
;;

(* Two level inefficient indexing; a program is a list of clauses.
   Approximated matching is used to retrieve the candidates.
   Unification is then performed on the candidates.
   *** NOTE: this is probably redundant and more inefficient than
       just doing eager unification without approximated matching ***
   Retrieving the good clauses is O(n) where n is the size of the
   program. *)
module ProgramIndexL(Atom: ApproximatableRefreshableAtomT) : ProgramT
    with type atomT := Atom.t
    and  type formulaT := RefreshableFormulae(Atom).formula
    and  type bindings := Atom.bindings =
   struct
        module Form = RefreshableFormulae(Atom)

        (* triples (app,(a,f)) where app is the approximation of a *)
        type t = (Atom.approx * (Atom.t * Form.formula)) list

        (* backchain: bindings -> atomT -> 
                         Form.formula Hash.t -> 
                            (bindings * formulaT) list           *)
        let backchain binds a l =
          let app = Atom.approx a in
          let l = List.filter (fun (a',_) -> Atom.matchp app a') l in
          filter_map (fun (_,clause) ->
           let atom,f = Form.refresh clause in
           try
            let binds = Atom.unify binds atom a in 
            Some (binds,f)
           with NotUnifiable _ -> None
           ) l
        ;;
        
        let make =
          List.map (fun ((a,_) as clause) -> Atom.approx a,clause)
   end;;

(* ---------------------------------------- *)

module type GCT =
 sig
  type bindings
  type formula
  val gc: force:bool -> bindings -> formula list -> bindings
 end

module NoGC(Atom: RefreshableAtomT) :
 GCT with type bindings := Atom.bindings
     and  type formula := RefreshableFormulae(Atom).formula =
 struct
  let gc ~force binds _ = binds
 end

module type RunT =
 sig
  type formula
  type bindingsT
  type progT
  type cont (* continuation *)
  val run: progT -> formula -> (bindingsT * cont) option
  val next: cont -> (bindingsT * cont) option
  val main_loop: progT -> formula -> unit
 end

module Run(Atom: RefreshableAtomT)(Prog: ProgramT with type atomT := Atom.t and type formulaT := RefreshableFormulae(Atom).formula and type bindings := Atom.bindings)(GC : GCT with type bindings := Atom.bindings and type formula := RefreshableFormulae(Atom).formula) :
 RunT
  with type progT := Prog.t
  and type bindingsT := Atom.bindings
  and type formula := RefreshableFormulae(Atom).formula
   = struct 
        module F = RefreshableFormulae(Atom)

        (* A cont is just the program plus the or list,
           i.e. a list of level * bindings * head of and_list * tl of and_list 
           The level is incremented when there is a *)
        type cont =
          Prog.t * (int * Atom.bindings * F.formula * F.formula list) list

        (* WARNING: bad non reentrant imperative code here
           At least query should go into the continuation for next
           to work!
        *)
        let query = ref F.True;;

        let run0 prog =
         (* aux lvl binds andl orl f
           (lvl,binds,(f::andl))::orl) *)
         let rec aux lvl binds andl orl f =
          let binds = GC.gc (f = F.True && andl=[]) binds (!query::f::andl) in
          match f with
             F.True ->                  (* (True::andl)::orl *)
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
           | F.Cut ->
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
           | F.Atom i ->         (*A::and)::orl)*)                       
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
                    
           | F.And (f1, f2) ->             (* ((f1,f2)::andl)::orl *)
              aux lvl binds (f2::andl) orl f1  (* (f1::(f2::andl))::orl *)

           (* Because of the +2 vs +1, the semantics of (c,! ; d)
              is to kill the alternatives for c, preserving the d one.
              Note: this is incoherent with the semantics of ! w.r.t.
              backchaining, but that's what Tejyus implements. *)
           | F.Or (f1, f2) ->              (* ((f1;f2)::andl)::orl) *)
              aux (lvl+2) binds andl ((lvl+1,binds,f2,andl)::orl) f1
                                           (* (f1::andl)::(f2::andl)::orl *)
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
              Gc.full_major() ; let binds,size = Atom.cardinal binds in
              prerr_endline ("Final bindings size: " ^ string_of_int size) ;
              Some (binds,orl)
           | None -> None)

        let run prog f =
         query := f ;
         run_next prog 0 (Atom.empty_bindings) [] [] f

        let next (prog,orl) =
          match orl with
            [] -> None
          | (lvl,binds,f,andl)::orl -> run_next prog lvl binds andl orl f

        let main_loop prog query =
         let rec aux =
          function
             None -> prerr_endline "Fail"
           | Some (l,cont) ->
              prerr_endline ("Query: " ^ F.pp query) ;
              prerr_endline (Atom.pp_bindings l) ;
              prerr_endline "More? (Y/n)";
              if read_line() <> "n" then
               aux (next cont)
         in
          aux (run prog query)

     end

(*
open FormulaeInt;;

module ProgramInt = Program(AtomInt);;

let prog = ProgramInt.make
 [ 0, And (Atom 1, Atom 2)
 ; 1, Or (Atom 3, Atom 2)
 ; 3, Atom 4
 ; 2, Or (Atom 4, Atom 5)
 ; 5, True ]
;;

module RunInt = Run(AtomInt)(ProgramInt);; 

RunInt.main_loop prog (Atom 0);;
*)

(*------------------- TERM ------------------*)

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

module type FuncT =
  sig
    type t
    val pp : t -> string
    val eq : t -> t -> bool
  end;;

module Func : FuncT with type t = int = 
  struct
    type t = int
    let pp n = "f" ^ string_of_int n
    let eq = (=)
  end;;

module FuncS : FuncT with type t = string = 
  struct
    type t = string
    let pp n = n
    let eq = (=)
  end;;

module type TermT =
  sig
    type varT
    type funcT
    type term = Var of varT | App of funcT * (term list)
    val pp : term -> string

    (* TODO (LATER) Introduce a Convertable module type *)
    type converter
    val empty_converter : converter
    val term_of_ast : converter -> Lprun2.term -> converter * term
  end;;

module Term(Var:VarT)(Func:FuncT) :
 TermT
  with type varT := Var.t
  and  type funcT := Func.t =
   struct
     type term = Var of Var.t | App of Func.t * (term list)

     let rec pp =
      function
         Var v -> Var.pp v
       | App(f,l) -> Func.pp f ^"("^ String.concat "," (List.map pp l) ^")"

     (* Note: converters from asts are the same as
        refreshers, but both have fixed types :-(
        Should be made parametric *)
     let var_of_ast l n =
      try l,List.assoc n l
      with Not_found ->
       let n' = Var.fresh () in
       (n,n')::l,n'

     type converter = (Lprun2.vart * Var.t) list

     let empty_converter = []

     let rec term_of_ast l =
      function
         Lprun2.Var v ->
          let l,v = var_of_ast l v in
          l, Var v
       | Lprun2.App(f,tl) ->
          let l,rev_tl =
            List.fold_left
             (fun (l,tl) t -> let l,t = term_of_ast l t in (l,t::tl))
             (l,[]) tl
          in
          (* TODO: convert the Funcs too *)
          l, App(Obj.magic f,List.rev rev_tl)

   end

module type RefreshableTermT =
 sig include TermT include Refreshable with type r := term end
;;

module RefreshableTerm(Var:VarT)(Func:FuncT) :
 RefreshableTermT
  with type varT := Var.t
  and  type funcT := Func.t
  and  type term = Term(Var)(Func).term =
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
 end

module type BindingsT =
   sig
        type varT
        type termT
        type bindings
        val pp_bindings : bindings -> string
        val cardinal : bindings -> bindings * int
        val empty_bindings: bindings
        (* bind sigma v t = sigma [v |-> t] *)
        val bind : bindings -> varT -> termT -> bindings
        (* lookup sigma v = Some t   iff  [v |-> t] \in sigma *)
        val lookup : bindings -> varT -> termT option
        val filter : (varT -> bool) -> bindings -> bindings
   end

module ImpBindings(Func: FuncT) : 
 BindingsT 
  with type varT := ImpVariable.t
  and type termT := Term(ImpVariable)(Func).term
  =
   struct
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

module Bindings(Vars: VarT)(Func: FuncT) : 
 BindingsT 
  with type varT := Vars.t
  and type termT := Term(Vars)(Func).term
  =
   struct
     module MapVars = Map.Make(Vars)
     module Terms = Term(Vars)(Func)
     module VarSet = Set.Make(Vars);;
     type bindings = Terms.term MapVars.t

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
   end

module WeakBindings(Vars: WeakVarT)(Func: FuncT) : 
 BindingsT 
  with type varT := Vars.t
  and type termT := Term(Vars)(Func).term
  =
   struct
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
         if tbr = [] then bind else (
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
   end

module type UnifyT =
   sig
        type bindings
        type termT
        (* unify sub t1 t2 = sub'  iff  t1 sub' = t2 sub' and sub <= sub' *)
        val unify: bindings -> termT -> termT -> bindings         
   end;;

module Unify(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 UnifyT
  with type bindings := Bind.bindings
  and type termT := Term(Var)(Func).term
=
   struct
        module T = Term(Var)(Func)

        let rec unify sub t1 t2 = match t1,t2 with
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

module FlatUnify(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 UnifyT
  with type bindings := Bind.bindings
  and type termT := Term(Var)(Func).term
=
   struct
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

module FOAtom(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 RefreshableAtomT
  with type t = Term(Var)(Func).term
=
 struct
   include RefreshableTerm(Var)(Func)
   include Bind
   include Unify(Var)(Func)(Bind)
   type t = term
   let atom_of_ast = term_of_ast
 end

module HashableFOAtom(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 HashableRefreshableAtomT
  with type t = Term(Var)(Func).term
=
 struct
  include FOAtom(Var)(Func)(Bind)
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


module MapableFOAtom(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 MapableRefreshableAtomT
  with type t = Term(Var)(Func).term
=
 struct
  include FOAtom(Var)(Func)(Bind)
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


module ApproximatableFOAtom(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 ApproximatableRefreshableAtomT
  with type t = Term(Var)(Func).term
=
 struct
  include FOAtom(Var)(Func)(Bind)

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
 end

module FOFlatAtom(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 RefreshableAtomT
  with type t = Term(Var)(Func).term
  and  type bindings = Bind.bindings
=
 struct
   include RefreshableTerm(Var)(Func)
   include Bind
   include FlatUnify(Var)(Func)(Bind)
   type t = term
   let atom_of_ast = term_of_ast
 end

module HashableFOFlatAtom(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 HashableRefreshableAtomT
  with type t = Term(Var)(Func).term
  and  type bindings = Bind.bindings
=
 struct
  include FOFlatAtom(Var)(Func)(Bind)
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
 end

(* IMPLEMENT A GC

input: andl + current formula
       bindings

1. V = FV(andl+current formula)   all variables occurring in
2. O = emptyset    (already visited variables)
   while not empty V
     v <- V
     O := v + O
     let t = bindings(v)
     for each w in FV(t)
      if w in O then ()
      else V := w + V
3. now V is empty and O holds all the reachable variables
   for each v in Dom(bindings)
    if v not in O then remove v bindings 
*)

module GC(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t)(Formulae: FormulaeT with type atomT := FOAtom(Var)(Func)(Bind).t) :
 GCT with type bindings := Bind.bindings
     and type formula :=    Formulae.formula 
=
 struct
  
  module Term = Term(Var)(Func);;
  open Term
  open Formulae

  module VarSet = Set.Make(Var);;
    let rec findVarsTerm =
     function
      Var(x) -> VarSet.singleton x
    | App(_,args) -> 
        List.fold_left 
          (fun acc term -> 
             VarSet.union (findVarsTerm term) acc) VarSet.empty args

    let rec find_vars_fla =
     function
      True -> VarSet.empty
    | Cut -> VarSet.empty
    | Atom(t) -> findVarsTerm t 
    | And(f1,f2) -> VarSet.union (find_vars_fla f1) (find_vars_fla f2)
    | Or(f1,f2) -> VarSet.union (find_vars_fla f1) (find_vars_fla f2)

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



(*
module FOAtomImpl = FOAtom(Variable)(Func)(Bindings(Variable)(Func))
module FOProgram = Program(FOAtomImpl)
module RunFO = Run(FOAtomImpl)(FOProgram)
module FOTerm = Term(Variable)(Func)
module FOFormulae = RefreshableFormulae(FOAtomImpl)

open FOTerm;;
open FOFormulae;;

let p = 0
let q = 1
let two = 2
let x = Variable.fresh ()
let prog = FOProgram.make
 [ App(p,[Var x]), Atom(App(q,[Var x]))
 ; App(q,[App(two,[])]), True ]
;;

let y = Variable.fresh () in
let query = Atom (App(p,[Var y])) in
prerr_endline ("Testing " ^ FOFormulae.pp query);
RunFO.main_loop prog query
;;
*)

module
 Implementation
  (IAtom: AtomT)
  (IFormulae: FormulaeT with type atomT := IAtom.t)
  (IProgram: ProgramT with type formulaT := IFormulae.formula
                      and type atomT := IAtom.t
                      and type bindings := IAtom.bindings)
  (IRun: RunT with type progT := IProgram.t
              and type bindingsT := IAtom.bindings
              and type formula := IFormulae.formula)
  (Descr : sig val descr : string end)
 : Lprun2.Implementation
=
 struct
  (* RUN with non indexed engine *)
  type query = IFormulae.formula
  type program = (IAtom.t * IFormulae.formula) list
  let query_of_ast = IFormulae.query_of_ast
  let program_of_ast = IFormulae.program_of_ast
  let msg q = Descr.descr ^ IFormulae.pp q
  let execute_once p q = IRun.run (IProgram.make p) q = None
  let execute_loop p q = IRun.main_loop (IProgram.make p) q
 end
;;

(* List of implementations, i.e. quadruples
   msg: formula -> string
   load_and_run: program -> Program.t
   load_and_main_loop: program -> query -> unit *)
let implementations =
 (* RUN with non indexed engine *)
 let impl1 =
  let module IAtom = FOAtom(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = Program(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(NoGC(IAtom)) in
  let module Descr = struct let descr = "Testing with no index list " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
   : Lprun2.Implementation) in

 let impl2 =
  (* RUN with indexed engine *)
  let module IAtom = HashableFOAtom(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = ProgramHash(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(NoGC(IAtom)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in

 let impl3 =
  (* RUN with two levels inefficient indexed engine *)
  let module IAtom = ApproximatableFOAtom(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = ProgramIndexL(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(NoGC(IAtom)) in
  let module Descr = struct let descr = "Testing with two level inefficient index " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in

 let impl4 =
  let module IAtom = HashableFOAtom(WeakVariable)(FuncS)(WeakBindings(WeakVariable)(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = ProgramHash(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(NoGC(IAtom)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl and automatic GC " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in

 let impl5 =
  (* RUN with indexed engine and automatic GC *)
  let module IAtom = HashableFOFlatAtom(WeakVariable)(FuncS)(WeakBindings(WeakVariable)(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = ProgramHash(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(NoGC(IAtom)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening and automatic GC " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in

 let impl6 =
  (* RUN with indexed engine *)
  let module IAtom = HashableFOFlatAtom(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = ProgramHash(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(NoGC(IAtom)) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in

 let impl7 =
  let module IAtom = HashableFOFlatAtom(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = ProgramHash(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(GC(Variable)(FuncS)(Bindings(Variable)(FuncS))(RefreshableFormulae(IAtom))) in
  let module Descr = struct let descr = "Testing with one level index hashtbl + flattening + manual GC " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in

let impl8 =
  (* RUN with indexed engine and Map of clauses instead of Hash of clauses*)
  let module IAtom = MapableFOAtom(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = ProgramMap(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(NoGC(IAtom)) in
  let module Descr = struct let descr = "Testing with one level index map " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in

 let impl9 =
  (* RUN with indexed engine *)
  let module IAtom = HashableFOAtom(ImpVariable)(FuncS)(ImpBindings(FuncS)) in
  let module IFormulae = RefreshableFormulae(IAtom) in
  let module IProgram = ProgramHash(IAtom) in
  let module IRun = Run(IAtom)(IProgram)(NoGC(IAtom)) in
  let module Descr = struct let descr = "Testing with imperative one level index hashtbl " end in
  (module Implementation(IAtom)(IFormulae)(IProgram)(IRun)(Descr)
  : Lprun2.Implementation) in


 [impl1;impl2;impl3;impl4;impl5;impl6;impl7;impl8;impl9]
;;
