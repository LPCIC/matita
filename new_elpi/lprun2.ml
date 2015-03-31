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

module type FuncT =
  sig
    type t
    val pp : t -> string
    val eq : t -> t -> bool
    val andf : t
    val orf : t
    val cutf : t
  end;;

module FuncS : FuncT with type t = string = 
  struct
    type t = string
    let pp n = n
    let eq = (=)
    let andf = ","
    let orf = ";"
    let cutf = "!"
  end;;

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

module type TermT =
  sig  
    type vart
    type funct
    type term = Var of vart 
              | App of funct * term list

    type formula = Cut
					  | Atom of term
					  | And of term list
					  | Or of term list

    val mkCut : term
    val mkAnd : term list -> term
    val mkOr : term list -> term

    (* raise NotAFormula *)
    val as_formula: term -> formula

    val pp: term -> string
  end;;

module Term(Var: VarT)(Func: FuncT) : TermT 
    with type vart = Var.t and type funct = Func.t 
 = 
  struct
    type vart = Var.t
    type funct = Func.t

    type term = Var of Var.t 
              | App of Func.t * term list

    type formula = Cut
					  | Atom of term
					  | And of term list
					  | Or of term list

    let rec pp_term = 
      function 
        Var v -> Var.pp v
      | App(f, args) -> 
          Func.pp f ^ "(" ^ String.concat " " (List.map pp_term args) ^ ")"

    let mkAnd l = App(Func.andf,l)
    let mkOr  l = App(Func.orf, l)
    let mkCut   = App(Func.cutf,[]) 
    

     (* raise NotAFormula *)
    let as_formula =
      function
        Var _ -> raise (NotFormula (lazy "Trying to prove a variable"))
      | App(f,l) ->
         (* And [] is interpreted as false *)
         if f = Func.andf then And l
         (* Or [] is interpreted as true *)
         else if f = Func.orf then Or l
         else if f = Func.cutf then Cut
         else Atom (App(f,l))

     let rec pp =
       function
         Var v -> Var.pp v
       | App (f,l) -> 
           (*if f = Func.andf then
           else if f = Func.orf then
           else if f = Func.cut then*)
          (* TODO: formulae should be pp as such *)
          "(" ^ String.concat " " (Func.pp f :: List.map pp l) ^ ")"
  end;;


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


module Run(Term: RefreshableTermT)(Prog: ProgramT with type Bind.termT = Term.term)(*(GC : GCT type formula := Term.formula)*)(*TODO : RESTORE*) :
  sig
    type cont (* continuation *)
    val run: Prog.t -> Term.term -> (Prog.Bind.bindings * cont) option
    val next: cont -> (Prog.Bind.bindings * cont) option
    val main_loop: Prog.t -> Term.term -> unit
  end
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

module FOTerm = RefreshableTerm(Variable)(FuncS)
include FOTerm

let implementations = 
  let impl1 =
  (* RUN with non indexed engine *)
    let module TermImpl = FOTerm in
    let module FOProgram = Program(TermImpl)(Unify(Variable)(FuncS)(Bindings(Variable)(FuncS))) in
    let module RunFO = Run(TermImpl)(FOProgram)(*(NoGC(FOAtomImpl))*) in
    (fun q -> "Testing with no index list " ^ FOTerm.pp q),
    (fun p q -> RunFO.run (FOProgram.make p) q = None),
    (fun p q -> RunFO.main_loop (FOProgram.make p) q)
  in 
  [impl1]

