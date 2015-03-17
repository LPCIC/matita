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
        val pp_bindings : bindings -> string
        val empty_bindings : bindings
        (* raises NotUnifiable in case of failure *)
        val unify: bindings -> t -> t -> bindings
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
        let pp_bindings () = ""
        let empty_bindings = ()
        let unify () x y =
         if (x = y) then ()
         else
          raise (NotUnifiable
           (lazy (string_of_int x ^ " vs " ^ string_of_int y)))
   end;;

module AtomString : RefreshableAtomT with type t = string =
   struct
        type t = string
        let pp x = x

        type refresher = unit
        let empty_refresher = ()
        let refresh () n = (),n

        type bindings = unit
        let pp_bindings () = ""
        let empty_bindings = ()
        let unify () x y =
         if (x = y) then ()
         else
          raise (NotUnifiable
           (lazy (x ^ " vs " ^ y)))
   end;;

module type FormulaeT =
   sig
             type atomT
             type formula = 
                And of formula * formula
                    | Or of formula * formula
              | True
                    | Atom of atomT;;

         val pp : formula -> string
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
              | Atom of Atom.t;;

        let rec pp =
         function
            And(f1,f2) -> "(" ^ pp f1 ^ "," ^ pp f2 ^ ")"
          | Or(f1,f2) -> "(" ^ pp f1 ^ ";" ^ pp f2 ^ ")"
          | True -> "true"
          | Atom a -> Atom.pp a
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

(* One level indexing; a program is an hash-table indexed on the
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

        let rec filter_map mapf =
         function
            [] -> []
          | hd::tl ->
             match mapf hd with
                None -> filter_map mapf tl
              | Some hd' -> hd'::filter_map mapf tl
   
                  
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

module Run(Atom: RefreshableAtomT)(Prog: ProgramT with type atomT := Atom.t and type formulaT := RefreshableFormulae(Atom).formula and type bindings := Atom.bindings):
   sig
    type cont (* continuation *)
    val run: Prog.t -> RefreshableFormulae(Atom).formula ->
              (Atom.bindings * cont) option
    val next: cont -> (Atom.bindings * cont) option

    val main_loop: Prog.t -> RefreshableFormulae(Atom).formula -> unit
   end
   = struct 
        module F = RefreshableFormulae(Atom)

        (* A cont is just the program plus the or list,
           i.e. a list of bindings * head of and_list * tl of and_list *)
        type cont =
          Prog.t * (Atom.bindings * F.formula * F.formula list) list

        let run0 prog =
         (* aux binds andl orl f
           (binds,(f::andl))::orl) *)
         let rec aux binds andl orl =
          function
             F.True ->                  (* (True::andl)::orl *)
              (match andl with
                  [] -> Some (binds,orl)       (* (binds,[])::orl *)
                | hd::tl -> aux binds tl orl hd) (* (hd::tl)::orl *) 

           | F.Atom i ->                (*  (A::and)::orl) *)                       
               (match Prog.backchain binds i prog with              
                   [] ->
                    (match orl with
                        [] -> None
                      | (bnd,f,andl)::tl -> aux bnd andl tl f)
                 | (bnd,f)::tl ->
                     aux bnd andl
                      (List.append
                        (List.map (fun (bnd,f) -> bnd,f,andl) tl)
                        orl) f)
                    
           | F.And (f1, f2) ->             (* ((f1,f2)::andl)::orl *)
              aux binds (f2::andl) orl f1  (* (f1::(f2::andl))::orl *)

           | F.Or (f1, f2) ->              (* ((f1;f2)::andl)::orl) *)
              aux binds andl ((binds,f2,andl)::orl) f1
                                           (* (f1::andl)::(f2::andl)::orl *)
         in
          aux


        let run_next prog binds andl orl f =
         let time0 = Unix.gettimeofday() in
         let res =
          match run0 prog binds andl orl f with
             Some (binds,orl) -> Some (binds,(prog,orl))
           | None -> None in
         let time1 = Unix.gettimeofday() in
         prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
         res

        let run prog f = run_next prog (Atom.empty_bindings) [] [] f

        let next (prog,orl) =
          match orl with
            [] -> None
          | (binds,f,andl)::orl -> run_next prog binds andl orl f

        let main_loop prog query =
         let rec aux =
          function
             None -> prerr_endline "Fail"
           | Some (l,cont) ->
              prerr_endline (Atom.pp_bindings l) ;
              prerr_endline "More? (Y/n)";
              if read_line() <> "n" then
               aux (next cont)
         in
          aux (run prog query)

     end

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

module type TermT =
   sig
            type varT
        type funcT
            type term = Var of varT | App of funcT * (term list)
        val pp : term -> string
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
        val empty_bindings: bindings
        (* bind sigma v t = sigma [v |-> t] *)
        val bind : bindings -> varT -> termT -> bindings
        (* lookup sigma v = Some t   iff  [v |-> t] \in sigma *)
        val lookup : bindings -> varT -> termT option 
   end

module Bindings(Vars: VarT)(Func: FuncT) : 
 BindingsT 
  with type varT := Vars.t
  and type termT := Term(Vars)(Func).term
  =
   struct
        module MapVars = Map.Make(Vars)
        module Terms = Term(Vars)(Func)
        type bindings = Terms.term MapVars.t

        let empty_bindings = MapVars.empty

        let lookup bind k =
         try Some (MapVars.find k bind)
         with Not_found -> None

        let bind bind k v = MapVars.add k v bind

        let pp_bindings bind =
         String.concat "\n"
          (MapVars.fold
            (fun k v s -> (Vars.pp k ^ " |-> " ^ Terms.pp v) :: s)
            bind [])
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

module FOUnif = Unify(Variable)(Func)(Bindings(Variable)(Func))

module FOAtom(Var: VarT)(Func: FuncT)(Bind: BindingsT with type termT := Term(Var)(Func).term and type varT := Var.t) :
 RefreshableAtomT
  with type t = Term(Var)(Func).term
=
 struct
   include RefreshableTerm(Var)(Func)
   include Bind
   include Unify(Var)(Func)(Bind)
   type t = term
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
 end

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

(* ------------ test rev.mod --------------- *)

let x1 = App(1,[])
let x2 = App(2,[])
let x3 = App(3,[])
let x4 = App(4,[])
let x5 = App(5,[])
let x6 = App(6,[])
let x7 = App(7,[])
let x8 = App(8,[])
let x9 = App(9,[])
let x10 = App(10,[])

let xnil = App(100,[])
let xcons = 101
let append = 102
let aux = 103
let rev = 104

let l = Var (Variable.fresh ())
let l1 = Var (Variable.fresh ())
let rl = Var (Variable.fresh ())
let x = Var (Variable.fresh ())
let ls = Var (Variable.fresh ())
let acc = Var (Variable.fresh ())
let r = Var (Variable.fresh ())
let xs = Var (Variable.fresh ())

(*
rev L RL  :- aux L xnil  RL .
aux xnil  L  L .
aux (xcons X XS)  ACC  R :- aux XS (xcons X ACC) R . 
append xnil L L .
append (xcons X XS) L (xcons X L1)  :- append XS L L1 .
*)
let prog =
 [ 
   App(rev,[l ; rl]), Atom(App(aux,[l ; xnil ; rl]))

 ; App(aux,[xnil ; l ; l]), True
 ; App(aux,[App(xcons,[x ; xs]) ; acc ; r]), Atom(App(aux,[xs ; App(xcons,[x ; acc]) ; r]))

 ; App(append,[xnil ; l ; l]), True
 ; App(append,[App(xcons,[x ; xs]) ; l ; App(xcons,[x ; l1])]), Atom(App(append,[xs ; l ; l1]))
 ]
;;

(* X1 =  (xcons x1 (xcons x2 (xcons x3 (xcons x4 (xcons x5 (xcons x6 (xcons x7 (xcons x8 (xcons x9 (xcons x10 xnil)))))))))) *)
let query =
let _bigX1 = 
App(xcons, [x1 ; App(xcons, [x2 ; App(xcons, [x3 ; 
App(xcons, [x4 ; App(xcons, [x5 ; App(xcons, [x6 ; 
App(xcons, [x7 ; App(xcons, [x8 ; App(xcons, [x9 ; 
App(xcons, [x10 ; xnil])])])])])])])])])]) in
let _bigY = Var (Variable.fresh ()) in
let _bigZ = Var (Variable.fresh ()) in
let _bigX2 = Var (Variable.fresh ()) in
let _bigX3 = Var (Variable.fresh ()) in
let _bigX4 = Var (Variable.fresh ()) in
let _bigX5 = Var (Variable.fresh ()) in
let _bigX6 = Var (Variable.fresh ()) in
let _bigX7 = Var (Variable.fresh ()) in
let _bigX8 = Var (Variable.fresh ()) in
let _bigX9 = Var (Variable.fresh ()) in
let _bigX10 = Var (Variable.fresh ()) in
let _bigX11 = Var (Variable.fresh ()) in
let _bigX12 = Var (Variable.fresh ()) in
let _bigX13 = Var (Variable.fresh ()) in
let _bigX14 = Var (Variable.fresh ()) in
let _bigX15 = Var (Variable.fresh ()) in
let _bigX16 = Var (Variable.fresh ()) in
let _bigX17 = Var (Variable.fresh ()) in
let _bigX18 = Var (Variable.fresh ()) in
let querylist = [
Atom (App(append,[_bigX1 ; _bigX1 ; _bigX2])) ;
(*Atom (App(append,[_bigX2 ; _bigX2 ; _bigX3])) ;
Atom (App(append,[_bigX3 ; _bigX3 ; _bigX4])) ;
Atom (App(append,[_bigX4 ; _bigX4 ; _bigX5])) ;
Atom (App(append,[_bigX5 ; _bigX5 ; _bigX6])) ;
Atom (App(append,[_bigX6 ; _bigX6 ; _bigX7])) ;
Atom (App(append,[_bigX7 ; _bigX7 ; _bigX8])) ;
Atom (App(append,[_bigX8 ; _bigX8 ; _bigX9])) ;
Atom (App(append,[_bigX9 ; _bigX9 ; _bigX10])) ;
Atom (App(append,[_bigX10 ; _bigX10 ; _bigX11])) ;
Atom (App(append,[_bigX11 ; _bigX11 ; _bigX12])) ;
Atom (App(append,[_bigX12 ; _bigX12 ; _bigX13])) ;
Atom (App(append,[_bigX13 ; _bigX13 ; _bigX14])) ;
Atom (App(append,[_bigX14 ; _bigX14 ; _bigX15])) ;
Atom (App(append,[_bigX15 ; _bigX15 ; _bigX16])) ;
Atom (App(append,[_bigX16 ; _bigX16 ; _bigX17])) ;
Atom (App(append,[_bigX17 ; _bigX17 ; _bigX18])) ;*)
Atom (App(rev,[_bigX2 ; _bigY])) ;
Atom (App(rev,[_bigY ; _bigZ])) ] in
  List.fold_left (fun fla acc -> FOFormulae.And(fla,acc)) True querylist
;;

(* RUN with non indexed engine *)
prerr_endline ("Testing " ^ FOFormulae.pp query);
let loadedprog = FOProgram.make prog in
RunFO.main_loop loadedprog query;

(* RUN with indexed engine *)
module FOAtomImplHash = HashableFOAtom(Variable)(Func)(Bindings(Variable)(Func))
module FOProgramHash = ProgramHash(FOAtomImplHash)
module RunFOHash = Run(FOAtomImplHash)(FOProgramHash);;
prerr_endline ("Testing with index " ^ FOFormulae.pp query);
let loadedprog = FOProgramHash.make (Obj.magic prog) in
RunFOHash.main_loop loadedprog (Obj.magic query)

(* RUN with two levels inefficient indexed engine *)
module FOAtomImplApprox = ApproximatableFOAtom(Variable)(Func)(Bindings(Variable)(Func))
module FOProgramApprox = ProgramIndexL(FOAtomImplApprox)
module RunFOApprox = Run(FOAtomImplApprox)(FOProgramApprox);;
prerr_endline ("Testing with two level inefficient index " ^ FOFormulae.pp query);
let loadedprog = FOProgramApprox.make (Obj.magic prog) in
RunFOApprox.main_loop loadedprog (Obj.magic query)
