(***** real code *****)

exception NotFormula of string Lazy.t;;

module type TermT =
  sig  
    type funct
    type term =
       Var of term array * int
     | App of funct * term array
    type vart = term array * int

    type formula =
       Cut
     | Atom of term
     | And of term list
     | Or of term list

    val eq_var : vart -> vart -> bool
    type refresher
    val empty_refresher : refresher
    val refresh_var : refresher -> vart -> term array -> refresher * vart

    val deref : vart -> term
    val assign : vart -> term -> unit

    val mkAnd : term list -> term
    val mkOr : term list -> term

    (* raise NotAFormula *)
    val as_formula: term -> formula

    val pp: term -> string

    val query_of_ast : Lprun2.term -> term
    val program_of_ast : (Lprun2.term * Lprun2.term) list -> (term * term) list
  end;;

module Term(Func: Lprun2.FuncT) : TermT 
    with type funct = Func.t 
 = 
  struct
    type funct = Func.t

    type term =
       Var of term array * int
     | App of Func.t * term array
    and vart = term array * int

    let eq_var (args1,i1) (args2,i2) = args1==args2 && i1=i2

    let deref (args,i) = args.(i)
    let assign (args,i) t = args.(i) <- t

    type formula =
      Cut
    | Atom of term
    | And of term list
    | Or of term list

    let rec pp = 
      function 
        Var (_,i) -> "X" ^ string_of_int i
      | App(f, args) -> 
          Func.pp f ^ "(" ^ String.concat " " (List.map pp (Array.to_list args)) ^ ")"

    let mkAnd = function [f] -> f | l -> App(Func.andf,Array.of_list l)
    let mkOr  = function [f] -> f | l -> App(Func.orf,Array.of_list l)
    
     (* raise NotAFormula *)
    let as_formula =
      function
        Var _ -> raise (NotFormula (lazy "Trying to prove a variable"))
      | App(f,l) as x->
         (* And [] is interpreted as false *)
         if Func.eq f Func.andf then And (Array.to_list l)
         (* Or [] is interpreted as true *)
         else if Func.eq f Func.orf then Or (Array.to_list l)
         else if Func.eq f Func.cutf then Cut
         else Atom x

    type refresher = (vart * vart) list
    let empty_refresher = []
 
    let refresh_var l ((_,i0) as v) args =
     try l,snd (List.find (fun (x,_) -> eq_var x v) l)
     with Not_found ->
      let v' = args,i0 in
      (v,v')::l, v'

    let var_of_ast l v args i =
     try l,snd (List.find (fun x -> Lprun2.Variable.eq v (fst x)) l)
     with Not_found ->
      let v' = args,i in
      (v,v')::l, v'


     let rec term_of_ast l =
      let rec aux args i l =
       function
         Lprun2.Var v ->
          let l,(args,i) = var_of_ast l v args i in
          l, Var (args,i)
       | Lprun2.App(f,tl) ->
          let tl' = Array.make (List.length tl) (Obj.magic ()) (* dummy *) in
          let l = ref l in
          List.iteri (fun i t -> let l',t' = aux tl' i !l t in l := l' ; tl'.(i) <- t') tl ;
          (* TODO: convert the Funcs too *)
          !l, App(Obj.magic f,tl')
      in
       aux [||] (-999) l

    let query_of_ast t = snd (term_of_ast [] t)

    let program_of_ast p =
     List.map (fun (a,f) ->
      let l,a = term_of_ast [] a in
      let _,f = term_of_ast l f in
      a,f) p
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


module RefreshableTerm(Func:Lprun2.FuncT) : RefreshableTermT
  with  type funct = Func.t
  and  type term = Term(Func).term 
  and  type formula = Term(Func).formula
=
 struct
   include Term(Func)
  
   let refresh l =
    let rec aux args l =
     function
       Var (args',i') ->
        let l,(args,i) = refresh_var l (args',i') args in
        l, Var (args,i)
     | App(f,tl) ->
        let tl = Array.copy tl in
        let l = ref l in
        Array.iteri (fun i t -> let l',t' = aux tl !l t in l := l' ; tl.(i) <- t') tl ;
        !l, App(f,tl)
    in
     aux [||] l
   
   type clause = term * term

   let refresh_clause (hd,bo) =
     let l,hd = refresh empty_refresher hd in
     let _,bo = refresh l bo in
     (hd,bo)

   let refresh_query q = snd (refresh empty_refresher q)

 end;;

module Bindings(Func: Lprun2.FuncT) : Lprun2.BindingsT 
  with type varT = Term(Func).vart
  and type termT = Term(Func).term
  =
   struct
     module T = Term(Func)
     type varT = T.vart
     type termT = T.term

     type bindings = unit (* TODO Trail goes here *)

     let empty_bindings = ()
        
     let lookup _ v =
      match T.deref v with
         T.Var (args',v') when T.eq_var v (args',v') -> None
       | t -> Some t

     let bind _ v t = T.assign v t

     let cardinal _ = (), (-1)

     let pp_bindings _ = "<< no way to print >>"
        
     let filter f _ = assert false (* TODO assign None *)
   end;;

exception NotUnifiable of string Lazy.t

(* DIFFERENCE BETWEEN = AND := IN MODULE TYPE CONSTRAINTS
module type T = sig type t val f : t -> t end
T with type t = int  sig type t = int val f : t -> t end
T with type t := int sig val f: int -> int end *)

module Unify(Func: Lprun2.FuncT)(Bind: Lprun2.BindingsT with type termT = Term(Func).term and type varT = Term(Func).vart) : Lprun2.UnifyT
   with module Bind = Bind
=
  struct
    module T = Term(Func)
    module Bind = Bind

    let rec unify sub t1 t2 = 
      match t1,t2 with
        (T.Var (args1,i1), T.Var (args2,i2)) when T.eq_var (args1,i1) (args2,i2) -> sub
      | (T.Var (args1,i1), _) ->
          (match Bind.lookup sub (args1,i1) with
             None -> Bind.bind sub (args1,i1) t2
           | Some t -> unify sub t t2)
      | (_, T.Var _) -> unify sub t2 t1
      | (T.App (f1,l1), T.App (f2,l2)) -> 
          if Func.eq f1 f2 && Array.length l1 = Array.length l2 then
            Lprun3.array_fold_left2 unify sub l1 l2
          else
            raise (NotUnifiable (lazy "Terms are not unifiable!"))
   end;;

exception NotAnAtom;;

(* No indexing at all; a program is a list and retrieving the clauses
   from the program is O(n) where n is the size of the program.
   Matching is done using unification directly. *)
module Program(Term: RefreshableTermT)(Unify: Lprun2.UnifyT with type Bind.termT = Term.term) : Lprun2.ProgramT with module Bind = Unify.Bind
 =
  struct
    module Bind = Unify.Bind

    type t = (Term.term*Term.term) list
     (* backchain: bindings -> termT -> 
                    (Term.term*Term.term) list -> 
                          (bindings * Term.term) list           *)
    let backchain binds a l =
      Lprun2.filter_map (fun clause -> 
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
module ProgramHash(Term: RefreshableTermT)(Unify: Lprun2.UnifyT with type Bind.termT = Term.term) : Lprun2.ProgramT with module Bind = Unify.Bind =
  struct
     module Bind = Unify.Bind

     let index =
      function
         Term.Var _ -> raise (Failure "Ill formed program")
       | Term.App(f,_) -> f

     module Hash = Hashtbl.Make(
      struct
       (* TODO fixme to remove the Obj.magic *)
       type t = Term.funct (*Lprun2.Lprun2.FuncS.t*)
       let hash = Obj.magic Hashtbl.hash
       let equal = Obj.magic Lprun2.FuncS.eq
      end)
     type t = Term.clause Hash.t
                  
   (* backchain: bindings -> term -> 
                         Term.term Hash.t -> 
                            (bindings * term) list           *)
     let backchain binds a h =
       let l = List.rev (Hash.find_all h (index a)) in
       Lprun2.filter_map (fun clause -> 
         let atom,f = Term.refresh_clause clause in
         try
           let binds = Unify.unify binds atom a in 
             Some (binds,f)
           with NotUnifiable _ -> None) 
         l                       
        
     let make p =
       let h = Hash.create 199 in
       List.iter
         (fun ((a,v) as clause) -> Hash.add h (index a) clause) p;
       h
   end;;

(* Two level inefficient indexing; a program is a list of clauses.
   Approximated matching is used to retrieve the candidates.
   Unification is then performed on the candidates.
   *** NOTE: this is probably redundant and more inefficient than
       just doing eager unification without approximated matching ***
   Retrieving the good clauses is O(n) where n is the size of the
   program. *)
module ProgramIndexL(Term: RefreshableTermT)(Unify: Lprun2.UnifyT with type Bind.termT = Term.term) : Lprun2.ProgramT with module Bind = Unify.Bind =
   struct
        module Bind = Unify.Bind

        (* MODULE APPROXIMATABLE: TO BE MOVED OUTSIDE/ *)
        type approx = Term.funct * (Term.funct option)

        let approx =
         function
            Term.App(f,[||]) -> f,None
          | Term.Var _ -> raise (Failure "Ill formed program")
          | Term.App(f,a) ->
             match a.(0) with
                Term.Var _ -> f,None
              | Term.App(g,_) -> f, Some g

        let matchp app1 app2 =
         match app1,app2 with
            (f1,None),(f2,_)
          | (f1,_),(f2,None)-> f1=f2
          | (f1,Some g1),(f2,Some g2) -> f1=f2 && g1=g2
        (* /MODULE APPROXIMATABLE: TO BE MOVED OUTSIDE *)

        (* triples (app,(a,f)) where app is the approximation of a *)
        type t = (approx * (Term.term * Term.term)) list

        (* backchain: bindings -> atomT -> 
                         Form.formula Hash.t -> 
                            (bindings * formulaT) list           *)
        let backchain binds a l =
          let app = approx a in
          let l = List.filter (fun (a',_) -> matchp app a') l in
          Lprun2.filter_map (fun (_,clause) ->
           let atom,f = Term.refresh_clause clause in
           try
            let binds = Unify.unify binds atom a in 
            Some (binds,f)
           with NotUnifiable _ -> None
           ) l
        ;;
        
        let make =
          List.map (fun ((a,_) as clause) -> approx a,clause)
   end;;


module Run(Term: RefreshableTermT)(Prog: Lprun2.ProgramT with type Bind.termT = Term.term)(*(GC : GCT type formula := Term.formula)*)(*TODO : RESTORE*) :
 Lprun2.RunT with type term := Term.term and type bindingsT := Prog.Bind.bindings
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

module
 Implementation
  (ITerm: TermT)
  (IProgram: Lprun2.ProgramT with type Bind.termT = ITerm.term
                      (*and type bindings := ITerm.bindings*))
  (IRun: Lprun2.RunT with type progT := IProgram.t
              and type bindingsT := IProgram.Bind.bindings
              and type term := ITerm.term)
  (Descr : sig val descr : string end)
 : Lprun2.Implementation
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


let implementations = 
  let impl1 =
    (* RUN with non indexed engine *)
    let module ITerm = RefreshableTerm(Lprun2.FuncS) in
    let module IProgram = Program(ITerm)(Unify(Lprun2.FuncS)(Bindings(Lprun2.FuncS))) in
    let module IRun = Run(ITerm)(IProgram)(*(NoGC(FOAtomImpl))*) in
    let module Descr = struct let descr = "Testing with no index, optimized2 imperative " end in
    (module Implementation(ITerm)(IProgram)(IRun)(Descr)
     : Lprun2.Implementation) in

  let impl2 =
    (* RUN with hashtbl *)
    let module ITerm = RefreshableTerm(Lprun2.FuncS) in
    let module IProgram = ProgramHash(ITerm)(Unify(Lprun2.FuncS)(Bindings(Lprun2.FuncS))) in
    let module IRun = Run(ITerm)(IProgram)(*(NoGC(FOAtomImpl))*) in
    let module Descr = struct let descr = "Testing with one level index, optimized2 imperative " end in
    (module Implementation(ITerm)(IProgram)(IRun)(Descr)
     : Lprun2.Implementation) in

  let impl3 =
    (* RUN with two level inefficient index *)
    let module ITerm = RefreshableTerm(Lprun2.FuncS) in
    let module IProgram = ProgramIndexL(ITerm)(Unify(Lprun2.FuncS)(Bindings(Lprun2.FuncS))) in
    let module IRun = Run(ITerm)(IProgram)(*(NoGC(FOAtomImpl))*) in
    let module Descr = struct let descr = "Testing with two level inefficient index, optimized2 imperative " end in
    (module Implementation(ITerm)(IProgram)(IRun)(Descr)
     : Lprun2.Implementation) in

  [impl1; impl2; impl3]
