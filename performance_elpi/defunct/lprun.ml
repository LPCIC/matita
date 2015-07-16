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

(* ImpVariable *)
        type vart = Obj.t option ref

        let ppvar _ = "??"
        let compare x y = assert false
        let eq = (==)

        type refresher = (Obj.t option ref * Obj.t option ref) list
        let empty_refresher = []

        let varfresh,varrefresh =
         let fresh () = ref None in
          fresh,
          (fun l n ->
            try l,List.assq n l
            with Not_found ->
             let n' = fresh () in
             (n,n')::l,n')

(* FuncS *)
    let ppfunc n = n
    let eq = (=)

(* Term *)
     type term = Var of vart | App of string * (term list)

     let rec pp =
      function
         Var v -> ppvar v
       | App(f,l) -> ppfunc f ^"("^ String.concat "," (List.map pp l) ^")"

     (* Note: converters from asts are the same as
        refreshers, but both have fixed types :-(
        Should be made parametric *)
     let var_of_ast l n =
      try l,List.assoc n l
      with Not_found ->
       let n' = varfresh () in
       (n,n')::l,n'

     type converter = (Lprun2.vart * vart) list

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

(* RefreshableTerm *)
   let empty_refresher = []

   let rec refresh l =
    function
       Var v ->
        let l,v = varrefresh l v in
        l, Var v
     | App(f,tl) ->
        let l,rev_tl =
          List.fold_left
           (fun (l,tl) t -> let l,t = refresh l t in (l,t::tl))
           (l,[]) tl
        in
        l, App(f,List.rev rev_tl)

(* ImpBindings *)
     type bindings = unit (* TODO Trail goes here *)

     let empty_bindings = ()
        
     let lookup _ k = Obj.magic !k

     let bind _ k v = k := Some (Obj.magic v)

     let cardinal _ = (), (-1)

     let pp_bindings _ = "<< no way to print >>"
        
     let filter f _ = assert false (* TODO assign None *)

(* FOAtom *)
   let atom_of_ast = term_of_ast

(* ??? *)
  let index =
   function
      App(f,_) -> f
    | Var _ -> raise (Failure "Ill formed program")


(* Formulae *)
        type formula = 
                And of formula * formula
              | Or of formula * formula
              | True
              | Cut
              | Atom of term;;

        let rec forpp =
         function
            And(f1,f2) -> "(" ^ forpp f1 ^ "," ^ forpp f2 ^ ")"
          | Or(f1,f2) -> "(" ^ forpp f1 ^ ";" ^ forpp f2 ^ ")"
          | True -> "true"
          | Cut -> "!"
          | Atom a -> pp a

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
             let k,t = atom_of_ast k t in
             k,Atom t

        let query_of_ast t = snd (formula_of_ast [] t)

        let program_of_ast p =
         List.map (fun (a,f) ->
          let l,a = atom_of_ast [] a in
          let _,f = formula_of_ast l f in
          a,f) p


(* RefreshableFormulae *)


        let refresh (hd,bo) =
         let l = [] in
         let l,hd = refresh l hd in
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
              let l,a = refresh l a in
              l, Atom a in
          let _,bo = aux l bo in
          (hd,bo)

(* Unify *)

        let rec unify sub t1 t2 = match t1,t2 with
            (Var v1, Var v2) when v1==v2 -> sub
            | (Var v1, _) ->
                (match lookup sub v1 with
                   None -> bind sub v1 t2
                 | Some t -> unify sub t t2)
          | (_, Var _) -> unify sub t2 t1
          | (App (f1,l1), App (f2,l2)) -> 
                if f1=f2 && List.length l1 = List.length l2 then
                  List.fold_left2 unify sub l1 l2
                else
                  raise (NotUnifiable (lazy "rms are not unifiable!"))

(* ProgramHash *)
     module Hash = Hashtbl
                  
   (* backchain: bindings -> atomT -> 
                         Form.formula Hash.t -> 
                            (bindings * formulaT) list           *)
     let backchain binds a h =
       let l = List.rev (Hash.find_all h (index a)) in
       filter_map (fun clause -> 
         let atom,f = refresh clause in
         try
           let binds = unify binds atom a in 
             Some (binds,f)
           with NotUnifiable _ -> None) 
         l                       
        
     let make p =
       let h = Hash.create 199 in
       List.iter
         (fun ((a,v) as clause) -> Hash.add h (index a) clause) p;
       h


(* Run *)

        (* A cont is just the program plus the or list,
           i.e. a list of level * bindings * head of and_list * tl of and_list 
           The level is incremented when there is a *)

        (* WARNING: bad non reentrant imperative code here
           At least query should go into the continuation for next
           to work!
        *)
        let query = ref True;;

        let run0 prog =
         (* aux lvl binds andl orl f
           (lvl,binds,(f::andl))::orl) *)
         let rec aux lvl binds andl orl f =
          match f with
             True ->                  (* (True::andl)::orl *)
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
           | Cut ->
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
           | Atom i ->         (*A::and)::orl)*)                      
               (match backchain binds i prog with              
                   [] ->
                    (match orl with
                        [] -> None
                      | (lvl,bnd,f,andl)::tl -> aux lvl bnd andl tl f)
                 | (bnd,f)::tl ->
                     aux (lvl+1) bnd andl
                      (List.append
                        (List.map (fun (bnd,f) -> lvl+1, bnd,f,andl) tl)
                        orl) f)
                    
           | And (f1, f2) ->             (* ((f1,f2)::andl)::orl *)
              aux lvl binds (f2::andl) orl f1  (* (f1::(f2::andl))::orl *)

           (* Because of the +2 vs +1, the semantics of (c,! ; d)
              is to kill the alternatives for c, preserving the d one.
              Note: this is incoherent with the semantics of ! w.r.t.
              backchaining, but that's what Tejyus implements. *)
           | Or (f1, f2) ->              (* ((f1;f2)::andl)::orl) *)
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
              Gc.full_major() ; let binds,size = cardinal binds in
              prerr_endline ("Final bindings size: " ^ string_of_int size) ;
              Some (binds,orl)
           | None -> None)

        let run prog f =
         query := f ;
         run_next prog 0 (empty_bindings) [] [] f

        let next (prog,orl) =
          match orl with
            [] -> None
          | (lvl,binds,f,andl)::orl -> run_next prog lvl binds andl orl f

        let main_loop prog query =
         let rec aux =
          function
             None -> prerr_endline "Fail"
           | Some (l,cont) ->
              prerr_endline ("Query: " ^ forpp query) ;
              prerr_endline (pp_bindings l) ;
              prerr_endline "More? (Y/n)";
              if read_line() <> "n" then
               aux (next cont)
         in
          aux (run prog query)



let implementations =
 let impl9 =
  (* RUN with indexed engine *)
  let descr = "Testing with imperative one level index hashtbl " in
  (module
 struct
  (* RUN with non indexed engine *)
  type query = formula
  type program = (term * formula) list
  let query_of_ast = query_of_ast
  let program_of_ast = program_of_ast
  let msg q = descr ^ forpp q
  let execute_once p q = run (make p) q = None
  let execute_loop p q = main_loop (make p) q
 end
  : Lprun2.Implementation) in


 [impl9]
;;
