(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

module U   = NUri
module R   = NReference
module C   = NCic
module P   = NCicPp
module E   = NCicEnvironment
(* elpi interface *)
module LPA = Elpi_ast
module LPP = Elpi_parser
module LPD = Elpi_API.Data
module LPR = Elpi_API.Runtime
module LPC = Elpi_API.Compiler
(* elpi initialization only *)
module LPT = Elpi_trace
module LPX = Elpi_custom (* registers the custom predicates, if we need them *)

exception Error of string

type engine = Kernel
            | Refiner

type outcome = Skip of string
             | Fail
             | OK
             | Timeout

type kernel_t = NO | FG of int | CSC

type tag = SORT | PROD | ABST | ABBR | APPL | CASE | HOLE | VECT

type query = QueryType | QueryExpansion

type query_result = GetType of LPA.term
                  | GetExpansion of (int * LPA.term)
(*
                  | GetConstructor
                  | GetInductive
                  | GetFixpoint
*)

module Query = struct
   type t = query * R.reference
   let equal (q1, r1) (q2, r2) = (q1 = q2) && R.eq r1 r2
   let hash (q, r) = Hashtbl.hash q + R.hash r
end

module QH = Hashtbl.Make(Query)

(* variables ****************************************************************)

let matita_dir = Filename.dirname (Sys.argv.(0))

let kernel = ref NO

let maxsteps = ref max_int

let error s = raise (Error s)

let get_program kernel =
   let paths, filenames_kernel, filenames_refiner = match kernel with
      | FG 0 -> ["../../elpi"; "../../lib"; "../../refiner-ALT-0"; ],
                [ "debug_front.elpi";
                  "kernel_matita.elpi";
                  "kernel.elpi";
                  "debug_end.elpi";
                ],
                [ "debug_front.elpi";
                  "kernel_matita.elpi";
                  "kernel.elpi";
                  "debug_end.elpi";
                ]
      | FG 1 -> [ "../../elpi"; "../../lib"; "../../refiner-ALT-1"; ],
                [ "kernel_trace.elpi";
                  "kernel.elpi";
                  "kernel_matita.elpi";
                ],
                [ "kernel_trace.elpi";
                  "kernel.elpi";
                  "kernel_matita.elpi";
                ]
      | CSC  -> [ "../../elpi"; "../../refiner-CSC"; ],
                [ "all_kernel.elpi" ],
                [ "all_refiner.elpi" ]
      | _    -> [ "../.."; ], [], []
   in
   let ast_kernel,ast_refiner =
     if filenames_kernel <> [] then begin
       let paths = List.map (Filename.concat matita_dir) paths in
       let args = List.map (fun x -> ["-I";x]) paths in
       let _args = Elpi_API.init (List.flatten args) Sys.(getcwd ()) in
       LPP.parse_program filenames_kernel, LPP.parse_program filenames_refiner
     end else [],[] in
   LPC.program_of_ast ast_kernel, LPC.program_of_ast ast_refiner

let kernel_program, refiner_program =
 let kernel,refiner = get_program !kernel in
 ref kernel, ref refiner

let current = ref None

let seen = ref []

let verbose = ref true

let print_constraints = ref true

let caching = ref false

let validate = ref true

let refine = ref true

(* guess based on nat.ma *)
let cache_size = 223

let cache = QH.create cache_size

let status = new P.status

(* internals ****************************************************************)

let fail () = raise LPD.No_clause

let xlate tag = match !kernel, tag with
   | NO  , _    -> "??"
   | _   , SORT -> "sort"
   | FG _, PROD -> "prod"
   | CSC , PROD -> "arr"
   | FG _, ABST -> "abst"
   | CSC , ABST -> "lam"
   | _   , ABBR -> "abbr"
   | FG _, APPL -> "appl"
   | CSC , APPL -> "app"
   | FG _, CASE -> "case"
   | CSC , CASE -> "match"
   | _   , HOLE -> "hole"
   | _   , VECT -> "vect"

let rt_gref r =
   let R.Ref (uri, spec) = r in
   let _, _, _, _, obj = E.get_checked_obj status uri in
   match obj, spec with
      | C.Constant (_, _, None, u, _)  , R.Decl          ->
         None, u
      | C.Constant (_, _, Some t, u, _), R.Def h         ->
         Some (h, t), u
      | C.Fixpoint (true, fs, _)       , R.Fix (i, _, h) ->
         let _, _, _, u, t = List.nth fs i in
         Some (h, t), u
      | C.Fixpoint (false, fs, _)      , R.CoFix i       ->
         let _, _, _, u, _ = List.nth fs i in
         None, u
      | C.Inductive (_, _, us, _)      , R.Ind (_, i, _) ->
         let _, _, u, _ = List.nth us i in
         None, u
      | C.Inductive (_, _, us, _)      , R.Con (i, j, _) ->
         let _, _, _, ws = List.nth us i in
         let _, _, w = List.nth ws (pred j) in
         None, w
      | _                                                ->
         assert false

let ind_gref r =
   let R.Ref (uri, spec) = r in
   let _, _, _, _, obj = E.get_checked_obj status uri in
   match obj, spec with
      | C.Inductive (_, _, us, _)      , R.Ind (_, i, k) ->
         let _, _, _, ws = List.nth us i in
         uri, i, k, List.length ws
      | _                                                ->
         fail ()

let id x = "u+" ^ x

let univ_of u =
   try Scanf.sscanf (U.string_of_uri u) "cic:/matita/pts/Type%s@.univ" id
   with Scanf.Scan_failure _ | End_of_file -> assert false

let mk_univ s =
   let cons = match s with
      | C.Prop             -> ["s+prop"]
      | C.Type []          -> ["s+type"; "u+0"]
      | C.Type [`Type, u]  -> ["s+type"; univ_of u]
      | C.Type [`CProp, u] -> ["s+cprop"; univ_of u]
      | _                  -> assert false (* for now we process just universes in normal form *)
   in
   LPA.mkApp (List.map LPA.mkCon cons)

let mk_nil = LPA.mkNil

let mk_cons v vs = LPA.mkSeq [v; vs]
(* Parked code:
let mk_pi n f = LPA.mkApp [LPA.mkCon "pi"; LPA.mkLam n f]

let mk_impl a b = LPA.mkApp [LPA.mkCon "=>"; a; b]

let mk_pi_impl n a b = mk_pi n (mk_impl a b)
*)
let mk_head x = LPA.mkCon (xlate x)

let mk_name i = Printf.sprintf "x%u" i

let mk_lref c i = LPA.mkCon (mk_name (c - i))

let mk_gref r = LPA.mkCon (R.string_of_reference r)

let mk_sort s = LPA.mkApp [mk_head SORT; mk_univ s]

let mk_meta l = LPA.mkApp (LPA.mkFreshUVar ()::l)

let mk_prod n w t = LPA.mkApp [mk_head PROD; w; LPA.mkLam (mk_name n) t]

let mk_abst n w t = LPA.mkApp [mk_head ABST; w; LPA.mkLam (mk_name n) t]

let mk_abbr n w v t = LPA.mkApp [mk_head ABBR; w; v; LPA.mkLam (mk_name n) t]

let mk_appl t v = LPA.mkApp [mk_head APPL; t; v]

let mk_case w v u ts = LPA.mkApp [mk_head CASE; w; u; v; ts]

let mk_hole () = LPA.mkApp [mk_head HOLE]

let mk_vect () = LPA.mkApp [mk_head VECT]

let mk_is_type u time = LPA.mkApp [LPA.mkCon "is_type"; u; time]

let mk_has_type t u time = LPA.mkApp [LPA.mkCon "has_type"; t; u; time]

let mk_approx t v w time = LPA.mkApp [LPA.mkCon "approx"; t; v; w; time]

let mk_approx_cast t u v time =
  LPA.mkApp [LPA.mkCon "approx_cast"; t; u; v; time]

(* matita to elpi *)
let rec lp_term status d c = function
   | C.Implicit `Vector    -> mk_vect ()
   | C.Implicit _          -> mk_hole ()
   | C.Meta (i, (liftno,lc as l))         ->
      begin try
         let _, _, v, _ = List.assoc i d in
         lp_term status d c (NCicSubstitution.subst_meta status l v)
      with Not_found ->
       let lc = NCicUtils.expand_local_context lc in
       let lc = List.map (NCicSubstitution.lift status liftno) lc in
       let lc = List.map (lp_term status d c) lc in
       mk_meta lc (*error "meta here" (* uncomment to use fresh metas *)*)
      end
   | C.Rel i               -> mk_lref c i
   | C.Const r             -> mk_gref r
   | C.Sort s              -> mk_sort s
   | C.Prod (_, w, t)      -> mk_prod c (lp_term status d c w) (lp_term status d (succ c) t)
   | C.Lambda (_, w, t)    -> mk_abst c (lp_term status d c w) (lp_term status d (succ c) t)
   | C.LetIn (_, w, v, t)  -> mk_abbr c (lp_term status d c w) (lp_term status d c v) (lp_term status d (succ c) t)
   | C.Appl []             -> assert false
   | C.Appl [t]            -> lp_term status d c t
   | C.Appl [t; v]         -> mk_appl (lp_term status d c t) (lp_term status d c v)
   | C.Appl (t :: v :: vs) -> lp_term status d c (C.Appl (C.Appl [t; v] :: vs))
   | C.Match (r, u, v, ts) -> mk_case (mk_gref r) (lp_term status d c v) (lp_term status d c u) (lp_terms status d c ts)

and lp_terms status d c = function
   | []      -> mk_nil
   | v :: vs -> mk_cons (lp_term status d c v) (lp_terms status d c vs)

let split_type r =
   let aux () =
      let _, u = rt_gref r in lp_term status [] 0 u
   in
   if !caching then match QH.find_all cache (QueryType, r) with
      | [GetType x] -> x
      | []          ->
         let x = aux () in
         QH.add cache (QueryType, r) (GetType x);
         x
      | _           -> assert false
   else aux ()

let split_expansion r =
   let aux () = match rt_gref r with
      | Some (h, t), _ -> h, lp_term status [] 0 t
      | _              -> fail ()
   in
   if !caching then match QH.find_all cache (QueryExpansion, r) with
      | [GetExpansion x] -> x
      | []               ->
         let x = aux () in
         QH.add cache (QueryExpansion, r) (GetExpansion x);
         x
      | _                -> assert false
   else aux ()

let split_inductive r =
   let uri, i, k, l = ind_gref r in
   let rec mk_list js j =
      if j < 1 then js else
      let s = R.reference_of_spec uri (R.Con (i,j,k)) in
      mk_list (mk_cons (mk_gref s) js) (pred j)
   in
   k, mk_list mk_nil l

let split_constructor = function
   | R.Ref (_, R.Con (_, j, k)) -> pred j, k
   |_                           -> fail ()

let split_fixpoint = function
   | R.Ref (_, R.Fix (_, l, _)) -> l
   |_                           -> fail ()

let mk_term ~depth t =
   LPC.term_of_ast ~depth t

let mk_int ~depth i =
   LPC.term_of_ast ~depth (LPA.mkInt i)

let mk_eq t1 t2 = LPD.App (LPD.Constants.eqc, t1, [t2])

let mk_true ~depth = LPC.term_of_ast ~depth (LPA.mkCon "true")

let show = LPD.Constants.show

let dummy = LPD.Constants.dummy

let rec get_gref ~depth = function
   | LPD.Const c                                                    ->
       if c >= 0 then fail () else R.reference_of_string (show c)
   | LPD.UVar ({LPD.contents=t;_},vardepth,args) when t != dummy    ->
      get_gref ~depth (LPR.deref_uv ~from:vardepth ~to_:depth args t)
   | LPD.AppUVar ({LPD.contents=t;_},vardepth,args) when t != dummy ->
      get_gref ~depth (LPR.deref_appuv ~from:vardepth ~to_:depth args t)
   | _                                                              -> fail ()

let get_gref f ~depth t =
   try f (get_gref ~depth t) with
      | Failure "nth"
      | Invalid_argument "List.nth"
      | R.IllFormedReference _
      | E.ObjectNotFound _
      | LPD.No_clause           -> fail ()

let get_type ~depth ~env:_ _ = function
   | [t1; t2] ->
      let u1 = get_gref split_type ~depth t1 in
      [mk_eq (mk_term ~depth u1) t2]
   | _        -> fail ()

let get_expansion ~depth ~env:_ _ = function
   | [t1; t2; t3] ->
      let h, t = get_gref split_expansion ~depth t1 in
      [mk_eq (mk_int ~depth (-h)) t2; mk_eq (mk_term ~depth t) t3]
   | _            -> fail ()

let get_constructor ~depth ~env:_ _ = function
   | [t1; t2; t3] ->
      let j, k = get_gref split_constructor ~depth t1 in
      [mk_eq (mk_int ~depth j) t2; mk_eq (mk_int ~depth k) t3]
   | _            -> fail ()

let get_inductive ~depth ~env:_ _ = function
   | [t1; t2; t3] ->
      let k, ts = get_gref split_inductive ~depth t1 in
      [mk_eq (mk_int ~depth k) t2; mk_eq (mk_term ~depth ts) t3]
   | _            -> fail ()

let get_fixpoint ~depth ~env:_ _ = function
   | [t1; t2] ->
      let l = get_gref split_fixpoint ~depth t1 in
      [mk_eq (mk_int ~depth l) t2]
   | _        -> fail ()

let on_object ~depth ~env:_ _ args = match args, !current with
   | [t1], Some t ->
      [mk_eq (mk_term ~depth t) t1]
   | _            -> fail ()

let after_object ~depth ~env:_ _ args = match args with
   | [t1] ->
      let pred t = mk_term ~depth t = t1 in
      if List.exists pred !seen then [mk_true ~depth] else fail ()
   | _    -> fail ()

(* initialization ***********************************************************)

let _ =
   LPR.register_custom "$get_type" get_type;
   LPR.register_custom "$get_expansion" get_expansion;
   LPR.register_custom "$get_constructor" get_constructor;
   LPR.register_custom "$get_inductive" get_inductive;
   LPR.register_custom "$get_fixpoint" get_fixpoint;
   LPR.register_custom "$on_object" on_object;
   LPR.register_custom "$after_object" after_object

(* interface ****************************************************************)

let set_kernel e =
   kernel := e;
   let program_ker, program_ref = get_program e in
   kernel_program := program_ker;
   refiner_program := program_ref

(* Note: to be replaced by String.uppercase_ascii *)
let set_kernel_from_string s = match String.uppercase s with
   | "NO"  -> set_kernel NO
   | "FG0" -> set_kernel (FG 0)
   | "FG1" -> set_kernel (FG 1)
   | "FG2" -> set_kernel (FG 2)
   | "CSC" -> set_kernel CSC
   | _     -> ()

let prints_off () =
   verbose := false;
   print_constraints := false

let cache_on () =
   caching := true

let total_query_time = ref 0.0

let at_exit () =
(*
   let string_of_query = function
      | QueryType      -> "?TypeOf"
      | QueryExpansion -> "?ExpansionOf"
   in
   let map (q, r) _ =
      Printf.eprintf "%s %s\n%!" (string_of_query q) (R.string_of_reference r)
   in
      QH.iter map cache;
*)
   if !caching then begin
      Printf.eprintf "cache length: %u\n%!" (QH.length cache)
   end;
   print_endline ("ELPI whole query-execution time: " ^
      string_of_float !total_query_time
   )

let trace_options = ref []
let typecheck = ref false

let set_apply_subst, apply_subst =
 let g : (NCic.status -> NCic.substitution -> NCic.context -> NCic.term -> NCic.term) ref = ref (fun _ -> assert false) in
 (function f -> g := f),
 (fun x -> !g x)
;;

let apply_subst x = apply_subst (x :> NCic.status);;

let apply_subst_to_closure status is_type d c t =
   let rec aux t = function
      | []                        -> t
      | (name, C.Def (v, w)) :: c ->
         aux (C.LetIn (name, w, v, t)) c
      | (name, C.Decl w)     :: c ->
         aux (if is_type then C.Prod (name, w, t) else C.Lambda (name, w, t)) c
   in
   apply_subst status d [] (aux t c)

let execute engine status r query =
   let str = R.string_of_reference r in
   let str = str ^ " (" ^ (match engine with Kernel -> "kernel" | Refiner -> "refiner") ^ ")" in
   if !verbose then Printf.printf "ELPI ?? %s\n%!" str;
   let t = lp_term status [] 0 (C.Const r) in
   current := Some t;
   let result, msg, time = try
      if engine = Kernel && not !validate then error "not validating";
      if engine = Refiner && not !refine then error "not refining";
      let program = match engine with
         | Kernel  -> !kernel_program
         | Refiner -> !refiner_program
      in
      let query, get_lp_time =
        let time = LPA.mkCon "TIME" in
        LPC.query_of_ast program (Ploc.dummy, query time),
        fun s ->
          match LPD.SMap.find "TIME" s with
          | LPD.CData d when LPD.CD.is_float d -> LPD.CD.to_float d
          | _ -> assert false
        in
      if !typecheck then LPC.typecheck program query;
      Elpi_API.trace !trace_options;
      Format.pp_set_margin Format.err_formatter 250;
      Format.pp_set_margin Format.std_formatter 250;
      let t0 = Unix.gettimeofday () in
      let time () =
        let t1 = Unix.gettimeofday () in
        t1 -. t0 in
      let (_,_,timediff) as res =
        try 
          match 
            LPR.execute_once program
               ~max_steps:!maxsteps ~print_constraints:!print_constraints query 
          with
          | `Success s -> OK, "OK", get_lp_time (Lazy.force s)
          | `Failure -> Fail, "KO", time ()
          | `NoMoreSteps ->
               Timeout, Printf.sprintf "KO(steps=%d)" !maxsteps, time ()
        with e -> Fail, Printexc.to_string e, time () in
      total_query_time := !total_query_time +. timediff;
      res
      with Error s -> Skip s, "OO[" ^ s ^ "]", 0.0
   in
   if !verbose then Printf.printf "ELPI %s %s\n%!" msg str;
   if engine = Kernel && not (List.mem t !seen) then seen := t :: !seen;
   time,result

let is_type status r u =
   let query time = mk_is_type (lp_term status [] 0 u) time in
   execute Kernel status r query

let has_type status r t u =
   let query time =
     mk_has_type (lp_term status [] 0 t) (lp_term status [] 0 u) time in
   execute Kernel status r query

let approx status r c s1 t s2 v w =
   let t = apply_subst_to_closure status false s1 c t in
   let v = apply_subst_to_closure status false s2 c v in
   let w = apply_subst_to_closure status true  s2 c w in
   let query time = mk_approx (lp_term status [] 0 t) (lp_term status [] 0 v) (lp_term status [] 0 w) time in
   execute Refiner status r query

let approx_cast status r c s1 t u s2 v =
   let t = apply_subst_to_closure status false s1 c t in
   let u = apply_subst_to_closure status true  s1 c u in
   let v = apply_subst_to_closure status false s2 c v in
   let query time = mk_approx_cast (lp_term status [] 0 t) (lp_term status [] 0 u) (lp_term status [] 0 v) time in
   execute Refiner status r query
