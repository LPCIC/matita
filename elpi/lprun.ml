(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Lpdata
open LP
open Subst
open Red

exception UnifFail of string lazy_t

let _ = Trace.pr_exn
  (function UnifFail s -> "unif: "^Lazy.force s | _ -> raise Trace.Unknown)

let fail s = raise (UnifFail (lazy s))
let lfail l = raise (UnifFail l)

let print_unif_prob s rel a b fmt =
  Format.fprintf fmt "@[%a@ %s %a@]%!"
    (prf_data []) (apply_subst s a) rel (prf_data []) (apply_subst s b)

let rec rigid x = match x with
  | Uv _ -> false
  | Tup xs -> rigid (look (IA.get 0 xs))
  | _ -> true

let eta n t = TRACE "eta" (fun fmt -> prf_data [] fmt t)
 let t =
   fixTup (IA.init (n+1) (fun i -> if i = 0 then (lift n t) else mkDB (n+1-i))) in
 SPY "etaed" (prf_data []) t;
 t

let inter xs ys = IA.filter (fun x -> not(IA.for_all (equal x) ys)) xs

(* construction of bindings: ↓ is ^- and ⇑ is ^= *)
let cst_lower xs lvl =
  IA.filter (fun x -> match look x with Con(_,l) -> l <= lvl | _ -> false) xs
let (^=) = cst_lower

let rec position_of i stop v = (); fun x ->
  if i = stop then fail "cannot occur"
  else if equal x (IA.get i v) then mkDB (stop - i)
  else position_of (i+1) stop v x
let (^-) what where = IA.map (position_of 0 (IA.len where) where) what
let (^--) x v = position_of 0 (IA.len v) v x

let mk_al nbinders args =
  (* builds: map (lift nbinders) args @ [DB nbinders ... DB 1] *)
  let nargs = IA.len args in
  IA.init (nbinders + nargs)
    (fun i ->
      if i < nargs then Red.lift nbinders (IA.get i args)
      else mkDB (nargs + nbinders - i))

(* pattern unification fragment *)
let higher lvl x = match look x with (DB l | Con(_,l)) -> l > lvl | _ -> false
let rec not_in v len i x =
  if i+1 = len then true
  else not(equal x (IA.get (i+1) v)) && not_in v len (i+1) x
let isPU xs =
  match look (IA.get 0 xs) with
  | Uv (_,lvl) ->
      IA.for_alli (fun i x -> i = 0 || higher lvl x) xs &&
      IA.for_alli (fun i x -> i = 0 || not_in xs (IA.len xs) i x) xs
  | _ -> false

(* Based on Xiaochu Qi PHD (pages 51..52) / or reference 41 *)
let rec bind x id depth lvl args t s =
  let t, s = whd s t in
  TRACE "bind" (print_unif_prob s (":= "^string_of_int depth^"↓") x t)
  match look t with
  | Bin(m,t) -> let t, s = bind x id (depth+m) lvl args t s in mkBin m t, s
  | Ext _ -> t, s
  | Con (_,l) when l <= lvl -> t, s
  | Con _ -> t ^-- mk_al depth args, s (* XXX optimize *)
  (* the following 2 cases are: t ^-- mk_al depth args, s *) (* XXX CHECK *)
  | DB m when m <= depth -> t, s
  | DB m -> lift depth (mkDB (m-depth) ^-- args), s
  | Tup bs as t when rigid t ->
      let ss, s = IA.fold_map (bind x id depth lvl args) bs s in
      mkTup ss, s
  | (Tup _ | Uv _) as tmp -> (* pruning *)
      let bs = match tmp with
        | Tup bs -> bs | Uv _ -> IA.of_array [|t|] | _ -> assert false in
      match look (IA.get 0 bs) with
      | (Bin _ | Con _ | DB _ | Ext _ | Tup _) -> assert false
      | Uv(j,l) when j <> id && l > lvl && isPU bs ->
          let bs = IA.tl bs in
          let nbs = IA.len bs in
          let h, s = fresh_uv lvl s in
          let al = mk_al depth args in
          let cs = al ^= l in (* constants X = id,lvl can copy *)
          let ws = cs ^- al in
          let zs = inter al bs in (* XXX paper excludes #l-1, why? *)
          let vs = zs ^- al in
          let us = zs ^- bs in
          let nws, nvs, ncs, nus = IA.len ws, IA.len vs, IA.len cs, IA.len us in
          let vj = mkBin nbs (mkApp h (IA.append cs us) 0 (ncs + nus)) in
          let s = set_sub j vj s in
          let t = mkApp h (IA.append ws vs) 0 (nws+nvs) in
          SPY "vj" (prf_data []) vj; SPY "t" (prf_data[]) t;
          t, s
      | Uv(j,l) when j <> id && isPU bs ->
          let bs = IA.tl bs in
          let nbs = IA.len bs in
          let h, s = fresh_uv lvl s in
          let cs = bs ^= lvl in (* constants X = id,lvl can copy *)
          let ws = cs ^- bs in
          let al = mk_al depth args in
          let zs = inter al bs in (* XXX paper excludes #l-1, why? *)
          let vs = zs ^- bs in
          let us = zs ^- al in
          let nws, nvs, ncs, nus = IA.len ws, IA.len vs, IA.len cs, IA.len us in
          let vj = mkBin nbs (mkApp h (IA.append ws vs) 0 (nws + nvs)) in
          let s = set_sub j vj s in
          let t = mkApp h (IA.append cs us) 0 (ncs+nus) in
          SPY "vj" (prf_data []) vj; SPY "t" (prf_data[]) t;
          t, s
      | Uv _ -> fail "ho-ho"

let mksubst x id lvl t args s =
  let nargs = IA.len args in
(*
  match look t with
  | Bin(k,Uv(id1,_)) when id1 = id -> assert false (* TODO *)
  | Bin(k,Tup xs) when equal (IA.get 0 xs) (Uv (id,lvl)) && isPU xs ->
      assert false (* TODO *)
  | _ ->
*)
     let t, s = bind x id 0 lvl args t s in
     set_sub id (mkBin nargs t) s

let rec unify a b s = TRACE "unify" (print_unif_prob s "=" a b)
  let a, s =  whd s a in
  let b, s =  whd s b in
  match look a, look b with
  | Con _, Con _ | Ext _, Ext _ | DB _, DB _ ->
      if equal a b then s else fail "rigid"
  | Bin(nx,x), Bin(ny,y) when nx = ny -> unify x y s
  | Bin(nx,x), Bin(ny,y) when nx < ny -> unify (eta (ny-nx) x) y s
  | Bin(nx,x), Bin(ny,y) when nx > ny -> unify x (eta (nx-ny) y) s
  | ((Bin(nx,x), y) | (y, Bin(nx,x))) when rigid y -> unify x (eta nx (kool y)) s
  | Uv(i,_), Uv(j,_) when i = j -> s
  | x, y -> if rigid x && rigid y then unify_fo x y s else unify_ho x y s
and unify_fo x y s =
  match x, y with
  | Tup xs, Tup ys when IA.len xs = IA.len ys -> IA.fold2 unify xs ys s
  | _ -> fail "founif"
and unify_ho x y s =
  match x, y with
  | (((Uv (id,lvl) as x), y) | (y, (Uv (id,lvl) as x))) ->
      mksubst (kool x) id lvl (kool y) (IA.init 0 (fun _ -> kool y)) s
  | (((Tup xs as x), y) | (y, (Tup xs as x))) when isPU xs -> begin
      match look (IA.get 0 xs) with
      | Uv (id,lvl) -> mksubst (kool x) id lvl (kool y) (IA.tl xs) s
      | _ -> assert false
    end
  | _ -> fail "not a pattern unif"

(* ******************************** Main loop ******************************* *)

exception NoClause
type objective = [ `Atom of data | `Unify of data * data ]
type goal = int * int * objective * clause list

(* Important: when we move under a pi we put a constant in place of the
 * bound variable. This was hypothetical clauses do not need to be lifted
 * when we move under other pi binders *)
let mkhv =
  let i = ref 0 in
  let small_digit = function
    | 0 -> "₀" | 1 -> "₁" | 2 -> "₂" | 3 -> "₃" | 4 -> "₄" | 5 -> "₅"
    | 6 -> "₆" | 7 -> "₇" | 8 -> "₈" | 9 -> "₉" | _ -> assert false in
  let rec digits_of n = n mod 10 :: if n > 10 then digits_of (n / 10) else [] in
  fun depth ->
    incr i;
    mkCon ("𝓱"^
      String.concat "" (List.map small_digit (List.rev (digits_of !i)))) depth

let contextualize depth s t hv =
  Red.reloc_uv_subst
    ~uv_increment:(Subst.top s) ~cur_level:depth (List.rev hv) t

let contextualize_premise depth subst premise nuv =
  let rec aux cdepth depth s hv eh = function
  | Atom t ->
      [cdepth,nuv,`Atom(contextualize depth s t hv),
       List.map (fun t -> cdepth,nuv, t, Conj []) eh]
  | AtomBI (BIUnif(x,y)) -> [cdepth,nuv,`Unify(x,y),[]]
  | Impl(t,h) ->
      aux cdepth depth s hv (contextualize depth s t hv :: eh) h
  | Pi h -> aux (cdepth+1) depth s (mkhv (depth+1)::hv) eh h
  | Sigma h ->
      let m, s = Subst.fresh_uv cdepth s in
      aux cdepth depth s (m :: hv) eh h
  | Conj l -> List.flatten (List.map (aux cdepth depth s hv eh) l)
  in
    aux depth depth subst [] [] premise

let contextualize depth subst atom : data =
  contextualize depth subst atom []

let rec select (goal : head) depth s (prog : program) =
  match prog with
  | [] ->
      Printf.eprintf "fail: %s\n%!" (string_of_data (apply_subst s goal));
      raise NoClause
  | (_,nuv,hd,hyp) as clause :: prog ->
      try
        let hd = contextualize depth s hd in
        let chyp h = contextualize_premise depth s h nuv in
        let s = Subst.raise_top nuv s in
        let s = unify goal hd s in
        Format.eprintf "@[<hv2>  use:@ %a@]@\n%!" prf_clause clause;
        Format.eprintf "@[<hv2>  sub:@ %a@]@\n%!" Subst.prf_subst s;
        s, chyp hyp, prog
      with UnifFail _ -> select goal depth s prog

let rec run (prog : program) s ((depth,_,goal,extra_hyps) : goal) =
  let prog = extra_hyps @ prog in
  match goal with
  | `Atom goal ->
      let rec aux alternatives =
        Format.eprintf "@[<hv2>on:@ %a%s@]@\n%!"
          (prf_data []) (apply_subst s goal)
          (if !Trace.debug then Printf.sprintf " (%d,%d)" depth (Subst.top s)
          else "");
        let s, goals, alternatives = select goal depth s alternatives in
        try List.fold_left (run prog) s goals
        with NoClause -> aux alternatives in
      aux prog
  | `Unify(a,b) ->
        Format.eprintf "@[<hv2>on:@ %a = %a%s@]@\n%!"
          (prf_data []) (apply_subst s a) (prf_data []) (apply_subst s b)
          (if !Trace.debug then Printf.sprintf " (%d,%d)" depth (Subst.top s)
          else "");
      try
        let s = unify a b s in
        Format.eprintf "@[<hv2>  sub:@ %a@]@\n%!" Subst.prf_subst s;
        s
      with UnifFail _ -> raise NoClause

let run (p : program) (g : premise) =
  let s = empty 0 in
  let maxuv = fold_premise max_uv g 0 in
  let gs = contextualize_premise 0 s g maxuv in
  let s = Subst.raise_top (maxuv+1) s in
  List.fold_left (run p) s gs

(* vim:set foldmethod=marker: *)
