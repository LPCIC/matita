open Format
let debug = false
let dbg x = if debug then fprintf err_formatter x else ifprintf err_formatter x

(* Experiment with De Bruijn levels *)

(* Things understood (code not necessarily there):
   - caching the max level in a lambda term is possible.
   - closed term needs to be lifted, and UVar are in LP closed terms
     E.g. \x.x at top level is \1.1, at depth n-1 is \n.n
     hence whenever you deref, you need to know the current depth (context
     length)
   - original clauses are closed terms, hence at each application need
     to be lifted at the level d (length of the current ctx), but
     the head rarely contains a lambda, hence nothing to be done
   - hypothetical clauses are open terms, only their closed subterms (typically
     there are none) need to be lifted.
   In short, by caching the max rel in term one can avoid lifting the heads.
   - the body of clauses (original ones) do contain binders (thing at the
     lambda typing rule) so turning "hyps" into the new goals needs a new
     combination of
     - to_heap (as in desperate)
     - lift at depth d: this mean that the premise (pi 1\of (F 1)) is turned
       into (pi d\of (F d))
     - goals with a pi increment d, and pop the lambda: Rel d is bound
       in the new context, nothing to be done.
   The optimization that should save us:
   - if we continue with the goal (of (F d)) and we unify it with
     the head of the next clause to be tried, we whnd (F d)
   - (F d), after deref is (App [Lam k,t; Rel d]), if d=k no beta is needed
     and we just return t
   So the term assigned to F need not be lifted (i.e. the solutions of
   Uv are closed w.r.t. the context of Uv.  What I'm saying is that if
   we destructure (lam 1\ lam 2\f 1 2) using the of rule twice we must
   assign to the F1 (the F of the first rule, that is of level 1)
   (1\lam 2\f 1 2) and to the F2 (level 2) directly (2\f 1 2), that is an open
   term, but closed in the context of F2 (i.e. deref F2, in its orig context
   does nothing).

   I think that what should be the invariant is that the linguistic construct
   that model pattern matching of the input should not alter the input, just
   refresh the clauses.  (In elpi, they substitute fresh 'c' in place of
   the bound variables)

   Speculation on the representation of Uvar in HO case:
   - Matita 0.5 has (X (DbL 1) .. (DbL d) a1 .. an)
   - Matita 1.0 has the shortcut:  X (Irl(len,lift))  === X (DbL 1) .. (DbL d)
   - LP has     (X^d a1 .. an) and expands/lifts/whatever on the fly at
     unif(bind) time.
   
   There seems to be a intimate parallel between Matita 1.0 and L-\lambda:
   In Matita 1.0 the Uv has 2 options: an explicit list of terms, or an
   IRL(length,lift).  With DBL, the irl would be made of "constant" rels,
   so lift can go.  What is left is the length, that is the depth/level
   of a LP unif variable.

   The code below is like matita 0.5

   I'd try with the Matita 1.0 approach, without the lift (since irl are
   made of "constants" in DBL) and expand on the fly when you exit the
   fragment.  
*)

(* Input data in De Bruijn Level format, starting from 1 *)
type data =
  | DbL of int
  | Lam of data
  | App of data list
  | Const of string
  | Implicit (* Linear, duplication via beta *)

let pp_data ?(d=1) f t =
  let rec pp n f = function
    | DbL n -> fprintf f "%d" n
    | Lam t -> fprintf f "@[<hov 1>\\%d.@,%a@]" n (pp (n+1)) t
    | Const s -> fprintf f "%s" s
    | App l -> fprintf f "@[<hv 1>(%a)@]" (ppl n) l
    | Implicit -> fprintf f "?"
  and ppl n f = function
    | [] -> ()
    | [t] -> fprintf f "%a" (pp n) t
    | t :: ts -> fprintf f "%a@ " (pp n) t; ppl n f ts
  in
    pp d f t
;;

type test = [ `Whnf | `Nf | `Unif of bool ]

type suite = (data * test * data) list

let suite : suite = (* {{{ *) [
  (* A test for whd *)
  App[ Lam (App[ DbL 1; Lam (App [Const "f"; DbL 1; DbL 2])]); Lam(DbL 1) ],
  `Whnf,
  Lam (App [ Const "f"; Lam(DbL 2); DbL 1])
;
  (* A test for nf *)
  App[ Lam (App[ DbL 1; Lam (App [DbL 1; DbL 2])]); Lam(DbL 1) ],
  `Nf,
  Lam (DbL 1)
;
  (* The usual 2*2 = 4 test to discover buggy lift/subst *)
  (let two = Lam(Lam(App[DbL 3;App[DbL 3; DbL 4]])) in
   Lam(Lam(App[ two; two; DbL 1; App[DbL 2;DbL 2] ]))),
  `Nf,
  Lam(Lam(App[DbL 1;App[DbL 1;App[DbL 1;App[DbL 1;App[DbL 2;DbL 2]]]]]))
;
  (* test that "stuff" is not delifted nor lifted being "constant" in 
     the context of the redex *)
  (let stuff = App[DbL 1; DbL 1] in
   Lam(App[Lam(Lam(App[DbL 2;stuff])); stuff]),
   `Nf,
   Lam(Lam(App[DbL 1; DbL 1; stuff])))
;
   Lam(App[Lam(Lam(Lam(App[DbL 2; DbL 4; DbL 3]))); Implicit]),
   `Unif true,
   Lam(Lam(Lam(App[DbL 2;DbL 3; DbL 1; Const "w"])))
] (* }}} *)

module type L = sig

  type term
  val read : data -> term
  val write : term -> data

  val whnf : int -> term -> term
  val nf : int -> term -> term
  val unif : term -> term -> bool

  val pp : formatter -> term -> unit

  val id : string

end

let out = err_formatter

let rec run ?(cur=0) (m : (module L) list) (t : suite) =
  match t with
  | [] -> ()
  | (input,op,output) :: rest ->
    List.iter (fun (module M : L) ->
      let open M in
      match op with
      | `Nf ->
        let i = read input in
        let o = M.nf 0 i in
        fprintf out "%d:%5s: @[<hv 0>%a@ --nf-->@ %a@]\n%!" cur id pp i pp o;
        assert(output = write o)
      | `Whnf ->
        let i = read input in
        let o = whnf 0 i in
        fprintf out "%d:%5s: @[<hv 0>%a@@ --wh-->@ %a@]\n%!" cur id pp i pp o;
        assert(output = write o)
      | `Unif eb ->
        let i = read input in
        let o = read output in
        fprintf out "%d:%5s: @[<hv 0>%a@ --?--@ %a@]\n%!" cur id pp i pp o;
        let res, b = if M.unif i o then "=", true else "/", false in
        fprintf out "%d:%5s: @[<hv 0>%a@ --%s--@ %a@]\n%!" cur id pp i res pp o;
        fprintf out "%d:%5s: @[<hv 0>%a@ <--nf--%s--nf-->@ %a@]\n%!"
          cur id pp (nf 0 i) res pp (nf 0 o);
        assert(b = eb);
        assert(not eb || (nf 0 i) = (nf 0 o));
      )
    m;
    fprintf out "\n%!";
    run ~cur:(cur+1) m rest
;;

(* helpers *)
let digit_sup = function
  | 0 -> "⁰" | 1 -> "¹" | 2 -> "²" | 3 -> "³" | 4 -> "⁴" | 5 -> "⁵"
  | 6 -> "⁶" | 7 -> "⁷" | 8 -> "⁸" | 9 -> "⁹" | _ -> assert false
let digit_sub = function
  | 0 -> "₀" | 1 -> "₁" | 2 -> "₂" | 3 -> "₃" | 4 -> "₄" | 5 -> "₅"
  | 6 -> "₆" | 7 -> "₇" | 8 -> "₈" | 9 -> "₉" | _ -> assert false
let rec digits_of n = n mod 10 :: if n >= 10 then digits_of (n / 10) else []
let subscript n =
  String.concat "" (List.map digit_sub (List.rev (digits_of n)))
let superscript n =
  String.concat "" (List.map digit_sup (List.rev (digits_of n)))
let rec seq n = function
  | 0 -> ""
  | 1 -> string_of_int n
  | w -> string_of_int n ^ " " ^ seq (n+1) (w-1)

let rec for_all2 f l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | x::xs, y::ys -> f x y && for_all2 f xs ys
  | _ -> false

(* ***************************** EXPERIMENTS ******************************* *)

(* With HO things are harder, so here I have a base implementation of
   De Bruijn levels one can copy and improve.  *)

module DBL : L = struct (* {{{ *)

(* Name conventions:
    d is for depth, the current context length
    w is for width, for multi lambda: \1 2 3 4.t is Lam(w,t) with w=4
*)

let id = "DBL"

type lvl = int (* max level of the term, a metadata to speed up lift/subst *)
type name = int (* the depth at which the lambda occurs *)
type width = int (* multi lambda *)
type term =
  | XDb of int
  | XLam of width * term * name
  | XApp of term list * lvl
  | XConst of string
  | XUv of term list * term ref * lvl (* local subst & val (Matita 0.5) *)
let dummy = XConst "☠"

let rec lvl_of = function
  | XDb i -> i
  | XConst _ -> 0
  | XApp(_,lvl) -> lvl
  | XUv(_,_,lvl) -> lvl
  | XLam(w,t,name) -> max (w+name-1) (lvl_of t)
let max_lvl tl = List.fold_left (fun m t -> max m (lvl_of t)) 0 tl

(* smart constructors: pack Lam(Lam...) and App[App[..]] *)
let mkXLam w t d = if w = 0 then t else
  match t with XLam(n,t,_) -> XLam(n+w,t,d) | _ -> XLam(w,t,d)
let rec mkXApp = function
  | [] -> assert false
  | [x] -> x
  | XApp (l,_) :: args -> mkXApp (l @ args)  (* could be smarter for the lvl *)
  | l -> XApp(l, max_lvl l)

(* mkdbl n n = Db 1 ... Db n *)
let rec mkdbl d = function 0 -> [] | n -> XDb(d-n+1) :: mkdbl d (n-1)

let rec read d = function
  | DbL i -> XDb i
  | Lam t -> mkXLam 1 (read (d+1) t) (d+1)
  | App l -> let l = List.map (read d) l in mkXApp l
  | Const s -> XConst s
  | Implicit -> XUv(mkdbl d d, ref dummy,d)
let read x = read 0 x

(* When you put t under n additional Lam *)
(* CAVEAT: this is here because "write" needs it *)
let lift t n i = if n = 0 then t else
  let rec aux = function
(*     | (XApp (_,lvl) | XUv(_,_, lvl)) as orig when lvl < i -> orig *)
    | XApp (ts, lvl) -> XApp (List.map aux ts, lvl+n)
    | XDb j when j >= i -> XDb (j + n)
    | XDb _ as t -> t
    | XLam (w, t, name) -> mkXLam w (aux t) (name+n)
    | XConst _ as x -> x
    | XUv(lc, r, lvl) -> XUv(List.map aux lc, r, lvl+n)
  in
    aux t

let rec mknLam t = function 0 -> t | n -> Lam(mknLam t (n-1))

let rec write d = function
  | XDb i -> DbL i
  | XLam (w,t,_) -> mknLam (write (d+w) t) w
  | XApp (l,_) -> App (List.map (write d) l)
  | XConst s -> Const s
  | XUv (_,{ contents = t },_) when t == dummy -> Implicit
  | XUv (lc, { contents = t }, lvl) ->
      (* Inconvenience of DBL: closed terms (like the ones assigned
       * to UVars) needs to be lifted, and then they immediately generate
       * a bunch of beta redexes.  Possible optimization: coalesce lift+beta
       * and code a uv_instance function *)
      write d (XApp(lift t d 0 :: lc, lvl))
let write t = write 0 t

let pp ?(d=1) f t =
  let rec pp d f = function
    | XDb n -> fprintf f "%d" n
    | XLam (w,t,name) ->
        assert(name=d);  (* this is both an assertion you call pp with a
                            correct d *and* that the XLam nodes have the
                            right name *)
        fprintf f "@[<hov 1>\\%s.@,%a@]" (seq d w) (pp (d+w)) t
    | XConst s -> fprintf f "%s" s
    | XUv(lc, { contents = t }, lvl) when t == dummy ->
        fprintf f "?%s[%a]" (subscript lvl) (ppl d) lc
    | XUv(lc, { contents = t }, _) -> pp d f (mkXApp (lift t (d-1) 0 :: lc))
    | XApp (XUv(lc, { contents = t }, _)::l, lvl)  when t != dummy ->
        pp d f (mkXApp (lift t (d-1) 0 :: lc @ l))
    | XApp (l, lvl) -> fprintf f "@[<hov 1>%s(%a)@]" (subscript lvl) (ppl d) l
  and ppl d f = function
    | [] -> ()
    | [t] -> fprintf f "%a" (pp d) t
    | t :: ts -> fprintf f "%a@ " (pp d) t; ppl d f ts
  in
    pp d f t
let pp_d d f t = pp ~d f t
let pp f t = pp f t

let nth l i =
  try List.nth l i
  with _ -> fprintf out "nth %d on %a\n%!" i pp (mkXApp l); assert false

(* substitutes Db i ... Db(i+largs-1) with the corresponding args.
 * largs is the length of args, i is (also) the redex depth *)
let sub t i largs args =
  let rec aux d = function
(*     | (XApp (_,lvl) | XUv(_,_,lvl)) as orig when lvl < i -> orig *)
    | XDb j when j >= i && j < i+largs -> lift (nth args (j-i)) d i
    | XDb j when j >= i+largs -> XDb (j - largs)
    | XDb _ as x -> x
    | XApp (ts,_) -> mkXApp (List.map (aux d) ts)
    | XLam (w,t,name) -> mkXLam w (aux (d+w) t) (name-largs)
    | XConst _ as x -> x
    | XUv(lc, r, lvl) -> let lc = List.map (aux d) lc in XUv(lc, r, max_lvl lc)
  in
    aux 0 t

(* To align a multi lambda and a multi appl *)
let rec eat_args w acc args = if w = 0 then  0, List.rev acc, args else
  match args with
  | [] -> w, List.rev acc, []
  | x::xs -> eat_args (w-1) (x::acc) xs

let beta body d nlams args =
  let lam_left, args, args_left = eat_args nlams [] args in
  let reduct = sub body d (nlams - lam_left) args in
  dbg "beta: @[<hov 1>%a@ -> sub %a %d %d %a@ -> %a@]\n%!"
     (pp_d d) (mkXApp (mkXLam nlams body d :: args)) (pp_d (d+nlams)) body
     d (nlams - lam_left) (pp_d d) (XApp (args,max_lvl args)) (pp_d d) reduct;
  mkXLam lam_left (mkXApp (reduct :: args_left)) d

let rec whnf d = function
  | XUv(lc, { contents = t },_) when t != dummy ->
      whnf d (mkXApp(lift t d 0 ::lc))
  | XApp (XUv(lc, { contents = t }, _) :: args, _) when t != dummy ->
      whnf d (mkXApp(lift t d 0 :: lc @ args))
  | XApp (XLam (w,hd,_) :: args, _) as orig ->
      dbg "whnf:redex: %a\n%!" (pp_d (d+1)) orig;
      whnf d (beta hd (d+1) w args)
  | x -> x

let nf d t =
  let rec nf ?(stop=false) d = function 
  | XUv(lc, { contents = t },_) when t != dummy ->
      nf d (mkXApp(lift t d 0 :: lc))
  | XApp (XUv(lc, { contents = t },_) :: args, _) when t != dummy ->
      nf d (mkXApp(lift t d 0 :: lc @ args))
  | XApp (XLam (w,hd,_) :: args, _) as orig ->
      dbg "nf:redex: %a\n%!" (pp_d (d+1)) orig;
      nf d (beta hd (d+1) w args)
  | XApp _ as x when stop -> x
  | XApp (xs, _) -> nf ~stop:true d (mkXApp (List.map (nf d) xs))
  | XLam (w,t,n) -> mkXLam w (nf (d+w) t) n
  | XDb _ | XConst _ | XUv _ as x -> x
  in
    nf d t

exception UnifFail

(* does t occur in l *)
let pos_of t l =
  let rec aux n = function
  | [] -> raise UnifFail
  | x::xs -> if x = t then XDb n else aux (n+1) xs in
  aux 1 l

(* binds args in t *)
let bind r t depth args =
  dbg "bind: %a args: %a\n%!" (pp_d depth) t (pp_d depth) (mkXApp args);
  let largs = List.length args in
  let rec aux d t =
    match whnf (d+depth) t with
    | XConst _ as c -> c
    | XDb i when i > d -> XDb(largs + i - d)
    | XDb i as x -> pos_of x args
    | XApp (l,_) -> mkXApp(List.map (aux d) l)
    | XLam (w,t,name) -> mkXLam w (aux (d+w) t) name
    | XUv (_,lr,_) when r == lr -> raise UnifFail (* occur check *)
    | XUv (lc,lr,_) -> assert false (* TODO: pruning *)
  in
  let rc = aux depth t in
  dbg "bound: %a\n%!" (pp_d (depth+List.length args)) rc;
  rc

(* pattern fragment *)
let rec isPU = function
  | [] -> true
  | XDb i :: rest ->
      List.for_all (function XDb j -> j <> i | _ -> false) rest && isPU rest
  | _ -> false

(* No trail for now *)
let unif a b =
  let rec unif d a b =
    dbg "unif: %a = %a\n%!" (pp_d (d+1)) a (pp_d (d+1)) b;
    match whnf d a, whnf d b with
    | XLam (v,x,n1), XLam (w,y,n2) -> assert(n1=n2);
        if v < w then unif (d+v) x (XLam(w-v,y,n2+v)) else
        if v > w then unif (d+w) (XLam(v-w,x,n1+w)) y else
        unif (d+w) x y
        (* TODO: eta *)
    | XConst a, XConst b -> a = b
    | XDb a, XDb b -> a = b
    | XApp(XUv (lc,r,_) :: args,_), t 
    | t, XApp(XUv (lc,r,_) :: args,_) -> (* as in Matita *)
       let w = List.length lc + List.length args in
       r := mkXLam w (XUv(mkdbl w w, ref dummy,w)) 1;
       unif d a b
    | XUv(lc,r,_), t | t, XUv(lc,r,_) when isPU lc ->
       r := mkXLam (List.length lc) (bind r t d lc) 1; true
    | XApp (xs,_), XApp (ys,_) -> for_all2 (unif d) xs ys
    | _ -> false
  in
    unif 0 a b

end (* }}} *)

let _ = run [ (module DBL : L) ] suite;;

(* vim:set foldmethod=marker: *)
