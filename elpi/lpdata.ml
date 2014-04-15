(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module IA = struct include BIA (* {{{ Immutable arrays *)

  let append v1 v2 =
    let len1 = BIA.len v1 in
    BIA.init (len1 + BIA.len v2)
      (fun i -> if i < len1 then BIA.get i v1 else BIA.get (i-len1) v2)

  let cons t v =
    BIA.init (BIA.len v+1) (fun i -> if i = 0 then t else BIA.get (i-1) v)

end (* }}} *)

module C : sig (* {{{ External, user defined, datatypes *)

  type t
  type ty
  type data = {
    t : t;
    ty : ty;
  }

  val declare : ('a -> string) -> ('a -> 'a -> bool) -> 'a -> data
  
  val print : data -> string
  val equal : data -> data -> bool

(* }}} *)
end = struct (* {{{ *)

type t = Obj.t
type ty = int

type data = {
  t : Obj.t;
  ty : int
}

module M = Int.Map
let m : ((data -> string) * (data -> data -> bool)) M.t ref = ref M.empty

let cget x = Obj.obj x.t
let print x = fst (M.find x.ty !m) x
let equal x y = x.ty = y.ty && snd (M.find x.ty !m) x y

let fresh_tid =
  let tid = ref 0 in
  fun () -> incr tid; !tid

let declare print cmp =
  let tid = fresh_tid () in
  m := M.add tid ((fun x -> print (cget x)),
                  (fun x y -> cmp (cget x) (cget y))) !m;
  fun v -> { t = Obj.repr v; ty = tid }

end (* }}} *)

module PPLIB = struct (* {{{ auxiliary lib for PP *)

let on_buffer f x =
  let b = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer b in
  f fmt x;
  Format.pp_print_flush fmt ();
  Buffer.contents b
let rec iter_sep spc pp = function
  | [] -> ()
  | [x] -> pp x
  | x::tl -> pp x; spc (); iter_sep spc pp tl

end (* }}} *)
open PPLIB

module LP = struct

type var = int
type level = int
type name = string

type olam = int
type nlam = int
type uvreloc = int * level
let nolvl = -1
let noreloc = 0,nolvl

type kind_of_data =
  | Uv of var * level
  | Con of name * level
  | DB of int
  | Bin of int * data
  | Tup of data IA.t
  | Ext of C.data
and data =
  | XUv of var * level
  | XCon of name * level
  | XDB of int
  | XBin of int * data
  | XTup of data IA.t
  | XExt of C.data
  | XSusp of suspended_job ref
and suspended_job = Done of data | Todo of uvreloc * data * olam * nlam * env
and env =
  | XNil
  | XArgs of data IA.t * int * env
  | XMerge of env * nlam * olam * env
  | XSkip of int * nlam * env

module PP = struct (* {{{ pretty printer for data *)

let small_digit = function
  | 0 -> "⁰" | 1 -> "¹" | 2 -> "²" | 3 -> "³" | 4 -> "⁴" | 5 -> "⁵"
  | 6 -> "⁶" | 7 -> "⁷" | 8 -> "⁸" | 9 -> "⁹" | _ -> assert false

let rec digits_of n = n mod 10 :: if n > 10 then digits_of (n / 10) else []

let string_of_level lvl = if !Trace.debug then "^" ^ string_of_int lvl
  else if lvl = 0 then ""
  else String.concat "" (List.map small_digit (List.rev (digits_of lvl)))

let pr_cst x lvl = x ^ if !Trace.debug then string_of_level lvl else ""
let pr_var x lvl =
  "X" ^ string_of_int x ^ if !Trace.debug then string_of_level lvl else ""

let rec fresh_names k = function
  | 0 -> []
  | n -> ("w" ^ string_of_int k) :: fresh_names (k+1) (n-1)

module P = Format

let rec prf_data ctx fmt t =
  let rec print ?(pars=false) ctx = function
    | XBin (n,x) ->
       P.pp_open_hovbox fmt 2;
       let names = fresh_names (List.length ctx) n in
       if pars then P.pp_print_string fmt "(";
       P.pp_print_string fmt (String.concat "\\ " names ^ "\\");
       P.pp_print_space fmt ();
       print (List.rev names @ ctx) x;
       if pars then P.pp_print_string fmt ")";
       P.pp_close_box fmt ()
    | XDB x -> P.pp_print_string fmt 
        (try (if !Trace.debug then "'" else "") ^List.nth ctx (x-1)
        with Failure _ | Invalid_argument _ ->
          "_" ^ string_of_int (x-List.length ctx))
    | XCon (x,lvl) -> P.pp_print_string fmt (pr_cst x lvl)
    | XUv (x,lvl) -> P.pp_print_string fmt (pr_var x lvl)
    | XTup xs ->
        P.pp_open_hovbox fmt 2;
        if pars then P.pp_print_string fmt "(";
        iter_sep (P.pp_print_space fmt) (print ~pars:true ctx) (IA.to_list xs);
        if pars then P.pp_print_string fmt ")";
        P.pp_close_box fmt ()
    | XExt x ->
        P.pp_open_hbox fmt ();
        P.pp_print_string fmt (C.print x);
        P.pp_close_box fmt ()
    | XSusp ptr ->
        match !ptr with
        | Done t -> P.fprintf fmt ".(@["; print ctx t; P.fprintf fmt ")@]"
        | Todo(u,t,ol,nl,e) ->
            P.fprintf fmt "@[<hov 2>⟦%d,%d, " (fst u) (snd u);
            print ctx t;
            P.fprintf fmt ",@ %d, %d,@ " ol nl;
            prf_env ctx fmt e;
            P.fprintf fmt "⟧@]";
  in
    print ctx t

and prf_env ctx fmt e =
  let rec print_env = function
    | XNil -> P.pp_print_string fmt "nil"
    | XArgs(a,n,e) ->
        P.fprintf fmt "(@[<hov 2>";
        iter_sep (fun () -> P.fprintf fmt ",@ ")
          (prf_data ctx fmt) (IA.to_list a);
        P.fprintf fmt "@]|%d)@ :: " n;
        print_env e
    | XMerge(e1,nl1,ol2,e2) ->
        P.fprintf fmt "@[<hov 2>⦃";
        print_env e1;
        P.fprintf fmt ",@ %d, %d,@ " nl1 ol2;
        print_env e2;
        P.fprintf fmt "⦄@]";
    | XSkip(n,m,e) ->
        P.fprintf fmt "@@(%d,%d)@ :: " n m;
        print_env e;
  in
    P.pp_open_hovbox fmt 2;
    print_env e;
    P.pp_close_box fmt ()

let string_of_data ?(ctx=[]) t = on_buffer (prf_data ctx) t
let string_of_env ?(ctx=[]) e = on_buffer (prf_env ctx) e

end (* }}} *)
include PP

let (--) x y = max 0 (x - y)
let mkXSusp ?(uv_reloc=noreloc) t n o e = XSusp(ref(Todo(uv_reloc,t,n,o,e)))

let rec epush e = TRACE "epush" (fun fmt -> prf_env [] fmt e)
  match e with
  | (XNil | XArgs _ | XSkip _) as x -> x
  | XMerge(e1,nl1,ol2,e2) -> let e1 = epush e1 in let e2 = epush e2 in
  match e1, e2 with
  | e1, XNil when ol2 = 0 -> (*m2*) e1
  | XNil, e2 when nl1 = 0 -> (*m3*) e2
  | XNil, XArgs(a,l,e2) -> (*m4*)
      let nargs = IA.len a in
      if nl1 = nargs then e2 (* repeat m4, end m3 *)
      else if nl1 > nargs then epush (XMerge(XNil,nl1 - nargs, ol2 - nargs, e2))
      else XArgs(IA.sub nl1 (nargs-nl1) a,l,e2) (* repeast m4 + m3 *)
  | XNil, XSkip(a,l,e2) -> (*m4*)
      if nl1 = a then e2 (* repeat m4, end m3 *)
      else if nl1 > a then epush (XMerge(XNil,nl1 - a, ol2 - a, e2))
      else XSkip(a-nl1,l-nl1,e2) (* repeast m4 + m3 *)
  | (XArgs(_,n,_) | XSkip(_,n,_)) as e1, XArgs(b,l,e2) when nl1 > n -> (*m5*)
      let drop = min (IA.len b) (nl1 - n) in
      if drop = IA.len b then
        epush (XMerge(e1,nl1 - drop, ol2 - drop, e2))
      else   
        epush (XMerge(e1,nl1 - drop, ol2 - drop,
          XArgs(IA.sub drop (IA.len b - drop) b,l,e2)))
  | (XArgs(_,n,_) | XSkip(_,n,_)) as e1, XSkip(b,l,e2) when nl1 > n -> (*m5*)
      let drop = min b (nl1 - n) in
      if drop = b then epush (XMerge(e1,nl1 - drop, ol2 - drop, e2))
      else epush (XMerge(e1,nl1 - drop, ol2 - drop, XSkip(b - drop,l-drop,e2)))
  | XArgs(a,n,e1), ((XArgs(_,l,_) | XSkip(_,l,_)) as e2) -> (*m6*)
      assert(nl1 = n);
      let m = l + (n -- ol2) in
      let t = IA.get 0 a in
      let e1 = if IA.len a > 1 then XArgs(IA.tl a,n,e1) else e1 in
      (* ugly *)
      XArgs(IA.of_array [|mkXSusp t ol2 l e2|], m, XMerge(e1,n,ol2,e2))
  | XSkip(a,n,e1), ((XArgs(_,l,_) | XSkip(_,l,_)) as e2) -> (*m6*)
      assert(nl1 = n);
      let m = l + (n -- ol2) in
      let e1 = if a > 1 then XSkip(a-1,n-1,e1) else e1 in
      (* ugly *)
      XArgs(IA.of_array [|mkXSusp (XDB 1) 0 l e2|], m, XMerge(e1,n,ol2,e2))
  | XArgs _, XNil -> assert false
  | XNil, XNil -> assert false
  | XSkip _, XNil -> assert false
  | ((XMerge _, _) | (_, XMerge _)) -> assert false

let store ptr v = ptr := Done v; v
let push t =
  match t with
  | (XUv _ | XCon _ | XDB _ | XBin _ | XTup _ | XExt _) as x -> x
  | XSusp { contents = Done t } -> t
  | XSusp ({ contents = Todo (uvrl,t,ol,nl,e) } as ptr) ->
      let rec push u t ol nl e = TRACE "push" (fun fmt -> prf_data [] fmt t)
        match t with
        | XSusp { contents = Done t } -> push u t ol nl e
        | XSusp { contents = Todo (u1,t,ol1,nl1,e1) } -> (*m1*)
            push (fst u + fst u1,snd u) t (ol1 + (ol -- nl1)) (nl + (nl1 -- ol))
              (XMerge(e1,nl1,ol,e))
        | (XCon _ | XExt _) as x -> (*r1*) x
        | XUv (i,l) when snd u = nolvl -> XUv (i+fst u,l)
        | XUv (i,_) -> XUv (i+fst u,snd u)
        | XBin(n,t) -> (*r6*)
            assert(n > 0);
            store ptr
              (XBin(n,mkXSusp ~uv_reloc:u t (ol+n) (nl+n) (XSkip(n,nl+n,e))))
        | XTup a -> (*r5*)
            store ptr (XTup(IA.map (fun t -> mkXSusp ~uv_reloc:u t ol nl e) a))
        | XDB i -> (* r2, r3, r4 *)
            let e = epush e in
            SPY "epushed" (prf_env []) e;
            match e with
            | XMerge _ -> assert false
            | XNil -> assert(ol = 0); store ptr (XDB(i+nl))
            | XArgs(a,l,e) ->
                let nargs = IA.len a in
                if i <= nargs
                then push noreloc (IA.get (nargs - i) a) 0 (nl - l) XNil
                else push u (XDB(i - nargs)) (ol - nargs) nl e
            | XSkip(n,l,e) -> 
                if (i <= n) then store ptr (XDB (i + nl - l))
                else push u (XDB(i - n)) (ol - n) nl e
      in
        push uvrl t ol nl e

let isSubsp = function XSusp _ -> true | _ -> false

let look x =
  let x = push x in
  SPY "pushed" (prf_data []) x;
  match x with
  | XUv (v,l) -> Uv(v,l)
  | XCon (n,l) -> Con(n,l)
  | XDB i -> DB i
  | XBin (n,t) -> Bin(n,t)
  | XTup a -> Tup a
  | XExt e -> Ext e
  | XSusp _ -> assert false
let mkUv v l = XUv(v,l)
let mkCon n l = XCon(n,l)
let mkDB i = XDB i
let mkTup xs = if IA.len xs = 1 then IA.get 0 xs else XTup xs
let mkExt x = XExt x
let kool = function
  | Uv (v,l) -> XUv(v,l)
  | Con (n,l) -> XCon(n,l)
  | DB i -> XDB i
  | Bin (n,t) -> XBin(n,t)
  | Tup a -> XTup a
  | Ext e -> XExt e

let mkBin n t =
  if n = 0 then t
  else match t with
    | XBin(n',t) -> XBin(n+n',t)
    | _ -> XBin(n,t)

let mkApp t v start stop =
  if start = stop then t else
  match t with
  | XTup xs -> XTup(IA.append xs (IA.sub start (stop-start) v))
  | _ -> XTup(IA.cons t (IA.sub start (stop-start) v))

let fixTup xs =
  match push (IA.get 0 xs) with
  | XTup ys -> XTup (IA.append ys (IA.tl xs))
  | _ -> XTup xs

let rec equal a b = match push a, push b with
 | XUv (x,_), XUv (y,_) -> x = y
 | XCon (x,_), XCon (y,_) -> x = y
 | XDB x, XDB y -> x = y
 | XBin (n1,x), XBin (n2,y) -> n1 = n2 && equal x y
 | XTup xs, XTup ys -> IA.for_all2 equal xs ys
 | XExt x, XExt y -> C.equal x y
 | ((XBin(n,x), y) | (y, XBin(n,x))) -> begin
     match push x with
     | XTup xs ->
        let nxs = IA.len xs in
        let eargs = nxs - n in
           eargs > 0
        && IA.for_alli (fun i t -> i < eargs || equal t (XDB (nxs-i))) xs
        && let hd = mkTup (IA.sub 0 eargs xs) in
           equal hd (mkXSusp y 0 n XNil)
     | _ -> false
   end
 | _ -> false

let isBin x = match push x with XBin _ -> true | _ -> false

let rec fold f x a = match push x with
  | (XDB _ | XCon _ | XUv _ | XExt _) as x -> f x a
  | XBin (_,x) -> fold f x a
  | XTup xs -> IA.fold (fold f) xs a
  | XSusp _ -> assert false

let rec map f x = match push x with
  | (XDB _ | XCon _ | XUv _ | XExt _) as x -> f x
  | XBin (ns,x) -> XBin(ns, map f x)
  | XTup xs -> XTup(IA.map (map f) xs)
  | XSusp _ -> assert false

let max_uv x a = match push x with XUv (i,_) -> max a i | _ -> a

let rec fold_map f x a = match push x with
  | (XDB _ | XCon _ | XUv _ | XExt _) as x -> f x a
  | XBin (n,x) -> let x, a = fold_map f x a in XBin(n,x), a
  | XTup xs -> let xs, a = IA.fold_map (fold_map f) xs a in XTup xs, a
  | XSusp _ -> assert false
 
(* PROGRAM *)
type builtin = BIUnif of data * data

let map_builtin f = function BIUnif(a,b) -> BIUnif(f a, f b)
let fold_builtin f x a = match x with BIUnif(x,y) -> f y (f x a)
let fold_map_builtin f x a = match x with
  | BIUnif(x,y) ->
      let x, a = f x a in
      let y, a = f y a in
      BIUnif(x,y), a

type program = clause list
and clause = int * int * head * premise (* level, maxuv, head, premises *)
and head = data
and premise =
  | Atom of data
  | AtomBI of builtin
  | Conj of premise list
  | Impl of data * premise
  | Pi of premise
  | Sigma of premise
and goal = premise

let rec map_premise f = function
  | Atom x -> Atom(f x)
  | AtomBI bi -> AtomBI (map_builtin f bi)
  | Conj xs -> Conj(List.map (map_premise f) xs)
  | Impl(x,y) -> Impl(f x, map_premise f y)
  | Pi x  -> Pi(map_premise f x)
  | Sigma x  -> Sigma(map_premise f x)

let rec fold_premise f x a = match x with
  | Atom x -> f x a
  | AtomBI bi -> fold_builtin f bi a
  | Conj xs -> List.fold_left (fun a x -> fold_premise f x a) a xs
  | Impl(x,y) -> fold_premise f y (f x a)
  | Pi x -> fold_premise f x a
  | Sigma x -> fold_premise f x a

let rec fold_map_premise f p a = match p with
  | Atom x -> let x, a = f x a in Atom x, a
  | AtomBI bi -> let bi, a = fold_map_builtin f bi a in AtomBI bi, a
  | Conj xs ->
      let xs, a =
        List.fold_left (fun (l,a) x ->
          let x, a = fold_map_premise f x a in
          x::l, a)
        ([],a) xs in
      Conj(List.rev xs), a
  | Impl(x,y) -> let x, a = f x a in
                 let y, a = fold_map_premise f y a in
                 Impl(x,y), a
  | Pi y -> let y, a = fold_map_premise f y a in Pi y, a
  | Sigma y -> let y, a = fold_map_premise f y a in Sigma y, a

module PPP = struct (* {{{ pretty printer for programs *)

let prf_builtin ctx fmt = function
  | BIUnif (a,b) -> 
      Format.pp_open_hvbox fmt 2;
      prf_data ctx fmt a;
      Format.pp_print_space fmt ();
      Format.pp_print_string fmt "= ";
      prf_data ctx fmt b;
      Format.pp_close_box fmt ()

let rec prf_premise ?(pars=false) ctx fmt = function
  | Atom p -> prf_data ctx fmt p
  | AtomBI bi -> prf_builtin ctx fmt bi
  | Conj l ->
       Format.pp_open_hvbox fmt 2;
       if pars then Format.pp_print_string fmt "(";
       iter_sep (fun () ->
         Format.pp_print_string fmt ","; Format.pp_print_space fmt ())
         (prf_premise ctx fmt) l;
       if pars then Format.pp_print_string fmt ")";
       Format.pp_close_box fmt ()
  | Pi p ->
       let x = "x" ^ string_of_int (List.length ctx) in
       Format.pp_open_hvbox fmt 2;
       Format.pp_print_string fmt ("pi "^x^"\\");
       Format.pp_print_space fmt ();
       prf_premise (x::ctx) fmt p;
       Format.pp_close_box fmt ()
  | Sigma p ->
       let x = "Y" ^ string_of_int (List.length ctx) in
       Format.pp_open_hvbox fmt 2;
       Format.pp_print_string fmt ("sigma "^x^"\\");
       Format.pp_print_space fmt ();
       prf_premise (x::ctx) fmt p;
       Format.pp_close_box fmt ()
  | Impl (x,p) ->
       Format.pp_open_hvbox fmt 2;
       prf_data ctx fmt x;
       Format.pp_print_space fmt ();
       Format.pp_open_hovbox fmt 0;
       Format.pp_print_string fmt "==> ";
       prf_premise ~pars:true ctx fmt p;
       Format.pp_close_box fmt ();
       Format.pp_close_box fmt ()

let prf_premise ctx fmt = prf_premise ctx fmt
let string_of_premise p = on_buffer (prf_premise []) p
let string_of_goal = string_of_premise
let prf_goal = prf_premise []

let string_of_head = string_of_data

let prf_clause fmt (_, _, hd, hyps) =
  Format.pp_open_hvbox fmt 2;
  prf_data [] fmt hd;
  if hyps <> Conj [] then begin
    Format.pp_print_space fmt ();
    Format.pp_print_string fmt ":- ";
  end;
  prf_premise [] fmt hyps;
  Format.pp_print_string fmt ".";
  Format.pp_close_box fmt ()

let string_of_clause c = on_buffer prf_clause c

let prf_program fmt p =
  Format.pp_open_vbox fmt 0;
  iter_sep (Format.pp_print_space fmt) (prf_clause fmt) p;
  Format.pp_close_box fmt ()
let string_of_program p = on_buffer prf_program p

end (* }}} *)
include PPP

module Parser : sig (* {{{ parser for LP programs *)

  val parse_program : string -> program
  val parse_goal : string -> goal
  val parse_data : string -> data

(* }}} *)
end = struct (* {{{ *)

let rec number = lexer [ '0'-'9' number | ]
let rec ident =
  lexer [ [ 'a'-'z' | '\'' | '_' | '0'-'9' ] ident | '^' '0'-'9' number | ]

let lvl_name_of s =
  match Str.split (Str.regexp_string "^") s with
  | [ x ] -> x, 0
  | [ x;l ] -> x, int_of_string l
  | _ -> raise (Token.Error ("<name> ^ <number> expected.  Got: " ^ s))

let arr = lexer [ "=>" ]

let tok = lexer
  [ [ 'A'-'Z' ] ident -> "UVAR", $buf 
  | [ 'a'-'z' ] ident -> "CONSTANT", $buf
  | [ '_' '0'-'9' ] number -> "REL", $buf
  | [ ":-" ] -> "ENTAILS",$buf
  | [ ',' ] -> "COMMA",","
  | [ '.' ] -> "FULLSTOP","."
  | [ '\\' ] -> "BIND","\\"
  | [ '/' ] -> "BIND","/"
  | [ '(' ] -> "LPAREN","("
  | [ ')' ] -> "RPAREN",")"
  | [ '=' ] arr -> "IMPL", $buf
  | [ '=' ] -> "EQUAL","="
]

let spy f s = if !Trace.debug then begin
  Printf.eprintf "<- %s\n"
    (match Stream.peek s with None -> "EOF" | Some x -> String.make 1 x);
  let t, v as tok = f s in
  Printf.eprintf "-> %s = %s\n" t v;
  tok
  end else f s

let rec lex c = parser
  | [< ' ( ' ' | '\n' ); s >] -> lex c s
  | [< '( '%' ); s >] -> comment c s
  | [< s >] ->
       match spy (tok c) s with
       | "CONSTANT","pi" -> "PI", "pi"
       | "CONSTANT","sigma" -> "SIGMA", "sigma"
       | x -> x
and comment c = parser
  | [< '( '\n' ); s >] -> lex c s
  | [< '_ ; s >] -> comment c s

open Plexing

let lex_fun s =
  (Stream.from (fun _ -> Some (lex Lexbuf.empty s))), (fun _ -> Ploc.dummy)

let tok_match (s1,_) = (); function
  | (s2,v) when s1=s2 ->
      if !Trace.debug then Printf.eprintf "%s = %s = %s\n" s1 s2 v;
      v
  | (s2,v) ->
      if !Trace.debug then Printf.eprintf "%s <> %s = %s\n" s1 s2 v;
      raise Stream.Failure

let lex = {
  tok_func = lex_fun;
  tok_using = (fun _ -> ());
  tok_removing = (fun _ -> ());
  tok_match = tok_match;
  tok_text = (function (s,_) -> s);
  tok_comm = None;
}

let g = Grammar.gcreate lex
let lp = Grammar.Entry.create g "lp"
let premise = Grammar.Entry.create g "premise"
let atom = Grammar.Entry.create g "atom"

let uvmap = ref []
let conmap = ref []
let reset () = uvmap := []; conmap := []
let top_uv () = List.length !uvmap

let get_uv u =
  if List.mem_assoc u !uvmap then List.assoc u !uvmap
  else
    let n = List.length !uvmap in
    uvmap := (u,n) :: !uvmap;
    n
let check_con n l =
  try
    let l' = List.assoc n !conmap in
    if l <> l' then
      raise (Token.Error ("Constant "^n^" used at different levels"))
  with Not_found -> conmap := (n,l) :: !conmap

let rec binders c n = function
    | (XCon _ | XUv _) as x when equal x c -> XDB n
    | (XCon _ | XUv _ | XExt _ | XDB _) as x -> x
    | XBin(w,t) -> XBin(w,binders c (n+w) t)
    | XTup xs -> XTup (IA.map (binders c n) xs)
    | XSusp _ -> assert false
and binders_premise c n = function
    | Pi t -> Pi(binders_premise c (n+1) t)
    | Sigma t -> Sigma(binders_premise c (n+1) t)
    | Atom t -> Atom(binders c n t)
    | AtomBI bi -> AtomBI (binders_builtin c n bi)
    | Conj l -> Conj(List.map (binders_premise c n) l)
    | Impl(a,t) -> Impl(binders c n a, binders_premise c n t)
and binders_builtin c n = function
    | BIUnif (a,b) -> BIUnif(binders c n a, binders c n b)

EXTEND
  GLOBAL: lp premise atom;
  lp: [ [ cl = LIST1 clause -> cl ] ];
  clause :
    [ [ hd = atom;
        hyps =
          [ ENTAILS; hyp = premise; FULLSTOP -> hyp
          | FULLSTOP -> Conj [] ] ->
              let top = top_uv () in reset ();
              0, top, hd, hyps ] ];
  atom :
    [ "1"
      [ hd = atom LEVEL "2"; args = LIST0 atom LEVEL "2" ->
          if args = [] then hd else mkTup (IA.of_list (hd :: args)) ]
    | "2" 
      [ [ c = CONSTANT; b = OPT [ BIND; a = atom LEVEL "1" -> a ] ->
          let c, lvl = lvl_name_of c in 
          let x = mkCon c lvl in
          match b with
          | None -> check_con c lvl; x
          | Some b ->  mkBin 1 (binders x 1 b) ]
      | [ u = UVAR -> let u, lvl = lvl_name_of u in mkUv (get_uv u) lvl ]
      | [ i = REL ->
            mkDB (int_of_string (String.sub i 1 (String.length i - 1))) ]
      | [ LPAREN; a = atom LEVEL "1"; RPAREN -> a ] ]
    ];
  premise :
    [ "1"
      [ [ conj = LIST1 premise LEVEL "2" SEP COMMA ->
            if List.length conj = 1 then List.hd conj else Conj conj ] ]
    | "2"
      [ a = atom; IMPL; p = premise -> Impl(a,p)
      | a = atom; EQUAL; b = atom -> AtomBI (BIUnif(a,b))
      | a = atom -> Atom a
      | PI; c = CONSTANT; BIND; p = premise ->
         let c, lvl = lvl_name_of c in
         let x = mkCon c lvl in
         Pi(binders_premise x 1 p)
      | SIGMA; u = UVAR; BIND; p = premise ->
         let u, lvl = lvl_name_of u in
         let x = mkUv (get_uv u) lvl in
         Sigma(binders_premise x 1 p)
      | LPAREN; a = premise LEVEL "1"; RPAREN -> a ]

    ];
END

let parse e s =
  reset ();
  try Grammar.Entry.parse e (Stream.of_string s)
  with Ploc.Exc(l,(Token.Error msg | Stream.Error msg)) ->
    let last = Ploc.last_pos l in
    let ctx_len = 10 in
    let ctx =
      let start = max 0 (last - ctx_len) in
      let len = min (String.length s - start) ctx_len in
      "…" ^ String.sub s start len in
    raise (Stream.Error(Printf.sprintf "%s: %s" ctx msg))
  | Ploc.Exc(_,e) -> raise e

let parse_program s : program = parse lp s 
let parse_goal s : goal = parse premise s
let parse_data s : data = parse atom s

end (* }}} *)
include Parser

end

module Subst = struct (* {{{ LP.Uv |-> data mapping *)
open LP

type subst = { assign : data Int.Map.t; top_uv : int }
let empty n = { assign = Int.Map.empty; top_uv = n }

let last_sub_lookup = ref (XDB 0)
let in_sub i { assign = assign } =
  try last_sub_lookup := Int.Map.find i assign; true
  with Not_found -> false
let set_sub i t s = { s with assign = Int.Map.add i t s.assign }

let rec iter_sep spc pp = function
  | [] -> ()
  | [x] -> pp x
  | x::tl -> pp x; spc (); iter_sep spc pp tl

let prf_subst fmt s =
  Format.pp_open_hovbox fmt 2;
  Format.pp_print_string fmt "{ ";
  iter_sep
    (fun () -> Format.pp_print_string fmt ";";Format.pp_print_space fmt ())
    (fun (i,t) ->
       Format.pp_open_hvbox fmt 0;
       Format.pp_print_string fmt (pr_var i 0);
       Format.pp_print_space fmt ();
       Format.pp_print_string fmt ":= ";
       prf_data [] fmt (map (fun x -> kool (look x)) t);
       Format.pp_close_box fmt ())
    (Int.Map.bindings s.assign);
  Format.pp_print_string fmt " }";
  Format.pp_close_box fmt ()
let string_of_subst s = on_buffer prf_subst s

let apply_subst s t =
  let rec subst x = match look x with
    | Uv(i,_) when in_sub i s -> map subst !last_sub_lookup
    | _ -> x in
  map subst t
let apply_subst_goal s = map_premise (apply_subst s)

let top s = s.top_uv
let raise_top i s = { s with top_uv = s.top_uv + i + 1 }

let fresh_uv lvl s = XUv(s.top_uv,lvl), { s with top_uv = s.top_uv + 1 }

end (* }}} *)

module Red = struct (* {{{ beta reduction, whd, and nf (for tests) *) 

open LP
open Subst


let lift ?(from=0) k t =
  if k = 0 then t
  else if from = 0 then mkXSusp t 0 k XNil
  else mkXSusp t from (from+k) (XSkip(k,from,XNil))

let beta depth t start len v =
  mkXSusp t len 0
    (XArgs(IA.init len (fun i -> (IA.get (i+start) v)), 0, XNil))

let reloc_uv_subst ~uv_increment:u ~cur_level:lvl args t =
  let nargs = List.length args in
  mkXSusp ~uv_reloc:(u,lvl) t nargs 0
    (if nargs > 0 then XArgs (IA.of_list args, 0, XNil) else XNil)
  
let rec whd s t =
  match look t with
  | (Ext _ | Con _ | DB _ | Bin _) -> t, s
  | Uv (i,_) when in_sub i s ->
      let t = !last_sub_lookup in
      let t', s = whd s t in
      t', if t == t' then s else set_sub i t' s
  | Uv _ -> t, s
  | Tup v ->
      let hd = IA.get 0 v in
      let hd', s = whd s hd in
      match look hd' with
      | Bin (n_lam,b) ->
        let n_args = IA.len v - 1 in
        if n_lam = n_args then
          whd s (beta 0 b 1 n_args v)
        else if n_lam < n_args then
          whd s (mkApp (beta 0 b 1 n_lam v) v (n_lam+1) (n_args+1))
        else
          let diff = n_lam - n_args in
          (beta diff (mkBin diff b) 1 n_args v), s
      | _ ->
          if hd == hd' then t, s else mkApp hd' (IA.tl v) 0 (IA.len v-1), s
          
let rec nf s x = match look x with
  | (Ext _ | Con _ | DB _) as x -> kool x
  | Bin(n,t) -> mkBin n (nf s t)
  | (Tup _ | Uv _) as xf ->
      let x', _ = whd s x in 
      match look x' with
      | Tup xs -> mkTup (IA.map (nf s) xs)
      | _ -> if x == x' then kool xf else nf s x'

end (* }}} *)

(* vim:set foldmethod=marker: *)
