exception NotInProlog;;

type formula = Lprun2.term
type program = (Lprun2.term * Lprun2.term) list
type goal = Lprun2.term

let mkClause lhs rhs = lhs,rhs

let rec mkConj = Lprun2.mkAnd

let rec mkDisj = Lprun2.mkOr

let mkAtomBiUnif a b = Lprun2.mkEq a b

let true_clause = Lprun2.mkTrue, mkConj []

let eq_clause =
 let v = Lprun2.Var (Lprun2.Variable.fresh ()) in
  mkAtomBiUnif v v, mkConj []

let or_clauses =
 let v1 = Lprun2.Var (Lprun2.Variable.fresh ()) in
 let v2 = Lprun2.Var (Lprun2.Variable.fresh ()) in
  [ mkDisj [v1;v2], v1
  ; mkDisj [v1;v2], v2 ]

let mkApp =
 function
    Lprun2.App(c,l1)::l2 -> Lprun2.App(c,l1@l2)
  | _ -> raise NotInProlog

let mkAtomBiCut = Lprun2.mkCut

let uvmap = ref [];;
let reset () = uvmap := []

let get_uv u =
  if List.mem_assoc u !uvmap then List.assoc u !uvmap
  else
    let n = Lprun2.Variable.fresh () in
    uvmap := (u,n) :: !uvmap;
    n

let mkUVar u = Lprun2.Var (get_uv u)
let mkCon c = Lprun2.App(Lprun2.ASTFuncS.from_string c,[])

let rec number = lexer [ '0'-'9' number ]
let rec ident =
  lexer [ [ 'a'-'z' | 'A'-'Z' | '\'' | '_' | '-' | '0'-'9' ] ident
        | '^' '0'-'9' number | ]

let rec string = lexer [ '"' | _ string ]

(*
let lvl_name_of s =
  match Str.split (Str.regexp_string "^") s with
  | [ x ] -> Name.make x, 0
  | [ x;l ] -> Name.make x, int_of_string l
  | _ -> raise (Token.Error ("<name> ^ <number> expected.  Got: " ^ s))
*)

let tok = lexer
  [ 'A'-'Z' ident -> "UVAR", $buf 
  | 'a'-'z' ident -> "CONSTANT", $buf
  | '_' '0'-'9' number -> "REL", $buf
  | '_' -> "FRESHUV", "_"
  |  ":-"  -> "ENTAILS",$buf
  |  ":"  -> "COLON",$buf
  |  "::"  -> "CONS",$buf
  | ',' -> "COMMA",","
  | ';' -> "SEMICOLON",","
  | '.' -> "FULLSTOP","."
  | '\\' -> "BIND","\\"
  | '/' -> "BIND","/"
  | '(' -> "LPAREN","("
  | ')' -> "RPAREN",")"
  | '[' -> "LBRACKET","["
  | ']' -> "RBRACKET","]"
  | '|' -> "PIPE","|"
  | "=>" -> "IMPL", $buf
  | '=' -> "EQUAL","="
  | '<' -> "LT","<"
  | '>' -> "GT",">"
  | '$' 'a'-'z' ident -> "BUILTIN",$buf
  | '!' -> "BANG", $buf
  | '@' -> "AT", $buf
  | '#' -> "SHARP", $buf
  | '?' -> "QMARK", $buf
  | '"' string -> "LITERAL", let b = $buf in String.sub b 1 (String.length b-2)
]

let option_eq x y = match x, y with Some x, Some y -> x == y | _ -> x == y

let rec lex c = parser bp
  | [< '( ' ' | '\n' | '\t' ); s >] -> lex c s
  | [< '( '%' ); s >] -> comment c s
  | [< '( '/' ); s >] ep ->
       if option_eq (Stream.peek s) (Some '*') then comment2 c s
       else ("BIND", "/"), (bp,ep)
  | [< s >] ep ->
       if option_eq (Stream.peek s) None then ("EOF",""), (bp, ep)
       else
       (match tok c s with
       | "CONSTANT","pi" -> "PI", "pi"
       | "CONSTANT","sigma" -> "SIGMA", "sigma"
       | "CONSTANT","nil" -> "NIL", "nil"
       | "CONSTANT","delay" -> "DELAY","delay"
       | "CONSTANT","in" -> "IN","in"
       | "CONSTANT","with" -> "WITH","with"
       | "CONSTANT","resume" -> "RESUME","resume"
       | "CONSTANT","context" -> "CONTEXT","context"
       | x -> x), (bp, ep)
and comment c = parser
  | [< '( '\n' ); s >] -> lex c s
  | [< '_ ; s >] -> comment c s
and comment2 c = parser
  | [< '( '*' ); s >] ->
       if option_eq (Stream.peek s) (Some '/') then (Stream.junk s; lex c s)
       else comment2 c s
  | [< '_ ; s >] -> comment2 c s


open Plexing

let lex_fun s =
  let tab = Hashtbl.create 207 in
  let last = ref Ploc.dummy in
  (Stream.from (fun id ->
     let tok, loc = lex Lexbuf.empty s in
     last := Ploc.make_unlined loc;
     Hashtbl.add tab id !last;
     Some tok)),
  (fun id -> try Hashtbl.find tab id with Not_found -> !last)

let tok_match (s1,_) = (); function
  | (s2,v) when Pervasives.compare s1 s2 == 0 -> v
  | (s2,v) -> raise Stream.Failure

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
let goal = Grammar.Entry.create g "goal"

(*
let uvmap = ref []
let conmap = ref []
let reset () = uvmap := []; conmap := []
let uvlist () = List.map snd !uvmap
*)

(*
let get_uv u =
  if List.mem_assoc u !uvmap then List.assoc u !uvmap
  else
    let n = List.length !uvmap in
    uvmap := (u,n) :: !uvmap;
    n
*)
(*
let fresh_lvl_name () = lvl_name_of (Printf.sprintf "_%d" (List.length !uvmap))

let check_con n l =
  try
    let l' = List.assoc n !conmap in
    if l <> l' then
      raise
        (Token.Error("Constant "^Name.to_string n^" used at different levels"))
  with Not_found -> conmap := (n,l) :: !conmap
let mkFreshCon name lvl =
  let name = Name.make name in
  let t = mkConN name lvl in
  assert(not(List.mem_assoc name !conmap));
  conmap := (name,lvl) :: !conmap;
  t
*)

(*
let sigma_abstract t =
  let uvl = collect_Uv t in
  List.fold_left (fun p uv -> mkSigma1 (grab uv 1 p)) t uvl
*)

(* TODO : test that it is of the form of a clause
let check_clause x = ()
let check_goal x = ()*)

let atom_levels =
  ["pi";"disjunction";"conjunction";"implication";"equality";"term";"app";"simple";"list"]

let () =
  Grammar.extend [ Grammar.Entry.obj atom, None,
    List.map (fun x -> Some x, Some Gramext.NonA, []) atom_levels ]

EXTEND
  GLOBAL: lp premise atom goal;
  lp: [ [ cl = LIST0 clause; EOF -> true_clause::eq_clause::or_clauses@cl ] ];
(*  name : [ [ c = CONSTANT -> c | u = UVAR -> u | FRESHUV -> "_" ] ];
  label : [ [ COLON;
              n = name;
              p = OPT [ LT; n = name -> `Before n | GT; n = name -> `After n ];
              COLON -> n,p ] ];
*)
  clause :
    [[ (*name = OPT label;*)
       hd = concl; hyp = OPT [ ENTAILS; hyp = premise -> hyp ]; FULLSTOP ->
(*
         let name, insertion = match name with
         | None -> CN.fresh (), `Here
         | Some (s,pos) -> match pos with
             | None -> CN.make s, `Here
             | Some (`Before "_") -> CN.make ~float:`Begin s, `Begin
             | Some (`After "_") -> CN.make ~float:`End s, `End
             | Some (`Before n) -> CN.make s, `Before(CN.make ~existing:true n)
             | Some (`After n) -> CN.make s, `After(CN.make ~existing:true n) in
*)
         let hyp = match hyp with None -> mkConj [](*L.empty*) | Some h -> h in
(*
         let clause = sigma_abstract (mkImpl hyp (mkAtom hd)) in
         check_clause clause;
         reset (); 
         ([], key_of clause, clause, name), insertion*)
         reset (); 
         mkClause hd hyp ]];
  goal:
    [[ p = premise -> (*
         let g = sigma_abstract p in
         check_goal g;
         reset ();
         g*)
         reset (); 
         p ]];
  premise : [[ a = atom -> a ]];
  concl : [[ a = atom LEVEL "term" -> a ]];
  atom : LEVEL "pi"
     [(*[ PI; x = bound; BIND; p = atom LEVEL "disjuction" ->
         let (x, is_uv), annot = x, None in
         let bind = if is_uv then mkSigma1 else mkPi1 annot in
         bind (grab x 1 p)
      | PI; annot = bound; x = bound; BIND; p = atom LEVEL "disjuction" ->
         let (x, is_uv), annot = x, Some (fst annot) in
         let bind = if is_uv then mkSigma1 else mkPi1 annot in
         bind (grab x 1 p)
      | PI; LPAREN; annot = atom LEVEL "disjuction"; RPAREN;
        x = bound; BIND; p = atom LEVEL "disjuction" ->
         let (x, is_uv), annot = x, Some annot in
         let bind = if is_uv then mkSigma1 else mkPi1 annot in
         bind (grab x 1 p)
      | PI; annot = atom LEVEL "list";
        x = bound; BIND; p = atom LEVEL "disjuction" ->
         let (x, is_uv), annot = x, Some annot in
         let bind = if is_uv then mkSigma1 else mkPi1 annot in
         bind (grab x 1 p)
      | SIGMA; x = bound; BIND; p = atom LEVEL "disjuction" ->
         mkSigma1 (grab (fst x) 1 p) ]*)];
  atom : LEVEL "disjunction"
     [[ l = LIST1 atom LEVEL "conjunction" SEP SEMICOLON -> mkDisj l ]];
  atom : LEVEL "conjunction"
     [[ l = LIST1 atom LEVEL "implication" SEP COMMA -> mkConj l ]];
  atom : LEVEL "implication"
     [[ (*a = atom; IMPL; p = atom LEVEL "implication" ->
          mkImpl (mkAtom a) (mkAtom p)
      | a = atom; ENTAILS; p = premise ->
          mkImpl (mkAtom p) (mkAtom a)*) ]];
  atom : LEVEL "equality"
     [[ a = atom; EQUAL; b = atom LEVEL "term" ->
          mkAtomBiUnif a b ]];
  atom : LEVEL "term"
     [(*[ l = LIST1 atom LEVEL "app" SEP CONS ->
          if List.length l = 1 then List.hd l
          else
            let l = List.rev l in
            let last = List.hd l in
            let rest = List.rev (List.tl l) in
            mkSeq (L.of_list rest) last ]*)];
  atom : LEVEL "app"
     [[ hd = atom; args = LIST1 atom LEVEL "simple" ->
          (*match args with
          | [tl;x] when equal x sentinel -> mkVApp `Rev tl hd None
          | _ ->*) mkApp (hd::args) (*(L.of_list (hd :: args))*) ]];
  atom : LEVEL "simple" 
     [[ c = CONSTANT(*; b = OPT [ BIND; a = atom LEVEL "term" -> a ]*) ->
          (*let c, lvl = lvl_name_of c in 
          let x = mkConN c lvl in
          (match b with
          | None -> check_con c lvl; x
          | Some b ->  mkBin 1 (grab x 1 b))*)
          mkCon c
      | u = UVAR -> (*let u, lvl = lvl_name_of u in mkUv (get_uv u) lvl*) mkUVar u
      | u = FRESHUV -> (*let u, lvl = fresh_lvl_name () in mkUv (get_uv u) lvl*) mkUVar u
      (*| i = REL -> mkDB (int_of_string (String.sub i 1 (String.length i - 1)))
      | NIL -> mkNil
      | s = LITERAL -> mkExt (mkString s)
      | AT; hd = atom LEVEL "simple"; args = atom LEVEL "simple" ->
          mkVApp `Regular hd args None
      | AT -> sentinel
      | CONTEXT; hd = atom LEVEL "simple" -> mkAtomBiContext hd
      | QMARK; hd = atom LEVEL "simple"; args = atom LEVEL "simple" ->
          mkVApp `Flex hd args None
      | SHARP; hd = atom LEVEL "simple"; args = atom LEVEL "simple";
        info = OPT atom LEVEL "simple" ->
          mkVApp `Frozen hd args info
      | bt = BUILTIN; a = atom LEVEL "simple" -> mkAtomBiCustom bt a*)
      | BANG -> mkAtomBiCut
      (*| DELAY; t = atom LEVEL "simple"; p = atom LEVEL "simple";
        vars = OPT [ IN; x = atom LEVEL "simple" -> x ];
        info = OPT [ WITH; x = atom LEVEL "simple" -> x ] ->
          mkDelay t p vars info
      | RESUME; t = atom LEVEL "simple"; p = atom LEVEL "simple" -> mkResume t p*)
      | LPAREN; a = atom; RPAREN -> a ]];
  atom : LEVEL "list" 
     [(*[ LBRACKET; xs = LIST0 atom LEVEL "implication" SEP COMMA;
          tl = OPT [ PIPE; x = atom LEVEL "term" -> x ]; RBRACKET ->
          let tl = match tl with None -> mkNil | Some x -> x in
          if List.length xs = 0 && tl <> mkNil then 
            raise (Token.Error ("List with not elements cannot have a tail"));
          if List.length xs = 0 then mkNil
          else mkSeq (L.of_list xs) tl ]*)];
  (*bound : 
    [[ c = CONSTANT -> let c, lvl = lvl_name_of c in mkConN c lvl, false
      | u = UVAR -> let u, lvl = lvl_name_of u in mkUv (get_uv u) lvl, true ]
    ];*)
END

let parse e s =
  reset ();
  try Grammar.Entry.parse e (Stream.of_string s)
  with Ploc.Exc(l,(Token.Error msg | Stream.Error msg)) ->
    let last = Ploc.last_pos l in
    let ctx_len = 70 in
    let ctx =
      let start = max 0 (last - ctx_len) in
      let len = min 100 (min (String.length s - start) last) in
      "…" ^ String.sub s start len ^ "…" in
    raise (Stream.Error(Printf.sprintf "%s\nnear: %s" msg ctx))
  | Ploc.Exc(_,e) -> raise e

let parse_program (*?(ontop=[])*) s : program =
  (* let insertions = parse lp s in
  let insert prog = function
    | item, (`Here | `End) -> prog @ [item]
    | item, `Begin -> item :: prog
    | (_,_,_,name as item), `Before n ->
        let newprog = List.fold_left (fun acc (_,_,_,cn as c) ->
          if CN.equal n cn then acc @ [item;c]
          else acc @ [c]) [] prog in
        if List.length prog = List.length newprog then
          raise (Stream.Error ("unable to insert clause "^CN.to_string name));
        newprog
    | (_,_,_,name as item), `After n ->
        let newprog = List.fold_left (fun acc (_,_,_,cn as c) ->
          if CN.equal n cn then acc @ [c;item]
          else acc @ [c]) [] prog in
        if List.length prog = List.length newprog then
          raise (Stream.Error ("unable to insert clause "^CN.to_string name));
        newprog in
  List.fold_left insert ontop insertions*)
  parse lp s

let parse_goal s : goal = parse goal s
(*let parse_data s : data = parse atom s*)
