type token =
  | MODULE
  | END
  | IMPORT
  | ACCUMULATE
  | ACCUMSIG
  | USESIG
  | LOCAL
  | LOCALKIND
  | CLOSED
  | SIG
  | KIND
  | TYPE
  | TYPEABBREV
  | EXPORTDEF
  | USEONLY
  | INFIXL
  | INFIX
  | INFIXR
  | PREFIX
  | PREFIXR
  | POSTFIX
  | POSTFIXL
  | LAMBDA
  | FORALL
  | FORSOME
  | COLONDASH
  | IMPLIES
  | INFIXLAMBDA
  | TYARROW
  | CUT
  | PI
  | SIGMA
  | COMMA
  | SEMICOLON
  | AMPAND
  | RDIVIDE
  | NILLIST
  | LISTCONS
  | EQUAL
  | PLUS
  | MINUS
  | TIMES
  | LESS
  | LEQ
  | GTR
  | GEQ
  | UMINUS
  | PERIOD
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | COLON
  | VBAR
  | SIGSTART
  | MODSTART
  | TERMSTART
  | EOF
  | ID of ((string * Preabsyn.pidkind))
  | SYID of ((string * Preabsyn.pidkind))
  | VID of ((string * Preabsyn.pidkind))
  | UPCID of ((string * Preabsyn.pidkind))
  | STRLIT of (string)
  | INTLIT of (int)
  | REALLIT of (float)

val parseModule :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Preabsyn.pmodule
val parseSignature :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Preabsyn.pmodule
val parseModClause :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Preabsyn.pterm
