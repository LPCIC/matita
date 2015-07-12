sig delay.

type memb                     A -> list A -> o.
type append    list A -> list A -> list A -> o.
type if        o -> o -> o -> o.
type forevery  (A -> o) -> list A -> o.

% The flex test will only make sense if everyone promises not to
% use this dummy constant anywhere.  Notice that dummy cannot be
% made into an abstract datatype.

type dummy     A.
type flex      A -> o.

kind seq     type.
type trivial seq.                    % Trivially true sequent.
type arrow   list o -> o -> seq.     % Primitive sequent
type bind    (A -> seq) -> seq.      % Better to replace polymorphic type
                                     %   with a specific type if possible

% Since lambda Prolog does not allow implications in terms, we
%  introduce a constant that shall be interpreted as implication.

type ==>     o -> o -> o.
infixr ==>   4.

type non_atomic, atomic    o -> o.

% (clause Head Body) encodes   " Head :- Body.  "
type clause  o -> o -> o.

type delay          o -> o.
type delay_seq    seq -> o.

% Simply application of a clause for backchaining.
type bc  seq -> seq -> o.

% Reduce goals by either backchaining or delaying them.
type prove, prv         list seq -> list seq -> o.
type listify                 seq -> list seq -> o.
type backchain   seq -> list seq -> list seq -> o.
type bind_list   (A -> list seq) -> list seq -> o.

% Example: Simple test cases
% kind i      type.
% type a      i.
% type f      i -> i -> i.
% type h      (i -> i) -> i.
% 
% type copy   i -> i -> o.
% type subst  (i -> i) -> i -> i -> o.
% type test   int -> list i -> list seq -> o.

% Example: Matita inspired example

kind term type.
type app    term -> term -> term.
type prod   term -> (term -> term) -> term.
type lam    term -> (term -> term) -> term.
type set    term.

type nat  term.
type zero term.
type succ term.

type of     term -> term -> term -> o.
type unify          term -> term -> o.
type test_unify     term -> term -> term -> term -> o.

type copy           term -> term -> o.
type subst          (term -> term) -> term -> term -> o.
