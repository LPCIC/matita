% Early draft (7 Feb 2014)
% A (meta) interpreter for lambda Prolog that allows for the 
% declarations of delayed goals.

module delay.
%%%%%%%%%%%%%%%%  Standard stuff for debugging   %%%%%%%%%%%%%%
type qspy             o -> o.
type announce, spy    o -> o.
type bracket          string -> o -> string -> o.  % Auxiliary

bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n", fail).
qspy G :- (term_to_string G _, G, term_to_string G _).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% backchain A B C :- announce (backchain A B C).
% bc        A B   :- announce (bc A B).
% clause    A B   :- announce (clause A B).
% delay     A     :- announce (delay A).
% listify   A B   :- announce (listify A B).
% prv       A B   :- announce (prv A B).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Standard library predicates
memb X (X::_).
memb X (_::L) :- memb X L.

append nil L L.
append (X::L) K (X::M) :- append L K M.

if P Q R :- P, !, Q.
if P Q R :- R.

forevery P nil.
forevery P (X::L) :- P X, forevery P L.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

flex X :- not (not (X = dummy)).

non_atomic (_ ==> _) & non_atomic (_, _) & 
non_atomic (pi _)    & non_atomic true.  
atomic A :- not (non_atomic A).

delay_seq (bind Seq)       :- pi x\ delay_seq (Seq x).
delay_seq (arrow Hyp Atom) :- delay Atom.

% Call the following predicate with sequents that have just *atomic* rhs.
% Do not call with a conjunction as the goal.
prove Seqs Final :-
 (prv nil Delays => prv Seqs nil),
  if (forevery delay_seq Delays) (Delays = Final) (prove Delays Final).

prv (Seq::Seqs) Delays :-
  if (delay_seq Seq) (prv Seqs (Seq::Delays))
                     (backchain Seq Seqs Delays).

bc (bind In) (bind Out) :- pi x\ bc (In x) (Out x).
bc (arrow Hyps Atom) trivial           :- atomic Atom, memb   Atom Hyps.
bc (arrow Hyps Atom) (arrow Hyps Body) :- atomic Atom, clause Atom Body.

backchain Seq Seqs Delays :-
  bc Seq Seq', listify Seq' Seqs', append Seqs' Seqs Seqs'',
  prv Seqs'' Delays.

%  Bizarre: the following qspy seems to be needed to make sure that
%  this predicate works.  Probably, printing and normalization interact strangely.
%  To exercise this bug, try the following simple query: 
%    ?- listify (arrow nil (pi x\ pi y\ copy x y)) L.
listify (bind Seq) L :- (pi x\ qspy (listify (Seq x) (K x))), bind_list K L.
listify trivial nil.
listify (arrow Hyps true) [].
listify (arrow Hyps (pi G)) L :- listify (bind x\ arrow Hyps (G x)) L.
listify (arrow Hyps (H ==> G)) L :- listify (arrow (H::Hyps) G) L.
listify (arrow Hyps (G , G')) L :- 
   listify (arrow Hyps G ) K,
   listify (arrow Hyps G') K', append K K' L.
listify (arrow Hyps Atom) [(arrow Hyps Atom)] :- atomic Atom.

bind_list (x\ (Seq x)::(Seqs x)) ((bind Seq)::Rest) :- bind_list Seqs Rest.
bind_list (x\ nil) nil.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Examples: simple copy-clause example for first phase of testing.
% 
%   delay (copy X Y) :- flex X.
% % delay (copy X Y) :- flex X, flex Y.
% clause (copy a a) true.
% clause (copy (f X Y) (f U V)) (copy X U, copy Y V).
% clause (copy (h X)   (h U))   (pi x\ copy x x ==> copy (X x) (U x)).
% clause (subst M T S) (pi x\ copy x T ==> copy (M x) S).
% 
% test 1 [X]       Delays :- prove [(arrow nil (copy a X))] Delays.
% test 2 [X]       Delays :- prove [(arrow nil (copy (f a a) X))] Delays.
% test 3 [X,U]     Delays :- prove [(arrow nil (copy (f U a) X))] Delays.
% test 4 [X,Y,Z,U] Delays :- prove [(arrow nil (copy (f X Y) U)), (arrow nil (copy U (f a Z)))] Delays.
% test 5 [X,Y,U,Z] Delays :- prove [(arrow nil (copy U (f a Z))), (arrow nil (copy (f X Y) U))] Delays.
% test 6 [X,U,Z]   Delays :- prove [(arrow nil (copy (f X a) U)), (arrow nil (copy U (f a Z)))] Delays.
% test 7 [X,Y]     Delays :- prove [(arrow nil (copy (h w\ f X w) Y))] Delays.
% test 8 [X,Y]     Delays :- prove [(arrow nil (copy (h w\ f X w) Y)),(arrow nil (copy Y (h w\ f w w)))] Delays.
% test 9 [X]       Delays :- prove [(arrow nil (copy (h w\ w) (h w\ X)))] Delays. % should fail
% test 10 [X,Y]    Delays :- prove [(arrow nil (copy (h w\ X) (h w\ Y))),(arrow nil (copy a X))] Delays.
% test 11 [(h F), (h G), X] Delays :- prove [(arrow nil (subst F a (h G))),(arrow nil (copy a X))] Delays.
% test 12 [(h F)]  Delays :- prove [(arrow nil (subst F a (f a a)))] Delays.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

delay  (of A B C) :- flex A.
clause (of (app M N) (F N') (app M' N'))
       (of M T M', unify T (prod S F), of N S' N', unify S S').
clause (of (prod S F) set (prod S2 F2))
       (of S S0 S2, unify S0 set, (pi x\ (of x S2 x) ==> of (F x) (T x) (F2 x), unify (T x) set)).
clause (of (lam S F) (prod S2 T) (lam S2 F2))
       (of S S0 S2, unify S0 set, pi x\ (of x S2 x) ==> of (F x) (T x) (F2 x)).
clause (of set set set) true.
clause (of nat set nat) true.
clause (of zero nat zero) true.
clause (of succ (prod nat x\ nat) succ) true.

delay  (copy A B) :- flex A.
clause (copy (app M N) (app M' N')) (copy M M', copy N N').
clause (copy (prod M N) (prod M' N')) (copy M M', pi x\ copy x x ==> copy (N x) (N' x)).
clause (copy (lam  M N) (prod M' N')) (copy M M', pi x\ copy x x ==> copy (N x) (N' x)).
clause (copy set set) true.
clause (copy nat nat) true.
clause (copy zero zero) true.
clause (copy succ succ) true.
clause (subst M T S) (pi x\ (copy x T) ==> copy (M x) S).

delay (unify A B) :- flex A ; flex B.
%delay (unify A B) :- flex A, flex B.
clause (unify X Y) (copy X Y).
clause (unify nat nat) true.
clause (unify set set) true.
clause (unify zero zero) true.
clause (unify succ succ) true.
clause (unify (lam S F) (lam T G))
       (unify S T, pi x\ of x S x ==> unify x x ==> copy x x ==> unify (F x) (G x)).
clause (unify (prod S F) (prod T G))
       (unify S T, pi x\ of x S x ==> unify x x ==> copy x x ==> unify (F x) (G x)).
clause (unify (app H A)
       (app K B)) (unify H K, unify A B).
clause (unify (app L M) X)
       (unify L (lam _ F), subst F M S, unify S X).
clause (unify X (app L M))
       (unify L (lam _ F), subst F M S, unify X S).
clause (test_unify A B A1 B1)
       (of A TA A1, of B TB B1, unify TA TB, unify A1 B1).

% The following now work:
% ?- prove [(arrow nil (test_unify (app (lam nat x\ x) zero) zero A B))] Delay.
% ?- prove [(arrow nil (unify (lam nat x\x) (lam nat x\x)))] D.

% Bugs
% prove [(arrow nil (of M nat M')), (arrow nil (unify M zero))] D.
% prove [(arrow nil (of M nat M, unify M succ))] D.
