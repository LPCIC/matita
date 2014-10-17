module cic.

eq X X.

neq A B :- neq B A.
neq (app L) (lam _ F).
neq (app xnil) (app (xcons HD TL)).
neq (app (xcons X XS)) (app (xcons Y YS)) :- neq X Y.
neq (app (xcons X XS)) (app (xcons Y YS)) :- neq (app XS) (app YS).
neq (lam TY1 F) (lam TY2 G) :- neq TY1 TY2.
neq (lam TY1 F) (lam TY2 G) :- pi x\ neq (F x) (G x).
neq (prod S T) (app L).
neq (prod S T) (lam _ L).
neq (prod S T) set.
neq (lam _ F) set.
neq (app L) set.

list2 F xnil xnil.
%:list2_xcons:
list2 F (xcons X XS) (xcons Y YS) :- F X Y, list2 F XS YS.

list1 F xnil.
list1 F (xcons X XS) :- F X, list1 F XS.

rev-aux xnil Acc Acc.
rev-aux (xcons X XS) Acc O :- rev-aux XS (xcons X Acc) O.
rev L LR :- rev-aux L xnil LR.

if C D B1 B2 :- eq C D, B1.
if C D B1 B2 :- neq C D, B2.

%%%%%%%%%%%%%%%%% <auxiliary predicates> %%%%%%%%%%%%%%
is_term set.
is_term (lam T F) :- is_term T, pi x\ is_term x => is_term (F x).
is_term (prod T F) :- is_term T, pi x\ is_term x => is_term (F x).
is_term (app L) :- list1 is_term L.
%%%%%%%%%%%%%%%%% </auxiliary predicates> %%%%%%%%%%%%%%

copy set set.

%:copy_lam:
copy (lam T1 F1) (lam T2 F2) :-
 copy T1 T2,
 pi x\ copy x x => copy (F1 x) (F2 x).

%:copy_prod:
copy (prod T1 F1) (prod T2 F2) :-
 copy T1 T2,
 pi x\ copy x x => copy (F1 x) (F2 x).

%:copy_app:
copy (app L1) (app L2) :- list2 copy L1 L2.

of T ExpTY NewT :- of T InfTY RT, coerce RT InfTY ExpTY NewT.

% cases dropped
coerce T TyA TyE T :- unify TyA TyE.

% mono-directional rule
of hole Ty2 T2 :- of Ty set Ty, copy Ty Ty2, of T Ty T, copy T T2.

of (lam S F) (prod S2 T) (lam S2 F2) :-
  of S set S2,
  pi x\ of x S2 x => copy x x => of (F x) (T x) (F2 x).

% case dropped
%of (lam S F) TY (lam S2 F2) :-
%  whd-w-delta TY (prod S2 T),
%  of S set S3,
%  unify S2 S3,
%  (pi x\ (of x S3 x :- !) => of (F x) (T x) (F2 x)).

of (prod S F) set (prod S2 F2) :-
  of S set S2, pi x\ of x S2 x => copy x x => of (F x) set (F2 x).

of (app (xcons T U)) TyV V :-
  of T TyT T1, eat-prod T1 xnil xnil TyT U V TyV.

of set set set.

eat-prod T xnil _ TY xnil     T TY. % :- !. % kill unary app
eat-prod T XS _ TY xnil     (app (xcons T  Args)) TY :- rev XS Args.
% kernel disentangled from refiner
eat-prod T XS XSTY TY (xcons U US) V TyV :-
  whd-w-delta TY WhdTY,
  eq WhdTY (prod Src Tgt),
  of U Src U1,
  eat-prod T (xcons U1 XS) (xcons Src XSTY) (Tgt U1) US V TyV.

% Teorema su eat-prod!
%eat-prod T XS XSTY TY (xcons U US) V TyV :-
%  whd-w-delta TY WhdTY,
%  if (WhdTY = prod Src Tgt)
%    (of U Src U1,
%     eat-prod T (xcons U1 XS) (xcons Src XSTY) (Tgt U1) US V TyV)
%    (WhdTY = #M _,
%     mk-prod (xcons U US) (xcons U1 U1S) Prod, unify WhdTY Prod,
%     % infefficient, U1S are already refined
%     WhdTY = prod TyU Tgt, eat-prod T (xcons U1 XS) (xcons TyU XSTY) (Tgt U1) U1S V TyV).

% cases missing
whd-w-delta X Y :- whd X Y.

and A B :- A, B.

whd (app (xcons HD (xcons A Rest))) X :-
  whd HD HDRed,
  if HDRed (lam _ F)
     (and (subst F A Rest Reduct) (whd Reduct X))
     (eq X (app (xcons HDRed (xcons A Rest)))).

whd X X.

subst Where What Rest Out :- % fixme: app[app)...
  (pi x\ copy x What => copy (Where x) Out2),
  if (app Rest) (app xnil) (eq Out Out2) (eq Out (app (xcons Out2 Rest))).

unify A B :- unif ff A B.

unif ff set set.

unif ff (app AS) (app BS) :- list2 unify AS BS.

unif ff (lam S F) (lam T G) :-
  unify S T, pi x\ of x S x => copy x x => unify (F x) (G x).
unif ff (prod S F) (prod T G) :-
  unify S T, pi x\ of x S x => copy x x => unify (F x) (G x).


unif _ X Y :- whd-progress X Z, unify Z Y.


unif ff A B :- unif tt B A.

whd-progress X Y :- whd X Y, neq X Y.
