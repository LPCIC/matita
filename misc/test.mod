module test.

% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.
% of X A B :- fail.

if B T FOO :- B, !, T.
if FOO BAR E :- E.

rev L RL :- rev-aux L [] RL.
rev-aux [] L L.
rev-aux [X|XS] ACC R :- rev-aux XS [X|ACC] R. 

 whd X X.
 whd-w-delta X Y :-
   (whd (atom ID) RedBody :- body ID Body, whd Body RedBody) => whd X Y.
of (let-in T V B) (let-in T2 V2 BTY2) (let-in T2 V2 B2) :-
  of T set T2, of V T2 V2,
  pi x\ def x T2 V2 => of (B x) (BTY2 x) (B2 x).
of V TY V :- def V TY _, !. 
of (app [T|U]) TyV V :- of T TyT T1, eat-prod T1 [] [] TyT U V TyV.
eat-prod T [] _ TY []     T TY :- !. % kill unary app
eat-prod T XS _ TY []     (app [T| Args]) TY :- rev XS Args.
eat-prod T XS XSTY TY [U|US] V TyV :-
   whd-w-delta TY WhdTY,
  if (WhdTY = prod Src Tgt)
     (of U Src U1,
      eat-prod T [U1|XS] [Src|XSTY] (Tgt U1) US V TyV)
     fail.
of (atom ID) T (atom ID) :- env ID T, !.
env zero (atom nat).
env succ (prod (atom nat) (x \ (atom nat))).
env nat set.

ten X Y :- (app [atom succ,app [atom succ,app [atom succ,app [atom succ,app [atom succ,app [atom succ,app [atom succ,app [atom succ,app [atom succ,app [atom succ, X]]]]]]]]]]) = Y.

hundred X Y :- ten X Z1, ten Z1 Z2, ten Z2 Z3, ten Z3 Z4, ten Z4 Z5, ten Z5 Z6, ten Z6 Z7, ten Z7 Z8, ten Z8 Z9, ten Z9 Y.

test X :-
 hundred (atom zero) Z1,
 hundred Z1 Z2,
 hundred Z2 Z3,
 hundred Z3 Z4,
 hundred Z4 Z5,
 hundred Z5 Z6,
 hundred Z6 Z7,
 hundred Z7 Z8,
 hundred Z8 Z9,
 hundred Z9 Z10,
 of Z10 X Y.

%test X Y :- of (app [atom succ,atom zero]) X Y.
%(app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ, app [atom succ,atom zero ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]) X Y. 
