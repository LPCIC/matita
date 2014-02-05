module refiner.

/************************* helpers ************************/

is_flex T :- not (not (dummy1__ = T)).

is_same_flex M N :-
  is_flex M, is_flex N, not(dummy1__ = M, dummy2__ = N).

mem X [(Y::T::nil)|_] T :- is_same_flex X Y, !.
mem X [_|L] T :- mem X L T.

find M Sig T :- mem M Sig T, !.
find M Sig T :- !, prt "Meta " M, prt " not found in " Sig,  not true.

type prt string -> A -> o.
prt S T :- 
    print S, term_to_string T TMP, print TMP, print "\n".

/************************* refiner ************************/

of Sig M T M Sig :-
  is_flex M,
  !,
  find M Sig T.

of Sig hole T M [ [M,T], [T,set] | Sig].

of Sig1 (lam S F) (prod S2 T) (lam S2 F2) Sig3 :-
  of Sig1 S SO S2 Sig2,
  unify Sig2 SO set,
  pi x\ (pi Sig\ of Sig x S2 x Sig) => of Sig2 (F x) (T x) (F2 x) Sig3.

of Sig1 (prod S F) set (prod S2 F2) Sig3 :-
  of Sig1 S SO S2 Sig2,
  unify Sig2 SO set,
  pi x\ (pi Sig\ of Sig x S2 x Sig) =>
    of Sig2 (F x) (T x) (F2 x) Sig3,
    unify Sig3 (T x) set.

of Sig1 (app M1 N1) (F N2) (app M2 N2) Sig4 :-
    of Sig1 M1 TM1 M2 Sig2,
    of Sig2 N1 TN1 N2 Sig3,
    pi x\
      of Sig3 hole _ (F x) Sig4,
      unify Sig4 TM1 (prod TN1 F).

of Sig zero nat zero Sig.

of Sig succ (prod nat (x \ nat)) succ Sig.

of Sig plus (prod nat (x\ prod nat (y\ nat))) plus Sig.

of Sig nat set nat Sig.

of Sig set set set Sig.

of Sig vect (prod nat (x\ set)) vect Sig.
of Sig vnil (app vect zero) vnil Sig.
of Sig vcons (prod nat (n\ prod (app vect n) (w\ app vect (app succ n)))) vcons Sig.

of Sig (rec Rty N Base Step) Rty2 (rec Rty2 N2 Base2 Step2) Sig5 :-
  of Sig1 Rty TRty Rty2 Sig2,
  unify Sig2 TRty set,
  of Sig2 N TN N2 Sig3,
  unify Sig3 TN nat,
  of Sig3 Base TBase Base2 Sig4,
  unify Sig4 TBase Rty2,
  pi n\ pi acc\
   (pi Sig\ of Sig n nat n Sig) =>
   (pi Sig\ of Sig acc Rty2 acc Sig) =>
     of Sig4 (Step n acc) TStep (Step2 n acc) Sig5,
     unify Sig5 TStep Rty2.

/* retype */
rof Sig T TY :- of Sig T TY _ _.

/************************* unify ************************/

/* M=M, we also assert M is in Sig */
unif ff Sig M N :- is_same_flex M N, !, find M Sig _.

/* flex=term */
unif ff Sig M N,
unif ff Sig N M :-
  is_flex M,
  !,
  find M Sig T,
  rof Sig N TN,
  unify Sig TN T,
  M = N.

/* reflexive closure + heuristic for == */
unif ff _ T T :- !.

/* heuristic: fire explicit weak head beta redexes */
unif ff Sig (app (lam _ F) M) X,
unif ff Sig X (app (lam _ F) M) :- !, unify Sig (F M) X.

/* contextual closure + heuristic */
unif ff Sig (app H A) (app K B) :- unify Sig H K, unify Sig A B.

/* contextual closure */
unif ff Sig (lam S F) (lam T G) :- !, unify Sig S T, pi x\ unify Sig (F x) (G x).
unif ff Sig (prod S F) (prod T G) :- !, unify Sig S T, pi x\ unify Sig (F x) (G x).

/* contextual closure + heuristic */
unif ff Sig (rec A1 B1 C1 D1) (rec A2 B2 C2 D2) :-
    unify Sig A1 A2,
    unify Sig B1 B2,
    unify Sig C1 C2,
    pi x\ pi acc\ unify Sig (D1 x acc) (D2 x acc).

/* beta */
unif _ Sig (app L M) X :- unify Sig L (lam _ F), !, unify Sig (F M) X.

/* delta */
unif _ Sig plus (lam nat
             (n\ (rec nat n
                    (lam nat (x\ x))
                    (m\ acc\ lam nat (n\ app succ (app acc n)))))) :- !.
/* iota */
unif _ Sig (rec _ N B R) X :- unify Sig N zero, !, unify Sig B X.
unif _ Sig (rec T N B R) X :- unify Sig N (app succ M), !, unify Sig (R M (rec T M B R)) X.

/* symmetric */
unif ff Sig A B :- unif tt Sig B A.

unify Sig A B :- unif ff Sig A B.

test_unify Sig1 A B A1 B1 Sig3 :-
  prt "" (of Sig1 A TA A1 Sig2),
  of Sig1 A TA A1 Sig2,
  prt "" (of Sig2 B TB B1 Sig3),
  of Sig2 B TB B1 Sig3,
  prt "" (unify Sig3 TA TB),
  unify Sig3 TA TB,
  prt "" (unify Sig3 A1 B1),
  unify Sig3 A1 B1.
