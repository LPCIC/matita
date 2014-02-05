module refiner.

/************************* unify ************************/

/* reflexive closure + heuristic for == */
unif ff T T :- !.

/* heuristic: fire explicit weak head beta redexes */
unif ff (app (lam _ F) M) X,
unif ff X (app (lam _ F) M) :- !, unif ff (F M) X.

/*unif ff (app (lam _ F) M) X,
unif ff X (app (lam _ F) M) :- !,
 pi x\ unif ff M x => unif ff X (F x).*/

/* contextual closure + heuristic */
unif ff (app H A) (app K B) :- unif ff H K, unif ff A B.

/* contextual closure */
unif ff (lam S F) (lam T G) :- !, unif ff S T, pi x\ unif ff (F x) (G x).
unif ff (prod S F) (prod T G) :- !, unif ff S T, pi x\ unif ff (F x) (G x).

/* contextual closure + heuristic */
unif ff (rec A1 B1 C1 D1) (rec A2 B2 C2 D2) :-
    unif ff A1 A2,
    unif ff B1 B2,
    unif ff C1 C2,
    pi x\ pi acc\ unif ff (D1 x acc) (D2 x acc).

/* beta */
unif _ (app L M) X :- unif ff L (lam _ F), !, unif ff X (F M).

/* delta */
unif _ plus (lam nat
             (n\ (rec nat n
                    (lam nat (x\ x))
                    (m\ acc\ lam nat (n\ app succ (app acc n)))))) :- !.
/* iota */
unif _ (rec _ N B R) X :- unif ff N zero, !, unif ff B X.
unif _ (rec T N B R) X :- unif ff N (app succ M), !, unif ff (R M (rec T M B R)) X.

/* symmetric */
unif ff A B :- unif tt B A.

unify A B :- unif ff A B.

/************************* typeof ************************/

of zero nat zero nil K :- K.

of succ (prod nat (x \ nat)) succ nil K :- K.

of f (prod nat (x \ prod nat (y \ nat))) f nil K :- K.

of plus (prod nat (x\ prod nat (y\ nat))) plus nil K :- K.

of nat set nat nil K :- K.

of set set set nil K :- K.


of vect (prod nat (x\ set)) vect nil K :- K.
of vnil (app vect zero) vnil nil K :- K.
of vcons (prod nat (n\ prod (app vect n) (w\ app vect (app succ n)))) vcons nil K :- K.


of (prod O1 T1) set (prod O2 T2) (append S1 S2) K :-
    pi x\ (pi H\ H => of x O1 x nil H) => of (T1 x) set (T2 x) S2 (
    of O1 set O2 S1 K).

of (lam T1 F1) X (lam T2 F2) (append S1 S2) K :-
    pi x\ (pi H\ H => of x T1 x nil H) => of (F1 x) (T x) (F2 x) S2 (
    of T1 SO T2 S1 (
    unify SO set,
    unify X (prod T2 T),
    K)).


of (app M1 N1) X (app M2 N2) (append S1 S2) K :-
    of M1 T M2 S1 (
    unify T (prod A F),
    of N1 S N2 S2 (
    unify S A,
    unify X (F N2),
    K)).

/*of hole X M ((M::X::nil)::nil) K :- pi x\ (pi S\ pi H\ H => of x X M S H) => K.*/

/* of hole X M ((M::X::nil)::nil) K :- pi x\ K. */
