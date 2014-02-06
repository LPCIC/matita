module refiner.

/************************* helpers ************************/

is_flex T :- not (not (dummy1__ = T)).

is_same_flex M N :-
  is_flex M, is_flex N, not(dummy1__ = M, dummy2__ = N).

type prt string -> A -> o.
prt S T :- 
    print S, term_to_string T TMP, print TMP, print "\n".

/************************* refiner ************************/

of _ M _ _ _ :-  is_flex M, !, prt "GAME OVER" M, not true.

of Sig (ginst M T) T (ginst M T) nil :- is_flex M, !.
of Sig (ginst M T) T2 M1 Sig2 :- !, of Sig M T2 M1 Ex1, unify (append Sig Ex1) T2 T.

of Sig hole (ginst T set) (ginst M (ginst T set)) [ goal M (ginst T set), goal T set ].

sigma_appl [] [] _ _ :- !.
sigma_appl [S1 X|Ss] [decl T S1|Ss1] X T :- sigma_appl Ss Ss1 X T.
sigma_appl (append L R) (append L1 R1) X T :- sigma_appl L L1 X T, sigma_appl R R1 X T.

of Sig (lam S F) (prod S2 T) (lam S2 F2) (append Ex1 Ex3) :-
  of Sig S SO S2 Ex1, Sig2 = append Sig Ex1,
  unify Sig2 SO set,
  pi x\ sigma Ex2\ (pi Sig\ of Sig x S2 x nil) =>
    of Sig2 (F x) (T x) (F2 x) Ex2,
    sigma_appl Ex2 /*=*/ Ex3 x S2.

of Sig1 (prod S F) set (prod S2 F2) (append Ex1 Ex3) :-
  of Sig1 S SO S2 Ex1, Sig2 = append Sig Ex1,
  unify Sig2 SO set,
  pi x\ sigma Ex2\ sigma Sig3\ (pi Sig\ of Sig x S2 x nil) =>
    of Sig2 (F x) (T x) (F2 x) Ex2, Sig3 = append Sig2 Ex2,
    unify Sig3 (T x) set,
    sigma_appl Ex2 /*=*/ Ex3 x S2.

of Sig1 (app M1 N1) (F N2) (app M2 N2) (append (append Ex1 Ex2) Ex4) :-
    of Sig1 M1 TM1 M2 Ex1, Sig2 = append Sig1 Ex1,
    of Sig2 N1 TN1 N2 Ex2, Sig3 = append Sig2 Ex2,
    pi x\ sigma Ex3\ sigma Sig4\
      of Sig3 hole _ (F x) Ex3, Sig4 = append Sig3 Ex3,
      prt "XX " (unify nil TM1 (prod TN1 F)),
      unify Sig4 TM1 (prod TN1 F),
      prt "done" true,
      sigma_appl Ex3 /*=*/ Ex4 x TN1.

of Sig zero nat zero nil.

of Sig succ (prod nat (x \ nat)) succ nil.

of Sig plus (prod nat (x\ prod nat (y\ nat))) plus nil.

of Sig nat set nat nil.

of Sig set set set nil.
of Sig vect (prod nat (x\ set)) vect nil.
of Sig vnil (app vect zero) vnil nil.
of Sig vcons (prod nat (n\ prod (app vect n) (w\ app vect (app succ n)))) vcons nil.

of Sig (rec Rty N Base Step) Rty2 (rec Rty2 N2 Base2 Step2) (append (append Ex1 Ex2) (append Ex3 Ex6)) :-
  of Sig1 Rty TRty Rty2 Ex1, Sig2 = append Sig1 Ex1,
  unify Sig2 TRty set,
  of Sig2 N TN N2 Ex2, Sig3 = append Sig2 Ex2,
  unify Sig3 TN nat,
  of Sig3 Base TBase Base2 Ex3, Sig4 = append Sig3 Ex3,
  unify Sig4 TBase Rty2,
  pi n\ sigma Ex5\ sigma Sig5\ pi acc\ sigma Ex4\
   (pi Sig\ of Sig n nat n nil) =>
   (pi Sig\ of Sig acc Rty2 acc nil) =>
     of Sig4 (Step n acc) TStep (Step2 n acc) Ex4, Sig5 = append Sig4 Ex4,
     unify Sig5 TStep Rty2,
     sigma_appl Ex4 /*=*/ Ex5 acc RTy2,
     sigma_appl Ex5 /*=*/ Ex6 n nat.

/* retype */
rof Sig T TY :- of Sig T TY _ _.

/************************* unify ************************/

unif _ _ M _ :-  is_flex M, !, prt "GAME OVER" M, not true.
unif _ _ _ M :-  is_flex M, !, prt "GAME OVER" M, not true.

/* M=M, we also assert M is in Sig */
unif ff Sig (ginst M TM) (ginst N TN) :- is_same_flex M N, !, unify Sig TM TN.

/* flex=term */
unif ff Sig (ginst M T) N,
unif ff Sig N (ginst M T) :-
  is_flex M,
  !,
  prt "flexible " (unif ff nil N (ginst M T)),
  prt " " (rof nil N TN),
  rof Sig N TN,
  prt "unify " (unify nil TN T),
  unify Sig TN T,
  prt "OK " true,
  M = N.

/* reflexive closure + heuristic for == */
/*unif ff _ T T :- !.*/
unif ff _ nat nat :- !.
unif ff _ set set :- !.

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
