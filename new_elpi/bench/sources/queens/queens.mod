% ?- queens(4, Qs).
%   produces
%   Qs = [3,1,4,2] ;
%   Qs = [2,4,1,3]

% queens   +int  -[int]

module queens.

%spy X :- $print start X, X, $print ok X.
%spy X :- $print ko X, fail.


plus zero X X.
plus (s X) Y (s S) :- plus X Y S.

less zero (s _).
less (s X) (s Y) :- less X Y.

neq zero (s _).
neq (s _) zero.
neq (s X) (s Y) :- neq X Y.

queens N Qs :- range (s zero) N Ns, queens_aux Ns xnil Qs.

queens_aux xnil Qs Qs.
queens_aux UnplacedQs SafeQs Qs :- 
        select UnplacedQs UnplacedQs1 Q,
        not_attack SafeQs Q (s zero),
        queens_aux UnplacedQs1 (xcons Q SafeQs) Qs.


not_attack_aux Xs X :- not_attack Xs X (s zero).
not_attack xnil DUMMY1 DUMMY2 :- !.
not_attack (xcons Y Ys) X N :- plus Y N S1, neq X S1, 
                               plus X N S2, neq Y S2,
                               N1 = (s N), 
                               not_attack Ys X N1.

%select A B C :- $print first_clause (select A B C), fail.
select (xcons X Xs) Xs X.
%select A B C :- $print backtrack (select A B C), fail.
select (xcons Y Ys) (xcons Y Zs) X :- select Ys Zs X.
%select A B C :- $print no_more_chances (select A B C), fail.

range N N (xcons N xnil) :- !.
range M N (xcons M Ns) :- less M N, M1 = (s M), range M1 N Ns.

main :- queens (s (s (s (s zero)))) L, xxx L.
xxx (xcons (s (s zero)) (xcons (s (s (s (s zero)))) (xcons (s zero) (xcons (s (s (s zero))) xnil)))).

q L :- queens (s (s (s (s zero)))) L.



% ----------------------------------------------------------
%queens(N,Qs) :- range(1,N,Ns), queens(Ns,[],Qs).

%queens([],Qs,Qs).
%queens(UnplacedQs,SafeQs,Qs) :-  select(UnplacedQs,UnplacedQs1,Q),
%             not_attack(SafeQs,Q), queens(UnplacedQs1,[Q|SafeQs],Qs).

%not_attack(Xs,X) :- not_attack(Xs,X,1).
%not_attack([],_,_) :- !.
%not_attack([Y|Ys],X,N) :-X =\= Y+N,X =\= Y-N,N1 is N+1,not_attack(Ys,X,N1).

%select([X|Xs],Xs,X).
%select([Y|Ys],[Y|Zs],X) :- select(Ys,Zs,X).

%range(N,N,[N]) :- !.
%range(M,N,[M|Ns]) :- M < N, M1 is M+1, range(M1,N,Ns).
