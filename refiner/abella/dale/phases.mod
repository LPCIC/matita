module phases.

memb X (X::_).
memb X (_::L) :- memb X L.

% The main predicate here is (boundry Gamma Atm Premises).  This is provable
% if there is a way to reduce the proof of the sequent  Gamma --> Atm
% to the premises stored in Premises.  Those premises are computed first 
% by deciding on a formula to use in backchaining, then then calling 
% the backchaining phase (called sync here) and then the goal-reduction
% phase (called async here).

boundry Gamma Atm Premises :- (prog D ; memb D Gamma), sync Gamma Atm D Premises.

sync Gamma Atm (and D1 D2) Premises :- sync Gamma Atm D1 Premises ; 
                                       sync Gamma Atm D2 Premises.
sync Gamma Atm (all D)     Premises :- sigma T\ sync Gamma Atm (D T) Premises.
sync Gamma Atm (imp G D)   (pand P Q) :- async Gamma G P, sync Gamma Atm D Q.
sync Gamma Atm (atm Atm)   none.

async Gamma tt none.
async Gamma (and B C) (pand P Q) :- async Gamma B P, async Gamma C Q.
async Gamma (all B) (eigen P)    :- pi x\ async Gamma (B x) (P x).
async Gamma (imp B C) Premises   :- async (B::Gamma) C Premises.
async Gamma (atm Atm) (one Gamma Atm).

% Proving (pr) is then achieved by repeatedly achieved by repeatedly 
% exploring the reduction of a sequent to possible premises.

pr Gamma Atm :- boundry Gamma Atm Premises, continue Premises.

continue none.
continue (pand P Q)      :- continue P, continue Q.
continue (eigen  P)      :- pi x\ continue (P x).
continue (one Gamma Atm) :- pr Gamma Atm.

% Example program

prog D :- program "of" D.

program "of" 
(all M\ all N\ all A\ all B\ (imp (and (atm (of M (arr A B))) (atm (of N A)))
                                  (atm (of (app M N) B)))).
program "of" 
 (all A\ all B\ all R\ (imp (all x\ (imp (atm (of x A)) (atm (of (R x) B))))
                                        (atm (of (abs R) (arr A B))))).
