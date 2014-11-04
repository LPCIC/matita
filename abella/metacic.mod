module metacic.

accumulate cic.

%%%%%%%%%%%%%%%%% <auxiliary predicates> %%%%%%%%%%%%%%
is_term set.
is_term (lam T F) :- is_term T, pi x\ is_term x => is_term (F x).
is_term (prod T F) :- is_term T, pi x\ is_term x => is_term (F x).
is_term (app L) :- list1 is_term L.
%%%%%%%%%%%%%%%%% </auxiliary predicates> %%%%%%%%%%%%%%

%of (#F L Seq) TY T :- T = @F L, of-seq Seq L TY.
of-seq (vdash TY) xnil TY.
of-seq (decl T Seq) (xcons V VS) TY :- of V T V, of-seq (Seq V) VS TY.
%of-seq (def T BO Seq) [V|VS] TY :- rof V T, unify V BO, of-seq (Seq BO) VS TY.
