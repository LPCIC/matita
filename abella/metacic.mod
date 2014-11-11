module metacic.

accumulate cic.

%of (#F L Seq) TY T :- T = @F L, of-seq Seq L TY.
of-seq (vdash TY) xnil TY.
of-seq (decl T Seq) (xcons V VS) TY :- of V T V, of-seq (Seq V) VS TY.
%of-seq (def T BO Seq) [V|VS] TY :- rof V T, unify V BO, of-seq (Seq BO) VS TY.
