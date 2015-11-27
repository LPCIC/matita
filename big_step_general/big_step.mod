module big_step.

%:aand:
to_fla (aand F1 F2) :- to_fla F1, to_fla F2.
%:oor1:
to_fla (oor F1 F2) :- to_fla F1.
%:oor2:
to_fla (oor F1 F2) :- to_fla F2.
to_fla ttrue.
%:ssigma:
to_fla (ssigma F) :- to_fla (F X).
%:iimp:
to_fla (iimp F1 F2) :- (to_fla F1) => (to_fla F2).
%:ppi:
to_fla (ppi F) :- pi x\ (to_fla (F x)).


