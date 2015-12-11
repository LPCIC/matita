module big_step.

%:aand:
fla_to_o (aand F1 F2) :- fla_to_o F1, fla_to_o F2.
%:oor1:
fla_to_o (oor F1 F2) :- fla_to_o F1.
%:oor2:
fla_to_o (oor F1 F2) :- fla_to_o F2.
fla_to_o ttrue.
%:ssigma:
fla_to_o (ssigma F) :- fla_to_o (F X).
%:iimp:
fla_to_o (iimp F1 F2) :- (fla_to_o F1) => (fla_to_o F2).
%:ppi:
fla_to_o (ppi F) :- pi x\ (fla_to_o (F x)).


