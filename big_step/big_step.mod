module big_step.

%:aand:
aand F G :- F, G.

%:oor1:
oor F G :- F.
%:oor2:
oor F G :- G.

ttrue.

%:ssigma:
ssigma F :- F X.
