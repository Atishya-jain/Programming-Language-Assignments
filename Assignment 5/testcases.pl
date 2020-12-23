hastype(t,234,W).
hastype(t,true,W).
hastype(t,false,W).

lookup([(variable(x),intT)],variable(x),W) :- !.

hastype([(variable(y),boolT),(variable(x),intT)],absolute(variable(x)),W).

hastype([p(variable(x),boolT)], abstr(variable(x),plus(const(5),variable(x))),T).
