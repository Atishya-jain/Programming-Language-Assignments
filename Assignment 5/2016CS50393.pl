append([],X,X).
append([X|Xs],Y,[X|L3]) :- append(Xs,Y,L3).

lookup([], variable(X), T) :- !,fail.
lookup([p(variable(X),T1)|Gamma], variable(X), T1) :- !.
lookup([p(variable(Y),T1)|Gamma], variable(X), T) :- lookup(Gamma, variable(X), T).

hastype(Gamma, const(X), constT).
hastype(Gamma, bool(X), boolT).
hastype(Gamma, variable(X), T) :- lookup(Gamma, variable(X), T).
hastype(Gamma, abs(X), constT) :- hastype(Gamma, X, constT).
hastype(Gamma, mod(X,Y), constT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, pow(X,Y), constT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, plus(X,Y), constT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, sub(X,Y), constT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, mul(X,Y), constT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, div(X,Y), constT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, andx(X,Y), boolT) :- hastype(Gamma, X, boolT), hastype(Gamma, Y, boolT).
hastype(Gamma, orx(X,Y), boolT) :- hastype(Gamma, X, boolT), hastype(Gamma, Y, boolT).
hastype(Gamma, notx(X), boolT) :-  hastype(Gamma, X, boolT).
hastype(Gamma, grt(X,Y), boolT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, lst(X,Y), boolT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, grtEq(X,Y), boolT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, lstEq(X,Y), boolT) :- hastype(Gamma, X, constT), hastype(Gamma, Y, constT).
hastype(Gamma, implies(X,Y), boolT) :- hastype(Gamma, X, boolT), hastype(Gamma, Y, boolT).
hastype(Gamma, equ(X,Y), T) :- hastype(Gamma, X, T), hastype(Gamma, Y, T).
hastype(Gamma, ite(X,Y,Z), T) :- hastype(Gamma, X, boolT), hastype(Gamma, Y, T), hastype(Gamma, Z, T).
hastype(Gamma, abstr(variable(X), E1), arrowT(T1,T2)) :- hastype([p(variable(X),T1) | Gamma], E1, T2).
hastype(Gamma, func(E1, E2), T) :- hastype(Gamma, E2, T1), hastype(Gamma, E1, arrowT(T1,T)).
hastype(Gamma, pair(E1,E2), crossT(T1, T2)) :- hastype(Gamma, E1, T1), hastype(Gamma, E2, T2).
hastype(Gamma, letIn(D,E), T) :- typeElaborates(Gamma, D, T1), hastype(T1, E, T).
hastype(Gamma, tuple([]), tupleT([])) :- !.
hastype(Gamma, tuple([X|Xs]), tupleT(T)) :- hastype(Gamma, X, T1), hastype(Gamma, tuple(Xs), tupleT(T2)), append([T1], T2, T).
hastype(Gamma, proj(tuple([X|Xs]),const(0)), T) :- hastype(Gamma, X, T),!.
hastype(Gamma, proj(tuple([X|Xs]),const(Y)), T) :- Y1 is Y-1, hastype(Gamma, proj(tuple(Xs), const(Y1)), T).

typeElaborates(Gamma, def(variable(X),E), [p(variable(X), T)]) :- hastype(Gamma, E, T).
typeElaborates(Gamma, seriesDef(D1,D2), T) :- typeElaborates(Gamma, D1, T1), append(T1,Gamma,A), typeElaborates(A, D2, T2), append(T2, T1, T).
typeElaborates(Gamma, parallelDef(D1,D2), T) :- typeElaborates(Gamma, D1, T1), typeElaborates(Gamma, D2, T2), append(T1, T2, T).
typeElaborates(Gamma, localDef(D1,D2), T) :- typeElaborates(Gamma, D1, T1), append(T1, Gamma, T2), typeElaborates(T2, D2, T).


%%hastype([], func(abstr(variable(X),plus(const(5),variable(X))), const(5)),T).
%%hastype([],ite(bool(5), const(5), const(7)),T).
%%typeElaborates([],def(variable(X), const(5)), T).
%%typeElaborates([],seriesDef(def(variable(X), const(5)), def(variable(Y), plus(const(5), const(6)))), T).
%%typeElaborates([],seriesDef(def(variable(X), const(5)), def(variable(X), andx(bool(5), bool(6)))), T).
%%typeElaborates([],localDef(def(variable(X), const(5)), def(variable(Y), andx(bool(5), bool(6)))), T).
%%hastype([], letIn(def(variable(X), bool(true)), notx(variable(X))), T).
%%hastype([], proj(tuple([const(1), bool(true), notx(bool(true)), plus(const(5), const(8))]), const(2)), T).
%% hastype([], tuple([const(1), bool(true), notx(bool(true)), plus(const(5), const(8))]), T).
%% hastype([p(variable(y),boolT),p(variable(x),constT)],equ(bool(true),bool(false)),W).
%% hastype([p(variable(y),boolT),p(variable(x),constT)],tuple([bool(true),bool(false),const(23),variable(y),variable(x)]),W).
%% hastype([],letIn( localDef( def(variable(y),bool(true)),def(variable(x),andx(variable(y),bool(false))) ),andx(variable(x),variable(x))),W).

%% Counter example for last one -> hastype([], variable(x), T). will return false. that means a variable has to be declared with its type and can't be worked with any type.