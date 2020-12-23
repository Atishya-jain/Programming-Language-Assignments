edge(1,2).
edge(2,3).
edge(3,4).
edge(3,5).
path(X,X).
path(X,Y) :- edge(X,Z), path(Z,Y), !.

%% teaches(dr_fred, history).
%% teaches(dr_fred, english).
%% teaches(dr_fred, drama).
%% teaches(dr_fiona, physics).
%% studies(alice, english).
%% studies(angus, english).
%% studies(amelia, drama).
%% studies(alex, physics).