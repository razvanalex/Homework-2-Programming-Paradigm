% C = [[1, rosu], [2, negru], [3, albastru], [4, negru]]
% E = [[1, 2], [2, 3], [1, 3], [3, 4]]
% G = [[[1, rosu], [2, negru], [3, albastru], [4, negru]], [[1, 2], [2, 3], [1, 3], [3, 4]]]

% Testing values.
getColors(C) :- C = [[1, rosu], [2, negru], [3, albastru], [4, negru], [5, galben]].
getEdges(E) :- E = [[1,2], [2,3], [3,4], [4,5], [2,4], [1,4]].
getGraph(G) :- G = [C, E], getColors(C), getEdges(E).


% Formulae implementation
% F1 AND F2 implementation
and(F1, F2) :- F1, F2.

% F1 OR F2 implementation
or(F1, _) :- F1, !.
or(_, F2) :- F2.

% NOT F implementation
% not(F) :- F == false.

% LTL
% future(_).
% global(_).
% next(_).

% Evaluate LTL
evalLTL(_, valid, true) :- !.
evalLTL(Color, Color, true) :- !.
evalLTL(Color, and(F1, F2), and(R1, R2)) :- evalLTL(Color, F1, R1), R1, evalLTL(Color, F2, R2), !.
evalLTL(Color, or(F1, F2), or(R1, R2)) :- or(evalLTL(Color, F1, R1), evalLTL(Color, F2, R2)), !.
evalLTL(Color, not(F), not(R)) :- not(evalLTL(Color, F, R)), !.

% evalLTL(Color, future(Color), true).
% evalLTL(X, future(Y), future(Y)) :- X \= Y.

% evalLTL(Color, global(Color), global(Color)).
% evalLTL(X, global(Y), fail) :- X \= Y.

evalLTL(_, next(F2), F2) :- !.


% Member implementation
member(E, [E|_]).
member(E, [_|T]) :- member(E, T).

% Get node index from graph
getNode([], []) :- !.
getNode([[N, _] | T], [N | V]) :- getNode(T, V).

% Get node form graph
node(X, [V,_]) :- member(X, V).

% Get color of node
getColorOfNode(X, [[X, C] | _], C) :- !.
getColorOfNode(X, [[Y, _] | T], R) :- X \= Y, getColorOfNode(X, T, R).

% Append colors
appColors([], _, []) :- !.
appColors([X | T2], C, [[X, R2] | R]) :- getColorOfNode(X, C, R2), appColors(T2, C, R).

% Get adjacent edge
edge(X, Y, [_,E]) :- member([X,Y], E).

% Get all adjacent nodes
edgesAux(_, [], []) :- !.
edgesAux(X, [[X, Y] | T], [Y | List]) :- edgesAux(X, T, List), !.
edgesAux(X, [_ | T], List) :- edgesAux(X, T, List).
edges(X, [_, E], List) :- edgesAux(X, E, List).

% Get all edges nod visited
edgesNVAux(_, [], _, []) :- !.
edgesNVAux(X, [[X, Y]], Visited, [Y]) :- not(member(Y, Visited)), !.
edgesNVAux(X, [[X, Y] | T], Visited, [Y | List]) :- 
    not(member(Y, Visited)), edgesNVAux(X, T, Visited, List), !.
edgesNVAux(X, [_ | T], Visited, List) :- edgesNVAux(X, T, Visited, List).
edgesNotVisited(X, E, Visited, List) :- edgesNVAux(X, E, Visited, List), List \= [].

% Queue implementation.
% Insert element into a queue
insertQ(Queue, E, [E|Queue]).

% Extract element from a queue.
extractQ([], _, []) :- fail.
extractQ([H], H, []) :- !.
extractQ([H|T], E, [H|Q]) :- extractQ(T, E, Q).

% Add list to queue, in reverse order
addListToQ(Q, [], Q) :- !.
addListToQ(Q, [H | T], R) :- insertQ(Q, H, Q2), addListToQ(Q2, T, R).

% Add unique to list
addUnique(List, [], List) :- !.
addUnique(List, [H | T], R) :- member(H, List), addUnique(List, T, R), !.
addUnique(List, [H | T], R) :- member(H, T), addUnique(List, T, R), !.
addUnique(List, [H | T], [H | R]) :- addUnique(List, T, R), !.

% Add unique to queue, in the same order
addUniqueToQ(Q, L, R) :- addUnique(Q, L, R).

% Get size of a list
sizeOfList([], 0) :- !.
sizeOfList([_ | T], R) :- sizeOfList(T, N), R is N + 1.

% Create parents list
getParents([C, _], R) :- setParentsAux(C, 0, R).

% Set parents
setParentsAux([], _, []) :- !.
setParentsAux([H | T], Prt, [[H, Prt] | R]) :- setParentsAux(T, Prt, R).

changeParent([], _, []) :- !.
changeParent([[X, _] | T], [X, N], [[X, N] | R]) :- changeParent(T, [X, N], R), !.
changeParent([H | T], X, [H | R]) :- changeParent(T, X, R).

changeAllPrts(AllParents, [], AllParents) :- !.
changeAllPrts(AllParents, [H | T], R) :- 
    changeParent(AllParents, H, R1),
    changeAllPrts(R1, T, R).

setParents(AllParents, List, Prt, R) :- 
    setParentsAux(List, Prt, R1), 
    changeAllPrts(AllParents, R1, R).

% Extract path from parents
extractPathAux(_, Src, []) :-  Src is 0, !.
extractPathAux(Parents, Src, [Src | Path]) :- 
    edge(Src, Dest, [_, Parents]), 
    extractPathAux(Parents, Dest, Path), !.
extractPath(Parents, Dest, R) :- 
    extractPathAux(Parents, Dest, R1), 
    reverse(R1, R).

% Get shortest path, using BFS
getPathAux(Dest, _, Queue, _, Parents, Parents) :-
        extractQ(Queue, [X, C, F], _),
        evalLTL(C, F, valid),
        Dest = X, !.

getPathAux(Dest, _, Queue, _, Parents, Parents) :-
    extractQ(Queue, [X, C, F], _),
    evalLTL(C, F, true),
    Dest = X, !.

getPathAux(Dest, [V, E], Queue, Visited, Parents, PrtsRez) :-
    extractQ(Queue, H, Q),
    H = [Node, C, F],
    edgesNotVisited(Node, E, Visited, List),
    appColors(List, V, AppColorList),
    addUniqueToQ(Q, AppColorList, Q2),
    addUnique(Visited, List, NewVisited),
    setParents(Parents, List, Node, NewPrts),
    getPathAux(Dest, [V, E], Q2, NewVisited, NewPrts, PrtsRez), !.

getPathAux(Dest, G, Queue, Visited, Parents, PrtsRez) :-
    extractQ(Queue, _, Q),
    getPathAux(Dest, G, Q, Visited, Parents, PrtsRez), !.

bfs(Source, Dest, [C, E], Formulae, PrtsRez) :-
    getColorOfNode(Source, E, Color),
    Q = [[Source, Color, Formulae]],
    V = [Source],
    getNode(C, NewC),
    getParents([NewC, E], Parents),
    getPathAux(Dest, [C, E], Q, V, Parents, PrtsRez).

debugCode(P) :- getGraph(G), F = valid, bfs(1, 4, G, F, P).
%getGraph(G), Src = 5, Dst = 3, bfs(Src, Dst, G, P), extractPath(P,Dst, R).

getPath(From, To, Graph, Formulae, Path) :- 
    bfs(From, To, Graph, Formulae, Parents), 
    extractPath(Parents, To, Path).
