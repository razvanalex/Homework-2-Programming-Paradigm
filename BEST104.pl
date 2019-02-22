% C = [[1, rosu], [2, negru], [3, albastru], [4, negru]]
% E = [[1, 2], [2, 3], [1, 3], [3, 4]]
% G = [[[1, rosu], [2, negru], [3, albastru], [4, negru]], [[1, 2], [2, 3], [1, 3], [3, 4]]]

% Testing values.
getColors(C) :- C = [[1, r], [2, r], [3, r], [4, r]].
getEdges(E) :- E = [[1, 2], [2, 3], [1, 3], [3, 4]].
getGraph(G) :- G = [C, E], getColors(C), getEdges(E).

% F1 AND F2 implementation
% and(valid, valid) :- !.
and(F1, F2) :- F1, F2.

% F1 OR F2 implementation
% or(valid, _) :- !.
% or(_, valid) :- !.
or(F1, _) :- F1, !.
or(_, F2) :- F2.

% NOT F implementation
% not(F) :- F == false.

% Member implementation
member(E, [E|_]).
member(E, [_|T]) :- member(E, T).

% Get node index from graph
getNode([], []) :- !.
getNode([[N, _] | T], [N | V]) :- getNode(T, V).

% Get node form graph
node(X, [V,_]) :- member(X, V).

% Get adjacent edge
edge(X, Y, [_,E]) :- member([X,Y], E).

% Get all adjacent nodes
edgesAux(_, [], []) :- !.
edgesAux(X, [[X, Y] | T], [Y | List]) :- edgesAux(X, T, List), !.
edgesAux(X, [_ | T], List) :- edgesAux(X, T, List).

nodeColor(X, [[X, C] | _], [X, C]) :- !.
nodeColor(X, [_ | T], R) :- nodeColor(X, T, R).

allNodesColor([], _, []).
allNodesColor([H | T], C, [R1 | R2]) :- nodeColor(H, C, R1), allNodesColor(T, C, R2).

edges(X, [C, E], R) :- edgesAux(X, E, List), allNodesColor(List, C, R).

% Get all edges nod visited
edgesNVAux(_, [], _, []) :- !.
edgesNVAux(X, [[X, Y]], Visited, [Y]) :- not(member(Y, Visited)), !.
edgesNVAux(X, [[X, Y] | T], Visited, [Y | List]) :- not(member(Y, Visited)), edgesNVAux(X, T, Visited, List), !.
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


% Valid is always true
satFormula(valid, _, valid) :- !.
satFormula(and(valid, valid), _, valid) :- !.
satFormula(or(valid, _), _, valid) :- !.
satFormula(or(_, valid), _, valid) :- !.
satFormula(not(valid), _, fail) :- !.

satFormula(fail, _, fail) :- !.
satFormula(and(fail, _), _, fail) :- !.
satFormula(and(_, fail), _, fail) :- !.
satFormula(or(fail, fail), _, fail) :- !.
satFormula(not(fail), _, valid) :- !.

% Atom satisfaction
satFormula(Color, Color, valid) :- !.

% Next satisfaction
satFormula(next(F), _, F) :- !.

% Future satisfaction F Φ ≡ Φ ∨ X(F Φ)
satFormula(future(F), Color, NewF) :- 
    satFormula(or(F, next(future(F))), Color, NewF), !.

% Global satisfaction G Φ ≡ Φ ∧ X(G Φ)
satFormula(global(F), Color, NewF) :- 
    satFormula(and(F, next(global(F))), Color, NewF), !.

% Weak Until satisfaction φ W ψ ≡ ψ ∨ (φ ∧ X(φ W ψ)) 
satFormula(until(C1, C2), Color, NewF) :- 
    satFormula(or(C2, and(C1, next(until(C1, C2)))), Color, NewF), !.

% And satisfaction
satFormula(and(Color, F), Color, NewF) :-
    satFormula(F, Color, NewF), !.

satFormula(and(F, Color), Color, NewF) :-
    satFormula(F, Color, NewF), !.

satFormula(and(F1, F2), Color, NewF) :-
    satFormula(F1, Color, NewF1),
    satFormula(F2, Color, NewF2),
    (NewF1 = NewF2, satFormula(NewF2, Color, NewF);
    NewF1 = fail, NewF = fail;
    NewF2 = fail, NewF = fail;
    NewF1 = valid, NewF = NewF2;
    NewF2 = valid, NewF = NewF1;
    and(NewF1, NewF2) = and(F1, F2), NewF = and(F1, F2); 
    F1 = next(_), F2 = next(_), NewF = and(NewF1, NewF2);
    F1 = next(_), NewF = and(NewF1, NewF2);
    F2 = next(_), NewF = and(NewF1, NewF2);
    satFormula(and(NewF1, NewF2), Color, NewF)), !.

% Or satisfaction
satFormula(or(Color, _), Color, valid) :- !.
satFormula(or(_, Color), Color, valid) :- !.
satFormula(or(F1, F2), Color, NewF) :-
    satFormula(F1, Color, NewF1),
    satFormula(F2, Color, NewF2),
    (NewF1 = NewF2, satFormula(NewF2, Color, NewF);
    NewF1 = valid, NewF = valid;
    NewF2 = valid, NewF = valid;
    NewF1 = fail, NewF = NewF2;
    NewF2 = fail, NewF = NewF1;
    or(NewF1, NewF2) = or(F1, F2), NewF = or(F1, F2);
    F1 = next(_), F2 = next(_), NewF = or(NewF1, NewF2);
    F1 = next(_), NewF = or(NewF1, NewF2);
    F2 = next(_), NewF = or(NewF1, NewF2);
    satFormula(or(NewF1, NewF2), Color, NewF)), !.

% Not satisfaction
satFormula(not(F), Color, NewF) :- 
    satFormula(F, Color, R),
    satFormula(not(R), Color, NewF), !.

% Cannot unify, the R = fail.
satFormula(_, _, fail) :- !.



% fdf
addNodeToPath(Pair, Node, Rez) :-
    Pair = [Path, Formula],
    Node = [Vertex, Color],
    satFormula(Formula, Color, NewF),
    NewF \= fail,
    not(member(Vertex, Path)),
    NewPath = [Vertex | Path],
    Rez = [NewPath, NewF], !.

% daca nu poate pune in path, da fail
% apel: createNewPaths(Pair|Formula, ListAdj, Rez).
createNewPaths(_, [], []) :- !.
createNewPaths(Pair, [H | T], [R | Rez]) :- 
    addNodeToPath(Pair, H, R), 
    createNewPaths(Pair, T, Rez), !.
createNewPaths(Pair, [_ | T], Rez) :- 
    createNewPaths(Pair, T, Rez).

% Get shortest path, using BFS
% todo: until(color, _).
getPathAux(Dest, _, Queue, [H | T]) :-
    extractQ(Queue, Head, _),
    Head = [[H | T], Formula],
    (Formula = valid; Formula = global(_); Formula = until(_, _)),
    Dest = H, !.

getPathAux(Dest, G, Queue, Path) :-
    extractQ(Queue, Head, Q),
    Head = [[H | _], _],
    edges(H, G, Neighbors),
    createNewPaths(Head, Neighbors, R),
    addUniqueToQ(Q, R, Q2),
    getPathAux(Dest, G, Q2, Path), !.

getPathAux(Dest, G, Queue, Path) :-
    extractQ(Queue, _, Q),
    getPathAux(Dest, G, Q, Path), !.

bfs(Source, Dest, [C, E], Formula, Path) :-
    nodeColor(Source, C, [Source, NodeCol]),
    satFormula(Formula, NodeCol, NewF),
    Q = [[[Source], NewF]],
    getPathAux(Dest, [C, E], Q, AuxPath),
    reverse(AuxPath, Path).


% bfs(Source, Dest, [C, E], Formula, Paths) :-
    % Q = [Source],
    % V = [Source],
    % getNode(C, NewC),
    % getParents([NewC, E], Parents),
    % getPathAux(Dest, [C, E], Q, V, Parents, PrtsRez).
    % Q = [[Source, Formula]],
    % getNode(C, NewC).
    % getPathAux(Dest, [C, E], Q, V, Parents, Paths).

% getPath(From, To, Graph, Formula, Path) :- 
%     bfs(From, To, Graph, P), extractPath(P, To, Path).

% getGraph(G), Src = 5, Dst = 3, bfs(Src, Dst, G, P), extractPath(P,Dst, R).

% debugCode(R) :- getGraph(G), Q = [[[1], and(negru, next(albastru))]], getPathAux(3, G, Q, R).
% getGraph(G), Src = 5, Dst = 3, bfs(Src, Dst, G, P), extractPath(P,Dst, R).

getPath(From, To, Graph, Formula, Path) :- 
    bfs(From, To, Graph, Formula, Path).

% debugCode(R) :- 
%     getGraph(G), 
%     Src = 1, 
%     Dst = 4, 
%     F = global(r), 
%     bfs(Src, Dst, G, F, R).


% debugCode(NewF) :- 
%     satFormula(and(n, and(next(r), and(next(next(g)), next(next(next(v)))))), n, NewF).