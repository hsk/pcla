:- module('lib/commands',[]).

replicate(0,_,[]).
replicate(N,V,[V|Vs]) :- N1 is N - 1, replicate(N1,V,Vs).
findIndex(F,Ls,R) :- findIndex1(F,0,Ls,R).
findIndex1(F,N,[X|_],N) :- call(F,X),!.
findIndex1(F,N,[_|Xs],R) :- N1 is N + 1, findIndex1(F,N1,Xs,R).
elemIndex(E,Ls,R) :- findIndex(=(E),Ls,R).
onlyL(I,N,Rs) :-
  replicate(I,[wL],R1),NI1 is N-I-1,replicate(NI1,[pL(1),wL],R2),append(R1,R2,R3),append(R3,Rs).
onlyR(I,N,Rs) :-
  replicate(I,[wR],R1),NI1 is N-I-1,replicate(NI1,[pR(1),wR],R2),append(R1,R2,R3),append(R3,Rs).
assumption(_,[],[(Assms⊦Props)|_],[apply(Rs)]) :-
  findIndex([A]>>member(A,Assms),Props,I),!,
  nth0(I,Props,I2),elemIndex(I2,Assms,J),!,
  length(Props,Pi),length(Assms,Aj),
  onlyR(I,Pi,Ps),onlyL(J,Aj,As),append([Ps,As,[i]],Rs).
assumption(_,[],[(Assms⊦Props)|Js],_) :- throw(cannotSolve([(Assms⊦Props)|Js])).
assumption(_,_,_,_) :- throw(wrongArgument([])).
implyR(Env,i([(I,Ps)]),Js,[use(I, Ps)| Cs1]) :- implyR(Env,[],Js,Cs1).
implyR(_,[],_,
    [ apply([impL]),defer*[],assumption*[],apply([pR(1), wR])]) :- !.
implyR(_,Arg,_,_) :- throw(wrongArgument(Arg)).
implyL(Env,i([(I,Ps)]),Js,[use(I,Ps)|Cs]) :- implyL(Env,[],Js,Cs).
implyL(_,[],_,[apply([impL]),assumption*[],apply([pL(1),wL])]).
implyL(_,Arg,_,_) :- throw(wrongArgument(Arg)).
genR(_,i([(I,[])]),[_ ⊦ [P|_] |_],[
  apply([cut(forall(I, P))]),
  defer*[],
  apply([forallL(I)]),
  assumption*[],
  apply([pR(1), wR])
]) :- !.
genR(_,Arg,Js,_) :- throw(wrongArgument(Arg,Js)).
genL(_,i([(I,[])]),[[P|Ps] ⊦ _ |_],[
  apply([cut(forall(I, P))]),
  apply([forallR(I)]),
  assumption*[],
  apply([pL(PLen), wL])
]) :- length(Ps,PLen).
genL(_,Arg,_,_) :- throw(wrongArgument(Arg)).
absL(_,[],[[A|_] ⊦ [B|_]|_],[
  apply([cut(A==>B)]),
  defer*[],
  apply([impL]),
  assumption*[],
  assumption*[],
  apply([pR(1),wR, wL])
]).
absL(_,Arg,Js,_) :- throw(wrongArgument(Arg,Js)).

export_command([assumption,implyR,implyL,genR,genL,absL]).

/* --------------------------------------------- */

definition([n(I:Typ),p([Body])],[constant(I,Typ),axiom(I2,Body)]) :- format(atom(I2),'~w_def',[I]).
definition(Arg,_) :- throw(wrongArgument(Arg)).

export_decl([definition]).
