:- module('lib/eqCommands',[]).

refl(_,t(T),_,[
  apply([cut(forall(r,eq*[r,r]))]),
  use(refl, [eq: ([x]=>eq*[x,x])]),
  apply([forallR(r)]),
  assumption*[],
  apply([forallL(T)]),
  assumption*[]
]).
refl(_,Arg,_,_) :- throw(wrongArgument(Arg)).

export_command([refl]).
export_decl([]).
