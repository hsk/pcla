:- module('lib/eqCommands',[]).

refl(_,t(T),_,[
  apply([cut(forall(r,eq*[*r,*r]))]),
  use(refl, [eq: predFun([x], predFml(eq*[*x,*x]))]),
  apply([forallR(r)]),
  com(assumption, []),
  apply([forallL(T)]),
  com(assumption, [])
]).
refl(_,Arg,_,_) :- throw(wrongArgument(Arg)).

export_command([refl]).
export_decl([]).
