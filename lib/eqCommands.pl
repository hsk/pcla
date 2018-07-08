:- module('lib/eqCommands',[]).
:- use_module(fol).
:- use_module(lk).
:- use_module(claire).
:- use_module(env).

refl(_,t(T),_,[
  apply([cut(forall(r,pred(eq,[!r,!r])))]),
  use(refl, [eq: predFun([x], predFml(pred(eq,[!x,!x])))]),
  apply([forallR(r)]),
  newCommand(assumption, []),
  apply([forallL(T)]),
  newCommand(assumption, [])
]).
refl(_,Arg,_,_) :- throw(wrongArgument(Arg)).

export_command([refl]).
export_decl([]).
