:- module('lib/eqCommands',[]).
:- use_module(fol).
:- use_module(lk).
:- use_module(claire).
:- use_module(env).

refl(_,_,_,_).
/*
let refl : env -> argument -> judgement list -> command list =
  fun env arg js -> match arg with
  | ArgTerms [t] -> 
    [ Apply [Cut(pFormula "Forall r. eq(r,r)")];
      Use("refl", ["eq", PredFun(["x"], PredFml(pFormula "eq(x,x)"))]);
      Apply [ForallR "r"];
      NewCommand("assumption", ArgEmpty);
      Apply [ForallL t];
      NewCommand("assumption", ArgEmpty);
    ]
  | arg -> raise (WrongArgument arg)
*/
export_command([refl]).
export_decl([]).
