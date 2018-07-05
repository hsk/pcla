open FOL
open LK
open Claire
open Env
open Lexer

exception WrongArgument of argument

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

let export_command = [ "refl", refl ]
let export_decl    = []
