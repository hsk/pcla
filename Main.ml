open Claire
open Env
open Checker

let clairepl env =
  let rec safep m p =
    try Printf.printf "%s%!" m; p(read_line())
    with err -> Printf.printf "%s\n" (Printexc.to_string err); safep m p
  in
  let rec go = function
    | DeclAwait cont,env -> go (cont (safep "decl>" Lexer.pDecl,env))
    | ProofNotFinished(js, cont),env' ->
      List.iter (fun j -> Printf.printf "%s\n" (LK.show_judgement j)) js;
      let (t,raw) = safep "command>" (fun s -> let s' = Lexer.pCommand s in (s',s)) in
      go (cont(t,{ env' with proof = env'.proof @ [t,raw] }))
    | (RunCommandError(idt, err, cont) as z),env' ->
      let rec init = function
        | [a] -> []
        | x::xs -> x::init xs
      in
      Printf.printf "%s\n" (showDeclSuspender z);
      if env'.proof = [] then go (cont env') else go (cont {env' with proof = init (env'.proof)})
    | DeclError(idt, err, cont),env' ->
      Printf.printf "%s: %s\n" idt (Printexc.to_string err);
      go (cont env)
  in
  go (toplevel env)

let _ =
  let env = {Env.defEnv with hs=M.fromList [
    "Commands.ml",(Commands.export_decl,Commands.export_command);
    "EqCommands.ml",(EqCommands.export_decl,EqCommands.export_command)]}
  in
  if Array.length Sys.argv != 2 then begin
    Printf.printf "=========================\n";
    Printf.printf "=== Welcome to Claire ===\n";
    Printf.printf "=========================\n";
    Printf.printf "\n";
    clairepl env
  end else begin
    let str = Lexer.readFile Sys.argv.(1) in
    let Laire ds = Lexer.pLaire str in
    let env = Checker.claire env ds in
    Printf.printf "= Constants =\n";
    List.iter (fun(k,v)->Printf.printf "(%S,%s)\n" k (FOL.show_type v)) (M.bindings env.types);
    Printf.printf "= Proved Theorems =\n";
    List.iter (fun(k,v)->Printf.printf "(%S,%s)\n" k (FOL.show_formula v)) (M.bindings env.thms)
  end
