:- use_module(claire).
:- use_module(fol).
:- use_module(env).
:- use_module(checker).
/*
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
*/
clairepl(Env) :- toplevel(Env,R),go(Env,R).

main :- current_prolog_flag(argv, []),
  writeln('========================='),
  writeln('=== Welcome to Claire ==='),
  writeln('========================='),nl,
  defEnv(Env),clairepl(Env).
main :-
  catch((
    current_prolog_flag(argv, [File|_]),
    read_file_to_terms(File,Ds,[]),
    (laire(Ds);writeln('syntax error'),halt),!,
    defEnv(Env),!,claire(Env,Ds,Env_),!,
    writeln('= Constants ='),
    member(types=Types,Env_),maplist(writeln,Types),
    writeln('= Proved Theorems ='),
    member(thms=Thms,Env_),maplist(writeln,Thms)
  ),Err,writeln(Err)).
:- main.
:- halt.
