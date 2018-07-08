:- use_module(claire).
:- use_module(fol).
:- use_module(env).
:- use_module(checker).

main :-
  catch((
    current_prolog_flag(argv,[File|_]),
    read_file_to_terms(File,Ds,[]),
    (laire(Ds);writeln('syntax error'),halt),!,
    defEnv(Env),!,claire(Env,Ds,Env_),!,
    writeln('= Constants ='),
    member(types=Types,Env_),maplist(writeln,Types),
    writeln('= Proved Theorems ='),
    member(thms=Thms,Env_),maplist(writeln,Thms)
  ),Err,writeln(Err)).
main :- current_prolog_flag(argv,[]),
  writeln('========================='),
  writeln('=== Welcome to Claire ==='),
  writeln('========================='),nl,
  defEnv(Env),clairepl(Env).

clairepl(Env) :- toplevel(Env,Sus),!,clairepl1(Env,Sus).
clairepl1(_,(declAwait(Cont),Env)) :- safep('decl>',decl,Decl),call(Cont,Decl,Env,Sus),clairepl1(Env,Sus).
clairepl1(_,(proofNotFinished(Js,Cont),Env)) :-
  maplist(writeln,Js),
  safep('command>',[S,S]>>command(S),T),
  select(proof=Proof,Env,proof=Proof2,Env2),append(Proof,[T],Proof2),
  call(Cont,T,Env2,Sus),clairepl1(Env2,Sus).
clairepl1(_,(runCommandError(Idt,Err,Cont),Env_)) :-
  showDeclSuspender(runCommandError(Idt,Err,Cont),R),writeln(R),!,
  (member(proof=[],Env_),!,call(Cont,Env_,Sus),!,clairepl1(Env_,Sus);
    select(proof=Proof,Env_,proof=Proof2,Env2),init(Proof,Proof2),!,
    call(Cont,Env2,Sus),!,clairepl1(Env2,Sus)).
clairepl1(Env,(declError(Idt,Err,Cont),_)) :-
  format('~w: ~w\n',[Idt,Err]),!,call(Cont,Env,Sus),!,clairepl1(Env,Sus).
init([_],[]).
init([X|Xs],[X|Xs_]) :- init(Xs,Xs_).
safep(M,P,R) :- catch((prompt1(M),read(D),call(P,D,R)),Err,(writeln(Err),!,safep(M,P,R))).

:- main.
:- halt.
