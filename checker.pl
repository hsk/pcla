:- module(checker,[claire/3]).
:- use_module(fol).
:- use_module(lk).
:- use_module(claire).
:- use_module(env).
:- use_module(typing).

commandM(_,[],(comReturn,[])) :- !.
commandM(Env,Js,(comAwait(Env,command1),Js)) :- !.
command1(Env,Js,apply(Rs),Sus) :-
  catch((!,judge(Rs,Js,Js_),!,commandM(Env, Js_,Sus)),
  goalError(R,Js2),Sus=(commandError(apply, cannotApply(R, Js2), commandM(Env)),Js)).
command1(Env,Js,noApply(R),Sus) :-
  catch((judge([R],Js,_),commandM(Env,Js,Sus)),
  goalError(R_,Js_),Sus=(commandError(noapply, cannotApply(R_, Js_), commandM(Env)),Js)).
command1(Env,Js,use(Idx),Sus) :- !,command1(Env,Js,use(Idx, []),Sus).
command1(Env,Js,use(Idx, Pairs),Sus) :-
  catch((member(thms=Thms,Env),member(Idx=F,Thms),
    foldl([(Idt:Pred),F1,Insts1]>>(
      format(atom(Idt1),'?~w',[Idt]),substPred(Idt1,Pred,F1,Insts1)
    ),Pairs,F,Insts),!,
    [(Assms⊦Props)|Js_]=Js,!,commandM(Env,[([Insts|Assms]⊦Props)|Js_],Sus)
  ),_,Sus=(commandError(use, noSuchTheorem(Idx), commandM(Env)),Js)).
command1(Env,[],inst(_, _),(commandError("inst","empty judgement", commandM(Env)),[])).
command1(Env,Js,inst(Idt, Pred),Sus) :-
  catch((Js=[([Assm|Assms]⊦Props)|Js_],
    format(atom(Idt1),'?~w',[Idt]),substPred(Idt1,Pred,Assm,Assm_),
    commandM(Env, [([Assm_|Assms]⊦Props)|Js_],Sus)),
  Err,Sus=(commandError("inst", cannotInstantiate(Err), commandM(Env)),Js)).
command1(Env,[J|Js],newCommand(defer, []),Sus) :- !,append(Js,[J],Js_),commandM(Env,Js_,Sus).
command1(Env,Js,newCommand(Com, Args),Sus) :-
  member(newcommands=Newcommands,Env),member(Com=Cmd,Newcommands),!,
  catch((call(Cmd,Env,Args,Js,Coms),!,commandM(Env,Js,Sus1),!,
         commandRun(Sus1,Coms,Js_),!,commandM(Env,Js_,Sus)),
  Err,Sus=(commandError(Com, Err, commandM(Env)),Js)).
command1(Env,Js,newCommand(Com,_),(commandError(Com, noSuchCommand, commandM(Env)),Js)).
commandRun((commandError(_, Exn, _),_),_,_) :- throw(Exn).
commandRun((comReturn,Js),_,Js).
commandRun((comAwait(_,_),Js),[],Js).
commandRun((comAwait(Env,Cont),Js),[C|Coms],Js_) :- !,call(Cont,Env,Js,C,Sus1),commandRun(Sus1,Coms,Js_).

% ---------------------------------------

toplevel(Env,(declAwait(toplevel1),Env)).
%toplevel1(D,_,_) :- writeln(toplevel1(D)),fail.
toplevel1(axiom(Idx,F),Env,Sus) :-
  !,catch((!,infer(Env,F),insertThm(Idx,F,Env,Env1),toplevel(Env1,Sus)),
  Err,Sus=(declError(typecheck,typeError(F,Err),toplevel),Env)).
toplevel1(theorem(Idx, F, proof(Coms)),Env,Sus) :- 
  !,catch((infer(Env, F),select(proof=_,Env,proof=[],Env_),
    newGoal(F,Js),!,commandM(Env_,Js,Sus1),!,toplevel1thm(Idx,F,Env,Sus1,Coms,Sus)
  ),Err,(declError("typecheck",typeError(F, Err),toplevel),Env)).
toplevel1(import(Path),Env,Sus) :- !,read_file_to_terms(Path,Ds,[]),!,claire(Env,Ds,Sus1),!,toplevel(Sus1,Sus),!.
toplevel1(constant(P,Typ),Env,Sus) :- !,select(types=Types,Env,types=[P=Typ|Types],Env_),toplevel(Env_,Sus).
toplevel1(printProof,Env,Sus) :- !,print_proof(Env,P),writeln(P),toplevel(Env,Sus).
toplevel1(plFile(Name),Env,Sus) :- !,catch((use_module(Name,[]),
  Name:export_command(Cs),Name:export_decl(Ds),
  maplist([A,A=(Name:A)]>>!,Ds,Ds_),maplist([A,A=(Name:A)]>>!,Cs,Cs_),
  select(newdecls=NDecl,Env,newdecls=NDecl2,Env2),union(NDecl,Ds_,NDecl2),
  select(newcommands=NComs,Env2,newcommands=NComs3,Env3),union(NComs,Cs_,NComs3),!,
  toplevel(Env3,Sus)
  ),_,Sus=(declError(plFile, plFileLoadError(Name), toplevel),Env)).
toplevel1(newDecl(Dec,Args),Env,Sus) :- !,member(newdecls=Decls,Env),member(Dec=Fun,Decls),
  toplevel(Env,Sus1),call(Fun,Args,Ds),declrunner(Sus1,Ds,Sus).
toplevel1(newDecl(Dec,_),Env,(declError(Dec, noSuchDecl(Dec), toplevel),Env)).

newGoal(F,[[]⊦[F]]).

declrunner((declAwait(_),Env),[],Sus) :- !,toplevel(Env,Sus),!.
declrunner((declAwait(Cont),Env),[D|Ds],Sus) :- call(Cont,D,Env,Sus1),!,declrunner(Sus1,Ds,Sus).
declrunner((Err,_),D,_) :- !,showDeclSuspender(Err,Err_),throw('declrunner error':Err_;D).

toplevel1thm(Idx,F,Env,(comReturn,_),_,Sus) :- !,insertThm(Idx,F,Env,Sus1),!,toplevel(Sus1,Sus).
toplevel1thm(Idx,F,Env,(commandError(Idt,Err,Cont),Js_),Coms,
  (runCommandError(Idt, Err, [_,Sus]>>(call(Cont,Js_,Sus1),toplevel1thm(Idx,F,Env,Sus1,Coms,Sus))),Env)).
toplevel1thm(Idx,F,Env,(comAwait(_,Cont),Js_),[],
  (proofNotFinished(Js_, [Com_,Env1,Sus]>>toplevel1thm(Idx,F,Env1,(comAwait(Env1,Cont),Js_),[Com_],Sus)),Env)).
toplevel1thm(Idx,F,Env,(comAwait(_,Cont),Js_),[Com|Coms],Sus) :-
  !,call(Cont,Env,Js_,Com,Sus1),!,toplevel1thm(Idx,F,Env,Sus1,Coms,Sus).

claire(Env,Decls,R) :- toplevel(Env,R1),!,claire1(R1,Decls,R).
claire1((declAwait(_),Env),[],Env) :- !.
claire1((declAwait(Cont),Env),[D|Ds],R) :- !,call(Cont,D,Env,R1),!,claire1(R1,Ds,R). 
claire1((Z,Env),_,Env) :- showDeclSuspender(Z,Z_),!,writeln(Z_).

% ---------------------------------------

showJudge(Assms ⊦ Prop,J_) :- reverse(Assms,Assms_),format(atom(J_),'\n  ~w',[Assms_⊦Prop]).
showDeclSuspender(declAwait(_),declAwait).
showDeclSuspender(proofNotFinished(Js, _),proofNotFinished:Js_) :- maplist(showJudge,Js,Js_).
showDeclSuspender(runCommandError(Idt,Err,_),runCommandError(Err):Idt).
showDeclSuspender(declError(I,Err,_),declError(Err):I).
