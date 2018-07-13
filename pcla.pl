:- module(pcla,[]).
:- expects_dialect(sicstus),bb_put(cnt,0).
:- op(1200,xfx,⊦), op(650,xfy,[==>,$]), op(10,fx,[*,fun]).

{A} :- call(A).

main :- current_prolog_flag(argv,[File|_]),read_file_to_terms(File,Ds,[]),!,
   declRun(env{thms:[],types:[],proof:[],coms:[],decls:[]},Ds,G),!,
   writeln('= Constants ='),maplist(writeln,G.types),
   writeln('= Proved Theorems ='),maplist(writeln,G.thms).

% rule
%ruleRun(Rs,Js,_) :- writeln(ruleRun(Rs;Js)),fail.
ruleRun([],J,J).
ruleRun([R1|R],J,J_) :- rule(R1,J,J1),ruleRun(R,J1,J_).
ruleRun([R|_],J,_) :- cannotApply(R,J).
rule(i,[A⊦A|J],J).
rule(cut(F),[A⊦P|J],[A⊦[F|P],[F|A]⊦P|J]).
rule(andL1,[[and(F,_)|A]⊦P|J],[[F|A]⊦P|J]).
rule(andL2,[[and(_,F)|A]⊦P|J],[[F|A]⊦P|J]).
rule(andR,[A⊦[and(F1,F2)|P]|J],[A⊦[F1|P],A⊦[F2|P]|J]).
rule(orL,[[or(F1,F2)|A]⊦P|J],[[F1|A]⊦P,[F2|A]⊦P|J]).
rule(orR1,[A⊦[or(F,_)|P]|J],[A⊦[F|P]|J]).
rule(orR2,[A⊦[or(_,F)|P]|J],[A⊦[F|P]|J]).
rule(impL,[[F1==>F2|A]⊦P|J],[A⊦[F1|P],[F2|A]⊦P|J]).
rule(impR,[A⊦[F1==>F2|P]|J],[[F1|A]⊦[F2|P]|J]).
rule(bottomL,[[bottom|_]⊦_|J],J).
rule(topR,[_⊦[top|_]|J],J).
rule(forallL(T),[[forall(X,F)|A]⊦P|J],[[F_|A]⊦P|J]) :- substFormula(X,T,F,F_).
rule(forallR(Y),[A⊦[forall(X,F)|P]|J],[A⊦[F_|P]|J]) :- substFormula(X,*Y,F,F_).
rule(existL(Y),[[exist(X,F)|A]⊦P|J],[[F_|A]⊦P|J]) :- substFormula(X,*Y,F,F_).
rule(existR(T),[A⊦[exist(X,F)|P]|J],[A⊦[F_|P]|J]) :- substFormula(X,T,F,F_).
rule(wL,[[_|A]⊦P|J],[A⊦P|J]).
rule(wR,[A⊦[_|P]|J],[A⊦P|J]).
rule(cL,[[F|A]⊦P|J],[[F,F|A]⊦P|J]).
rule(cR,[A⊦[F|P]|J],[A⊦[F,F|P]|J]).
rule(pL(K),[A⊦P|J],[[Ak|K_]⊦P|J]) :- length(A,L),K<L,nth0(K,A,Ak,K_).
rule(pR(K),[A⊦P|J],[A⊦[Pk|P_]|J]) :- length(P,L),K<L,nth0(K,P,Pk,P_).

substTerm(I,T,*I,T) :- !.
substTerm(I,T,fun Is->E,fun Is->E_) :- \+member(I,Is),!,substTerm(I,T,E,E_).
substTerm(I,T,E1$E2,E1_$E2_) :- !,maplist(substTerm(I,T),[E1|E2],[E1_|E2_]).
substTerm(_,_,T,T).

substFormula(I,T,P*Es,P*Es_) :- !,maplist(substTerm(I,T),Es,Es_).
substFormula(I,T,forall(X,F),forall(X,F_)) :- !,substFormula(I,T,F,F_).
substFormula(I,T,exist(X,F),exist(X,F_)) :- !,substFormula(I,T,F,F_).
substFormula(I,T,F,F_) :- F=..[Op,F1,F2],!,maplist(substFormula(I,T),[F1,F2],Fs),F_=..[Op|Fs].
substFormula(_,_,F,F).

substPred(I,P,I*Ts,F_) :- !,beta(Ts,P,F_).
substPred(I,P,forall(V,F),forall(V,F_)) :- !,substPred(I,P,F,F_).
substPred(I,P,exist(V,F),exist(V,F_)) :- !,substPred(I,P,F,F_).
substPred(I,P,F,F_) :- F=..[Op,F1,F2],!,maplist(substPred(I,P),[F1,F2],Fs),F_=..[Op|Fs].
substPred(_,_,Pred,Pred) :- !.
beta(Xs,predFun([],P),F_) :- beta(Xs,P,F_).
beta([],predFun(Z,P),_) :- throw(argumentsNotFullyApplied(predFun(Z,P))).
beta([X|Xs],predFun([T|Ts],F),F_) :- sbterm(T,X,F,F1),beta(Xs,predFun(Ts,F1),F_).
beta([],predFml(F),F).
beta(Xs,predFml(F)) :- throw(cannotApplyToFormula(Xs,F)).
sbterm(T,X,predFun(Ys,F),predFun(Ys,F_)) :- sbterm(T,X,F,F_).
sbterm(T,X,predFml(F),predFml(F_)) :- substFormula(T,X,F,F_).

% command

comRun((_,[]),     _,[]).
comRun((_,J),     [], J).
comRun((G,J_),[C|Cs], J) :- !,com(C,G,J_,R),comRun(R,Cs,J).
comRun(E,          _, _) :- throw(E).
proofRun((G,[]),    _,N,R) :- !,call(N,G,R),!.
proofRun((_,J),    [],_,R) :- !,R=proofNotFinished(J).
proofRun((G,J),[C|Cs],N,R) :- !,com(C,G,J,R1),!,proofRun(R1,Cs,N,R).
proofRun(Err,       _,_,R) :- !,R=Err.
com(apply(Rs)    ,G,J,R) :- ruleRun(Rs,J,J_),is_list(J_),!,R=(G,J_).
com(apply(Rs)    ,_,J,R) :- ruleRun(Rs,J,E),!,R=comError(apply,E,J).
com(noApply(R1)  ,G,J,R) :- ruleRun([R1],J,J_),is_list(J_),!,R=(G,J).
com(noApply(R1)  ,_,J,R) :- ruleRun([R1],J,E),!,R=comError(noapply,E,J).
com(use(I)       ,G,J,R) :- !,com(use(I, []),G,J,R).
com(use(I,Pairs) ,G,J,R) :- member(I=F,G.thms),
                            !,catch({
                              foldl([Idt:Pred,F1,Insts1]>>(
                                format(atom(Idt1),'?~w',[Idt]),substPred(Idt1,Pred,F1,Insts1)
                              ),Pairs,F,Insts),!,
                              [(Assms⊦Props)|J_]=J,!,R=(G,[[Insts|Assms]⊦Props|J_])
                            },Err,{R=comError(use,cannotUse(I,Pairs,Err),J)}).
com(use(I,_)     ,_,J,R) :- !,R=comError(use, noSuchTheorem(I),J).
com(inst(I,Pred), G,J,R) :- J=[[Assm|Assms]⊦Props|J_],
                            !,catch({
                              format(atom(I1),'?~w',[I]),substPred(I1,Pred,Assm,Assm_),
                              R=(G,[[Assm_|Assms]⊦Props|J_])
                            },Err,{R=comError(inst, cannotInstantiate(Err),J)}).
com(inst(_,_)    ,_,J,R) :- !,R=comError(inst,'empty judgement',J).
com(com(defer,[]),G,J,R) :- !,J=[J1|J_],append(J_,[J1],J_2),R=(G,J_2).
com(com(Com,Args),G,J,R) :- member(Com=Cmd,G.coms),
                            !,catch({
                              call(Cmd,G,Args,J,Cs),!,comRun((G,J),Cs,J_),!,R=(G,J_)
                            },E,{
                              E=comError(_,Err,_)->R=comError(Com,Err,J);
                              true               ->R=comError(Com,E,J)
                            }).
com(com(Com,_)   ,_,J,R) :- R=comError(Com, noSuchCom(Com),J).

% decl
%decl(D,_,_) :- writeln(decl(D)),fail.
declRun(G,     [],G) :- is_dict(G).
declRun(G, [D|Ds],R) :- is_dict(G),decl(D,G,R1),!,declRun(R1,Ds,R).
declRun(E,      D,_) :- writeln('decl error':E;D),halt(1).
decl(import(Path),    G,R) :- !,read_file_to_terms(Path,Ds,[]),!,declRun(G,Ds,R),!.
decl(constant(P,Typ), G,R) :- !,R=G.put(types,[P=Typ|G.types]).
decl(axiom(Idx,F),    G,R) :- !,catch({
                                infer(G,F),!,insertThm(Idx,F,G,R)
                              },Err,{R=error(axiom,typeError(F,Err))}).
decl(theorem(Idx,F,P),G,R) :- !,catch({ P=proof(Cs),
                                infer(G,F),!,G_=G.put(proof,[]),!,
                                proofRun((G_,[[]⊦[F]]),Cs,insertThm(Idx,F),R)
                              },Err,{R=error(theorem,typeError(F,Err))}).
decl(plFile(N),    G,R) :- !,catch({
                                use_module(N,[]),N:export_command(Cs),N:export_decl(Ds),
                                maplist([P,P=(N:P)]>>!,Ds,Ds_),maplist([P,P=(N:P)]>>!,Cs,Cs_),
                                union(G.decls,Ds_,Decl2),union(G.coms,Cs_,Coms3),
                                R=G.put(decls,Decl2).put(coms,Coms3)
                              },_,{R=error(plFile, plFileLoadError(N))}).
decl(newDecl(Dec,Arg),G,R) :- member(Dec=Fun,G.decls),!,
                              call(Fun,Arg,Ds),declRun(G,Ds,R).
decl(newDecl(Dec,_),  _,R) :- !,R=error(Dec,noSuchDecl(Dec)).

insertThm(Idx,F,G,G_) :-  metagen(G.types,F,F_),G_=G.put(thms,[Idx=F_|G.thms]).
metagen(E,P*Es,P*Es) :- member(P=_,E).
metagen(_,P*Es,P_*Es) :- format(atom(P_),'?~w',[P]).
metagen(_,top,top).
metagen(_,bottom,bottom).
metagen(E,and(F1,F2),and(F1_,F2_)) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
metagen(E,or(F1,F2),or(F1_,F2_)) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
metagen(E,F1==>F2,F1_==>F2_) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
metagen(E,forall(V,F),forall(V,F_)) :- metagen(E,F,F_).
metagen(E,exist(V,F),exist(V,F_)) :- metagen(E,F,F_).



% typing
newVarT(varT(C1)) :- bb_get(cnt,C),C1 is C + 1,bb_put(cnt,C1).

infer(G,F) :- bb_put(ctx,[]),infer1(G.types,F,[],_).
infer1(G,P*Es,S,S_) :- member(P=T1,G),!,instantiate(T1,T1_),!,
                       foldl(infer2(G),Es,(prop,S),(T,S1)),!,
                       unify((T,T1_),S1,S_).
infer1(G,P*Es,S,S1) :- !,foldl(infer2(G),Es,(prop,S),(T,S1)),!,
                       bb_update(ctx,Ctx,[P=T|Ctx]).
infer1(G,F) --> {(F=forall(_,F1);F=exist(_,F1)),!},foldl(infer1(G),[F1]).
infer1(G,F) --> {!,F=..[_,F1,F2]},foldl(infer1(G),[F1,F2]).
infer1(_,_,S,S).
infer2(G,E,(P1,S2),((T2->P1),S2_)):-inferTerm(G,E,T2,S2,S2_).

%inferTerm(_,E,_,_,_) :- writeln(inferTerm(E)),fail.
inferTerm(G,*V,T_,S,S) :- member(V=T,G),!,instantiate(T,T_).
inferTerm(_,*V,T,S,S) :- bb_get(ctx,Ctx),member(V=T,Ctx).
inferTerm(_,*V,T,S,S) :- newVarT(T),bb_update(ctx,Ctx,[V=T|Ctx]).
inferTerm(G,fun Xs->E,T,S,S_) :-
  foldl([X1,XTs1,[X1=T1|XTs1]]>>newVarT(T1),Xs,[],XTs),
  bb_get(ctx,Ctx),foldl([X=T,Ctx1,[X=T|Ctx1]]>>!,XTs,Ctx,Ctx_),bb_put(ctx,Ctx_),
  inferTerm(G,E,T2,S,S1),
  bb_get(ctx,Ctx2),foldl([X,Ctx3,Ctx3_]>>select(X=_,Ctx3,Ctx3_),Xs,Ctx2,Ctx2_),bb_put(ctx,Ctx2_),
  newVarT(T),foldl([_=T3,T21,(T3->T21)]>>!,XTs,T2,T2_),unify((T2_,T),S1,S_).
inferTerm(G,E$Es,T,S,S5) :-
  inferTerm(G,E,T1,S,S1),!,
  foldl([E2,(Ts2,S2),([T2|Ts2],S3)]>>inferTerm(G,E2,T2,S2,S3),Es,([],S1),(Ts,S4)),
  newVarT(T),foldl([T3,T4,(T3->T4)]>>!,Ts,T,T2),unify((T1,T2),S4,S5).

instantiate(T,T_) :- inst(T,T_,[],_),!.
inst(varT(I),T,C,C) :- member(I=T,C).
inst(varT(I),T,C,[I=T|C]) :- newVarT(T).
inst(prop,prop,C,C).
inst(X->Y,X_->Y_) --> inst(X,X_),inst(Y,Y_).
inst(conT(Cn,[]),conT(Cn,[]),C,C).
inst(conT(Cn,[X|Xs]),conT(Cn,[X_|Xs_])) --> inst(X,X_),inst(conT(Cn,Xs),conT(Cn,Xs_)).

unify((X,X)) --> {!}.
unify((varT(I),T),S,S_) :- member(varT(I)=T1,S),unify((T1,T),S,S_).
unify((varT(I),T)) --> {occurs(I,T)},union([varT(I),T]).
unify((T,varT(I))) --> unify((varT(I),T)).
unify((conT(C,Xs),conT(C,Ys))) --> {maplist(unify1,Xs,Ys,XYs)},foldl(unify,XYs).
unify(((X1->X2),(Y1->Y2))) --> unify((X1,Y1)),unify((X2,Y2)).
unify((X,Y)) --> {throw(unificationFailed(X,Y))}.
unify1(X,Y,(X,Y)).
occurs(T,I,varT(I)) :- throw(unificationFailed(varT(I), T)).
occurs(T,I,conT(_,Ts)) :- maplist(occurs(T,I),Ts).
occurs(T,I,T1->T2) :- occurs(T,I,T1),occurs(T,I,T2).
occurs(_,_,_).
occurs(I,T) :- occurs(T,I,T),!.

:- main.
:- halt.