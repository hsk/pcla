:- op(1200,xfx,⊦), op(650,xfy,[==>,$,=>]), op(10,fx,[fun]).

% fol

ident(S) :- atom(S).
term(I) :- ident(I).
term(fun Is->E) :- maplist(ident,Is),term(E).
term(E$Es) :- term(E),maplist(term,Es).

formula(I*Es) :- ident(I),maplist(term,Es).
formula(top).
formula(bottom).
formula(and(F1,F2)) :- formula(F1),formula(F2).
formula(or(F1,F2)) :- formula(F1),formula(F2).
formula(F1==>F2) :- formula(F1),formula(F2).
formula(forall(I,F)) :- ident(I),formula(F).
formula(exist(I,F)) :- ident(I),formula(F).

predicate(Is=>P) :- !,maplist(ident,Is),predicate(P).
predicate(F) :- formula(F).

typeForm(_,prop) :- !.
typeForm(TA,A) :- call(TA,A).
typeForm(TA,I*Ts) :- !,ident(I),maplist(typeForm(TA),Ts).
typeForm(TA,T1->T2) :- !,typeForm(TA,T1),!,typeForm(TA,T2).
identT(T) :- T \= prop,ident(T).
type(T) :- typeForm(identT,T),!.

% lk

rule(i). rule(cut(F)) :- formula(F).
rule(andL1). rule(andL2). rule(andR).
rule(orL). rule(orR1). rule(orR2).
rule(impL). rule(impR). rule(bottomL). rule(topR).
rule(forallL(T)) :- term(T). rule(forallR(I)) :- ident(I).
rule(existL(I)) :- ident(I). rule(existR(T)) :- term(T).
rule(wL). rule(wR). rule(cL). rule(cR).
rule(pL(I)) :- integer(I). rule(pR(I)) :- integer(I).

% claire

thmIndex(X) :- atom(X).
pair(I:P) :- ident(I),predicate(P).
pairs(IPs) :- maplist(pair,IPs).
ipairs((I,IPs)) :- ident(I),pairs(IPs).
argument([]).
argument(p(Ps)) :- maplist(predicate,Ps).
argument(t(Es)) :- maplist(term,Es).
argument(n(I:T)) :- ident(I),type(T).
argument(i(IIPs)) :- maplist(ipairs,IIPs).
command(apply(Rs)) :- maplist(rule,Rs).
command(use(I,IPs)) :- thmIndex(I),pairs(IPs).
command(use(I)) :- thmIndex(I).
command(inst(I,P)) :- ident(I),predicate(P).
command(noApply(R)) :- rule(R).
command(com(I,A)) :- ident(I),argument(A).
proof(proof(Cs)) :- maplist(command,Cs).
decl(theorem(I,F,Pr)) :- thmIndex(I),formula(F),proof(Pr).
decl(axiom(I,F)) :- thmIndex(I),formula(F).
decl(import(X)) :- atom(X).
decl(printProof).
decl(constant(I,T)) :- ident(I),type(T).
decl(plFile(X)) :- atom(X).
decl(newDecl(I,As)) :- ident(I),maplist(argument,As).
laire(Ds) :- maplist(decl,Ds).

dependFile1(import(File)) :- check(File).
dependFile1(_).
dependFile(Ds) :- maplist(dependFile1,Ds).

check(File):-
  catch((
    read_file_to_terms(File,Ds,[]),
    (laire(Ds),format('syntax ok ~w\n',[File]),dependFile(Ds);writeln('syntax error'),halt(1))
  ),Err,(writeln(Err),halt(2))).

:- current_prolog_flag(argv,[File|_]), check(File).
:- halt.
