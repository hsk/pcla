:- module(claire,[
  thmIndex/1,pair/1,pairs/1,argument/1,command/1,proof/1,decl/1,laire/1
]).
:- use_module(fol).
:- use_module(lk).
thmIndex(X) :- atom(X).
pair(I:P) :- ident(I),predicate(P).
pairs(IPs) :- maplist(pair,IPs).
ipairs((I,IPs)) :- ident(I),pairs(IPs).
argument([]).
argument(p(Ps)) :- maplist(predicate,Ps).
argument(argTerms(Es)) :- maplist(term,Es).
argument(n(I:T)) :- ident(I),type(T).
argument(i(IIPs)) :- maplist(ipairs,IIPs).
command(apply(Rs)) :- maplist(rule,Rs).
command(use(I,IPs)) :- thmIndex(I),pairs(IPs).
command(use(I)) :- thmIndex(I).
command(inst(I,P)) :- ident(I),predicate(P).
command(noApply(R)) :- rule(R).
command(newCommand(I,A)) :- ident(I),argument(A).
proof(proof(Cs)) :- maplist(command,Cs).
decl(theorem(I,F,Pr)) :- thmIndex(I),formula(F),proof(Pr).
decl(axiom(I,F)) :- thmIndex(I),formula(F).
decl(import(X)) :- atom(X).
decl(printProof).
decl(constant(I,T)) :- ident(I),type(T).
decl(plFile(X)) :- atom(X).
decl(newDecl(I,As)) :- ident(I),maplist(argument,As).
laire(Ds) :- maplist(decl,Ds).
