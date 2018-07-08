:- module(fol,[
  op(1200,xfx,⊦),
  op(650,xfy,[==>,$]),
  op(10,fx,[!]),
  ident/1,term/1,formula/1,const/1,neg/1,predicate/1,typeForm/2,type/1,
  substType/4,substFormula/4,substPred/4
]).
ident(S) :- atom(S).
term(!I) :- ident(I).
term(fun(Is,E)) :- maplist(ident,Is),term(E).
term(E$Es) :- term(E),maplist(term,Es).

formula(pred(I,Es)) :- ident(I),maplist(term,Es).
formula(top).
formula(bottom).
formula(and(F1,F2)) :- formula(F1),formula(F2).
formula(or(F1,F2)) :- formula(F1),formula(F2).
formula((F1==>F2)) :- formula(F1),formula(F2).
formula(forall(I,F)) :- ident(I),formula(F).
formula(exist(I,F)) :- ident(I),formula(F).

const(C) :- format('please rewrite pred(~w,[])\n',[C]),halt.
neg(A) :- format('please rewrite ==>(~w,bottom)\n',[A]),halt.

predicate(predFun(Is,P)) :- maplist(ident,Is),predicate(P).
predicate(predFml(F)) :- formula(F).

typeForm(TA,varT(A)) :- !,call(TA,A).
typeForm(TA,conT(I,Ts)) :- !,ident(I),maplist(typeForm(TA),Ts).
typeForm(TA,T1->T2) :- !,typeForm(TA,T1),!,typeForm(TA,T2).
typeForm(_,prop) :- !.
%typeForm(TA,T) :- writeln(error:typeForm(TA,T)).
type(T) :- typeForm(ident,T),!.

substType(X,T,varT(X),T) :- !.
substType(_,_,varT(Y),varT(Y)).
substType(X,T,conT(Y,Ts),conT(Y,Ts_)) :- maplist(subType(X,T),Ts,Ts_).
substType(X,T,(Y1->Y2),(Y1_->Y2_)) :- maplist(subType(X,T),[Y1,Y2],[Y1_,Y2_]).
substType(_,_,prop,prop).

substTerm(I,T_,!I,T_).
substTerm(_,_,!I,!I).
substTerm(I,_,fun(Is,E),fun(Is,E)) :- member(I,Is),!.
substTerm(I,T_,fun(Is,E),fun(Is,E_)) :- substTerm(I,T_,E,E_).
substTerm(I,T_,E1$E2,E1_$E2_) :- maplist(substTerm(I,T_),[E1|E2],[E1_|E2_]).

substFormula(I,T_,pred(P,Es),pred(P,Es_)) :- maplist(substTerm(I,T_),Es,Es_).
substFormula(_,_,top,top).
substFormula(_,_,bottom,bottom).
substFormula(I,T_,and(F1,F2),and(F1_,F2_)) :- maplist(substFormula(I,T_),[F1,F2],[F1_,F2_]).
substFormula(I,T_,or(F1,F2),or(F1_,F2_)) :- maplist(substFormula(I,T_),[F1,F2],[F1_,F2_]).
substFormula(I,T_,(F1==>F2),(F1_==>F2_)) :- maplist(substFormula(I,T_),[F1,F2],[F1_,F2_]).
substFormula(I,T_,forall(X,F),forall(X,F_)) :- substFormula(I,T_,F,F_).
substFormula(I,T_,exist(X,F),exist(X,F_)) :- substFormula(I,T_,F,F_).

sbterm(T,X,predFun(Ys,F),predFun(Ys,F_)) :- sbterm(T,X,F,F_).
sbterm(T,X,predFml(F),predFml(F_)) :- substFormula(T,X,F,F_).
beta(Xs,predFun([],P),F_) :- beta(Xs,P,F_).
beta([],predFun(Z,P),_) :- throw(argumentsNotFullyApplied(predFun(Z,P))).
beta([],predFml(F),F).
beta([X|Xs],predFun([T|Ts],F),F_) :- sbterm(T,X,F,F1),beta(Xs,predFun(Ts,F1),F_).
beta(Xs,predFml(F)) :- throw(cannotApplyToFormula(Xs,F)).

substPred(I,P,pred(I,Ts),F_) :- !,beta(Ts,P,F_).
substPred(_,_,pred(I,Ts),pred(I,Ts)).
substPred(_,_,top,top).
substPred(_,_,bottom,bottom).
substPred(I,P,and(F1,F2),and(F1_,F2_)) :- maplist(substPred(I,P),[F1,F2],[F1_,F2_]).
substPred(I,P,or(F1,F2),or(F1_,F2_)) :- maplist(substPred(I,P),[F1,F2],[F1_,F2_]).
substPred(I,P,(F1==>F2),(F1_==>F2_)) :- maplist(substPred(I,P),[F1,F2],[F1_,F2_]).
substPred(I,P,forall(V,F),forall(V,F_)) :- substPred(I,P,F,F_).
substPred(I,P,exist(V,F),exist(V,F_)) :- substPred(I,P,F,F_).
