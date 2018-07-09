:- module(env,[
  %env/1,
  defEnv/1,print_proof/2,
  insertThm/4]).
:- use_module(fol).
:- use_module(lk).
:- use_module(claire).

defEnv([thms=[],types=[],proof=[],newcommands=[],newdecls=[]]).

print_proof(Env,S) :-
  member(proof=Pr,Env),filter(print_proof1,Pr,Pr1),
  maplist(print_proof2,Pr1,Pr2),
  atomic_list_concat(Pr2,'\n',Pr3),
  format(atom(S),'= proof of the previous theorem =\nproof\n~w\nqed\n',[Pr3]).
print_proof1((noApply(_),_)) :- fail,!.
print_proof1(_).
print_proof2(X,X_) :- format(atom(X_),'  ~w',X).

metagen(E,P*Es,P*Es) :- member(P=_,E).
metagen(_,P*Es,P_*Es) :- format(atom(P_),'?~w',[P]).
metagen(_,top,top).
metagen(_,bottom,bottom).
metagen(E,and(F1,F2),and(F1_,F2_)) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
metagen(E,or(F1,F2),or(F1_,F2_)) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
metagen(E,(F1==>F2),(F1_==>F2_)) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
metagen(E,forall(V,F),forall(V,F_)) :- metagen(E,F,F_).
metagen(E,exist(V,F),exist(V,F_)) :- metagen(E,F,F_).

insertThm(Idx,F,Env,Env_) :-
  member(types=Types,Env),metagen(Types,F,F_),
  select(thms=Thms,Env,thms=[Idx=F_|Thms],Env_).
