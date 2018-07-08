:- module(typing,[infer/2,union/3]).
:- expects_dialect(sicstus).
:- use_module(claire).
:- use_module(fol).
:- use_module(env).
foldr(F,Ls,A,A_) :- reverse(Ls,Ls_),!,foldl(F,Ls_,A,A_).
union(A,[],A).
union(A,[B|Bs],R) :- member(B,A),union(A,Bs,R).
union(A,[B|Bs],R) :- append(A,[B],C),union(C,Bs,R).

utype(U) :- typeForm(int,U).
unions(A,B) :- foldl(union,A,[],B).
reset :- bb_put(cnt,0).
new_id(C1) :- bb_get(cnt,C),C1 is C + 1,bb_put(cnt,C1).
:- reset.

fvT(varT(V),[V]).
fvT(conT(_,Ts),Vs) :- maplist(fvT,Ts,Vss),unions(Vss,Vs).
fvT((T1->T2),Vs) :- fvT(T1,V1),fvT(T2,V2),union(V1,V2,Vs).
fvT(prop,[]).
occurs(I,T) :- fvT(T,V),!,(member(I,V),writeln(koko),throw(unificationFailed(varT(I), T));true).

unify((X,X)) --> {!}.
unify((varT(I),T),S,S_) :- member(varT(I)=T1,S),unify((T1,T),S,S_).
unify((varT(I),T)) --> {occurs(I,T)},union([varT(I),T]).
unify((T,varT(I))) --> unify((varT(I),T)).
unify((conT(C,Xs),conT(C,Ys))) --> {maplist(unify1,Xs,Ys,XYs)},foldl(unify,XYs).
unify(((X1->X2),(Y1->Y2))) --> unify((X1,Y1)),unify((X2,Y2)).
unify((X,Y)) --> {throw(unificationFailed(X,Y))}.
unify1(X,Y,(X,Y)).

instantiate(T,T_) :- inst(T,T_,[],_),!.
inst(varT(I),varT(T),C,C) :- member(I=T,C).
inst(varT(I),varT(N),C,[I=N|C]) :- new_id(N).
inst(prop,prop,C,C).
inst((X->Y),(X_->Y_)) --> inst(X,X_),inst(Y,Y_).
inst(conT(Cn,[]),conT(Cn,[]),C,C).
inst(conT(Cn,[X|Xs]),conT(Cn,[X_|Xs_])) --> inst(X,X_),inst(conT(Cn,Xs),conT(Cn,Xs_)).

%inferTerm(_,E,_,_,_) :- writeln(inferTerm(E)),fail.
inferTerm(Env,var(V),T_,S,S) :- member(V=T,Env),!,instantiate(T,T_).
inferTerm(_,var(V),T,S,S) :- bb_get(ctx,Ctx),member(V=T,Ctx).
inferTerm(_,var(V),T,S,S) :- new_id(I),T = varT(I),bb_update(ctx,Ctx,[V=T|Ctx]).
inferTerm(Env,abs(Xs, E),T,S,S_) :-
  maplist([X1,(X1=varT(Id1))]>>new_id(Id1),Xs,XTs),
  bb_get(ctx,Ctx),foldl([(X=T),Ctx1,[(X=T)|Ctx1]]>>!,XTs,Ctx,Ctx_),bb_put(ctx,Ctx_),
  inferTerm(Env,E,T2,S,S1),
  bb_get(ctx,Ctx2),foldl([X,Ctx3,Ctx3_]>>select(X=_,Ctx3,Ctx3_),Xs,Ctx2,Ctx2_),bb_put(ctx,Ctx2_),
  new_id(Id),T=varT(Id),
  foldr([_=T3,T21,(T3->T21)]>>!,XTs,T2,T2_),unify((T2_,T),S1,S_).
inferTerm(Env,E$Es,T,S,S5) :-
  inferTerm(Env,E,T1,S,S1),!,
  foldr([E2,(Ts2,S2),([T2|Ts2],S3)]>>inferTerm(Env,E2,T2,S2,S3),Es,([],S1),(Ts,S4)),
  new_id(Id),T=varT(Id),foldr([A,B,(A->B)]>>!,Ts,T,T2),unify((T1,T2),S4,S5).

infer(Env,F) :-
%  writeln(infer(F)),!,
  bb_put(ctx,[]),member(types=Types,Env),infer1(Types,F,[],_).
infer1(_,top,S,S).
infer1(_,bottom,S,S).
infer1(Env,forall(_,F)) --> infer1(Env,F).
infer1(Env,exist(_,F)) --> infer1(Env,F).
infer1(Env,and(F1,F2)) --> infer1(Env,F1),infer1(Env,F2).
infer1(Env,or(F1,F2)) --> infer1(Env,F1),infer1(Env,F2).
infer1(Env,(F1==>F2)) --> infer1(Env,F1),infer1(Env,F2).
infer1(Env,pred(P,Es),S,S_) :-
  member(P=T1,Env),!,instantiate(T1,T1_),!,
  foldl([E,(P1,S2),((T2->P1),S2_)]>>inferTerm(Env,E,T2,S2,S2_),Es,(prop,S),(T,S1)),!,
  unify((T,T1_),S1,S_).
infer1(Env,pred(P,Es),S,S1) :- !,
  foldl([E,(P1,S2),((T2->P1),S2_)]>>inferTerm(Env,E,T2,S2,S2_),Es,(prop,S),(T,S1)),!,
  bb_update(ctx,Ctx,[P=T|Ctx]).
