:- module(lk,[judgement/1,assmIndex/1,rule/1,judge/3]).
:- use_module(fol).
judgement(Fs1 ⊦ Fs2) :- maplist(formula,Fs1),maplist(formula,Fs2).
assmIndex(I) :- string(I).
rule(i). rule(cut(F)) :- formula(F).
rule(andL1). rule(andL2). rule(andR).
rule(orL). rule(orR1). rule(orR2).
rule(impL). rule(impR). rule(bottomL). rule(topR).
rule(forallL(T)) :- term(T). rule(forallR(I)) :- ident(I).
rule(existL(I)) :- ident(I). rule(existR(T)) :- term(T).
rule(wL). rule(wR). rule(cL). rule(cR).
rule(pL(I)) :- integer(I). rule(pR(I)) :- integer(I).

%judge(Rs,Js,_) :- writeln(judge(Rs;Js)),fail.
judge([i|R],[A⊦A|J],J_) :- judge(R,J,J_).
judge([cut(F)|R],[A⊦P|J],J_) :- judge(R,[A⊦[F|P],[F|A]⊦P|J],J_).
judge([andL1|R],[[and(F,_)|A]⊦P|J],J_) :- judge(R,[[F|A]⊦P|J],J_).
judge([andL2|R],[[and(_,F)|A]⊦P|J],J_) :- judge(R,[[F|A]⊦P|J],J_).
judge([andR|R],[A⊦[and(F1,F2)|P]|J],J_) :- judge(R,[A⊦[F1|P],A⊦[F2|P]|J],J_).
judge([orL|R],[[or(F1,F2)|A]⊦P|J],J_) :- judge(R,[[F1|A]⊦P,[F2|A]⊦P|J],J_).
judge([orR1|R],[A⊦[or(F,_)|P]|J],J_) :- judge(R,[A⊦[F|P]|J],J_).
judge([orR2|R],[A⊦[or(_,F)|P]|J],J_) :- judge(R,[A⊦[F|P]|J],J_).
judge([impL|R],[[(F1==>F2)|A]⊦P|J],J_) :- judge(R,[A⊦[F1|P],[F2|A]⊦P|J],J_).
judge([impR|R],[A⊦[(F1==>F2)|P]|J],J_) :- judge(R,[[F1|A]⊦[F2|P]|J],J_).
judge([bottomL|R],[[bottom|_]⊦_|J],J_) :- judge(R,J,J_).
judge([topR|R],[_⊦[top|_]|J],J_) :- judge(R,J,J_).
judge([forallL(T)|R],[[forall(X,F)|A]⊦P|J],J_) :- substFormula(X,T,F,F_),judge(R,[[F_|A]⊦P|J],J_).
judge([forallR(Y)|R],[A⊦[forall(X,F)|P]|J],J_) :- substFormula(X,!Y,F,F_),judge(R,[A⊦[F_|P]|J],J_).
judge([existL(Y)|R],[[exist(X,F)|A]⊦P|J],J_) :- substFormula(X,!Y,F,F_),judge(R,[[F_|A]⊦P|J],J_).
judge([existR(T)|R],[A⊦[exist(X,F)|P]|J],J_) :- substFormula(X,T,F,F_),judge(R,[A⊦[F_|P]|J],J_).
judge([wL|R],[[_|A]⊦P|J],J_) :- judge(R,[A⊦P|J],J_).
judge([wR|R],[A⊦[_|P]|J],J_) :- judge(R,[A⊦P|J],J_).
judge([cL|R],[[F|A]⊦P|J],J_) :- judge(R,[[F,F|A]⊦P|J],J_).
judge([cR|R],[A⊦[F|P]|J],J_) :- judge(R,[A⊦[F,F|P]|J],J_).
judge([pL(K)|R],[A⊦P|J],J_) :- length(A,L),K<L,nth0(K,A,Ak,K_),judge(R,[[Ak|K_]⊦P|J],J_).
judge([pR(K)|R],[A⊦P|J],J_) :- length(P,L),K<L,nth0(K,P,Pk,P_),judge(R,[A⊦[Pk|P_]|J],J_).
judge([],J,J) :- !.
judge([R|_],J,_) :- throw(goalError(R,J)).
