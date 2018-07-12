# 200行定理証明支援系

定理証明支援系を200行で作りました。

処理系が小さい理由は以下のとおりです:

- リファクタリングに小さくした
- パーサはPrologのものを使用しているためパーサしません
- 動的型システムなので型指定がない
- 構文検査器は別プログラム
- １行に複数命令ある
- 論理型言語の単一化を用いた
- 演算子を用いて短縮
- 外部ライブラリは別ソース
- Prologで書いた

プログラムの中身は大雑把に構文検査、メインプログラム、宣言実行、コマンド実行、判断実行、置換処理、型検査から出来ています。
また、外部ライブラリ `lib/*.pl` と定理証明言語のライブラリ `lib/*.cl` があります。

## 構文検査 syntax_check.pl

構文検査は独立したメインプログラムsyntax_check.pl(77行)で行います。
この定理証明支援系の言語はPrologの項読み込み機能を使ってLispのS式を読み込むようにPrologのデータとして読み込まれます。その後、正規木文法として構文検査を行います。
正規木文法は、正規表現のツリーバージョンと言えるものですが、BNFと同等の検査を行うことが出来ます。

## メイン処理

    :- module(pcla,[]).
    :- expects_dialect(sicstus),bb_put(cnt,0).
    :- op(1200,xfx,⊦), op(650,xfy,[==>,$]), op(10,fx,[*,fun]).

    {A} :- call(A).

型検査の前に外部のコマンド拡張から使えるようにするためのmodule宣言をします。
SICSTus Prologの機能であるブラックボード(`bb_get/2`,`bb_put/3`)でPrologのオンメモリデータベースに気軽にアクセスできるようにします。
`op/3` を用いて演算子の指定をすることでより読みやすくします。
`{}/1` は `{}` をただのカッコのように扱えるようにして例外処理を読みやすくします。

    main :- current_prolog_flag(argv,[File|_]),read_file_to_terms(File,Ds,[]),!,
            declRun([thms=[],types=[],proof=[],coms=[],decls=[]],Ds,G),!,
            writeln('= Constants ='),member(types=Types,G),maplist(writeln,Types),
            writeln('= Proved Theorems ='),member(thms=Thms,G),maplist(writeln,Thms).

メインの処理はファイルを読み込んで、宣言の並びを実行し、結果の環境中の型と定理を表示します。

## 宣言実行

    declRun(G,     [],G) :- is_list(G).
    declRun(G, [D|Ds],R) :- is_list(G),decl(D,G,R1),!,declRun(R1,Ds,R).
    declRun(E,      D,_) :- writeln('decl error':E;D),halt(1).

declRun/3は環境と宣言リストを受取り環境を返します。
宣言が空、あるいはエラーなら終了しますが宣言があれば次の宣言を実行します。
１つ１つの宣言を実行するのがdecl/3で宣言と環境を受取り環境またはエラーを返します。

    decl(import(Path),    G,R) :- !,read_file_to_terms(Path,Ds,[]),
                                  !,declRun(G,Ds,R),!.
    decl(constant(P,Typ), G,R) :- !,select(types=Types,G,types=[P=Typ|Types],R).
    decl(axiom(Idx,F),    G,R) :- !,catch({
                                    infer(G,F),!,insertThm(Idx,F,G,R)
                                  },Err,{R=error(axiom,typeError(F,Err))}).
    decl(theorem(Idx,F,P),G,R) :- !,catch({ P=proof(Cs),
                                    infer(G,F),!,select(proof=_,G,proof=[],G_),!,
                                    proofRun((G_,[[]⊦[F]]),Cs,insertThm(Idx,F),R)
                                  },Err,{R=error(theorem,typeError(F,Err))}).
    decl(plFile(Mod),     G,R) :- !,catch({
                                    use_module(Mod,[]),Mod:export_command(Cs),
                                    Mod:export_decl(Ds),
                                    maplist([P,P=(Mod:P)]>>!,Ds,Ds_),
                                    maplist([P,P=(Mod:P)]>>!,Cs,Cs_),
                                    select(decls=Decl,G,decls=Decl2,G2),
                                    union(Decl,Ds_,Decl2),
                                    select(coms=Coms,G2,coms=Coms3,R),
                                    union(Coms,Cs_,Coms3),!
                                  },_,{R=error(plFile, plFileLoadError(Mod))}).
    decl(newDecl(Dec,Arg),G,R) :- member(decls=Decls,G),member(Dec=Fun,Decls),!,
                                  call(Fun,Arg,Ds),declRun(G,Ds,R).
    decl(newDecl(Dec,_),  _,R) :- !,R=error(Dec,noSuchDecl(Dec)).

importは他のclファイルを読み込みます。
constantは定数宣言でtypesに名前とそれに対応する型を追加します。
axiomは公理で、型推論inferを呼び出しその後、insertThmで環境に公理を保存します。公理は証明が必要ない命題です。
theoremは定理で、公理と同様に型推論を行いますが証明が必要なのでproofRunを実行します。proofRunには正常終了時に行う処理を渡しています。
plFileはPrologのファイルを読み込む命令です。プラグインとしてuse_moduleを用いて読み込み、環境に組み込みます。
newDeclはユーザーが定義した宣言をdeclRunを用いて実行します。

    insertThm(Idx,F,G,G_) :-  member(types=Types,G),metagen(Types,F,F_),
                              select(thms=Thms,G,thms=[Idx=F_|Thms],G_).
    metagen(E,P*Es,P *Es) :- member(P=_,E).
    metagen(_,P*Es,P_*Es) :- format(atom(P_),'?~w',[P]).
    metagen(_,   top,   top).
    metagen(_,bottom,bottom).
    metagen(E, and(F1,F2),and(F1_,F2_)) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
    metagen(E,  or(F1,F2), or(F1_,F2_)) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
    metagen(E,    F1==>F2,   F1_==>F2_) :- metagen(E,F1,F1_),metagen(E,F2,F2_).
    metagen(E,forall(V,F),forall(V,F_)) :- metagen(E,F,F_).
    metagen(E, exist(V,F), exist(V,F_)) :- metagen(E,F,F_).

insertThm/4 は定理を環境に保存するのですがその際は環境にない述語をmetagenを用いて述語の名前に?を付けます。

## コマンド実行

    % command
    proofRun((G,[]),    _,N,R) :- !,call(N,G,R),!.
    proofRun((_,J),    [],_,R) :- !,R=proofNotFinished(J).
    proofRun((G,J),[C|Cs],N,R) :- !,com(C,G,J,R1),!,proofRun(R1,Cs,N,R).
    proofRun(Err,       _,_,R) :- !,R=Err.

proofRunは証明を実行するためのコマンドを実行します。
判断がなくなれば終了コマンドを実行し、
判断は残っているのにコマンドがなくなった場合は証明終わっていないことを返します。
判断もコマンドもあれば1つコマンドを実行しproofRunを呼び出して次のコマンドを実行します。
エラーが帰ってきた場合はエラーをそのまま返却します。

    comRun((_,[]),     _,[]).
    comRun((_,J),     [], J).
    comRun((G,J_),[C|Cs], J) :- !,com(C,G,J_,R),comRun(R,Cs,J).
    comRun(E,          _, _) :- throw(E).

comRun/3はユーザー定義されたコマンドを実行する際に使います。proofRun/3に似ていますが、動作が異なります。

com/4は1回に1つだけ実行します。
実行後処理の継続を返します。コマンドと環境と判断列から判断列と環境を返します。
proofRun、comRunから呼び出されます。

    com(apply(Rs)    ,G,J,R) :- !,judge(Rs,J,J_),!,(is_list(J_),R=(G,J_)
                                ;R=comError(apply,J_,J)).
    com(noApply(R1)  ,G,J,R) :- !,judge([R1],J,J_),!,(is_list(J_),R=(G,J)
                                ;R=comError(noapply,J_,J)).
    com(use(I)       ,G,J,R) :- !,com(use(I, []),G,J,R).
    com(use(I,Pairs) ,G,J,R) :- member(thms=Thms,G),member(I=F,Thms),
                                !,catch({
                                  foldl([Idt:Pred,F1,F1_]>>(
                                    format(atom(Idt1),'?~w',[Idt]),
                                    substPred(Idt1,Pred,F1,F1_)
                                  ),Pairs,F,F_),!,
                                  [(A⊦Props)|J_]=J,!,R=(G,[[F_|A]⊦Props|J_])
                                },Err,{R=comError(use,cannotUse(I,Pairs,Err),J)}).
    com(use(I,_)     ,_,J,R) :- !,R=comError(use, noSuchTheorem(I),J).
    com(inst(I,Pred), G,J,R) :- J=[[A|Assms]⊦Props|J_],
                                !,catch({
                                  format(atom(I1),'?~w',[I]),substPred(I1,Pred,A,A_),
                                  R=(G,[[A_|Assms]⊦Props|J_])
                                },Err,{R=comError(inst, cannotInstantiate(Err),J)}).
    com(inst(_,_)    ,_,J,R) :- !,R=comError(inst,'empty judgement',J).
    com(com(defer,[]),G,J,R) :- !,J=[J1|J_],append(J_,[J1],J_2),R=(G,J_2).
    com(com(Com,Args),G,J,R) :- member(coms=Coms,G),member(Com=Cmd,Coms),
                                !,catch({
                                  call(Cmd,G,Args,J,Cs),!,
                                  comRun((G,J),Cs,J_),R=(G,J_)
                                },E,{
                                  E=comError(_,Err,_)->R=comError(Com,Err,J);
                                  true               ->R=comError(Com,E,J)
                                }).
    com(com(Com,_)   ,_,J,R) :- R=comError(Com, noSuchCom(Com),J).

コマンドは規則を実行するapply,規則が動くことを確認するnoApply、定理を使って判断を増やすuse、判断のトップの置換をするinst、ユーザー定義コマンドを実行するcomがあります。ユーザー定義の組み込みコマンドにはdeferコマンドがありこれは最初の判断を最後に移動します。


## 判断実行

判断の処理はjudge/3で行います。

    % judge
    %judge(Rs,Js,_) :- writeln(judge(Rs;Js)),fail.
    judge([i|R],[A⊦A|J],J_) :- judge(R,J,J_).
    judge([cut(F)|R],[A⊦P|J],J_) :- judge(R,[A⊦[F|P],[F|A]⊦P|J],J_).
    judge([andL1|R],[[and(F,_)|A]⊦P|J],J_) :- judge(R,[[F|A]⊦P|J],J_).
    judge([andL2|R],[[and(_,F)|A]⊦P|J],J_) :- judge(R,[[F|A]⊦P|J],J_).
    judge([andR|R],[A⊦[and(F1,F2)|P]|J],J_) :- judge(R,[A⊦[F1|P],A⊦[F2|P]|J],J_).
    judge([orL|R],[[or(F1,F2)|A]⊦P|J],J_) :- judge(R,[[F1|A]⊦P,[F2|A]⊦P|J],J_).
    judge([orR1|R],[A⊦[or(F,_)|P]|J],J_) :- judge(R,[A⊦[F|P]|J],J_).
    judge([orR2|R],[A⊦[or(_,F)|P]|J],J_) :- judge(R,[A⊦[F|P]|J],J_).
    judge([impL|R],[[F1==>F2|A]⊦P|J],J_) :- judge(R,[A⊦[F1|P],[F2|A]⊦P|J],J_).
    judge([impR|R],[A⊦[F1==>F2|P]|J],J_) :- judge(R,[[F1|A]⊦[F2|P]|J],J_).
    judge([bottomL|R],[[bottom|_]⊦_|J],J_) :- judge(R,J,J_).
    judge([topR|R],[_⊦[top|_]|J],J_) :- judge(R,J,J_).
    judge([forallL(T)|R],[[forall(X,F)|A]⊦P|J],J_) :- substFormula(X,T,F,F_),
                                                      judge(R,[[F_|A]⊦P|J],J_).
    judge([forallR(Y)|R],[A⊦[forall(X,F)|P]|J],J_) :- substFormula(X,*Y,F,F_),
                                                      judge(R,[A⊦[F_|P]|J],J_).
    judge([existL(Y)|R],[[exist(X,F)|A]⊦P|J],J_) :- substFormula(X,*Y,F,F_),
                                                    judge(R,[[F_|A]⊦P|J],J_).
    judge([existR(T)|R],[A⊦[exist(X,F)|P]|J],J_) :- substFormula(X,T,F,F_),
                                                    judge(R,[A⊦[F_|P]|J],J_).
    judge([wL|R],[[_|A]⊦P|J],J_) :- judge(R,[A⊦P|J],J_).
    judge([wR|R],[A⊦[_|P]|J],J_) :- judge(R,[A⊦P|J],J_).
    judge([cL|R],[[F|A]⊦P|J],J_) :- judge(R,[[F,F|A]⊦P|J],J_).
    judge([cR|R],[A⊦[F|P]|J],J_) :- judge(R,[A⊦[F,F|P]|J],J_).
    judge([pL(K)|R],[A⊦P|J],J_) :- length(A,L),K<L,nth0(K,A,Ak,K_),
                                   judge(R,[[Ak|K_]⊦P|J],J_).
    judge([pR(K)|R],[A⊦P|J],J_) :- length(P,L),K<L,nth0(K,P,Pk,P_),
                                   judge(R,[A⊦[Pk|P_]|J],J_).
    judge([],J,J) :- !.
    judge([R|_],J,cannotApply(R,J)).

この処理は末尾再帰最適化されたRC状態マシンとしてみるとわかりやすいでしょう。
ルールのリストと判断のリストを受取りルールに基づいて判断のリストを書き換えます。
ルールがなくなるか、エラーになるまで動き続け、判断リストまたはエラーを返します。

## 置換

ラムダ項、論理式、述語、の置換処理があります。

    % subst
    substTerm(I,T,*I,T) :- !.
    substTerm(I,T,fun Is->E,fun Is->E_) :- \+member(I,Is),!,substTerm(I,T,E,E_).
    substTerm(I,T,E1$E2,E1_$E2_) :- !,maplist(substTerm(I,T),[E1|E2],[E1_|E2_]).
    substTerm(_,_,T,T).

    substFormula(I,T,P*Es,P*Es_) :- !,maplist(substTerm(I,T),Es,Es_).
    substFormula(I,T,forall(X,F),forall(X,F_)) :- !,substFormula(I,T,F,F_).
    substFormula(I,T,exist(X,F),exist(X,F_)) :- !,substFormula(I,T,F,F_).
    substFormula(I,T,F,F_) :- F=..[Op,F1,F2],!,
                              maplist(substFormula(I,T),[F1,F2],Fs),F_=..[Op|Fs].
    substFormula(_,_,F,F).

    substPred(I,P,I*Ts,F_) :- !,beta(Ts,P,F_).
    substPred(I,P,forall(V,F),forall(V,F_)) :- !,substPred(I,P,F,F_).
    substPred(I,P,exist(V,F),exist(V,F_)) :- !,substPred(I,P,F,F_).
    substPred(I,P,F,F_) :- F=..[Op,F1,F2],!,
                           maplist(substPred(I,P),[F1,F2],Fs),F_=..[Op|Fs].
    substPred(_,_,Pred,Pred) :- !.
    beta(Xs,predFun([],P),F_) :- beta(Xs,P,F_).
    beta([],predFun(Z,P),_) :- throw(argumentsNotFullyApplied(predFun(Z,P))).
    beta([],predFml(F),F).
    beta([X|Xs],predFun([T|Ts],F),F_) :- sbterm(T,X,F,F1),
                                         beta(Xs,predFun(Ts,F1),F_).
    beta(Xs,predFml(F)) :- throw(cannotApplyToFormula(Xs,F)).
    sbterm(T,X,predFun(Ys,F),predFun(Ys,F_)) :- sbterm(T,X,F,F_).
    sbterm(T,X,predFml(F),predFml(F_)) :- substFormula(T,X,F,F_).

betaってなにとかtodo
Prologは=..を使って複合項を分離できるので分離して処理することでor,and,==>の処理をまとめて１行で書けてたりします。

## 型検査 infer

型検査機は通常のラムダ計算に、論理式を扱えるように拡張したものです。

    % typing
    newVarT(varT(C1)) :- bb_get(cnt,C),C1 is C + 1,bb_put(cnt,C1).

newVarT/1はグローバルな変数を使ってユニークな型変数を返します。

    infer(G,F) :- bb_put(ctx,[]),member(types=Types,G),infer1(Types,F,[],_).
    infer1(G,P*Es,S,S_) :- member(P=T1,G),!,instantiate(T1,T1_),!,
                          foldl(infer2(G),Es,(prop,S),(T,S1)),!,
                          unify((T,T1_),S1,S_).
    infer1(G,P*Es,S,S1) :- !,foldl(infer2(G),Es,(prop,S),(T,S1)),!,
                          bb_update(ctx,Ctx,[P=T|Ctx]).
    infer1(G,F) --> {(F=forall(_,F1);F=exist(_,F1)),!},foldl(infer1(G),[F1]).
    infer1(G,F) --> {!,F=..[_,F1,F2]},foldl(infer1(G),[F1,F2]).
    infer1(_,_,S,S).
    infer2(G,E,(P1,S2),((T2->P1),S2_)):-inferTerm(G,E,T2,S2,S2_).

論理式の型は決まっているのでただトラバースするだけです。 -->を用いている箇所はDCGの記法を用いています。

    %inferTerm(_,E,_,_,_) :- writeln(inferTerm(E)),fail.
    inferTerm(G,*V,T_,S,S) :- member(V=T,G),!,instantiate(T,T_).
    inferTerm(_,*V,T,S,S) :- bb_get(ctx,Ctx),member(V=T,Ctx).
    inferTerm(_,*V,T,S,S) :- newVarT(T),bb_update(ctx,Ctx,[V=T|Ctx]).
    inferTerm(G,fun Xs->E,T,S,S_) :-
      foldl([X1,XTs1,[X1=T1|XTs1]]>>newVarT(T1),Xs,[],XTs),
      bb_get(ctx,Ctx),foldl([X=T,Ctx1,[X=T|Ctx1]]>>!,XTs,Ctx,Ctx_),
      bb_put(ctx,Ctx_),
      inferTerm(G,E,T2,S,S1),
      bb_get(ctx,Ctx2),foldl([X,Ctx3,Ctx3_]>>select(X=_,Ctx3,Ctx3_),Xs,Ctx2,Ctx2_),
      bb_put(ctx,Ctx2_),
      newVarT(T),foldl([_=T3,T21,(T3->T21)]>>!,XTs,T2,T2_),unify((T2_,T),S1,S_).
    inferTerm(G,E$Es,T,S,S5) :-
      inferTerm(G,E,T1,S,S1),!,
      foldl([E2,(Ts2,S2),([T2|Ts2],S3)]>>
        inferTerm(G,E2,T2,S2,S3),Es,([],S1),(Ts,S4)),
      newVarT(T),foldl([T3,T4,(T3->T4)]>>!,Ts,T,T2),unify((T1,T2),S4,S5).

ラムダ項の推論は基本的なものです。

    instantiate(T,T_) :- inst(T,T_,[],_),!.
    inst(varT(I),T,C,C) :- member(I=T,C).
    inst(varT(I),T,C,[I=T|C]) :- newVarT(T).
    inst(prop,prop,C,C).
    inst(X->Y,X_->Y_) --> inst(X,X_),inst(Y,Y_).
    inst(conT(Cn,[]),conT(Cn,[]),C,C).
    inst(conT(Cn,[X|Xs]),conT(Cn,[X_|Xs_])) --> inst(X,X_),
                                                inst(conT(Cn,Xs),conT(Cn,Xs_)).

環境にある変数は参照された場合に具体化されます。

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

unifyは型と型が同じであるという方程式を生成します。同じ型ならなにもしませんが、型変数と他の型があれば、その型の中身に型変数が出現しないかoccurs/3で確認してから方程式に追加します。

## ユーザー定義宣言

外部ファイルを記述するにはexport_decl/1とexport_command/1に定義した述語名を記述します。

    export_decl([definition]).

export_declは宣言の定義です。

definition

    definition([n(I:Typ),p([predFml(Body)])],[constant(I,Typ),axiom(I2,Body)]) :-
      format(atom(I2),'~w_def',[I]).
    definition(Arg,_) :- throw(wrongArgument(Arg)).

## ユーザー定義コマンド

ユーザー定義コマンドはPrologのプログラムで追加できるコマンドです。
追加するにはexport_commandに以下のように定義します:

    export_command([assumption,implyR,implyL,genR,genL,absL]).

例えばassumptionのコマンドは以下のように定義します。

    :- module('lib/commands',[]).

    assumption(_,[],[(Assms⊦Props)|_],[apply(Rs)]) :-
      findIndex([A]>>member(A,Assms),Props,I),!,
      nth0(I,Props,I2),elemIndex(I2,Assms,J),!,
      length(Props,Pi),length(Assms,Aj),
      onlyR(I,Pi,Ps),onlyL(J,Aj,As),append([Ps,As,[i]],Rs).
    assumption(_,[],[(Assms⊦Props)|Js],_) :- throw(cannotSolve([(Assms⊦Props)|Js])).
    assumption(_,_,_,_) :- throw(wrongArgument([])).

    replicate(0,_,[]).
    replicate(N,V,[V|Vs]) :- N1 is N - 1, replicate(N1,V,Vs).
    findIndex(F,Ls,R) :- findIndex1(F,0,Ls,R).
    findIndex1(F,N,[X|_],N) :- call(F,X),!.
    findIndex1(F,N,[_|Xs],R) :- N1 is N + 1, findIndex1(F,N1,Xs,R).
    elemIndex(E,Ls,R) :- findIndex(=(E),Ls,R).
    onlyL(I,N,Rs) :-
      replicate(I,[wL],R1),NI1 is N-I-1,replicate(NI1,[pL(1),wL],R2),
      append(R1,R2,R3),append(R3,Rs).
    onlyR(I,N,Rs) :-
      replicate(I,[wR],R1),NI1 is N-I-1,replicate(NI1,[pR(1),wR],R2),
      append(R1,R2,R3),append(R3,Rs).

implyR

    implyR(Env,i([(I,Ps)]),Js,[use(I, Ps)| Cs1]) :- implyR(Env,[],Js,Cs1).
    implyR(_,[],_,
        [ apply([impL]),com(defer, []),com(assumption, []),apply([pR(1), wR])]) :- !.
    implyR(_,Arg,_,_) :- throw(wrongArgument(Arg)).

implyL

    implyL(Env,i([(I,Ps)]),Js,[use(I,Ps)|Cs]) :- implyL(Env,[],Js,Cs).
    implyL(_,[],_,[apply([impL]),com(assumption,[]),apply([pL(1),wL])]).
    implyL(_,Arg,_,_) :- throw(wrongArgument(Arg)).

genR

    genR(_,i([(I,[])]),[_ ⊦ [P|_] |_],[
      apply([cut(forall(I, P))]),
      com(defer, []),
      apply([forallL(*I)]),
      com(assumption, []),
      apply([pR(1), wR])
    ]) :- !.
    genR(_,Arg,Js,_) :- throw(wrongArgument(Arg,Js)).

genL

    genL(_,i([(I,[])]),[[P|Ps] ⊦ _ |_],[
      apply([cut(forall(I, P))]),
      apply([forallR(*I)]),
      com(assumption, []),
      apply([pL(PLen), wL])
    ]) :- length(Ps,PLen).
    genL(_,Arg,_,_) :- throw(wrongArgument(Arg)).

absL

    absL(_,[],[[A|_] ⊦ [B|_]|_],[
      apply([cut(A==>B)]),
      com(defer, []),
      apply([impL]),
      com(assumption, []),
      com(assumption, []),
      apply([pR(1),wR, wL])
    ]).
    absL(_,Arg,Js,_) :- throw(wrongArgument(Arg,Js)).
