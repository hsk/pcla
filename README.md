# 200行定理証明支援系

去年のアドベントカレンダーで、@muyon_myonさんの一人Computer Science Advent Calendar [1] で Haskell を使った定理証明系を作成する記事がありました。この記事とHaskellのソースを参考に定理証明支援系を移植した後改良を重ねてPrologのソース200行にしてみました。

処理系が小さい理由は以下のとおりです:

- リファクタリング
- Prologで書いた
    - 論理型言語の単一化を用いた
    - 構文検査器は別プログラム
    - 動的型システムなので型指定がない
    - パーサはPrologのものを使用
    - １行に複数命令記述
    - 演算子を用いて短縮
- 外部ライブラリは別ソース

プログラムの中身は大雑把に構文検査、メインプログラム、宣言適用、コマンド適用、規則適用、置換処理、型検査から出来ています。
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

メインの処理はファイルを読み込んで、宣言の並びを `declRun/3` で実行し、結果の環境中の型と定理を表示します。

## 規則適用

規則の処理は`ruleRun/3`で行います。個々の規則に対する処理は`rule/3`で行います。

    % rule
    ruleRun([],J,J).
    ruleRun([R1|R],J,J_) :- rule(R1,J,J1),ruleRun(R,J1,J_).
    ruleRun([R1|_],J,_) :- cannotApply(R1,J).
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

`runRule/3` は末尾再帰最適化された規則リストと判断リストのRC状態マシンです。
規則に基づいて判断リストを書き換えます。
規則がなくなるか、エラーになるまで動き続け、判断リストまたはエラーを返します。

## 置換

ラムダ項,論理式,述語の置換処理があり、それぞれ `substTerm/4`,`substFormula/4`,`substPred/4`が対応しています。
`rule/3` で `substFormula/4` を用いており、 `substPred/4` は `com/4` で用います。

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

Prologは `=../2` を使って複合項を分離できるので分離して`or`,`and`,`==>`をまとめて処理しています。
<!-- betaってなに? todo -->

## コマンド実行

    comRun((_,[]),     _,[]).
    comRun((_,J),     [], J).
    comRun((G,J_),[C|Cs], J) :- !,com(C,G,J_,R),comRun(R,Cs,J).
    comRun(E,          _, _) :- throw(E).

`comRun/3`はコマンドを実行する述語です。
`ruleRun/3` と同様に判断リストJがなくなるかコマンドリストCがなくなるまで `com/4` を実行しエラーがあったら例外を投げます。

`com/4`は1つだけコマンドを実行します。
実行後処理の継続を返します。コマンドと環境と判断列から判断列と環境を返します。
`comRun/3`,`proofRun/3`から呼び出されます。

    com(apply(Rs)    ,G,J,R) :- !,rule(Rs,J,J_),!,(is_list(J_),R=(G,J_)
                                ;R=comError(apply,J_,J)).
    com(noApply(R1)  ,G,J,R) :- !,rule([R1],J,J_),!,(is_list(J_),R=(G,J)
                                ;R=comError(noapply,J_,J)).
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
    com(inst(_,_)    ,_,J,R) :- !,R=comError(inst,'empty rulement',J).
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


## 宣言実行

    declRun(G,     [],G) :- is_list(G).
    declRun(G, [D|Ds],R) :- is_list(G),decl(D,G,R1),!,declRun(R1,Ds,R).
    declRun(E,      D,_) :- writeln('decl error':E;D),halt(1).

`declRun/3`は`ruleRun/4`, `comRun/3`と同様に宣言リストから宣言を１つ取り出して`decl/3`を呼び出しなくなるまで実行します。
宣言が空、あるいはエラーなら終了しますが宣言があれば次の宣言を実行します。

`decl/3`は宣言の１つを処理します:

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
axiomは公理の宣言で、型推論`infer/2`を呼び出しその後、`insertThm/2`で環境に公理を保存します。公理は証明が必要ない命題なので証明はありません。
theoremは定理の宣言で、公理と同様に型推論`infer/2`を呼び、`insertThm/2`で環境に定理を保存します。定理は証明が必要なので`comRun/3`と同様にコマンドを処理する`proofRun/4`を実行します。`proofRun/4`は正常終了時に行う処理を渡します。
plFileはPrologのファイルを読み込む命令です。プラグインとしてuse_moduleを用いて読み込み、環境に組み込みます。
newDeclはユーザーが定義した宣言を`declRun/3`を用いて実行します。

    proofRun((G,[]),    _,N,R) :- !,call(N,G,R),!.
    proofRun((_,J),    [],_,R) :- !,R=proofNotFinished(J).
    proofRun((G,J),[C|Cs],N,R) :- !,com(C,G,J,R1),!,proofRun(R1,Cs,N,R).
    proofRun(Err,       _,_,R) :- !,R=Err.

`proofRun/4` は証明を実行するためのコマンドを実行します。 `comRun/3` に似ていますが、動作が異なります。
判断がなくなれば終了コマンド`N/2`を実行し、
判断は残っているのにコマンドがなくなった場合は証明終わっていないことを返します。
エラーが帰ってきた場合はエラーをそのまま返却します。

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

`insertThm/4` は定理を環境に保存するのですがその際は環境にない述語を`metagen/3`を用いて述語の名前に`?`を付けます。

## 型検査 infer

型検査機は通常のラムダ計算に、論理式を扱えるように拡張したものです。

    newVarT(varT(C1)) :- bb_get(cnt,C),C1 is C + 1,bb_put(cnt,C1).

`newVarT/1`はグローバルな変数を使ってユニークな型変数を返します。

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

論理式の型は決まっているのでただトラバースするだけです。 `-->/2`を用いている箇所はDCGの記法を用いています。

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

`unify/4`は型と型が同じであるという方程式を生成します。同じ型ならなにもしませんが、型変数と他の型があれば、その型の中身に型変数が出現しないか`occurs/3`で確認してから方程式に追加します。

以上でメインプログラム `pcla.pl` を全て見ました。

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


## todo 読者目線で見ることを考えてこの文書を改善する

- 命令の意味がわからない
- Prologの難しい機能使わんでくれ
- 抽象構文に、静的型付けするための無駄なネストがあるので消す
- BNFとか知らんよ
    - BNF簡単だぞ
    - 構文検査はBNFライクにしたい
        - RTG使おう
- ライセンスは？ MIT Licenceでよいかと
- 元の文書のリンクに触れる



## 参考

[1] https://qiita.com/advent-calendar/2017/myuon_myon_cs

[2] https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2017/doc/implementation.pdf
