# 200行定理証明支援系

去年のアドベントカレンダーで、@muyon_myonさんの一人Computer Science Advent Calendar [1] で Haskell を使った定理証明系を作成する記事がありました。この記事とHaskellのソースを参考に定理証明支援系を移植した後改良を重ねてPrologのソース200行にしてみました。
The Isabelle/Isar Implementation [2] をおそらく参考にしたようなので詳しくはそちらを参照するとよいでしょう。

処理系が小さい理由は以下のとおりです:

- Prologで書いた
- リファクタリング
- 論理型言語の単一化を用いた
- 構文検査器は別プログラム
- 動的型システムなので型指定がない
- パーサはPrologのものを使用
- １行に複数命令記述
- 演算子を用いて短縮
- 外部ライブラリは別ソース
- 静的型付けするために必要な抽象構文のネストがない

プログラムの中身は大雑把に構文検査、メインプログラム、宣言適用、コマンド適用、規則適用、置換処理、型検査から出来ています。
また、外部ライブラリ `lib/*.pl` と定理証明言語のライブラリ `lib/*.cl` があります。

## 構文

fol

    [T]         ::= maplist(T).
    ident       ::= atom.
    term        ::= ident
                  | [ident]->term
                  | term*[term].
    formula     ::= ident*[term]
                  | top
                  | bottom
                  | and(formula,formula)
                  | or(formula,formula)
                  | formula==>formula
                  | forall(ident,formula)
                  | exist(ident,formula).
    predicate   ::= [ident]=>predicate
                  | formula.
    typeForm(T) ::= prop
                  | call(T)
                  | ident*[typeForm(T)]
                  | typeForm(T)->typeForm(T).
    identT(T)   ::= ident.
    type        ::= typeForm(identT).

lk

    rule        ::= i | cut(formula)
                  | andL1 | andL2 | andR
                  | orL | orR1 | orR2
                  | impL | impR | bottomL | topR
                  | forallL(term) | forallR(ident)
                  | existL(ident) | existR(term)
                  | wL | wR | cL | cR
                  | pL(integer) | pR(integer).

claire

    thmIndex    ::= atom.
    pair        ::= ident:predicate.
    pairs       ::= [pair].
    ipairs      ::= (ident,pairs).
    argument    ::= []
                  | p([predicate])
                  | t([term])
                  | n(ident:type)
                  | i([ipairs]).
    command     ::= apply([rule])
                  | use(thmIndex,pairs)
                  | inst(ident,predicate)
                  | noApply(rule)
                  | ident*argument.
    decl        ::= theorem(thmIndex,formula,proof([command]))
                  | axiom(thmIndex,formula)
                  | import(atom)
                  | printProof
                  | constant(ident,type)
                  | plFile(atom)
                  | ident*[argument].
    laire       ::= [decl].

## ユーザーマニュアル

pclaは大まかにいうとFOLとLKとDeclsの3つの層に分かれています。
FOLはλ項のterm、論理式formula、述語predicate、型typeからなる一階述語論理です。
LKは証明に用いる規則ruleを含みます。
Declsは上位の宣言で、定理theorem,公理axiom,インポートimport,証明印字printProof,定数constant,Prologファイル読み込みplFile,ユーザー定義宣言から成ります。
定理には証明が必ず必要で、証明の中身はcommandリストです。
コマンドには規則適用apply,定理使用use,述語のインスタンス化inst,規則確認noApply,ユーザー定義コマンド適用comがあります。

### FOL

#### term
    term        ::= ident
                  | [ident]->term
                  | term*[term].

#### formula

    formula     ::= ident*[term]
                  | top
                  | bottom
                  | and(formula,formula)
                  | or(formula,formula)
                  | formula==>formula
                  | forall(ident,formula)
                  | exist(ident,formula).

#### predicate

    predicate   ::= [ident]=>predicate
                  | formula.

#### type

    typeForm(T) ::= prop
                  | call(T)
                  | ident*[typeForm(T)]
                  | typeForm(T)->typeForm(T).
    identT(T)   ::= ident.
    type        ::= typeForm(identT).

### LK

    rule        ::= i | cut(formula)
                  | andL1 | andL2 | andR
                  | orL | orR1 | orR2
                  | impL | impR | bottomL | topR
                  | forallL(term) | forallR(ident)
                  | existL(ident) | existR(term)
                  | wL | wR | cL | cR
                  | pL(integer) | pR(integer).

#### i

    rule(i,[A⊦A|J],J).

「AならばA」はあたりまえだから判断から除去できる規則がandL1です。

i は私ならば私である。といった判断を除去します。

#### cut(formula)

    rule(cut(F),[A⊦P|J],[A⊦[F|P],[F|A]⊦P|J]).

cutは飛躍のある論理に新しい論理を追加して間をつなぎます。

「AならばP」のとき、「AならばFかつP」かつ「FかつAならばP」という規則がcutです。

#### andL1 | andL2 | andR

    rule(andL1,[[and(F,_)|A]⊦P|J],[[F|A]⊦P|J]).
    rule(andL2,[[and(_,F)|A]⊦P|J],[[F|A]⊦P|J]).
    rule(andR,[A⊦[and(F1,F2)|P]|J],[A⊦[F1|P],A⊦[F2|P]|J]).

andL1は仮定内のandの左側のみを取り出し、andL2はandの右側を取り出します。
andRは結論のandを2つの判断に分割します。

「AかつBならばC」ならば、「AならばC」という規則がandL1です。
「AかつBならばC」ならば、「BならばC」という規則がandL2です。
「AならばBかつC」ならば、「AならばBかつAならばC」という規則がandL2です。

#### orL | orR1 | orR2

トップのorの規則です。

    rule(orL,[[or(F1,F2)|A]⊦P|J],[[F1|A]⊦P,[F2|A]⊦P|J]).
    rule(orR1,[A⊦[or(F,_)|P]|J],[A⊦[F|P]|J]).
    rule(orR2,[A⊦[or(_,F)|P]|J],[A⊦[F|P]|J]).

「F1またはF2、ならばP」ならば、「F1ならばP、かつF2ならばP」という規則がorLです。
「Aならば、BまたはC」ならば、「AならばB」という規則がorR1です。
「Aならば、BまたはC」ならば、「AならばC」という規則がorR2です。

#### impL | impR | bottomL | topR

    rule(impL,[[F1==>F2|A]⊦P|J],[A⊦[F1|P],[F2|A]⊦P|J]).
    rule(impR,[A⊦[F1==>F2|P]|J],[[F1|A]⊦[F2|P]|J]).
    rule(bottomL,[[bottom|_]⊦_|J],J).
    rule(topR,[_⊦[top|_]|J],J).

impLはF1ならばF2かつAならばPならば、AならばF1かつPかつF2かつAならばPとします。
impRはAならばF1ならばF2かつPならば、F1かつAならばF2かつPとします。
bottomLはbottomを仮定から取り除きます。
topRはtopを結論から取り除きます。

#### forallL(term) | forallR(ident)

    rule(forallL(T),[[forall(X,F)|A]⊦P|J],[[F_|A]⊦P|J]) :- substFormula(X,T,F,F_).
    rule(forallR(Y),[A⊦[forall(X,F)|P]|J],[A⊦[F_|P]|J]) :- substFormula(X,Y,F,F_).

forallL(T)は仮定のforall(X,F)のFをXからTに置き換えます。
forallR(Y)は結論のforall(X,F)のFをXからYに置き換えます。

#### existL(ident) | existR(term)

    rule(existL(Y),[[exist(X,F)|A]⊦P|J],[[F_|A]⊦P|J]) :- substFormula(X,Y,F,F_).
    rule(existR(T),[A⊦[exist(X,F)|P]|J],[A⊦[F_|P]|J]) :- substFormula(X,T,F,F_).

existL(Y) は仮定のexist(X,F)のFをXからYに置き換えます。
existR(T) は結論のexist(X,F)のFをXからTに置き換えます。

#### wL | wR | cL | cR

    rule(wL,[[_|A]⊦P|J],[A⊦P|J]).
    rule(wR,[A⊦[_|P]|J],[A⊦P|J]).
    rule(cL,[[F|A]⊦P|J],[[F,F|A]⊦P|J]).
    rule(cR,[A⊦[F|P]|J],[A⊦[F,F|P]|J]).

wLは一つ仮定を捨てます。弱化ですね。
wRは結論を1つ捨てます。
cLは仮定をコピーします。
cRは結論を1つコピーします。

wL,wRで全部消したら証明になるのかというとならないはずです。

#### pL(integer) | pR(integer)

    rule(pL(K),[A⊦P|J],[[Ak|K_]⊦P|J]) :- length(A,L),K<L,nth0(K,A,Ak,K_).
    rule(pR(K),[A⊦P|J],[A⊦[Pk|P_]|J]) :- length(P,L),K<L,nth0(K,P,Pk,P_).

pL(K)はK番目の仮定をいちばんうしろに移動します。
pR(K)はK番目の結論をいちばんうしろに移動します。

### Decls

## Prologの難しい機能

TODO

## 構文検査 syntax_check.pl,syntax_rtg.pl

構文検査は独立したメインプログラムsyntax_check.pl(77行)で行います。
この定理証明支援系の言語はPrologの項読み込み機能を使ってLispのS式を読み込むようにPrologのデータとして読み込みます。その後、正規木文法として構文検査を行います。

syntax_rtg.plはもう一つの構文検査プログラムです。正規木文法ライブラリをもちいています。
正規木文法は、正規表現のツリーバージョンと言えるものですが、BNFと同様のリカージョンを含んだ言語の検査を行うことが出来ます。
syntax_rtg.plを動かすには、

    ?- pack_install(rtg).

としてSWI-Prologのパッケージからライブラリをインストールして使います。


## メイン処理

    :- module(pcla,[]).
    :- expects_dialect(sicstus),bb_put(cnt,0).
    :- op(1200,xfx,⊦), op(650,xfy,[==>,=>]).

    {A} :- call(A).

型検査の前に外部のコマンド拡張から使えるようにするためのmodule宣言をします。
SICSTus Prologの機能であるブラックボード(`bb_get/2`,`bb_put/3`)でPrologのオンメモリデータベースに気軽にアクセスできるようにします。
`op/3` を用いて演算子の指定をすることでより読みやすくします。
`{}/1` は `{}` をただのカッコのように扱えるようにして例外処理を読みやすくします。

    main :- current_prolog_flag(argv,[File|_]),read_file_to_terms(File,Ds,[]),!,
      declRun(env{thms:[],types:[],proof:[],coms:[],decls:[]},Ds,G),!,
      writeln('= Constants ='),maplist(writeln,G.types),
      writeln('= Proved Theorems ='),maplist(writeln,G.thms).

メインの処理はファイルを読み込んで、宣言の並びを `declRun/3` で実行し、結果の環境中の型と定理を表示します。

## 規則適用

規則の処理は`ruleRun/3`で行います。個々の規則に対する処理は`rule/3`で行います。

    % rule
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
    rule(forallR(Y),[A⊦[forall(X,F)|P]|J],[A⊦[F_|P]|J]) :- substFormula(X,Y,F,F_).
    rule(existL(Y),[[exist(X,F)|A]⊦P|J],[[F_|A]⊦P|J]) :- substFormula(X,Y,F,F_).
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

    substTerm(I,T,I,T) :- atom(I),!.
    substTerm(I,T,Is->E,Is->E_) :- \+member(I,Is),!,substTerm(I,T,E,E_).
    substTerm(I,T,E*Es,E_*Es_) :- !,maplist(substTerm(I,T),[E|Es],[E_|Es_]).
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
    beta(Xs,[]=>P,F_) :- beta(Xs,P,F_).
    beta([],Z=>P,_) :- throw(argumentsNotFullyApplied(Z=>P)).
    beta([X|Xs],[T|Ts]=>F,F_) :- sbterm(T,X,F,F1),beta(Xs,Ts=>F1,F_).
    beta([],F,F).
    beta(Xs,F) :- throw(cannotApplyToFormula(Xs,F)).
    sbterm(T,X,Ys=>F,Ys=>F_) :- sbterm(T,X,F,F_).
    sbterm(T,X,F,F_) :- substFormula(T,X,F,F_).

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

    com(apply(Rs)    ,G,J,R) :- ruleRun(Rs,J,J_),is_list(J_),!,R=(G,J_).
    com(apply(Rs)    ,_,J,R) :- ruleRun(Rs,J,E),!,R=comError(apply,E,J).
    com(noApply(R1)  ,G,J,R) :- ruleRun([R1],J,J_),is_list(J_),!,R=(G,J).
    com(noApply(R1)  ,_,J,R) :- ruleRun([R1],J,E),!,R=comError(noapply,E,J).
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

コマンドは規則を実行するapply,規則が動くことを確認するnoApply、定理を使って判断を増やすuse、判断のトップの置換をするinst、ユーザー定義コマンドを実行するcomがあります。ユーザー定義の組み込みコマンドにはdeferコマンドがありこれは最初の判断を最後に移動します。


## 宣言実行

    declRun(G,     [],G) :- is_dict(G).
    declRun(G, [D|Ds],R) :- is_dict(G),decl(D,G,R1),!,declRun(R1,Ds,R).
    declRun(E,      D,_) :- writeln('decl error':E;D),halt(1).

`declRun/3`は`ruleRun/4`, `comRun/3`と同様に宣言リストから宣言を１つ取り出して`decl/3`を呼び出しなくなるまで実行します。
宣言が空、あるいはエラーなら終了しますが宣言があれば次の宣言を実行します。

`decl/3`は宣言の１つを処理します:

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
    decl(Dec*Arg,G,R) :- member(Dec=Fun,G.decls),!,
                                  call(Fun,Arg,Ds),declRun(G,Ds,R).
    decl(D\ec*_,  _,R) :- !,R=error(Dec,noSuchDecl(Dec)).


importは他のclファイルを読み込みます。
constantは定数宣言でtypesに名前とそれに対応する型を追加します。
axiomは公理の宣言で、型推論`infer/2`を呼び出しその後、`insertThm/2`で環境に公理を保存します。公理は証明が必要ない命題なので証明はありません。
theoremは定理の宣言で、公理と同様に型推論`infer/2`を呼び、`insertThm/2`で環境に定理を保存します。定理は証明が必要なので`comRun/3`と同様にコマンドを処理する`proofRun/4`を実行します。`proofRun/4`は正常終了時に行う処理を渡します。
plFileはPrologのファイルを読み込む命令です。プラグインとしてuse_moduleを用いて読み込み、環境に組み込みます。
decl*[argumet]はユーザーが定義した宣言を`declRun/3`を用いて実行します。

    proofRun((G,[]),    _,N,R) :- !,call(N,G,R),!.
    proofRun((_,J),    [],_,R) :- !,R=proofNotFinished(J).
    proofRun((G,J),[C|Cs],N,R) :- !,com(C,G,J,R1),!,proofRun(R1,Cs,N,R).
    proofRun(Err,       _,_,R) :- !,R=Err.

`proofRun/4` は証明を実行するためのコマンドを実行します。 `comRun/3` に似ていますが、動作が異なります。
判断がなくなれば終了コマンド`N/2`を実行し、
判断は残っているのにコマンドがなくなった場合は証明終わっていないことを返します。
エラーが帰ってきた場合はエラーをそのまま返却します。

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

`insertThm/4` は定理を環境に保存するのですがその際は環境にない述語を`metagen/3`を用いて述語の名前に`?`を付けます。

## 型検査 infer

型検査機は通常のラムダ計算に、論理式を扱えるように拡張したものです。

    newVarT(C1) :- bb_get(cnt,C),C1 is C + 1,bb_put(cnt,C1).

`newVarT/1`はグローバルな変数を使ってユニークな型変数を返します。

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

論理式の型は決まっているのでただトラバースするだけです。 `-->/2`を用いている箇所はDCGの記法を用いています。

    inferTerm(G,V,T_,S,S) :- atom(V),member(V=T,G),!,instantiate(T,T_).
    inferTerm(_,V,T,S,S) :- atom(V),bb_get(ctx,Ctx),member(V=T,Ctx).
    inferTerm(_,V,T,S,S) :- atom(V),newVarT(T),bb_update(ctx,Ctx,[V=T|Ctx]).
    inferTerm(G,Xs->E,T,S,S_) :-
      foldl([X1,XTs1,[X1=T1|XTs1]]>>newVarT(T1),Xs,[],XTs),
      bb_get(ctx,Ctx),foldl([X=T,Ctx1,[X=T|Ctx1]]>>!,XTs,Ctx,Ctx_),bb_put(ctx,Ctx_),
      inferTerm(G,E,T2,S,S1),
      bb_get(ctx,Ctx2),foldl([X,Ctx3,Ctx3_]>>select(X=_,Ctx3,Ctx3_),Xs,Ctx2,Ctx2_),bb_put(ctx,Ctx2_),
      newVarT(T),foldl([_=T3,T21,(T3->T21)]>>!,XTs,T2,T2_),unify((T2_,T),S1,S_).
    inferTerm(G,E*Es,T,S,S5) :-
      inferTerm(G,E,T1,S,S1),!,
      foldl([E2,(Ts2,S2),([T2|Ts2],S3)]>>inferTerm(G,E2,T2,S2,S3),Es,([],S1),(Ts,S4)),
      newVarT(T),foldl([T3,T4,(T3->T4)]>>!,Ts,T,T2),unify((T1,T2),S4,S5).

ラムダ項の推論は基本的なものです。

    varT(A) :- integer(A);atom(A),A\=prop.
    instantiate(T,T_) :- inst(T,T_,[],_),!.
    inst(I,T,C,C) :- varT(I),member(I=T,C).
    inst(I,T,C,[I=T|C]) :- newVarT(T).
    inst(prop,prop,C,C).
    inst(X->Y,X_->Y_) --> inst(X,X_),inst(Y,Y_).
    inst(Cn*[],Cn*[],C,C).
    inst(Cn*[X|Xs],Cn*[X_|Xs_]) --> inst(X,X_),inst(Cn*Xs,Cn*Xs_).

環境にある変数は参照された場合に具体化されます。

    unify((X,X)) --> {!}.
    unify((I,T),S,S_) :- varT(I),member(I=T1,S),unify((T1,T),S,S_).
    unify((I,T)) --> {varT(I),occurs(I,T)},union([I,T]).
    unify((T,I)) --> {varT(I)},unify((I,T)).
    unify((C*Xs,C*Ys)) --> {maplist(unify1,Xs,Ys,XYs)},foldl(unify,XYs).
    unify(((X1->X2),(Y1->Y2))) --> unify((X1,Y1)),unify((X2,Y2)).
    unify((X,Y)) --> {throw(unificationFailed(X,Y))}.
    unify1(X,Y,(X,Y)).
    occurs(T,I,I) :- varT(I),throw(unificationFailed(I, T)).
    occurs(T,I,_*Ts) :- maplist(occurs(T,I),Ts).
    occurs(T,I,T1->T2) :- occurs(T,I,T1),occurs(T,I,T2).
    occurs(_,_,_).
    occurs(I,T) :- occurs(T,I,T),!.

`unify/4`は型と型が同じであるという方程式を生成します。同じ型ならなにもしませんが、型変数と他の型があれば、その型の中身に型変数が出現しないか`occurs/3`で確認してから方程式に追加します。

以上でメインプログラム `pcla.pl` を全て見ました。

## ユーザー定義宣言

外部ファイルを記述するには`export_decl/1`と`export_command/1`に定義した述語名を記述します。

    export_decl([definition]).

export_declは宣言の定義です。

definition

    definition([n(I:Typ),p([predFml(Body)])],[constant(I,Typ),axiom(I2,Body)]) :-
      format(atom(I2),'~w_def',[I]).
    definition(Arg,_) :- throw(wrongArgument(Arg)).

## ユーザー定義コマンド

ユーザー定義コマンドはPrologのプログラムで追加できるコマンドです。
追加するには`export_command/1`に以下のように定義します:

    export_command([assumption,implyR,implyL,genR,genL,absL]).

assumptionのコマンドは以下のように定義されています:

    :- module('lib/commands',[]).

    replicate(0,_,[]).
    replicate(N,V,[V|Vs]) :- N1 is N - 1, replicate(N1,V,Vs).
    findIndex(F,Ls,R) :- findIndex1(F,0,Ls,R).
    findIndex1(F,N,[X|_],N) :- call(F,X),!.
    findIndex1(F,N,[_|Xs],R) :- N1 is N + 1, findIndex1(F,N1,Xs,R).
    elemIndex(E,Ls,R) :- findIndex(=(E),Ls,R).
    onlyL(I,N,Rs) :-
      replicate(I,[wL],R1),NI1 is N-I-1,replicate(NI1,[pL(1),wL],R2),append(R1,R2,R3),append(R3,Rs).
    onlyR(I,N,Rs) :-
      replicate(I,[wR],R1),NI1 is N-I-1,replicate(NI1,[pR(1),wR],R2),append(R1,R2,R3),append(R3,Rs).
    assumption(_,[],[(Assms⊦Props)|_],[apply(Rs)]) :-
      findIndex([A]>>member(A,Assms),Props,I),!,
      nth0(I,Props,I2),elemIndex(I2,Assms,J),!,
      length(Props,Pi),length(Assms,Aj),
      onlyR(I,Pi,Ps),onlyL(J,Aj,As),append([Ps,As,[i]],Rs).
    assumption(_,[],[(Assms⊦Props)|Js],_) :- throw(cannotSolve([(Assms⊦Props)|Js])).
    assumption(_,_,_,_) :- throw(wrongArgument([])).

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
      apply([forallL(I)]),
      com(assumption, []),
      apply([pR(1), wR])
    ]) :- !.
    genR(_,Arg,Js,_) :- throw(wrongArgument(Arg,Js)).

genL

    genL(_,i([(I,[])]),[[P|Ps] ⊦ _ |_],[
      apply([cut(forall(I, P))]),
      apply([forallR(I)]),
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

- TODO 命令の意味

## todo 読者目線で見ることを考えてこの文書を改善する

- 命令の意味がわからない
- Prologの難しい機能使わんでくれ
    - 説明しよう
- 抽象構文に、静的型付けするための無駄なネストがあるので消したことを書く

## ライセンス

MIT Licence

## 参考

[1] https://qiita.com/advent-calendar/2017/myuon_myon_cs

[2] The Isabelle/Isar Implementation
https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2017/doc/implementation.pdf
