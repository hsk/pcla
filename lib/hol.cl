import('lib/preliminaries.cl').

% imply,eq
constant(imp,conT(bool,[]) -> conT(bool,[]) -> conT(bool,[])).
constant(eqt,varT(a) ->varT(a) -> conT(bool,[])).

% connectives & quantifiers

newDecl(definition,[
  n(true : conT(bool,[])),
  p([predFml(pred(eq,[
    !true,
    !eqt$[fun([x],!x),fun([x],!x)]
  ]))])
]).
newDecl(definition,[
  n( all: ((varT(a) -> conT(bool,[])) -> conT(bool,[]))),
  p([predFml(pred(eq,[
    !all$[!'P'],
    !eqt$[!'P',fun([x],!true)]
  ]))])
]).
newDecl(definition,[
  n( ex: ((varT(a) -> conT(bool,[])) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    !ex$[!'P'],
    !all$[fun(['Q'],
      !imp$[
        !all$[fun([x],
          !imp$[
            !'P'$[!x],
            !'Q'])],
        !'Q'])]]))])]).
newDecl(definition,[
  n( false: conT(bool,[]) ),
  p([predFml(pred(eq,[
    !false,!all$[fun(['P'],!'P')]
  ]))])
]).
newDecl(definition,[
  n( not: (conT(bool,[]) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    !not$[!'P'],
    !imp$[!'P',!false]
  ]))])
]).
newDecl(definition,[
  n( and: (conT(bool,[]) -> conT(bool,[]) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    !and$[!'P',!'Q'],
    !all$[fun(['R'],
      !imp$[
        !imp$[
          !'P',
          !imp$[!'Q',!'R']],
        !'R'])]]))])]).
newDecl(definition,[
  n( or: (conT(bool,[]) -> conT(bool,[]) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    !or$[!'P',!'Q'],
    !all$[fun(['R'],
      !imp$[
        !imp$[!'P',!'R'],
        !imp$[
          !imp$[!'Q',!'R'],
          !'R']])]]))])]).
newDecl(definition,[
  n( iff: (conT(bool,[]) -> conT(bool,[]) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    !iff$[!'P',!'Q'],
    !eqt$[!'P',!'Q']]))])]).
%axiom eqrefl: eq(eqt(t,t),true)
axiom(eqrefl,pred(eq,[!eqt$[!t,!t],!true])).
%axiom eqsubst: eq(eqt(s,t),true) ==> P(s) ==> P(t)
axiom(eqsubst,pred(eq,[!eqt$[!s,!t],!true]) ==> pred('P',[!s]) ==> pred('P',[!t])).
%axiom eqext: (Forall x. eq(eqt(f(x),g(x)),true)) ==> eq(eqt(x => f(x),x => g(x)),true)
axiom(eqext,
  forall(x,pred(eq,[!eqt$[!f$[!x],!g$[!x]],!true])) ==>
  pred(eq,[!eqt$[fun([x],!f$[!x]),fun([x],!g$[!x])],!true])).
%axiom impI: (eq(eqt(P,true),true) ==> eq(eqt(Q,true),true)) ==> eq(imp(P,Q),true)
axiom(impI,
  (pred(eq,[!eqt$[!'P',!true],!true]) ==>
   pred(eq,[!eqt$[!'Q',!true],!true])) ==>
   pred(eq,[!imp$[!'P',!'Q'],!true])).
%axiom mp: eq(imp(P,Q),true) ==> eq(P,true) ==> eq(Q,true)
axiom(mp,
  pred(eq,[!imp$[!'P',!'Q'],!true]) ==>
  pred(eq,[!'P',!true]) ==>
  pred(eq,[!'Q',!true])).
%axiom iff: eq(imp(imp(P,Q),imp(imp(Q,P),eqt(P,Q))),true)
axiom(iff,
  pred(eq,[
    !imp$[
      !imp$[!'P',!'Q'],
      !imp$[
        !imp$[!'Q',!'P'],
        !eqt$[!'P',!'Q']]],
    !true])).
%axiom True_or_False: eq(or(eqt(P,true),eqt(P,false)),true)
axiom('True_or_False',
  pred(eq,[
    !or$[
      !eqt$[!'P',!true],
      !eqt$[!'P',!false]],
    !true])).

% fundamental rules

%% equality

theorem(eqsym,pred(eq,[!eqt$[!s,!t],!true]) ==> pred(eq,[!eqt$[!t,!s],!true]),
  proof([
    apply([impR]),
    newCommand(implyL,i([(eqsubst,['P':
      predFun([x],predFml(pred(eq,[!eqt$[!x,!s],!true])))])])),
    newCommand(implyR,[]),
    use(eqrefl,[]),
    newCommand(genR,i([(s,[])])),
    apply([forallR(t)]),
    apply([i])
  ])).

theorem(eqssubst,pred(eq,[!eqt$[!t,!s],!true]) ==> pred('P',[!s]) ==> pred('P',[!t]),
  proof([
    newCommand(genR,i([(s,[])])),
    newCommand(genR,i([(t,[])])),
    apply([forallR(r),forallR(t)]),
    newCommand(genR,i([(r,[])])),
    apply([forallR(s),impR]),
    newCommand(implyL,i([(eqsym,[])])),
    newCommand(absL,[]),
    newCommand(genR,i([(s,[])])),
    newCommand(genR,i([(t,[])])),
    apply([forallR(r),forallR(t)]),
    newCommand(genR,i([(r,[])])),
    apply([forallR(s)]),
    use(eqsubst,['P': predFun([x],predFml(pred('P',[!x])))]),
    apply([i])
  ])).
