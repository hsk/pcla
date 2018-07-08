import('lib/preliminaries.cl').

% imply, eq
constant(imp,conT(bool, []) -> conT(bool, []) -> conT(bool, [])).
constant(eqt,varT(a) ->varT(a) -> conT(bool,[])).

% connectives & quantifiers

newDecl(definition,[
  n(true : conT(bool,[])),
  p([predFml(pred(eq,[
    var(true),
    app(var(eqt),[abs([x],var(x)), abs([x],var(x))])
  ]))])
]).
newDecl(definition,[
  n( all: ((varT(a) -> conT(bool,[])) -> conT(bool,[]))),
  p([predFml(pred(eq,[
    app(var(all),[var('P')]),
    app(var(eqt),[var('P'),abs([x], var(true))])
  ]))])
]).
newDecl(definition,[
  n( ex: ((varT(a) -> conT(bool,[])) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    app(var(ex),[var('P')]),
    app(var(all),[abs(['Q'],
      app(var(imp),[
        app(var(all),[abs([x],
          app(var(imp),[
            app(var('P'),[var(x)]),
            var('Q')]))]),
        var('Q')]))])]))])]).
newDecl(definition,[
  n( false: conT(bool,[]) ),
  p([predFml(pred(eq,[
    var(false), app(var(all),[abs(['P'], var('P'))])
  ]))])
]).
newDecl(definition,[
  n( not: (conT(bool,[]) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    app(var(not),[var('P')]),
    app(var(imp),[var('P'),var(false)])
  ]))])
]).
newDecl(definition,[
  n( and: (conT(bool,[]) -> conT(bool,[]) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    app(var(and),[var('P'),var('Q')]),
    app(var(all),[abs(['R'],
      app(var(imp),[
        app(var(imp),[
          var('P'),
          app(var(imp),[var('Q'),var('R')])]),
        var('R')]))])]))])]).
newDecl(definition,[
  n( or: (conT(bool,[]) -> conT(bool,[]) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    app(var(or),[var('P'),var('Q')]),
    app(var(all),[abs(['R'],
      app(var(imp),[
        app(var(imp),[var('P'),var('R')]),
        app(var(imp),[
          app(var(imp),[var('Q'),var('R')]),
          var('R')])]))])]))])]).
newDecl(definition,[
  n( iff: (conT(bool,[]) -> conT(bool,[]) -> conT(bool,[])) ),
  p([predFml(pred(eq,[
    app(var(iff),[var('P'),var('Q')]),
    app(var(eqt),[var('P'),var('Q')])]))])]).
%axiom eqrefl: eq(eqt(t,t),true)
axiom(eqrefl,pred(eq,[app(var(eqt),[var(t),var(t)]),var(true)])).
%axiom eqsubst: eq(eqt(s,t),true) ==> P(s) ==> P(t)
axiom(eqsubst, pred(eq,[app(var(eqt),[var(s),var(t)]),var(true)]) ==> pred('P',[var(s)]) ==> pred('P',[var(t)])).
%axiom eqext: (Forall x. eq(eqt(f(x),g(x)),true)) ==> eq(eqt(x => f(x), x => g(x)),true)
axiom(eqext,
  forall(x, pred(eq,[app(var(eqt),[app(var(f),[var(x)]),app(var(g),[var(x)])]),var(true)])) ==>
  pred(eq,[app(var(eqt),[abs([x], app(var(f),[var(x)])), abs([x], app(var(g),[var(x)]))]),var(true)])).
%axiom impI: (eq(eqt(P,true),true) ==> eq(eqt(Q,true),true)) ==> eq(imp(P,Q),true)
axiom(impI,
  (pred(eq,[app(var(eqt),[var('P'),var(true)]),var(true)]) ==>
   pred(eq,[app(var(eqt),[var('Q'),var(true)]),var(true)])) ==>
   pred(eq,[app(var(imp),[var('P'),var('Q')]),var(true)])).
%axiom mp: eq(imp(P,Q),true) ==> eq(P,true) ==> eq(Q,true)
axiom(mp,
  pred(eq,[app(var(imp),[var('P'),var('Q')]),var(true)]) ==>
  pred(eq,[var('P'),var(true)]) ==>
  pred(eq,[var('Q'),var(true)])).
%axiom iff: eq(imp(imp(P,Q),imp(imp(Q,P),eqt(P,Q))),true)
axiom(iff,
  pred(eq,[
    app(var(imp),[
      app(var(imp),[var('P'),var('Q')]),
      app(var(imp),[
        app(var(imp),[var('Q'),var('P')]),
        app(var(eqt),[var('P'),var('Q')])])]),
    var(true)])).
%axiom True_or_False: eq(or(eqt(P,true),eqt(P,false)),true)
axiom('True_or_False',
  pred(eq,[
    app(var(or),[
      app(var(eqt),[var('P'),var(true)]),
      app(var(eqt),[var('P'),var(false)])]),
    var(true)])).

% fundamental rules

%% equality

theorem(eqsym, pred(eq,[app(var(eqt),[var(s),var(t)]),var(true)]) ==> pred(eq,[app(var(eqt),[var(t),var(s)]),var(true)]),
  proof([
    apply([impR]),
    newCommand(implyL, i([(eqsubst, ['P':
      predFun([x],predFml(pred(eq,[app(var(eqt),[var(x),var(s)]),var(true)])))])])),
    newCommand(implyR,[]),
    use(eqrefl,[]),
    newCommand(genR, i([(s,[])])),
    apply([forallR(t)]),
    apply([i])
  ])).

theorem(eqssubst, pred(eq,[app(var(eqt),[var(t),var(s)]),var(true)]) ==> pred('P',[var(s)]) ==> pred('P',[var(t)]),
  proof([
    newCommand(genR, i([(s,[])])),
    newCommand(genR, i([(t,[])])),
    apply([forallR(r), forallR(t)]),
    newCommand(genR, i([(r,[])])),
    apply([forallR(s), impR]),
    newCommand(implyL,i([(eqsym,[])])),
    newCommand(absL,[]),
    newCommand(genR, i([(s,[])])),
    newCommand(genR, i([(t,[])])),
    apply([forallR(r), forallR(t)]),
    newCommand(genR, i([(r,[])])),
    apply([forallR(s)]),
    use(eqsubst, ['P': predFun([x], predFml(pred('P',[var(x)])))]),
    apply([i])
  ])).
