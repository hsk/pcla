plFile('lib/commands').
constant(eq,varT(a)->varT(a)->prop).
axiom(refl, pred(eq,[var(r),var(r)])).
axiom(subst, pred(eq,[var(a),var(b)]) ==> pred('P',[var(a)]) ==> pred('P',[var(b)])).
theorem(sym, pred(eq,[var(r),var(s)]) ==> pred(eq,[var(s),var(r)]),proof([
  apply([impR]),
  apply([cut(forall(a,forall(b, pred(eq,[var(a),var(b)]) ==> pred(eq,[var(a),var(a)]) ==> pred(eq,[var(b),var(a)]))))]),
  use(subst),
  apply([forallR(a), forallR(b)]),
  inst('P', predFun([x],predFml(pred(eq,[var(x),var(a)])))),
  newCommand(assumption,[]),
  apply([forallL(var(r)), forallL(var(s))]),
  apply([impL]),
  newCommand(assumption,[]),
  apply([impL]),
  use(refl),
  newCommand(assumption,[]),
  newCommand(assumption,[])
])).

theorem(trans, pred(eq,[var(r),var(s)]) ==> pred(eq,[var(s),var(t)]) ==> pred(eq,[var(r),var(t)]),
proof([
  apply([impR, impR]),
  apply([cut(forall(a,forall(b,pred(eq,[var(a),var(b)]) ==> pred(eq,[var(r),var(a)]) ==> pred(eq,[var(r),var(b)]))))]),
  use(subst),
  inst('P', predFun([x],predFml(pred(eq,[var(r),var(x)])))),
  apply([forallR(a), forallR(b)]),
  newCommand(assumption,[]),
  apply([forallL(var(s)), forallL(var(t))]),
  apply([impL]),
  newCommand(assumption,[]),
  apply([impL]),
  newCommand(assumption,[]),
  newCommand(assumption,[])
])).
plFile('lib/eqCommands').

%%%%%%%%

theorem('Curry',
  (pred('P',[]) ==> pred('Q',[]) ==> pred('R',[])) ==> (and(pred('P',[]), pred('Q',[])) ==> pred('R',[])),
proof([
  apply([impR, impR, pL(1), impL, andL1]),
  newCommand(assumption,[]),
  newCommand(implyR,[]),
  apply([andL2]),
  newCommand(assumption,[])
])).

theorem('Uncurry', (and(pred('P',[]), pred('Q',[])) ==> pred('R',[])) ==> (pred('P',[]) ==> pred('Q',[]) ==> pred('R',[])),
proof([
  apply([impR, impR, impR, pL(2)]),
  newCommand(implyR,[]),
  apply([andR]),
  newCommand(assumption,[]),
  newCommand(assumption,[])
])).
