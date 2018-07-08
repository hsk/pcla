plFile('lib/commands').
constant(eq,varT(a)->varT(a)->prop).
axiom(refl, pred(eq,[!r,!r])).
axiom(subst, pred(eq,[!a,!b]) ==> pred('P',[!a]) ==> pred('P',[!b])).
theorem(sym, pred(eq,[!r,!s]) ==> pred(eq,[!s,!r]),proof([
  apply([impR]),
  apply([cut(forall(a,forall(b, pred(eq,[!a,!b]) ==> pred(eq,[!a,!a]) ==> pred(eq,[!b,!a]))))]),
  use(subst),
  apply([forallR(a), forallR(b)]),
  inst('P', predFun([x],predFml(pred(eq,[!x,!a])))),
  newCommand(assumption,[]),
  apply([forallL(!r), forallL(!s)]),
  apply([impL]),
  newCommand(assumption,[]),
  apply([impL]),
  use(refl),
  newCommand(assumption,[]),
  newCommand(assumption,[])
])).

theorem(trans, pred(eq,[!r,!s]) ==> pred(eq,[!s,!t]) ==> pred(eq,[!r,!t]),
proof([
  apply([impR, impR]),
  apply([cut(forall(a,forall(b,pred(eq,[!a,!b]) ==> pred(eq,[!r,!a]) ==> pred(eq,[!r,!b]))))]),
  use(subst),
  inst('P', predFun([x],predFml(pred(eq,[!r,!x])))),
  apply([forallR(a), forallR(b)]),
  newCommand(assumption,[]),
  apply([forallL(!s), forallL(!t)]),
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
