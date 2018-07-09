plFile('lib/commands').
constant(eq,varT(a)->varT(a)->prop).
axiom(refl, eq*[!r,!r]).
axiom(subst, eq*[!a,!b] ==> 'P'*[!a] ==> 'P'*[!b]).
theorem(sym, eq*[!r,!s] ==> eq*[!s,!r],proof([
  apply([impR]),
  apply([cut(forall(a,forall(b, eq*[!a,!b] ==> eq*[!a,!a] ==> eq*[!b,!a])))]),
  use(subst),
  apply([forallR(a), forallR(b)]),
  inst('P', predFun([x],predFml(eq*[!x,!a]))),
  newCommand(assumption,[]),
  apply([forallL(!r), forallL(!s)]),
  apply([impL]),
  newCommand(assumption,[]),
  apply([impL]),
  use(refl),
  newCommand(assumption,[]),
  newCommand(assumption,[])
])).

theorem(trans, eq*[!r,!s] ==> eq*[!s,!t] ==> eq*[!r,!t],
proof([
  apply([impR, impR]),
  apply([cut(forall(a,forall(b,eq*[!a,!b] ==> eq*[!r,!a] ==> eq*[!r,!b])))]),
  use(subst),
  inst('P', predFun([x],predFml(eq*[!r,!x]))),
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
  ('P'*[] ==> 'Q'*[] ==> 'R'*[]) ==> (and('P'*[], 'Q'*[]) ==> 'R'*[]),
proof([
  apply([impR, impR, pL(1), impL, andL1]),
  newCommand(assumption,[]),
  newCommand(implyR,[]),
  apply([andL2]),
  newCommand(assumption,[])
])).

theorem('Uncurry', (and('P'*[], 'Q'*[]) ==> 'R'*[]) ==> ('P'*[] ==> 'Q'*[] ==> 'R'*[]),
proof([
  apply([impR, impR, impR, pL(2)]),
  newCommand(implyR,[]),
  apply([andR]),
  newCommand(assumption,[]),
  newCommand(assumption,[])
])).
