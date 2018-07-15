plFile('lib/commands').
constant(eq,a->a->prop).
axiom(refl, eq*[r,r]).
axiom(subst, eq*[a,b]==>'P'*[a]==>'P'*[b]).
theorem(sym, eq*[r,s]==>eq*[s,r],proof([
  apply([impR]),
  apply([cut(forall(a,forall(b, eq*[a,b]==>eq*[a,a]==>eq*[b,a])))]),
  use(subst),
  apply([forallR(a), forallR(b)]),
  inst('P',[x]=>eq*[x,a]),
  com(assumption,[]),
  apply([forallL(r), forallL(s)]),
  apply([impL]),
  com(assumption,[]),
  apply([impL]),
  use(refl),
  com(assumption,[]),
  com(assumption,[])
])).

theorem(trans, eq*[r,s]==>eq*[s,t]==>eq*[r,t],proof([
  apply([impR, impR]),
  apply([cut(forall(a,forall(b,eq*[a,b]==>eq*[r,a]==>eq*[r,b])))]),
  use(subst),
  inst('P',[x]=>eq*[r,x]),
  apply([forallR(a), forallR(b)]),
  com(assumption,[]),
  apply([forallL(s), forallL(t)]),
  apply([impL]),
  com(assumption,[]),
  apply([impL]),
  com(assumption,[]),
  com(assumption,[])
])).
plFile('lib/eqCommands').

%%%%%%%%

theorem('Curry',('P'*[]==>'Q'*[]==>'R'*[])==>(and('P'*[], 'Q'*[])==>'R'*[]),
proof([
  apply([impR, impR, pL(1), impL, andL1]),
  com(assumption,[]),
  com(implyR,[]),
  apply([andL2]),
  com(assumption,[])
])).

theorem('Uncurry',(and('P'*[], 'Q'*[])==>'R'*[])==>('P'*[]==>'Q'*[]==>'R'*[]),
proof([
  apply([impR, impR, impR, pL(2)]),
  com(implyR,[]),
  apply([andR]),
  com(assumption,[]),
  com(assumption,[])
])).
