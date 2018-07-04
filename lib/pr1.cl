Ml_file "Commands.ml"

# equality
constant eq: 'a => 'a => prop

axiom refl: eq(r,r)
axiom subst: eq(a,b) ==> P(a) ==> P(b)

theorem sym: eq(r,s) ==> eq(s,r)
proof
  apply ImpR
  apply Cut [Forall a. Forall b. eq(a,b) ==> eq(a,a) ==> eq(b,a)]
  use subst
  apply (ForallR a, ForallR b)
  inst P [x => eq(x,a)]
  assumption
  apply (ForallL [r], ForallL [s])
  apply ImpL
  assumption
  apply ImpL
  use refl
  assumption
  assumption
qed

theorem trans: eq(r,s) ==> eq(s,t) ==> eq(r,t)
proof
  apply (ImpR, ImpR)
  apply Cut [Forall a. Forall b. eq(a,b) ==> eq(r,a) ==> eq(r,b)]
  use subst
  inst P [x => eq(r,x)]
  apply (ForallR a, ForallR b)
  assumption
  apply (ForallL [s], ForallL [t])
  apply ImpL
  assumption
  apply ImpL
  assumption
  assumption
qed
