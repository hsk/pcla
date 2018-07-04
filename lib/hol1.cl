Ml_file "Commands.ml"

# imply, eq
constant imp: bool => bool => bool
constant eqt: 'a => 'a => bool
constant eq: 'a => 'a => prop

axiom refl: eq(r,r)
axiom subst: eq(a,b) ==> P(a) ==> P(b)

# connectives & quantifiers
definition {
  n[ true: bool ];
  p[ eq(true, eqt(x => x, x => x)) ];
}

