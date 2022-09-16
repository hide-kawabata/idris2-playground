-- congruence
congApp : {a, b : Type} -> (f, g : a -> b) -> f = g -> ((x : a) -> f x = g x)
congApp f f Refl x = Refl

subst : {a : Type} -> {x, y : a} -> (p : a -> Type) -> x = y -> p x -> p y
subst p Refl px = px

-- Leibniz equality (incomplete)
lequal : {a : Type} -> (x, y : a) -> Type -- <==== no Type1
lequal {a} x y = (p : a -> Type) -> p x -> p y

reflLE : {a : Type} -> {x : a} -> lequal x x
reflLE p y = y

transLE : {a : Type} -> {x, y, z : a} -> lequal x y -> lequal y z -> lequal x z
transLE xy yz p px = yz p (xy p px)

symLE : {a : Type} -> {x, y : a} -> lequal x y -> lequal y x
symLE {a} {x} {y} xy p z = 
  let q : a -> Type
      q z = p z -> p x in
  let qx : q x
      qx = reflLE p in
  let qy : q y
      qy = xy q qx in
  ?asdf

mlequality_implies_lequality : {a : Type} -> {x, y : a} -> x = y -> lequal x y
mlequality_implies_lequality xy p = subst p xy

