%default total

b : Bool -> Nat
b True = 1
b _ = 2

d : Double -> Nat
d 1.5 = 1
d _ = 2

n : Nat -> Nat
n 8 = 200
n (S m) = m
n _ = 100
