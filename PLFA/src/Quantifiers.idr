%default total

forallElim : {a : Type} -> {b : a -> Type}
             -> (l : (x : a) -> b x) -> (m : a) -> b m
forallElim l m = l m

existsElim : {a : Type} -> {b : a -> Type} -> {c : Type}
             -> ((x : a) -> b x -> c) -> (x ** b x) -> c
existsElim f (x ** bx) = f x bx
