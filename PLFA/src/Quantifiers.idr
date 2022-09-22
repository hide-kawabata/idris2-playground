%default total

forallElim : {0 a : Type} -> {0 b : a -> Type}
             -> (l : (x : a) -> b x) -> (m : a) -> b m
forallElim l m = l m

existsElim : {0 a : Type} -> {0 b : a -> Type} -> {0 c : Type}
             -> ((x : a) -> b x -> c) -> (x ** b x) -> c
existsElim f (x ** bx) = f x bx
