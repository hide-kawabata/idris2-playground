import Data.Vect

replicate' : {n : _} -> a -> Vect n a
replicate' = replicate n

ex6 : Vect ? Bool
ex6 = replicate' {n = 2} True

ex6' : Vect ?hole Bool
ex6' = replicate' {n = 2} True
