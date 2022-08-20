import Data.Vect

{- lemma for rewriting -}
total plusSuc : (m : Nat) -> (n : Nat) -> m + (S n) = S (m + n)
plusSuc 0 n = Refl                                             
plusSuc (S m') n = cong S (rewrite plusSuc m' n in Refl)

{- type rewriter -}
tt : Vect (plus len (S n)) a -> Vect (S (plus len n)) a
tt xs = rewrite plusSuccRightSucc len n in xs

{- reverses a vector using an accumulator : vrevacc0 [1,2,3] [] => [3,2,1] -}
vrevacc0 : {m : Nat} -> {n : Nat} -> (Vect m a) -> (Vect n a) -> Vect (m + n) a
vrevacc0 [] ys = ys
--vrevacc0 (x :: xs') ys = ?vrevacc0_rhs -- (1) goal : vrevacc0_rhs : Vect (S (plus len n)) a (why len?)
--vrevacc0 (x :: xs') ys = vrevacc0 xs' (x :: ys) -- (2) need to change the index from plus len (S n) and S (plus len n)
vrevacc0 (x :: xs') ys = tt $ vrevacc0 xs' (x :: ys) -- (3) OK
--vrevacc0 (x :: xs') ys = rewrite plusSuccRightSucc m n in vrevacc0 xs' (x :: ys) -- (4) NG (why?)
--vrevacc0 (x :: xs') ys = rewrite sym $ plusSuc m n in vrevacc0 xs' (x :: ys) -- (5) NG (why?)

