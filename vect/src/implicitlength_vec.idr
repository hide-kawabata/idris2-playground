import Data.Nat

{- definition of Vec (not Vect) -}
data Vec : (n : Nat) -> (a : Type) -> Type where
     Vnil : Vec 0 a
     Vcons : a -> Vec n a -> Vec (S n) a

{- lemma for rewriting -}
total plusSuc : (m : Nat) -> (n : Nat) -> m + (S n) = S (m + n)
plusSuc 0 n = Refl
plusSuc (S m') n = cong S (rewrite plusSuc m' n in Refl)

{- type rewriter -}
tt0 : Vec (plus len (S n)) a -> Vec (S (plus len n)) a
tt0 xs = rewrite plusSuccRightSucc len n in xs
--tt0 xs = rewrite sym $ plusSuc len n in xs

{- reverse a vector using an accumulator -}
{- vrevacc (Vcons 1 (Vcons 2 (Vcons 3 Vnil))) => (Vcons 3 (Vcons 2 (Vcons 1 Vnil))) -}
vrevacc : {m : Nat} -> {n : Nat} -> Vec m a -> Vec n a -> Vec (m + n) a
vrevacc Vnil ys = ys
--vrevacc (Vcons x xs') ys = ?vrevacc_rhs -- (1) goal : vrevacc_rhs : Vec (S (plus n n)) a (why?)
--vrevacc (Vcons x xs') ys = vrevacc xs' (Vcons x ys) -- (2) need to change the index from plus n (S n) to S (plus n n)
vrevacc (Vcons x xs') ys = tt0 $ vrevacc xs' (Vcons x ys) -- (3) OK
--vrevacc (Vcons x xs') ys = rewrite plusSuccRightSucc m n in vrevacc xs' (Vcons x ys) -- (4) NG (why?)
--vrevacc (Vcons x xs') ys = rewrite sym $ plusSuc m n in vrevacc xs' (Vcons x ys) -- (5) NG (why?)

