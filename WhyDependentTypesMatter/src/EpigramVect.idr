{- Section 4 -}

%default total

data Vec : (n : Nat) -> (a : Type) -> Type where
     Vnil : Vec 0 a
     Vcons : (x : a) -> (xs : Vec n a) -> Vec (S n) a

vtail : (xs : Vec (S n) a) -> Vec n a
vtail (Vcons x xs) = xs

vapp : (fs : Vec n (s -> t)) -> (ss : Vec n s) -> Vec n t
vapp Vnil Vnil = Vnil
vapp (Vcons f fs') (Vcons s ss') = Vcons (f s) (vapp fs' ss')

vmap : (f : s -> t) -> (ss : Vec n s) -> Vec n t
vmap f Vnil = Vnil
vmap f (Vcons x xs) = Vcons (f x) (vmap f xs)

nadd : (m : Nat) -> (n : Nat) -> Nat
nadd 0 n = n
nadd (S k) n = S (nadd k n)

vconc : (xs : Vec m a) -> (ys : Vec n a) -> Vec (nadd m n) a
vconc Vnil ys = ys
vconc (Vcons x xs') ys = Vcons x (vconc xs' ys)

vecn : {n : Nat} -> (x : a) -> Vec n a
vecn {n = 0} x = Vnil
vecn {n = (S k)} x = Vcons x (vecn x)

vadd : (v : Vec n Int) -> (w : Vec n Int) -> Vec n Int
vadd Vnil Vnil = Vnil
vadd (Vcons x xs) (Vcons y ys) = Vcons (x + y) (vadd xs ys)

vinc : {n : Nat} -> (v : Vec n Int) -> Vec n Int
vinc v = let v1 = vecn 1 in
         vadd v v1

vmap2 : {n : Nat} -> (f : s -> t) -> (ss : Vec n s) -> Vec n t
vmap2 f ss = vapp (vecn f) ss

xpose : {i : Nat} -> {j : Nat} -> Vec i (Vec j a) -> Vec j (Vec i a)
xpose Vnil = vecn Vnil
xpose (Vcons xj xi'j) = vapp (vapp (vecn Vcons) xj) (xpose xi'j)

plusSuc : (m : Nat) -> (n : Nat) -> m + (S n) = S (m + n)
plusSuc 0 n = Refl
plusSuc (S m') n = cong S (rewrite plusSuc m' n in Refl)

{- Be careful of implicit variables -}
vrevacc : (xs : Vec m a) -> (ys : Vec n a) -> Vec (m + n) a
vrevacc {m = 0} {n = n} Vnil ys = ys
vrevacc {m = (S m')} {n = n} (Vcons x xs) ys = -- Vec (S (plus m' n)) a
  -- plus m' (S n) <--> S (plus m' n)
--  rewrite plusSuccRightSucc m' n in -- import Data.Nat
  rewrite sym $ plusSuc m' n in
  vrevacc xs (Vcons x ys)
