module PeanoEtc

import Data.Nat -- Only a few of the following depends on this.

%default total

data Natural : Type where
    Zero : Natural
    Succ : Natural -> Natural

add_Natural : Natural -> Natural -> Natural
add_Natural Zero y = y                             ---   0 + y = y
add_Natural (Succ x) y = Succ (add_Natural x y)    ---  (S x) + y = S (x + y)

add_0_r : (n : Natural) -> add_Natural n Zero = n
add_0_r Zero = Refl
add_0_r (Succ x) =
  let IH = add_0_r x in
  rewrite IH in
  Refl

-- uses Nat
add_0_r' : (n : Nat) -> n + Z = n
add_0_r' n = plusZeroRightNeutral n -- requires Data.Nat

add_n_Sm : (n : Natural) -> (m : Natural) ->
  add_Natural n (Succ m) = Succ (add_Natural n m)
add_n_Sm Zero m = Refl
add_n_Sm (Succ n') m =
  let IH = add_n_Sm n' m in
  rewrite IH in 
  Refl

add_commutative : (n : Natural) -> (m : Natural) -> 
  add_Natural n m = add_Natural m n
add_commutative Zero m =
  let t = add_0_r m in
  rewrite t in
  Refl
add_commutative (Succ n') m =
  let t = add_n_Sm m n' in
  rewrite t in
  let IH = add_commutative n' m in
  rewrite IH in
  Refl

add_assoc : (m, n, o : Natural) -> 
  add_Natural m (add_Natural n o) = add_Natural (add_Natural m n) o
add_assoc Zero n o = Refl
add_assoc (Succ x) n o =
  let ih = add_assoc x n o in
  rewrite ih in 
  Refl

mul_Natural : (n : Natural) -> (m : Natural) -> Natural
mul_Natural Zero m = Zero
mul_Natural (Succ x) m = add_Natural (mul_Natural x m) m

mul_m_0 : (m : Natural) -> mul_Natural m Zero = Zero
mul_m_0 Zero = Refl
mul_m_0 (Succ x) = let IH = mul_m_0 x in rewrite IH in Refl

mul_m_Sn : (m, n : Natural) ->
  mul_Natural m (Succ n) = add_Natural m (mul_Natural m n)
mul_m_Sn Zero n = Refl
mul_m_Sn (Succ m) n = -- m*(n+1)+(n+1) = m+(m*n+n) + 1
  rewrite mul_m_Sn m n in -- m+m*n+(n+1) = m+(m*n+n) + 1
  rewrite sym $ add_assoc m (mul_Natural m n) (Succ n) in -- m+(m*n+(n+1)) = m+(m*n+n) + 1
  rewrite add_n_Sm (mul_Natural m n) n in -- m+(m*n+n + 1) = m+(m*n+n) + 1
  rewrite add_n_Sm m (add_Natural (mul_Natural m n) n) in -- m+(m*n+n) + 1 = m+(m*n+n) + 1
  Refl

mul_m_Sn' : (m, n : Natural) ->
  mul_Natural m (Succ n) = add_Natural (mul_Natural m n) m -- m*(n+1) = m*n + m
mul_m_Sn' Zero n = Refl
mul_m_Sn' (Succ x) n = -- (x*(n+1)) + (n+1) = (x*n + n) + (x+1)
  rewrite mul_m_Sn' x n in -- ((x*n) + x) + (n+1) = (x*n + n) + (x+1)
  rewrite add_n_Sm (add_Natural (mul_Natural x n) x) n in -- x*n+x+n + 1 = x*n+n+(x+1)
  rewrite add_n_Sm (add_Natural (mul_Natural x n) n) x in -- x*n+x+n + 1 = x*n+n+x + 1
  rewrite sym $ add_assoc (mul_Natural x n) x n in -- x*n+(x+n) + 1 = x*n+n+x + 1
  rewrite sym $ add_assoc (mul_Natural x n) n x in -- x*n+(x+n) + 1 = x*n+(n+x) + 1
  rewrite add_commutative x n in
  Refl

mul_comm : (n : Natural) -> (m : Natural) ->
  mul_Natural n m = mul_Natural m n
mul_comm Zero m = let t = mul_m_0 m in rewrite t in Refl
mul_comm (Succ x) Zero = mul_m_0 (Succ x)
mul_comm (Succ x) (Succ y) = -- (x*(y+1)) + (y+1) = (y*(x+1)) + (x+1)
  rewrite mul_m_Sn' x y in -- ((x*y)+x) + (y+1) = (y*(x+1)) + (x+1)
  rewrite mul_m_Sn' y x in -- ((x*y)+x) + (y+1) = ((y*x)+y) + (x+1)
  rewrite mul_comm y x in -- ((x*y)+x) + (y+1) = ((x*y)+y) + (x+1)
  rewrite add_n_Sm (add_Natural (mul_Natural x y) x) y in -- x*y+x+y + 1 = (x*y+y) + (x+1)
  rewrite add_n_Sm (add_Natural (mul_Natural x y) y) x in -- x*y+x+y + 1 = x*y+y+x + 1
  rewrite sym $ add_assoc (mul_Natural x y) x y in -- x*y+(x+y) + 1 = x*y+y+x + 1
  rewrite sym $ add_assoc (mul_Natural x y) y x in -- x*y+(x+y) + 1 = x*y+(y+x) + 1
  rewrite add_commutative x y in -- x*y+(y+x) + 1 = x*y+(y+x) + 1
  Refl

-----------------------------------------------------------

data NPair : (t1 : Type) -> (t2 : Type) -> Type where
  MkNPair : (n : t1) -> (m : t2) -> NPair t1 t2

data NEither : (t1 : Type) -> (t2 : Type) -> Type where
  NLeft : (n : t1) -> NEither t1 t2
  NRight : (m : t2) -> NEither t1 t2

a : NPair Natural Natural
a = MkNPair (Succ (Succ Zero)) (Zero)

x : Natural
x = Succ (Succ Zero)

-- uses Bool and Nat
y : NEither Bool Nat
y = NLeft True

-- uses Bool and Nat
y' : NEither Bool Nat
y' = NRight 3

