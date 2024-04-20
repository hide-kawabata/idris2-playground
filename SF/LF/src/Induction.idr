%default total
{- Induction -}

-- Proof by Induction

add_0_r : (n : Nat) -> n + 0 = n
add_0_r 0 = Refl
add_0_r (S n') = let IHn = add_0_r n' in rewrite IHn in Refl

minus_n_n : (n : Nat) -> minus n n = 0
minus_n_n 0 = Refl
minus_n_n (S n') = let IHn = minus_n_n n' in rewrite IHn in Refl

-- Exercise
mul_O_r : (n : Nat) -> n * 0 = 0
mul_O_r 0 = Refl
mul_O_r (S n') = mul_O_r n'

plus_n_Sm : (n : Nat) -> (m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm 0 m = Refl
plus_n_Sm (S n') 0 = let ih = plus_n_Sm n' 0 in rewrite ih in Refl
plus_n_Sm (S n') (S m') = let ih = plus_n_Sm n' (S m') in
                          rewrite ih in Refl
add_comm : (n : Nat) -> (m : Nat) -> n + m = m + n
add_comm 0 0 = Refl
add_comm 0 (S m') = rewrite add_comm m' 0 in Refl
add_comm (S n') m = rewrite add_comm n' m in
                    rewrite plus_n_Sm m n' in Refl
add_assoc : (n : Nat) -> (m : Nat) -> (p : Nat) -> n + (m + p) = (n + m) + p
add_assoc 0 m p = Refl
add_assoc (S k) m p = rewrite add_assoc k m p in Refl

-- Exercise
double : (n : Nat) -> Nat
double 0 = 0
double (S n') = S (S (double n'))
double_plus : (n : Nat) -> double n = n + n
double_plus 0 = Refl
double_plus (S n') = 
  rewrite (sym $ plus_n_Sm n' n') in rewrite double_plus n' in Refl

-- Exercise
eqb_refl : (n : Nat) -> (n == n) = True
eqb_refl 0 = Refl
eqb_refl (S n') = eqb_refl n'

-- Exercise
negb : (b : Bool) -> Bool
negb True = False
negb False = True
even, odd : (n : Nat) -> Bool
even 0 = True
even (S n') = odd n'
odd 0 = False
odd (S n') = even n'
even_S : (n : Nat) -> even (S n) = negb (even n)
even_S 0 = Refl
even_S (S 0) = Refl
even_S (S (S n')) = even_S n'

-- Proof Within Proofs

h : (n : Nat) -> n + 0 + 0 = n
h 0 = Refl
h (S n') = let ih = h n' in rewrite ih in Refl

mult_0_plus' : (n : Nat) -> (m : Nat) -> (n + 0 + 0) * m = n * m
mult_0_plus' n m = rewrite h n in Refl


plus_rearrange : (n : Nat) -> (m : Nat) -> (p : Nat) -> (q : Nat) -> 
  (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange n m p q = rewrite add_comm n m in Refl

-- More Exercises

-- Exercise
add_shuffle3 : (n : Nat) -> (m : Nat) -> (p : Nat) -> n + (m + p) = m + (n + p)
add_shuffle3 n m p = rewrite add_assoc n m p in
                     rewrite add_comm n m in 
                     rewrite add_assoc m n p in Refl
partial
mul_comm : (m : Nat) -> (n : Nat) -> m * n = n * m
mul_comm 0 0 = Refl
mul_comm 0 (S n') = mul_comm 0 n'
mul_comm (S m') n = rewrite mul_comm n (S m') in Refl -- <=====
total
mul_t : (n : Nat) -> (m' : Nat) -> plus n (mult n m') = mult n (S m')
mul_t 0 m' = Refl
mul_t (S n') m' = 
  let ih = sym (mul_t n' m') in
  rewrite ih in
  rewrite add_assoc n' m' (mult n' m') in 
  rewrite add_assoc m' n' (mult n' m') in 
  rewrite add_comm n' m' in
  cong S Refl
total
mul_comm' : (m : Nat) -> (n : Nat) -> m * n = n * m
mul_comm' 0 0 = Refl
mul_comm' 0 (S n') = mul_comm' 0 n'
mul_comm' (S m') n = rewrite mul_comm' m' n in mul_t n m'

total
leb : (n : Nat) -> (m : Nat) -> Bool
leb 0 m = True
leb (S n') 0 = False
leb (S n') (S m') = leb n' m'
plus_leb_compat_l : (n : Nat) -> (m : Nat) -> (p : Nat) ->
  n <= m = True -> (p + n) <= (p + m) = True
plus_leb_compat_l n m 0 prf = prf
plus_leb_compat_l n m (S p') prf = plus_leb_compat_l n m p' prf

-- Exercise
leb_refl : (n : Nat) -> (n <= n) = True
leb_refl 0 = Refl
leb_refl (S n') = leb_refl n'
zero_neqb_S : (n : Nat) -> 0 == (S n) = False
zero_neqb_S n = Refl
andb : (b1 : Bool) -> (b2 : Bool) -> Bool
andb False b2 = False
andb True b2 = b2
andb_false_r : (b : Bool) -> andb b False = False
andb_false_r False = Refl
andb_false_r True = Refl

-- Nat to Bin and Back to Nat

data Bin : Type where
  Z : Bin
  B0 : (n : Bin) -> Bin
  B1 : (n : Bin) -> Bin

implementation Eq Bin where
  Z == Z = True
  B0 n == B0 m = n == m
  B1 n == B1 m = n == m
  _ == _ = False

total
incr : (m : Bin) -> Bin
incr Z = B1 Z
incr (B0 m') = B1 m'
incr (B1 m') = B0 (incr m')

total
bin_to_nat : (m : Bin) -> Nat
bin_to_nat Z = 0
bin_to_nat (B0 n) = let n' = bin_to_nat n in n' + n'
bin_to_nat (B1 n) = let n' = bin_to_nat n in 1 + n' + n'
{-
bin_to_nat (B0 n) = let n' = bin_to_nat n in n' * 2
bin_to_nat (B1 n) = let n' = bin_to_nat n in n' * 2 + 1
-}

test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z)
test_bin_incr1 = Refl
test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z)
test_bin_incr2 = Refl
test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z))
test_bin_incr3 = Refl
test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2
test_bin_incr4 = Refl
test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z)
test_bin_incr5 = Refl
test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z)
test_bin_incr6 = Refl

bin_to_nat_pres_incr : (b : Bin) -> bin_to_nat (incr b) = 1 + bin_to_nat b
bin_to_nat_pres_incr Z = Refl
bin_to_nat_pres_incr (B0 n) = cong S Refl
bin_to_nat_pres_incr (B1 n) =
  rewrite (bin_to_nat_pres_incr n) in
  rewrite (plus_n_Sm (bin_to_nat n) (bin_to_nat n)) in
  Refl

-- Exercise
nat_to_bin : (n : Nat) -> Bin
nat_to_bin 0 = Z
nat_to_bin (S n') = let b = nat_to_bin n' in incr b
nat_bin_nat : (n : Nat) -> bin_to_nat (nat_to_bin n) = n
nat_bin_nat 0 = Refl
nat_bin_nat (S n') =
  rewrite bin_to_nat_pres_incr (nat_to_bin n') in 
  rewrite nat_bin_nat n' in
  Refl

-- Bin to Nat and Back to Bin (Advanced)

{-
bin_nat_bin_fails : (b : Bin) -> nat_to_bin (bin_to_nat b) = b
-}

-- Exercise
double_incr : (n : Nat) -> double (S n) = S (S (double n))
double_incr 0 = Refl
double_incr (S n') = Refl
double_bin : (b : Bin) -> Bin
double_bin Z = Z
double_bin (B0 n) = B0 (B0 n)
double_bin (B1 n) = B0 (B1 n)
double_bin_zero : double_bin Z = Z
double_bin_zero = Refl
double_incr_bin : (b : Bin) -> double_bin (incr b) = incr (incr (double_bin b))
double_incr_bin Z = Refl
double_incr_bin (B0 n) = Refl
double_incr_bin (B1 n) = Refl

-- Exercise
normalize : (b : Bin) -> Bin
normalize Z = Z
normalize (B0 b') = case (normalize b') of
  Z => Z
  r@_ => B0 r
normalize (B1 b') = B1 (normalize b')
