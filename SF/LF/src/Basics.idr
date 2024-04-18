{- Basics -}

-- Introduction

-- Data and Functions

data Day : Type where
  Monday : Day
  Tuesday : Day
  Wednesday : Day
  Thursday : Day
  Friday : Day
  Saturday : Day
  Sunday : Day

total
next_weekday : (d : Day) -> Day
next_weekday Monday = Tuesday
next_weekday Tuesday = Wednesday
next_weekday Wednesday = Thursday
next_weekday Thursday = Friday
next_weekday Friday = Monday
next_weekday Saturday = Monday
next_weekday Sunday = Monday

test_next_weekday : next_weekday (next_weekday Saturday) = Tuesday
test_next_weekday = Refl

data MyBool : Type where
  MyTrue : MyBool
  MyFalse : MyBool

total
negb : (b : MyBool) -> MyBool
negb MyTrue = MyFalse
negb MyFalse = MyTrue

total
andb : (b1 : MyBool) -> (b2 : MyBool) -> MyBool
andb MyTrue b2 = b2
andb MyFalse b2 = MyFalse

total
orb : (b1 : MyBool) -> (b2 : MyBool) -> MyBool
orb MyTrue b2 = MyTrue
orb MyFalse b2 = b2

test_orb1 : (orb MyTrue MyFalse) = MyTrue
test_orb1 = Refl
test_orb2 : (orb MyFalse MyFalse) = MyFalse
test_orb2 = Refl
test_orb3 : (orb MyFalse MyTrue) = MyTrue
test_orb3 = Refl
test_orb4 : (orb MyTrue MyTrue) = MyTrue
test_orb4 = Refl

total
(&&) : MyBool -> MyBool -> MyBool
x && y = andb x y

total
(||) : MyBool -> MyBool -> MyBool
x || y = orb x y

test_orb5 : MyFalse || MyFalse || MyTrue = MyTrue
test_orb5 = Refl

total
negb' : (b : Bool) -> Bool
negb' b = if b then False else True

-- Exercise 1

total
nandb : (b1 : MyBool) -> (b2 : MyBool) -> MyBool
nandb b1 b2 = negb (andb b1 b2)

test_nandb1 : nandb MyTrue MyFalse = MyTrue
test_nandb1 = Refl

data RGB : Type where
  Red : RGB
  Green : RGB
  Blue : RGB

data Color : Type where
  Black : Color
  White : Color
  Primary : (p : RGB) -> Color

total
monochrome : (c : Color) -> MyBool
monochrome Black = MyTrue
monochrome White = MyTrue
monochrome (Primary p) = MyFalse

total
isRed : (c : Color) -> MyBool
isRed Black = MyFalse
isRed White = MyFalse
isRed (Primary Red) = MyTrue
isRed (Primary _) = MyFalse

data Bit : Type where
  B1 : Bit
  B0 : Bit

data Nybble : Type where
  Bits : Bit -> Bit -> Bit -> Bit -> Nybble

total
all_zero : (nb : Nybble) -> MyBool
all_zero (Bits B0 B0 B0 B0) = MyTrue
all_zero (Bits _ _ _ _) = MyFalse

data MyNat : Type where
  O : MyNat
  S : (n : MyNat) -> MyNat

implementation Eq MyNat where
  O == O = True
  O == S _ = False
  S n == O = False
  S n == S m = n == m

total
pred : (n : MyNat) -> MyNat
pred O = O
pred (S n') = n'

total
minustwo : (n : MyNat) -> MyNat
minustwo O = O
minustwo (S O) = O
minustwo (S (S n')) = n'

total
even : (n : MyNat) -> MyBool
even O = MyTrue
even (S O) = MyFalse
even (S (S n')) = even n'

total
odd  : (n : MyNat) -> MyBool
odd n = negb (even n)

test_odd1 : odd (S O) = MyTrue
test_odd1 = Refl
test_odd2 : odd (S (S (S (S O)))) = MyFalse
test_odd2 = Refl

total
plus : (n : MyNat) -> (m : MyNat) -> MyNat
plus O m = m
plus (S n') m = S (plus n' m)

total
mult : (n : MyNat) -> (m : MyNat) -> MyNat
mult O m = O
mult (S n') m = plus m (mult n' m)

test_mult1 : mult (S (S (S O))) (S (S (S O))) = (S(S(S(S(S(S(S(S(S O)))))))))
test_mult1 = Refl

total
minus : (n : MyNat) -> (m : MyNat) -> MyNat
minus O _ = O
minus n@(S _) O = n
minus (S n') (S m') = minus n' m'

total
exp : (base : MyNat) -> (power : MyNat) -> MyNat
exp base O = S O
exp base (S p) = mult base (exp base p)

-- Exercise 1

total
factorial : MyNat -> MyNat
factorial O = S O
factorial (S n') = mult (S n') (factorial n')

test_factorial1 : (factorial (S(S(S O)))) = (S(S(S(S(S(S O))))))
test_factorial1 = Refl

total
eqb : (n : MyNat) -> (m : MyNat) -> MyBool
eqb O O = MyTrue
eqb O (S m') = MyFalse
eqb (S n') O = MyFalse
eqb (S n') (S m') = eqb n' m'

total
leb : (n : MyNat) -> (m : MyNat) -> MyBool
leb O m = MyTrue
leb (S n') O = MyFalse
leb (S n') (S m') = leb n' m'

test_leb1 : leb (S (S O)) (S (S O)) = MyTrue
test_leb1 = Refl

-- Proof by Simplification

plus_O_n : (n : MyNat) -> plus O n = n
plus_O_n n = Refl

plus_1_1 : (n : MyNat) -> plus (S O) n = S n
plus_1_1 n = Refl

mult_0_1 : (n : MyNat) -> mult O n = O
mult_0_1 n = Refl

-- Proof by Rewritng

plus_id_example : (n : MyNat) -> (m : MyNat) -> n = m -> plus n n = plus m m
plus_id_example n m prf = rewrite prf in Refl

-- Exercise 1

plus_id_exercise : (n : MyNat) -> (m : MyNat) -> (o : MyNat) -> 
  n = m -> m = o -> plus n m = plus m o
plus_id_exercise n m o prf prf1 = 
  rewrite prf in rewrite prf1 in Refl

mult_n_O : (p : MyNat) -> mult p O = O
mult_n_O O = Refl
mult_n_O (S n) = let ih = mult_n_O n in rewrite ih in Refl

mult_n_O_m_O : (p : MyNat) -> (q : MyNat) -> plus (mult p O) (mult q O) = O
mult_n_O_m_O p q = 
  rewrite mult_n_O p in rewrite mult_n_O q in Refl

-- Exercise 1

mult_n_1 : (p : MyNat) -> mult p (S O) = p
mult_n_1 O = Refl
mult_n_1 (S n) = rewrite mult_n_1 n in Refl

-- Proof by Case Analysis

plus_1_neq_O : (n : MyNat) -> plus n (S O) == O = False
plus_1_neq_O O = Refl
plus_1_neq_O (S n) = Refl

negb_involutive : (b : MyBool) -> negb (negb b) = b
negb_involutive MyTrue = Refl
negb_involutive MyFalse = Refl

andb_commutatie : (b : MyBool) -> (c : MyBool) -> andb b c = andb c b
andb_commutatie MyTrue MyTrue = Refl
andb_commutatie MyTrue MyFalse = Refl
andb_commutatie MyFalse MyTrue = Refl
andb_commutatie MyFalse MyFalse = Refl

-- Exercise 2

andb_true_elim2 : (b : MyBool) -> (c : MyBool) -> 
  andb b c = MyTrue -> c = MyTrue
andb_true_elim2 MyTrue c prf = rewrite prf in Refl
andb_true_elim2 MyFalse _ Refl impossible

-- Exercise 1

zero_nbeq_plus_1 : (n : MyNat) -> O == plus n (S O) = False
zero_nbeq_plus_1 O = Refl
zero_nbeq_plus_1 (S n) = Refl

-- More Exerciese

-- Warmups

-- Exercise
identity_fn_applied_twice : (f : Bool -> Bool) -> 
  ((x : Bool) -> f x = x) -> (b : Bool) -> f (f b) = b
identity_fn_applied_twice f g x = 
  let r = g x in rewrite r in rewrite r in Refl

-- Exercise
identity_fn_applied_twice' : (f : MyBool -> MyBool) -> 
  ((x : MyBool) -> f x = negb x) -> (b : MyBool) -> f (f b) = b
identity_fn_applied_twice' f g b = 
  let r = g b in 
  let r' = g (negb b) in
  rewrite r in
  rewrite r' in case b of 
    MyTrue => Refl
    MyFalse => Refl

-- Exercise
andb_eq_orb : (b : MyBool) -> (c : MyBool) -> (andb b c = orb b c) -> b = c
andb_eq_orb MyTrue c prf = rewrite prf in Refl
andb_eq_orb MyFalse c prf = rewrite prf in Refl


-- Course Late Policies, Formalized

-- Binary Numerals
