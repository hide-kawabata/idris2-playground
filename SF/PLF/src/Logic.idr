{-
  From (mainly) Logical Foundations (of Software Foundations) by Benjamin Pierce
  (answers to exercises omitted)
-}

import Data.Nat
import Syntax.PreorderReasoning
import Decidable.Equality

%hide Prelude.Stream.(::)

%default total

-- Logical Connectives ---------------------------
-- Conjunction -----------------------------------

and_example : Pair (3 + 4 = 7) (2 * 2 = 4)
and_example = (Refl, Refl)

and_intro : {a, b : Type} -> a -> b -> Pair a b
and_intro x y = (x, y)

and_example' : Pair (3 + 4 = 7) (2 * 2 = 4)
and_example' = (Refl, Refl)

-- exercise
and_exercise : (n, m : Nat) -> (n + m = 0) -> Pair (n = 0) (m = 0)

and_example2 : (n, m : Nat) -> Pair (n = 0) (m = 0) -> (n + m = 0)
and_example2 0 m p = snd p
and_example2 (S n') m p = 
  let prfn = fst p in
  let prfm = snd p in
  rewrite sym $ prfn in
  rewrite prfm in
  let prf0 = plusZeroRightNeutral n' in
  rewrite prf0 in
  Refl

tmp : {n, m, p : Type} -> (n -> m) -> (m -> p) -> (n -> p)
tmp f g x = g (f x)

and_example2' : (n, m : Nat) -> Pair (n = 0) (m = 0) -> (n + m = 0)
and_example2' n m (prfn0, prfm0) = Calc $
  |~ n + m
  ~~ 0 ... (rewrite prfn0 in
            rewrite prfm0 in Refl)

and_example3 : (n, m : Nat) -> n + m = 0 -> n * m = 0
and_example3 n m prf = 
  let (p1, p2) = and_exercise n m prf in
  rewrite p1 in -- the goal reduces to 0 = 0 at this point!
  Refl

proj1 : {p, q : Type} -> Pair p q -> p
proj1 (x, y) = x

-- exercise
proj2 : {p, q : Type} -> Pair p q -> q

and_commut : {p, q : Type} -> Pair p q -> Pair q p
and_commut (x, y) = (y, x)

-- exercise
and_assoc : {p, q, r : Type} -> Pair p (Pair q r) -> Pair (Pair p q) r


-- Disjunction -----------------------------------
factor_is_O : (n, m : Nat) -> Either (n = 0) (m = 0) -> n * m = 0
factor_is_O n m (Left x) = rewrite x in Refl
factor_is_O n m (Right x) = rewrite x in multZeroRightZero n

or_intro_l : {a, b : Type} -> a -> Either a b
or_intro_l x = Left x

zero_or_succ : (n : Nat) -> Either (n = 0) (n = S (pred n))
zero_or_succ 0 = Left Refl
zero_or_succ (S k) = Right Refl

-- exercise
mult_is_O : (n, m : Nat) -> n * m = 0 -> Either (n = 0) (m = 0)

-- exercise
or_commut : {p, q : Type} -> Either p q -> Either q p


-- Falsehood and Negation -----------------------------

ex_falso_quodlibet : {t : Type} -> Void -> t
ex_falso_quodlibet x impossible

-- exercise
not_implies_our_not : {p : Type} -> Not p -> ({q : Type} -> p -> q)

zero_not_one : Not (0 = 1)
zero_not_one Refl impossible

not_False : Not Void
not_False x = absurd x

contradiction_implies_anything : {p, q : Type} -> Pair p (Not p) -> q
contradiction_implies_anything (x, y) = absurd (y x)

double_neg : {p : Type} -> p -> Not (Not p)
double_neg x f = absurd (f x)

-- exercise
contrapositive : {p, q : Type} -> (p -> q) -> (Not q -> Not p)

-- exercise
not_both_true_and_false : {p : Type} -> Not (Pair p (Not p))

-- exercise
de_morgan_not_or : {p, q : Type} -> Not (Either p q) -> Pair (Not p) (Not q)

de_morgan_or_not : Pair (Not p) (Not q) -> Not (Either p q)
de_morgan_or_not (np, nq) p_q =
  -- (Not p, Not q) -> Not (Either p q)
  -- (p -> Void, q -> Void) -> (Either p q) -> Void
  case p_q of
    Left prf_p => np prf_p
    Right prf_q => nq prf_q

de_morgan_and_not_not : Pair p q -> Not (Either (Not p) (Not q))
de_morgan_and_not_not (prf_p, prf_q) np_nq =
  case np_nq of
    Left prf_np => prf_np prf_p
    Right prf_nq => prf_nq prf_q

de_morgan_not_or_not : Either (Not p) (Not q) -> Not (Pair p q)
  -- Either (p -> Void) (q -> Void) -> ((Pair p q) -> Void)
de_morgan_not_or_not (Left prf_np) (prf_p, prf_q) = prf_np prf_p
de_morgan_not_or_not (Right prf_nq) (prf_p, prf_q) = prf_nq prf_q

de_morgan_and_not : Either (Not p) (Not q) -> Not (Pair p q)
  -- Either (p -> Void) (q -> Void) -> ((Pair p q) -> Void)
de_morgan_and_not (Left prf_np) (prf_p, prf_q) = prf_np prf_p
de_morgan_and_not (Right prf_nq) (prf_p, prf_q) = prf_nq prf_q

-- not provable in pure intuitionistic logic
--de_morgan_not_and : Not (Pair p q) -> Either (Not p) (Not q)

not_true_is_false : {b : Bool} -> Not (b = True) -> (b = False)
not_true_is_false {b = False} f = Refl
not_true_is_false {b = True} f = absurd $ f Refl


-- Truth ----------------------------------------

disc_fn : (n : Nat) -> Type
disc_fn 0 = () -- Truth; actually any type is OK.
disc_fn (S k) = Void -- Falsehood

disc_example : (n : Nat) -> Not (0 = S n)
disc_example _ Refl impossible


-- Logical Equivalence --------------------------
iff : (p, q : Type) -> Type
iff p q = Pair (p -> q) (q -> p)

iff_sym : {p, q : Type} -> (iff p q) -> (iff q p)
iff_sym (x, y) = (y, x)

not_true_iff_false : (b : Bool) -> iff (Not (b = True)) (b = False)
not_true_iff_false False = -- ((False = True -> Void) -> False = False,
                           --  False = False -> False = True -> Void)  
  let p1 : (False = True -> Void) -> (False = False)
      p1 _ = Refl
      p2 : False = False -> False = True -> Void
      p2 _ pne = absurd pne
      in
  (p1, p2)
not_true_iff_false True = -- ((True = True -> Void) -> True = False,
                          --  True = False -> True = True -> Void)
  let p1 : (True = True -> Void) -> (True = False)
      p1 f = absurd (f Refl)
      p2 : True = False -> True = True -> Void
      p2 _ _ impossible
      in
  (p1, p2)

apply_iff_example1 : {p, q, r : Type} -> iff p q -> (q -> r) -> (p -> r)
apply_iff_example1 (x, z) f y = f (x y)

apply_iff_example2 : {p, q, r : Type} -> iff p q -> (p -> r) -> (q -> r)
apply_iff_example2 (x, z) f y = f (z y)

-- exercise
or_distributes_over_and : (p, q, r : Type) -> 
  iff (Either p (Pair q r)) (Pair (Either p q) (Either p r))


-- Setoids and Logical Equivalence ----------------------


-- Existential Quantification ---------------------------
double : Nat -> Nat
double 0 = 0
double (S k) = S (S (double k))

even : (x : Nat) -> Type
even x = (n : Nat ** x = double n) -- type function, not an ordinary proof

four_is_even : even 4
four_is_even = (2 ** Refl)

exists_example_2 : (n : Nat) -> (m ** n = 4 + m) -> (o ** n = 2 + o)
exists_example_2 n (m' ** prf) = rewrite prf in (S (S m') ** Refl)

-- exercise
dist_not_exists : {x : Type} -> (p : x -> Type) -> 
  ((a : x) -> p a) -> Not (a ** Not (p a))

-- Programming with Propositions --------------------------
inf : {a : Type} -> (x : a) -> (l : List a) -> Type
inf x [] = Void
inf x (x' :: l') = Either (x' = x) (inf x l')

in_example_1 : inf 4 [1, 2, 3, 4, 5]
in_example_1 = Right (Right (Right (Left Refl)))

in_example_2 : (n : Nat) -> (inf n [2, 4]) -> (n' ** n = 2 * n')
in_example_2 n (Left x) = -- (n' : Nat ** n = plus n' (plus n' 0))
                          -- x : 2 = n
  rewrite sym $ x in (1 ** Refl)
in_example_2 n (Right x) = -- (n' : Nat ** n = plus n' (plus n' 0))
                           -- Either (4 = n) Void
  let Left rw = x in
  rewrite sym $ rw in
  (2 ** Refl)

-- Applying Theorems to Arguments -------------------------
add_comm : (n, m : Nat) -> n + m = m + n
add_comm 0 m = rewrite plusZeroRightNeutral m in Refl
add_comm (S k) m = rewrite add_comm k m in 
                   rewrite plusSuccRightSucc m k in Refl

add_comm3 : (x, y, z : Nat) -> x + (y + z) = (z + y) + x
add_comm3 x y z = rewrite add_comm z y in
                  rewrite add_comm x (y + z) in
                  Refl

in_not_nil_42 : (l : List Nat) -> inf 42 l -> Not (l = [])
in_not_nil_42 [] x prf = x
in_not_nil_42 (_ :: _) _ Refl impossible

-- Coq vs. Set Theory -------------------------------------
-- Functional Extensionality ------------------------------
function_equality_ex1 : (\x => 3 + x) = (\x => (pred 4) + x)
function_equality_ex1 = Refl

-- not provable in pure intuitionistic type theory
--function_equality_ex1' : (\x => x + 3) = (\x => (pred 4) + x)

0 functional_extensionality : {x, y : Type} -> {f, g : x -> y} ->
  ((a : x) -> f a = g a) -> f = g

0 function_equality_ex2 : (\x => plus x 1) = (\x => plus 1 x)
function_equality_ex2 =
  functional_extensionality 
  (\a => rewrite add_comm 1 a in Refl)


-- Propositions vs. Booleans -----------------------------
-- Working with Decidable Properties ---------------------
evenb : (n : Nat) -> Bool
evenb 0 = True
evenb (S 0) = False
evenb (S (S k)) = evenb k

even_42_bool : evenb 42 = True
even_42_bool = Refl

even_42_type : even 42
even_42_type = (21 ** Refl)

even_double : (k : Nat) -> evenb (double k) = True
even_double 0 = Refl
even_double (S k) = rewrite even_double k in Refl

negb : (b : Bool) -> Bool
negb False = True
negb True = False

negneg : (b : Bool) -> b = negb (negb b)
negneg False = Refl
negneg True = Refl

even_S : (n : Nat) -> evenb (S n) = negb (evenb n)
even_S 0 = Refl
even_S (S k) = 
  rewrite even_S k in
  rewrite sym $ negneg (evenb k) in
  Refl

halve_nat : Nat -> Nat
halve_nat 0 = 0
halve_nat (S 0) = 0
halve_nat (S (S k)) = S (halve_nat k)

double_of_half_T : (n : Nat) -> evenb n = True -> double (halve_nat n) = n
double_of_half_T 0 Refl = Refl
double_of_half_T 1 Refl impossible
double_of_half_T (S (S k)) prf = cong (\x => S (S x)) $ double_of_half_T k prf

evenb_false_neg : (n : Nat) -> Not (evenb n = True) -> evenb n = False
evenb_false_neg 0 f = absurd (f Refl)
evenb_false_neg (S 0) f = Refl
evenb_false_neg (S (S k)) f = evenb_false_neg k f

-- you can not prove this
--evenb_true_neg : (n : Nat) -> evenb n = True -> Not (evenb n = False)
--evenb_true_neg 0 _ _ impossible
--evenb_true_neg 1 _ _ impossible -- <==========
--evenb_true_neg (S (S k)) prf prf1 = ?evenb_true_neg_rhs_3

double_of_half_F : (n : Nat) -> Not (evenb n = True)
                   -> S (double (halve_nat n)) = n
double_of_half_F 0 prf = absurd (prf Refl)
double_of_half_F (S 0) prf = Refl
double_of_half_F (S (S k)) prf = cong (\x => S (S x)) $ double_of_half_F k prf

-- exercise
even_double_conv : (n : Nat) -> 
  (k : Nat ** n = if evenb n then double k else S (double k))


-- Classical vs. Constructive Logic ----------------------
