module lf-basics where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Bool

data day : Set where
    monday : day
    tuesday : day
    wednesday : day
    thursday : day
    friday : day
    saturday : day
    sunday : day

next-weekday : (d : day) -> day
next-weekday monday = tuesday
next-weekday tuesday = wednesday
next-weekday wednesday = thursday
next-weekday thursday = friday
next-weekday friday = monday
next-weekday saturday = monday
next-weekday sunday = monday

test-next-weekday : next-weekday (next-weekday saturday) ≡ tuesday
test-next-weekday = refl

negb : (b : Bool) → Bool
negb false = true
negb true = false

andb : (b1 b2 : Bool) → Bool
andb false b2 = false
andb true b2 = b2

data rgb : Set where
    red : rgb
    green : rgb
    blue : rgb

data color : Set where
    black : color
    white : color
    primary : (p : rgb) -> color

monochrome : (c : color) -> Bool
monochrome black = true
monochrome white = true
monochrome (primary p) = false

isred : (c : color) -> Bool
isred black = false
isred white = false
isred (primary red) = true
isred (primary _) = false

data bit : Set where
    bb1 : bit
    bb0 : bit

data nybble : Set where
    bits : bit → bit → bit → bit → nybble

all-zero : (nb : nybble) -> Bool
all-zero (bits bb0 bb0 bb0 bb0) = true
all-zero (bits _ _ _ _) = false

pred : (n : ℕ) -> ℕ
pred zero = zero
pred (suc n') = n'

minustwo : (n : ℕ) → ℕ
minustwo zero = zero
minustwo (suc zero) = zero
minustwo (suc (suc n')) = n'

even : (n : ℕ) → Bool
even zero = true
even (suc zero) = false
even (suc (suc n')) = even n'

odd : (n : ℕ) → Bool
odd n = negb (even n)

test-odd1 : odd (suc zero) ≡ true
test-odd1 = refl
test-odd2 : odd (suc (suc (suc (suc zero)))) ≡ false
test-odd2 = refl

plus : (n : ℕ) → (m : ℕ) → ℕ
plus zero m = m
plus (suc n') m = suc (plus n' m)

mult : (n : ℕ) → (m : ℕ) → ℕ
mult zero m = zero
mult (suc n') m = plus m (mult n' m)

test-mult1 : mult (suc (suc (suc zero))) (suc (suc (suc zero))) ≡ (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
test-mult1 = refl

minus : (n : ℕ) → (m : ℕ) → ℕ
minus zero m = zero 
minus (suc n) zero = suc n 
minus (suc n) (suc m) = minus n m

exp : (base : ℕ) → (power : ℕ) → ℕ
exp base zero = suc zero 
exp base (suc power) = mult base (exp base power)

factorial : ℕ → ℕ
factorial zero = suc zero 
factorial (suc n) = mult (suc n) (factorial n)

test-factorial1 : factorial (suc (suc (suc zero))) ≡ suc (suc (suc (suc (suc (suc zero)))))
test-factorial1 = refl

-- Proof by Simplification

plus-0-n : (n : ℕ) → plus zero n ≡ n
plus-0-n n = refl

plus-1-1 : (n : ℕ) → plus (suc zero) n ≡ suc n
plus-1-1 n = refl

mult-0-1 : (n : ℕ) → mult zero n ≡ zero
mult-0-1 n = refl

-- Proof by Rewriting

plus-id-example : (n : ℕ) → (m : ℕ) → n ≡ m → plus n n ≡ plus m m
plus-id-example n m prf rewrite prf = refl

plus-id-exercise : (n m o : ℕ) → n ≡ m → m ≡ o → plus n m ≡ plus m o
plus-id-exercise n m o n≡m m≡o 
    rewrite n≡m 
    rewrite m≡o = refl

mult-n-0 : (p : ℕ) → mult p zero ≡ zero
mult-n-0 zero = refl 
mult-n-0 (suc p')
    rewrite (mult-n-0 p') = refl

mult-n-0-m-0 : (p q : ℕ) → plus (mult p zero) (mult q zero) ≡ zero
mult-n-0-m-0 p q
    rewrite (mult-n-0 p)
    rewrite (mult-n-0 q)
    = refl

mult-n-1 : (p : ℕ) → mult p (suc zero) ≡ p
mult-n-1 zero = refl 
mult-n-1 (suc p') rewrite (mult-n-1 p') = refl

-- Proof by Case Analysis

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc m = false
suc n == zero = false
suc n == suc m = n == m

plus-1-neq-0 : (n : ℕ) → plus n (suc zero) == zero ≡ false
plus-1-neq-0 zero = refl 
plus-1-neq-0 (suc n') = refl

negb-involutive : (b : Bool) → negb (negb b) ≡ b
negb-involutive false = refl 
negb-involutive true = refl

andb-true-elim2 : (b c : Bool) → andb b c ≡ true → c ≡ true
andb-true-elim2 true c p rewrite p = refl 

zero-nbeq-plus-1 : (n : ℕ) → zero == plus n (suc zero) ≡ false
zero-nbeq-plus-1 zero = refl 
zero-nbeq-plus-1 (suc n) = refl

identity-fn-applied-twice : (f : Bool → Bool) → ((x : Bool) → f x ≡ x) →
    (b : Bool) → f (f b) ≡ b
identity-fn-applied-twice f p b
    rewrite (p b)
    = p b

identity-fn-applied-twice' : (f : Bool → Bool) → ((x : Bool) → f x ≡ negb x) → 
    (b : Bool) → f (f b) ≡ b
identity-fn-applied-twice' f p b with b
identity-fn-applied-twice' f p b    | true rewrite (p true) rewrite (p false) = refl
identity-fn-applied-twice' f p b    | false rewrite (p false) rewrite (p true) = refl


-- Binary Numerals

data bin : Set where
    z : bin
    b0 : (n : bin) → bin
    b1 : (n : bin) → bin

incr : bin → bin
incr z = b1 z 
incr (b0 m) = b1 m
incr (b1 m) = b0 (incr m)

bin-to-nat : bin → ℕ
bin-to-nat z = 0 
bin-to-nat (b0 n) = let n' = bin-to-nat n in n' + n'
bin-to-nat (b1 n) = let n' = bin-to-nat n in n' + n' + 1

test-bin-incr1 : incr (b1 z) ≡ b0 (b1 z)
test-bin-incr1 = refl
test-bin-incr2 : incr (b0 (b1 z)) ≡ b1 (b1 z)
test-bin-incr2 = refl
test-bin-incr3 : incr (b1 (b1 z)) ≡ b0 (b0 (b1 z))
test-bin-incr3 = refl
test-bin-incr4 : bin-to-nat (b0 (b1 z)) ≡ 2
test-bin-incr4 = refl
test-bin-incr5 : bin-to-nat (incr (b1 z)) ≡ 1 + bin-to-nat (b1 z)
test-bin-incr5 = refl
test-bin-incr6 : bin-to-nat (incr (incr (b1 z))) ≡ 2 + bin-to-nat (b1 z)
test-bin-incr6 = refl
