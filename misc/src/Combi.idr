import Data.Nat
import Data.Vect
import Decidable.Equality

%default total
%unbound_implicits off

-----------------------------------------------------------------------------------

fact : Nat -> Nat
fact 0 = 1
fact (S k) = (S k) * fact k

prop_mult_ge_0 : (n, m : Nat) -> GTE (mult n m) 0
prop_mult_ge_0 n m = LTEZero

prop_mult_ge1_ge1_ge1 : (n, m : Nat) -> GTE n 1 -> GTE m 1 -> GTE (mult n m) 1
prop_mult_ge1_ge1_ge1 0 m x y = x
prop_mult_ge1_ge1_ge1 (S k) (S _) (LTESucc x) (LTESucc y) = LTESucc LTEZero

prop_plus_increasing : (n, m : Nat) -> GTE (plus n m) n
prop_plus_increasing 0 m = LTEZero
prop_plus_increasing (S n') m = let ih = prop_plus_increasing n' m in LTESucc ih

prop_fact_ge_1 : (n : Nat) -> GTE (fact n) 1
prop_fact_ge_1 0 = LTESucc LTEZero
prop_fact_ge_1 (S n') = 
    let ih = prop_fact_ge_1 n' in
    let plinc = prop_plus_increasing (fact n') (mult n' (fact n')) in
    transitive ih plinc

prop_plus_fact_ge_1 : (n, m : Nat) -> GTE (plus (fact n) m) 1
prop_plus_fact_ge_1 n m =
    let t1 = prop_plus_increasing (fact n) m in -- plus (fact n) m >= fact n
    let t2 = prop_fact_ge_1 n in -- fact n >= 1
    transitive t2 t1

subX : (a, b : Nat) -> {auto p : GTE a b} -> Nat
subX a 0 {p = LTEZero} = a -- not decreasing!
subX (S a') (S b') {p = (LTESucc x)} = subX a' b'

-- assertion for termination is used
-- precondition imposed
divX : (n : Nat) -> (d : Nat) -> {auto 0 d_1 : GTE d 1} -> (Nat, Nat)
divX n d {d_1} = case decEq (d `lte` n) True of
    (Yes prf) =>
        let (q, r) = 
            divX (assert_smaller n (subX n d {p=lteReflectsLTE d n prf})) d in
        (S q, r)
    (No contra) => (Z, n)

-- assertion for termination eliminated
-- fuel should be greater than n
divX_fuel : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> (Nat, Nat)
divX_fuel 0 n d = (n, d)
divX_fuel (S fuel') n d = case decEq (d `lte` n) True of
    (Yes prf) =>
        let (q, r) =
            divX_fuel fuel' (subX n d {p=lteReflectsLTE d n prf}) d in
            (S q, r)
    (No contra) => (Z, n)

-- assertion for termination eliminated
-- weird minus is used for subtraction
-- fuel should be greater than n
divX_fuel2 : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> (Nat, Nat)
divX_fuel2 0 n d = (n, d)
divX_fuel2 (S fuel') n d = case (d `lte` n) of
    True => let (q, r) = divX_fuel2 fuel' (minus n d) d in (S q, r)
    False => (Z, n)

divX_fuel2fst : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> Nat
divX_fuel2fst 0 n d = n
divX_fuel2fst (S fuel') n d = case (d `lte` n) of
    True => S (divX_fuel2fst fuel' (minus n d) d)
    False => Z

prop_minus : (n : Nat) -> minus n 0 = n
prop_minus 0 = Refl
prop_minus (S k) = Refl

prop_minus2 : (n : Nat) -> gte n (minus n 1) = True
prop_minus2 0 = Refl
prop_minus2 (S n') = 
    rewrite prop_minus n' in
    prop_minus2_rhs_1 n'
    where
        prop_minus2_rhs_1 : (n' : Nat) -> lte n' (S n') = True
        prop_minus2_rhs_1 0 = Refl
        prop_minus2_rhs_1 (S k) = prop_minus2_rhs_1 k
        
prop_minusS : (k : Nat) -> (lte 1 k = True) -> S (minus k 1) = k
prop_minusS Z Refl impossible
prop_minusS (S k') Refl = cong S (prop_minus k')

prop_div' : (n : Nat) -> div' n n 0 = n
prop_div' 0 = Refl
prop_div' (S n') =
    rewrite prop_minus n' in
    cong S (prop_div' n')

prop_lte_1 : (k : Nat) -> (lte 1 k = True -> Void) -> lte 1 k = False
prop_lte_1 0 f = Refl
prop_lte_1 (S k) f = void (f Refl)

prop_lte_1_1 : (k : Nat) -> (lte 1 k = True -> Void) -> k = 0
prop_lte_1_1 0 f = Refl
prop_lte_1_1 (S k) f = void (f Refl)

prop_lte_1_2 : (k : Nat) -> (lte 1 (minus k 0) = True) -> Void

prop_lte_1_3 : (k : Nat) -> (lte 1 k = True -> Void) -> lte 1 k = False
prop_lte_1_3 0 f = Refl
prop_lte_1_3 (S k) f = void (f Refl)

prop_lte_S : (m, n : Nat) -> lte (S m) n = True -> lte m n = True
prop_lte_S 0 n prf = Refl
prop_lte_S (S k) 0 prf = prf
prop_lte_S (S k) (S j) prf = prop_lte_S k j prf

-- prop_divX_fuel2_k_km1_1_km1 : (k : Nat) -> fst (divX_fuel2 k (minus k 1) 1) = minus k 1
-- prop_divX_fuel2_k_km1_1_km1 0 = Refl
-- prop_divX_fuel2_k_km1_1_km1 (S k') =
--     case decEq (lte 1 (minus k' 0)) True of
--         (Yes prf) =>
--             rewrite prf in
--             rewrite prop_minus k' in
--             let ih = prop_divX_fuel2_k_km1_1_km1 k' in
--             ?prop_divX_fuel2_k_km1_1_km1_rhs_2
--         (No contra) => ?prop_divX_fuel2_k_km1_1_km1_rhs_3

prop_divX_fuel2fst_k_km1_1_km1 : (k : Nat) -> divX_fuel2fst k (minus k 1) 1 = minus k 1
prop_divX_fuel2fst_k_km1_1_km1 0 = Refl
prop_divX_fuel2fst_k_km1_1_km1 (S k') =
    case decEq (lte 1 (minus k' 0)) True of
        (Yes prf) =>
            rewrite prf in
            rewrite prop_minus k' in
            rewrite prop_divX_fuel2fst_k_km1_1_km1 k' in
            let rw = prop_minus k' in
            -- prf : lte 1 (minus k' 0) = True
            let prf' = replace {p = \r => lte 1 r = True} rw prf in
            prop_minusS k' prf'
        (No contra) =>
            let rw = prop_minus k' in
            rewrite rw in
            let contra' = replace {p = \r => lte 1 r = True -> Void} rw contra in
            rewrite prop_lte_1_1 k' contra' in
            Refl

-- prop_divX_fuel2' : (n, m : Nat) -> divX_fuel2 n m 1
-- prop_divX_fuel2 : (n, m : Nat) -> {auto p : GTE m 1} -> 
--     fst (divX_fuel2 (S n) n m) = divNatNZ n m ItIsSucc
-- prop_divX_fuel2 : (n, m : Nat) -> 
--     fst (divX_fuel2 (S n) n (S m)) = divNatNZ n (S m) ItIsSucc
-- prop_divX_fuel2 0 0 = Refl
-- prop_divX_fuel2 (S k) 0 =
--     rewrite prop_minus k in
--     rewrite prop_div' k in
--     case decEq (lte 1 k) True of
--         (Yes prf) =>
--             ?prop_divX_fuel2_rhs_4
--         (No contra) =>
--             rewrite prop_lte_1_1 k contra in
--             Refl
-- prop_divX_fuel2 0 (S k) = Refl
-- prop_divX_fuel2 (S n') (S m') =
--     case decEq (lte (S m') n') True of
--         (Yes prf) =>
--             rewrite prf in
--             ?hoo_2
--         (No contra) => ?hoo_3
prop_divX_fuel2fst : (n, m : Nat) -> 
    divX_fuel2fst (S n) n (S m) = divNatNZ n (S m) ItIsSucc
prop_divX_fuel2fst 0 0 = Refl
prop_divX_fuel2fst (S k) 0 =
    rewrite prop_minus k in
    rewrite prop_div' k in
    case decEq (lte 1 k) True of
        (Yes prf) =>
            rewrite prf in
            rewrite prop_divX_fuel2fst_k_km1_1_km1 k in
            rewrite prop_minusS k prf in
            Refl
        (No contra) =>
            rewrite prop_lte_1_1 k contra in
            Refl
prop_divX_fuel2fst 0 (S k) = Refl
prop_divX_fuel2fst (S n') (S m') =
    case decEq (lte (S m') n') True of
        (Yes prf) =>
            rewrite prf in
            -- S (if lte (S (S m')) (minus n' (S m'))
            --    then S (divX_fuel2fst n' (minus (minus n' (S m')) (S (S m'))) (S (S m')))
            --    else 0) = 
            --   (if lte n' m'
            --    then 0
            --    else S (div' n' (minus (S n') (S (S m'))) (S m')))
            ?hoo_2
        (No contra) => ?hoo_3



-- wrapper for divX
--- only quotient is returned
--- precondition introduced for eliminating zero-division
divS : (n : Nat) -> (d : Nat) -> {auto d_1 : GTE d 1} -> Nat
-- divS a b = fst $ divX a b
-- divS a b = fst $ divX_fuel a a b
divS a b = fst $ divX_fuel2 a a b
-- divS a b = div' (S a) a b

-- naive definition of combination
-- 0 C 0 ==> 1
-- 0 C 1 ==> 1
-- 0 C 2 ==> 0
math_combi_raw : (n, m : Nat) -> Nat
math_combi_raw n m = div (fact n) ((fact (minus n m)) `mult` (fact m))

-- why this behaves differently from the above??? 
-- 0 C 0 ==> 0
-- 0 C 1 ==> 0
-- 0 C 2 ==> 0
math_combi_raw' : (n, m : Nat) -> Nat
math_combi_raw' n m = div' (fact n) (fact n) ((fact (minus n m)) `mult` (fact m)) --- div' uses fuel
-- Note!! div' is not a simple division function!a


math_combi : (n, m : Nat) -> Nat
math_combi n m =
    let ev1 = prop_fact_ge_1 (minus n m) in
    let ev2 = prop_fact_ge_1 m in
    let ev3 = prop_mult_ge1_ge1_ge1 (fact (minus n m)) (fact m) ev1 ev2 in
    let t = divS (fact n) ((fact (minus n m)) `mult` (fact m)) {d_1=ev3}
    -- let t = divS (fact n) ((fact (minus n m)) `mult` (fact m))
    in
    t

math_combi' : (n, m : Nat) -> Nat
math_combi' n m = case decEq (n `gte` m) True of
    (Yes prf) => math_combi n m
    (No contra) => 0

math_combi2 : Nat -> Nat -> Nat
math_combi2 n m = div n m

-- prop_divNat : divNat 0 1 = 1 -- can you prove this?

funny : (Nat, Nat)
funny = case decEq (lte 1 (subX 1 1)) True of
--   Yes prf => let (q, r) = divX (assert_smaller (subX 1 1) (subX (subX 1 1) 1)) 1 in (S q, r)
  Yes prf => (1, absurd prf)
  No contra => (0, subX 1 1)
--   aaa => ?holo

ttt0 : subX 3 2 = 1 -- definitionally equal?
ttt0 = Refl
ttt0' : divX 3 2 = (1, 1) -- propositionally equal?
ttt0' = ?ttt0'_rhs -- Refl
-- Can't solve constraint between:
-- (1, 1) and 
--  let (q, r) = divX (assert_smaller 3 (subX 3 2)) 2 in (S q, r).
ttt0'' : divX_fuel (S 3) 3 2 = (1, 1)
ttt0'' = ?ttt0''_rhs -- decEq...
ttt0''' : divX_fuel2 (S 3) 3 2 = (1, 1)
ttt0''' = Refl
ttt02 : div 3 2 = 1
ttt02 = Refl -- Integer!!!
ttt02' : divNat 3 2 = 1
ttt02' = ?ttt02'_rhs -- divNat 3 2 = 1 (not covering)
ttt02'' : divNatNZ 3 2 ItIsSucc = 1
ttt02'' = Refl
ttt02''' : div' 3 3 2 = 1 -- the first argument is fuel
ttt02''' = Refl
ttt_combi_raw : math_combi_raw 0 1 = 1
ttt_combi_raw = ?ttt_combi_raw_rhs -- divNat 1 1 = 1
ttt_combi_raw' : math_combi_raw' 0 1 = 0
ttt_combi_raw' = Refl
ttt_combi : math_combi 0 1 = 1
ttt_combi = Refl
ttt_combi' : math_combi' 0 1 = 0
ttt_combi' = Refl
ttt_combi2 : math_combi2 0 1 = 0
ttt_combi2 = ?ttt03_rhs -- divNat 0 1 = 1

ttt : lte 2 (subX 6 2) = True
ttt = Refl {x=True}
ttt2 : subX 1 1 = 0
ttt2 = Refl {x=subX 1 1}

ttt3 : (n, m : Nat) -> Nat
ttt3 n m = -- requires : LTE 1 (mult (fact (minus n m)) (fact m))
    let e1 = prop_fact_ge_1 (minus n m) in
    let e2 = prop_fact_ge_1 m in
    let e3 = prop_mult_ge1_ge1_ge1 (fact (minus n m)) (fact m) e1 e2 in
    fst $ divX (fact n) ((fact (minus n m)) `mult` (fact m)) {d_1=e3}

ttt3_0_1 : Nat
ttt3_0_1 = 
    let e1 = prop_fact_ge_1 (minus 0 1) in
    let e2 = prop_fact_ge_1 1 in
    let e3 = prop_mult_ge1_ge1_ge1 (fact (minus 0 1)) (fact 1) e1 e2 in
    fst $ divX (fact 0) ((fact (minus 0 1)) `mult` (fact 1)) {d_1=e3}

test_ttt3_rhs' : (Nat, Nat)
test_ttt3_rhs' = case decEq (lte 1 (subX 1 1)) True of {
        Yes prf =>
            let (q, r) =
                divX (assert_smaller (subX 1 1) (subX (subX 1 1) 1)) 1 in (S q, r) ;
        No contra => (0, subX 1 1) 
    }

test_ttt3 : ttt3 0 1 = 1
test_ttt3 = 
    ?test_ttt3_rhs


prop_math_combi_0_1_1 : math_combi 0 1 = 1
prop_math_combi_0_1_1 = 
    rewrite ttt2 in
    ?hoho
prop_math_combi'_0_1_0 : math_combi' 0 1 = 0
prop_math_combi'_0_1_0 = Refl
prop_math_combi'_3_1_3 : math_combi' 3 1 = 1
prop_math_combi'_3_1_3 = 
    let rw = ttt in
    ?prop_math_combi'_3_1_3_rhs -- divNat 6 2 = 1

prop_math_combi_eq : (n, m : Nat) -> {auto p : m = 1 -> Void} ->
    math_combi n m = math_combi' n m
prop_math_combi_eq n 0 = Refl
prop_math_combi_eq n (S 0) = ?prop_math_combi_eq_rhs_2
prop_math_combi_eq 0 (S (S m')) = ?prop_math_combi_eq_rhs_3
prop_math_combi_eq (S n') (S (S m')) = ?prop_math_combi_eq_rhs_4

nC : (n, m : Nat) -> Nat
nC 0      _ = 0
nC (S n') 0 = 1
nC (S n') (S m') =
    ((nC (S n') m') `mult` ((S n') `minus` m')) `divS` (S m')

prop_nC : (n, m : Nat) -> {p : LTE 1 (minus (S n) m)} ->
    nC (S n) m = divS (mult (nC n m) (S n)) (minus (S n) m)
-- prop_nC 0 0 {p} = ?prop_nC_rhs_not_impossible_1
-- prop_nC 0 (S 0) {p} = ?prop_nC_rhs_not_impossible_2
-- prop_nC 0 (S (S k)) {p} = ?prop_nC_rhs_not_impossible_3
-- prop_nC (S k) m = ?prop_nC_rhs_1

prop_n_m_1 : (n, m : Nat) ->
    GTE n m -> GT m Z ->
    GTE (n `minus` (m `minus` 1)) Z
prop_n_m_1 Z Z LTEZero LTEZero impossible
prop_n_m_1 Z Z LTEZero (LTESucc x) impossible
prop_n_m_1 Z (S k) x y = LTEZero
prop_n_m_1 (S _) Z LTEZero LTEZero impossible
prop_n_m_1 (S _) Z LTEZero (LTESucc x) impossible
prop_n_m_1 (S n') (S m') (LTESucc x) (LTESucc y) =
    let ih = prop_n_m_1 n' m' x y in LTEZero
