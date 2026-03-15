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

divX : (n : Nat) -> (d : Nat) -> {auto 0 d_1 : GTE d 1} -> (Nat, Nat)
divX n d {d_1} = case decEq (d `lte` n) True of
    (Yes prf) =>
        let (q, r) = 
            divX (assert_smaller n (subX n d {p=lteReflectsLTE d n prf})) d in
        (S q, r)
    (No contra) => (Z, n)

divS : (n : Nat) -> (d : Nat) -> {auto d_1 : GTE d 1} -> Nat
divS a b = fst $ divX a b

math_combi : (n, m : Nat) -> Nat
-- math_combi n m = (fact n) `div` ((fact (minus n m)) `mult` (fact m))
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

-- prop_divNat : divNat 0 1 = 1 -- can you prove this?

funny : (Nat, Nat)
funny = case decEq (lte 1 (subX 1 1)) True of
--   Yes prf => let (q, r) = divX (assert_smaller (subX 1 1) (subX (subX 1 1) 1)) 1 in (S q, r)
  Yes prf => (1, absurd prf)
  No contra => (0, subX 1 1)
--   aaa => ?holo

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
