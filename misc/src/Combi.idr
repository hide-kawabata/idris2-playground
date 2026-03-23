import Data.Nat
import Data.Vect
import Decidable.Equality

%default total
%unbound_implicits off

-----------------------------------------------------------------------------------

fact : Nat -> Nat
fact 0 = 1
fact (S k) = (S k) * fact k

prop_plus_1_ge1 : (n, m : Nat) -> LTE 1 n -> GTE (plus n m) 1
prop_plus_1_ge1 0 0 x = x
prop_plus_1_ge1 0 (S k) x = LTESucc LTEZero
prop_plus_1_ge1 (S k) m x = LTESucc LTEZero

prop_fact : (n : Nat) -> GTE (fact n) 1
prop_fact 0 = LTESucc (LTEZero {right=0}) {right=0} {left=0}
prop_fact (S n') =
    let ih = prop_fact n' in
    let rw = prop_plus_1_ge1 (fact n') (mult n' (fact n')) ih in
    rw

prop_mult_ge_0 : (n, m : Nat) -> GTE (mult n m) 0
prop_mult_ge_0 n m = LTEZero

prop_mult_ge1_ge1_ge1 : (n, m : Nat) -> GTE n 1 -> GTE m 1 -> GTE (mult n m) 1
prop_mult_ge1_ge1_ge1 0 m x y = x
prop_mult_ge1_ge1_ge1 (S k) (S _) (LTESucc x) (LTESucc y) = LTESucc LTEZero

prop_plus_increasing : (n, m : Nat) -> GTE (plus n m) n
prop_plus_increasing 0 m = LTEZero
prop_plus_increasing (S n') m = let ih = prop_plus_increasing n' m in LTESucc ih

-- the same as prop_fact
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

-- returns meaningless value (fuel+n) if d is zero
divX_fuel2fst : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> Nat
divX_fuel2fst 0 n d = n
divX_fuel2fst (S fuel') n d = case (d `lte` n) of
    True => S (divX_fuel2fst fuel' (minus n d) d)
    False => Z

div'W : (n, d : Nat) -> {auto d_1 : GTE d 1} -> Nat
div'W n (S d) = div' n n d

divXW : (n, d : Nat) -> Nat
divXW n d = divX_fuel2fst (S n) n d


prop_t_v_f : (b : Bool) -> (b = True -> Void) -> b = False
prop_t_v_f False f = Refl
prop_t_v_f True f = absurd (f Refl)


prop_minus : (n : Nat) -> minus n 0 = n
prop_minus 0 = Refl
prop_minus (S k) = Refl

prop_minusNN : (n : Nat) -> minus n n = 0
prop_minusNN 0 = Refl {x=0}
prop_minusNN (S k) = prop_minusNN k

prop_minusSnSn : (n : Nat) -> minus (S n) (S n) = 0
prop_minusSnSn 0 = Refl {x=0}
prop_minusSnSn (S k) = prop_minusSnSn k

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


-- prop_lte_minus : (k, j : Nat) -> lte (S k) j = True -> lte (S (S k)) (minus j (S k)) = True
-- prop_lte_minus k 0 prf = prf
-- prop_lte_minus 0 (S j) prf = ?prop_lte_minus_rhs_2
-- prop_lte_minus (S k) (S j) prf = ?prop_lte_minus_rhs_3

prop_div' : (n : Nat) -> div' n n 0 = n
prop_div' 0 = Refl
prop_div' (S n') =
    rewrite prop_minus n' in
    cong S (prop_div' n')

prop_div'0 : (n : Nat) -> div' n 0 n = 0
prop_div'0 0 = Refl
prop_div'0 (S k) = Refl

prop_div'2 : (e, n, m : Nat) -> lte n e = True -> lte n m = True -> div' e n m = 0
prop_div'2 0 n m prf prf1 = Refl
prop_div'2 (S k) 0 0 prf prf1 = Refl
prop_div'2 (S k) (S j) 0 prf prf1 = absurd prf1
prop_div'2 (S k) n (S j) prf prf1 =
    rewrite prf1 in
    Refl
    
prop_divX_fuel2fst_1 : (e, n : Nat) -> lte n e = True -> divX_fuel2fst e n 1 = n
prop_divX_fuel2fst_1 0 0 Refl = Refl
prop_divX_fuel2fst_1 (S k) 0 Refl = Refl
prop_divX_fuel2fst_1 0 (S k) prf = Refl
prop_divX_fuel2fst_1 (S j) (S k) prf =
    rewrite prop_minus k in
    rewrite prop_divX_fuel2fst_1 j k prf in
    Refl

prop_mult_0 : (n : Nat) -> mult n 0 = 0
prop_mult_0 0 = Refl
prop_mult_0 (S k) = prop_mult_0 k




prop_lte_k_Sk : (k : Nat) -> lte k (S k) = True
prop_lte_k_Sk 0 = Refl
prop_lte_k_Sk (S k) = prop_lte_k_Sk k

prop_lte_k_SSk : (k : Nat) -> lte k (S (S k)) = True
prop_lte_k_SSk 0 = Refl
prop_lte_k_SSk (S k) = prop_lte_k_SSk k


-- prop_minus_special : lte 1 k = True -> lte (minus k 1) k -> 
prop_minus_k1k : (k : Nat) -> lte (minus k 1) k = True
prop_minus_k1k 0 = Refl
prop_minus_k1k (S k) =
    rewrite prop_minus k in
    rewrite prop_lte_k_Sk k in
    Refl

prop_lte_c : (m : Nat) -> lte m m = True
prop_lte_c 0 = Refl
prop_lte_c (S k) = prop_lte_c k

prop_lte_S_r : (m, n : Nat) -> lte m n = True -> lte m (S n) = True
prop_lte_S_r 0 0 prf = Refl
prop_lte_S_r (S k) 0 prf = absurd prf
prop_lte_S_r 0 (S k) prf = Refl
prop_lte_S_r (S j) (S k) prf = prop_lte_S_r j k prf

prop_lte_minus : (n', m' : Nat) -> lte (minus n' (S m')) (S n') = True
prop_lte_minus 0 m' = Refl
prop_lte_minus (S k) 0 = rewrite prop_minus k in rewrite prop_lte_k_SSk k in Refl
prop_lte_minus (S k) (S j) =
    let ih = prop_lte_minus k j in
    -- lte (minus k (S j)) (S (S k)) = True
    rewrite prop_lte_S_r (minus k (S j)) (S k) ih in
    Refl

prop_minus_n_Sm : (n', m' : Nat) -> lte (minus n' (S m')) n' = True
prop_minus_n_Sm 0 0 = Refl
prop_minus_n_Sm (S k) 0 =
    rewrite prop_minus k in
    prop_lte_k_Sk k
prop_minus_n_Sm 0 (S k) = Refl
prop_minus_n_Sm (S j) (S k) =
    let ih = prop_minus_n_Sm j k in
    let rw = prop_lte_S_r (minus j (S k)) j ih in
    rw

prop_lte_Sm_minus : (m, n' : Nat) -> lte m n' = True -> lte (S m) (minus n' m) = True
prop_lte_Sm_minus m 0 prf = ?prop_lte_Sm_minus_rhs_0
prop_lte_Sm_minus m (S k) prf = ?prop_lte_Sm_minus_rhs_1

prop_lte_Sm_m : (m : Nat) -> lte (S m) m = False
prop_lte_Sm_m 0 = Refl
prop_lte_Sm_m (S k) = prop_lte_Sm_m k

prop_lte_1 : (k : Nat) -> (lte 1 k = True -> Void) -> lte 1 k = False
-- prop_lte_1 0 f = Refl
-- prop_lte_1 (S k) f = void (f Refl)
prop_lte_1 k f = prop_t_v_f (lte 1 k) f

prop_lte_1_1 : (k : Nat) -> (lte 1 k = True -> Void) -> k = 0
prop_lte_1_1 0 f = Refl
prop_lte_1_1 (S k) f = void (f Refl)

prop_lte_k_0 : (k : Nat) -> (lte k 0 = True) -> k = 0
prop_lte_k_0 0 prf = Refl
prop_lte_k_0 (S _) Refl impossible

prop_lte_1_2 : (k : Nat) -> (lte 1 (minus k 0) = True) -> Void

prop_lte_Sm_n_t : (m', n' : Nat) -> (lte (S m') n' = True) -> lte n' m' = False
prop_lte_Sm_n_t _ Z Refl impossible
prop_lte_Sm_n_t 0 (S k) prf = Refl
prop_lte_Sm_n_t (S j) (S k) prf = prop_lte_Sm_n_t j k prf

prop_lte_Sm_n_v : (m', n' : Nat) -> (lte (S m') n' = True -> Void) -> lte (S m') n' = False
-- prop_lte_Sm_n_v m' 0 f = Refl
-- prop_lte_Sm_n_v 0 (S k) f = void (f Refl)
-- prop_lte_Sm_n_v (S j) (S k) f = prop_lte_Sm_n_v j k f
prop_lte_Sm_n_v m' n' f = prop_t_v_f (lte (S m') n') f

prop_lte_Sm_n_v_t : (m', n' : Nat) -> (lte (S m') n' = True -> Void) -> lt n' (S m') = True
prop_lte_Sm_n_v_t m' 0 f = Refl
prop_lte_Sm_n_v_t 0 (S k) f = absurd (f Refl)
prop_lte_Sm_n_v_t (S j) (S k) f = prop_lte_Sm_n_v_t j k f

-- prop_lte_m_n_v : (n', m' : Nat) -> (lte n' m' = True -> Void) -> lte n' m' = False
prop_lte_Sn_m_v_lte_n_m : (k, j : Nat) -> (lte (S k) j = True -> Void) -> lte j k = True
prop_lte_Sn_m_v_lte_n_m k 0 f = Refl
prop_lte_Sn_m_v_lte_n_m 0 (S j) f = void (f Refl)
prop_lte_Sn_m_v_lte_n_m (S k) (S j) f = rewrite prop_lte_Sn_m_v_lte_n_m k j f in Refl

prop_lte_Sm_n : (m', n' : Nat) -> lte (S m') n' = False -> lte n' m' = True
prop_lte_Sm_n m' 0 prf = Refl
prop_lte_Sm_n Z (S _) Refl impossible
prop_lte_Sm_n (S j) (S k) prf = prop_lte_Sm_n j k prf

prop_lte_1_3 : (k : Nat) -> (lte 1 k = True -> Void) -> lte 1 k = False
---- prop_lte_1_3 0 f = Refl
---- prop_lte_1_3 (S k) f = void (f Refl)
-- prop_lte_1_3 k f = prop_lte_Sm_n_v Z k f
prop_lte_1_3 k f = prop_t_v_f (lte 1 k) f

prop_lte_lt : (m, n : Nat) -> lte (S m) n = True -> lte n m = False
prop_lte_lt _ Z Refl impossible
prop_lte_lt 0 (S k) prf = Refl
prop_lte_lt (S j) (S k) prf = rewrite prop_lte_lt j k prf in Refl


prop_lte_S : (m, n : Nat) -> lte (S m) n = True -> lte m n = True
prop_lte_S 0 n prf = Refl
prop_lte_S (S k) 0 prf = prf
prop_lte_S (S k) (S j) prf = prop_lte_S k j prf

prop_lte_Sm_n_n_m_v : (m', n' : Nat) -> lte (S m') n' = True -> lte n' m' = True -> Void
prop_lte_Sm_n_n_m_v m' 0 prf prf1 = absurd prf
prop_lte_Sm_n_n_m_v 0 (S k) prf prf1 = absurd prf1
prop_lte_Sm_n_n_m_v (S j) (S k) prf prf1 = prop_lte_Sm_n_n_m_v j k prf prf1

prop_lte_m_n_Sn_m : (m, n' : Nat) -> (lte m n' = True -> Void) -> lte (S n') m = True
prop_lte_m_n_Sn_m 0 0 f = absurd (f Refl)
prop_lte_m_n_Sn_m (S k) 0 f = Refl
prop_lte_m_n_Sn_m 0 (S k) f = absurd (f Refl)
prop_lte_m_n_Sn_m (S j) (S k) f = rewrite prop_lte_m_n_Sn_m j k f in Refl


prop_lte_0_nz : (n : Nat) -> Not (n = 0) -> LTE 0 n -> LTE 1 n
prop_lte_0_nz 0 nnz LTEZero = absurd (nnz Refl)
prop_lte_0_nz (S k) nnz LTEZero = LTESucc LTEZero



-- prop_divX_fuel2fst_le : (n, d : Nat) -> LTE 1 d -> LTE d n -> 
--     LT (n `minus` (d `mult` (S (divX_fuel2fst n (n `minus` d) d)))) d
-- -- prop_divX_fuel2fst_le Z Z LTEZero LTEZero impossible
-- -- prop_divX_fuel2fst_le Z Z (LTESucc _) LTEZero impossible
-- prop_divX_fuel2fst_le Z Z _ LTEZero impossible
-- -- prop_divX_fuel2fst_le (S _) Z LTEZero LTEZero impossible
-- -- prop_divX_fuel2fst_le (S _) Z (LTESucc _) LTEZero impossible
-- prop_divX_fuel2fst_le (S _) Z _ LTEZero impossible
-- prop_divX_fuel2fst_le (S n') (S d') (LTESucc LTEZero) (LTESucc x) =
--     let ih = \n' => \d' => prop_divX_fuel2fst_le n' d' _ _ in
--     let ih' = ih (S n') (S d') in
--     ih'





-- def_div : (f : Nat -> Nat -> Nat) -> (d, n : Nat) -> GT d 0 -> GTE n 0 -> GT d (n `minus` (d `mult` f n d))
def_div : DPair (Nat -> Nat -> Nat) 
    (\f => (d, n : Nat) -> GT d 0 -> GTE n 0 -> GT d (n `minus` (d `mult` f n d)))
def_div = (divXW ** (
    \d => \n => \argD => \argN => 
        case decEq (lte d n) True of
            (Yes prf) =>
                rewrite prf in
                case decEq n 0 of
                    (Yes x) => rewrite x in argD
                    (No contra) =>
                        let n1 = prop_lte_0_nz n contra argN in
                        let prf' = lteReflectsLTE d n prf in
                        ?def_div_rhs_8
            (No contra) =>
                rewrite prop_t_v_f (lte d n) contra in
                rewrite prop_mult_0 d in
                rewrite prop_minus n in
                let rw2 = prop_lte_m_n_Sn_m d n contra in
                lteReflectsLTE (S n) d rw2
    ))

-- prop_div : (f, g : Nat -> Nat -> Nat) -> def_div f -> def_div g ->
    -- (d, n : Nat) -> GT d 0 -> GTE n 0 -> f n d = g n d


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

-- the result of this seems to be obtained by a simple reduction
-- the right-hand side is immediately reduced
prop_divX_fuel2fst_i : (e, n, m : Nat) -> lte n (S e) = True -> lte (S m) n = True -> 
    S (divX_fuel2fst e (minus n (S m)) (S m)) = divX_fuel2fst (S e) n (S m)
prop_divX_fuel2fst_i _ Z _ Refl Refl impossible
prop_divX_fuel2fst_i e (S k) 0 prf Refl =
    rewrite prop_minus k in
    Refl
prop_divX_fuel2fst_i 0 (S k) (S j) prf prf1 =
    -- prf1 : lte (S j) k = True
    -- prf : lte k 0 = True
    let rw = prop_lte_k_0 k prf in
    let contra = replace {p = \r => lte (S j) r = True} rw prf1 in
    absurd contra
prop_divX_fuel2fst_i (S i) (S k) (S j) prf prf1 =
    rewrite prf1 in
    Refl

-- prop_div'_invariant : (e, n, m : Nat) -> 

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
    -- divX_fuel2fst (S n) n (S m) = divNatNZ n (S m) ItIsSucc
    divX_fuel2fst (S n) n (S m) = div' n n m
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
        (Yes prf) => -- S m' <= n'
            rewrite prf in
            -- S (if lte (S (S m')) (minus n' (S m'))
            --    then S (divX_fuel2fst n' (minus (minus n' (S m')) (S (S m'))) (S (S m')))
            --    else 0) = 
            --   (if lte n' m'
            --    then 0
            --    else S (div' n' (minus (S n') (S (S m'))) (S m')))
            case decEq (lte (S (S m')) (minus n' (S m'))) True of
                (Yes x) => -- S (S m') <= n' - (S m')
                    rewrite x in 
                    -- S (S (divX_fuel2fst n' (minus (minus n' (S m')) (S (S m'))) (S (S m')))) 
                    -- = (if lte n' m' then 0 else S (div' n' (minus (S n') (S (S m'))) (S m')))
                    rewrite prop_lte_Sm_n_t m' n' prf in
                    -- prf : lte (S m') n' = True
                    -- x : lte (S (S m')) (minus n' (S m')) = True
                    -- goal : S (S (divX_fuel2fst n' (minus (minus n' (S m')) (S (S m'))) (S (S m'))))
                    --          = S (div' n' (minus n' (S m')) (S m'))
                    -- goal' : S (divX_fuel2fst (S n') (minus n' (S m')) (S (S m')))
                    --          = div' (S n') (S n') (S m')
                    -- goal'' : divX_fuel2fst (S (S n')) (S n') (S (S m'))
                    --          = div' (S n') (S n') (S m')
                    
                    -- -- req: lte (minus n' (S m')) (S n') = True
                    -- -- req: lte (S (S m')) (minus n' (S m')) = True
                    -- let req1 = prop_lte_minus n' m' in
                    -- let rw = prop_divX_fuel2fst_i n' (minus n' (S m')) (S m') req1 x in
                    -- -- rewrite rw in
                    -- -- rewrite x in
                    -- -- let rw' = replace {p = \r => S (divX_fuel2fst n' (minus (minus n' (S m')) (S (S m'))) (S (S m'))) = (if r then S (divX_fuel2fst n' (minus (minus n' (S m')) (S (S m'))) (S (S m'))) else 0)} x _ in

                    let ih = prop_divX_fuel2fst n' m' in
                    -- ih is essentially: S (divX_fuel2fst n' (minus n' (S m')) (S m')) = div' n' n' m'
                    -- ih is essentially:    divX_fuel2fst (S n') n' (S m') = div' n' n' m'
                    let ih' = replace {p = \r => (if r then S (divX_fuel2fst n' (minus n' (S m')) (S m')) else 0) = div' n' n' m'} prf _ in

                    ?hoo_6
                (No contra) => -- S (S m') > n' - (S m')
                    rewrite prop_t_v_f (lte (S (S m')) (minus n' (S m'))) contra in
                    rewrite prop_lte_Sm_n_t m' n' prf in
                    cong S (
                        -- 0 = div' n' (minus n' (S m')) (S m')
                        let rw = prop_lte_Sm_n_v_t (S m') (minus n' (S m')) contra in
                        rewrite prop_div'2 n' (minus n' (S m')) (S m') (prop_minus_n_Sm n' m') rw in
                        Refl
                    )
        (No contra) => -- S m' > n'
            -- let rw = prop_lte_Sm_n_v m' n' contra in
            let rw = prop_t_v_f (lte (S m') n') contra in
            rewrite rw in
            let rw2 = prop_lte_Sm_n m' n' rw in
            rewrite rw2 in
            Refl

-- the same as above!
prop_divX_fuel2fst2 : (n, m : Nat) -> divX_fuel2fst (S n) n (S m) = div' n n m
prop_divX_fuel2fst2 0 m = Refl
prop_divX_fuel2fst2 (S n') m =
    case decEq n' m of
        (Yes prf) => -- n' == m, which is a special case of S n' > m
            -- a special case of n >= (S m)
            -- a special case of n > m
            rewrite prf in
            rewrite prop_lte_Sm_m m in
            rewrite prop_lte_c m in
            -- let rw = prop_minusSnSn m in
            let rw = prop_minusNN (S m) in
            rewrite rw in -- omitting some rewriting above causes problems (why?)
            rewrite prop_div'0 m in
            Refl
        (No contra) => -- m /= n'
            case decEq (lte m n') True of
                (Yes prf) => -- n' > m (since m != n'), which implies S n' > m
                    -- a special case of n >= (S m)
                    -- a special case of n > m
                    rewrite prf in
                    ?hole_2
                (No f) => -- n' < m, that is, S n' <= m
                    -- n < S m
                    -- n <= m
                    rewrite prop_t_v_f (lte m n') f in
                    rewrite prop_lte_m_n_Sn_m m n' f in
                    Refl
    -- case decEq (lte (S n') m) True of
    --     (Yes prf) => 
    --         rewrite prf in
    --         rewrite prop_lte_lt n' m prf in
    --         Refl
    --     (No contra) =>
    --         rewrite prop_lte_Sm_n_v n' m contra in
    --         let mn' = prop_lte_Sn_m_v_lte_n_m n' m contra in
    --         rewrite mn' in
    --         -- lte (S m) (minus n' m)
    --         ?prop_divX_fuel2fst2_rhs_3


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
