import Data.Nat
import Data.Vect
import Decidable.Equality

%default total

-------------------------------------------------------------
max' : Nat -> Nat -> Nat
max' 0 0 = 0
max' 0 (S k) = S k
max' (S k) 0 = S k
max' (S k) (S j) = let kj = max' k j in S kj

t : (n : Nat) -> LTE n n
t 0 = LTEZero
t (S k) = LTESucc (t k)

spec_max' : {0 m : _} -> (a, b : Nat) -> max' a b = m -> 
    (Either (a = m) (b = m), LTE a m, LTE b m)
spec_max' 0 0 Refl = (Right Refl, LTEZero, LTEZero)
spec_max' 0 (S b) Refl = -- (Either (0 = S b) (S b = S b), (LTE 0 (S b), LTE (S b) (S b)))
    (Right Refl, LTEZero, t (S b))
spec_max' (S b) 0 Refl = -- (Either (S b = S b) (0 = S b), (LTE (S b) (S b), LTE 0 (S b)))
    (Left Refl, t (S b), LTEZero)
spec_max' (S k) (S j) Refl = 
    let (p, q, r) = spec_max' k j Refl in
    (case p of
          (Left x) => (Left (cong S x), rewrite sym x in t (S k), LTESucc r)
          (Right x) => (Right (cong S x), LTESucc q, rewrite sym x in LTESucc (t j)))
-------------------------------------------------------------


prop_plus1 : (a, b : Nat) -> 0 = plus a b -> (a = 0, b = 0)
prop_plus1 0 b prf = (Refl {x=0}, rewrite prf in Refl {x=b})
prop_plus1 (S k) b prf = void (uninhabited prf)
-- x : S k = plus (mult b d) r
prop_plus2 : (k, bd, r : Nat) -> S k = plus bd r -> Not (bd = 0, r = 0)
prop_plus2 k bd r prf (x, y) =
    -- prf : S k = plus bd r
    -- x : bd = 0
    -- y : r = 0
    let t = replace {p = \bd => S k = plus bd r} x prf in
    -- let t' = replace {p = \r => S k = plus bd r} y prf in
    -- t' : S k = plus bd 0
    -- let t'' = replace {p = \bd => plusCommutative bd 0} t'

    -- y : r = 0
    -- t : S k = r
    let tt = replace {p = \r => S k = r} y t in
    void (uninhabited tt)

-- eq'' : mult b d' = mult b d
prop_mult : (a, b, b' : Nat) -> mult a b = mult a b' -> b = b'

prop_conjL : {ty1, ty2 : Type} -> Not ty1 -> Not (ty1, ty2)
prop_conjL f (x, y) = f x
prop_conjR : {ty1, ty2 : Type} -> Not ty2 -> Not (ty1, ty2)
prop_conjR f (x, y) = f y

--  t : (mult b d = 0, r = 0) -> Void
--  prf : r = 0
prop_conj2 : {ty1, ty2 : Type} -> ty2 -> Not (ty1, ty2) -> Not ty1
prop_conj2 x f = \y => f (y, x)

prop_conj : {ty1, ty2 : Type} -> (ty1, ty2) -> (prf : Not ty2) -> ty1
prop_conj (x, y) prf = x

fact : Nat -> Nat
fact 0 = 1
fact (S k) = (S k) * fact k

-- j+1 <= k+1 ==> j <= k
prop_lte_S : (j, k : Nat) -> LTE (S j) (S k) -> LTE j k
prop_lte_S 0 _ = \arg => LTEZero
prop_lte_S (S j) _ = \(LTESucc arg) => arg

-- k+1 > k
prop_lte_Z : (k : Nat) -> Not (LTE (S k) k)
prop_lte_Z Z LTEZero impossible
prop_lte_Z Z (LTESucc x) impossible
prop_lte_Z (S k) (LTESucc x) = prop_lte_Z k x

prop_lte_S2 : (j, k : Nat) -> LTE (S j) k -> LTE j k
prop_lte_S2 0 k x = LTEZero
prop_lte_S2 (S j') (S k') (LTESucc x) = let ih = prop_lte_S2 j' k' x in LTESucc ih

prop_lte_S3 : (j, k : Nat) -> LTE j k -> LTE j (S k)
prop_lte_S3 0 k LTEZero = LTEZero
prop_lte_S3 (S j') (S k') (LTESucc x) = let ih = prop_lte_S3 j' k' x in LTESucc ih

prop_lte_assoc : (j, k, l : Nat) -> LTE j k -> LTE k l -> LTE j l
prop_lte_assoc 0 k l LTEZero y = LTEZero
prop_lte_assoc (S j') (S k') (S l') (LTESucc x) (LTESucc y) =
    let ih = prop_lte_assoc j' k' l' x y in
    LTESucc ih

prop_plus_ge0 : (n, m : Nat) -> GTE (plus n m) 0
prop_plus_ge0 0 m = LTEZero
prop_plus_ge0 (S n') m = LTEZero

-- Type-to-Bool
t2b_plus_ge0 : (n, m : Nat) -> GTE n 1 -> 0 < plus n m = True
t2b_plus_ge0 (S n') m (LTESucc x) = Refl

prop_mult_ge0 : (n, m : Nat) -> GTE (mult n m) 0
prop_mult_ge0 0 m = LTEZero
prop_mult_ge0 (S n') m =
    let prf = prop_plus_ge0 0 (plus m (mult n' m)) in
    prf
    
prop_plus_geN : (n : Nat) -> GTE (plus n 0) n
prop_plus_geN 0 = LTEZero
prop_plus_geN (S n') = LTESucc (prop_plus_geN n')

prop_plus_geNMN : (n, m : Nat) -> GTE (plus n m) n
prop_plus_geNMN n 0 = prop_plus_geN n
prop_plus_geNMN 0 (S m') = LTEZero
prop_plus_geNMN (S n') (S m') =
    let ih = prop_plus_geNMN n' m' in
    rewrite sym $ plusSuccRightSucc n' m' in
    let rw = prop_lte_S3 n' (plus n' m') ih in
    LTESucc rw

prop_fact_ge1 : (n : Nat) -> GTE (fact n) 1
prop_fact_ge1 0 = LTESucc LTEZero
prop_fact_ge1 (S n') =
    let ih = prop_fact_ge1 n' in
    -- goal : LTE 1 (plus (fact n') (mult n' (fact n')))
    -- let e1 = prop_mult_ge0 n' (fact n') in
    let e2 = prop_plus_geNMN (fact n') (mult n' (fact n')) in
    prop_lte_assoc 1 (fact n') (plus (fact n') (mult n' (fact n'))) ih e2
    

----------------------------------------------------------------------------
-- giving precondition makes this function covering (ant thus total)
-- "subX returns a Nat" <=== this is not saying what subX is
-- implementation of subtraction for naturals; no proof accompanied
subX : (a, b : Nat) -> {auto 0 p : GTE a b} -> Nat
subX a 0 {p = LTEZero} = a
subX (S a') (S b') {p = (LTESucc x)} = subX a' b'

-- "for all a and b, a = b + (subX a b) holds"
-- "You can obtain a Nat r such that a = b + r by using the function subX."
spec_subX : (a, b : Nat) -> {auto 0 p : GTE a b} -> a = b `plus` (a `subX` b)
spec_subX a 0 {p = LTEZero} = Refl
spec_subX (S a') (S b') {p = (LTESucc x)} = let ih = spec_subX a' b' in cong S ih

-- "subP returns r of Nat such that a = b + r"
-- "You can obtain a Nat r such that a = b + r by using this function, subP."
-- proof carrying code; spec is intrinsically proven
subP : (a, b : Nat) -> {auto 0 p : GTE a b} -> (r ** a = b `plus` r)
subP a 0 {p = LTEZero} = (a ** Refl)
subP (S a') (S b') {p = (LTESucc x)} = let (w ** prf) = subP a' b' in (w ** cong S prf)

-- "subP0 performs just like subX" <=== this is not saying what subX is
subP0 : (a, b : Nat) -> {auto 0 p : GTE a b} -> (r ** r = a `subX` b)
subP0 a 0 {p = LTEZero} = (a ** Refl)
subP0 (S a') (S b') {p = (LTESucc x)} = subP0 a' b'

-- "subP0' performs just like subX" <=== this is not saying what subX is
subP0' : (a, b : Nat) -> {auto 0 p : GTE a b} -> (r ** r = a `subX` b)
subP0' a b = (subX a b ** Refl) -- subP0' is just a copy of subX
----------------------------------------------------------------------------

-- n >= d ==> n <= d (bool -> prop)
prop_gte : (n, d : Nat) -> n >= d = True -> GTE n d
prop_gte 0 0 Refl = LTEZero
prop_gte 0 (S k) prf = void $ uninhabited prf
prop_gte (S k) 0 Refl = LTEZero
prop_gte (S k) (S j) prf = let ih = prop_gte k j prf in LTESucc ih

-- a+1 <= b ==> a <= b
prop_lte : (a, b : Nat) -> LTE (S a) b -> LTE a b
prop_lte 0 b x = LTEZero
prop_lte (S _) Z LTEZero impossible
prop_lte (S _) Z (LTESucc x) impossible
prop_lte (S k) (S j) (LTESucc x) = let ih = prop_lte k j x in LTESucc ih

-- n >= d ==> subX n d >= 0
prop_subX0 : (n, d : Nat) -> {auto 0 p : GTE n d} -> GTE (subX n d) Z
prop_subX0 0 0 {p = LTEZero} = LTEZero
prop_subX0 Z (S _) impossible
prop_subX0 Z (S _) impossible
prop_subX0 (S k) 0 {p = LTEZero} = LTEZero
prop_subX0 (S k) (S j) {p} = LTEZero

-- k >= k ==> subX k k == 0
prop_subX1 : (k : Nat) -> {auto 0 p : GTE k k} -> subX k k = Z
prop_subX1 0 = Refl {x=0}
prop_subX1 (S k) {p = (LTESucc x)} = prop_subX1 k

prop_plus_subX : (r, d : Nat) -> {auto 0 p : GTE r d} -> r = plus d (subX r d)
prop_plus_subX r 0 = Refl
prop_plus_subX (S r') (S k) {p = (LTESucc x)} = let ih = prop_plus_subX r' k in cong S ih


-- prop_gtelte : (k : Nat) -> LTE k k -> GTE k k
-- prop_gtelte k x = x

-- tf_gtelte : (k, j : Nat) -> LTE j k -> GTE k j
-- tf_gtelte k j x = x

-- subX k k == 0
prop_subX_kk : (k : Nat) -> subX k k {p = t k} = 0
prop_subX_kk 0 = Refl
prop_subX_kk (S k) = let ih = prop_subX_kk k in ih

-- prf : k = j
-- t : LTE k (subX k j)
-- prop_funny : (k, j : Nat) -> (prf : k = j) -> (t : LTE k (subX k j)) -> LTE k
-- k+1 > (k+1)-(k+1)
prop_subX_lemma : (k : Nat) -> Not (LTE (S k) (subX (S k) (S k) {p=t (S k)}))
prop_subX_lemma Z LTEZero impossible
prop_subX_lemma Z (LTESucc x) impossible
prop_subX_lemma (S k) x =
    let t = prop_subX_kk k in
    -- x : LTE (S (S k)) (subX k k)
    -- t : subX k k = 0
    let x' = replace {p = \skk => LTE (S (S k)) skk} t x in
    void $ uninhabited x'
-- k+1 > (j-j)
prop_subX_lemma' : (k, j : Nat) -> Not (LTE (S k) (subX j j {p=t j}))
prop_subX_lemma' _ Z LTEZero impossible
prop_subX_lemma' _ Z (LTESucc x) impossible
prop_subX_lemma' k (S j') x = let ih = prop_subX_lemma' k j' in ih x

-- j+1 <= k+1 ==> k+1 <= (k+1)-(j+1) ==> j+1 <= 0
prop_subX_lemma2 : (j, k : Nat) -> (prf : LTE (S j) (S k)) -> LTE (S k) (subX (S k) (S j)) -> LTE (S j) Z
prop_subX_lemma2 Z Z (LTESucc x) = \arg => arg
prop_subX_lemma2 Z (S k) (LTESucc LTEZero) = \(LTESucc arg) => let v = prop_lte_Z k arg in void v
prop_subX_lemma2 (S j) Z LTEZero impossible
prop_subX_lemma2 (S j) Z (LTESucc x) impossible
prop_subX_lemma2 (S j) (S k) LTEZero impossible
prop_subX_lemma2 (S j) (S k) (LTESucc x) =
    let ih = prop_subX_lemma2 j k x in 
    \arg => let tmp = prop_lte (S k) (subX (S k) (S j)) arg in
    let pp = ih tmp in absurd pp

prop_subX_lemma3 : (r0, d0 : Nat) -> {auto ps : GTE r0 d0} -> Not (LTE (S r0) (subX r0 d0))
prop_subX_lemma3 r0 0 {ps = LTEZero} x = let co = prop_lte_Z r0 x in co
prop_subX_lemma3 (S r') (S d') {ps = (LTESucc y)} x =
    let ih = prop_subX_lemma3 r' d' in
    -- x : LTE (S (S r')) (subX r' d')
    let co = prop_lte_S2 (S r') (subX r' d') x in
    ih co

-- d >= 1 && n >= d ==> -d <= -1 ==> n-d <= n-1 < n  ==> n-d < n
prop_subX : (n, d : Nat) -> {auto pd : GTE d 1} -> {auto ps : GTE n d} -> Not (GTE (subX n d) n)
prop_subX Z Z _ impossible
prop_subX Z (S _) _ impossible
prop_subX (S _) Z _ impossible
prop_subX (S k) (S j) {pd} {ps} pg = 
    case decEq k j of
         (Yes (Refl {x})) => 
            -- ps : LTE (S x) (S x)
            -- pg : LTE (S x) (subX (S x) (S x))
            -- pd : LTE 1 (S x)
            let subXz = prop_subX1 (S x) in
            let pg' = replace {p = \arg2 => LTE (S x) arg2} subXz pg in
            absurd pg'
         (No contra) =>
            -- ps : LTE (S j) (S k)                 -- j <= k
            -- pg : LTE (S k) (subX (S k) (S j))    -- k+1 <= (k+1)-(j+1)   -- j+1 <= 0  <== contradiction
            -- pd : LTE 1 (S j)                     -- 1 <= j+1
            -- contra : k = j -> Void               -- k != j
            let subXjk = subX (S k) (S j) {p=ps} in
            let pg' = prop_subX_lemma2 j k ps pg in
            absurd pg'

-- Type-to-Bool conversion
-- t2b_lte

-- Bool-to-Type conversion
prop_lt : (r, d : Nat) -> not (compareNat r d == LT) = True -> GTE r d
prop_lt 0 0 Refl = LTEZero
prop_lt Z (S _) Refl impossible
prop_lt (S k) 0 Refl = LTEZero
prop_lt (S k) (S j) prf = let ih = prop_lt k j prf in LTESucc ih

-- Bool-to-Type conversion
prop_ltv : (r, d : Nat) -> (not (compareNat r d == LT) = True -> Void) -> Not (GTE r d)
prop_ltv 0 0 f LTEZero = f Refl
prop_ltv (S r') 0 f LTEZero = f Refl
prop_ltv (S r') (S d') f (LTESucc x) = let ih = prop_ltv r' d' f x in ih

prop_subX2 : (n, d : Nat) -> {auto 0 p : LTE d n} -> n > (subX n d) = True -> Not (LTE n (subX n d))
prop_subX2 0 0 {p = LTEZero} prf x = absurd prf
prop_subX2 (S n') 0 {p = LTEZero} prf (LTESucc x) = ?prop_subX2_rhs_5
prop_subX2 (S n') (S d') {p = (LTESucc y)} prf x = let ih = prop_subX2 n' d' {p=y} in ?prop_subX2_rhs_4

-----------------------------------------------------------------------------
-- giving precondition makes this function covering
divX : (n : Nat) -> (d : Nat) -> {auto 0 d_1 : GTE d 1} -> (Nat, Nat)
divX n d {d_1} = case decEq (n >= d) True of
    (Yes prf) =>
        let (q, r) = divX (assert_smaller n (subX n d {p=prop_gte n d prf})) d in -- prop_subX guarantees n < n-d
        (S q, r)
    (No contra) => (Z, n)

divX' : (n : Nat) -> (d : Nat) -> {auto 0 d_1 : GTE d 1} -> (Nat, Nat)
divX' n d {d_1} = case decEq (n >= d) True of
    (Yes prf) =>
        -- let (q, r) = divX' (assert_smaller n (subX n d {p=prop_gte n d prf})) d in -- prop_subX guarantees n < n-d
        -- (S q, r)
        case decEq (n > subX n d {p=prop_gte n d prf}) True of
            (Yes x) =>
                -- prf : not (compareNat n d == LT) = True
                -- x : compareNat n (subX n d) == GT = True
                let prf' = prop_lt n d prf in
                ?hohoholle_0
            (No contra) =>
                -- prf : not (compareNat n d == LT) = True
                -- contra : compareNat n (subX n d) == GT = True -> Void
                ?hohoholle_1
    (No contra) => (Z, n)

-- n = plus (mult q d) r =======> How can I obtain pre' : n = plus (mult (S q) d) r' ?
eq_calc1 : (n, d, q, r : Nat) -> {r' : Nat} -> {auto pre : n = plus (mult q d) r} -> {auto prf : GTE r d} -> r' = subX r d {p = prf} -> n = plus (mult (S q) d) r'
eq_calc1 n d q r {r'} {pre} {prf} eqprf = ?hole

-- typical initialization: n, d, q<-0, r<-n
-- precondition: d > 0
-- precondition: n = q * d + r
-- precondition: r >= d <==== required to go one step further
-- postcondition: n = q' * d + r' /\ r > r'
-- depends on subX
divPstep : (n, d, q, r : Nat) ->
        {auto 0 d_1 : GTE d 1} -> -- d >= 1
        {auto yet : GTE r d} -> -- r >= d <========== yet is used in the evaluation!
        {auto 0 inv : n = (q `mult` d) `plus` r} -> -- n = q*d+r  (n = (q'+1)*d+(r'-d))
        DPair (Nat, Nat) (\(q', r') => (n = (q' `mult` d) `plus` r', LTE r r' -> Void)) -- n = q'*d+r' /\ r > r'
divPstep n (S d0) q (S r0) {d_1 = (LTESucc x)} {yet = (LTESucc y)} {inv} =
    ((S q, subX r0 d0) **
     rewrite inv in
     rewrite plusCommutative d0 (mult q (S d0)) in
     rewrite plusSuccRightSucc (plus (mult q (S d0)) d0) (subX r0 d0) in
     rewrite sym $ plusAssociative (mult q (S d0)) d0 (S (subX r0 d0)) in
     rewrite sym $ plusSuccRightSucc d0 (subX r0 d0) in
     rewrite sym $ prop_plus_subX r0 d0 in -- LTE (S r0) (subX r0 d0) -> Void
     let prf = prop_subX_lemma3 r0 d0 in -- y, which is depending on yet, is used here implicitly
     (Refl, prf))

-- typical initialization: n, d, q<-0, r<-n
-- precondition: d > 0
-- precondition: n = q * d + r
-- postcondition: n = q' * d + r' /\ r' < d
divP : (n, d, q, r : Nat) ->
        {auto 0 d_1 : GTE d 1} -> 
        {auto inv : n = (q `mult` d) `plus` r} ->
        DPair (Nat, Nat) (\(q', r') => (n = (q' `mult` d) `plus` r', Not (GTE r' d)))
divP n d q r {d_1} {inv} =
    case decEq (r >= d) True of
        (Yes rGTEdB) =>
            let rGTEd = prop_lt r d rGTEdB in -- Bool-to-Type conversion
            let ((q', r') ** (inv', aux)) = divPstep n d q r {yet=rGTEd} in -- stronger version, aux : Not (LTE r r')
            -- divP n d q' (assert_smaller r r') {inv=inv'} -- <============== NG (Why???)
            -- let dp = divP n d q' (assert_smaller r r') {inv=inv'} in dp -- <==== still NG
            -- let ((q'', r'') ** inv'') = divP n d q' r' {inv=inv'} in ((q'', r'') ** inv'') -- NG, non-terminating, aux is useless
            let ((q'', r'') ** inv'') = divP n d q' (assert_smaller r r') {inv=inv'} in ((q'', r'') ** inv'') -- OK
        (No contra) =>
            -- not (compareNat r d == LT) = True -> Void
            let prf = prop_ltv r d contra in -- Bool-to-Type conversion
            ((q, r) ** (inv, prf))

-- proof carrying code of division for naturals
divPwrapper : (n, d : Nat) ->
        {auto 0 d_1 : GTE d 1} -> 
        DPair (Nat, Nat) (\(q', r') => (n = (q' `mult` d) `plus` r', Not (GTE r' d)))
divPwrapper n d {d_1} = 
    let ((q', r') ** prf) = divP n d 0 n {d_1} in
    -- goal : (lamc : (Nat, Nat) ** let (q', r') = lamc in n = plus (mult q' d) r')
    ((q', r') ** prf)
-----------------------------------------------------------------------------


-- permutation (functional specification)
nP : Nat -> Nat -> Nat
nP _ 0 = 1
nP 0 (S _) = 0
nP (S n) (S x) = (S n) * nP n x

-- combinations --------------------------------------------------------------
-- using nP and div (primitive)
nC : Nat -> Nat -> Nat
nC n x = nP n x `div` fact x

-- direct definition using div (primitive)
nC' : Nat -> Nat -> Nat
nC' _ 0 = 1
nC' 0 (S _) = 0
nC' (S n) (S x) = ((S n) `mult` nC' n x) `div` (S x)

nC_nC' : (n, x : Nat) -> nC n x = nC' n x
nC_nC' 0 0 = ?nC_nC'_rhs_2 -- divNat 1 1 = 1
nC_nC' 0 (S k) = ?nC_nC'_rhs_3 -- divNat 0 (plus (fact k) (mult k (fact k))) = 0
nC_nC' (S k) 0 = ?nC_nC'_rhs_4 -- divNat 1 1 = 1
nC_nC' (S k) (S j) = let ih = nC_nC' k j in ?nC_nC'_rhs_5 -- divNat (plus (nP k j) (mult k (nP k j))) (plus (fact j) (mult j (fact j))) = divNat (plus (nC' k j) (mult k (nC' k j))) (S j)
-- all of the above lines are provable with appropriate lemmas about divNat and arithmetic rules for Nat
{- Note: about div
    Main> :printdef div
    Prelude.div : Integral ty => ty -> ty -> ty
    div = \arg, arg => __bind_div arg arg
    Main> :t divNat
    Data.Nat.divNat : Nat -> Nat -> Nat
    Main> :printdef divNat
    Data.Nat.divNat : Nat -> Nat -> Nat
    divNat left (S right) = divNatNZ left (S right) ItIsSucc
    Main> :printdef divNatNZ
    Data.Nat.divNatNZ : Nat -> (y : Nat) -> (0 _ : NonZero y) -> Nat
    divNatNZ left (S right) _ = div' left left right
    Main> :printdef div'      
    Data.Nat.div' : Nat -> Nat -> Nat -> Nat
    div' 0 centre right = 0
    div' (S fuel) centre right = if lte centre right then 0 else S (div' fuel (minus centre (S right)) right)
    Main> :total div
    Prelude.Num.div is total
    Main> :total divNat
    Data.Nat.divNat is not covering all cases
    Main> :total divNatNZ
    Data.Nat.divNatNZ is total
    Main> :total div'
    Data.Nat.div' is total
 -}


-- using nP and divX
nC1 : Nat -> Nat -> Nat
nC1 n x =
    let fGE1 = prop_fact_ge1 x in
    let (q, r) = divX (nP n x) (fact x) {d_1=fGE1} in q

-- using nP and divPwrapper
nC1' : Nat -> Nat -> Nat
nC1' n x =
    let fGE1 = prop_fact_ge1 x in
    let ((q, r) ** prf) = divPwrapper (nP n x) (fact x) {d_1=fGE1} in q

-- direct definition using divX
nC2 : Nat -> Nat -> Nat
nC2 _ 0 = 1
nC2 0 (S _) = 0
nC2 (S n) (S x) = let (q, r) = divX ((S n) `mult` nC2 n x) (S x) in q

-- direct definition using divPwrapper (inappropreately heavy)
nC2' : Nat -> Nat -> Nat
nC2' _ 0 = 1
nC2' 0 (S _) = 0
nC2' (S n) (S x) = let ((q, r) ** prf) = divPwrapper ((S n) `mult` nC2' n x) (S x) in q


-- prop_nC2_Z : (x : Nat) -> nC2 0 x = 0
-- prop_nC2_Z 0 = ?prop_nC2_Z_rhs_0
-- prop_nC2_Z (S k) = ?prop_nC2_Z_rhs_1


-- [x::ys | ys <- xs]
-- makeList x xss = [x::ys | ys <- xss]
makeLists : a -> Vect n (Vect m a) -> Vect n (Vect (S m) a)
makeLists x [] = []
makeLists x (y :: xs) = [x :: y] ++ makeLists x xs

makeListsL : a -> List (List a) -> List (List a)
makeListsL x [] = []
makeListsL x (y :: xs) = [x :: y] ++ makeListsL x xs

{-
 combinations 0 [1,2,3] ---> [[]]
 combinations 1 [1,2,3] ---> [[1],[2],[3]]
 combinations 2 [1,2,3] ---> [[1,2],[1,3],[2,3]]
 combinations 3 [1,2,3] ---> [[1,2,3]]
 combinations 4 [1,2,3] ---> []
 -}
combinationsL : Int -> List a -> List (List a)
combinationsL 0 _ = [[]]
combinationsL _ [] = []
combinationsL n (x::xs) = [x::ys | ys <- combinationsL (n-1) xs] ++ combinationsL n xs
combinationsL' : Int -> List a -> List (List a)
combinationsL' 0 _ = [[]]
combinationsL' _ [] = []
combinationsL' n (x::xs) = makeListsL x (combinationsL' (n-1) xs) ++ combinationsL n xs

-- requires properties of divNat, ...
combinations : (x : Nat) -> (l : Vect n a) -> {c : Nat} -> c = nC (length l) x -> Vect c (Vect x a)
combinations 0 [] Refl = ?combinations_rhs_4
combinations (S k) [] prf = ?combinations_rhs_3
combinations x (y :: xs) prf = ?combinations_rhs_1

combinations' : (x : Nat) -> (ys : Vect n a) -> {c : Nat} -> c = nC' (length ys) x -> Vect c (Vect x a)
combinations' 0 [] Refl = [[]]
combinations' (S x') [] Refl = []
combinations' x (y :: ys') prf =
    let l1 = combinations' x ys' in -- requires the proof of c = nC' (length ys') x
    -- let l2 = makeLists x (combinations' (subX x 1) ys') in -- needs info about ?c = nC' (length ys') (subX x 1)
    ?combinations'_rhs_2

combinations1 : (x : Nat) -> (ys : Vect n a) -> {c : Nat} -> c = nC1 (length ys) x -> Vect c (Vect x a)
combinations1 0 [] Refl = [[]]
combinations1 (S x') [] Refl =
    let e1 = prop_fact_ge1 x' in
    let e1' = t2b_plus_ge0 (fact x') (mult x' (fact x')) e1 in
    rewrite e1' in
    []
combinations1 x (y :: ys') Refl =
    -- goal
    -- Vect (let (q, r) = case decEq (not (compareNat (nP (S (length ys')) x) (fact x) == LT)) True of
    --  { Yes prf => 
    --        let (q, r) = divX (assert_smaller (nP (S (length ys')) x) (subX (nP (S (length ys')) x) (fact x))) (fact x) in
    --        (S q, r) ;
    --    No contra => (0, nP (S (length ys')) x) }
    --        in q) (Vect x a)
    let l1 = combinations1 x ys' in -- requires the proof of c = nC1 (length ys) x
    -- let l2 = makeLists x (combinations1 (subX x 1) ys') in -- needs info about ?c = nC1 (length ys') (subX x 1) 
    ?combinations1_rhs_2

combinations1' : (x : Nat) -> (l : Vect n a) -> {c : Nat} -> c = nC1' (length l) x -> Vect c (Vect x a)
combinations1' 0 [] Refl = [[]]
combinations1' (S x') [] prf = ?combinations1'_rhs_4
combinations1' x (y :: xs) prf = ?combinations1'_rhs_1

combinations2 : (x : Nat) -> (ys : Vect n a) -> {c : Nat} -> c = nC2 (length ys) x -> Vect c (Vect x a)
combinations2 0 [] Refl = [[]]
combinations2 (S x') [] Refl = []
combinations2 x (y :: ys') Refl =
    let l1 = combinations2 x ys' in -- requires the proof of c = nC2 (length ys') x
    -- let l2 = makeLists x (combinations2 (subX x 1) ys') in -- needs info about ?c = nC2 (length ys') (subX x 1)
    ?combinations2_rhs_2

combinations2' : (x : Nat) -> (ys : Vect n a) -> {c : Nat} -> c = nC2' (length ys) x -> Vect c (Vect x a)
combinations2' 0 [] Refl = [[]]
combinations2' (S x') [] Refl = []
combinations2' x (y :: ys') prf =
    let l1 = combinations2' x ys' in -- requires the proof of c = nC2' (length ys') x
    -- let l2 = makeLists x (combinations2' (subX x 1) ys') in -- needs info about ?c = nC2' (length ys') (subX x 1)
    ?combinations2'_rhs_1


-- combinations : (x : Nat) -> (l : Vect n a) -> LTE x n -> Vect (S n) (Vect x a)
-- combinations 0 [] LTEZero = [[]]
-- combinations 0 (x :: xs) LTEZero = [] :: combinations 0 xs LTEZero
-- combinations (S _) [] LTEZero impossible
-- combinations (S _) [] (LTESucc x) impossible
-- combinations (S k) (x :: xs) y = ?hole
-- combinations (S k) (x :: xs) y = makeLists x (combinations k xs ?p) ++ combinations (S k) xs ?p2

-- combinations 0 _ = [[]]
-- combinations _ [] = []
-- combinations n (x::xs) = [x::ys | ys <- combinations (n-1) xs] ++ combinations n xs


-- spec1_combinations_length