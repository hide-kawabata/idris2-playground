import Data.Nat
import Data.Vect
import Decidable.Equality

%default total

t : (n : Nat) -> LTE n n
t 0 = LTEZero
t (S k) = LTESucc (t k)

max' : Nat -> Nat -> Nat
max' 0 0 = 0
max' 0 (S k) = S k
max' (S k) 0 = S k
max' (S k) (S j) = let kj = max' k j in S kj

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

-- [x::ys | ys <- xs]
-- makeList x xss = [x::ys | ys <- xss]
makeLists : a -> Vect n (Vect m a) -> Vect n (Vect (S m) a)
makeLists x [] = []
makeLists x (y :: xs) = [x :: y] ++ makeLists x xs

{-
 combinations 0 [1,2,3] ---> [[]]
 combinations 1 [1,2,3] ---> [[1],[2],[3]]
 combinations 2 [1,2,3] ---> [[1,2],[1,3],[2,3]]
 combinations 3 [1,2,3] ---> [[1,2,3]]
 combinations 4 [1,2,3] ---> []
 -}
-- combinations : Int -> List a -> List (List a)
-- combinations 0 _ = [[]]
-- combinations _ [] = []
-- combinations n (x::xs) = [x::ys | ys <- combinations (n-1) xs] ++ combinations n xs

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

-- giving precondition makes this function covering (ant thus total)
-- "subX returns a Nat" <=== this is not saying what subX is
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

-- j+1 <= k+1 ==> j <= k
prop_lte_S : (j, k : Nat) -> LTE (S j) (S k) -> LTE j k
prop_lte_S 0 _ = \arg => LTEZero
prop_lte_S (S j) _ = \(LTESucc arg) => arg

-- k+1 > k
prop_lte_Z : (k : Nat) -> Not (LTE (S k) k)
prop_lte_Z Z LTEZero impossible
prop_lte_Z Z (LTESucc x) impossible
prop_lte_Z (S k) (LTESucc x) = prop_lte_Z k x

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

prop_subX_lemma3 : (r0, d0 : Nat) -> {auto pd : GTE d0 1} -> {auto ps : GTE r0 d0} -> Not (LTE (S r0) (subX r0 d0))
prop_subX_lemma3 _ Z _ impossible
prop_subX_lemma3 Z (S _) _ impossible
prop_subX_lemma3 (S r') (S d') {pd = (LTESucc y)} {ps = (LTESucc z)} x = ?prop_subX_lemma3_rhs_5

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

prop_lt : (r, d : Nat) -> not (compareNat r d == LT) = True -> GTE r d
prop_lt 0 0 Refl = LTEZero
prop_lt Z (S _) Refl impossible
prop_lt (S k) 0 Refl = LTEZero
prop_lt (S k) (S j) prf = let ih = prop_lt k j prf in LTESucc ih

prop_subX2 : (n, d : Nat) -> {auto 0 p : LTE d n} -> n > (subX n d) = True -> Not (LTE n (subX n d))
prop_subX2 0 0 {p = LTEZero} prf x = absurd prf
prop_subX2 (S n') 0 {p = LTEZero} prf (LTESucc x) = ?prop_subX2_rhs_5
prop_subX2 (S n') (S d') {p = (LTESucc y)} prf x = let ih = prop_subX2 n' d' {p=y} in ?prop_subX2_rhs_4

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

-- initialize (precondition): n, d, q<-0, r<-n
-- precondition: d > 0
-- invariant (precondition): n = q * d + r
-- precondition: r >= d <==== required to go one step further
-- postcondition: n = q' * d + r'
-- postcondition: r' < d' <==== this is not guaranteed 
-- depends on subX; subP is prefereable?
divPstep : (n, d, q, r : Nat) ->
        {auto 0 d_1 : GTE d 1} -> -- d >= 1
        {auto 0 yet : GTE r d} -> -- r >= d
        {auto 0 inv : n = (q `mult` d) `plus` r} -> -- n = q*d+r  (n = (q'+1)*d+(r'-d))
        DPair (Nat, Nat) (\(q', r') => n = (q' `mult` d) `plus` r') -- n = q'*d+r'
        -- (q' ** (r' ** n = (q' `mult` d) `plus` r')) -- n = q'*d+r'
divPstep n (S d0) q (S r0) {d_1 = (LTESucc x)} {yet = (LTESucc y)} {inv} =
    -- goal : plus (mult q (S d0)) (S r0) = S (plus (plus d0 (mult q (S d0))) (subX r0 d0))
    ((S q, subX r0 d0) **
     rewrite inv in
     rewrite plusCommutative d0 (mult q (S d0)) in
     rewrite plusSuccRightSucc (plus (mult q (S d0)) d0) (subX r0 d0) in
     -- goal : plus (mult q (S d0)) (S r0) = plus (plus (mult q (S d0)) d0) (S (subX r0 d0))
     rewrite sym $ plusAssociative (mult q (S d0)) d0 (S (subX r0 d0)) in
     -- goal : (S r0) = (plus d0 (S (subX r0 d0)))
     rewrite sym $ plusSuccRightSucc d0 (subX r0 d0) in
     -- goal : r0 = plus d0 (subX r0 d0))
     rewrite sym $ prop_plus_subX r0 d0 in
     Refl)

divPstep' : (n, d, q, r : Nat) ->
        {auto 0 d_1 : GTE d 1} -> -- d >= 1
        {auto 0 yet : GTE r d} -> -- r >= d
        {auto 0 inv : n = (q `mult` d) `plus` r} -> -- n = q*d+r  (n = (q'+1)*d+(r'-d))
        DPair (Nat, Nat) (\(q', r') => (n = (q' `mult` d) `plus` r', LTE r r' -> Void)) -- n = q'*d+r' /\ r > r'
        -- (q' ** (r' ** n = (q' `mult` d) `plus` r')) -- n = q'*d+r'
divPstep' n (S d0) q (S r0) {d_1 = (LTESucc x)} {yet = (LTESucc y)} {inv} =
    -- goal : plus (mult q (S d0)) (S r0) = S (plus (plus d0 (mult q (S d0))) (subX r0 d0))
    ((S q, subX r0 d0) **
     rewrite inv in
     rewrite plusCommutative d0 (mult q (S d0)) in
     rewrite plusSuccRightSucc (plus (mult q (S d0)) d0) (subX r0 d0) in
     -- goal : plus (mult q (S d0)) (S r0) = plus (plus (mult q (S d0)) d0) (S (subX r0 d0))
     rewrite sym $ plusAssociative (mult q (S d0)) d0 (S (subX r0 d0)) in
     -- goal : (S r0) = (plus d0 (S (subX r0 d0)))
     rewrite sym $ plusSuccRightSucc d0 (subX r0 d0) in
     -- goal : r0 = plus d0 (subX r0 d0))
     rewrite sym $ prop_plus_subX r0 d0 in
     -- LTE (S r0) (subX r0 d0) -> Void
     (Refl, ?hohooo))


-- initialize (precondition): n, d, q<-0, r<-n
-- precondition: d > 0
-- invariant (precondition): n = q * d + r
-- postcondition: n = q' * d + r'
-- postcondition: r' < d' <==== required
divP : (n, d, q, r : Nat) ->
        {auto 0 d_1 : GTE d 1} -> 
        {auto inv : n = (q `mult` d) `plus` r} ->
        DPair (Nat, Nat) (\(q', r') => n = (q' `mult` d) `plus` r')
divP n d q r {d_1} {inv} =
    case decEq (r >= d) True of
        (Yes rGTEdB) =>
            let rGTEd = prop_lt r d rGTEdB in
            let ((q', r') ** inv') = divPstep n d q r {yet=rGTEd} in
            -- divP n d q' (assert_smaller r r') {inv=post} -- <============== Why is this not accepted?
            -- let dp = divP n d q' (assert_smaller r r') {inv=inv'} in 
            -- dp
            let ((q'', r'') ** inv'') = divP n d q' (assert_smaller r r') {inv=inv'} in
            ((q'', r'') ** inv'')
        (No contra) => ((q, r) ** inv)

divPwrapper : (n, d : Nat) ->
        {auto 0 d_1 : GTE d 1} -> 
        DPair (Nat, Nat) (\(q', r') => n = (q' `mult` d) `plus` r')
divPwrapper n d {d_1} = 
    let ((q', r') ** prf) = divP n d 0 n {d_1} in
    -- goal : (lamc : (Nat, Nat) ** let (q', r') = lamc in n = plus (mult q' d) r')
    ((q', r') ** prf)

divQ : (n : Nat) -> (d : Nat) -> {auto d_1 : GTE d 1} -> {c : Either (LTE n d) (Not (LTE n d))} ->
        {r : Nat} -> DPair (Nat, Nat) (\(q, r) => (n = (q `mult` d) `plus` r, Not (GTE r d)))
divQ n d {d_1} {c} = case c of
    (Left LTEZero) =>
        let q = 0 in
        let r = 0 in
        let rw = multZeroLeftZero d in
        ((q, r) ** (?hooh, ?hooho_2))
    (Left (LTESucc x)) => ?hooho_3
    (Right x) => ?hooho_1

-- divY : (n : Nat) -> (d : Nat) -> {auto 0 d_1 : GTE d 1} -> {r : Nat} -> (q ** (n = q * d + r, Not (GTE r d)))
divY : (n : Nat) -> (d : Nat) -> {auto 0 d_1 : GTE d 1} -> {r : Nat} ->
        DPair (Nat, Nat) (\(q, r) => (n = (q `mult` d) `plus` r, Not (GTE r d)))
divY 0 (S d') {d_1 = (LTESucc x)} = let (q, r) = divX 0 (S d') in (?hoho ** ?hohos)
divY (S k) d {d_1} = ?hole_1
-- divY n d {d_1} =
--     let (q, r) = divX n d {d_1} in
--     let eq = ?prf1 in
--     let lt = ?prf2 in
--     (q ** (eq, lt))


divrem : Nat -> Nat -> Nat -> Nat -> Bool
divrem a b d r = a == b * d + r && r < b
DivRem : Nat -> Nat -> Nat -> Nat -> Type
DivRem a b d r = (a = (b `mult` d) `plus` r,  GTE r b -> Void)
prop_divrem1 : (a, b, d, r, d', r' : Nat) -> DivRem a b d r -> DivRem a b d' r' -> (d = d', r = r')
-- prop_divrem1 a b d r d' r' (x, z) (y, w) = (?part1, ?part2)
-- prop_divrem1 0 b d r d' r' (x, z) (y, w) = (?part11, ?part21)
prop_divrem1 0 0 d r d' r' (x, z) (y, w) = 
    (let z' = replace {p = \r => LTE 0 r} x LTEZero in void (z z'),
     rewrite sym x in rewrite sym y in Refl {x=0})
prop_divrem1 0 (S b') d r d' r' (x, z) (y, w) =
    -- x : 0 = plus (plus d (mult b' d)) r
    -- y : 0 = plus (plus d' (mult b' d')) r'
    let (x', r1) = prop_plus1 (plus d (mult b' d)) r x in
    let (x'', _) = prop_plus1 d (mult b' d) (sym x') in
    let (y', r2) = prop_plus1 (plus d' (mult b' d')) r' y in
    let (y'', _) = prop_plus1 d' (mult b' d') (sym y') in
    (rewrite x'' in rewrite y'' in Refl, rewrite r1 in rewrite r2 in Refl)
prop_divrem1 (S k) b d r d' r' (x, z) (y, w) =
    -- x : S k = plus (mult b d) r
    -- y : S k = plus (mult b d') r'
    let t = prop_plus2 k (mult b d) r x in
    let t' = prop_plus2 k (mult b d') r' y in
    case decEq r 0 of
      (Yes r_0) => case decEq r' 0 of
        (Yes r'_0) => (
            let s = prop_conj2 r_0 t in
            let s' = prop_conj2 r'_0 t' in
            let x2 = replace {p = \r => S k = plus (mult b d) r} r_0 x in
            let y2 = replace {p = \r' => S k = plus (mult b d') r'} r'_0 y in
            -- x2 : S k = plus (mult b d) 0
            -- y2 : S k = plus (mult b d') 0
            let eq = replace {p = \sk => sk = plus (mult b d) 0} y2 x2 in
            let eq' = replace {p = \rhs => plus (mult b d') 0 = rhs} 
                            (plusCommutative (mult b d) 0) eq in
            let eq'' = replace {p = \lhs => lhs = mult b d} (plusCommutative (mult b d') 0) eq' in
            ?part122_2,
            rewrite r_0 in rewrite r'_0 in Refl)
        (No contra) => ?part122_3
      (No contra) => ?part122_1



{- permutation and combination -}
nP : Nat -> Nat -> Nat
nP _ 0 = 1
nP 0 (S _) = 0
nP (S n) (S x) = (S n) * nP n x
nC : Nat -> Nat -> Nat
nC n x = nP n x `div` fact x
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




combinations : (x : Nat) -> (l : Vect n a) -> {c : Nat} -> c = nC (length l) x -> Vect c (Vect x a)
combinations x l Refl = ?combinations_rhs_0

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