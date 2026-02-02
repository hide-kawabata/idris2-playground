module MyInteger

import Data.Nat
import Decidable.Equality

%default total

data MISign = Pos | Neg
data MyInteger = MI MISign Nat

convMIToI : MyInteger -> Integer
convMIToI (MI Pos k) = natToInteger k
convMIToI (MI Neg k) = negate (natToInteger k)

convIToMI : Integer -> MyInteger
convIToMI i = if i >= 0 then MI Pos (integerToNat i) else MI Neg (integerToNat (-i))

--------------------------------------------------

negateMI : MyInteger -> MyInteger
negateMI (MI _ 0) = MI Pos 0
negateMI (MI Pos abs) = MI Neg abs
negateMI (MI Neg abs) = MI Pos abs

normalizeMI : MyInteger -> MyInteger
normalizeMI (MI Neg 0) = MI Pos 0
normalizeMI mi = mi

plusMI : MyInteger -> MyInteger -> MyInteger
plusMI (MI Neg abs1) (MI Neg abs2) = normalizeMI $ MI Neg (plus abs1 abs2)
plusMI (MI Neg abs1) (MI Pos abs2) = case abs1 >= abs2 of
                                            False => MI Pos (minus abs2 abs1)
                                            True => normalizeMI $ MI Neg (minus abs1 abs2)
plusMI (MI Pos abs1) (MI Neg abs2) = case abs1 >= abs2 of
                                            False => normalizeMI $ MI Neg (minus abs2 abs1)
                                            True => MI Pos (minus abs1 abs2)
plusMI (MI Pos abs1) (MI Pos abs2) = MI Pos (plus abs1 abs2)

minusMI : MyInteger -> MyInteger -> MyInteger
minusMI x y = normalizeMI $ plusMI x (negateMI y)

-- plusI : Integer -> Integer -> Integer
-- plusI i j = let mi = convIToMI i
--                 mj = convIToMI j in
--             let mk = plusMI mi mj in
--             convMIToI mk

multMI : MyInteger -> MyInteger -> MyInteger
multMI (MI Pos k) (MI Pos j) = MI Pos (mult k j)
multMI (MI Pos k) (MI Neg j) = normalizeMI $ MI Neg (mult k j)
multMI (MI Neg k) (MI Pos j) = normalizeMI $ MI Neg (mult k j)
multMI (MI Neg k) (MI Neg j) = MI Pos (mult k j)

-- multI : Integer -> Integer -> Integer
-- multI i j = let mi = convIToMI i
--                 mj = convIToMI j in
--             let mk = multMI mi mj in
--             convMIToI mk

zeroMI, oneMI, twoMI, threeMI : MyInteger
zeroMI = MI Pos Z
-- oneMI : MyInteger
oneMI = MI Pos (S Z)
-- twoMI : MyInteger
twoMI = MI Pos (S (S Z))
threeMI = MI Pos (S (S (S Z)))

ltMI : MyInteger -> MyInteger -> Bool
ltMI (MI Pos k) (MI Pos j) = k < j
ltMI (MI Pos k) (MI Neg j) = False
ltMI (MI Neg k) (MI Pos j) = True
ltMI (MI Neg k) (MI Neg j) = k > j
-- ltMItest01 : ltMI (convIToMI 3) (convIToMI 3) = False
-- ltMItest01 = Refl
-- ltMItest02 : ltMI (convIToMI 3) (convIToMI 4) = True
-- ltMItest02 = Refl
-- ltMItest03 : ltMI (convIToMI 4) (convIToMI 3) = False
-- ltMItest03 = Refl
-- ltMItest04 : ltMI (convIToMI (-3)) (convIToMI (-3)) = False
-- ltMItest04 = Refl
-- ltMItest05 : ltMI (convIToMI (-3)) (convIToMI (-4)) = False
-- ltMItest05 = Refl
-- ltMItest06 : ltMI (convIToMI (-4)) (convIToMI (-3)) = True
-- ltMItest06 = Refl
-- ltMItest07 : ltMI (convIToMI (3)) (convIToMI (-4)) = False
-- ltMItest07 = Refl
-- ltMItest08 : ltMI (convIToMI (-4)) (convIToMI (3)) = True
-- ltMItest08 = Refl
eqMI : MyInteger -> MyInteger -> Bool
eqMI (MI Pos k) (MI Pos j) = k == j
eqMI (MI Pos 0) (MI Neg 0) = True
eqMI (MI Pos _) (MI Neg _) = False
eqMI (MI Neg 0) (MI Pos 0) = True
eqMI (MI Neg _) (MI Pos _) = False
eqMI (MI Neg k) (MI Neg j) = k == j
-- eqMItest01 : eqMI (convIToMI 3) (convIToMI 4) = False
-- eqMItest01 = Refl
leMI : MyInteger -> MyInteger -> Bool
leMI x y = eqMI x y || ltMI x y
gtMI : MyInteger -> MyInteger -> Bool
gtMI x y = leMI y x
geMI : MyInteger -> MyInteger -> Bool
geMI x y = eqMI x y || gtMI x y

-----------------------------------------------

covering
more : MyInteger -> MyInteger
more x = if leMI x zeroMI then oneMI else plusMI (more (minusMI x twoMI)) threeMI


-----------------------------------------------

isZeroMI : MyInteger -> Bool
isZeroMI (MI _ 0) = True
isZeroMI (MI _ _) = False

plusMIZeroLeftNeutral : (mi : MyInteger) -> plusMI (MI Pos 0) mi = normalizeMI mi
plusMIZeroLeftNeutral (MI Pos k) = Refl {x = MI Pos k}
plusMIZeroLeftNeutral (MI Neg 0) = Refl {x = MI Pos 0}
plusMIZeroLeftNeutral (MI Neg (S k)) = Refl {x = MI Neg (S k)}

plusMIZeroRightNeutral : (mi : MyInteger) -> plusMI mi (MI Pos 0) = normalizeMI mi
plusMIZeroRightNeutral (MI Pos k) = rewrite plusZeroRightNeutral k in Refl {x = MI Pos k}
plusMIZeroRightNeutral (MI Neg 0) = Refl {x = MI Pos 0}
plusMIZeroRightNeutral (MI Neg (S k)) = Refl {x = MI Neg (S k)}

ltORltF : (k, j : Nat) -> Either (k < j = True) (k < j = False)
ltORltF 0 0 = Right (Refl {x = False})
ltORltF 0 (S k) = Left (Refl {x = True})
ltORltF (S k) 0 = Right (Refl {x = False})
ltORltF (S k) (S j) = let ih = ltORltF k j in ih

ltORge : (k, j : Nat) -> Either (k < j = True) (k >= j = True)
ltORge 0 0 = Right (Refl {x = True})
ltORge 0 (S k) = Left (Refl {x = True})
ltORge (S k) 0 = Right (Refl {x = True})
ltORge (S k) (S j) = let ih = ltORge k j in ih

lttrans : (k, j, i : Nat) -> k < j = True -> j < i = True -> k < i = True 
lttrans 0 0 i prf prf1 = prf1
lttrans 0 (S k) 0 prf prf1 = prf1
lttrans 0 (S k) (S j) prf prf1 = prf
lttrans (S _) 0 _ Refl _ impossible
lttrans (S k) (S j) 0 prf prf1 = prf1
lttrans (S k) (S j) (S i) prf prf1 = 
    let ih = lttrans k j i prf prf1 in
    ih

lt0contra : (i : Nat) -> i < 0 = True -> Void
lt0contra 0 Refl impossible
lt0contra (S _) Refl impossible

le0Zero : (k : Nat) -> k <= 0 = True -> k = 0
le0Zero 0 prf = Refl
le0Zero (S k) prf = absurd prf


-- t1 0 0 prf prf1 = void (prf1 Refl)
-- t1 0 (S k) prf prf1 = Refl
-- t1 (S k) 0 prf prf1 = prf
-- t1 (S k) (S j) prf prf1 = ?holall

kLTj_jLEkF : (k, j : Nat) -> k < j = True -> j <= k = False
kLTj_jLEkF 0 0 prf = rewrite prf in Refl
kLTj_jLEkF 0 (S k) prf = Refl
kLTj_jLEkF (S _) 0 Refl impossible
kLTj_jLEkF (S k) (S j) prf = let ih = kLTj_jLEkF k j prf in ih

t1pre : (k, j : Nat) -> (k >= j = True -> Void) -> k < j = True
t1pre 0 0 f = void (f Refl)
t1pre 0 (S k) f = Refl
t1pre (S k) 0 f = void (f Refl)
t1pre (S k) (S j) f = let ih = t1pre k j f in ih

kLEj_kEQV_kLTj : (k, j : Nat) -> k <= j = True -> (k = j -> Void) -> k < j = True
kLEj_kEQV_kLTj 0 0 prf f = void (f Refl)
kLEj_kEQV_kLTj (S k) 0 prf f = prf
kLEj_kEQV_kLTj k (S j) prf f = let lt = t1pre k (S j) in ?t1_rhs_1

ltTltF : (k, j : Nat) -> k < j = True -> j < k = False
ltTltF 0 0 prf = Refl
ltTltF 0 (S k) prf = Refl
ltTltF (S k) 0 prf = rewrite prf in Refl
ltTltF (S k) (S j) prf = ltTltF k j prf

ltFleT : (k, j : Nat) -> k < j = False -> j <= k = True
ltFleT 0 0 prf = Refl
ltFleT 0 (S _) Refl impossible
ltFleT (S k) 0 Refl = Refl
ltFleT (S k) (S j) prf = let ih = ltFleT k j prf in ih

bT_bFV : (b : Bool) -> b = True -> b = False -> Void
bT_bFV True Refl Refl impossible

bFV_bT : (b : Bool) -> (b = False -> Void) -> b = True
bFV_bT False f = let v = f Refl in void v
bFV_bT True f = Refl


kLEj_kLEFV : (k, j : Nat) -> k < j = True -> k < j = False -> Void
kLEj_kLEFV k j = bT_bFV (k < j)

kLTj_jLEkV : (k, j : Nat) -> k < j = True -> j <= k = True -> Void
kLTj_jLEkV k j prf prf1 = let t = kLTj_jLEkF k j prf in let t' = bT_bFV (j <= k) prf1 t in t'

kLTj_kLEj : (k, j : Nat) -> k < j = True -> k <= j = True
kLTj_kLEj 0 0 Refl impossible
kLTj_kLEj 0 (S k) Refl = Refl
kLTj_kLEj (S _) 0 Refl impossible
kLTj_kLEj (S k) (S j) prf = let ih = kLTj_kLEj k j prf in ih

kLTj_jGEk : (k, j : Nat) -> k < j = True -> j >= k = True
kLTj_jGEk 0 0 prf = Refl
kLTj_jGEk 0 (S k) prf = Refl
kLTj_jGEk (S k) 0 prf = prf
kLTj_jGEk (S k) (S j) prf = kLTj_jGEk k j prf

leTleTeq : (k, j : Nat) -> k <= j = True -> j <= k = True -> k = j
leTleTeq 0 0 prf prf1 = Refl
leTleTeq 0 (S _) Refl Refl impossible
leTleTeq (S _) 0 Refl _ impossible
leTleTeq (S k) (S j) prf prf1 = let ih = leTleTeq k j prf prf1 in rewrite ih in Refl

ltFltFeq : (k, j : Nat) -> k < j = False -> j < k = False -> k = j
ltFltFeq 0 0 Refl Refl = Refl
ltFltFeq 0 (S _) Refl _ impossible
ltFltFeq (S _) 0 _ Refl impossible
ltFltFeq (S k) (S j) prf prf1 = let ih = ltFltFeq k j prf prf1 in rewrite ih in Refl


minusjj : (j : Nat) -> minus j j = 0
minusjj 0 = Refl
minusjj (S k) = minusjj k

minusj0 : (j : Nat) -> minus j 0 = j
minusj0 0 = Refl
minusj0 (S k) = Refl

kEQj_kjRefl : (k, j : Nat) -> k == j = True -> k = j
kEQj_kjRefl 0 0 prf = Refl
kEQj_kjRefl 0 (S _) Refl impossible
kEQj_kjRefl (S _) 0 Refl impossible
kEQj_kjRefl (S k) (S j) prf = let ih = kEQj_kjRefl k j prf in rewrite ih in Refl

kEQkTrue : (k : Nat) -> k == k = True
kEQkTrue 0 = Refl
kEQkTrue (S k) = let ih = kEQkTrue k in ih

kjRefl_kjEq : (k, j : Nat) -> k = j -> k == j = True
kjRefl_kjEq k j prf =
    rewrite prf in
    let t = kEQkTrue j in
    t

-- msji_smji : (j, i : Nat) -> minus (S j) i = S (minus j i)

siLTj_iLTj : (i, j : Nat) -> (S i) < j = True -> i < j = True
siLTj_iLTj 0 0 Refl impossible
siLTj_iLTj 0 (S k) prf = Refl
siLTj_iLTj (S k) 0 prf = prf
siLTj_iLTj (S k) (S j) prf = 
  let ih = siLTj_iLTj k j prf in
  ih

kPiLTj_iLTj : (k, j, i : Nat) -> plus k i < j = True -> i < j = True
kPiLTj_iLTj 0 j i prf = prf
kPiLTj_iLTj (S _) 0 _ Refl impossible
kPiLTj_iLTj (S k) (S j) 0 prf = Refl
kPiLTj_iLTj (S k) (S j) (S i) prf =
  let t = plusSuccRightSucc k i in
  let ih = kPiLTj_iLTj k j (S i) prf in
  let u = siLTj_iLTj i j ih in
  u 

kPiEqj_kEqMji : (k, j, i : Nat) -> plus k i = j -> k = minus j i
kPiEqj_kEqMji 0 0 i prf = Refl
kPiEqj_kEqMji (S _) 0 _ Refl impossible
kPiEqj_kEqMji 0 (S j) i prf = rewrite sym $ prf in rewrite minusjj i in Refl
kPiEqj_kEqMji (S k) (S j) i prf =
    -- rewrite sym prf in
    ?hole_3

kPiEQj_kEQjMi : (k, j, i : Nat) -> plus k i == j = True -> k == minus j i = True
kPiEQj_kEQjMi k j i prf = 
    let t = kEQj_kjRefl (plus k i) j prf in
    ?kPiEQj_kEQjMi_rhs

pppm2 : (k, j, i1, i2 : Nat) -> plus k (plus i1 i2)  < j = True -> plus k i1 < minus j i2= True
pppm2 0 0 0 i2 prf = let contra = lt0contra i2 in void (contra prf)
pppm2 0 0 (S k) i2 prf = prf
pppm2 0 (S k) i1 i2 prf = ?pppm2_rhs_3
pppm2 (S k) j i1 i2 prf = ?pppm2_rhs_1

pppm : (k, j, i1, i2 : Nat) -> plus (plus k i1) i2  < j = True -> plus k i1 < minus j i2= True
pppm 0 0 i1 i2 prf =
    let contra = lt0contra (plus i1 i2) in
    let t = contra prf in
    void (contra prf)
pppm 0 (S k) i1 i2 prf = ?pppm_rhs_3
pppm (S k) j i1 i2 prf = ?pppm_rhs_1

minusji0 : (j, i : Nat) -> i < j = True -> 0 < minus j i = True
minusji0 0 i prf = 
    let t = lt0contra i in
    let u = t prf in
    void u
minusji0 (S k) 0 prf = prf
minusji0 (S k) (S j) prf = minusji0 k j prf

ltS : (i, j : Nat) -> i < j = True -> i < (S j) = True
ltS 0 j prf = Refl
ltS (S k) 0 prf = absurd prf
ltS (S k) (S j) prf =
    let ih = ltS k j prf in
    ih

leS : (i, j : Nat) -> i <= j = True -> i <= (S j) = True
leS 0 j prf = Refl
leS (S k) 0 prf = absurd prf
leS (S k) (S j) prf =
    let ih = leS k j prf in
    ih

mikLTmjk1 : (k, j, i : Nat) -> i < j = True -> k < i = True -> minus i k < minus j k = True
mikLTmjk1 0 j i prf prf1 = 
    let mi = minusj0 i in 
    rewrite mi in
    let mj = minusj0 j in
    rewrite mj in
    prf
mikLTmjk1 (S k) 0 i prf prf1 = 
    let contra = lt0contra i in
    void (contra prf)
mikLTmjk1 (S _) (S _) 0 _ Refl impossible
mikLTmjk1 (S k) (S j) (S i) prf prf1 = mikLTmjk1 k j i prf prf1

mikLTmjk2 : (k, j, i : Nat) -> i < j = True -> k <= i = True -> minus i k < minus j k = True
mikLTmjk2 0 j i prf prf1 = 
     let mi = minusj0 i in 
     rewrite mi in
     let mj = minusj0 j in
     rewrite mj in
     prf
mikLTmjk2 (S k) 0 i prf prf1 = 
     let contra = lt0contra i in
     void (contra prf)
mikLTmjk2 (S _) (S _) 0 _ Refl impossible
mikLTmjk2 (S k) (S j) (S i) prf prf1 =
     mikLTmjk2 k j i prf prf1

mpkiaLEmja : (k, j, i, i' : Nat) -> plus k i < j = True -> i' < i = True -> minus (plus k i) i' < minus j i' = True
mpkiaLEmja k j i 0 prf prf1 =
    let ki0 = minusj0 (plus k i) in
    rewrite ki0 in
    let j0 = minusj0 j in
    rewrite j0 in
    prf
mpkiaLEmja _ _ 0 (S _) _ Refl impossible
mpkiaLEmja 0 0 (S i) (S k1) prf prf1 = absurd prf
mpkiaLEmja 0 (S k) (S i) (S k1) prf prf1 = 
    let t = mikLTmjk1 k1 k i prf prf1 in
    t
mpkiaLEmja (S _) 0 (S _) (S _) Refl _ impossible
mpkiaLEmja (S k) (S j) (S i) (S k1) prf prf1 =
    let t = ltS k1 i prf1 in
    let ih = mpkiaLEmja k j (S i) k1 prf t in
    ih

mpkiaLTmja : (k, j, i, i' : Nat) -> plus k i < j = True -> i' <= i = True -> minus (plus k i) i' < minus j i' = True
mpkiaLTmja k j i 0 prf prf1 = 
    let ki0 = minusj0 (plus k i) in
    rewrite ki0 in
    let j0 = minusj0 j in
    rewrite j0 in
    prf
mpkiaLTmja _ _ 0 (S _) _ Refl impossible
mpkiaLTmja 0 0 (S i) (S k1) prf prf1 = absurd prf
mpkiaLTmja 0 (S k) (S i) (S k1) prf prf1 = mikLTmjk2 k1 k i prf prf1 
mpkiaLTmja (S k) 0 (S i) (S k1) prf prf1 = absurd prf
mpkiaLTmja (S k) (S j) (S i) (S k1) prf prf1 =
    let t = leS k1 i prf1 in
    let ih = mpkiaLTmja k j (S i) k1 prf t in
    ih 

ge0 : (i : Nat) -> 0 <= i = True
ge0 0 = Refl
ge0 (S k) = Refl

gei : (i : Nat) -> i <= i = True
gei 0 = Refl
gei (S k) = gei k

minusSuccLT : (a, b : Nat) -> b < a = True -> minus (S a) b = S (minus a b)
minusSuccLT 0 b prf =
    let contra = lt0contra b prf in
    void contra
minusSuccLT (S k) 0 prf = Refl
minusSuccLT (S k) (S j) prf = 
    let ih = minusSuccLT k j prf in
    ih

minusSuccLE : (a, b : Nat) -> b <= a = True -> minus (S a) b = S (minus a b)
minusSuccLE 0 b prf =
    let t = leTleTeq 0 b (ge0 b) prf in
    rewrite sym t in
    Refl
minusSuccLE (S k) 0 prf = Refl
minusSuccLE (S k) (S j) prf =
    let ih = minusSuccLE k j prf in
    ih

pluskjj : (k, j : Nat) -> j <= plus k j = True
pluskjj 0 j = rewrite (gei j) in Refl
pluskjj (S k) j =
    let t = plusSuccRightSucc k j in
    let u = leS j (plus k j) in
    let ih = pluskjj k j in
    u ih

mpkiikRefl : (k, i : Nat) -> minus (plus k i) i = k
mpkiikRefl 0 i = minusjj i
mpkiikRefl (S k) 0 = let t = plusZeroRightNeutral k in rewrite t in Refl
mpkiikRefl (S k) (S j) =
    let ih = mpkiikRefl k j in
    let t = plusSuccRightSucc k j in
    rewrite sym t in
    let u = plusCommutative k j in
    let v = minusSuccLE (plus k j) j in
    let w = pluskjj k j in
    let s = v w in
    rewrite s in
    rewrite ih in
    Refl

kLTmji : (k, j, i : Nat) -> plus k i < j = True -> k < minus j i = True
kLTmji k j i prf =
    let t = mpkiaLTmja k j i i prf (gei i) in
    let u = mpkiikRefl k i in
    rewrite sym t in
    rewrite u in
    Refl

minusjiP : (j, i : Nat) -> i < j = True -> 0 < minus j i = True
minusjiP 0 0 prf = prf
minusjiP 0 (S k) prf = prf
minusjiP (S k) 0 prf = prf
minusjiP (S k) (S j) prf = minusjiP k j prf

arith01 : (i, j, k : Nat) -> i+k < j = True -> minus j (plus i k) = minus (minus j i) k
arith01 i j 0 prf = 
    rewrite plusZeroRightNeutral i in
    rewrite minusZeroRight (minus j i) in
    Refl {x = minus j i}
arith01 i j (S k) prf = -- minus j (plus i (S k)) = minus (minus j i) (S k)
    let t = minusMinusMinusPlus j i (S k) in
    rewrite t in
    Refl {x = minus j (plus i (S k))}

kij_ikj : (i, j, k : Nat) -> k+i < j = True -> i+k < j = True
kij_ikj i j k prf = rewrite plusCommutative i k in prf

arith01' : (i, j, k : Nat) -> k+i < j = True -> minus j (plus i k) = minus (minus j i) k
arith01' i j k prf = let rw = kij_ikj i j k prf in let t = arith01 i j k rw in t

arith02 : (j, i : Nat) -> i < j = True -> 0 < minus j i = True
arith02 0 0 prf = prf
arith02 0 (S k) prf = prf
arith02 (S k) 0 prf = prf
arith02 (S k) (S j) prf = let ih = arith02 k j prf in ih

arith02e : (j, i : Nat) -> i <= j = True -> 0 <= minus j i = True
arith02e 0 0 prf = Refl
arith02e 0 (S k) prf = Refl
arith02e (S k) 0 prf = Refl
arith02e (S k) (S j) prf = let ih = arith02e k j prf in rewrite ih in Refl

arith03 : (i : Nat) -> 0 < i = True -> normalizeMI (MI Neg i) = MI Neg i
arith03 0 Refl impossible
arith03 (S k) prf = Refl {x = MI Neg (S k)}

funny : (i : Nat) -> Z = S i
funny 0 = ?hole
funny (S k) = let ih = funny k in rewrite ih in absurd ih 

funnyeq : 0 = 1
funnyeq = ?funnyeq_rhs

funnyeq2 : 0 = 1 -> Void
funnyeq2 Refl impossible

arith03epre : MI Pos 0 = MI Neg 0 -> Void
arith03epre Refl impossible

-- arith03e : (i : Nat) -> 0 <= i = True -> normalizeMI (MI Neg i) = MI Neg i
-- arith03e 0 prf = void ?holeas
-- arith03e (S k) prf = ?arith03e_rhs_1

arith04 : (j, i : Nat) -> i < j = True -> MI Neg (minus j i) = plusMI (MI Neg j) (MI Pos i)
arith04 j 0 prf =
    let t = kLTj_jGEk 0 j prf in
    rewrite t in
    rewrite minusj0 j in
    rewrite arith03 j prf in
    Refl {x = MI Neg j}
arith04 j (S k) prf =
    let t = kLTj_jGEk (S k) j prf in
    rewrite t in
    let t' = minusjiP j (S k) prf in
    let t'' = arith03 (minus j (S k)) t' in 
    rewrite t'' in
    Refl {x = MI Neg (minus j (S k))}

arith05 : (k, i, j : Nat) -> k < plus i j = True -> k < i = True -> minus (plus i j) k = plus (minus i k) j
arith05 0 0 j prf prf1 = rewrite minusj0 j in Refl
arith05 0 (S k) j prf prf1 = Refl
arith05 (S k) 0 j prf prf1 = absurd prf1
arith05 (S k) (S i) j prf prf1 = let ih = arith05 k i j prf prf1 in ih

plusMICommutative : (mi, mj : MyInteger) -> plusMI mi mj = plusMI mj mi
plusMICommutative (MI Pos 0) (MI Neg 0) = Refl {x = MI Pos 0}
plusMICommutative (MI Pos (S k)) (MI Neg 0) = Refl {x = MI Pos (S k)}
plusMICommutative (MI Pos k) (MI Pos j) = rewrite plusCommutative k j in Refl {x = MI Pos (plus j k)}
plusMICommutative (MI Pos 0) (MI Neg (S j)) = Refl {x = MI Neg (S j)}
plusMICommutative (MI Pos (S k)) (MI Neg (S j)) = 
    case ltORltF k j of -- k < j or k >= j
      (Left prf) => -- k < j
        case ltORltF j k of -- j < k or k >= j
            (Left prf1) => -- j < k
                let t = kLTj_kLEj j k prf1 in let t' = kLTj_jLEkV k j prf t in void t'
            (Right prf1) => -- k >= j
                rewrite prf1 in rewrite prf in Refl
      (Right prf) => -- k >= j
        case ltORltF j k of -- j < k or j >= k
            (Left prf1) => -- j < k
                rewrite prf1 in rewrite prf in Refl
            (Right prf1) => -- j >= k
                rewrite prf in 
                rewrite prf1 in
                let a = ltFleT k j prf in 
                let b = ltFleT j k prf1 in
                let t = leTleTeq k j b a in
                rewrite t in
                -- let u = minusjj j in
                let u = minusZeroN j in
                rewrite sym u in
                Refl
plusMICommutative (MI Neg 0) (MI Pos 0) = Refl {x = MI Pos 0}
plusMICommutative (MI Neg 0) (MI Pos (S k)) = Refl {x = MI Pos (S k)}
plusMICommutative (MI Neg (S k)) (MI Pos 0) = Refl {x = MI Neg (S k)}
plusMICommutative (MI Neg (S k)) (MI Pos (S j)) =
    case ltORltF k j of
        (Left kLTj) => 
            case ltORltF j k of
                (Left jLTk) =>
                    let t = kLTj_kLEj k j kLTj in
                    let t' = kLTj_jLEkV j k jLTk t in void t'
                (Right jGEk) =>
                    rewrite kLTj in
                    rewrite jGEk in
                    Refl
        (Right kGEj) =>
            case ltORltF j k of
                (Left jLTk) =>
                    rewrite kGEj in
                    rewrite jLTk in
                    Refl
                (Right jGEk) =>
                    let a = ltFleT k j kGEj in
                    let b = ltFleT j k jGEk in
                    let t = leTleTeq j k a b in
                    rewrite kGEj in
                    rewrite jGEk in
                    rewrite t in
                    -- rewrite minusjj k in
                    rewrite sym $ minusZeroN k in
                    Refl
plusMICommutative (MI Neg k) (MI Neg j) = 
    rewrite plusCommutative k j in
    Refl {x = normalizeMI (MI Neg (plus j k))}

plusMIAssociative : (x, y, z : MyInteger) -> plusMI x (plusMI y z) = plusMI (plusMI x y) z
plusMIAssociative (MI Pos k) (MI Pos i) (MI Pos j) =
    let t = plusAssociative k i j in rewrite t in Refl
plusMIAssociative (MI Pos k) (MI Pos i) (MI Neg j) = -- goal : k + (i + -j) = (k + i) + -j
    case ltORltF i j of
        (Left iLTj) => rewrite iLTj in -- i < j
            case ltORltF (plus k i) j of
                (Left kiLTj) => -- k + i < j
                    case ltORltF j (plus k i) of
                        (Left jLTki) => -- j < k + i
                            let s = kLTj_kLEj j (plus k i) jLTki in
                            let p = kLTj_jLEkV (plus k i) j kiLTj s in
                            void p
                        (Right jLTkiF) => -- !(j < k + i)
                            rewrite kiLTj in
                            let ta01' = arith01' i j k kiLTj in
                            let mji = arith02 j i iLTj in
                            let mji' = arith03 (minus j i) mji in -- normalizeMI (MI Neg (minus j i)) = MI Neg (minus j i)
                            let kijPos = arith02 j (plus k i) kiLTj in
                            let kijPos' = arith03 (minus j (plus k i)) kijPos in
                            rewrite kijPos' in
                            rewrite plusCommutative k i in
                            rewrite ta01' in
                                -- goal : plusMI (MI Pos k) (normalizeMI (MI Neg (minus j i))) = MI Neg (minus (minus j i) k)
                            let t'pre = kLTmji k j i kiLTj in
                            let t' = arith04 (minus j i) k t'pre in -- MI Neg (minus (minus j i) k) = plusMI (MI Neg (minus j i)) (MI Pos k)
                            let pMIcomm = plusMICommutative (MI Neg (minus j i)) (MI Pos k) in
                                -- pMIcomm : plusMI (MI Neg (minus j i)) (MI Pos k) = plusMI (MI Pos k) (MI Neg (minus j i))
                            rewrite mji' in
                                --- goal : plusMI (MI Pos k) MI Neg (minus j i) = MI Neg (minus (minus j i) k)
                            rewrite t' in
                                --- goal : plusMI (MI Pos k) MI Neg (minus j i) = plusMI (MI Neg (minus j i)) (MI Pos k)
                            rewrite pMIcomm in
                                --- goal : plusMI (MI Pos k) MI Neg (minus j i) = plusMI (MI Pos k) (MI Neg (minus j i))
                            rewrite t'pre in
                                Refl
                (Right kiGEj) => -- k + i >= j
                    ?plusMIAssociative_rhs_9
        (Right iGEj) => -- !(i < j)
            rewrite iGEj in
            case ltORltF (plus k i) j of
                (Left kiLTj) => 
                    rewrite kiLTj in -- goal: MI Pos (plus k (minus i j)) = normalizeMI (MI Neg (minus j (plus k i)))
                    -- 0 < k + i < j
                    let rw = arith03 in
                    ?plusMIAssociative_rhs_11
                (Right klLTjF) => ?plusMIAssociative_rhs_15
plusMIAssociative (MI Pos k) (MI Neg i) (MI Pos j) = -- goal : k + (-i + j) = (k + -i) + j
    ?plusMIAssociative_rhs_7
plusMIAssociative (MI Pos k) (MI Neg i) (MI Neg j) = -- goal : k + (-i + -j) = (k + -i) + -j
     ?plusMIAssociative_rhs_8
plusMIAssociative (MI Neg k) (MI Pos i) (MI Pos j) = -- goal : -k + (i + j) = (-k + i) + j
    let step1 = plusMICommutative (MI Neg k) (plusMI (MI Pos i) (MI Pos j)) in -- comm : -k + (i + j) = (i + j) + -k
    let step2 = plusMICommutative (MI Pos i) (MI Pos j) in -- comm : (i + j) + -k = (j + i) + -k
    -- let step3 = plusMIAssociative (MI Pos j) (MI Pos i) (MI Neg k) in -- known : (j + i) + -k = j + (i + -k)
    let step4 = plusMICommutative (MI Pos j) (plusMI (MI Pos i) (MI Neg k)) in -- comm : j + (i + -k) = (i + -k) + j
    let step5 = plusMICommutative (plusMI (MI Pos i) (MI Neg k)) (MI Pos j) in -- comm : (i + -k) + j = (-k + i) + j
    case ltORltF k (plus i j) of
      (Left kLTij) => rewrite kLTij in
        case ltORltF k i of
            (Left kLTi) =>
                rewrite kLTi in -- goal: MI Pos (minus (plus i j) k) = MI Pos (plus (minus i k) j)
                let rw = arith05 k i j kLTij kLTi in
                rewrite rw in
                Refl
            (Right kLTiF) =>
                rewrite kLTiF in -- goal: MI Pos (minus (plus i j) k) = plusMI (normalizeMI (MI Neg (minus k i))) (MI Pos j)
                let mki = arith02e k i (ltFleT k i kLTiF) in
                let mki' = arith03 (minus k i) in 
                case decEq k i of
                    (Yes kEi) => rewrite kEi in
                        rewrite minusjj i in
                        rewrite plusCommutative i j in
                        let jii = mpkiikRefl j i in
                        rewrite jii in
                        Refl
                    (No contra) =>
                        -- goal : MI Pos (minus (plus i j) k) = plusMI (normalizeMI (MI Neg (minus k i))) (MI Pos j)
                        ?holel_5 
      (Right kLTijF) => ?hole_1
plusMIAssociative (MI Neg k) (MI Pos i) (MI Neg j) = -- goal : -k + (i + -j) = (-k + i) + -j
     ?plusMIAssociative_rhs_12
plusMIAssociative (MI Neg k) (MI Neg i) (MI Pos j) = -- goal : -k + (-i + j) = (-k + -i) + j
     ?plusMIAssociative_rhs_13
plusMIAssociative (MI Neg k) (MI Neg i) (MI Neg j) = -- goal : -k + (-i + -j) = (-k + -i) + -j
    ?plusMIAssociative_rhs_14
