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

spec_max' : {m : _} -> (a, b : Nat) -> max' a b = m -> 
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
prop_conjL : {ty1, ty2 : Type} -> Not ty1 -> Not (ty1, ty2)
prop_conjL f (x, y) = f x
prop_conjR : {ty1, ty2 : Type} -> Not ty2 -> Not (ty1, ty2)
prop_conjR f (x, y) = f y

prop_conj2 : {ty1, ty2 : Type} -> ty2 -> Not (ty1, ty2) -> ty1
prop_conj2 x f = 
    ?hohoho
    -- let p = (?hol, x) in
    -- let t = f p in
    -- void t

--  t : (mult b d = 0, r = 0) -> Void
--  prf : r = 0
prop_conj : {ty1, ty2 : Type} -> Not (ty1, ty2) -> (prf : Not ty2) -> ty1
prop_conj f prf = 
    -- let t = void $ f (?hoe2, void $ prf ?hoe) in
    -- prf : ty2 -> Void
    -- f : (ty1, ty2) -> Void
    -- let t = prop_conjR prf {ty1 = ty1} in
    ?hole

fact : Nat -> Nat
fact 0 = 1
fact (S k) = (S k) * fact k
div1 : Nat -> Nat -> Nat
div1 _ 0 = 0 -- special value, no error 
div1 0 _ = 0
div1 (S n) (S m) = ?hoho
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
      (Yes prf) => case decEq r' 0 of
        (Yes v) => (?part122_2, rewrite prf in rewrite v in Refl)
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
nC' (S n) (S x) = ((S n) * nC' n x) `div` (S x)
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