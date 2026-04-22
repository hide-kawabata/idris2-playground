import Data.Nat
import Data.Vect
import Data.Vect.Elem

%default total

-----------------------------------------------------------------------------------

-- recursively defined combination function (n C k = n! / (k! x (n-k)!)
nC : Nat -> Nat -> Nat
nC 0 0 = 1
nC 0 (S r) = 0
nC (S n) 0 = 1
nC (S n) (S r) = nC n r `plus` nC n (S r)

-- compute [x:xs | xs <- ll]
-- prepend 5 [[1,2],[3,4]] ---> [[5, 1, 2], [5, 3, 4]]
-- prepend 5 [] ---> []
prepend : {a : Type} -> {n, m : Nat} -> a -> 
    Vect n (Vect m a) -> Vect n (Vect (S m) a)
prepend x [] = []
prepend x (y :: xs) = [x :: y] ++ prepend x xs

-- obtain all list of combinations from a given list
-- combi 3 [1,2,3,4] ---> [[1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]]
combi : {len : Nat} -> {a : Type} ->
    (n : Nat) -> (l : Vect len a) -> Vect (nC len n) (Vect n a)
combi 0 [] = [[]]
combi 0 (x :: xs) = [[]]
combi (S k) [] = []
combi (S k) (x :: xs) = prepend x (combi k xs) ++ combi (S k) xs

-----------------------------------------------------------------------------------

-- SubVect : a sequence (or a vector) is a subsequence if all elements in the
-- sequence appear in a larger sequence in an order-preserving way:
-- e.g. SubVect [1,3] [0,1,2,3,4] is valid but SubVect [1,3] [0,3,2,1,4] is not.
data SubVect : Vect len1 a -> Vect len2 a -> Type where
    SVNil : SubVect [] xs
    SVTake : SubVect xs ys -> SubVect (x :: xs) (x :: ys)
    SVSkip : SubVect xs ys -> SubVect xs (y :: ys)

Uninhabited (SubVect (x::xs) [])

test_SubVect1 : SubVect [1,2,3] [1,2,3]
test_SubVect1 = SVTake (SVTake (SVTake SVNil))
test_SubVect2 : SubVect [1,2,3] ([]++[1,2,3])
test_SubVect2 = SVTake (SVTake (SVTake SVNil))
test_SubVect3 : SubVect [1,2,3] [0,1,2,3]
test_SubVect3 = SVSkip (SVTake (SVTake (SVTake SVNil)))
test_SubVect4 : SubVect [1,3] [0,1,2,3]
test_SubVect4 = SVSkip (SVTake (SVSkip (SVTake SVNil)))
test_SubVect5 : SubVect [] [1]
test_SubVect5 = SVNil
test_SubVect6 : SubVect [] [1,2]
test_SubVect6 = SVNil
test_SubVect6' : SubVect [] [1,2]
test_SubVect6' = SVNil

----------------------------------------------------------------------------------

-- completeness proof of combi
mutual
    -- induction on n and len (length of l)
    combiComplete : {a : Type} -> (n : Nat) -> {len : Nat} ->
        (l : Vect len a) -> (v : Vect n a) -> SubVect v l -> Elem v (combi n l)
    combiComplete 0 [] [] SVNil = Here
    combiComplete 0 (y :: xs) [] _ = Here
    combiComplete (S _) [] (_ :: _) _ impossible
    combiComplete (S k) (y :: xs) (y :: ys) (SVTake x) =
        -- goal : Elem (y :: ys) (prepend y (combi k xs) ++ combi (S k) xs)
        let ih = combiComplete k xs ys x in
        let pe = prependElem y (combi k xs) ys ih in
        elemAppendLeft (prepend y (combi k xs)) (combi (S k) xs) pe
    combiComplete (S k) (y :: xs) (z :: ys) (SVSkip x) =
        -- goal : Elem (z :: ys) (prepend y (combi k xs) ++ combi (S k) xs)
        let ih = combiComplete (S k) xs (z :: ys) x in
        elemAppendRight (prepend y (combi k xs)) (combi (S k) xs) ih

    prependElem : {a : Type} -> (x : a) -> {n, m : Nat} -> (ys : Vect n (Vect m a)) ->
        (v : Vect m a) -> (prf : Elem v ys) -> Elem (x :: v) (prepend x ys)
    prependElem x (_ :: _) v Here = Here
    prependElem x (_ :: _) v (There later) = There (prependElem x _ v later)

    elemAppendLeft : {a : Type} -> {n1, n2, m : Nat} ->
        (l1 : Vect n1 (Vect m a)) -> (l2 : Vect n2 (Vect m a)) -> {v : Vect m a} ->
        (prf : Elem v l1) -> Elem v (l1 ++ l2)
    elemAppendLeft (_ :: _) l2 Here = Here
    elemAppendLeft (_ :: _) l2 (There later) = There (elemAppendLeft _ l2 later)

    elemAppendRight : {a : Type} -> {n1, n2, m : Nat} ->
        (l1 : Vect n1 (Vect m a)) -> (l2 : Vect n2 (Vect m a)) -> {v : Vect m a} ->
        (prf : Elem v l2) -> Elem v (l1 ++ l2)
    elemAppendRight [] l2 prf = prf
    elemAppendRight (x :: xs) l2 prf = There (elemAppendRight xs l2 prf)

----------------------------------------------------------------------------------

-- properties which I thought might be useful but not used
prop_SubVect_nil : {a : Type} -> {n : Nat} -> (l : Vect n a) -> SubVect [] l
prop_SubVect_nil l = SVNil

prop_SubVect_hd :  {a : Type} -> (h : a) -> {n1, n2 : Nat} ->
    (l1 : Vect n1 a) -> (l2 : Vect n2 a) ->
    (prf : SubVect (h :: l1) (h :: l2)) -> SubVect l1 l2
prop_SubVect_hd h [] [] (SVTake SVNil) = SVNil
prop_SubVect_hd _ [] [] (SVSkip _) impossible
prop_SubVect_hd h [] (x :: xs) (SVTake y) = y
prop_SubVect_hd h [] (x :: xs) (SVSkip y) = SVNil
prop_SubVect_hd h (x :: xs) [] (SVTake y) = y
prop_SubVect_hd _ (_ :: _) [] (SVSkip _) impossible
prop_SubVect_hd h (x :: xs) (y :: ys) (SVTake z) = z
prop_SubVect_hd h (x :: xs) (h :: ys) (SVSkip (SVTake z)) = SVSkip z
prop_SubVect_hd h (x :: xs) (y :: ys) (SVSkip (SVSkip z)) =
    SVSkip (prop_SubVect_hd h (x :: xs) ys (SVSkip z))

prop_SubVect_len : {a : Type} -> {n1, n2 : Nat} ->
    (l1 : Vect n1 a) -> (l2 : Vect n2 a) -> (prf : SubVect l1 l2) -> LTE n1 n2
prop_SubVect_len [] [] SVNil = LTEZero
prop_SubVect_len [] (x :: xs) prf = LTEZero
prop_SubVect_len (_ :: _) [] _ impossible
prop_SubVect_len (x :: xs) (x :: ys) (SVTake z) =
    let ih = prop_SubVect_len xs ys z in LTESucc ih
prop_SubVect_len (x :: xs) (y :: ys) (SVSkip z) =
    let t = SVSkip z {y=x} in
    let t' = prop_SubVect_hd x xs ys t in  
    let ih = prop_SubVect_len (x :: xs) ys z in
    LTESucc (prop_SubVect_len xs ys t')

prop_SubVect_shorten1 : {a : Type} -> {e : a} -> {n1, n2 : Nat} ->
    (l1 : Vect n1 a) -> (l2 : Vect n2 a) ->
    (prf : SubVect (e::l1) l2) -> SubVect l1 l2
prop_SubVect_shorten1 [] l2 prf = SVNil
prop_SubVect_shorten1 (x :: xs) (_ :: _) (SVTake y) = SVSkip y
prop_SubVect_shorten1 (x :: xs) (_ :: _) (SVSkip y) =
    SVSkip (prop_SubVect_shorten1 (x :: xs) _ y)

-- probably not provable in a constructive logic
-- concatElem : {a : Type} -> {n1, n2 : Nat} -> (l1 : Vect n1 a) -> (l2 : Vect n2 a) ->
--     {v : a} -> (prf : Elem v (l1 ++ l2)) -> Either (Elem v l1) (Elem v l2)

----------------------------------------------------------------------------------

-- C's property : k < j ==> k C j = 0
prop_nC_kLTj : (k : Nat) -> (j : Nat) -> LT k j -> nC k j = 0
prop_nC_kLTj Z Z _ impossible
prop_nC_kLTj 0 (S k) (LTESucc x) = Refl
prop_nC_kLTj (S k) (S j) (LTESucc x) = 
    rewrite (prop_nC_kLTj k j x) in
    prop_nC_kLTj k (S j) (LTESucc (prop_LTE_S k j x))
    where
        prop_LTE_S : (n, m : Nat) -> LTE (S n) m -> LTE n m
        prop_LTE_S 0 m x = LTEZero
        prop_LTE_S (S k) (S _) (LTESucc x) = LTESucc (prop_LTE_S k _ x)

-- a property of combi : length l < n ==> combi n l = []
-- note: prop_nC_kLTj is used in the sigunature
prop_combi : {a : Type} -> (len : Nat) -> (n : Nat) -> (l : Vect len a) ->
    (prf : LT len n) ->
    combi n l = (let t = prop_nC_kLTj len n prf in rewrite t in [])
prop_combi Z Z [] _ impossible
prop_combi 0 (S k) [] prf = Refl
prop_combi (S _) Z (_ :: _) _ impossible
prop_combi (S k) (S j) (x :: xs) (LTESucc y) = 
    rewrite prop_combi k j xs y in -- IH 1
    rewrite prop_nC_kLTj k j y in -- nC k j = 0
    let rw2 = prop_nC_kLTj k (S j) (let t = prop_LTE_mn_nSn (S k) j y in t) in
    rewrite rw2 in -- nC k (S j) = 0
    let t = prop_combi k (S j) xs (let t = prop_LTE_mn_nSn (S k) j y in t) in
    rewrite t in -- IH 2
    Refl
       where
        prop_LTE_mn_nSn : (m, n : Nat) -> LTE m n -> LTE m (S n)
        prop_LTE_mn_nSn 0 n x = LTEZero
        prop_LTE_mn_nSn (S k) (S _) (LTESucc x) = LTESucc (prop_LTE_mn_nSn k _ x)

----------------------------------------------------------------------------------

-- This definition is logically fine, but not suitable for induction
data SubVect0 : {a : Type} -> {n1, n2 : Nat} ->
    (l1 : Vect n1 a) -> (l2 : Vect n2 a) -> Type where
    SVRefl : {a : Type} -> {n1 : Nat} -> (l1 : Vect n1 a) -> SubVect0 l1 l1
    SVIns : {a : Type} -> {n1, n21, n22 : Nat} ->
            (l1 : Vect n1 a) -> (l21 : Vect n21 a) -> (l22 : Vect n22 a) ->
            (prf : SubVect0 l1 (l21 ++ l22)) ->
            (x : a) -> 
            SubVect0 l1 (l21 ++ [x] ++ l22)

Uninhabited (SubVect0 (x::xs) [])

test_SubVect01 : SubVect0 [1,2,3] [1,2,3]
test_SubVect01 = SVRefl [1, 2, 3]
test_SubVect02 : SubVect0 [1,2,3] ([]++[1,2,3])
test_SubVect02 = SVRefl [1, 2, 3]
test_SubVect03 : SubVect0 [1,2,3] [0,1,2,3]
test_SubVect03 = SVIns [1,2,3] [] [1,2,3] (SVRefl [1,2,3]) 0
test_SubVect04 : SubVect0 [1,3] [0,1,2,3]
test_SubVect04 = SVIns [1,3] [] [1,2,3] prf2 0
    where
        prf1 : SubVect0 [1,3] [1,3]
        prf1 = SVRefl [1,3]
        prf2 : SubVect0 [1,3] [1,2,3]
        prf2 = SVIns [1,3] [1] [3] prf1 2
test_SubVect05 : SubVect0 [] [1]
test_SubVect05 = SVIns [] [] [] (SVRefl []) 1
test_SubVect06 : SubVect0 [] [1,2]
test_SubVect06 = SVIns [] [1] [] (SVIns [] [] [] (SVRefl []) 1) 2
test_SubVect06' : SubVect0 [] [1,2]
test_SubVect06' = SVIns [] [] [2] (SVIns [] [] [] (SVRefl []) 2) 1


-----------------------------------------------------------------------------------
