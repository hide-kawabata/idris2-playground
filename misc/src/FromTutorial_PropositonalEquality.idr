import Data.Vect

mapListLength : (f : a -> b) -> (as : List a) -> length as = length (map f as)
mapListLength f [] = Refl
mapListLength f (x :: xs) = case mapListLength f xs of
                                prf => rewrite prf in Refl

mapListLength2 : (f : a -> b) -> (as : List a) -> length as = length (map f as)
mapListLength2 f [] = Refl
mapListLength2 f (x :: xs) = case mapListLength2 f xs of
                                prf => cong S prf

mapListLength3 : (f : a -> b) -> (as : List a) -> length as = length (map f as)
mapListLength3 f [] = Refl
mapListLength3 f (x :: xs) = cong S $ mapListLength3 f xs



-- be careful to use lowercase letters 
mapMaybeId1 : (ma : Maybe a) -> map id ma = ma
mapMaybeId1 Nothing  = Refl
mapMaybeId1 (Just x) = ?mapMaybeId1_rhs

Id : a -> a
Id = id
mapMaybeId2 : (ma : Maybe a) -> map Id ma = ma
mapMaybeId2 Nothing  = Refl
mapMaybeId2 (Just x) = Refl

mapMaybeId : (ma : Maybe a) -> map Prelude.id ma = ma
mapMaybeId Nothing  = Refl
mapMaybeId (Just x) = Refl


-- expressing contradiction
onePlusOneWrongProvably : the Nat 1 + 1 = 3 -> Void
onePlusOneWrongProvably Refl impossible

-- using contradictory statements to prove
notSameLength1 : (List.length as = length bs -> Void) -> as = bs -> Void
notSameLength1 f prf = f (cong length prf)

-- using Not
notSameLength : Not (List.length as = length bs) -> Not (as = bs)
notSameLength f prf = f (cong length prf)

-- contraposition of cong
contraCong : {0 f : _} -> Not (f a = f b) -> Not (a = b)
contraCong fun x = fun $ cong f x

-- rewriting types ---------------------------------------------------------
addZeroRight : (n : Nat) -> n + 0 = n
addZeroRight 0     = Refl {x = 0} -- x is a term
addZeroRight (S k) = cong S $ addZeroRight k

-- replace for substituting one variable in a term by another, based on a proof of equality
-- note: this function `converts` the type of the argument
replaceVect : Vect (n + 0) a -> Vect n a
replaceVect as = replace {p = \k => Vect k a} (addZeroRight n) as

replaceVect' : {n : _} -> Vect (n + 0) a -> Vect n a
replaceVect' as = let prf = addZeroRight n in                  
                  let rewritten = replace {p = \k => Vect k a} prf as in rewritten
                    -- type of an argument is rewritten

rewriteVect : Vect (n + 0) a -> Vect n a
rewriteVect as = rewrite sym (addZeroRight n) in as -- the goal is rewritten

rewriteVect' : Vect (n + 0) a -> Vect n a
rewriteVect' as = let rw = sym (addZeroRight n) in
                  rewrite rw in as  -- the goal is rewritten

-- note: this function produces a value from arguments
revOnto : {m, n : _} -> Vect m a -> Vect n a -> Vect (m + n) a
revOnto xs [] = rewrite addZeroRight m in xs
revOnto {n = S len} xs (y :: ys) = 
    let prf = plusSuccRightSucc m len in
    rewrite sym prf in 
    revOnto (y :: xs) ys

-- separating proofs from the core computation
revOnto' : {m, n : _} -> Vect m a -> Vect n a -> Vect (m + n) a
revOnto' xs [] = prf_base $ xs -- returned value is xs
  where
    prf_base : {0 m : _} -> Vect m a -> Vect (plus m 0) a
    prf_base {m} xs = rewrite plusZeroRightNeutral m in xs
revOnto' {n = S len} xs (y :: ys) = prf_ind $ revOnto' (y :: xs) ys
  where
    prf_ind : {0 len : _} -> {0 m : _} -> Vect (S (m + len)) a -> Vect (m + S len) a
    prf_ind {len} {m} xs = rewrite sym $ plusSuccRightSucc m len in xs -- {len} {m} needed
    -- prf_ind {len} {m} xs = replace {p = \k => Vect k a} (plusSuccRightSucc m len) xs -- OK

-- proving equality of types
propVect : {n : _} -> Vect (n + 0) a = Vect n a -- equality of types
propVect = let prf = addZeroRight n in
           rewrite prf in Refl {x = Vect n a} -- x is a type

propVect' : {n : _} -> Vect (n + 0) a = Vect n a
propVect' = let prf = addZeroRight n in
            let rewritten = replace {p = \k => Vect k a} prf ?lhsval in ?hole00
                -- no values corresponding to the lhs and rhs of the goal

propEquiv : (a -> b) -> (b -> c) -> a -> c
propEquiv f g = \v => g (f v)

