

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
