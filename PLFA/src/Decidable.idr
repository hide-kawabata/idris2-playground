%default total

-- Evidence vs Computation

data LTE : Nat -> Nat -> Type where
  LTE0 : {n : Nat} -> LTE 0 n
  LTEn : {m, n : Nat} -> LTE m n -> LTE (S m) (S n)

p2lte4 : LTE 2 4
p2lte4 = LTEn (LTEn LTE0)

-- inversion <-> destruction
pN4lte2 : Not (LTE 4 2)
pN4lte2 (LTEn (LTEn x)) impossible
--pN4lte2 x = case x of
--              pN4lte2 (LTEn (LTEn x)) impossible

-- _<=b_
blte : Nat -> Nat -> Bool
blte 0 j = True
blte (S k) 0 = False
blte (S k) (S j) = blte k j


-- Relating evidence and computation (computation world -> evidence world)
b2t : Bool -> Type
b2t True = ()
b2t False = Void

truthEq : (b : Bool) -> b2t b -> b = True
truthEq False x = absurd x
truthEq True () = Refl -- note that () : ()

eqTruth : {b : Bool} -> b = True -> b2t b
eqTruth Refl = () -- note that () : ()

-- _<=b_ -> _<=_
blte2LTE : (m, n : Nat) -> b2t (blte m n) -> LTE m n
blte2LTE 0 n x = LTE0
--blte2LTE (S k) 0 x impossible
blte2LTE (S k) 0 x = absurd x -- it is apparent that x is uninhabited
blte2LTE (S k) (S j) x = LTEn $ blte2LTE k j x

-- _<=_ -> _<=b_
lTE2blte : {m, n : Nat} -> LTE m n -> b2t (blte m n)
lTE2blte LTE0 = ()
lTE2blte (LTEn prf) = lTE2blte prf


-- The best of both worlds
data Deci : (a : Type) -> Type where
  YES : a -> Deci a
  NO : Not a -> Deci a

notLTE0 : {m : Nat} -> Not (LTE (S m) 0)
notLTE0 _ impossible

notLTEn : {m, n : Nat} -> Not (LTE m n) -> Not (LTE (S m) (S n))
notLTEn f (LTEn x) = f x

-- _<=?_ (compare with blte2LTE)
lteDeci: (m, n : Nat) -> Deci (LTE m n)
lteDeci 0 n = YES LTE0
lteDeci (S k) 0 = NO notLTE0
lteDeci (S k) (S j) = case lteDeci k j of
                        (YES x) => YES $ LTEn x
                        (NO f) => NO $ notLTEn f

pDeci2LTE4 : lteDeci 2 4 = YES (LTEn (LTEn LTE0))
pDeci2LTE4 = Refl

pDeci4LTE2 : lteDeci 4 2 = NO (notLTEn (notLTEn (notLTE0 {m = _})))
pDeci4LTE2 = Refl


-- Decidables from booleans, and booleans from decidables

-- erasure
erase : {a : Type} -> Deci a -> Bool
erase (YES x) = True
erase (NO f) = False

-- _blte'_
blte' : Nat -> Nat -> Bool
blte' m n = erase $ lteDeci m n

-- if d is a value of type Deci a, b2t (erase d) is inhabited
-- exactly when a is inhabited
toWitness : {a : Type} -> {d : Deci a} -> b2t (erase d) -> a
toWitness {a = a} {d = (YES y)} () = y
toWitness {a = a} {d = (NO f)} x = absurd x

fromWitness : {a : Type} -> {d : Deci a} -> a -> b2t (erase d)
fromWitness {a = a} {d = (YES y)} x = ()
fromWitness {a = a} {d = (NO f)} x = f x

-- b2t (blte' m n) is inhabited exactly when (LTE m n) is inhabited
dir1 : {m, n : Nat} -> b2t (blte' m n) -> LTE m n
dir1 x = toWitness x

dir2 : {m, n : Nat} -> LTE m n -> b2t (blte' m n)
dir2 x = fromWitness x
