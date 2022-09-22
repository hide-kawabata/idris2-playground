import Syntax.PreorderReasoning

%default total

-- Evidence vs Computation

data LTE : Nat -> Nat -> Type where
  LTE0 : {0 n : Nat} -> LTE 0 n
  LTEn : {0 m, n : Nat} -> LTE m n -> LTE (S m) (S n)

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

tmp1 : (blte 2 4) = True
tmp1 = Calc $ 
  |~ blte 2 4
  ~~ blte 1 3 ...( Refl )
  ~~ blte 0 2 ...( Refl )
  ~~ True ...( Refl )

tmp2 : (blte 4 2) = False
tmp2 = Calc $
  |~ blte 4 2
  ~~ blte 3 1 ... ( Refl )
  ~~ False ...( Refl )


-- Relating evidence and computation (computation world -> evidence world)

b2t : Bool -> Type
b2t True = ()
b2t False = Void

truthEq : (b : Bool) -> b2t b -> b = True
truthEq False x = absurd x
truthEq True () = Refl -- note that () : ()

eqTruth : {0 b : Bool} -> b = True -> b2t b
eqTruth Refl = () -- note that () : ()

-- _<=b_ -> _<=_ : proof by induction on numbers
--                 proof of _<=b_ can be transfered to proof of _<=_
--                 (disproof of _<=b_ can NOT be transfered)
blte2LTE : (m, n : Nat) -> b2t (blte m n) -> LTE m n
blte2LTE 0 n x = LTE0
--blte2LTE (S k) 0 x impossible
blte2LTE (S k) 0 x = absurd x -- it is apparent that x is uninhabited
blte2LTE (S k) (S j) x = LTEn $ blte2LTE k j x

-- _<=_ -> _<=b_ : proof by induction on evidence
--                 proof of _<=_ can be transfered to proof of _<=b_
--                 (disproof of _<=_ is NOT considered)
lTE2blte : {0 m, n : Nat} -> LTE m n -> b2t (blte m n)
lTE2blte LTE0 = ()
lTE2blte (LTEn prf) = lTE2blte prf


-- The best of both worlds
data Deci : (a : Type) -> Type where
  YES : a -> Deci a -- "a is inhabited"
                    -- "YES x --> x is the evidence of a"
  NO : Not a -> Deci a -- "a is uninhabited"
                       -- "NO x --> x is the evidence that a cannot hold"

notLTE0 : {m : Nat} -> Not (LTE (S m) 0)
notLTE0 _ impossible

notLTEn : {m, n : Nat} -> Not (LTE m n) -> Not (LTE (S m) (S n))
notLTEn f (LTEn x) = f x

------------------------------------------------------------------
-- _<=?_ (compare with blte2LTE)
lteDeci: (m, n : Nat) -> Deci (LTE m n)
lteDeci 0 n = YES LTE0
lteDeci (S k) 0 = NO notLTE0
lteDeci (S k) (S j) = case lteDeci k j of
                        (YES x) => YES $ LTEn x
                        (NO f) => NO $ notLTEn f
------------------------------------------------------------------

lTEsksjLTEkj : {k, j : Nat} -> LTE (S k) (S j) -> LTE k j
lTEsksjLTEkj (LTEn x) = x

-- same as notLTEn
nLTEkjnLTEsksj : {k, j : Nat} -> Not (LTE k j) -> Not (LTE (S k) (S j))
nLTEkjnLTEsksj f = (\sksj => let s = lTEsksjLTEkj sksj in f s)

-- _<=b_ -> _<=?_
-- proof/disproof of _<=b_ can be transfered to proof/disproof of _<=?_
blteDeci : (m, n : Nat) -> b2t (blte m n) -> Deci (LTE m n)
blteDeci 0 n _ = YES LTE0
--blteDeci (S k) 0 x = NO (\y => x) -- x : Void (i.e. impossible)
blteDeci (S k) 0 x impossible
blteDeci (S k) (S j) x = 
  case blteDeci k j x of
    (YES prf) => YES $ LTEn prf -- prf : LTE k j
    (NO f) => NO (notLTEn f) -- f : Not (LTE k j)
                             -- goal : Deci (LTE (S k) (S j))
                             -- --> NO (Not (LTE (S k) (S j)))

-- _<=_ -> _<=?_
--                 proof of _<=_ can be transfered to proof of _<=?_
--                 (disproof of _<=_ is NOT considered)
lTEDeci : {m, n : Nat} -> LTE m n -> Deci (LTE m n)
lTEDeci prf = YES prf

-- _<=?_ -> _<=b_
-- proof/disproof of _<=?_ can be transfered to proof/disproof of _<=b_
lteDeciBlte : (m, n : Nat) -> Deci (LTE m n) 
              -> Either (b2t (blte m n)) (Not (b2t (blte m n)))
lteDeciBlte m n (YES x) = Left $ lTE2blte x
lteDeciBlte m n (NO f) = Right $ \p => let p' = blte2LTE m n p in f p'

-- _<=?_ -> _<=_
-- proof/disproof of _<=?_ can be transfered to proof/disproof of _<=_
lteDeciLTE : {m, n : Nat} -> Deci (LTE m n)
             -> Either (LTE m n) (Not (LTE m n))
lteDeciLTE (YES x) = Left x
lteDeciLTE (NO f) = Right f


pDeci2LTE4 : lteDeci 2 4 = YES (LTEn (LTEn LTE0))
pDeci2LTE4 = Refl

pDeci4LTE2 : lteDeci 4 2 = NO (notLTEn (notLTEn (notLTE0 {m = _})))
pDeci4LTE2 = Refl
-- goal : Equal {a = Deci (LTE 4 2)} {b = Deci (LTE 4 2)}
--        (NO {a = LTE 4 2} (notLTEn {m = 3} {n = 1}
--                          (notLTEn {m = 2} {n = 0}
--                          (notLTE0 {m = 1}))))  <========
--        (NO {a = LTE 4 2} (notLTEn {m = 3} {n = 1} 
--                          (notLTEn {m = 2} {n = 0}
--                          notLTE0)))            <========


-- Decidables from booleans, and booleans from decidables
-- _<=?_ (define using _<=b_, _<=b_->_<=_, and _<=_->_<=b_)
--lteDeci': (m, n : Nat) -> Deci (LTE m n)
--lteDeci': (m, n : Nat)
--          -> (x : b2t (blte m n))
--          -> (y : blte2LTE m n x)
--          -> (z : lTE2blte {m} {n} y)
--          -> Deci (LTE m n)
--lteDeci' m n x y z = ?lteDeci'_rhs -- illegal type
--lteDeci': (m, n : Nat)
--          -> (b2t (blte m n))
--          -> (blte2LTE m n)
--          -> (lTE2blte {m} {n})
--          -> Deci (LTE m n)
--lteDeci' m n x y z = ?lteDeci'_rhs -- illegal type
--lteDeci': (m, n : Nat) -> Deci (LTE m n)
--lteDeci' m n = ?look


-- erasure
erase : {0 a : Type} -> Deci a -> Bool
erase (YES x) = True
erase (NO f) = False

-- _blte'_
blte' : Nat -> Nat -> Bool
blte' m n = erase $ lteDeci m n

-- if d is a value of type Deci a, b2t (erase d) is inhabited
-- exactly when a is inhabited
toWitness : {0 a : Type} -> {d : Deci a} -> b2t (erase d) -> a
toWitness {a} {d = (YES y)} () = y
toWitness {a} {d = (NO f)} x = absurd x

fromWitness : {0 a : Type} -> {d : Deci a} -> a -> b2t (erase d)
fromWitness {a} {d = (YES y)} x = ()
fromWitness {a} {d = (NO f)} x = absurd $ f x

-- b2t (blte' m n) is inhabited exactly when (LTE m n) is inhabited
-- (Implicit argument of toWitness (i.e. Deci a) is important.
--  Thus, blte' can not be replaced as blte.)
dir1 : {m, n : Nat} -> b2t (blte' m n) -> LTE m n
dir1 x = toWitness x

dir2 : {m, n : Nat} -> LTE m n -> b2t (blte' m n)
dir2 x = fromWitness x
