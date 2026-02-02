-- 11 Sigma Types

import Data.Vect
import Data.String
import Data.DPair
import Data.Singleton

parseAndDrop : Vect (3 + n) String -> Maybe (Vect n Nat)
parseAndDrop = map (drop 3) . traverse parsePositive

f : Void -> Bool
f = const True

record AnyVect a where
  constructor MkAnyVect
  length : Nat
  vect   : Vect length a

-- Note, how from the outside of AnyVect a, the length of the wrapped vector is
-- not visible at the type level -- can not be
takeWhile : (a -> Bool) -> Vect n a -> AnyVect a
takeWhile f []        = MkAnyVect 0 []
takeWhile f (x :: xs) = case f x of
  False => MkAnyVect 0 []
  True  => let MkAnyVect n ys = takeWhile f xs in MkAnyVect (S n) (x :: ys)

record DPair' (a : Type) (p : a -> Type) where
  constructor MkDPair'
  fst : a
  snd : p fst

AnyVect' : (a : Type) -> Type
AnyVect' a = DPair Nat (\n => Vect n a)

AnyVect'' : (a : Type) -> Type
AnyVect'' a = (n : Nat ** Vect n a)

takeWhile3 : (a -> Bool) -> Vect m a -> (n ** Vect n a)
takeWhile3 f []        = (_ ** [])
takeWhile3 f (x :: xs) = case f x of
  False => (_ ** [])
  True  => let (_  ** ys) = takeWhile3 f xs in (_ ** x :: ys)

AnyMatrix : (a : Type) -> Type
AnyMatrix a = (m ** n ** Vect m (Vect n a))

takeWhileExists : (a -> Bool) -> Vect m a -> Exists (\n => Vect n a)
-- takeWhileExists f []        = Evidence _ []
-- takeWhileExists f (x :: xs) = case f x of
--   True  => let Evidence _ ys = takeWhileExists f xs
--             in Evidence _ (x :: ys)
--   False => takeWhileExists f xs
takeWhileExists f [] = Evidence 0 []
takeWhileExists f (x :: xs) = case f x of
    False => takeWhileExists f xs
    True => let Evidence n xs = takeWhileExists f xs in
            Evidence (S n) (x :: xs)

-- Singleton type example
true : Singleton True
true = Val _

vectLength : Vect n a -> Singleton n
vectLength [] = Val 0
vectLength (x :: xs) = let Val k = vectLength xs in
                       Val (S k)

-- no guarantee that the returned value is n at the type level
vectLength' : {n : _} -> Vect n a -> Nat
vectLength' {n = len} xs = len

bogusLength : Vect n a -> Nat
bogusLength = const 0

vleneq : (xs : Vect len _) -> Val (vectLength' xs) = vectLength xs
vleneq [] = Refl {x = Val 0}
vleneq (x :: xs) =
  let prf = vleneq xs in rewrite sym prf in Refl {x = Val len}

vleneq' : (xs : _) -> Val (vectLength' xs) = vectLength xs
vleneq' [] = Refl
vleneq' (x :: xs) =
  let prf = vleneq' xs in rewrite sym prf in Refl

toDPair : Exists (\n => Vect n a) -> (m ** Vect m a)
toDPair (Evidence _ as) = let Val m = vectLength as in (m ** as)
