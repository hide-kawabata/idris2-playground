import Data.Vect
-- import Decidable.Equality
import Data.Vect.Elem

{-
data Elem : a -> Vect k a -> Type where
    Here : Elem x (x :: xs)
    There : (later : Elem x xs) -> Elem x (y :: xs)

-- The following definitions are required to use absurd against your own Elem.
Uninhabited (Here = There e) where
    uninhabited Refl impossible
Uninhabited (There e = Here) where
    uninhabited Refl impossible
Uninhabited (Elem n []) where
    uninhabited Here impossible
    uninhabited (There later) impossible
-}

{-
removeElem0 : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
removeElem0 value (x :: xs) = case decEq value x of
                                  (Yes Refl) => xs
                                  (No contra) => x :: removeElem0 value xs -- type error
-}

oneInVector : Elem 1 [1, 2, 3]
oneInVector = Here

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

noElemInEmptyVect : {0 e : _} -> Elem e [] -> Void
noElemInEmptyVect Here impossible
noElemInEmptyVect (There later) impossible


two_plus_two_not_five : 2 + 2 = 5 -> Void
two_plus_two_not_five Refl impossible

Uninhabited (2 + 2 = 5) where
    uninhabited (Refl {x = 2 + 2}) impossible
    -- uninhabited Refl impossible -- this suffices

-- there can be many different ways of defining a function
total
removeElem : {n : _} -> (value : a) -> 
             (xs : Vect (S n) a) ->
             (prf : Elem value xs) -> -- expressing a contract
             Vect n a
removeElem value (value :: xs) Here = xs
-- removeElem {n = 0} value (y :: _) (There later) = []
-- removeElem {n = 0} value (y :: _) _ = []
-- removeElem {n = 0} value (y :: []) _ = []
-- removeElem {n = 0} value (y :: []) (There later) = []
-- removeElem {n = 0} value (y :: []) (There later) impossible
-- removeElem {n = 0} value (y :: _) (There later) impossible
-- removeElem {n = 0} _ (_ :: _) (There _) impossible
-- removeElem {n = 0} value (y :: []) (There later) = absurd later -- later must be Uninhabited
-- removeElem {n = _} value (y :: []) (There later) = absurd later -- later must be Uninhabited
removeElem {n = (S k)} value (y :: xs) (There later) = y :: removeElem value xs later

{-
Main> removeElem 1 (the (Vect _ Nat) [1, 2, 3]) Here
[2, 3]
Main> removeElem 1 (the (Vect _ Nat) [2, 1, 3]) (There Here)
[2, 3]
Main> removeElem 1 [1, 2, 3] Here
[2, 3]
Main> removeElem 1 [2, 1, 3] (There Here)
[2, 3]
 -}

total
removeElem' : {n : _} -> (value : a) -> 
             (xs : Vect (S n) a) ->
             (prf : Elem value xs) -> -- expressing a contract explicitly
             Vect n a
removeElem' value (value :: xs) Here = xs
removeElem' value (y :: xs) (There later) {n = (S k)} = y :: removeElem value xs later

total
removeElem_auto : {n : _} -> (value : a) ->
             (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} -> -- expressing a contract with the mark auto
             Vect n a
removeElem_auto value (value :: xs) {prf = Here} = xs
removeElem_auto value (y :: xs) {prf = (There later)} {n = (S k)}
    = y :: removeElem_auto value xs -- this suffices

-- it's no use of making the argument prf implicit, at least in this case
total
removeElem_noauto : {n : _} -> (value : a) ->
             (xs : Vect (S n) a) ->
             {prf : Elem value xs} -> -- expressing a contract without the mark auto
             Vect n a
removeElem_noauto value (value :: xs) {prf = Here} = xs
removeElem_noauto value (y :: xs) {prf = (There later)} {n = (S k)}
    = y :: removeElem_noauto value xs {prf = later} -- {prf = later} is required

