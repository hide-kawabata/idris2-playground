import Data.Vect

data Elem : a -> Vect k a -> Type where
     Here : Elem x (x :: xs)
     There : (later : Elem x xs) -> Elem x (y :: xs)

-- It seems that you need to write down explicitly
-- that Elem v [] is Uninhabited. (*1)
Uninhabited (Elem v []) where
  uninhabited _ impossible

removeElem : {n : _} ->
             (value : a) -> 
             (xs : Vect (S n) a) ->
             (prf : Elem value xs) ->
             Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later -- (*1)
removeElem {n = (S k)} value (y :: ys) (There later)
                                          = y :: removeElem value ys later
