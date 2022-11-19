import Data.Vect

data Elem : a -> Vect k a -> Type where
     Here : Elem x (x :: xs)
     There : (later : Elem x xs) -> Elem x (y :: xs)

-- It seems that you need to write down explicitly
-- that Elem v [] is Uninhabited. (*1)
Uninhabited (Elem v []) where
  uninhabited _ impossible

-- Q: How can you automatically obtain the right-hand side of (*1) ?

removeElem : {n : _} ->
             (value : a) -> 
             (xs : Vect (S n) a) ->
             (prf : Elem value xs) ->
             Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later -- (*1)
removeElem {n = (S k)} value (y :: ys) (There later)
                                          = y :: removeElem value ys later

removeElem_auto : {n : _} -> (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

removeElem' : {n : _} ->
              (value : a) -> (xs : Vect (S n) a) ->
              {auto prf : Elem value xs} ->
              Vect n a
removeElem' {n = n} value (value :: xs) {prf = Here} = xs
removeElem' {n = 0} value (y :: []) {prf = (There later)} = absurd later
removeElem' {n = (S k)} value (y :: xs) {prf = (There later)} =
            y :: removeElem' value xs

-- Q: Can you define a function that remove all occurrences of the
-- designated value in a Vect?
