{-
  Defining myReverse by using SnocList/snocList 
-}

--import Data.List

%default total

data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : {x : a} -> {xs : List a} ->
            (rec : SnocList xs) -> SnocList (xs ++ [x])

-- defined in Data.List
appendNilRightNeutral : (l : List a) -> l ++ [] = l
-- (1) Base case      : [] ++ [] = []
appendNilRightNeutral [] = Refl
-- (2) Induction step : xs ++ [] = xs => (x :: xs) ++ [] = x :: xs 
--  Refl must be used.
--  (x :: xs) ++ [] is simplified to x :: (xs ++ []).
--  IH "xs++[]=xs" is represented by "appendNilRightNeutral xs".
--  Thus, (x :: xs) ++ [] is rewritten to x :: xs.
appendNilRightNeutral (x :: xs) -- x :: (xs ++ []) = x :: xs
  = rewrite appendNilRightNeutral xs in Refl

-- defined in Data.List
appendAssociative : (l1 : List a) -> (l2 : List a) -> (l3 : List a) -> 
                    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3
appendAssociative [] l2 l3 = Refl
appendAssociative (x :: xs) l2 l3 = rewrite appendAssociative xs l2 l3 in Refl


-- The pair of 1st and 2nd arguments can be viewed as a kind of invariant.
snocListHelp : {input : _} -> (snoc : SnocList input) -> (rest : List a) ->
               SnocList (input ++ rest)
snocListHelp {input = input} snoc [] = 
  let exp = snoc in                      -- expression of the returned value
  rewrite appendNilRightNeutral input in -- proof of type correctness
  exp
snocListHelp {input = input} snoc (q :: qs) =
  let exp = snocListHelp (Snoc snoc {x=q}) qs in -- expression of the value
  rewrite appendAssociative input [q] qs in      -- proof of the type
  exp

-- another version
snocListHelp' : {input : _} -> (snoc : SnocList input) -> (rest : List a) ->
               SnocList (input ++ rest)
snocListHelp' {input = []} snoc [] = 
  let exp = snoc in -- expression of the returned value
  exp
snocListHelp' {input = []} snoc (x :: xs) =
  let exp = snocListHelp' (Snoc snoc) xs in -- expression of the returned value
  exp
snocListHelp' {input = (p :: ps)} snoc [] = 
  let exp = snoc in -- expression of the returned value
  rewrite appendNilRightNeutral ps in -- additional proof of type correctness
  exp
snocListHelp' {input = (p :: ps)} snoc (q :: qs) =
  let exp = snocListHelp' (Snoc {x=q} snoc) qs in -- expression
  rewrite appendAssociative ps [q] qs in -- proof of type correctness
  exp
 
-- convert a List to a SnocList (the covering function for SnocList)
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs -- the 1st argument is the accumulator


-- definition of myReverse by using snocList
myReverse : List a -> List a
myReverse xs = myReverseHelper xs (snocList xs)
  where
    myReverseHelper : (input : List a) -> SnocList input -> List a
    myReverseHelper [] Empty = []
    myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec
  {- You can also write myReverseHelper as follows:
    myReverseHelper' : (input : List a) -> SnocList input -> List a
    myReverseHelper' _ Empty = []
    myReverseHelper' _ (Snoc {x} rec {xs}) = x :: myReverseHelper' xs rec
  -}

-- definition of myReverse by using *with* construct
myReverse' : List a -> List a
myReverse' xs with (snocList xs)
  myReverse' [] | Empty = []
  myReverse' (xs ++ [x]) | (Snoc rec) = 
    x :: myReverse' xs | rec -- writing this way makes this function total
--    x :: myReverse' xs -- writing this way does not guarantee the totality

-- another version
myReverse'' : List a -> List a
myReverse'' xs with (snocList xs)
  myReverse'' _ | Empty = []
  myReverse'' _ | (Snoc rec {x} {xs}) = 
    x :: myReverse'' xs | rec

-- another version
myReverse3 : List a -> List a
myReverse3 xs with (snocList xs)
  myReverse3 [] | _ = []
  myReverse3 _ | (Snoc {x} rec {xs}) = 
    x :: myReverse3 xs | rec

-- for comparison:
{-
  Simple implementation of myReverse, which is slow.
  * total: covers and terminates
  * slow: requires O(n^2) steps 
  * vague specification: the type says almost nothing
-}
myReverseSlow : List a -> List a
myReverseSlow [] = []
myReverseSlow (x :: xs) = myReverseSlow xs ++ [x]

{-
  Simple but efficient implementation of myReverse.
  * total: covers and terminates
  * fast: requires only O(n) steps
  * vague specification: the type says almost nothing
-}
myReverseFast : List a -> List a
myReverseFast [] = []
myReverseFast (x :: xs) = myReverseFastHelper [x] xs
  where
    myReverseFastHelper : List a -> List a -> List a
    myReverseFastHelper ws [] = ws
    myReverseFastHelper [] (x :: xs) = myReverseFastHelper [x] xs
    myReverseFastHelper ws (x :: xs) = myReverseFastHelper (x::ws) xs

