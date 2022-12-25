{-
  simplified version of SplitList
-}
data SplitList : List a -> Type where
  SplitPair : (ls : List a) -> (rs : List a) -> SplitList (ls ++ rs)

total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp (length input) input
  where
    splitListHelp : Nat -> (input : List a) -> SplitList input
    splitListHelp Z [] = SplitPair [] [] -- length : even (zero)
    splitListHelp Z items = SplitPair [] items -- length : even (more than zero)
    splitListHelp (S Z) [] = SplitPair [] [] -- X (never comes here)
    splitListHelp (S Z) [x] = SplitPair [] [x] -- length : odd (one)
    splitListHelp (S Z) items = SplitPair [] items -- length : odd (more than one)
    splitListHelp (S (S k)) [] = SplitPair [] [] -- X
    splitListHelp (S (S k)) [x] = SplitPair [] [x] -- X
    splitListHelp (S (S k)) (x :: xs) -- length : odd or even, more than or equal to two
      = case splitListHelp k xs of
          (SplitPair ls rs) => SplitPair (x :: ls) rs

{-
-- a smarter implementation based on the one in the textbook

total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
  where
    splitListHelp : List a -> (input : List a) -> SplitList input
    splitListHelp [] [] = SplitPair [] [] -- length zero
    splitListHelp [x'] [x] = SplitPair [] [x] -- length one
    splitListHelp (_ :: _ :: c) (i :: is) -- length more than one
      = case splitListHelp c is of
          (SplitPair ls rs) => SplitPair (i :: ls) rs -- length more than two
    splitListHelp _ items = SplitPair [] items
-}
