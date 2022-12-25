data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [e]
  SplitPair : (ls : List a) -> (rs : List a) -> SplitList (ls ++ rs)

{-
  Some cases are not used but not excluded by type;
  used type is not precise enough for the purpose.
-}
total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp (length input) input
  where
    splitListHelp : Nat -> (input : List a) -> SplitList input
    splitListHelp Z [] = SplitNil -- length : even (zero)
    splitListHelp Z items = SplitPair [] items -- length : even (more than zero)
    splitListHelp (S Z) [] = SplitNil -- X (never comes here)
    splitListHelp (S Z) [x] = SplitOne -- length : odd (one)
    splitListHelp (S Z) items = SplitPair [] items -- length : odd (more than one)
    splitListHelp (S (S k)) [] = SplitNil -- X
    splitListHelp (S (S k)) [x] = SplitOne -- X
    splitListHelp (S (S k)) (x :: xs) -- length : odd or even, more than or equal to two
      = case splitListHelp k xs of
          SplitNil => SplitOne -- X (never comes here)
          SplitOne {e} => SplitPair [x] [e] -- X (never comes here)
          (SplitPair ls rs) => SplitPair (x :: ls) rs

{-
-- a smarter implementation in the textbook
total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
  where
    splitListHelp : List a -> (input : List a) -> SplitList input
    splitListHelp [] [] = SplitNil -- length zero
    splitListHelp [x'] [x] = SplitOne -- length one
    splitListHelp (_ :: _ :: c) (i :: is) -- length more than one
      = case splitListHelp c is of
          SplitNil => SplitOne -- length one !? (never comes here)
          SplitOne {e} => SplitPair [i] [e] -- length two
          (SplitPair ls rs) => SplitPair (i :: ls) rs -- length more than two
    splitListHelp _ items = SplitPair [] items
-}
