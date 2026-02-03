data LenList : (n : Nat) -> Type -> Type where
  MkLenList : (as : List a) -> LenList (length as) a

0 concatLen : (xs,ys : List a) -> length xs + length ys = length (xs ++ ys)
concatLen []        ys = Refl
concatLen (x :: xs) ys = cong S $ concatLen xs ys

(++) : LenList m a -> LenList n a -> LenList (m + n) a
MkLenList xs ++ MkLenList ys =
  rewrite concatLen xs ys in MkLenList (xs ++ ys)

-- believe me!
0 concatLenStr : (a,b : String) -> length a + length b = length (a ++ b)
concatLenStr a b = believe_me $ Refl {x = length a + length b}
-- concatLenStr a b = believe_me $ Refl {x = 8} -- This is accepted...

-- wrong 
0 doubleAddAssoc : (x,y,z : Double) -> x + (y + z) = (x + y) + z
doubleAddAssoc x y z = believe_me $ Refl {x = x + (y + z)}

Tiny : Double
Tiny = 0.0000000000000001

One : Double
One = 1.0

wrong : (0 _ : 1.0000000000000002 = 1.0) -> Void
wrong Refl impossible

boom : Void
boom = wrong (doubleAddAssoc One Tiny Tiny)
