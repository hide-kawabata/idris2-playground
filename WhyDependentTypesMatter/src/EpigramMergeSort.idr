{----
  Why Dependent Types Matter
  Section 1

  merge sort
  non-total sort
----}

--%hide Prelude.Nat
%hide Prelude.List

%default total
{-
data Nat : Type where
     Z : Nat
     S : Nat -> Nat
-}

data Order : Type where
     Le : Order
     Ge : Order

{-
data List : {X : Type} -> (x : X) -> Type where
     Nil : {X : Type} -> List X
     (::) : {X : Type} -> (x : X) -> (xs : List X) -> List X
-}
data List : {a : Type} -> a -> Type where
     Nil : List a
     (::) : (x : a) -> (xs : List a) -> List a

order : (x : Nat) -> (y : Nat) -> Order
order Z y = Le
order (S x) Z = Ge
order (S x) (S y) = order x y

merge : (xs : List Nat) -> (ys : List Nat) -> List Nat
merge [] ys = ys
merge (x :: xs') [] = x :: xs'
{-
merge (x :: xs') (y :: ys') with (order x y)
  merge (x :: xs') (y :: ys') | Le = x :: merge xs' (y :: ys')
  merge (x :: xs') (y :: ys') | Ge = y :: merge (x :: xs') ys'
-}
merge (x :: xs') (y :: ys') = case order x y of
                                   Le => x :: merge xs' ( y :: ys')
                                   Ge => y :: merge (x :: xs') ys'

deal : {a : Type} -> (xs : List a) -> (List a, List a)
deal [] = ([], [])
deal (x :: []) = (x :: [], [])
deal (x :: (y :: xs)) with (deal xs)
  deal (x :: (y :: xs)) | (z, w) = (x :: z, y :: w)

partial sort : (xs : List Nat) -> List Nat
{-
sort xs with (deal xs)
  sort xs | (ys, []) = ys
  sort xs | (ys, z :: zs) = merge (sort ys) (sort (z :: zs))
-}
sort xs = case deal xs of
               (ys, []) => ys
               (ys, z :: zs) => merge (sort ys) (sort (z :: zs))

