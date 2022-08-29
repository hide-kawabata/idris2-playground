{----
  Why Dependent Types Matter 
  Section 3

  merge sort
  using list
  total sort by using DealT data type for internal representation
  total: sort must be terminating
  spec: nothing can be said about the result
----}

import Data.List
%hide Data.List.merge

%default total 

data Order : Type where
     Le : Order
     Ge : Order

order : (x : Nat) -> (y : Nat) -> Order
order Z y = Le
order (S x) Z = Ge
order (S x) (S y) = order x y

data Parity : Type where
     P0 : Parity
     P1 : Parity

data DealT : (a : Type) -> Type where
     EmpT : DealT a
     LeafT : a -> DealT a
     NodeT : (p : Parity) -> (l : DealT a) -> (r : DealT a) -> DealT a

{- construct a balanced binary tree -}
{- steps as many as the hight of the tree are required -}
insertT : {a : Type} -> a -> (t : DealT a) -> DealT a
insertT x EmpT = LeafT x
insertT x (LeafT y) = NodeT P0 (LeafT y) (LeafT x)
insertT x (NodeT P0 l r) = NodeT P1 (insertT x l) r
insertT x (NodeT P1 l r) = NodeT P0 l (insertT x r)

{- converts a list to a tree -}
{- not so cheap -}
dealT : {a : Type} -> List a -> DealT a
dealT [] = EmpT
dealT (x :: xs) = insertT x (dealT xs)

merge : (xs : List Nat) -> (ys : List Nat) -> List Nat
merge [] ys = ys
merge (x :: xs') [] = x :: xs'
merge (x :: xs') (y :: ys') = case order x y of
                                   Le => x :: merge xs' ( y :: ys')
                                   Ge => y :: merge (x :: xs') ys'

mergeT : DealT Nat -> List Nat
mergeT EmpT = []
mergeT (LeafT x) = x :: []
mergeT (NodeT p l r) = merge (mergeT l) (mergeT r)

sort : List Nat -> List Nat
sort = mergeT . dealT

