{----
  merge sort
  total and length-aware (using Vector) version 
  total: sort function must terminates
  spec: length must be preserved during the process of sorting
----}

import Data.Nat
import Data.List

%default total

data Order : Type where
     Le : Order
     Ge : Order

data Vec : Nat -> Type -> Type where
     Vnil : Vec 0 a
     Vcons : a -> (xs : Vec n a) -> Vec (S n) a

order : (x : Nat) -> (y : Nat) -> Order
order Z y = Le
order (S x) Z = Ge
order (S x) (S y) = order x y

data Parity : Type where
     P0 : Parity
     P1 : Parity

hat: Parity -> Nat
hat P0 = 0
hat P1 = 1

data DealT : (n : Nat) -> (a : Type) -> Type where
     EmpT : DealT 0 a
     LeafT : a -> DealT 1 a
     NodeT : {m : Nat} -> (p : Parity) -> (l : DealT (hat p + m) a) -> (r : DealT m a) -> DealT ((hat p + m) + m) a -- "{m : Nat} ->" is necessary

--tr0 : Vec (S n) Nat -> Vec (S (plus n 0)) Nat
--tr0 xs = rewrite plusZeroRightNeutral n in xs

tr1 : Vec (S (plus m n)) Nat -> Vec (plus m (S n)) Nat
tr1 xs = rewrite sym $ plusSuccRightSucc m n in xs

merge : (xs : Vec m Nat) -> (ys : Vec n Nat) -> Vec (m + n) Nat
merge Vnil ys = ys
--merge (Vcons x xs') Vnil = tr0 $ Vcons x xs' -- goal : Vec (S (plus n 0)) Nat 
merge (Vcons x xs') Vnil = Vcons x (merge xs' Vnil) -- goal : Vec (S (plus n 0)) Nat 
merge (Vcons x xs') (Vcons y ys') = case order x y of
                                         Le => Vcons x (merge xs' (Vcons y ys'))
                                         Ge => Vcons y (tr1 $ merge (Vcons x xs') ys') -- goal : Vec (S (plus n (S n))) Nat

mergeT : DealT c Nat -> Vec c Nat
mergeT EmpT = Vnil
mergeT (LeafT x) = Vcons x Vnil
mergeT (NodeT p l r) = merge (mergeT l) (mergeT r) -- NodeT's implicit argument definition is required

tr2 : DealT (S (plus m (S m))) a -> DealT (S (S (plus m m))) a
tr2 t = rewrite plusSuccRightSucc m m in t

{- construct a balanced binary tree -}
{- steps as many as the hight of the tree are required -}
insertT : {a : Type} -> a -> (t : DealT n a) -> DealT (S n) a
insertT x EmpT = LeafT x
insertT x (LeafT y) = NodeT P0 (LeafT y) (LeafT x)
insertT x (NodeT P0 l r) = NodeT P1 (insertT x l) r
insertT x (NodeT P1 l r) = tr2 $ NodeT P0 l (insertT x r)

{- converts a vector to a tree -}
{- not so cheap -}
dealT : {a : Type} -> Vec n a -> DealT n a
dealT Vnil = EmpT
dealT (Vcons x xs) = insertT x (dealT xs)

sort : Vec n Nat -> Vec n Nat
sort = mergeT . dealT
