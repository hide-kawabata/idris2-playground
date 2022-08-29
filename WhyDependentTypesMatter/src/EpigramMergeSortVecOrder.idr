{- Dependent Order, from "Why Dependent Types Matter?" -}

{----
  merge sort
  using vec
  total
  sorted (the result is a sorted vector with the same length as the input)
----}

import Data.Nat

%default total
----------------------------------------------------------
data LE : Nat -> Nat -> Type where
     LeZ : LE 0 _
     LeS : LE x y -> LE (S x) (S y)

data Order2 : (x : Nat) -> (y : Nat) -> Type where
     Le2 : {x : Nat} -> {y : Nat} -> LE x y -> Order2 x y
     Ge2 : {y : Nat} -> {x : Nat} -> LE x y -> Order2 y x

-----------------------------
{-- is this called a covering function? --}
order2 : (x : Nat) -> (y : Nat) -> Order2 x y
order2 Z y = Le2 LeZ
order2 (S k) 0 = Ge2 LeZ
order2 (S k) (S j) = case order2 k j of
                          (Le2 klej) => Le2 (LeS klej)
                          (Ge2 jlek) => Ge2 (LeS jlek)

----------------------------------------------------------
{- Vec len a -}
data Vec : Nat -> Type -> Type where
     Vnil : Vec 0 a
     Vcons : a -> (xs : Vec n a) -> Vec (S n) a

{- OVec len min a -}
data OVec : Nat -> (b : Nat) -> Type -> Type where
     Ovnil : OVec 0 b a
     Ovcons : (x : Nat) -> (blex : LE b x) -> (xs: OVec m x a) -> OVec (S m) b a

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

--tr1 : OVec (S (plus m n)) b a -> OVec (plus m (S n)) b a
--tr1 xs = rewrite sym $ plusSuccRightSucc m n in xs

tr1 : OVec (S (S (plus n m))) b a -> OVec (S (plus n (S m))) b a
tr1 xs = rewrite sym $ plusSuccRightSucc n m in xs

merge : OVec m b a -> OVec n b a -> OVec (m + n) b a
merge Ovnil ys = ys
merge (Ovcons x blex xs') Ovnil = Ovcons x blex (merge xs' Ovnil)
merge (Ovcons x blex xs') (Ovcons y bley ys') = case order2 x y of
  (Le2 xley) => Ovcons x blex (merge xs' (Ovcons y xley ys'))
  (Ge2 ylex) => tr1 $ Ovcons y bley (merge (Ovcons x ylex xs') ys')

mergeT : DealT c Nat -> OVec c 0 Nat
mergeT EmpT = Ovnil
mergeT (LeafT x) = Ovcons x LeZ Ovnil
mergeT (NodeT p l r) = merge (mergeT l) (mergeT r) -- NodeT's implicit argument definition is required

tr2 : DealT (S (plus m (S m))) a -> DealT (S (S (plus m m))) a
tr2 xs = rewrite plusSuccRightSucc m m in xs

{- construct a balanced binary tree -}
{- steps as many as the hight of the tree are required -}
insertT : {a : Type} -> a -> (t : DealT n a) -> DealT (S n) a
insertT x EmpT = LeafT x
insertT x (LeafT y) = NodeT P0 (LeafT y) (LeafT x)
insertT x (NodeT P0 l r) = NodeT P1 (insertT x l) r
insertT x (NodeT P1 l r) = tr2 $ NodeT P0 l (insertT x r)

{- converts a list to a tree -}
{- not so cheap -}
dealT : {a : Type} -> Vec n a -> DealT n a
dealT Vnil = EmpT
dealT (Vcons x xs) = insertT x (dealT xs)

sort : Vec n Nat -> OVec n 0 Nat
sort = mergeT . dealT
