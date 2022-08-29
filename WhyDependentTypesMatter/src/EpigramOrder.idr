{- 
  Dependent Order, from "Why Dependent Types Matter?" 
  Section 5
-}

{----
  merge sort
  using list
  not total (no length check involved --- termination checked not performed)
  sorted (if the result is obtained, the result must be a sorted list)
----}

%default total
----------------------------------------------------------
{-- first attempt --}
data Order : Nat -> Nat -> Type where
     Le : (x : Nat) -> (y : Nat) -> Order x y
     Ge : (x : Nat) -> (y : Nat) -> Order x y

threeOrdFour : Order 3 4
threeOrdFour = Le 3 4

fiveOrdThree : Order 5 3
fiveOrdThree = Le 5 3 -- Nonsense!!

total
order : (x : Nat) -> (y : Nat) -> Order x y
order Z y = Le Z y
order (S k) Z = Ge (S k) Z
order (S k) (S j) = case order k j of
                         (Le k j) => Le (S k) (S j)
                         (Ge k j) => Ge (S k) (S j)

----------------------------------------------------------
{-- better definition --}
data LE : Nat -> Nat -> Type where
     LeZ : LE 0 _
     LeS : LE x y -> LE (S x) (S y)

data Order2 : (x : Nat) -> (y : Nat) -> Type where
     Le2 : {x : Nat} -> {y : Nat} -> LE x y -> Order2 x y
     Ge2 : {y : Nat} -> {x : Nat} -> LE x y -> Order2 y x

-----------------------------
total leRefl : (x : Nat) -> LE x x
leRefl Z = LeZ
leRefl (S k) = LeS (leRefl k)

total leTrans : {x : Nat} -> {y : Nat} -> {z : Nat} -> LE x y -> LE y z -> LE x z
leTrans LeZ _ = LeZ
leTrans (LeS xley') (LeS ylez') = LeS (leTrans xley' ylez')

total leASym : {x : Nat} -> {y : Nat} -> (xley : LE x y) -> (ylex : LE y x) -> x = y
leASym LeZ LeZ = Refl
leASym (LeS xley') (LeS ylex') = case leASym xley' ylex' of
                                      Refl => Refl
--leASym (LeS xley') (LeS ylex') = cong S (case leASym xley' ylex' of
--                                              Refl => Refl)

-----------------------------
threeLEFour : LE 3 4
threeLEFour = LeS (LeS (LeS LeZ))

threeOrd2Four : Order2 3 4
threeOrd2Four = Le2 (LeS (LeS (LeS LeZ)))

fiveLEThree : LE 5 3 -> Void
fiveLEThree (LeS (LeS (LeS _))) impossible

fiveOrd2Three : Order2 5 3
fiveOrd2Three = Ge2 (LeS (LeS (LeS LeZ)))

{-- is this called a covering function? --}
total
order2 : (x : Nat) -> (y : Nat) -> Order2 x y
order2 Z y = Le2 LeZ
order2 (S k) 0 = Ge2 LeZ
order2 (S k) (S j) = case order2 k j of
                          (Le2 klej) => Le2 (LeS klej)
                          (Ge2 jlek) => Ge2 (LeS jlek)

----------------------------------------------------------
data OList : (b : Nat) -> Type where
     Onil : OList b
     Ocons : (x : Nat) -> (blex : LE b x) -> (xs: OList x) -> OList b

data Parity : Type where
     P0 : Parity
     P1 : Parity

data DealT : (a : Type) -> Type where
     EmpT : DealT a
     LeafT : a -> DealT a
     NodeT : (p : Parity) -> (l : DealT a) -> (r : DealT a) -> DealT a

partial
merge : OList b -> OList b -> OList b
merge Onil ys = ys
merge (Ocons x blex xs') Onil = Ocons x blex xs'
merge (Ocons x blex xs') (Ocons y bley ys') = case order2 x y of
                                                   (Le2 xley) => Ocons x blex (merge xs' (Ocons y xley ys'))
                                                   (Ge2 ylex) => Ocons y bley (merge (Ocons x ylex xs') ys')

partial
mergeT : DealT Nat -> OList 0
mergeT EmpT = Onil
mergeT (LeafT x) = Ocons x LeZ Onil
mergeT (NodeT p l r) = merge (mergeT l) (mergeT r)

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

partial
sort : List Nat -> OList 0
sort = mergeT . dealT
