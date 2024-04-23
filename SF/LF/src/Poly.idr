{-
  Poly
  Polymorphism and Higher-Order Functions
 -}

-- Polymorphism

-- Polymorphic Lists

data BoolList : Type where
  BoolNil : BoolList
  BoolCons : (b : Bool) -> (l : BoolList) -> BoolList

data List' : (X : Type) -> Type where
  Nil : (X : Type) -> List' X
  Cons : (X : Type) -> (x : X) -> (l : List' X) -> List' X

repeat : (ty : Type) -> (x : ty) -> (count : Nat) -> List' ty
repeat ty x 0 = Nil ty
repeat ty x (S c') = Cons ty x (repeat ty x c')

test_repeat1 : repeat Nat 4 2 = Cons Nat 4 (Cons Nat 4 (Nil Nat))
test_repeat1 = Refl
test_repeat2 : repeat Bool False 1 = Cons Bool False (Nil Bool)
test_repeat2 = Refl

data Mumble : Type where
  A : Mumble
  B : (x : Mumble) -> (y : Nat) -> Mumble
  C : Mumble

data Grumble : (ty : Type) -> Type where
  D : (m : Mumble) -> Grumble ty
  E : (x : ty) -> Grumble ty

data IList : (ty : Type) -> Type where
  INil : IList ty
  ICons : (x : ty) -> (l : IList ty) -> IList ty

app : {ty : Type} -> (l1 : IList ty) -> (l2 : IList ty) -> IList ty
app {ty} INil l2 = l2
app {ty} (ICons x l) l2 = ICons x (app l l2)

rev : {ty : Type} -> (l : IList ty) -> IList ty
rev INil = INil
rev (ICons x l) = app (rev l) (ICons x INil)

length : {ty : Type} -> (l : IList ty) -> Nat
length INil = 0
length (ICons x l) = S (length l)

test_rev1 : rev (ICons 1 (ICons 2 INil)) = (ICons 2 (ICons 1 INil))
test_rev1 = Refl
test_rev2 : rev (ICons True INil) = ICons True INil
test_rev2 = Refl
test_length1 : length (ICons 1 (ICons 2 (ICons 3 INil))) = 3
test_length1 = Refl

app_nil_r : {ty : Type} -> (l : IList ty) -> app l INil = l
app_nil_r INil = Refl
app_nil_r (ICons x l) = let ih = app_nil_r l in rewrite ih in Refl

app_assoc : {ty : Type} -> (l1 : IList ty) -> (l2 : IList ty) -> (l3 : IList ty) ->
  app (app l1 l2) l3 = app l1 (app l2 l3)
app_assoc INil l2 l3 = Refl
app_assoc (ICons x l) l2 l3 = 
  let ih = app_assoc l l2 l3 in
  rewrite ih in Refl

rev_app_distr : {ty : Type} -> (l1 : IList ty) -> (l2 : IList ty) ->
    rev (app l1 l2) = app (rev l2) (rev l1)
rev_app_distr INil l2 = rewrite app_nil_r (rev l2) in Refl
rev_app_distr (ICons n l) l2 = 
    rewrite (rev_app_distr l l2) in
    rewrite (app_assoc (rev l2) (rev l) (ICons n INil)) in 
    Refl

rev_involutive : {ty : Type} -> (l : IList ty) -> 
    rev (rev l) = l
rev_involutive INil = Refl
rev_involutive (ICons x l) = 
    rewrite rev_app_distr (rev l) (ICons x INil) in
    rewrite rev_involutive l in 
    Refl
