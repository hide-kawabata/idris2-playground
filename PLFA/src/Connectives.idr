-- conjunction; applying destructors and reassembling with constructors
etaProd : {a, b : Type} -> (w : Pair a b) -> (fst w, snd w) = w
etaProd (x, y) = Refl

-- conjunction as a record type
record Conj (a, b : Type) where
  constructor MkConj
  proj1 : a
  proj2 : b

-- use of product and record; no difference in Idris (?)
etaConj : {a, b : Type} -> (w : Conj a b) -> MkConj (proj1 w) (proj2 w) = w
etaConj (MkConj proj1 proj2) = Refl

etaConj' : {a, b : Type} -> (w : Conj a b) -> MkConj w.proj1 w.proj2 = w
etaConj' (MkConj proj1 proj2) = Refl

-- elimination of disjunction
caseEither : {a, b, c : Type} -> (a -> c) -> (b -> c) -> Either a b -> c
caseEither f g (Left x) = f x
caseEither f g (Right y) = g y

-- disjunction; applying destructors and reassembling with constructors
etaEither : {a, b : Type} -> (w : Either a b) -> caseEither Left Right w = w
etaEither (Left x) = Refl
etaEither (Right y) = Refl

uniqEither : {a, b, c : Type} -> (h : Either a b -> c) -> (w : Either a b)
             -> caseEither (h . Left) (h . Right) w = h w
uniqEither h (Left x) = Refl
uniqEither h (Right y) = Refl

-- implication elimination (modus ponens)
impElim : {a, b : Type} -> (a -> b) -> a -> b
impElim f x = f x

-- elimination of implication followed by introduction is the identity
etaImp : {a, b : Type} -> (f : a -> b) -> (\x => f x) = f
etaImp f = Refl -- definitionally equal ???
