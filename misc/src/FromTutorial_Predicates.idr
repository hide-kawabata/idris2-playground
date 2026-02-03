-- Idris 2 Tutorial
-- 13 Predicates and Proof Search

data NotNil : (as : List a) -> Type where
  IsNotNil : NotNil (h :: t)

head1 : (as : List a) -> (0 _ : NotNil as) -> a
head1 (h :: _) _ = h
head1 [] IsNotNil impossible

head1' : (as : List a) -> {0 prf : NotNil as} -> a
head1' (h :: _) = h
head1' [] {prf=IsNotNil} impossible

head : (as : List a) -> {auto 0 prf : NotNil as} -> a
head (x :: _) = x
head [] impossible

head' : (as : List a) -> (0 _ : NotNil as) => a
head' (x :: _) = x
head' [] impossible


-- get' : (0 t : Type) -> HList ts -> t

-- get' : (t : Type) -> Type
-- get' t = t

-- voidQ : Type
-- voidQ = get' Void
