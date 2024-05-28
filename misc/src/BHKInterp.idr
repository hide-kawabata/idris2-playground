-- BHK interpretation

-- conjunction
land_commute : {p, q : Type} -> (p, q) -> (q, p)
land_commute (x, y) = (y, x)

-- disjunction
lor_commute : {p, q : Type} -> Either p q -> Either q p
lor_commute (Left x) = Right x
lor_commute (Right x) = Left x

-- existential quantifier
half_of_eight : DPair Nat (\k => k + k = 8)
half_of_eight = (4 ** Refl)

-- universal quantifier
half_of_even : (n : Nat) -> DPair Nat (\k => k = 1 + n)
half_of_even = \n => (S n ** Refl)

-- negation
four_is_not_five : 4 = 5 -> Void
four_is_not_five Refl impossible

-- uninhabited type
v : Void -> a
v x = absurd x

t : 4 = 5 -> a
t Refl impossible

t' : True = False -> a
t' prf = absurd prf

t'' : True = False -> a
t'' Refl impossible

prf : {p, q, r : Type} -> (p, Either q r) -> Either (p, q) (p, r)
prf (x, (Left y)) = Left (x, y)
prf (x, (Right y)) = Right (x, y)

prf2 : {p, q, r : Type} -> (p -> q -> r) -> (q -> p -> r)
prf2 f x y = f y x
