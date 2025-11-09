%default total

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : EqNat k j -> EqNat (S k) (S j)
sameS (Same j) = Same (S j)

-- When k and j are given explicitly -----
-- Following instance definitions are required.
Uninhabited (EqNat 0 (S k)) where -- for (*1)
  uninhabited (EqNat 0 (S k)) impossible
Uninhabited (EqNat (S k) 0) where -- for (*2)
  uninhabited (EqNat (S k) 0) impossible
sameS' : (k : _) -> (j : _) -> EqNat k j -> EqNat (S k) (S j)
-- sameS' k k (Same k) = Same (S k) -- this single line suffices
-- the following 4 lines make up an alternative proof
sameS' 0 0 prf = Same 1
sameS' 0 (S k) prf = absurd prf -- (*1)
sameS' (S k) 0 prf = absurd prf -- (*2)
sameS' (S k) (S j) prf = sameS prf


checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat 0 0 = Just (Same 0)
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                    Nothing => Nothing
                    (Just eq) => Just (sameS eq) -- use a special lemma

checkEqNat' : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat' 0 0 = Just (Same 0)
checkEqNat' 0 (S k) = Nothing
checkEqNat' (S k) 0 = Nothing
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                    Nothing => Nothing
                    (Just (Same k)) => Just (Same (S k)) -- define directly

checkEqNat'' : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat'' 0 0 = Just Refl
checkEqNat'' 0 (S k) = Nothing
checkEqNat'' (S k) 0 = Nothing
checkEqNat'' (S k) (S j) = case checkEqNat'' k j of
                    Nothing => Nothing
                    (Just eq) => Just (cong S eq) -- cong is available for =

checkEqNat3 : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat3 0 0 = Just Refl
checkEqNat3 0 (S k) = Nothing
checkEqNat3 (S k) 0 = Nothing
checkEqNat3 (S k) (S j) = do prf <- checkEqNat3 k j
                             pure (cong S prf)

checkEqNat4 : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat4 0 0 = Just Refl
checkEqNat4 0 (S k) = Nothing
checkEqNat4 (S k) 0 = Nothing
checkEqNat4 (S k) (S j) = case checkEqNat4 k j of
                            Nothing => Nothing
                            (Just Refl) => Just Refl

checkEqNat5 : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat5 0 0 = Just Refl
checkEqNat5 0 (S k) = Nothing
checkEqNat5 (S k) 0 = Nothing
checkEqNat5 (S k) (S j) = case checkEqNat5 k j of
                            Nothing => Nothing
                            (Just (Refl {x=a})) => Just (Refl {x=S a})
