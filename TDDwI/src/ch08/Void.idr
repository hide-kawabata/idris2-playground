%default total

-- 8.3.1

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

partial
loop : Void
loop = loop

valueNotSuc : (x : Nat) -> x = S x -> Void
valueNotSuc x Refl impossible

-- 8.3.2

-- valid but not useful definition
checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat num1 num2 = Nothing

