-- Negation

%default total 

NotElim : {a : Type} -> Not a -> a -> Void
NotElim f x = f x

NotNotIntro : {a : Type} -> a -> Not (Not a)
NotNotIntro x f = f x

NotNotNotElim : {a : Type} -> Not (Not (Not a)) -> Not a
NotNotNotElim f x = f (\g => f (\f1 => f (\g1 => f (\f2 => g x)))) -- OK???

NotNotNotElim' : {a : Type} -> Not (Not (Not a)) -> Not a
NotNotNotElim' f x = f (NotNotIntro x)
--NotNotNotElim' f x = f (\y => y x)

contraposition : {a, b : Type} -> (a -> b) -> (Not b -> Not a)
--contraposition f g x = g (f x)
contraposition f g = \x => g (f x)

notEqual : {a : Type} -> a -> a -> Type
notEqual x y = Not (x = y)

notEq12 : notEqual 1 2
--notEq12 Refl impossible
notEq12 a = case a of notEq12 Refl impossible

peano : {m : Nat} -> Not (0 = S m)
peano Refl impossible

-- excluded middle is irrefutable
emIrrefutable : {a : Type} -> Not (Not (Either a (Not a)))
emIrrefutable f = f (Right (\x => f (Left x)))
