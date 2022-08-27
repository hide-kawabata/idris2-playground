module VerifiedFunctorWork

%hide Prelude.(<$>)

%default total

infixr 8 <$>

public export
interface VerifiedFunctor (f : Type -> Type) where
  -- our map function.
  (<$>) : (a -> b) -> f a -> f b
  -- what about our laws?
  -- recall map id = id and map (f . g) = map f . map g
  mapIdLaw : (xs : f a) -> (<$>) {b = a} Prelude.id xs = Prelude.id xs -- what is this type? Why Prelude?
  mapComposeLaw : (xs : f a) -> (<$>) {a} (f . g) xs = ((<$>) f . (<$>) g) xs -- the implicits?

public export
implementation VerifiedFunctor List where
  (<$>) f [] = []
  (<$>) f (x :: xs) = f x :: (f <$> xs)
  mapIdLaw [] = Refl
  mapIdLaw (x :: xs) = 
    let rec = mapIdLaw xs 
    in rewrite rec in Refl
  {--
  mapComposeLaw [] = Refl
  mapComposeLaw (x :: xs) = 
    let rec = mapComposeLaw {g = g} xs
    in rewrite rec in Refl
    --}
  mapComposeLaw [] = Refl
  mapComposeLaw (x :: xs) = cong (List (g x) ::) (mapComposeLaw xs)
