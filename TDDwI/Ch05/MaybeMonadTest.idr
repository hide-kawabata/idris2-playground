%default total

{-
  Defining Maybe' and runMaybe.
-}

data Maybe' : (a : Type) -> Type where
    Just' : (x : a) -> Maybe' a
    Nothing' : {a : _} -> Maybe' a
    BindMaybe' : {a : _} -> Maybe' a -> (a -> Maybe' b) -> Maybe' b
    SeqMaybe' : {b : _} -> Maybe' Unit -> Maybe' b -> Maybe' b
    PureMaybe' : {a : _} -> a -> Maybe' a

-- ini is used only if Nothing occurs
procBind : {a : _} -> Maybe' a -> Maybe' a
procBind (BindMaybe' {a=x} m f) = let m' = procBind {a=x} m in
                              case m' of
                                Just' x => procBind (f x)
                                _ => Nothing'
procBind m = m                                

runMaybe : {a : _} -> a -> Maybe' a -> a
runMaybe {a} ini m = case (procBind m) of
                          (Just' x) => x
                          (PureMaybe' x) => x
                          _ => ini

(>>=) : {a : _} -> Maybe' a -> (a -> Maybe' b) -> Maybe' b
(>>=) = BindMaybe'
(>>) : {b : _} -> Maybe' Unit -> Maybe' b -> Maybe' b
(>>) = SeqMaybe'
pure : {a : _} -> a -> Maybe' a
pure = PureMaybe'

test : Maybe' Nat
test = do x <- Just' 3
          y <- Just' "a"
          z <- Just' 5
          -- _ <- Nothing' {a=Unit}
          -- Nothing' -- this is accepted because Seq lets the checker infer that a=Unit
          -- Nothing' {a=Unit}
          w <- Just' 9
          _ <- pure (x + z)
          -- pure (x + z) -- this is not allowed because the action's result type is not Unit
          pure z

test2 : Maybe' Nat
-- test2 = Just' 4
-- test2 = Just' 4 >>= (\x => pure x)
-- test2 = Just' 4 >>= (\_ => Nothing' >>= (\x => pure x))
test2 = Just' 4 >>= (\_ => Nothing' {a=Unit} >>= (\y => Just' 9 >>= (\x => pure x)))
-- test2 = Just' 4 >>= (\x => Just' 8 >>= (\y => pure $ x + y))


data State' : (sTy : Type) -> Type -> Type where
    Get' : State' sTy sTy
    Put' : sTy -> State' sTy Unit
    BindState' : State' sTy a -> (a -> State' sTy b) -> State' sTy b
    PureState' : (x : a) -> State' sTy a

runState' : (ini : sTy) -> State' sTy ty -> (sTy, ty)
runState' ini Get' = (ini, ini)
runState' ini (Put' news) = (news, ())
runState' ini (BindState' m f) = let (s', a') = runState' ini m in
                                    runState' s' (f a')
runState' ini (PureState' x) = (ini, x)

