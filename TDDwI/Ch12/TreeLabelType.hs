{-# LANGUAGE GADTs #-}
module TreeLabelType where

-- Define State ty as a GADT
data State stateType b where
    Get :: State stateType stateType
    Put :: stateType -> State stateType ()
    Pure :: ty -> State stateType ty
    Bind :: State stateType a -> (a -> State stateType b) -> State stateType b

-- Define runState
runState :: State stateType a -> stateType -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) st = ((), newState)
runState (Pure x) st = (x, st)
runState (Bind cmd prog) st = let (val, nextState) = runState cmd st in
                                  runState (prog val) nextState

get :: State stateType stateType
get = Get

put :: stateType -> State stateType ()
put = Put

-- Make State ty an instance of Functor
instance Functor (State stateType) where
        fmap func x = Bind x (\val -> Pure (func val))

-- Make State ty an instance of Applicative
instance Applicative (State stateType) where
        pure = Pure
        (<*>) f a = Bind f $ \f' ->
                    Bind a $ \a' ->
                    Pure (f' a')

-- Make State ty an instance of Monad
instance Monad (State stateType) where
        (>>=) = Bind

-- Make State ty an instance of MonadFail
instance MonadFail (State stateType) where
        fail _ = pure undefined


{-
    Example : apply Monad to Tree
-}
data Tree a = Empty
            | Node (Tree a) a (Tree a)
            deriving Show

testTree :: Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten :: Tree a -> [a]
flatten Empty = []
flatten (Node left val right) = flatten left ++ val : flatten right

-- treeLabelWith, treeLabelWith', and treeLabelWith2 are all equivalent
treeLabelWith :: Tree a -> State [labelType] (Tree (labelType, a))
treeLabelWith Empty = Pure Empty
treeLabelWith (Node left val right)
    = do left_labelled <- treeLabelWith left
         (this : rest) <- get -- get the current state (MonadFail required in Haskell)
         put rest -- set the state as current
         right_labelled <- treeLabelWith right
         pure (Node left_labelled (this, val) right_labelled)

treeLabelWith' :: Tree a -> State [labelType] (Tree (labelType, a))
treeLabelWith' Empty = Pure Empty
treeLabelWith' (Node left val right)
    = treeLabelWith' left >>= \left_labelled ->
      get >>= \(this : rest) -> -- MonadFail required in Haskell
      put rest >>= \_ ->
      treeLabelWith' right >>= \right_labelled ->
      pure (Node left_labelled (this, val) right_labelled)

treeLabelWith2 :: Tree a -> State [labelType] (Tree (labelType, a))
treeLabelWith2 Empty = Pure Empty
treeLabelWith2 (Node left val right)
    = Bind (treeLabelWith2 left) $ \left_labelled ->
      Bind Get $ \(this : rest) -> -- MonadFail required in Haskell
      Bind (Put rest) $ \_ ->
      Bind (treeLabelWith2 right) $ \right_labelled ->
      Pure (Node left_labelled (this, val) right_labelled)

test :: Tree (Integer, String)
test = fst $ runState (treeLabelWith testTree) [1..]
test' :: Tree (Integer, String)
test' = fst $ runState (treeLabelWith' testTree) [1..]
test2 :: Tree (Integer, String)
test2 = fst $ runState (treeLabelWith2 testTree) [1..]


{-
    Example : examine the behavior of testGet
-}
testGet :: State Integer String
testGet = do x <- get
             put $ x + 1 -- change state
             pure "OK" -- change result
testGet' :: State Integer String
testGet' = 
    Bind Get $ \x ->
    Bind (Put $ x + 1) $ \_ ->
    Pure "OK"
runGet' :: (String, Integer)
runGet' -- following RHSs are all equivalent
    -- = runState testGet' 3
    -- = runState (Bind Get $ \x -> Bind (Put $ x + 1) $ \_ -> Pure "OK") 3
    -- = let (val, nextState) = runState Get 3 in
    --     runState ((\x -> Bind (Put $ x + 1) $ \_ -> Pure "OK") val) nextState
    -- = let (val, nextState) = runState Get 3 in
    --     runState (Bind (Put $ val + 1) $ \_ -> Pure "OK") nextState
    -- = let (val, nextState) = runState Get 3 in
    --   let (val', nextState') = runState (Put $ val + 1) nextState in
    --     -- runState ((\_ -> Pure "OK") val') nextState' -- NG in Idris. Why?
    --     runState (Pure "OK") nextState'
    = let (val, nextState) = (3, 3) in
      let (val', nextState') = ((), val + 1) in
        ("OK", nextState')
