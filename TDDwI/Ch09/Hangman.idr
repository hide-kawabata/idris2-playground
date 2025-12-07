-- 9.2 Expressing program state in types: a guessing game

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

%default total

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
    MkWordState : (word : String) -> (missing : Vect letters Char) ->
        WordState guesses_remaining letters
        -- the relation "guesses_remaining = length (word)" is not kept in this type

data Finished : Type where
    Lost : (game : WordState 0 (S letters)) -> Finished
    Won : (game : WordState (S guesses_remaining) 0) -> Finished

data ValidInput : List Char -> Type where
    Letter : (c : Char) -> ValidInput [c]

isValidNil : ValidInput [] -> Void
isValidNil (Letter c) impossible

isValidTwo : ValidInput (x :: (y :: xs)) -> Void
isValidTwo (Letter c) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No isValidNil
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No isValidTwo

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

-- toUpper' performs the same thing as Data.String.toUpper
-- (overloading is done without declaring any interface????)
toUpper' : String -> String
toUpper' str = let cs = unpack str in
               pack $ map toUpper cs

partial
readGuess : IO (cs ** ValidInput cs)
readGuess = do putStr "Guess:"
               str <- getLine
               case isValidString (toUpper' str) of
                   (Yes prf) => pure (_ ** prf)
                   (No contra) => do putStrLn "Invalid guess"
                                     readGuess

removeElem : {n : _} -> (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} -> Vect n a
removeElem value (value :: xs) {prf = Here} = xs
removeElem value (y :: []) {prf = (There later)} {n = 0} = absurd later
removeElem value (y :: xs) {prf = (There later)} {n = (S k)}
    = y :: removeElem value xs

processGuess : {letters : _} -> (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing)
    = case isElem letter missing of
        (Yes prf) => Right (MkWordState word (removeElem letter missing))
        (No contra) => Left (MkWordState word missing)

partial
game : {guesses : _} -> {letters : _} -> WordState (S guesses) (S letters) -> IO Finished
game st = do
    ([letter] ** Letter letter) <- readGuess
    case (processGuess letter st) of
        (Left l) => do putStrLn "Wrong!"
                       case guesses of
                            0 => pure (Lost l)
                            (S k) => game l
        (Right r) => do putStrLn "Right!"
                        case letters of
                             0 => pure (Won r)
                             (S k) => game r

partial
main : IO ()
main = do result <- game {guesses = 2} (MkWordState "Test" ['T', 'E', 'S'])
          case result of
            (Lost (MkWordState word missing)) =>
                 putStrLn ("You lose. The word was " ++ word)
            (Won game) => putStrLn "You win!"


-- Note that you still can incorrectly define a game. (Cf Sec. 14.3)
funnygame : WordState (S guesses) (S letters) -> IO Finished 
funnygame state = pure (Lost (MkWordState "pqr" ['a']))
