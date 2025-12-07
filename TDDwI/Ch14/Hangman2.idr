-- 14.3 Modification of Hangman designed in 9.2

import Data.Vect.Elem
import Data.Vect
import Data.List -- for nub
import Decidable.Equality

%default total

data GameState : Type where
    NotRunning : GameState
    Running : (guesses : Nat) -> (letters : Nat) -> GameState

getletters : String -> List Char
getletters str = nub (map toUpper (unpack str))

data GuessResult = Correct | Incorrect

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    NewGame : (word : String) ->
                GameCmd Unit NotRunning (const (Running 6 (length (getletters word))))
    Won : GameCmd Unit (Running (S guesses) 0) (const NotRunning)
    Lost : GameCmd Unit (Running 0 (S letters)) (const NotRunning)
    Guess : (c : Char) ->
        GameCmd GuessResult 
            (Running (S guesses) (S letters))
            (\res => case res of
                        Correct => Running (S guesses) letters
                        Incorrect => Running guesses (S letters))
    ShowState : GameCmd Unit state (const state)
    Message : String -> GameCmd Unit state (const state)
    ReadGuess : GameCmd Char state (const state)
    Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
    Bind : GameCmd a state1 state2_fn ->
            ((res : a) -> GameCmd b (state2_fn res) state3_fn) ->
            GameCmd b state1 state3_fn

namespace GameCmd
    export
    (>>=) : GameCmd a state1 state2_fn ->
            ((res : a) -> GameCmd b (state2_fn res) state3_fn) ->
            GameCmd b state1 state3_fn
    (>>=) = Bind


namespace Loop
    public export
    data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
        Bind : GameCmd a state1 state2_fn ->
                ((res: a) -> Inf (GameLoop b (state2_fn res) state3_fn)) ->
                GameLoop b state1 state3_fn
        Exit : GameLoop Unit NotRunning (const NotRunning)
    export
    (>>=) : GameCmd a state1 state2_fn ->
            ((res: a) -> Inf (GameLoop b (state2_fn res) state3_fn)) ->
            GameLoop b state1 state3_fn
    (>>=) = Bind

-- 14.3.3 Implementing the game

gameLoop : {guesses, letters : _} -> GameLoop Unit (Running (S guesses) (S letters)) (const NotRunning)
gameLoop = do
    _ <- ShowState
    g <- ReadGuess
    ok <- Guess g
    case ok of
        Correct => case letters of
                        0 => do _ <- Won
                                _ <- ShowState
                                Exit
                        (S k) => do _ <- Message "Correct"
                                    gameLoop
        Incorrect => case guesses of
                        0 => do _ <- Lost
                                _ <- ShowState
                                Exit
                        (S k) => do _ <- Message "Correct"
                                    gameLoop

hangman : GameLoop Unit NotRunning (const NotRunning)
hangman = do _ <- NewGame "testing"
             gameLoop

-- 14.3.4 Defining a concrete game state

data Game : GameState -> Type where
    GameStart : Game NotRunning
    GameWon : (word : String) -> Game NotRunning
    GameLost : (word : String) -> Game NotRunning
    InProgress : (word : String) -> (guesses : Nat) ->
                (missing : Vect letters Char) ->
                Game (Running guesses letters)

Show (Game g) where
    show GameStart = "Starting"
    show (GameWon word) = "Game won: word was " ++ word
    show (GameLost word) = "Game lost: word was " ++ word
    show (InProgress word guesses missing)
         = "\n" ++ pack (map hideMissing (unpack word))
                ++ "\n" ++ show guesses ++ " guesses left"
        where hideMissing : Char -> Char
              hideMissing c = if c `elem` missing then '-' else c

data Fuel = Dry | More (Lazy Fuel)

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
    OK : (res : ty) -> Game (outstate_fn res) ->
            GameResult ty outstate_fn
    OutOfFuel : GameResult ty outstate_fn

-- 14.3.5 Running the game: executing GameLoop

ok : (res : ty) -> Game (outstate_fn res) ->
    IO (GameResult ty outstate_fn)
ok res st = pure (OK res st)

removeElem : (value : a) -> (xs : Vect (S n) a) ->
            {auto prf : Elem value xs} ->
            Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem value (x :: []) {prf = (There later)} = absurd later
removeElem value (x :: (y :: ys)) {prf = (There later)} = x :: removeElem value (y :: ys)

runCmd : Fuel -> Game instate -> GameCmd ty instate outstate_fn ->
            IO (GameResult ty outstate_fn)
runCmd (More fuel) state (NewGame word)
  = ok () (InProgress (pack $ map toUpper $ unpack $ word)
           _ (fromList (getletters word)))
runCmd (More fuel) (InProgress word _ missing) Won = ok () (GameWon word)
runCmd (More fuel) (InProgress word _ missing) Lost = ok () (GameLost word)
runCmd (More fuel) (InProgress word _ missing) (Guess c)
  = case isElem c missing of
      Yes prf => ok Correct (InProgress word _ (removeElem c missing))
      No contra => ok Incorrect (InProgress word _ missing)
runCmd (More fuel) state ShowState = do printLn state
                                        ok () state
runCmd (More fuel) state (Message str) = do putStrLn str
                                            ok () state
runCmd (More fuel) st ReadGuess = do
    putStr "Guess: "
    input <- getLine
    case unpack input of
        [x] => if isAlpha x 
                then ok (toUpper x) st
                else do putStrLn "Invalid input"
                        runCmd fuel st ReadGuess
        _ => do putStrLn "Invalid input"
                runCmd fuel st ReadGuess
runCmd (More fuel) state (Pure res) = ok res state
runCmd (More fuel) st (Bind cmd next)
  = do OK cmdRes newSt <- runCmd fuel st cmd
        | OutOfFuel => pure OutOfFuel
       runCmd fuel newSt (next cmdRes)
runCmd Dry _ _ = pure OutOfFuel

run : Fuel -> Game instate -> GameLoop ty instate outstate_fn ->
        IO (GameResult ty outstate_fn)
run Dry _ _ = pure OutOfFuel
run (More fuel) st (Bind cmd next)
  = do OK cmdRes newSt <- runCmd fuel st cmd
       | OutOfFuel => pure OutOfFuel
       run fuel newSt (next cmdRes)
run (More fuel) st Exit = ok () st

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do _ <- run forever GameStart hangman
          pure ()
