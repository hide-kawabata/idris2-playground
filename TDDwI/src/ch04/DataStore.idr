module Main

import Data.Vect
import Data.String {- span -}
import System.REPL {- repl, replWith -}

data DataStore : Type where
    MkData : (size : Nat) ->
             (items : Vect size String) ->
             DataStore

data Command = Add String
             | Get Integer
             | Quit

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (item :: items) = item :: addToData items

parseCommand : String -> String -> Maybe Command
parseCommand "add" str1 = Just (Add str1)
parseCommand "get" val = case all isDigit (unpack val) of
                            False => Nothing
                            True => Just (Get (cast val))
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

sumInputs : Integer -> String -> Maybe (String, Integer)
sumInputs i str = 
  let n = cast str in 
  if n >= 0 then 
    let n' = n + i in Just ("Subtotal: " ++ (show n'), n')
  else Nothing

getEntry : (store : DataStore) -> (pos : Integer) ->
           Maybe (String, DataStore)
getEntry store pos = let store_items = items store in 
                          case integerToFin pos (size store) of
                            Nothing => Just ("Out of range\n", store)
                            (Just id) => Just (index id store_items ++ "\n", store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse inp of
  Nothing => Just ("Invalid command\n", store)
  (Just (Add item)) => 
    Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
  (Just (Get pos)) => getEntry store pos
  (Just Quit) => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput