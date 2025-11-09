import Data.Vect
import Decidable.Equality

%default total

-- Listing 8.11

exactLength : {m : _} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case decEq m len of -- {m} can be elided
                                 Yes Refl => Just input
                                 No contra => Nothing
