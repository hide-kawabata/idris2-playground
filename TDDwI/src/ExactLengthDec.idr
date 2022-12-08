-- Listing 8.11

import Data.Vect
import Decidable.Equality

exactLength : {m : _} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case decEq m len of
                                 Yes Refl => Just input
                                 No contra => Nothing
