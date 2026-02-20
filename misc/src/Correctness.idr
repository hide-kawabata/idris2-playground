import Data.Nat
import Data.Vect

%default total

t : (n : Nat) -> LTE n n
t 0 = LTEZero
t (S k) = LTESucc (t k)

max' : Nat -> Nat -> Nat
max' 0 0 = 0
max' 0 (S k) = S k
max' (S k) 0 = S k
max' (S k) (S j) = let kj = max' k j in S kj

spec_max' : {m : _} -> (a, b : Nat) -> max' a b = m -> 
    (Either (a = m) (b = m), LTE a m, LTE b m)
spec_max' 0 0 Refl = (Right Refl, LTEZero, LTEZero)
spec_max' 0 (S b) Refl = -- (Either (0 = S b) (S b = S b), (LTE 0 (S b), LTE (S b) (S b)))
    (Right Refl, LTEZero, t (S b))
spec_max' (S b) 0 Refl = -- (Either (S b = S b) (0 = S b), (LTE (S b) (S b), LTE 0 (S b)))
    (Left Refl, t (S b), LTEZero)
spec_max' (S k) (S j) Refl = 
    let (p, q, r) = spec_max' k j Refl in
    (case p of
          (Left x) => (Left (cong S x), rewrite sym x in t (S k), LTESucc r)
          (Right x) => (Right (cong S x), LTESucc q, rewrite sym x in LTESucc (t j)))

-- [x::ys | ys <- xs]
-- makeList x xss = [x::ys | ys <- xss]
makeLists : a -> Vect n (Vect m a) -> Vect n (Vect (S m) a)
makeLists x [] = []
makeLists x (y :: xs) = [x :: y] ++ makeLists x xs

-- combinations : Int -> List a -> List (List a)
-- combinations 0 _ = [[]]
-- combinations _ [] = []
-- combinations n (x::xs) = [x::ys | ys <- combinations (n-1) xs] ++ combinations n xs

combinations : (x : Nat) -> Vect n a -> LTE x n -> Vect (S n) (Vect x a)
combinations 0 [] LTEZero = [[]]
combinations 0 (x :: xs) LTEZero = [] :: combinations 0 xs LTEZero
combinations (S _) [] LTEZero impossible
combinations (S _) [] (LTESucc x) impossible
combinations (S k) (x :: xs) y = ?hole
-- combinations (S k) (x :: xs) y = makeLists x (combinations k xs ?p) ++ combinations (S k) xs ?p2

-- combinations 0 _ = [[]]
-- combinations _ [] = []
-- combinations n (x::xs) = [x::ys | ys <- combinations (n-1) xs] ++ combinations n xs


-- spec1_combinations_length