import Data.Vect

append : {n,m : _} -> Vect n elm -> Vect m elm -> Vect (n + m) elm
append [] ys = ys
append (x :: xs) ys = x :: (append xs ys)

append'_xs : {len, m : _} ->
             Vect (S (plus m len)) elm -> Vect (plus m (S len)) elm
append'_xs zs =
  let prf = sym $ plusSuccRightSucc m len in
  rewrite prf in
  zs

append' : {n,m : _} -> Vect n elm -> Vect m elm -> Vect (m + n) elm
append' [] ys =
  let prf = plusZeroRightNeutral m in
  rewrite prf in
  ys
append' (x :: xs) ys = append'_xs (x :: append' xs ys)

myReverse_prf : {len : _} -> Vect (plus len 1) a -> Vect (S len) a
myReverse_prf ys = 
  rewrite plusCommutative 1 len in
  ys

myReverse : {n : _} -> Vect n a -> Vect n a
myReverse [] = []
myReverse (x :: xs) = myReverse_prf $ append xs [x]
