
import Data.Vect

data Vec : Nat -> Type -> Type where
    VNil : {t : Type} -> Vec 0 t
    VCons : {t : Type} -> {n : Nat} -> (e : t) -> (l : Vec n t) -> Vec (S n) t

data Vec' : (n : Nat) -> (t : Type) -> Type where
    VNil' : Vec' 0 t
    VCons' : (e : t) -> (l : Vec' n t) -> Vec' (S n) t

x'0 : Vec' 0 Nat
x'0 = VNil'
x'1 : Vec' 1 Nat
x'1 = VCons' 100 VNil'

x0 : Vec 0 Nat
x0 = VNil {t=Nat}

b0 : Vec 0 Bool
b0 = VNil {t=Bool}

x1 : Vec 1 Nat
x1 = VCons 300 VNil

x : Vec 3 Nat
x = VCons 100 (VCons 200 (VCons 300 VNil))

l0, l1, l2 : List Nat
l0 = [] {a=Nat}
l1 = [1, 3, 4, 5]
l2 = [1, 2]

bb : List Bool
bb = [] {a=Bool}

a0, a1 : Vect 3 Nat
a0 = [1, 2, 3]
a1 = [1, 1, 1]

Even : Nat -> Type
Even n = DPair Nat (\k => k + k = n) -- ∃k. k+k=n
even4 : Even 4
even4 = (2 ** Refl)
even100 : Even 100
even100 = (50 ** Refl)
