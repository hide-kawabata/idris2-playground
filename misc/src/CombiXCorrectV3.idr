import Data.Nat
import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

%default total

-----------------------------------------------------------------

-- Example definition of pairwise equality.
data EqualX : (a, b) -> (a, b) -> Type where
    EQL : {n, n' : a} -> {m, m' : b} -> (leftEqual : n = n') -> EqualX (n, m) (n', m')
    EQR : {n, n' : a} -> {m, m' : b} -> (rightEqual : m = m') -> EqualX (n, m) (n', m')

-- A dicision procedure for the EqualX relation.
decEqualX : (DecEq a, DecEq b) =>
    (x, y : (a, b)) -> Dec (EqualX x y)
decEqualX (p, q) (p', q') = 
    case decEq p p' of
        (Yes eq_p) => Yes (EQL eq_p)
        (No ne_p) => 
            case decEq q q' of
                 (Yes eq_q) => Yes (EQR eq_q)
                 (No ne_q) => No (\arg => 
                    case arg of
                        (EQL Refl) => ne_p Refl
                        (EQR Refl) => ne_q Refl)

-- Another example
data ConflPresen : (Integer, String, String, String) -> (Integer, String, String, String) -> Type where
    EQ1 : {d, d' : Integer} -> {r, r' : String} -> {pf, pf' : String} -> {pj, pj' : String} ->
          (d, r) = (d', r') -> ConflPresen (d, r, pf, pj) (d', r', pf', pj')
    EQ2 : {d, d' : Integer} -> {r, r' : String} -> {pf, pf' : String} -> {pj, pj' : String} ->
          (r, pf) = (r', pf') -> ConflPresen (d, r, pf, pj) (d', r', pf', pj')
    EQ3 : {d, d' : Integer} -> {r, r' : String} -> {pf, pf' : String} -> {pj, pj' : String} ->
          (pf, pj) = (pf', pj') -> ConflPresen (d, r, pf, pj) (d', r', pf', pj')

decConflPresen :
    (x, y : (Integer, String, String, String)) -> Dec (ConflPresen x y)
decConflPresen x@(d, r, pf, pj) y@(d', r', pf', pj') =
    case decEq (d, r) (d', r') of
        (Yes eq_dr) => Yes (EQ1 eq_dr)
        (No ne_dr) =>
            case decEq (r, pf) (r', pf') of
                (Yes eq_rf) => Yes (EQ2 eq_rf)
                (No ne_rf) => 
                    case decEq (pf, pj) (pf', pj') of
                        (Yes eq_fj) => Yes (EQ3 eq_fj)
                        (No ne_fj) => No (\arg =>
                            case arg of
                                (EQ1 Refl) => ne_dr Refl
                                (EQ2 Refl) => ne_rf Refl
                                (EQ3 Refl) => ne_fj Refl)

-----------------------------------------------------------------

-- Now filterX takes a binary decision procedure for filtering.
-- The decision proceture determines the type of elements.
filterX' :
    {0 ty : Type} ->
    {0 rel : ty -> ty -> Type} ->
    (decide : ((z, y : ty) -> Dec (rel z y))) ->
    (x : ty) ->
    {len : Nat} -> (l : Vect len ty) ->
    (n : Nat ** Vect n ty)
filterX' decide x [] = (0 ** [])
filterX' decide x (y :: xs) =
    case decide x y of
        (Yes prf) => filterX' decide x xs
        (No contra) =>
            let (m ** xs') = filterX' decide x xs in
            (S m ** y :: xs')

test_filterX_1 : filterX' Main.decEqualX (2, 2) [(1, 2), (2, 3), (3, 4), (4, 5)] = (2 ** [(3, 4), (4, 5)])
test_filterX_1 = Refl
test_filterX_2 : filterX' Main.decEqualX (2, 2) [(1, 2), (2, 3), (3, 4), (4, 5)] = (1 ** [(3, 4)]) -> Void
test_filterX_2 Refl impossible

prepend :
    {a : Type} -> {n, m : Nat} -> a -> 
    Vect n (Vect m a) -> Vect n (Vect (S m) a)
prepend x [] = []
prepend x (y :: xs) = [x :: y] ++ prepend x xs

-- Now combiX takes a binary decision procedure for filtering.
-- The decision proceture determines the type of elements.
combiX :
    {ty : Type} ->
    {0 rel : ty -> ty -> Type} ->
    (dec : ((z, y : ty) -> Dec (rel z y))) ->
    {len : Nat} ->
    (n : Nat) -> (l : Vect len ty) ->
    DPair Nat (\m => Vect m (Vect n ty))
combiX decEqX 0 [] = (1 ** [[]])
combiX decEqX 0 (x :: xs) = (1 ** [[]])
combiX decEqX (S k) [] = (0 ** [])
combiX decEqX (S k) (x :: xs) = 
    let (len' ** xs') = filterX' decEqX x xs in
    let (m1 ** part1) = combiX decEqX k xs' in
    let (m2 ** part2) = combiX decEqX (S k) xs in
    (plus m1 m2 ** prepend x part1 ++ part2)

test_combiX_1 : combiX Main.decEqualX 2 (the (Vect _ (Nat, Nat)) [(1, 2), (1, 3), (2, 3), (3, 4), (2, 4)]) =
    (6 ** [[(1, 2), (2, 3)], [(1, 2), (3, 4)], [(1, 2), (2, 4)], [(1, 3), (3, 4)], [(1, 3), (2, 4)], [(2, 3), (3, 4)]])
test_combiX_1 = Refl

data_1 : Vect 10 (Integer, String, String, String)
data_1 = [
            (20260514, "H", "ProfX", "ProjA"),
            (20260521, "H", "ProfX", "ProjA"),
            (20260514, "Q", "ProfX", "ProjA"),
            (20260521, "Q", "ProfX", "ProjA"),
            (20260521, "H", "ProfY", "ProjB"),
            (20260528, "H", "ProfY", "ProjB"),
            (20260521, "Q", "ProfY", "ProjB"),
            (20260528, "Q", "ProfY", "ProjB"),
            (20260521, "H", "ProfZ", "ProjC"),
            (20260521, "Q", "ProfZ", "ProjC")
         ]
test_combiX_2 : combiX Main.decConflPresen 3 Main.data_1 = 
        (16 **
        [[(20260514, ("H", ("ProfX", "ProjA"))), (20260521, ("H", ("ProfY", "ProjB"))), (20260521, ("Q", ("ProfZ", "ProjC")))],
        [(20260514, ("H", ("ProfX", "ProjA"))), (20260528, ("H", ("ProfY", "ProjB"))), (20260521, ("H", ("ProfZ", "ProjC")))],
        [(20260514, ("H", ("ProfX", "ProjA"))), (20260528, ("H", ("ProfY", "ProjB"))), (20260521, ("Q", ("ProfZ", "ProjC")))],
        [(20260514, ("H", ("ProfX", "ProjA"))), (20260521, ("Q", ("ProfY", "ProjB"))), (20260521, ("H", ("ProfZ", "ProjC")))],
        [(20260514, ("H", ("ProfX", "ProjA"))), (20260528, ("Q", ("ProfY", "ProjB"))), (20260521, ("H", ("ProfZ", "ProjC")))],
        [(20260514, ("H", ("ProfX", "ProjA"))), (20260528, ("Q", ("ProfY", "ProjB"))), (20260521, ("Q", ("ProfZ", "ProjC")))],
        [(20260521, ("H", ("ProfX", "ProjA"))), (20260528, ("H", ("ProfY", "ProjB"))), (20260521, ("Q", ("ProfZ", "ProjC")))],
        [(20260521, ("H", ("ProfX", "ProjA"))), (20260528, ("Q", ("ProfY", "ProjB"))), (20260521, ("Q", ("ProfZ", "ProjC")))],
        [(20260514, ("Q", ("ProfX", "ProjA"))), (20260521, ("H", ("ProfY", "ProjB"))), (20260521, ("Q", ("ProfZ", "ProjC")))],
        [(20260514, ("Q", ("ProfX", "ProjA"))), (20260528, ("H", ("ProfY", "ProjB"))), (20260521, ("H", ("ProfZ", "ProjC")))],
        [(20260514, ("Q", ("ProfX", "ProjA"))), (20260528, ("H", ("ProfY", "ProjB"))), (20260521, ("Q", ("ProfZ", "ProjC")))],
        [(20260514, ("Q", ("ProfX", "ProjA"))), (20260521, ("Q", ("ProfY", "ProjB"))), (20260521, ("H", ("ProfZ", "ProjC")))],
        [(20260514, ("Q", ("ProfX", "ProjA"))), (20260528, ("Q", ("ProfY", "ProjB"))), (20260521, ("H", ("ProfZ", "ProjC")))],
        [(20260514, ("Q", ("ProfX", "ProjA"))), (20260528, ("Q", ("ProfY", "ProjB"))), (20260521, ("Q", ("ProfZ", "ProjC")))],
        [(20260521, ("Q", ("ProfX", "ProjA"))), (20260528, ("H", ("ProfY", "ProjB"))), (20260521, ("H", ("ProfZ", "ProjC")))],
        [(20260521, ("Q", ("ProfX", "ProjA"))), (20260528, ("Q", ("ProfY", "ProjB"))), (20260521, ("H", ("ProfZ", "ProjC")))]])
test_combiX_2 = Refl

------------------------------------------------------------------------

-- SubVect xs ys : Elements of xs appears in ys in the same order.
-- Elementwise equality is checked based on the definitional equality.
-- Note that the proof of SubVect xs ys is not unique: eg. SubVect [3] [3, 3]
data SubVect : Vect len1 a -> Vect len2 a -> Type where
    SVNil : SubVect [] xs
    SVTake : (prf : SubVect xs ys) -> SubVect (x :: xs) (x :: ys)
    SVSkip : (prf : SubVect (x :: xs) ys) -> SubVect (x :: xs) (y :: ys)

Uninhabited (SubVect (x::xs) []) where
    uninhabited SVNil impossible
    uninhabited (SVTake _) impossible
    uninhabited (SVSkip _) impossible

-- SubVect is transitive
prop_SubVect_transitive : 
    (xs : Vect lx a) -> (ys : Vect ly a) -> (zs : Vect lz a) -> 
    (prf1 : SubVect xs ys) -> (prf2 : SubVect ys zs) -> SubVect xs zs
prop_SubVect_transitive [] ys zs prf1 prf2 = SVNil
prop_SubVect_transitive (x :: xs) (x :: ys) (x :: zs) (SVTake prf) (SVTake prf2) =
    let ih = prop_SubVect_transitive xs ys zs prf prf2 in
    SVTake ih
prop_SubVect_transitive (x :: xs) (x :: ys) (z :: zs) (SVTake prf) (SVSkip prf2) = 
    let t = SVTake prf {x=x} in
    let ih = prop_SubVect_transitive _ _ _ t prf2 in
    SVSkip ih
prop_SubVect_transitive (x :: xs) (y :: ys) (y :: zs) (SVSkip prf) (SVTake prf2) =
    let ih = prop_SubVect_transitive _ _ _ prf prf2 in
    SVSkip ih
prop_SubVect_transitive (x :: xs) (y :: ys) (z :: zs) (SVSkip prf) (SVSkip prf2) =
    let prf' = SVSkip prf {y=y} in
    let ih = prop_SubVect_transitive _ _ _ prf' prf2 in
    SVSkip ih

-- Adding an element at the head of ys does not affect the relation of SubVect xs ys
prop_SubVect_cons :
    (xs : Vect n1 a) -> (ys : Vect n2 a) ->
    (prfSub : SubVect xs ys) -> SubVect xs (y :: ys)
prop_SubVect_cons [] ys prfSub = SVNil
prop_SubVect_cons (x :: xs) ys prfSub = SVSkip prfSub

----------------------------------------------------------------

-- Now ElemX takes the type of elements and a binary relation explicitly.
-- e.g. ElemX (Nat, Nat) EqualX 
data ElemX : (0 ty : Type) -> (rel : ty -> ty -> Type) -> a -> Vect len a -> Type where
    HereX : (check2 : rel x y) -> ElemX ty rel x (y :: ys)
    ThereX : (checkElem : ElemX ty rel x ys) -> ElemX ty rel x (y :: ys)

test_ElemX_1 : ElemX (Nat, Nat) EqualX (the (Nat, Nat) (2, 3)) [(1, 2), (2, 4)]
test_ElemX_1 = ThereX (HereX (EQL Refl))

Uninhabited (ElemX ty rel x []) where
    uninhabited (HereX check2) impossible
    uninhabited (ThereX checkElem) impossible

-- Eliminating the head of xs does not change the relation ElemX x xs.
prop_ElemX_elim : (x, z : ty) -> (ys : Vect len ty) ->
    {rel : ty -> ty -> Type} ->
    Not (ElemX ty rel x (z :: ys)) -> Not (ElemX ty rel x ys)
prop_ElemX_elim {rel} x z ys f prf = f (ThereX prf)

-- Not (ElemX x xs) implies that x and the head element of xs is not EqualX
prop_ElemX_ne :
    {ty : Type} ->
    {rel : ty -> ty -> Type} ->
    (x, z : ty) -> (ys : Vect len ty) ->
    Not (ElemX ty rel x (z :: ys)) -> Not (rel x z)
prop_ElemX_ne {ty} x z ys f y = f (HereX y)

prop_NotElemX2 : 
    {rel : ty -> ty -> Type} ->
    {x, y : ty} ->
    (Not (rel x y)) -> (Not (ElemX ty rel x ys)) -> Not (ElemX ty rel x (y :: ys))
prop_NotElemX2 {rel} prfnp prfne = \arg => case arg of
    (HereX check2) => absurd (prfnp check2)
    (ThereX checkElem) => absurd (prfne checkElem)

prop_ElemX_elim_po2 :
    {rel : ty -> ty -> Type} ->
    (y, w : ty) -> (ys : Vect len ty) ->
    (prfElem : ElemX ty rel y (w :: ys)) -> (prfNeq : Not (rel y w)) -> ElemX ty rel y ys
prop_ElemX_elim_po2 y w [] (HereX check2) prfNeq = absurd (prfNeq check2)
prop_ElemX_elim_po2 _ _ [] (ThereX _) _ impossible
prop_ElemX_elim_po2 y w (z :: xs) (HereX check2)  prfNeq = absurd (prfNeq check2)
prop_ElemX_elim_po2 y w (z :: xs) (ThereX checkElem)  prfNeq = checkElem

------------------------------------------------------------

-- NoDupX xs: each pair of elements takens from xs is not equal in terms of EqualX
-- Now NoDupX takes the type of elements and a binary relation explicitly.
data NoDupX : (ty : Type) -> (rel : ty -> ty -> Type) -> Vect len a -> Type where
    NDXNil : NoDupX ty rel []
    NDXCons : 
        (x : ty) -> (l : Vect len1 ty) ->
        (prfND : NoDupX ty rel l) -> (prfNoElem : Not (ElemX ty rel x l)) -> NoDupX ty rel (x :: l)

---------------------------------------------------------------

prop_filterX_subvect2 :
    {ty : Type} ->
    {rel : ty -> ty -> Type} ->
    (decide : ((z, y : ty) -> Dec (rel z y))) -> -- decide
    (z : ty) -> {len, k : Nat} ->
    (ys : Vect k ty) ->
    (xs : Vect len ty) ->
    (prfSub : SubVect ys xs) ->
    (f : Not (ElemX ty rel z ys)) ->
    SubVect ys (snd (filterX' decide z xs))
prop_filterX_subvect2 {ty} decEQX z [] xs SVNil f = SVNil
prop_filterX_subvect2 {ty} decEQX z (x :: xs) (x :: ys) (SVTake prf) f with (decEQX z x)
  prop_filterX_subvect2 {ty} decEQX z (x :: xs) (x :: ys) (SVTake prf) f | (Yes y) =
    let ne_zx = prop_ElemX_ne {ty} z x xs f in
    absurd (ne_zx y)
  prop_filterX_subvect2 decEQX z (x :: xs) (x :: ys) (SVTake prf) f | (No contra) with (filterX' decEQX z ys) proof eq_fzys
    prop_filterX_subvect2 decEQX z (x :: xs) (x :: ys) (SVTake prf) f | (No contra) | ((mm ** vv)) =
        let t = prop_ElemX_elim z x xs f in
        let ih = prop_filterX_subvect2 decEQX z xs ys prf t in
        let ih' = replace {p = \c => SubVect xs ((c) .snd)} eq_fzys ih in
        SVTake ih'
prop_filterX_subvect2 decEQX z (x :: xs) (y :: ys) (SVSkip prf) f with (decEQX z y)
  prop_filterX_subvect2 decEQX z (x :: xs) (y :: ys) (SVSkip prf) f | (Yes w) =
    prop_filterX_subvect2 decEQX z (x :: xs) ys prf f
  prop_filterX_subvect2 decEQX z (x :: xs) (y :: ys) (SVSkip prf) f | (No contra) with (filterX' decEQX z ys) proof eq_fzys
    prop_filterX_subvect2 decEQX z (x :: xs) (y :: ys) (SVSkip prf) f | (No contra) | ((mm ** vv)) =
        let ih = prop_filterX_subvect2 decEQX z (x :: xs) ys prf f in
        let ih' = replace {p = \c => SubVect (x :: xs) ((c) .snd)} eq_fzys ih in
        SVSkip ih'

prop_filterX_sv : 
    {ty : Type} ->
    {rel : ty -> ty -> Type} ->
    (decide : ((z, y : ty) -> Dec (rel z y))) -> 
    {n : Nat} -> (x : ty) -> (xs : Vect n ty) ->
    (m : Nat) -> (fxs : Vect m ty) ->
    filterX' decide x xs = (m ** fxs) -> SubVect fxs xs
prop_filterX_sv decEQX x [] 0 [] Refl {n = 0} = SVNil
prop_filterX_sv decEQX x (y :: ys) m fxs prf {n = S n'} with (decEQX x y)
  prop_filterX_sv decEQX x (y :: ys) m fxs prf {n = S n'} | (Yes z) = 
    let ih = prop_filterX_sv decEQX x ys _ fxs prf in
    prop_SubVect_cons fxs ys {y=y} ih
  prop_filterX_sv decEQX x (y :: ys) m fxs prf {n = S n'} | (No contra) with (filterX' decEQX x ys) proof eq_fys
    prop_filterX_sv decEQX x (y :: ys) (S m') (y :: ys') Refl {n = S n'} | (No contra) | (m' ** ys') =
        let ih = prop_filterX_sv decEQX x ys m' ys' eq_fys in
        SVTake ih

prop_filterX_noelem : {len: Nat} ->
    {ty : Type} ->
    {rel : ty -> ty -> Type} ->
    (decide : ((z, y : ty) -> Dec (rel z y))) -> 
    (y : ty) -> (xs : Vect len ty) -> (xs' : Vect m ty) ->
    (dp : (m ** xs') = filterX' decide y xs) -> Not (ElemX ty rel y xs')
prop_filterX_noelem _ _ [] [] Refl (HereX check2) impossible
prop_filterX_noelem _ _ [] [] Refl (ThereX checkElem) impossible
prop_filterX_noelem _ _ (_ :: _) [] _ (HereX check2) impossible
prop_filterX_noelem _ _ (_ :: _) [] _ (ThereX checkElem) impossible
prop_filterX_noelem decEQX y (z :: xs) (w :: ys) dp x {len = S len'} with (decEQX y z) proof dec_yz
  prop_filterX_noelem decEQX y (z :: xs) (w :: ys) dp x {len = S len'} | (Yes eq_yz) = 
    prop_filterX_noelem decEQX y xs (w :: ys) dp x
  prop_filterX_noelem decEQX y (z :: xs) (w :: ys) dp x {len = S len'} | (No ne_yz) with (filterX' decEQX y xs) proof f_yxs
    prop_filterX_noelem decEQX y (z :: xs) (z :: v') Refl x {len = S len'} | (No ne_yz) | (m' ** v') = 
        let ih' = prop_filterX_noelem decEQX y xs v' (sym f_yxs) in
        ih' (prop_ElemX_elim_po2 y z v' x ne_yz)

prop_filterX_noelem2X :
    {ty : Type} ->
    {rel : ty -> ty -> Type} ->
    (decide : ((z, y : ty) -> Dec (rel z y))) -> 
    {e1 : ty} -> (e2 : ty) ->
    {lx : Nat} -> (xs : Vect lx ty) -> 
    {ly : Nat} -> (ys : Vect ly ty) ->
    (dp : (ly ** ys) = filterX' decide e1 xs) -> (prfNE : Not (ElemX ty rel e2 xs)) -> Not (ElemX ty rel e2 ys)
prop_filterX_noelem2X decEQX e2 {lx=0} [] {ly=0} [] Refl prfNE = prfNE
prop_filterX_noelem2X decEQX e2 {lx=S lx'} (x :: xs) {ly=0} [] dp prfNE = \arg => absurd arg
prop_filterX_noelem2X decEQX e2 {lx=S lx'} (x :: xs) {ly=S ly'} (y :: ys) dp prfNE with (decEQX e1 x)
  prop_filterX_noelem2X decEQX e2 {lx=S lx'} (x :: xs) {ly=S ly'} (y :: ys) dp prfNE | (Yes eq_e1x) = 
    let t = prop_ElemX_elim e2 x xs prfNE in    
    prop_filterX_noelem2X decEQX e2 {lx=lx'} xs {ly=S ly'} (y :: ys) dp t
  prop_filterX_noelem2X decEQX e2 {lx=S lx'} (x :: xs) {ly=S ly'} (y :: ys) dp prfNE | (No ne_e1x) with (filterX' decEQX e1 xs) proof eq_fe1xs
    prop_filterX_noelem2X decEQX e2 {lx=S lx'} (x :: xs) {ly=S ly'} (x :: ys') Refl prfNE | (No ne_e1x) | (ly' ** ys') =
        let t = prop_ElemX_elim e2 x xs prfNE in
        let u = prop_ElemX_ne e2 x xs prfNE in -- prfNE in
        let ih = prop_filterX_noelem2X decEQX e2 {lx=lx'} xs {ly=ly'} ys' (sym eq_fe1xs) t in
        prop_NotElemX2 u ih

---------------------------------------------------------------

prependElem : {a : Type} -> (x : a) -> {n, m : Nat} -> (ys : Vect n (Vect m a)) ->
    (v : Vect m a) -> (prf : Elem v ys) -> Elem (x :: v) (prepend x ys)
prependElem x (_ :: _) v Here = Here
prependElem x (_ :: _) v (There later) = There (prependElem x _ v later)

elemAppendLeft : {a : Type} -> {n1, n2, m : Nat} ->
    (l1 : Vect n1 (Vect m a)) -> (l2 : Vect n2 (Vect m a)) -> {v : Vect m a} ->
    (prf : Elem v l1) -> Elem v (l1 ++ l2)
elemAppendLeft (_ :: _) l2 Here = Here
elemAppendLeft (_ :: _) l2 (There later) = There (elemAppendLeft _ l2 later)

elemAppendRight : {a : Type} -> {n1, n2, m : Nat} ->
    (l1 : Vect n1 (Vect m a)) -> (l2 : Vect n2 (Vect m a)) -> {v : Vect m a} ->
    (prf : Elem v l2) -> Elem v (l1 ++ l2)
elemAppendRight [] l2 prf = prf
elemAppendRight (x :: xs) l2 prf = There (elemAppendRight xs l2 prf)


combiX_complete :
    {ty : Type} ->
    {rel : ty -> ty -> Type} ->
    (dec : ((z, y : ty) -> Dec (rel z y))) ->
    (n : Nat) -> {len : Nat} ->
    (l : Vect len ty) ->
    (v : Vect n ty) ->
    (prfSV : SubVect v l) -> (prfND : NoDupX ty rel v) ->
    {m : Nat} ->
    (l' : Vect m (Vect n ty)) ->
    (prf : (m ** l') = combiX dec n l) ->
    Elem v l'
combiX_complete decEqX 0 [] [] prfSV prfND [[]] Refl = Here
combiX_complete decEqX 0 (x :: xs) [] prfSV prfND [[]] Refl = Here
combiX_complete decEqX (S k) l@(x :: xs) (x :: ys) (SVTake prfSub) prfND l' prf with (filterX' decEqX x xs) proof f_xxs
  combiX_complete decEqX (S k) l@(x :: xs) (x :: ys) (SVTake prfSub) prfND l' prf | (mm ** vv) with (combiX decEqX k vv) proof f_cmbkvv
    combiX_complete decEqX (S k) l@(x :: xs) (x :: ys) (SVTake prfSub) prfND l' prf | (mm ** vv) | (m1 ** part1) with (combiX decEqX (S k) xs)
      combiX_complete decEqX (S k) l@(x :: xs) (x :: ys) (SVTake prfSub) (NDXCons x ys prfND prfNoElem) (prepend x part1 ++ part2) Refl | (mm ** vv) | (m1 ** part1) | (m2 ** part2) =
        let subvect = prop_filterX_subvect2 decEqX x ys xs prfSub prfNoElem in
        let subvect' = replace {p = \c => SubVect ys ((c) .snd)} f_xxs subvect in
        let ihElem = combiX_complete decEqX k vv ys subvect' prfND part1 (sym f_cmbkvv) in
        let pe = prependElem x part1 ys ihElem in
        elemAppendLeft (prepend x part1) part2 pe
combiX_complete decEqX (S k) (x :: xs) (y :: ys) (SVSkip prfSub) prfND l' prf
     with (filterX' decEqX x xs)
  combiX_complete decEqX (S k) (x :: xs) (y :: ys) (SVSkip prfSub) prfND l' prf
     | (mm ** vv) with (combiX decEqX k vv)
    combiX_complete decEqX (S k) (x :: xs) (y :: ys) (SVSkip prfSub) prfND l' prf
         | (mm ** vv) | (m1 ** part1) with (combiX decEqX (S k) xs) proof eq_cmb
      combiX_complete decEqX (S k) (x :: xs) (y :: ys) (SVSkip prfSub) prfND (prepend x part1 ++ part2) Refl
             | (mm ** vv) | (m1 ** part1) | (m2 ** part2) =
                let ihElem = combiX_complete decEqX (S k) xs (y :: ys) prfSub prfND part2 (sym eq_cmb) in
                elemAppendRight (prepend x part1) part2 ihElem

prop_Elem_conc_either : {x : a} -> {m1, m2 : Nat} -> 
    (l1 : Vect m1 a) -> (l2 : Vect m2 a) ->
    Elem x (l1 ++ l2) -> Either (Elem x l1) (Elem x l2)
prop_Elem_conc_either [] [] y = Left y
prop_Elem_conc_either [] (z :: xs) y = Right y
prop_Elem_conc_either (x :: xs) [] Here = Left Here
prop_Elem_conc_either (z :: xs) [] (There later) = 
    Left (There 
            (let ih = prop_Elem_conc_either xs [] later in
            let (Left ih') = ih in
            ih'))
prop_Elem_conc_either (x :: xs) (w :: ys) Here = Left Here
prop_Elem_conc_either (z :: xs) (w :: ys) (There later) =
    let ih = prop_Elem_conc_either xs (w :: ys) later in
    case ih of (Left y) => Left (There y); (Right y) => Right y

prependElemNegative : {a : Type} -> (y, x : a) -> {k, len' : Nat} -> 
    (ys : Vect k a) -> (xs : Vect len' (Vect k a)) -> (neprf : Not (x = y)) ->
    Elem (y :: ys) (prepend x xs) -> Void
prependElemNegative _ _ ys [] {len' = 0} neprf z = absurd z
prependElemNegative _ _ ys (ys :: xs) {len' = (S j)} neprf Here = neprf Refl
prependElemNegative _ _ ys (x :: xs) {len' = (S j)} neprf (There later) = 
    let ih = prependElemNegative _ _ ys xs {len' = j} neprf later in ih

-- induction on the length of ys (not v)
prependElemInv : {a : Type} -> (x : a) ->  (len : Nat) -> (n : Nat) ->
    (v : Vect len a) -> (ys : Vect n (Vect len a)) -> 
    (prf : Elem (x :: v) (prepend x ys)) -> Elem v ys
prependElemInv x len (S n) v (v :: ys) Here = Here
prependElemInv x len (S n) v (v' :: ys) (There later) = 
    let ih = prependElemInv x len n v ys later in There ih

prop_Elem_conc_2nd : {a : Type} -> {k, len, len2 : Nat} -> (v : Vect k a) -> 
    (l1 : Vect len (Vect k a)) -> (l2 : Vect len2 (Vect k a)) ->
    Elem v (l1 ++ l2) -> Not (Elem v l1) -> Elem v l2
prop_Elem_conc_2nd v l1 l2 x f = 
    let ei = prop_Elem_conc_either l1 l2 x in
    case ei of (Left y) => absurd (f y); (Right y) => y


combiX_sound1 :
    {ty : Type} ->
    DecEq ty =>
    {rel : ty -> ty -> Type} ->
    (dec : ((z, y : ty) -> Dec (rel z y))) ->
    (n : Nat) -> {len : Nat} ->
    (l : Vect len ty) ->
    (v : Vect n ty) ->
    {m : Nat} ->
    (l' : Vect m (Vect n ty)) ->
    (prf : (m ** l') = combiX dec n l) ->
    (prfElem : Elem v l') ->
    SubVect v l
--            n l  v   l'  prf  prfElem
combiX_sound1 decEqX 0 [] [] [[]] Refl prfElem = SVNil
combiX_sound1 decEqX 0 (x :: xs) [] [[]] Refl prfElem = SVNil
combiX_sound1 decEqX (S _) [] (_ :: _) [] Refl Here impossible -- l = [], l' = []
combiX_sound1 decEqX (S _) [] (_ :: _) [] Refl (There later) impossible -- l = [], l' = []
combiX_sound1 decEqX (S k) [] (y :: ys) (z :: zs) prf prfElem = 
    let absurdPrf = cong fst prf in
    absurd absurdPrf
combiX_sound1 decEqX (S _) (_ :: _) (_ :: _) [] _ Here impossible
combiX_sound1 decEqX (S _) (_ :: _) (_ :: _) [] _ (There later) impossible
combiX_sound1 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} with (filterX' decEqX x xs) proof eq_fxxs
  combiX_sound1 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) with (combiX decEqX k v_fxxs) proof eq_ckvfxxs
    combiX_sound1 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) with (combiX decEqX (S k) xs) proof eq_cskxs
      combiX_sound1 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) with (decEq x y)
        combiX_sound1 decEqX (S k) l@(y :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (Yes Refl) =
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let ei = prop_Elem_conc_either (prepend y v_ckvfxxs) v_cskxs prfElem' in
            case ei of
                (Left leftPrf) => 
                    let ttt = prependElemInv y k _ ys v_ckvfxxs leftPrf in
                    let ih = combiX_sound1 decEqX k (assert_smaller l v_fxxs) ys v_ckvfxxs (sym eq_ckvfxxs) ttt in
                    let fxxs_sv = prop_filterX_sv decEqX y xs m_fxxs v_fxxs (eq_fxxs) in
                    let sv = prop_SubVect_transitive ys v_fxxs xs ih fxxs_sv in
                    SVTake sv
                (Right rightPrf) => 
                    let ih = combiX_sound1 decEqX (S k) xs (y :: ys) _ (sym eq_cskxs) rightPrf in
                    SVSkip ih
        combiX_sound1 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (No ne_xy) =
            let fact = prependElemNegative y x ys v_ckvfxxs ne_xy in
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let t = prop_Elem_conc_2nd (y :: ys) (prepend x v_ckvfxxs) v_cskxs prfElem' fact in
            let ih = combiX_sound1 decEqX (S k) xs (y :: ys) _ (sym eq_cskxs) t in
            SVSkip ih


combiX_sound2_sub2 :
    {ty : Type} ->
    DecEq ty =>
    {rel : ty -> ty -> Type} ->
    (dec : ((z, y : ty) -> Dec (rel z y))) ->
    {n : Nat} -> {len : Nat} -> (l : Vect len ty) -> (y : ty) ->
    (v : Vect n ty) -> {m : Nat} -> (l' : Vect m (Vect n ty)) ->
    (prf : (m ** l') = combiX dec n l) -> (prfElem : Elem v l') -> (prfNE : Not (ElemX ty rel y l)) -> Not (ElemX ty rel y v)
--                n  l y  v  l'        prf prfElem prfNE
combiX_sound2_sub2 decEqX [] y [] ([] :: []) Refl Here prfNE = prfNE
combiX_sound2_sub2 decEqX [] y [] ([] :: []) Refl (There later) prfNE = prfNE
combiX_sound2_sub2 decEqX (x :: xs) y [] [[]] Refl prfElem prfNE = \arg => absurd arg
combiX_sound2_sub2 decEqX [] _ _ [] Refl Here _ impossible
combiX_sound2_sub2 _ [] _ _ [] Refl (There later) _ impossible
combiX_sound2_sub2 _ (_ :: _) _ [] [] _ Here _ impossible
combiX_sound2_sub2 _ (_ :: _) _ [] [] _ (There _) _ impossible
combiX_sound2_sub2 _ (_ :: _) _ (_ :: _) [] _ Here _ impossible
combiX_sound2_sub2 _ (_ :: _) _ (_ :: _) [] _ (There later) _ impossible
combiX_sound2_sub2 _ _ _ [] (_ :: _ :: _) _ _ _ = absurd
combiX_sound2_sub2 decEqX {n=S k} [] _ (_ :: _) (_ :: _) prf _ _ = absurd (cong fst prf)
combiX_sound2_sub2 decEqX {n=S k} l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE with (filterX' decEqX x xs) proof eq_fxxs
  combiX_sound2_sub2 decEqX {n=S k} l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) with (combiX decEqX k v_fxxs) proof eq_ckvfxxs
    combiX_sound2_sub2 decEqX {n=S k} l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) with (combiX decEqX (S k) xs) proof eq_cskxs
      combiX_sound2_sub2 decEqX {n=S k} l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) with (decEq x y)
        combiX_sound2_sub2 decEqX {n=S k} l@(y :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (Yes Refl) =
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let ei = prop_Elem_conc_either (prepend y v_ckvfxxs) v_cskxs prfElem' in
            case ei of
                (Left leftPrf) => 
                    let leftPrf' = prependElemInv y k _ ys v_ckvfxxs leftPrf in
                    let prfNE2 = prop_ElemX_ne v y xs prfNE in
                    let prfNE' = prop_ElemX_elim v y xs prfNE in
                    let t = prop_filterX_noelem2X decEqX v xs v_fxxs (sym eq_fxxs) prfNE' in
                    -- let ih = combiX_sound2_sub2 decEqX {n=k} v_fxxs v ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' t in
                    let ih = combiX_sound2_sub2 decEqX {n=k} (assert_smaller l v_fxxs) v ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' t in
                    prop_NotElemX2 prfNE2 ih
                (Right rightPrf) =>
                    let prfNE' = prop_ElemX_elim v y xs prfNE in
                    combiX_sound2_sub2 decEqX {n=S k} xs v (y :: ys) v_cskxs (sym eq_cskxs) rightPrf prfNE'
        combiX_sound2_sub2 decEqX l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (No ne_xy) =
            let fact = prependElemNegative y x ys v_ckvfxxs ne_xy in
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let t = prop_Elem_conc_2nd (y :: ys) (prepend x v_ckvfxxs) v_cskxs prfElem' fact in
            let prfNE' = prop_ElemX_elim v x xs prfNE in
            combiX_sound2_sub2 decEqX {n=S k} xs v (y :: ys) v_cskxs (sym eq_cskxs) t prfNE'


combiX_sound2 :
    {ty : Type} ->
    DecEq ty =>
    {rel : ty -> ty -> Type} ->
    (dec : ((z, y : ty) -> Dec (rel z y))) ->
    (n : Nat) -> {len : Nat} -> (l : Vect len ty) -> -- (y : ty) ->
    (v : Vect n ty) -> {m : Nat} -> (l' : Vect m (Vect n ty)) ->
    (prf : (m ** l') = combiX dec n l) -> (prfElem : Elem v l') -> NoDupX ty rel v
--         dec n  l v   l' prf prfElem
combiX_sound2 _ 0 [] [] ([] :: []) Refl Here = NDXNil
combiX_sound2 _ 0 [] [] ([] :: []) Refl (There later) = NDXNil
combiX_sound2 _ 0 (y :: ys) [] ([] :: []) Refl Here = NDXNil
combiX_sound2 _ 0 (y :: ys) [] ([] :: []) Refl (There later) = NDXNil
combiX_sound2 _ (S k) [] l' (l' :: xs) prf Here = absurd (cong fst prf)
combiX_sound2 _ (S k) [] l' (y :: xs) prf (There later) = absurd (cong fst prf)
combiX_sound2 _ (S _) (_ :: _) (_ :: _) [] _ Here impossible
combiX_sound2 _ (S _) (_ :: _) (_ :: _) [] _ (There later) impossible
combiX_sound2 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} with (filterX' decEqX x xs) proof eq_fxxs
  combiX_sound2 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) with (combiX decEqX k v_fxxs) proof eq_ckvfxxs
    combiX_sound2 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) with (combiX decEqX (S k) xs) proof eq_cskxs
      combiX_sound2 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) with (decEq x y)
        combiX_sound2 decEqX (S k) l@(y :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (Yes Refl) =
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let ei = prop_Elem_conc_either (prepend y v_ckvfxxs) v_cskxs prfElem' in
            case ei of
                (Left leftPrf) => 
                    let leftPrf' = prependElemInv y k _ ys v_ckvfxxs leftPrf in
                    -- let ih = combiX_sound2 decEqX k v_fxxs ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' in
                    let ih = combiX_sound2 decEqX k (assert_smaller l v_fxxs) ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' in
                    let tX = prop_filterX_noelem decEqX y xs v_fxxs (sym eq_fxxs) in
                    let u2 = combiX_sound2_sub2 decEqX v_fxxs y ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' tX in
                    NDXCons y ys ih (\arg => u2 arg)
                (Right rightPrf) => 
                    combiX_sound2 decEqX (S k) xs (y :: ys) v_cskxs (sym eq_cskxs) rightPrf
        combiX_sound2 decEqX (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (No ne_xy) =
            let fact = prependElemNegative y x ys v_ckvfxxs ne_xy in
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let t = prop_Elem_conc_2nd (y :: ys) (prepend x v_ckvfxxs) v_cskxs prfElem' fact in
            combiX_sound2 decEqX (S k) xs (y :: ys) v_cskxs (sym eq_cskxs) t

