import Data.Nat
import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

%default total

-----------------------------------------------------------------
-- Definition of the equality EqualX
-----------------------------------------------------------------

-- Let's treat two pairs of Nats are "the same" if one of their elements are definitionally the same.
-- Note that the proof of EqualX x y is not unique: e.g. EqualX (1, 1) (1, 1)
-- Note that the relation EqualX x y is not transitive.
data EqualX : (Nat, Nat) -> (Nat, Nat) -> Type where
    EQL : EqualX (n, m) (n, m')
    EQR : EqualX (n, m) (n', m)

-- EqualX x y implies that either of elements of the two are definitionally the same.
prop_EqualX_inv : EqualX (p, q) (p', q') -> Either (p = p') (q = q')
prop_EqualX_inv EQL = Left Refl
prop_EqualX_inv EQR = Right Refl

-- Contraposition of the above.
prop_NotEqualX : Not (Either (p = p') (q = q')) -> Not (EqualX (p, q) (p', q'))
prop_NotEqualX prf = \arg => prf (prop_EqualX_inv arg)

-- A dicision procedure for the EqualX relation.
decEqualX : (x, y : (Nat, Nat)) -> Dec (EqualX x y)
decEqualX (p, q) (p', q') =
    case decEq p p' of
        (Yes eq_p) => rewrite eq_p in Yes EQL
        (No ne_p) => 
            case decEq q q' of
                (Yes eq_q) => rewrite eq_q in Yes EQR
                (No ne_q) => 
                    let f = prop_NotEqualX (demorgan (ne_p, ne_q)) in
                    No (\arg => f arg)
    where
        demorgan : (Not tyA, Not tyB) -> Not (Either tyA tyB)
        demorgan (w, v) y = case y of
            (Left t) => w t
            (Right t) => v t

-----------------------------------------------------------------

filterX : 
    (x : (Nat, Nat)) ->
    {len : Nat} -> (l : Vect len (Nat, Nat)) ->
    (n : Nat ** Vect n (Nat, Nat))
filterX x [] = (0 ** [])
filterX x (y :: xs) =
    case decEqualX x y of
        (Yes prf) => filterX x xs
        (No contra) => 
            let (m ** xs') = filterX x xs in
            (S m ** y :: xs')

prepend : {a : Type} -> {n, m : Nat} -> a -> 
    Vect n (Vect m a) -> Vect n (Vect (S m) a)
prepend x [] = []
prepend x (y :: xs) = [x :: y] ++ prepend x xs

combiX : 
    {len : Nat} ->
    (n : Nat) -> (l : Vect len (Nat, Nat)) ->
    DPair Nat (\m => Vect m (Vect n (Nat, Nat)))
    -- (m : Nat ** Vect m (Vect n (Nat, Nat)))
combiX 0 [] = (1 ** [[]])
combiX 0 (x :: xs) = (1 ** [[]])
combiX (S k) [] = (0 ** [])
combiX (S k) (x :: xs) = 
    let (len' ** xs') = filterX x xs in
    let (m1 ** part1) = combiX k xs' in
    let (m2 ** part2) = combiX (S k) xs in
    (plus m1 m2 ** prepend x part1 ++ part2)

------------------------------------------------------------------------

-- SubVect xs ys : Elements of xs appears in ys in the same order.
-- Elementwise equality is checked based on the definitional equality.
-- Note that the proof of SubVect xs ys is not unique: eg. SubVect [3] [3, 3]
data SubVect : Vect len1 a -> Vect len2 a -> Type where
    SVNil : SubVect [] xs
    SVTake : (prf : SubVect xs ys) -> SubVect (x :: xs) (x :: ys)
    SVSkip : (prf : SubVect (x :: xs) ys) -> SubVect (x :: xs) (y :: ys)
    -- SVSkip : (prf : SubVect xs ys) -> SubVect xs (y :: ys)

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

-- Define the relation of ElemX: ElemX x xs means that x is in xs in the sense of EqualX-relation.
data ElemX : a -> Vect len a -> Type where
    HereX : (check2 : EqualX x y) -> ElemX x (y :: ys)
    ThereX : (checkElem : ElemX x ys) -> ElemX x (y :: ys)

Uninhabited (ElemX x []) where
    uninhabited (HereX check2) impossible
    uninhabited (ThereX checkElem) impossible

-- Eliminating the head of xs does not change the relation ElemX x xs.
prop_ElemX_elim : (x, z : ty) -> (ys : Vect len ty) ->
    Not (ElemX x (z :: ys)) -> Not (ElemX x ys)
prop_ElemX_elim _ _ [] _ _ impossible
prop_ElemX_elim x z (y :: xs) f (HereX check2) = f (ThereX (HereX check2))
prop_ElemX_elim x z (y :: xs) f (ThereX checkElem) = f (ThereX (ThereX checkElem))

-- Not (ElemX x xs) implies that x and the head element of xs is not EqualX
prop_ElemX_ne : (x, z : (Nat, Nat)) -> (ys : Vect len (Nat, Nat)) ->
    Not (ElemX x (z :: ys)) -> Not (EqualX x z)
prop_ElemX_ne x z ys f y = f (HereX y)

prop_NotElemX2 : 
    (Not (EqualX x y)) -> (Not (ElemX x ys)) -> Not (ElemX x (y :: ys))
prop_NotElemX2 prfnp prfne = \arg => case arg of
    (HereX check2) => absurd (prfnp check2)
    (ThereX checkElem) => absurd (prfne checkElem)

prop_ElemX_elim_po : (y, w : (Nat, Nat)) -> (ys : Vect len (Nat, Nat)) ->
    (prfElem : ElemX y (w :: ys)) -> (prfNeq : Not (EqualX y w)) -> ElemX y ys
prop_ElemX_elim_po y w [] (HereX check2) prfNeq = absurd (prfNeq check2)
prop_ElemX_elim_po _ _ [] (ThereX _) _ impossible
prop_ElemX_elim_po y w (z :: xs) (HereX check2)  prfNeq = absurd (prfNeq check2)
prop_ElemX_elim_po y w (z :: xs) (ThereX checkElem)  prfNeq = checkElem



------------------------------------------------------------

-- NoDupX xs: each pair of elements takens from xs is not equal in terms of EqualX
data NoDupX : Vect len a -> Type where
    NDXNil : NoDupX []
    NDXCons : {a : Type} ->
        (x : a) -> (l : Vect len1 a) ->
        (prfND : NoDupX l) -> (prfNoElem : Not (ElemX x l)) -> NoDupX (x :: l)

---------------------------------------------------------------

prop_filterX_subvect2 :
    (z : (Nat, Nat)) -> {len, k : Nat} ->
    (ys : Vect k (Nat, Nat)) ->
    (xs : Vect len (Nat, Nat)) ->
    (prfSub : SubVect ys xs) ->
    (f : Not (ElemX z ys)) ->
    SubVect ys (snd (filterX z xs))
prop_filterX_subvect2 z [] xs SVNil f = SVNil
prop_filterX_subvect2 z (x :: xs) (x :: ys) (SVTake prf) f with (decEqualX z x)
  prop_filterX_subvect2 z (x :: xs) (x :: ys) (SVTake prf) f | (Yes y) =
    let ne_zx = prop_ElemX_ne z x xs f in
    absurd (ne_zx y)
  prop_filterX_subvect2 z (x :: xs) (x :: ys) (SVTake prf) f | (No contra) with (filterX z ys) proof eq_fzys
    prop_filterX_subvect2 z (x :: xs) (x :: ys) (SVTake prf) f | (No contra) | ((mm ** vv)) =
        let t = prop_ElemX_elim z x xs f in
        let ih = prop_filterX_subvect2 z xs ys prf t in
        -- eq_fzys : filterX z ys = (mm ** vv)
        -- rewrite snd of eq_fzys into ih's type, then SVTake ih
        -- rewrite (sndEq eq_fzys) in SVTake ih
        -- ih : SubVect xs ((filterX z ys) .snd)
        let ih' = replace {p = \c => SubVect xs ((c) .snd)} eq_fzys ih in
        SVTake ih'
prop_filterX_subvect2 z (x :: xs) (y :: ys) (SVSkip prf) f with (decEqualX z y)
  prop_filterX_subvect2 z (x :: xs) (y :: ys) (SVSkip prf) f | (Yes w) =
    let ih = prop_filterX_subvect2 z (x :: xs) ys prf in
    ih f
  prop_filterX_subvect2 z (x :: xs) (y :: ys) (SVSkip prf) f | (No contra) with (filterX z ys) proof eq_fzys
    prop_filterX_subvect2 z (x :: xs) (y :: ys) (SVSkip prf) f | (No contra) | ((mm ** vv)) =
        let ih = prop_filterX_subvect2 z (x :: xs) ys prf f in
        -- ih : SubVect (x :: xs) ((filterX z ys) .snd)
        let ih' = replace {p = \c => SubVect (x :: xs) ((c) .snd)} eq_fzys ih in
        SVSkip ih'

prop_filterX_sv : {n : Nat} -> (x : (Nat,Nat)) -> (xs : Vect n (Nat,Nat)) ->
    (m : Nat) -> (fxs : Vect m (Nat,Nat)) ->
    filterX x xs = (m ** fxs) -> SubVect fxs xs
prop_filterX_sv x [] 0 [] Refl {n = 0} = SVNil
prop_filterX_sv x (y :: ys) m fxs prf {n = S n'} with (decEqualX x y)
  prop_filterX_sv x (y :: ys) m fxs prf {n = S n'} | (Yes z) = 
    let ih = prop_filterX_sv x ys _ fxs prf in
    prop_SubVect_cons fxs ys {y=y} ih
  prop_filterX_sv x (y :: ys) m fxs prf {n = S n'} | (No contra) with (filterX x ys) proof eq_fys
    prop_filterX_sv x (y :: ys) (S m') (y :: ys') Refl {n = S n'} | (No contra) | (m' ** ys') =
        let ih = prop_filterX_sv x ys m' ys' eq_fys in
        SVTake ih


prop_filterX_noelem : {len: Nat} ->
    (y : (Nat, Nat)) -> (xs : Vect len (Nat, Nat)) -> (xs' : Vect m (Nat, Nat)) ->
    (dp : (m ** xs') = filterX y xs) -> Not (ElemX y xs')
prop_filterX_noelem _ [] [] Refl (HereX check2) impossible
prop_filterX_noelem _ [] [] Refl (ThereX checkElem) impossible
prop_filterX_noelem _ (_ :: _) [] _ (HereX check2) impossible
prop_filterX_noelem _ (_ :: _) [] _ (ThereX checkElem) impossible
prop_filterX_noelem y (z :: xs) (w :: ys) dp x {len = S len'} with (decEqualX y z) proof dec_yz
  prop_filterX_noelem y (z :: xs) (w :: ys) dp x {len = S len'} | (Yes eq_yz) = 
    prop_filterX_noelem y xs (w :: ys) dp x
  prop_filterX_noelem y (z :: xs) (w :: ys) dp x {len = S len'} | (No ne_yz) with (filterX y xs) proof f_yxs
    prop_filterX_noelem y (z :: xs) (z :: v') Refl x {len = S len'} | (No ne_yz) | (m' ** v') = 
        let ih' = prop_filterX_noelem y xs v' (sym f_yxs) in
        ih' (prop_ElemX_elim_po y z v' x ne_yz)

prop_filterX_noelem2X :
    {e1 : (Nat, Nat)} -> (e2 : (Nat, Nat)) ->
    {lx : Nat} -> (xs : Vect lx (Nat, Nat)) -> 
    {ly : Nat} -> (ys : Vect ly (Nat, Nat)) ->
    (dp : (ly ** ys) = filterX e1 xs) -> (prfNE : Not (ElemX e2 xs)) -> Not (ElemX e2 ys)
prop_filterX_noelem2X e2 {lx=0} [] {ly=0} [] Refl prfNE = prfNE
prop_filterX_noelem2X e2 {lx=S lx'} (x :: xs) {ly=0} [] dp prfNE = \arg => absurd arg
prop_filterX_noelem2X e2 {lx=S lx'} (x :: xs) {ly=S ly'} (y :: ys) dp prfNE with (decEqualX e1 x)
  prop_filterX_noelem2X e2 {lx=S lx'} (x :: xs) {ly=S ly'} (y :: ys) dp prfNE | (Yes eq_e1x) = 
    let t = prop_ElemX_elim e2 x xs prfNE in    
    prop_filterX_noelem2X e2 {lx=lx'} xs {ly=S ly'} (y :: ys) dp t
  prop_filterX_noelem2X e2 {lx=S lx'} (x :: xs) {ly=S ly'} (y :: ys) dp prfNE | (No ne_e1x) with (filterX e1 xs) proof eq_fe1xs
    prop_filterX_noelem2X e2 {lx=S lx'} (x :: xs) {ly=S ly'} (x :: ys') Refl prfNE | (No ne_e1x) | (ly' ** ys') =
        let t = prop_ElemX_elim e2 x xs prfNE in
        let u = prop_ElemX_ne e2 x xs prfNE in -- prfNE in
        let ih = prop_filterX_noelem2X e2 {lx=lx'} xs {ly=ly'} ys' (sym eq_fe1xs) t in
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
    (n : Nat) -> {len : Nat} ->
    (l : Vect len (Nat, Nat)) ->
    (v : Vect n (Nat, Nat)) ->
    (prfSV : SubVect v l) -> (prfND : NoDupX v) ->
    {m : Nat} ->
    (l' : Vect m (Vect n (Nat, Nat))) ->
    (prf : (m ** l') = combiX n l) ->
    Elem v l'
combiX_complete 0 [] [] prfSV prfND [[]] Refl = Here
combiX_complete 0 (x :: xs) [] prfSV prfND [[]] Refl = Here
combiX_complete (S k) (x :: xs) (x :: ys) (SVTake prfSub) (NDXCons _ _ prfND prfNoElem) l' prf
    with (filterX x xs) proof f_xxs
  combiX_complete (S k) (x :: xs) (x :: ys) (SVTake prfSub) (NDXCons _ _ prfND prfNoElem) l' prf
     | (mm ** vv) with (combiX k vv) proof f_cmbkvv
    combiX_complete (S k) (x :: xs) (x :: ys) (SVTake prfSub) (NDXCons _ _ prfND prfNoElem) l' prf
         | (mm ** vv) | ((m1 ** part1)) with (combiX (S k) xs)
      combiX_complete (S k) (x :: xs) (x :: ys) (SVTake prfSub) (NDXCons _ _ prfND prfNoElem) (prepend x part1 ++ part2) Refl
             | (mm ** vv) | ((m1 ** part1)) | (m2 ** part2) = 
                let subvect = prop_filterX_subvect2 x ys xs prfSub prfNoElem in
                -- subvect : SubVect ys ((filterX x xs) .snd)
                let subvect' = replace {p = \c => SubVect ys ((c) .snd)} f_xxs subvect in
                let ihElem = combiX_complete k vv ys subvect' prfND part1 (sym f_cmbkvv) in
                let pe = prependElem x part1 ys ihElem in
                elemAppendLeft (prepend x part1) part2 pe
combiX_complete (S k) (x :: xs) (y :: ys) (SVSkip prfSub) prfND l' prf
     with (filterX x xs)
  combiX_complete (S k) (x :: xs) (y :: ys) (SVSkip prfSub) prfND l' prf
     | (mm ** vv) with (combiX k vv)
    combiX_complete (S k) (x :: xs) (y :: ys) (SVSkip prfSub) prfND l' prf
         | (mm ** vv) | (m1 ** part1) with (combiX (S k) xs) proof eq_cmb
      combiX_complete (S k) (x :: xs) (y :: ys) (SVSkip prfSub) prfND (prepend x part1 ++ part2) Refl
             | (mm ** vv) | (m1 ** part1) | (m2 ** part2) =
                let ihElem = combiX_complete (S k) xs (y :: ys) prfSub prfND part2 (sym eq_cmb) in
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
    (n : Nat) -> {len : Nat} ->
    (l : Vect len (Nat, Nat)) ->
    (v : Vect n (Nat, Nat)) ->
    {m : Nat} ->
    (l' : Vect m (Vect n (Nat, Nat))) ->
    (prf : (m ** l') = combiX n l) ->
    (prfElem : Elem v l') ->
    SubVect v l
--            n l  v   l'  prf  prfElem
combiX_sound1 0 [] [] [[]] Refl prfElem = SVNil
combiX_sound1 0 (x :: xs) [] [[]] Refl prfElem = SVNil
combiX_sound1 (S _) [] (_ :: _) [] Refl Here impossible -- l = [], l' = []
combiX_sound1 (S _) [] (_ :: _) [] Refl (There later) impossible -- l = [], l' = []
-- added the following
combiX_sound1 (S k) [] (y :: ys) (z :: zs) prf prfElem = 
    let absurdPrf = cong fst prf in
    absurd absurdPrf
combiX_sound1 (S _) (_ :: _) (_ :: _) [] _ Here impossible
combiX_sound1 (S _) (_ :: _) (_ :: _) [] _ (There later) impossible
combiX_sound1 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} with (filterX x xs) proof eq_fxxs
  combiX_sound1 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) with (combiX k v_fxxs) proof eq_ckvfxxs
    combiX_sound1 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) with (combiX (S k) xs) proof eq_cskxs
      combiX_sound1 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) with (decEq x y)
        combiX_sound1 (S k) l@(y :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (Yes Refl) =
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let ei = prop_Elem_conc_either (prepend y v_ckvfxxs) v_cskxs prfElem' in
            case ei of
                (Left leftPrf) => 
                    let ttt = prependElemInv y k _ ys v_ckvfxxs leftPrf in
                    let ih = combiX_sound1 k (assert_smaller l v_fxxs) ys v_ckvfxxs (sym eq_ckvfxxs) ttt in
                    -- let ih = combiX_sound1 k (assert_smaller (y :: xs) v_fxxs) ys v_ckvfxxs (sym eq_ckvfxxs) ttt in
                    -- let ih = combiX_sound1 k (v_fxxs) ys v_ckvfxxs (sym eq_ckvfxxs) ttt in
                    let fxxs_sv = prop_filterX_sv y xs m_fxxs v_fxxs (eq_fxxs) in
                    let sv = prop_SubVect_transitive ys v_fxxs xs ih fxxs_sv in
                    SVTake sv
                (Right rightPrf) => 
                    let ih = combiX_sound1 (S k) xs (y :: ys) _ (sym eq_cskxs) rightPrf in
                    SVSkip ih
        combiX_sound1 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (No ne_xy) =
            let fact = prependElemNegative y x ys v_ckvfxxs ne_xy in
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let t = prop_Elem_conc_2nd (y :: ys) (prepend x v_ckvfxxs) v_cskxs prfElem' fact in
            let ih = combiX_sound1 (S k) xs (y :: ys) _ (sym eq_cskxs) t in
            SVSkip ih


combiX_sound2_sub2 :
    {n : Nat} -> {len : Nat} -> (l : Vect len (Nat, Nat)) -> (y : (Nat, Nat)) ->
    (v : Vect n (Nat, Nat)) -> {m : Nat} -> (l' : Vect m (Vect n (Nat, Nat))) ->
    (prf : (m ** l') = combiX n l) -> (prfElem : Elem v l') -> (prfNE : Not (ElemX y l)) -> Not (ElemX y v)
--                n  l y  v  l'        prf prfElem prfNE
combiX_sound2_sub2 [] y [] ([] :: []) Refl Here prfNE = prfNE
combiX_sound2_sub2 [] y [] ([] :: []) Refl (There later) prfNE = prfNE
combiX_sound2_sub2 (x :: xs) y [] [[]] Refl prfElem prfNE = \arg => absurd arg
combiX_sound2_sub2 [] _ _ [] Refl Here _ impossible
combiX_sound2_sub2 [] _ _ [] Refl (There later) _ impossible
combiX_sound2_sub2 (_ :: _) _ [] [] _ Here _ impossible
combiX_sound2_sub2 (_ :: _) _ [] [] _ (There _) _ impossible
combiX_sound2_sub2 (_ :: _) _ (_ :: _) [] _ Here _ impossible
combiX_sound2_sub2 (_ :: _) _ (_ :: _) [] _ (There later) _ impossible
combiX_sound2_sub2 _ _ [] (_ :: _ :: _) _ _ _ = absurd
combiX_sound2_sub2 {n=S k} [] _ (_ :: _) (_ :: _) prf _ _ = absurd (cong fst prf)
combiX_sound2_sub2 {n=S k} l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE with (filterX x xs) proof eq_fxxs
  combiX_sound2_sub2 {n=S k} l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) with (combiX k v_fxxs) proof eq_ckvfxxs
    combiX_sound2_sub2 {n=S k} l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) with (combiX (S k) xs) proof eq_cskxs
      combiX_sound2_sub2 {n=S k} l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) with (decEq x y)
        combiX_sound2_sub2 {n=S k} l@(y :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (Yes Refl) =
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let ei = prop_Elem_conc_either (prepend y v_ckvfxxs) v_cskxs prfElem' in
            case ei of
                (Left leftPrf) => 
                    let leftPrf' = prependElemInv y k _ ys v_ckvfxxs leftPrf in
                    let prfNE2 = prop_ElemX_ne v y xs prfNE in
                    let prfNE' = prop_ElemX_elim v y xs prfNE in
                    let t = prop_filterX_noelem2X v xs v_fxxs (sym eq_fxxs) prfNE' in
                    let ih = combiX_sound2_sub2 {n=k} (assert_smaller l v_fxxs) v ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' t in
                    -- let ih = combiX_sound2_sub2 {n=k} v_fxxs v ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' t in
                    let tt = prop_NotElemX2 prfNE2 ih in
                    tt
                (Right rightPrf) =>
                    let prfNE' = prop_ElemX_elim v y xs prfNE in
                    combiX_sound2_sub2 {n=S k} xs v (y :: ys) v_cskxs (sym eq_cskxs) rightPrf prfNE'
        combiX_sound2_sub2 l@(x :: xs) v (y :: ys) (z :: zs) prf prfElem prfNE | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (No ne_xy) =
            let fact = prependElemNegative y x ys v_ckvfxxs ne_xy in
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let t = prop_Elem_conc_2nd (y :: ys) (prepend x v_ckvfxxs) v_cskxs prfElem' fact in
            let prfNE' = prop_ElemX_elim v x xs prfNE in
            combiX_sound2_sub2 {n=S k} xs v (y :: ys) v_cskxs (sym eq_cskxs) t prfNE'


combiX_sound2 :
    (n : Nat) -> {len : Nat} -> (l : Vect len (Nat, Nat)) ->
    (v : Vect n (Nat, Nat)) -> {m : Nat} -> (l' : Vect m (Vect n (Nat, Nat))) ->
    (prf : (m ** l') = combiX n l) -> (prfElem : Elem v l') -> NoDupX v
--            n  l v   l' prf prfElem
combiX_sound2 0 _ [] _ _ _ = NDXNil
combiX_sound2 (S _) [] (_ :: _) [] Refl Here impossible
combiX_sound2 (S _) [] (_ :: _) [] Refl (There later) impossible
combiX_sound2 (S k) [] (y :: ys) (z :: zs) prf prfElem =
    let absurdPrf = cong fst prf in
    absurd absurdPrf
combiX_sound2 (S _) (_ :: _) (_ :: _) [] _ Here impossible
combiX_sound2 (S _) (_ :: _) (_ :: _) [] _ (There later) impossible
combiX_sound2 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} with (filterX x xs) proof eq_fxxs
  combiX_sound2 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) with (combiX k v_fxxs) proof eq_ckvfxxs
    combiX_sound2 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) with (combiX (S k) xs) proof eq_cskxs
      combiX_sound2 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) with (decEq x y)
        combiX_sound2 (S k) l@(y :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (Yes Refl) =
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let ei = prop_Elem_conc_either (prepend y v_ckvfxxs) v_cskxs prfElem' in
            case ei of
                (Left leftPrf) => 
                    let leftPrf' = prependElemInv y k _ ys v_ckvfxxs leftPrf in
                    let ih = combiX_sound2 k (assert_smaller l v_fxxs) ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' in
                    -- let ih = combiX_sound2 k v_fxxs ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' in
                    let tX = prop_filterX_noelem y xs v_fxxs (sym eq_fxxs) in
                    let u2 = combiX_sound2_sub2 v_fxxs y ys v_ckvfxxs (sym eq_ckvfxxs) leftPrf' tX in
                    NDXCons y ys ih (\arg => u2 arg)
                (Right rightPrf) => 
                    let ih = combiX_sound2 (S k) xs (y :: ys) v_cskxs (sym eq_cskxs) rightPrf in
                    ih
        combiX_sound2 (S k) l@(x :: xs) (y :: ys) (z :: zs) prf prfElem {len = S len'} | (m_fxxs ** v_fxxs) | (m_ckvfxxs ** v_ckvfxxs) | (m_cskxs ** v_cskxs) | (No ne_xy) =
            let fact = prependElemNegative y x ys v_ckvfxxs ne_xy in
            let prfElem' = replace {p = \dp => Elem (y :: ys) (snd dp)} prf prfElem in
            let t = prop_Elem_conc_2nd (y :: ys) (prepend x v_ckvfxxs) v_cskxs prfElem' fact in
            let ih = combiX_sound2 (S k) xs (y :: ys) v_cskxs (sym eq_cskxs) t in
            ih
