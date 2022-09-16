%default total

invS : {n : Nat} -> S n = 0 -> Void
invS Refl impossible

-- less than or equal to
data LTE : Nat -> Nat -> Type where
  LTE0 : {n : Nat} -> LTE 0 n
  LTEn : {n, m : Nat} -> LTE n m -> LTE (S n) (S m)

-- inversion
invLTE : {n, m : Nat} -> LTE (S n) (S m) -> LTE n m
invLTE (LTEn x) = x

invLTE0 : {n : Nat} -> LTE n 0 -> n = 0
invLTE0 LTE0 = Refl

-- reflexivity
lteRefl : (n : Nat) -> LTE n n
lteRefl 0 = LTE0
lteRefl (S k) = LTEn (lteRefl k)

-- transitivity (induction on nat)
lteTrans : (n, m, o : Nat) -> LTE n m -> LTE m o -> LTE n o
lteTrans 0 m o nm mo = LTE0
--lteTrans (S k) 0 o nm mo = rewrite invLTE0 nm in mo
--lteTrans (S k) (S j) 0 nm mo = let mo2 = invLTE0 mo in absurd $ invS mo2
lteTrans (S k) (S j) (S i) nm mo = 
  let nm2 = invLTE nm in
  let mo2 = invLTE mo in
  let t = lteTrans k j i nm2 mo2 in
  LTEn t

-- transitivity (induction on evidence)
lteTrans' : {n, m, o : Nat} -> LTE n m -> LTE m o -> LTE n o
lteTrans' LTE0 mo = LTE0
lteTrans' (LTEn nm') (LTEn mo') = LTEn (lteTrans' nm' mo')

-- anti-symmetry (induction on nat)
lteASym : (n, m : Nat) -> LTE n m -> LTE m n -> n = m
lteASym 0 m nm mn = rewrite invLTE0 mn in Refl
--lteASym (S k) 0 nm mn = let nm2 = invLTE0 nm in absurd $ invS nm2
lteASym (S k) (S j) nm mn = 
  let nm2 = invLTE nm in
  let mn2 = invLTE mn in
  let t = lteASym k j nm2 mn2 in
  cong S t

-- anti-symmetry (induction on evidence)
lteASym' : {n, m : Nat} -> LTE n m -> LTE m n -> n = m
lteASym' LTE0 LTE0 = Refl
lteASym' (LTEn nm) (LTEn mn) = cong S $ lteASym' nm mn

-- totality
totLTE : (n, m : Nat) -> Either (LTE n m) (LTE m n)
totLTE 0 m = Left LTE0
totLTE (S k) 0 = Right LTE0
totLTE (S k) (S j) = -- Either (LTE (S k) (S j)) (LTE (S j) (S k)) 
  case totLTE k j of
    Left kj => Left $ LTEn kj
    Right jk => Right $ LTEn jk

plusZeroRightNeutral : (m : Nat) -> plus m 0 = m
plusZeroRightNeutral 0 = Refl
plusZeroRightNeutral (S k) = rewrite plusZeroRightNeutral k in Refl

plusSuccRightSucc : (l : Nat) -> (r : Nat) -> S (l + r) = l + S r
plusSuccRightSucc 0 r = Refl
plusSuccRightSucc (S k) r = rewrite sym $ plusSuccRightSucc k r in Refl

monoPlus : (m, n : Nat) -> LTE m (plus m n)
monoPlus m 0 = rewrite plusZeroRightNeutral m in lteRefl m
monoPlus 0 (S k) = LTE0
monoPlus (S j) (S k) = LTEn $ monoPlus j (S k)

monoPlus2 : (m, n, o : Nat) -> LTE m n -> LTE m (plus n o)
monoPlus2 0 n o LTE0 = LTE0
monoPlus2 (S n) (S m) o (LTEn mn) = LTEn $ monoPlus2 n m o mn

plusAssoc : (m, n : Nat) -> plus m n = plus n m
plusAssoc 0 n = rewrite plusZeroRightNeutral n in Refl
plusAssoc (S k) n = rewrite sym $ plusSuccRightSucc n k in
                    rewrite plusAssoc n k in Refl

-- monotonicity
monLTE : {m, n, p, q : Nat} -> LTE m n -> LTE p q -> LTE (m + p) (n + q)
monLTE LTE0 pq = -- LTE p (plus n q)
  rewrite plusAssoc n q in
  monoPlus2 p q n pq
monLTE (LTEn mn') pq = LTEn $ monLTE mn' pq


-- even and odd: mutually recursive types
-- (use of "mutual" might be standard in Idris (?))
data Even : Nat -> Type
data Odd : Nat -> Type

data Even : Nat -> Type where
  Ev0 : Even 0
  Evn : {n : Nat} -> Odd n -> Even (S n)

data Odd : Nat -> Type where
  Odn : {n : Nat} -> Even n -> Odd (S n)

evenSS : {n : Nat} -> Even n -> Even (S (S n))
evenSS Ev0 = Evn (Odn Ev0)
evenSS (Evn o) = Evn (Odn (Evn o))

invEv : {n : Nat} -> Even (S n) -> Odd n
invEv (Evn e) = e

invOd : {n : Nat} -> Odd (S n) -> Even n
invOd (Odn o) = o

-- mutually recursive proofs of o_o_e and e_e_e
o_o_e : (m, n : Nat) -> Odd m -> Odd n -> Even (m + n)

e_e_e : (m, n : Nat) -> Even m -> Even n -> Even (m + n)
e_e_e 0 n Ev0 en = en
e_e_e (S m') 0 (Evn om) Ev0 = rewrite plusZeroRightNeutral m' in Evn om
e_e_e (S m') (S n') (Evn om) (Evn on) = -- Even (S (plus m' (S n')))
  rewrite sym $ plusSuccRightSucc m' n' in
  evenSS $
  o_o_e m' n' om on 

o_o_e 0 _ (Odn x) _ impossible
o_o_e (S _) 0 _ (Odn x) impossible
o_o_e (S k) (S j) oSk oSj = 
  let ek = invOd oSk in
  let ej = invOd oSj in
  rewrite sym $ plusSuccRightSucc k j in
  evenSS $
  e_e_e k j ek ej

