{-
  On induction.
  Some materials are taken from idris2.readthedocs.io.
-}

-- a function that captures inductive definitions for Nat
nat_induction :
  (prop : Nat -> Type) ->
  (prop Z) ->
  ((k : Nat) -> prop k -> prop (S k)) ->
  (x : Nat) -> 
  prop x
nat_induction prop p_Z p_S Z = p_Z
nat_induction prop p_Z p_S (S k) = p_S k (nat_induction prop p_Z p_S k)

-- a definition of plus with nat_induction
plus_ind : Nat -> Nat -> Nat
plus_ind n m =
  nat_induction (\x => Nat) -- prop
                m -- prop Z, i.e., the value of plus_ind Z m
                (\k, k_rec => S k_rec) -- ind step; plus_ind (S k) m 
                                       -- where k_rec = plus_ind k m
                n -- prop n; argument for the prop (induction on n)

-- a definition of less-than-or-equal-to
le_ind : Nat -> Nat -> Bool
le_ind n m = -- induction on m
  nat_induction (\x => Bool) -- prop, result type
    (case n of
       0 => True
       S _ => False) -- prop Z, i.e., the value of le_ind (S k) 0
    (\k, k_rec => if k_rec then True
                  else if n == S k then True else False)
                                -- ind step of Nat -> Nat -> Bool
    m -- argument for prop

-- another definition of less-than-or-equal-to
le_ind' : Nat -> Nat -> Bool
le_ind' n m = -- induction on n
  nat_induction (\x => Bool)
    True -- case n = 0
    (\k, k_rec => if not k_rec then False
                  else if k == m then False else True)
    n

-- ordinary definition of less-than-or-equal-to
le0 : Nat -> Nat -> Bool
le0 0 m = True
le0 (S k) 0 = False
le0 (S k) (S m) = le0 k m



-- lemmas used for proving plus_commute{, ', ''}
m_plus_m_Z : (m : Nat) -> m = plus m Z
m_plus_m_Z 0 = Refl
m_plus_m_Z (S k) = cong S $ m_plus_m_Z k

S_plus_m_k : (m : Nat) -> (k : Nat) -> S (plus m k) = plus m (S k)
S_plus_m_k 0 k = Refl
S_plus_m_k (S j) k = rewrite S_plus_m_k j k in Refl

-- proving properties
plus_commute : (x, m : Nat) -> plus_ind x m = plus_ind m x -- ???
-- Are there any unfolding facility in Idris?

-- plus_commute ver1
plus_commute' : (x, m : Nat) -> plus x m = plus m x
plus_commute' 0 m = m_plus_m_Z m
plus_commute' (S k) m =
  rewrite plus_commute' k m in 
  rewrite S_plus_m_k m k in
  Refl

-- plus_commute ver2
plus_commute'' : (x, m : Nat) -> plus x m = plus m x
plus_commute'' x m = -- induction on x
  nat_induction (\x => plus x m = plus m x)
    (m_plus_m_Z m) -- base : x = 0
    (\k, k_rec => -- ind step : x = k
      rewrite k_rec in -- plus k m = plus m k
      rewrite S_plus_m_k m k in
      Refl)
    x
