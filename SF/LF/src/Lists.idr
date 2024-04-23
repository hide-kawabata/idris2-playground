module Lists
{-
  Lists
  Workking with Structured Data
-}

import Induction
%default total

-- Pairs of Numbers

data NatProd : Type where
  Pair : (n1 : Nat) -> (n2 : Nat) -> NatProd

fst : (p : NatProd) -> Nat
fst (Pair n1 n2) = n1

snd : (p : NatProd) -> Nat
snd (Pair n1 n2) = n2

swap_pair : (p : NatProd) -> NatProd
swap_pair (Pair n1 n2) = Pair n2 n1

surjective_paring' : (n : Nat) -> (m : Nat) ->
  Pair n m = Pair (fst (Pair n m)) (snd (Pair n m))
surjective_paring' n m = Refl

surjective_paring : (p : NatProd) -> p = Pair (fst p) (snd p)
surjective_paring (Pair n1 n2) = Refl

-- exercise
snd_fst_is_swap : (p : NatProd) -> Pair (snd p) (fst p) = swap_pair p
snd_fst_is_swap (Pair n1 n2) = Refl
fst_swap_is_snd : (p : NatProd) -> fst (swap_pair p) = snd p
fst_swap_is_snd (Pair n1 n2) = Refl

-- Lists of Numbers

data NatList : Type where
  Nil : NatList
  Cons : (n : Nat) -> (l : NatList) -> NatList

repeat : (n : Nat) -> (count : Nat) -> NatList
repeat n 0 = Nil
repeat n (S count') = Cons n (repeat n count')

length : (l : NatList) -> Nat
length Nil = 0
length (Cons h t) = S (length t)

app : (l1 : NatList) -> (l2 : NatList) -> NatList
app Nil l2 = l2
app (Cons h t) l2 = Cons h (app t l2)

hd : (dflt : Nat) -> (l : NatList) -> Nat
hd dflt Nil = dflt
hd dflt (Cons h t) = h

tl : (l : NatList) -> NatList
tl Nil = Nil
tl (Cons h t) = t

test_hd1 : hd 0 (Cons 1 (Cons 2 (Cons 3 Nil))) = 1
test_hd1 = Refl
test_hd2 : hd 0 Nil = 0
test_hd2 = Refl
test_tl : tl (Cons 1 (Cons 2 (Cons 3 Nil))) = (Cons 2 (Cons 3 Nil))
test_tl = Refl

-- exercise
nonzeros : (l : NatList) -> NatList
nonzeros Nil = Nil
nonzeros (Cons 0 l) = nonzeros l
nonzeros (Cons n@(S _) l) = Cons n (nonzeros l)
test_nonzeros : nonzeros (Cons 0 (Cons 1 (Cons 0 (Cons 2 (Cons 3 (Cons 0 (Cons 0 Nil))))))) = (Cons 1 (Cons 2 (Cons 3 Nil)))
test_nonzeros = Refl

oddmembers : (l : NatList) -> NatList
oddmembers Nil = Nil
oddmembers (Cons n l) = case (odd n) of
  False => oddmembers l
  True => (Cons n (oddmembers l))
test_oddmembers : oddmembers (Cons 0 (Cons 1 (Cons 0 (Cons 2 (Cons 3 (Cons 0 (Cons 0 Nil))))))) = (Cons 1 (Cons 3 Nil))
test_oddmembers = Refl

countoddmembers : (l : NatList) -> Nat
countoddmembers l = length (oddmembers l)
test_countoddmembers1 : countoddmembers (Cons 1 (Cons 0 (Cons 3 (Cons 1 (Cons 4 (Cons 5 Nil)))))) = 4
test_countoddmembers1 = Refl
test_countoddmembers2 : countoddmembers (Cons 0 (Cons 2 (Cons 4 Nil))) = 0
test_countoddmembers2 = Refl
test_countoddmembers3 : countoddmembers Nil = 0
test_countoddmembers3 = Refl

-- Bags via Lists

Bag : Type
Bag = NatList

count : (v : Nat) -> (s : Bag) -> Nat
count v Nil = 0
count v (Cons n l) = case (v == n) of
  True => 1 + count v l
  False => count v l
test_count1 : count 1 (Cons 1 (Cons 2 (Cons 3 (Cons 1 (Cons 4 (Cons 1 Nil)))))) = 3
test_count1 = Refl
test_count2 : count 6 (Cons 1 (Cons 2 (Cons 3 (Cons 1 (Cons 4 (Cons 1 Nil)))))) = 0
test_count2 = Refl

sum : Bag -> Bag -> Bag
sum b1 b2 = app b1 b2
test_sum1 : count 1 (sum (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 1 (Cons 4 (Cons 1 Nil)))) = 3
test_sum1 = Refl
add : (v : Nat) -> (s : Bag) -> Bag
add v s = (Cons v s)
test_add1 : count 1 (add 1 (Cons 1 (Cons 4 (Cons 1 Nil)))) = 3
test_add1 = Refl
test_add2 : count 5 (add 1 (Cons 1 (Cons 4 (Cons 1 Nil)))) = 0
test_add2 = Refl
member : (v : Nat) -> (s : Bag) -> Bool
member v Nil = False
member v (Cons n l) = case (v == n) of
  True => True
  False => member v l
test_member1 : member 1 (Cons 1 (Cons 4 (Cons 1 Nil))) = True
test_member1 = Refl
test_member2 : member 2 (Cons 1 (Cons 4 (Cons 1 Nil))) = False
test_member2 = Refl

-- exercise
remove_one : (v : Nat) -> (s : Bag) -> Bag
remove_one v Nil = Nil
remove_one v (Cons n l) = case (v == n) of
  True => l
  False => (Cons n (remove_one v l))
test_remove_one1 : count 5 (remove_one 5 (Cons 2 (Cons 1 (Cons 5 (Cons 4 (Cons 1 Nil)))))) = 0
test_remove_one1 = Refl
test_remove_one2 : count 5 (remove_one 5 (Cons 2 (Cons 1 (Cons 4 (Cons 1 Nil))))) = 0
test_remove_one2 = Refl
test_remove_one3 : count 4 (remove_one 5 (Cons 2 (Cons 1 (Cons 4 (Cons 5 (Cons 1 (Cons 4 Nil))))))) = 2
test_remove_one3 = Refl
test_remove_one4 : count 5 (remove_one 5 (Cons 2 (Cons 1 (Cons 5 (Cons 4 (Cons 5 (Cons 1 (Cons 4 Nil)))))))) = 1
test_remove_one4 = Refl

remove_all : (v : Nat) -> (s : Bag) -> Bag
remove_all v Nil = Nil
remove_all v (Cons n l) = case (v == n) of
  True => remove_all v l
  False => (Cons n (remove_all v l))
test_remove_all1 : count 5 (remove_all 5 (Cons 2 (Cons 1 (Cons 5 (Cons 4 (Cons 1 Nil)))))) = 0
test_remove_all1 = Refl
test_remove_all2 : count 5 (remove_all 5 (Cons 2 (Cons 1 (Cons 4 (Cons 1 Nil))))) = 0
test_remove_all2 = Refl
test_remove_all3 : count 4 (remove_all 5 (Cons 2 (Cons 1 (Cons 4 (Cons 5 (Cons 1 (Cons 4 Nil))))))) = 2
test_remove_all3 = Refl
test_remove_all4 : count 5 (remove_all 5 (Cons 2 (Cons 1 (Cons 5 (Cons 4 (Cons 5 (Cons 1 (Cons 4 Nil)))))))) = 0
test_remove_all4 = Refl

included : (s1 : Bag) -> (s2 : Bag) -> Bool
included Nil s2 = True
included (Cons n l) s2 = case (member n s2) of
  True => included l (remove_one n s2)
  False => False
test_included1 : included (Cons 1 (Cons 2 Nil)) (Cons 2 (Cons 1 (Cons 4 (Cons 1 Nil)))) = True
test_included1 = Refl
test_included2 : included (Cons 1 (Cons 2 (Cons 2 Nil))) (Cons 2 (Cons 1 (Cons 4 (Cons 1 Nil)))) = False
test_included2 = Refl

-- exercise
plus_n_O : (n : Nat) -> plus n 0 = n
plus_n_O 0 = Refl
plus_n_O (S n') = rewrite (plus_n_O n') in Refl
eqn : (n : Nat) -> n == n = True
eqn 0 = Refl
eqn (S k) = eqn k
add_inc_count : (n : Nat) -> (b : Bag) -> count n b + 1 = count n (add n b)
add_inc_count 0 b =
  let t = (sym $ plus_n_Sm (count 0 b) 0) in
  rewrite t in
  let t' = plus_n_O (count 0 b) in
  rewrite t' in
  Refl
add_inc_count (S n') b = 
  rewrite (eqn n') in
  rewrite (sym $ plus_n_Sm (count (S n') b) 0) in
  rewrite (plus_n_O (count (S n') b)) in
  Refl


-- Reasoning About Lists

nil_app : (l : NatList) -> app Nil l = l
nil_app l = Refl

pred : Nat -> Nat
pred 0 = 0
pred (S n) = n

tl_length_pred : (l : NatList) -> pred (length l) = length (tl l)
tl_length_pred [] = Refl
tl_length_pred (Cons n l) = Refl

-- Induction on Lists

app_assoc : (l1 : NatList) -> (l2 : NatList) -> (l3 : NatList) ->
  app (app l1 l2) l3 = app l1 (app l2 l3)
app_assoc [] l2 l3 = Refl
app_assoc (Cons n l) l2 l3 = 
  let ih = app_assoc l l2 l3 in
  rewrite ih in Refl

-- Reversing a List

rev : (l : NatList) -> NatList
rev [] = Nil
rev (Cons h t) = app (rev t) (Cons h Nil)

test_rev1 : rev (Cons 1 (Cons 2 (Cons 3 Nil))) = Cons 3 (Cons 2 (Cons 1 Nil))
test_rev1 = Refl

app_length : (l1 : NatList) -> (l2 : NatList) ->
  length (app l1 l2) = plus (length l1) (length l2)
app_length [] l2 = Refl
app_length (Cons n l) l2 = rewrite (app_length l l2) in Refl

rev_length : (l : NatList) -> length (rev l) = length l
rev_length [] = Refl
rev_length (Cons n l) =
  rewrite (app_length (rev l) (Cons n [])) in
  rewrite (rev_length l) in 
  rewrite (sym $ plus_n_Sm (length l) 0) in
  rewrite plus_n_O (length l) in
  Refl

-- exercise
app_nil_r : (l : NatList) -> app l Nil = l
app_nil_r [] = Refl
app_nil_r (Cons n l') = rewrite (app_nil_r l') in Refl

rev_app_distr : (l1 : NatList) -> (l2 : NatList) ->
  rev (app l1 l2) = app (rev l2) (rev l1)
rev_app_distr [] l2 = rewrite (app_nil_r (rev l2)) in Refl
rev_app_distr (Cons n l) l2 =
  rewrite (rev_app_distr l l2) in
  rewrite (app_assoc (rev l2) (rev l) (Cons n [])) in 
  Refl

rev_involutive : (l : NatList) -> rev (rev l) = l
rev_involutive [] = Refl
rev_involutive (Cons n l') = 
  rewrite (rev_app_distr (rev l') (Cons n [])) in 
  rewrite (rev_involutive l') in
  Refl

app_assoc4 : (l1 : NatList) -> (l2 : NatList) -> (l3 : NatList) -> (l4 : NatList) ->
  app l1 (app l2 (app l3 l4)) = app (app (app l1 l2) l3) l4
app_assoc4 l1 l2 l3 l4 =
  rewrite (sym $ app_assoc l1 l2 (app l3 l4)) in 
  rewrite (app_assoc (app l1 l2) l3 l4) in
  Refl

nz_app_distr : (l1 : NatList) -> (l2 : NatList) ->
  nonzeros (app l1 l2) = app (nonzeros l1) (nonzeros l2)
nz_app_distr [] l2 = Refl
nz_app_distr (Cons 0 l) l2 = nz_app_distr l l2
nz_app_distr (Cons (S k) l) l2 =
  rewrite (nz_app_distr l l2) in
  Refl

nonzeros_app : (l1 : NatList) -> (l2 : NatList) -> 
  nonzeros (app l1 l2) = app (nonzeros l1) (nonzeros l2)
nonzeros_app [] l2 = Refl
nonzeros_app (Cons n l) [] =
  rewrite (app_nil_r l) in
  rewrite (app_nil_r (nonzeros (Cons n l))) in Refl
nonzeros_app (Cons 0 l) (Cons k x) = 
  rewrite (nz_app_distr l (Cons k x)) in
  Refl
nonzeros_app (Cons (S j) l) (Cons k x) =
  rewrite (nz_app_distr l (Cons k x)) in
  Refl

-- exercise
eqkk : (k : Nat) -> k == k = True
eqkk 0 = Refl
eqkk (S k) = eqkk k

eqblist : (l1 : NatList) -> (l2 : NatList) -> Bool
eqblist [] [] = True
eqblist [] (Cons n l) = False
eqblist (Cons n l) [] = False
eqblist (Cons n l) (Cons k x) =
--  ifThenElse (n == k) (eqblist l x) False
  if (n == k) then (eqblist l x) else False

test_eqblist1 : eqblist Nil Nil = True
test_eqblist1 = Refl
test_eqblist2 : eqblist (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 1 (Cons 2 (Cons 3 Nil))) = True
test_eqblist2 = Refl
test_eqblist3 : eqblist (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 1 (Cons 2 (Cons 4 Nil))) = False
test_eqblist3 = Refl
eqblist_refl : (l : NatList) -> True = eqblist l l
eqblist_refl [] = Refl
eqblist_refl (Cons h t) = 
  rewrite (eqkk h) in 
  eqblist_refl t

-- List Exercises, Part 2

count_member_nonzero : (s : Bag) -> (1 <= (count 1 (Cons 1 s))) = True
count_member_nonzero [] = Refl
count_member_nonzero (Cons 0 l) = count_member_nonzero l
count_member_nonzero (Cons (S 0) l) = Refl
count_member_nonzero (Cons (S (S k)) l) = count_member_nonzero l

leb_n_Sn : (n : Nat) -> n <= (S n) = True
leb_n_Sn 0 = Refl
leb_n_Sn (S k) = leb_n_Sn k

remove_does_not_increase_count : (s : Bag) ->
  (count 0 (remove_one 0 s)) <= (count 0 s) = True
remove_does_not_increase_count [] = Refl
remove_does_not_increase_count (Cons 0 l) = 
  leb_n_Sn (count 0 l)
remove_does_not_increase_count (Cons (S k) l) =
  remove_does_not_increase_count l

bag_count_sum : (n : Nat) -> (s1 : Bag) -> (s2 : Bag) ->
  plus (count n s1) (count n s2) = count n (sum s1 s2)
bag_count_sum n [] s2 = Refl
bag_count_sum n (Cons h t) s2 with (n == h)
  _ | True = rewrite bag_count_sum n t s2 in Refl
  _ | False = rewrite bag_count_sum n t s2 in Refl


involution_injective : (f : Nat -> Nat) -> ((n : Nat) -> n = f (f n)) ->
  ((n1 : Nat) -> (n2 : Nat) -> f n1 = f n2 -> n1 = n2)
involution_injective f g n1 n2 prf = 
  rewrite g n1 in
  rewrite prf in
  sym $ g n2

rev_injective : (l1 : NatList) -> (l2 : NatList) -> 
  rev l1 = rev l2 -> l1 = l2
rev_injective l1 l2 prf =
  rewrite sym $ rev_involutive l1 in
  rewrite sym $ rev_involutive l2 in
  cong rev prf


-- Options

data NatOption : Type where
  Some : (n : Nat) -> NatOption
  None : NatOption

nth_error : (l : NatList) -> (n : Nat) -> NatOption
nth_error [] n = None
nth_error (Cons a l') 0 = Some a
nth_error (Cons a l') (S n') = nth_error l' n'
test_nth_error1 : nth_error (Cons 4 (Cons 5 (Cons 6 (Cons 7 Nil)))) 0 = Some 4
test_nth_error1 = Refl
test_nth_error2 : nth_error (Cons 4 (Cons 5 (Cons 6 (Cons 7 Nil)))) 3 = Some 7
test_nth_error2 = Refl
test_nth_error3 : nth_error (Cons 4 (Cons 5 (Cons 6 (Cons 7 Nil)))) 9 = None
test_nth_error3 = Refl

option_elim : (d : Nat) -> (o : NatOption) -> Nat
option_elim d (Some n') = n'
option_elim d None = d

hd_error : (l : NatList) -> NatOption
hd_error [] = None
hd_error (Cons n l) = Some n
test_hd_error1 : hd_error Nil = None
test_hd_error1 = Refl
test_hd_error2 : hd_error (Cons 1 Nil) = Some 1
test_hd_error2 = Refl
test_hd_error3 : hd_error (Cons 5 (Cons 6 Nil)) = Some 5
test_hd_error3 = Refl

option_elim_hd : (l : NatList) -> (dflt : Nat) ->
  hd dflt l = option_elim dflt (hd_error l)
option_elim_hd [] dflt = Refl
option_elim_hd (Cons n l) dflt = Refl


-- Partial Maps

data Id : Type where
  ID : (n : Nat) -> Id

eqb_id : (x1 : Id) -> (x2 : Id) -> Bool
eqb_id (ID n1) (ID n2) = n1 == n2

eqb_id_refl : (x : Id) -> eqb_id x x = True
eqb_id_refl (ID n) = eqn n

data PartialMap : Type where
  Empty : PartialMap
  Record : (i : Id) -> (v : Nat) -> (m : PartialMap) -> PartialMap

update : (d: PartialMap) -> (x : Id) -> (value : Nat) -> PartialMap
update d x value = Record x value d

find : (x : Id) -> (d : PartialMap) -> NatOption
find x Empty = None
find x (Record y v d') = if eqb_id x y then Some v else find x d'

update_eq : (d : PartialMap) -> (x : Id) -> (v : Nat) ->
  find x (update d x v) = Some v
update_eq Empty x v = rewrite eqb_id_refl x in Refl
update_eq (Record i k m) x v = rewrite eqb_id_refl x in Refl
