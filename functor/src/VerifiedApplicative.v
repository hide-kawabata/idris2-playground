(*
  Definition of List, function composition, list concatination
*)

Inductive List (a : Type) : Type :=
| Nil : List a
| Cons : a -> List a -> List a.

Arguments Nil {a}.
Arguments Cons {a}.

Notation "[]" := Nil.
Notation "h :: t" := (Cons h t).

Definition fcomp {a b c : Type} (f : b -> c) (g : a -> b) : a -> c :=
  fun x => f (g x).

Notation "f <.>" := (fcomp f) (at level 50, left associativity).

Fixpoint conc {a : Type} (l1 l2 : List a) : List a :=
  match l1 with
  | [] => l2
  | h :: t => h :: (conc t l2)
  end.

Notation "a ++ b" := (conc a b).

(*
  Definition of fmap to construct functors
*)

Fixpoint fmap {a b : Type} 
                  (g : a -> b) (l : List a) : List b :=
  match l with
  | []  => []
  | x :: xs  => (g x) :: (fmap g xs)
  end.

Notation "g <$>" := (fmap g) (at level 30).

Definition id {a : Type} (x : a) :=
  x.

(*
  Laws fmap should be obey to be a functor map
*)

Lemma mapIdLaw: forall a, forall xs : List a, 
    id <$> xs = id xs.
  intros.
  induction xs.
  - unfold id. simpl. reflexivity.
  - unfold id. simpl. unfold id in IHxs.
    rewrite IHxs. reflexivity.
Qed.

Lemma mapComposeLaw: 
  forall a b c : Type, forall xs : List a, forall f : b -> c, forall g : a -> b,
    (f <.> g) <$> xs = ((f <$>) <.> (g <$>)) xs.
  intros. induction xs.
  - unfold fcomp. simpl. reflexivity.
  - simpl. rewrite IHxs. unfold fcomp. simpl. reflexivity.
Qed.

(*--------------------------------------------------*)

(*
  Definitions of pure and ap (a.k.a. starship) to construct applicative functors
*)

Definition pure {a : Type} (x : a) : List a :=
  x :: [].

Fixpoint ap {a b : Type} (fs : List (a -> b)) (xs : List a) : List b :=
  match fs with
  | [] => []
  | h :: t => (h <$> xs) ++ (ap t xs)
  end.

Notation "t <*>" := (ap t) (at level 38).

(*
  Laws to be held by pure and ap (comLaw is at the end of this file)
*)

Lemma idLaw : forall a : Type, forall l : List a,
    (pure id) <*> l = l.
  induction l.
  - simpl. reflexivity.
  - simpl. simpl in IHl. rewrite IHl. unfold id. reflexivity.
Qed.

Lemma homLaw : forall a b : Type, forall x : a, forall f : a -> b,
    (pure f) <*> (pure x) = pure (f x).
  intros. simpl. unfold pure. reflexivity.
Qed.

Lemma intLaw : forall a b : Type, forall u : List (a -> b), forall y : a,
    u <*> (pure y) = (pure (fun f => f y)) <*> u.
  intros.
  simpl. induction u.
  - simpl. reflexivity.
  - simpl. rewrite <- IHu. reflexivity.
Qed.

(*----------------------
  lemmas used to prove comLaw (composition law)
-----------------------*)
Lemma concNil : forall a : Type, forall xs : List a,
    xs ++ [] = xs.
  intros. induction xs.
  - simpl. reflexivity.
  - simpl. rewrite IHxs. reflexivity.
Qed.

Lemma concAssoc : forall a : Type, forall l1 l2 l3 : List a,
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Lemma concAp : forall a b : Type, forall l1 l2 : List (a -> b), forall l3 : List a,
    (l1 ++ l2) <*> l3 = (l1 <*> l3) ++ (l2 <*> l3).
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1.
    simpl. apply concAssoc.
Qed.

Lemma concFmap : forall a b : Type, forall f : a -> b, forall l1 l2 : List a,
    f <$> (l1 ++ l2) = (f <$> l1) ++ (f <$> l2).
  induction l1.
  - simpl. reflexivity.
  - simpl. intros. rewrite <- IHl1.
    reflexivity.
Qed.

Lemma fmapFcomp: forall a b c : Type, forall f : b -> c, forall g : a -> b, forall x : List a,
    (f <.> g) <$> x = f <$> (g <$> x).
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.  

Lemma apFmap : forall a b c : Type,
  forall f : b -> c, forall gs : List (a -> b), forall xs : List a,
    ((f <.>) <$> gs) <*> xs = f <$> (gs <*> xs).
  intros a b c f gs xs.
  induction gs as [| g gs'].
  - simpl. reflexivity.
  - simpl. 
    rewrite (concFmap _ _ f (g <$> xs) (gs' <*> xs)).
    rewrite fmapFcomp.
    rewrite IHgs'.
    reflexivity.
Qed.

Lemma comLaw : forall a b c : Type,
  forall xs : List a, forall gs : List (a -> b), forall hs : List (b -> c),
    (((pure fcomp) <*> hs) <*> gs) <*> xs = hs <*> (gs <*> xs).
  intros.
  simpl. rewrite concNil. 
  induction hs.
  - simpl. reflexivity.
  - simpl. rewrite <- IHhs.
    rewrite concAp.
    rewrite apFmap.
    reflexivity.
Qed.

