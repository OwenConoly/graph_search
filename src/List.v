From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb.
Import ListNotations.

Lemma fold_right_inv_NoDup {A B} (P : list B -> A -> Prop) (f : B -> A -> A) l a :
  NoDup l ->
  P [] a ->
  (forall a' b l', ~In b l' -> In b l -> P l' a' -> P (b :: l') (f b a')) ->
  P l (fold_right f a l).
Proof.
  intros H ? ?. induction l; simpl; auto. simpl in *. inversion_clear H. eauto 6.
Qed.

Lemma in_not_nil A x (l : list A) :
  In x l ->
  l <> nil.
Proof. destruct l; simpl; congruence. Qed.

Lemma neq_nil_iff_exists_in A (l : list A) :
  l <> [] <-> exists x, In x l.
Proof.
  split.
  - destruct l as [|a l']; intros H; [congruence | exists a; left; reflexivity].
  - intros [x Hx]. destruct l as [|a l']; [destruct Hx | discriminate].
Qed.

Lemma forall_not_in_nil A (l : list A) :
  (forall x, ~In x l) ->
  l = [].
Proof. destruct l; auto. simpl. intros. exfalso. eapply H; auto. Qed.

Lemma incl_cons_r A (a : A) l :
  incl l (a :: l).
Proof. intros x Hx. right. exact Hx. Qed.

Lemma removelast_cons A (a b : A) l :
  removelast (a :: b :: l) = a :: removelast (b :: l).
Proof. reflexivity. Qed.

Lemma NoDup_removelast A (l : list A) :
  NoDup l ->
  NoDup (removelast l).
Proof. intro H. rewrite removelast_firstn_len. apply NoDup_firstn. exact H. Qed.

Lemma length_removelast_cons A (a : A) l :
  length (removelast (a :: l)) = length l.
Proof. rewrite removelast_firstn_len. rewrite length_firstn. cbn [length]. lia. Qed.

Lemma last_cons A (l : list A) a d :
  last (a :: l) d = last l a.
Proof.
  revert a d. induction l as [|b l' IH]; intros a d; [reflexivity|].
  change (last (b :: l') d = last (b :: l') a).
  rewrite (IH b d), (IH b a). reflexivity.
Qed.

Lemma last_cons_last_cons A (a : A) l d1 d2 :
  last (a :: l) d1 = last (a :: l) d2.
Proof. do 2 rewrite last_cons. reflexivity. Qed.

Section set_contains.
  Context {V : Type} {eqbV : Eqb V} {eqb_ok : Eqb_ok eqbV}.

  Definition set_contains vs v :=
    existsb (eqb v) vs.

  Lemma set_contains_true v vs :
    set_contains vs v = true <-> In v vs.
  Proof. unfold set_contains. symmetry. apply existsb_eqb_in. Qed.

  Lemma set_contains_false v vs :
    set_contains vs v = false <-> ~In v vs.
  Proof.
    unfold set_contains. rewrite existsb_eqb_in.
    destruct (existsb (eqb v) vs); intuition congruence.
  Qed.
End set_contains.
