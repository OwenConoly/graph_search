From Stdlib Require Import List Lia Permutation Morphisms.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb Tactics.Tactics.
Import ListNotations.

Definition same_set {A} (l1 l2 : list A) := forall a, In a l1 <-> In a l2.

Lemma same_set_refl A (x : list A) :
  same_set x x.
Proof. intros a. reflexivity. Qed.

Lemma fold_right_inv_NoDup {A B} (P : list B -> A -> Prop) (f : B -> A -> A) l a :
  NoDup l ->
  P [] a ->
  (forall a' b l', ~In b l' -> In b l -> P l' a' -> P (b :: l') (f b a')) ->
  P l (fold_right f a l).
Proof.
  intros H ? ?. induction l; simpl; auto. simpl in *. inversion_clear H. eauto 6.
Qed.

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

Lemma last_cons_nonempty A (a : A) l d :
  l <> [] ->
  last (a :: l) d = last l d.
Proof.
  intro Hl. rewrite last_cons. destruct l as [|b l']; [ congruence | ].
  apply last_cons_last_cons.
Qed.

Lemma In_last_cons A (l : list A) x d :
  In (last (x :: l) d) (x :: l).
Proof.
  revert x d. induction l as [|y l' IH]; intros x d.
  - left. reflexivity.
  - rewrite last_cons. right. apply IH.
Qed.

Lemma in_fst A B (x : A) (y : B) xys :
  In (x, y) xys ->
  In x (map fst xys).
Proof. induction xys; simpl; eauto. destruct 1; subst; eauto. Qed.

#[export] Instance Permutation_filter {A} (q : A -> bool) :
  Proper (@Permutation A ==> @Permutation A) (filter q).
Proof.
  intros l l' HP. induction HP; cbn [filter].
  - apply Permutation_refl.
  - destruct (q x); [ apply perm_skip | ]; assumption.
  - destruct (q x), (q y); solve [ apply perm_swap | apply Permutation_refl ].
  - eapply perm_trans; eassumption.
Qed.

Lemma filter_eq_nil {A} (P : A -> bool) l :
  (forall a, In a l -> P a = false) ->
  filter P l = [].
Proof.
  induction l as [|a l' IH]; intro H; [ reflexivity | ].
  cbn [filter]. rewrite (H a (or_introl eq_refl)). apply IH.
  intros b Hb. apply H. right. exact Hb.
Qed.

Lemma filter_eq_singleton {A} (P : A -> bool) l a0 :
  NoDup l ->
  In a0 l ->
  P a0 = true ->
  (forall a, In a l -> P a = true -> a = a0) ->
  filter P l = [a0].
Proof.
  induction l as [|a l' IH]; intros Hnd Hin Ha0 Huniq; [ destruct Hin | ].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
  cbn [filter]. destruct (P a) eqn:EPa.
  - assert (Haa0 : a = a0) by (apply Huniq; [ left; reflexivity | exact EPa ]).
    rewrite Haa0. f_equal. apply filter_eq_nil. intros b Hb.
    destruct (P b) eqn:EPb; [ | reflexivity ].
    assert (Hba0 : b = a0) by (apply Huniq; [ right; exact Hb | exact EPb ]).
    exfalso. apply Hnotin. rewrite Haa0, <- Hba0. exact Hb.
  - destruct Hin as [Ha_eq | Hin'].
    + subst a. rewrite Ha0 in EPa. discriminate.
    + apply IH; [ exact Hnd' | exact Hin' | exact Ha0 | ].
      intros b Hb HPb. apply Huniq; [ right; exact Hb | exact HPb ].
Qed.

Lemma NoDup_same_length {A} (l1 l2 : list A) :
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 <-> In x l2) ->
  length l1 = length l2.
Proof. intros HA HB Hiff. apply Permutation_length, NoDup_Permutation; assumption. Qed.

Lemma NoDup_flat_map {A B} (f : A -> list B) l :
  NoDup l ->
  (forall a, In a l -> NoDup (f a)) ->
  (forall a1 a2 b, In a1 l -> In a2 l -> In b (f a1) -> In b (f a2) -> a1 = a2) ->
  NoDup (flat_map f l).
Proof.
  intros Hnd Hnf Hdisj. induction l as [|a l IH]; cbn [flat_map].
  - constructor.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd].
    apply NoDup_app_iff. ssplit.
    + apply Hnf. left. reflexivity.
    + apply IH.
      * exact Hnd.
      * intros a0 Ha0. apply Hnf. right. exact Ha0.
      * intros a1 a2 b Hi1 Hi2 Hb1 Hb2.
        apply (Hdisj a1 a2 b); [ right; exact Hi1 | right; exact Hi2 | exact Hb1 | exact Hb2 ].
    + intros b Hb Hbf. apply in_flat_map in Hbf. destruct Hbf as [a2 [Ha2 Hb2]].
      assert (a = a2) as -> by
          (apply (Hdisj a a2 b); [ left; reflexivity | right; exact Ha2 | exact Hb | exact Hb2 ]).
      contradiction.
    + intros b Hbf Hb. apply in_flat_map in Hbf. destruct Hbf as [a2 [Ha2 Hb2]].
      assert (a = a2) as -> by
          (apply (Hdisj a a2 b); [ left; reflexivity | right; exact Ha2 | exact Hb | exact Hb2 ]).
      contradiction.
Qed.

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
