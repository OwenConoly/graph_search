From Stdlib Require Import List.
From coqutil Require Import Tactics.fwd.
From GraphSearch Require Import List.
Import ListNotations.

Section __.
  Context {V : Type}.

  Section path.
    Context (edge : V -> V -> Prop).

    Fixpoint path (first : V) (p : list V) :=
      match p with
      | [] => True
      | next :: p' => edge first next /\ path next p'
      end.

    Definition path_to first p last :=
      path first p /\ last = List.last p first.

    Definition reaches first last :=
      exists p, path_to first p last.

    Definition all_reachable root :=
      forall u v, edge u v -> reaches root u.
  End path.

  Lemma reaches_self R u :
    reaches R u u.
  Proof. cbv [reaches]. exists nil. cbv [path_to]. simpl. auto. Qed.

  Lemma reaches_step_before R u v w :
    reaches R v w ->
    R u v ->
    reaches R u w.
  Proof.
    cbv [reaches path_to]. intros. fwd. eexists (_ :: _). simpl. split; eauto.
    destruct p; try reflexivity. apply last_cons_last_cons.
  Qed.

  Lemma edge_closed_reaches_in R u0 v0 vs :
    (forall u v, In u vs -> R u v -> In v vs) ->
    In u0 vs ->
    reaches R u0 v0 ->
    In v0 vs.
  Proof.
    intros H Hu0 Hreach. cbv [reaches path_to] in Hreach. fwd.
    revert u0 Hu0 Hreachp0. induction p; cbn [path]; intros u0 Hu0 Hreach; auto.
    fwd. destruct p; eauto. rewrite last_cons. apply IHp; eauto.
  Qed.

  Lemma path_weaken R1 R2 first p :
    (forall x y, R1 x y -> R2 x y) ->
    path R1 first p ->
    path R2 first p.
  Proof.
    intros HR. revert first. induction p as [|a p IH]; intros first; cbn [path]; auto.
    intros [He Hp]. eauto.
  Qed.

  Lemma path_snoc R first p v :
    path R first (p ++ [v]) <-> path R first p /\ R (last p first) v.
  Proof.
    revert first. induction p as [|a p IH]; intros first.
    - simpl. tauto.
    - cbn [app path]. rewrite IH, last_cons. tauto.
  Qed.

  Lemma reaches_weaken R1 R2 u v :
    (forall x y, R1 x y -> R2 x y) ->
    reaches R1 u v ->
    reaches R2 u v.
  Proof.
    cbv [reaches path_to]. intros HR [p [Hp Hlast]].
    exists p. split; [eapply path_weaken; eauto | exact Hlast].
  Qed.

  Lemma reaches_step R u v w :
    reaches R u v ->
    R v w ->
    reaches R u w.
  Proof.
    cbv [reaches path_to]. intros [p [Hp Hlast]] Hedge.
    exists (p ++ [w]). rewrite path_snoc, last_last. subst v.
    split; [split; assumption | reflexivity].
  Qed.

  Lemma path_sink_last R v first p :
    (forall w, ~ R v w) ->
    path R first p ->
    In v p ->
    last p first = v.
  Proof.
    intros Hsink. revert first. induction p as [|a p IH]; intros first Hpath Hin.
    - destruct Hin.
    - destruct Hpath as [He Hp]. rewrite last_cons. destruct Hin as [-> | Hin].
      + destruct p as [|b p']; [reflexivity|]. destruct Hp as [Hvb _].
        exfalso. eapply Hsink; exact Hvb.
      + apply IH; assumption.
  Qed.

End __.
