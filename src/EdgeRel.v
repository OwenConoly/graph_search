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

    Definition locally_tree root :=
      forall n p1 p2,
        path_to root p1 n ->
        path_to root p2 n ->
        p1 = p2.
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
End __.
