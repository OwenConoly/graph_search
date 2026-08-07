From GraphSearch Require Import DFS GraphInterface EdgeRel List.
From coqutil Require Import Eqb Tactics.fwd Tactics Datatypes.List Datatypes.ListSet.
From Stdlib Require Import List Lia.
Import ListNotations.

Section __.
  Context {V : Type} {eqbV : Eqb V} {graph : graph.graph V}.
  Context {eqbV_ok : Eqb_ok eqbV} {graph_ok : graph.ok graph}.

  Definition check_locally_tree g root :=
    let '(_, is_tree) :=
      dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree) (fun tree _ _ => tree) g true root in
    is_tree.

  Definition num_nodes g root :=
    length (list_union eqb [root] (graph.all_nodes g)).

  Definition num_edges (g : graph) :=
    length (graph.all_edges g).

  Definition is_tree g root :=
    all_reachable (graph.edge g) root /\
      S (num_edges g) = num_nodes g root.

  Notation Reflects x := (BoolSpec x (~x)).

  Lemma Reflects_iff P Q b :
    Reflects P b ->
    P <-> Q ->
    Reflects Q b.
  Proof. intros HP Hiff. destruct HP; constructor; tauto. Qed.

  Lemma num_edges_empty :
    num_edges (graph.empty : graph) = O.
  Proof. Admitted.

  Lemma num_nodes_empty root :
    num_nodes graph.empty root = S O.
  Proof. Admitted.

  Lemma num_edges_put g u v :
    ~graph.edge g u v ->
    num_edges (graph.put g u v) = S (num_edges g).
  Proof. Admitted.

  Lemma num_nodes_put01 g root u v :
    In u (root :: graph.all_nodes g) ->
    ~In v (graph.all_nodes g) ->
    v <> root ->
    num_nodes (graph.put g u v) root = S (num_nodes g root).
  Proof. Admitted.

  Lemma num_nodes_put00 g root u v :
    In u (root :: graph.all_nodes g) ->
    In v (root :: graph.all_nodes g) ->
    num_nodes (graph.put g u v) root = num_nodes g root.
  Proof. Admitted.

  Lemma dfs_check_invariant (root : V) vs is_tree p (g : graph) :
    dfs_fold_state (fun _ _ _ => false) (fun tree _ _ => tree) (fun tree _ _ => tree)
      root [root] true vs is_tree p g ->
    Reflects (S (num_edges g) = num_nodes g root) is_tree.
  Proof.
    induction 1;
      try match goal with
      | H: dfs_fold_state _ _ _ _ _ _ _ _ _ _ |- _ => rename H into IH0; apply dfs_fold_state_invs in IH0; fwd
      end.
    - rewrite num_nodes_empty, num_edges_empty. auto.
    - apply set_contains_false in H1. eapply Reflects_iff; [eassumption|].
      rewrite num_edges_put by assumption. rewrite num_nodes_put01.
      + lia.
      + apply IH0p0. apply IH0p1. simpl. auto.
      + intro. apply H1. apply IH0p0. simpl. auto.
      + intro. subst. auto.
    - apply set_contains_true in H1. constructor.
      rewrite num_edges_put by assumption. rewrite num_nodes_put00.
      +

      eapply Reflects_iff; [eassumption|].
      specialize (IH0p1 u ltac:(simpl; eauto)). apply IH0p0 in IH0p1.
      destruct IH0p1 as [IH0p1|IH0p1].
      + subst.
      apply IH0p0 in IH0p1.
        destruct IH0p1; auto. subst.

      ssplit.
      + eapply Reflects_iff; [eassumption|].
        apply locally_tree_put_unseen; try assumption.
        * intros w Hw. apply HvA. apply graph.all_nodes_spec. exists w. right. exact Hw.
        * intros w Hw. apply HvA. apply graph.all_nodes_spec. exists w. left. exact Hw.
      + cbv [same_set] in *. intros a. specialize (IHp1 a). cbn [In] in IHp1 |- *.
        rewrite graph.all_nodes_put. split.
        * intros [Hr | [Hg | [Hu' | Hv']]].
          -- right. apply (proj1 IHp1). left. exact Hr.
          -- right. apply (proj1 IHp1). right. exact Hg.
          -- subst a. right. exact Hu_in.
          -- left. symmetry. exact Hv'.
        * intros [Hv' | Hsvs].
          -- right. right. right. symmetry. exact Hv'.
          -- apply (proj2 IHp1) in Hsvs.
             destruct Hsvs as [Hr | Hg]; [ left; exact Hr | right; left; exact Hg ].
      + apply incl_cons; [ left; reflexivity | apply incl_tl; exact IHp2 ].
      + intros y [<- | Hys].
        * eapply reaches_step.
          -- eapply reaches_weaken; [ | apply IHp3; exact Hu_in ].
             intros a c Hac. apply graph.edge_put. left. exact Hac.
          -- apply graph.edge_put. right. split; reflexivity.
        * eapply reaches_weaken; [ | apply IHp3; exact Hys ].
          intros a c Hac. apply graph.edge_put. left. exact Hac.
    - destruct st as [svs sb]. cbn [fst snd untree_edge_upd'] in IH |- *.
      cbn [already_seen] in Hseen. apply set_contains_true in Hseen. fwd.
      ssplit.
      + constructor. apply duplicate_edge_not_locally_tree.
        * apply IHp3. apply IHp2. left. reflexivity.
        * apply IHp3. exact Hseen.
        * exact Hnew.
      + cbv [same_set] in *. intros a. specialize (IHp1 a). cbn [In] in IHp1 |- *.
        rewrite graph.all_nodes_put. split.
        * intros [Hr | [Hg | [Hu' | Hv']]].
          -- apply (proj1 IHp1). left. exact Hr.
          -- apply (proj1 IHp1). right. exact Hg.
          -- subst a. apply IHp2. left. reflexivity.
          -- subst a. exact Hseen.
        * intros Hsvs. apply (proj2 IHp1) in Hsvs.
          destruct Hsvs as [Hr | Hg]; [ left; exact Hr | right; left; exact Hg ].
      + exact IHp2.
      + intros y Hys. eapply reaches_weaken; [ | apply IHp3; exact Hys ].
        intros a c Hac. apply graph.edge_put. left. exact Hac.
    - destruct st as [svs sb]. cbn [fst snd finish'] in IH |- *. fwd. ssplit.
      + exact IHp0.
      + exact IHp1.
      + apply incl_cons_inv in IHp2. exact (proj2 IHp2).
      + exact IHp3.
  Qed.

  Lemma check_tree_spec g root :
    Reflects (locally_tree (graph.edge g) root) (check_locally_tree g root).
  Proof.
    cbv [check_locally_tree].
    destruct (dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree) (fun tree _ _ => tree) g true root)
      as [l b] eqn:E.
    apply dfs_fold_spec in E. fwd.
    apply locally_tree_reachable_subgraph in Ep0.
    eapply Reflects_iff; [ | exact Ep0 ].
    simpl in Ep1. apply dfs_check_invariant in Ep1. exact (proj1 Ep1).
  Qed.

End __.
