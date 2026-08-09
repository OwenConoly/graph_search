From GraphSearch Require Import DFS GraphInterface List Trees.
From coqutil Require Import Eqb Tactics.fwd Tactics Datatypes.List Datatypes.ListSet.
From Stdlib Require Import List Lia.
Import ListNotations.

Section __.
  Context {V : Type} {eqbV : Eqb V} {graph : graph.graph V}.
  Context {eqbV_ok : Eqb_ok eqbV} {graph_ok : graph.ok graph}.

  Definition check_locally_tree g root :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree) (fun tree _ _ => tree) g true root.

  Notation Reflects x := (BoolSpec x (~x)).

  Lemma Reflects_iff P Q b :
    Reflects P b ->
    P <-> Q ->
    Reflects Q b.
  Proof. intros HP Hiff. destruct HP; constructor; tauto. Qed.

  Lemma check_tree_spec' (root : V) vs is_tree p (g : graph) :
    dfs_fold_state (fun _ _ _ => false) (fun tree _ _ => tree) (fun tree _ _ => tree)
      root [root] true vs is_tree p g ->
    Reflects (S (graph.num_edges g) = graph.num_nodes g root) is_tree.
  Proof.
    induction 1;
      try match goal with
      | H: dfs_fold_state _ _ _ _ _ _ _ _ _ _ |- _ => rename H into IH0; apply dfs_fold_state_invs in IH0; fwd
      end.
    - rewrite graph.num_nodes_empty, graph.num_edges_empty. auto.
    - apply set_contains_false in H1. eapply Reflects_iff; [eassumption|].
      rewrite graph.num_edges_put by assumption. rewrite graph.num_nodes_put01.
      + lia.
      + apply IH0p0. apply IH0p1. simpl. auto.
      + intro. apply H1. apply IH0p0. simpl. auto.
      + intro. subst. auto.
    - apply set_contains_true in H1. constructor.
      rewrite graph.num_edges_put by assumption. rewrite graph.num_nodes_put00.
      + apply many_edges in IH0p3. lia.
      + apply IH0p0. apply IH0p1. simpl. auto.
      + apply IH0p0. assumption.
    - assumption.
  Qed.

  Lemma check_tree_spec g root :
    let '(vs, is_tree) := check_locally_tree g root in
    Reflects (graph.is_locally_tree g root) is_tree /\
      (forall v, In v vs <-> graph.reaches g root v).
  Proof.
    destruct (check_locally_tree g root) as [vs is_tree] eqn:E.
    cbv [check_locally_tree] in E.
    split.
    - apply dfs_fold_spec in E. fwd.
      apply check_tree_spec' in Ep1.
      eapply Reflects_iff; [eassumption|].
      cbv [graph.is_locally_tree]. split; intros H; fwd; eauto.
      eapply graph.reachable_subgraph_unique in Ep0; [|exact Hp0].
      subst. assumption.
    - intro v.
      assert (Hconn : forall u, In u vs -> graph.reaches g root u).
      { intros u Hu. eapply dfs_fold_connected; [ exact E | exact Hu ]. }
      apply dfs_fold_spec in E. fwd.
      cbv [graph.reachable_subgraph] in Ep0.
      apply dfs_fold_state_vs_good in Ep1. cbv [same_set] in Ep1.
      assert (Hclosed : forall u w, In u vs -> graph.edge g u w -> In w vs).
      { intros u w Hu Hedge. rewrite Ep1. apply in_cons.
        rewrite graph.all_nodes_spec. exists u. right. apply Ep0. auto. }
      split.
      + exact (Hconn v).
      + intro Hr. apply (graph.edge_closed_reaches_in g root v vs).
        * exact Hclosed.
        * rewrite Ep1. apply in_eq.
        * exact Hr.
  Qed.
End __.
