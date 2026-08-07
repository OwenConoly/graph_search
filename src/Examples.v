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

  Definition is_tree g root :=
    all_reachable (graph.edge g) root /\
      S (graph.num_edges g) = graph.num_nodes g root.

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
      + assert (graph.num_nodes g root <= S (graph.num_edges g)) by (clear IH0p3; admit).
        lia.
      + apply IH0p0. apply IH0p1. simpl. auto.
      + apply IH0p0. assumption.
    - assumption.
  Admitted.

  Lemma check_tree_spec g root :
    Reflects (locally_tree (graph.edge g) root) (check_locally_tree g root).
  Proof.
    cbv [check_locally_tree]. Tactics.destruct_one_match.
    apply dfs_fold_spec in E. fwd.
    apply check_tree_spec' in Ep1.
    Print locally_tree.
    About locally_tree.
  Admitted.

End __.
