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
  Proof. unfold num_edges, graph.all_edges. rewrite graph.sources_empty. reflexivity. Qed.

  Lemma num_nodes_empty root :
    num_nodes graph.empty root = S O.
  Proof. unfold num_nodes. rewrite graph.all_nodes_empty. reflexivity. Qed.

  Lemma num_edges_put g u v :
    ~graph.edge g u v ->
    num_edges (graph.put g u v) = S (num_edges g).
  Proof.
    intro Hne. unfold num_edges.
    transitivity (length ((u, v) :: graph.all_edges g)).
    - apply NoDup_same_length.
      + apply graph.all_edges_NoDup.
      + apply NoDup_cons.
        * rewrite graph.In_all_edges. exact Hne.
        * apply graph.all_edges_NoDup.
      + intros [a b]. rewrite graph.In_all_edges, graph.edge_put. cbn [In].
        rewrite graph.In_all_edges, pair_equal_spec. tauto.
    - reflexivity.
  Qed.

  Lemma num_nodes_put01 g root u v :
    In u (root :: graph.all_nodes g) ->
    ~In v (graph.all_nodes g) ->
    v <> root ->
    num_nodes (graph.put g u v) root = S (num_nodes g root).
  Proof.
    intros Hu Hv Hvr. cbn [In] in Hu. unfold num_nodes.
    transitivity (length (v :: list_union eqb [root] (graph.all_nodes g))).
    - apply NoDup_same_length.
      + apply list_union_preserves_NoDup. apply graph.all_nodes_NoDup.
      + apply NoDup_cons.
        * rewrite In_list_union_spec. cbn [In].
          intros [[Hr | []] | Hin]; [ congruence | exact (Hv Hin) ].
        * apply list_union_preserves_NoDup. apply graph.all_nodes_NoDup.
      + intro x. rewrite In_list_union_spec, graph.all_nodes_put. cbn [In].
        rewrite In_list_union_spec. cbn [In].
        split.
        * intros [Hr | [Hg | [Hxu | Hxv]]]; subst; tauto.
        * intros [Hxv | [Hr | Hg]]; subst; tauto.
    - reflexivity.
  Qed.

  Lemma num_nodes_put00 g root u v :
    In u (root :: graph.all_nodes g) ->
    In v (root :: graph.all_nodes g) ->
    num_nodes (graph.put g u v) root = num_nodes g root.
  Proof.
    intros Hu Hv. unfold num_nodes. apply NoDup_same_length.
    - apply list_union_preserves_NoDup. apply graph.all_nodes_NoDup.
    - apply list_union_preserves_NoDup. apply graph.all_nodes_NoDup.
    - intro x. rewrite !In_list_union_spec, graph.all_nodes_put. cbn [In] in *.
      split.
      + intros [Hr | [Hg | [Hxu | Hxv]]]; subst; tauto.
      + tauto.
  Qed.

  Lemma check_tree_spec' (root : V) vs is_tree p (g : graph) :
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
      + assert (num_nodes g root <= S (num_edges g)) by (clear IH0p3; admit).
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
