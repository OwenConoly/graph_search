From GraphSearch Require Import DFS GraphInterface EdgeRel List.
From coqutil Require Import Eqb Tactics.fwd.
From Stdlib Require Import List.

Section __.
  Context {V : Type} {eqbV : Eqb V} {graph : graph.graph V}.
  Context {eqbV_ok : Eqb_ok eqbV} {graph_ok : graph.ok graph}.

  Definition check_locally_tree g root :=
    let '(_, is_tree) :=
      dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree) (fun tree _ _ => tree) g true root in
    is_tree.

  Notation Reflects x := (BoolSpec x (~x)).

  Lemma Reflects_iff P Q b :
    Reflects P b ->
    P <-> Q ->
    Reflects Q b.
  Proof. Admitted.

  Axiom blah : False.
  Lemma locally_tree_reachable_subgraph g g' (root : V) :
    reachable_subgraph root g' g ->
    locally_tree (graph.edge g') root <-> locally_tree (graph.edge g) root.
  Proof. destruct blah. Qed.

  Lemma locally_tree_empty (root : V) :
    locally_tree (graph.edge graph.empty) root.
  Proof. Admitted.

  Lemma check_tree_spec g root :
    Reflects (locally_tree (graph.edge g) root) (check_locally_tree g root).
  Proof.
    cbv [check_locally_tree]. Tactics.destruct_one_match.
    apply dfs_fold_spec in E. fwd. apply locally_tree_reachable_subgraph in Ep0.
    eapply Reflects_iff; [|eassumption]. clear Ep0. remember (l, b) as x eqn:E.
    eenough (H : _ /\ forall u v, graph.edge g' u v -> In v l).
    { exact (proj1 H). }
    revert l b E. induction Ep1; intros l b E; simpl in E; fwd.
    - split.
      + constructor. apply locally_tree_empty.
      + intros * H. cbv [graph.edge] in H. rewrite graph.edges_empty in H.
        simpl in H. contradiction.
    - destruct st. specialize (IHEp1 _ _ eq_refl). simpl in E. fwd.
      simpl in H0. apply set_contains_false in H0. eapply Reflects_iff; [eassumption|].
      Lemma locally_tree_put_unseen :
      apply set_
    Search BoolSpec.
    rewrite <- Ep0. by eassumption.
    apply
    Search BoolSpec.
