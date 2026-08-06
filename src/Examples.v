From GraphSearch Require Import DFS GraphInterface EdgeRel List.
From coqutil Require Import Eqb Tactics.fwd Tactics.
From Stdlib Require Import List.
Import ListNotations.

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

  Lemma locally_tree_put_unseen g u (v : V) root :
    (forall u', ~graph.edge g u' v) ->
    locally_tree (graph.edge g) root <-> locally_tree (graph.edge (graph.put g u v)) root.
  Proof. Admitted.

  Lemma all_nodes_empty :
    graph.all_nodes graph.empty = [].
  Proof. Admitted.

  Lemma all_nodes_spec g u :
    In u (graph.all_nodes g) <-> (exists v, graph.edge g u v \/ graph.edge g v u).
  Proof. Admitted.

  Lemma all_nodes_put g u v u' :
    In u' (graph.all_nodes (graph.put g u v)) <-> In u' (graph.all_nodes g) \/ u' = u \/ u' = v.
  Proof. Admitted.

  Lemma path_snoc A (R : A -> _) root p v :
    path R root (p ++ [v]) <-> path R root p /\ R (last p root) v.
  Proof. Admitted.

  Lemma path_weaken A (R1 R2 : A -> _) root p :
    path R1 root p ->
    (forall x y, R1 x y -> R2 x y) ->
    path R2 root p.
  Proof. Admitted.

  Lemma duplicate_edge_not_locally_tree g (root : V) u v :
    reaches (graph.edge g) root u ->
    reaches (graph.edge g) root v ->
    ~ graph.edge g u v ->
    ~ locally_tree (graph.edge (graph.put g u v)) root.
  Proof. Admitted.

  Lemma check_tree_spec g root :
    Reflects (locally_tree (graph.edge g) root) (check_locally_tree g root).
  Proof.
    cbv [check_locally_tree]. Tactics.destruct_one_match.
    apply dfs_fold_spec in E. fwd. apply locally_tree_reachable_subgraph in Ep0.
    eapply Reflects_iff; [|eassumption]. clear Ep0. remember (l, b) as x eqn:E.
    simpl in Ep1. remember [] as p eqn:Ep.
    replace (root :: p) with [root] in Ep1 by (subst; reflexivity).
    clear Ep.
    eenough (H : _ /\ same_set (root :: graph.all_nodes g') l /\ incl p l /\ (forall v, In v l -> reaches (graph.edge g') root v)).
    { exact (proj1 H). }
    revert l b E. induction Ep1; intros vs b E; simpl in E; fwd.
    - ssplit.
      + constructor. apply locally_tree_empty.
      + rewrite all_nodes_empty. cbv [same_set]. reflexivity.
      + apply incl_refl.
      + intros ? [?|[]]. subst. apply reaches_self.
    - destruct st. specialize (IHEp1 _ _ eq_refl). simpl in E. fwd.
      simpl in H0. apply set_contains_false in H0. ssplit.
      + eapply Reflects_iff; [eassumption|]. apply locally_tree_put_unseen.
        intros u' Hu'. apply H0. apply IHEp1p1. right. apply all_nodes_spec. eauto.
      + cbv [same_set] in *. intros. simpl. rewrite <- IHEp1p1. simpl.
        rewrite all_nodes_put.
        split; intros H'; repeat destruct H' as [H'|H']; subst; auto.
        specialize (IHEp1p2 u ltac:(simpl; auto)). apply IHEp1p1 in IHEp1p2.
        destruct IHEp1p2; auto.
      + apply incl_cons.
        -- simpl. auto.
        -- apply incl_tl. assumption.
      + admit.
    - destruct st. specialize (IHEp1 _ _ eq_refl). simpl in E. fwd.
      simpl in H0. apply set_contains_true in H0. ssplit.
      + constructor. apply duplicate_edge_not_locally_tree; auto.
        apply IHEp1p3. apply IHEp1p2. simpl. auto.
      + admit.
      + assumption.
      + (*todo use reaches_weaken*) admit.
    - destruct st. specialize (IHEp1 _ _ eq_refl). simpl in E. fwd.
      ssplit; auto. apply incl_cons_inv in IHEp1p2. fwd. auto.
  Admitted.
