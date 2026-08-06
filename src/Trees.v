From GraphSearch Require Import DFS GraphInterface EdgeRel List.
From coqutil Require Import Eqb Tactics.fwd Tactics Datatypes.List.
From Stdlib Require Import List Lia.
Import ListNotations.

Section __.
  Context {V : Type}.
  Context {graph : graph.graph V}.

  Unset Elimination Schemes.
  Inductive tree : Type :=
  | tree_cons : V -> list tree -> tree.
  Set Elimination Schemes.

  Fixpoint tree_size t :=
    match t with
    | tree_cons _ ts => S (fold_right max O (map tree_size ts))
    end.

  Lemma max_big n l :
    In n l -> n <= fold_right max O l.
  Proof.
    induction l.
    - simpl. contradiction.
    - simpl. destruct 1 as [H|H]; subst; try lia.
      apply IHl in H. lia.
  Qed.

  Lemma tree_ind P :
    (forall n l, Forall P l -> P (tree_cons n l)) ->
    forall t, P t.
  Proof.
    intros H t.
    remember (tree_size t) as n eqn:E.
    assert (Ht : tree_size t < S n) by lia.
    clear E. revert t Ht. induction (S n).
    - lia.
    - intros t Ht. destruct t. apply H. apply Forall_forall.
      simpl in Ht. intros x Hx.
      apply in_map with (f := tree_size) in Hx.
      apply max_big in Hx. apply IHn0. lia.
  Qed.

  Definition root t := match t with tree_cons r _ => r end.
  Definition children t := match t with tree_cons _ r => r end.

  Fixpoint nodes_of (t : tree) :=
    match t with
    | tree_cons v ts => v :: flat_map nodes_of ts
    end.

  Definition valid_tree (t : tree) := NoDup (nodes_of t).

  Fixpoint graph_of (t : tree) :=
    match t with
    | tree_cons v ts =>
        graph.union (graph.put_edges graph.empty v (map root ts))
          (fold_left graph.union (map graph_of ts) graph.empty)
    end.

  Lemma valid_tree_graph_edge t u :
    valid_tree t ->
    graph.edge (graph_of t) (root t) u ->
    In u (map root (children t)).
  Proof. Admitted.

  Lemma not_in_no_edge :
    ~In u (nodes_of t)

  Lemma tree_path_cons t n p' :
    valid_tree t ->
    path (graph.edge (graph_of t)) (root t) (n :: p') ->
    exists t',
      In t' (children t) /\
        root t' = n /\
        path (graph.edge (graph_of t')) n p'.
  Proof.
    induction t. intros Hvalid Hpath. cbn [root path] in Hpath. fwd.
    simpl. apply valid_tree_graph_edge in Hpathp0; [|assumption].
    apply in_map_iff in Hpathp0. fwd. simpl in Hpathp0p1.
    exists


  Lemma graph_of_tree_is_tree t :
    valid_tree t ->
    is_tree (graph.edge (graph_of t)) (root t).
  Proof.
    intros H. induction t. cbv [is_tree]. cbn [root]. split.
    - cbv [locally_tree]. cbv [path_to].
  Admitted.
