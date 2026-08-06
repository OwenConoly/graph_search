From GraphSearch Require Import DFS GraphInterface EdgeRel List.
From coqutil Require Import Eqb Tactics.fwd Tactics Datatypes.List.
From Stdlib Require Import List Lia.
Import ListNotations.

Section __.
  Context {V : Type}.
  Context {graph : graph.graph V}.
  Context {graph_ok : graph.ok graph}.

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

  (* ---------- edges of graph_of ---------- *)

  Lemma nodes_of_root t : In (root t) (nodes_of t).
  Proof. destruct t. simpl. left. reflexivity. Qed.

  Lemma edge_fold_union (gs : list graph) (g0 : graph) a b :
    graph.edge (fold_left graph.union gs g0) a b <->
    graph.edge g0 a b \/ exists g, In g gs /\ graph.edge g a b.
  Proof.
    revert g0. induction gs as [|g gs IH]; intros g0; cbn [fold_left].
    - split.
      + intros H. left. exact H.
      + intros [H | [g [[] _]]]. exact H.
    - rewrite IH, graph.edge_union. split.
      + intros [[H|H] | [g' [Hin He]]].
        * left. exact H.
        * right. exists g. split; [left; reflexivity | exact H].
        * right. exists g'. split; [right; exact Hin | exact He].
      + intros [H | [g' [[Heq | Hin] He]]].
        * left. left. exact H.
        * left. right. subst g'. exact He.
        * right. exists g'. split; [exact Hin | exact He].
  Qed.

  Lemma edge_graph_of v ts a b :
    graph.edge (graph_of (tree_cons v ts)) a b <->
    (a = v /\ In b (map root ts)) \/ (exists s, In s ts /\ graph.edge (graph_of s) a b).
  Proof.
    cbn [graph_of]. rewrite graph.edge_union.
    assert (H1 : graph.edge (graph.put_edges graph.empty v (map root ts)) a b <->
                 a = v /\ In b (map root ts)).
    { cbv [graph.edge]. rewrite graph.edges_put_edges, graph.edges_empty. cbn [In].
      split.
      - intros [[] | [Hv Hb]]. split; [symmetry; exact Hv | exact Hb].
      - intros [Ha Hb]. right. split; [symmetry; exact Ha | exact Hb]. }
    assert (H2 : graph.edge (fold_left graph.union (map graph_of ts) graph.empty) a b <->
                 exists s, In s ts /\ graph.edge (graph_of s) a b).
    { rewrite edge_fold_union. split.
      - intros [He | [g [Hg He]]].
        + exfalso. exact (graph.edge_empty _ _ He).
        + apply in_map_iff in Hg. destruct Hg as [s [Hgs Hin]]. subst g. exists s. auto.
      - intros [s [Hs He]]. right. exists (graph_of s). split; [apply in_map; exact Hs | exact He]. }
    rewrite H1, H2. reflexivity.
  Qed.

  Lemma edge_nodes s a b :
    graph.edge (graph_of s) a b -> In a (nodes_of s) /\ In b (nodes_of s).
  Proof.
    revert a b. induction s as [v ts IH] using tree_ind. intros a b He.
    apply edge_graph_of in He. cbn [nodes_of]. destruct He as [[Ha Hb] | [s [Hs He]]].
    - subst a. split.
      + left. reflexivity.
      + right. apply in_flat_map. apply in_map_iff in Hb. destruct Hb as [t [Hrt Hint]].
        exists t. split; [exact Hint | subst b; apply nodes_of_root].
    - rewrite Forall_forall in IH. specialize (IH s Hs a b He). destruct IH as [Hna Hnb].
      split; right; apply in_flat_map; exists s; auto.
  Qed.

  (* ---------- validity / disjointness ---------- *)

  Lemma root_not_in_children v ts :
    valid_tree (tree_cons v ts) -> ~ In v (flat_map nodes_of ts).
  Proof.
    cbv [valid_tree]. cbn [nodes_of]. intro H. apply NoDup_cons_iff in H. exact (proj1 H).
  Qed.

  Lemma valid_tree_child v ts s :
    valid_tree (tree_cons v ts) -> In s ts -> valid_tree s.
  Proof.
    cbv [valid_tree]. cbn [nodes_of]. intros H Hs.
    inversion H as [| x l Hnin Hnd Heq]. clear H.
    apply in_split in Hs. destruct Hs as [l1 [l2 Heqts]]. subst ts.
    rewrite flat_map_app in Hnd. cbn [flat_map] in Hnd.
    apply NoDup_app_remove_l in Hnd. apply NoDup_app_remove_r in Hnd. exact Hnd.
  Qed.

  Lemma disjoint_children v ts s s0 a :
    valid_tree (tree_cons v ts) ->
    In s ts -> In s0 ts ->
    In a (nodes_of s) -> In a (nodes_of s0) -> s = s0.
  Proof.
    cbv [valid_tree]. cbn [nodes_of]. intros H Hs Hs0 Ha Ha0.
    inversion H as [| x l Hnin Hnd Heq]. clear H.
    apply in_split in Hs0. destruct Hs0 as [l1 [l2 Heqts]]. subst ts.
    rewrite flat_map_app in Hnd. cbn [flat_map] in Hnd.
    apply in_app_or in Hs. destruct Hs as [Hs | [Hs | Hs]].
    - exfalso. apply NoDup_app_iff in Hnd. destruct Hnd as [_ [_ [Hdisj _]]].
      eapply Hdisj.
      + apply in_flat_map. exists s. split; [exact Hs | exact Ha].
      + apply in_or_app. left. exact Ha0.
    - symmetry. exact Hs.
    - exfalso. apply NoDup_app_remove_l in Hnd. apply NoDup_app_iff in Hnd.
      destruct Hnd as [_ [_ [Hdisj _]]]. eapply Hdisj.
      + exact Ha0.
      + apply in_flat_map. exists s. split; [exact Hs | exact Ha].
  Qed.

  Lemma path_last_in_nodes s a p :
    In a (nodes_of s) ->
    path (graph.edge (graph_of s)) a p ->
    In (last p a) (nodes_of s).
  Proof.
    revert a. induction p as [|b p' IH]; intros a Ha Hp.
    - simpl. exact Ha.
    - destruct Hp as [He Hp']. rewrite last_cons.
      apply IH.
      + exact (proj2 (edge_nodes s a b He)).
      + exact Hp'.
  Qed.

  (* ---------- how a path relates to the children ---------- *)

  Lemma edge_child_mono v ts s x y :
    In s ts ->
    graph.edge (graph_of s) x y ->
    graph.edge (graph_of (tree_cons v ts)) x y.
  Proof. intros Hs He. apply edge_graph_of. right. exists s. auto. Qed.

  Lemma valid_tree_graph_edge t u :
    valid_tree t ->
    graph.edge (graph_of t) (root t) u ->
    In u (map root (children t)).
  Proof.
    destruct t as [v ts]. intros Hvalid He.
    apply edge_graph_of in He. destruct He as [[_ Hb] | [s [Hs He]]].
    - exact Hb.
    - exfalso. apply (root_not_in_children v ts Hvalid).
      apply in_flat_map. exists s. split; [exact Hs | exact (proj1 (edge_nodes s v u He))].
  Qed.

  Lemma edge_in_child v ts s a b :
    valid_tree (tree_cons v ts) ->
    In s ts -> In a (nodes_of s) ->
    graph.edge (graph_of (tree_cons v ts)) a b ->
    graph.edge (graph_of s) a b.
  Proof.
    intros Hvalid Hs Ha He. apply edge_graph_of in He.
    destruct He as [[Hav _] | [s' [Hs' He]]].
    - exfalso. subst a. apply (root_not_in_children v ts Hvalid).
      apply in_flat_map. exists s. auto.
    - assert (s' = s).
      { eapply disjoint_children.
        - exact Hvalid.
        - exact Hs'.
        - exact Hs.
        - exact (proj1 (edge_nodes s' a b He)).
        - exact Ha. }
      subst s'. exact He.
  Qed.

  Lemma path_in_child v ts s a p :
    valid_tree (tree_cons v ts) ->
    In s ts -> In a (nodes_of s) ->
    path (graph.edge (graph_of (tree_cons v ts))) a p ->
    path (graph.edge (graph_of s)) a p.
  Proof.
    intros Hvalid Hs. revert a. induction p as [|b p' IH]; intros a Ha Hp.
    - exact I.
    - destruct Hp as [He Hp']. split.
      + eapply edge_in_child; eassumption.
      + apply IH.
        * exact (proj2 (edge_nodes s a b (edge_in_child v ts s a b Hvalid Hs Ha He))).
        * exact Hp'.
  Qed.

  Lemma tree_path_cons t n p' :
    valid_tree t ->
    path (graph.edge (graph_of t)) (root t) (n :: p') ->
    exists t', In t' (children t) /\ root t' = n /\ path (graph.edge (graph_of t')) n p'.
  Proof.
    destruct t as [v ts]. intros Hvalid Hpath. destruct Hpath as [He Hp].
    apply valid_tree_graph_edge in He; [ | exact Hvalid ].
    apply in_map_iff in He. destruct He as [s [Hrs Hs]].
    exists s. split; [exact Hs | split].
    - exact Hrs.
    - eapply path_in_child.
      + exact Hvalid.
      + exact Hs.
      + rewrite <- Hrs. apply nodes_of_root.
      + exact Hp.
  Qed.

  (* ---------- graph_of a valid tree is a tree ---------- *)

  Lemma graph_of_all_reachable t :
    valid_tree t ->
    all_reachable (graph.edge (graph_of t)) (root t).
  Proof.
    induction t as [v ts IH] using tree_ind. intros Hvalid. cbn [root].
    rewrite Forall_forall in IH.
    intros u b He. apply edge_graph_of in He.
    destruct He as [[Hu _] | [s [Hs He]]].
    - subst u. apply reaches_self.
    - pose proof (IH s Hs (valid_tree_child v ts s Hvalid Hs)) as Har.
      specialize (Har u b He).
      eapply reaches_step_before.
      + eapply reaches_weaken; [ | exact Har ].
        intros x y Hxy. eapply edge_child_mono; eassumption.
      + apply edge_graph_of. left. split; [reflexivity | apply in_map; exact Hs].
  Qed.

  Lemma graph_of_locally_tree t :
    valid_tree t ->
    locally_tree (graph.edge (graph_of t)) (root t).
  Proof.
    induction t as [v ts IH] using tree_ind. intros Hvalid. cbn [root].
    rewrite Forall_forall in IH.
    intros n p1 p2 [Hp1 Hl1] [Hp2 Hl2].
    destruct p1 as [|b1 p1']; destruct p2 as [|b2 p2'].
    - reflexivity.
    - exfalso. cbn [last] in Hl1.
      destruct (tree_path_cons (tree_cons v ts) b2 p2' Hvalid Hp2) as [s2 [Hs2 [Hb2 Hpath2]]].
      cbn [children] in Hs2. rewrite last_cons in Hl2.
      assert (Hin : In v (nodes_of s2)).
      { rewrite <- Hl1, Hl2. apply path_last_in_nodes.
        - rewrite <- Hb2. apply nodes_of_root.
        - exact Hpath2. }
      apply (root_not_in_children v ts Hvalid). apply in_flat_map. exists s2. auto.
    - exfalso. cbn [last] in Hl2.
      destruct (tree_path_cons (tree_cons v ts) b1 p1' Hvalid Hp1) as [s1 [Hs1 [Hb1 Hpath1]]].
      cbn [children] in Hs1. rewrite last_cons in Hl1.
      assert (Hin : In v (nodes_of s1)).
      { rewrite <- Hl2, Hl1. apply path_last_in_nodes.
        - rewrite <- Hb1. apply nodes_of_root.
        - exact Hpath1. }
      apply (root_not_in_children v ts Hvalid). apply in_flat_map. exists s1. auto.
    - destruct (tree_path_cons (tree_cons v ts) b1 p1' Hvalid Hp1) as [s1 [Hs1 [Hb1 Hpath1]]].
      destruct (tree_path_cons (tree_cons v ts) b2 p2' Hvalid Hp2) as [s2 [Hs2 [Hb2 Hpath2]]].
      cbn [children] in Hs1, Hs2. rewrite last_cons in Hl1, Hl2.
      assert (Hn1 : In n (nodes_of s1)).
      { rewrite Hl1. apply path_last_in_nodes.
        - rewrite <- Hb1. apply nodes_of_root.
        - exact Hpath1. }
      assert (Hn2 : In n (nodes_of s2)).
      { rewrite Hl2. apply path_last_in_nodes.
        - rewrite <- Hb2. apply nodes_of_root.
        - exact Hpath2. }
      assert (Hss : s1 = s2) by (eapply disjoint_children; eassumption).
      subst s2.
      rewrite <- Hb1 in Hpath1, Hl1. rewrite <- Hb2 in Hpath2, Hl2.
      pose proof (IH s1 Hs1 (valid_tree_child v ts s1 Hvalid Hs1)) as Hlt.
      assert (Hpp : p1' = p2').
      { apply (Hlt n).
        - split; [exact Hpath1 | exact Hl1].
        - split; [exact Hpath2 | exact Hl2]. }
      rewrite <- Hb1, <- Hb2, Hpp. reflexivity.
  Qed.

  Lemma graph_of_tree_is_tree t :
    valid_tree t ->
    is_tree (graph.edge (graph_of t)) (root t).
  Proof.
    intro Hvalid. cbv [is_tree]. split.
    - apply graph_of_locally_tree. exact Hvalid.
    - apply graph_of_all_reachable. exact Hvalid.
  Qed.

  Context {eqbV : Eqb V}.

  Definition tree_of (g : graph) root :=
    let '(_, tree_stack) :=
      dfs_fold (fun ts _ _ => ts) (fun ts _ _ => [] :: ts)
        (fun tss _ finished =>
           match tss with
           | ts :: ts' :: tss' => (tree_cons finished ts :: ts') :: tss'
           | _ => []
           end) g [[]] root in
    match tree_stack with
    | [[t]] => t
    | _ => tree_cons root []
    end.


  Lemma tree_of_valid_tree (g : graph) u :
    is_tree (graph.edge g) u ->
    valid_tree (tree_of g u).
  Proof. Admitted.
End __.
