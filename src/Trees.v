From GraphSearch Require Import DFS GraphInterface List.
From coqutil Require Import Eqb Tactics.fwd Tactics Datatypes.List Datatypes.ListSet.
From Stdlib Require Import List Lia Permutation.
Import ListNotations.

Section __.
  Context {V : Type} {eqbV : Eqb V} {eqbV_ok : Eqb_ok eqbV}.
  Context {graph : graph.graph V} {graph_ok : graph.ok graph}.

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

  Lemma edge_graph_of v ts a b :
    graph.edge (graph_of (tree_cons v ts)) a b <->
    (a = v /\ In b (map root ts)) \/ (exists s, In s ts /\ graph.edge (graph_of s) a b).
  Proof.
    cbn [graph_of]. rewrite graph.edge_union.
    assert (H1 : graph.edge (graph.put_edges graph.empty v (map root ts)) a b <->
                 a = v /\ In b (map root ts)).
    { rewrite graph.edge_put_edges, graph.edge_empty_iff. graph. }
    assert (H2 : graph.edge (fold_left graph.union (map graph_of ts) graph.empty) a b <->
                 exists s, In s ts /\ graph.edge (graph_of s) a b).
    { rewrite graph.edge_fold_union. split.
      - intros [He | [g [Hg He]]].
        + exfalso. exact (graph.edge_empty _ _ He).
        + apply in_map_iff in Hg. destruct Hg as [s [Hgs Hin]]. subst g. exists s. auto.
      - intros [s [Hs He]]. right. eexists. rewrite in_map_iff. graph. }
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

  Lemma edge_child_mono v ts s x y :
    In s ts ->
    graph.edge (graph_of s) x y ->
    graph.edge (graph_of (tree_cons v ts)) x y.
  Proof. intros Hs He. apply edge_graph_of. right. exists s. auto. Qed.

  Definition on_untree_edge (ts : list (list tree)) (_ : list V) (_ : V) := ts.
  Definition on_tree_edge (ts : list (list tree)) (_ : list V) (_ : V) := [] :: ts.
  Definition on_finish (tss : list (list tree)) (_ : list V) (finished : V) :=
    match tss with
    | ts :: ts' :: tss' => (tree_cons finished ts :: ts') :: tss'
    | _ => []
    end.

  Definition tree_of (g : graph) root :=
    let '(_, tree_stack) :=
      dfs_fold on_untree_edge on_tree_edge on_finish g [[]] root in
    match tree_stack with
    | [[t]] => t
    | _ => tree_cons root []
    end.

  (* nodes appearing in every tree across every frame of the DFS stack *)
  Definition stack_nodes (tss : list (list tree)) : list V :=
    flat_map (flat_map nodes_of) tss.

  Lemma stack_nodes_cons f tss :
    stack_nodes (f :: tss) = flat_map nodes_of f ++ stack_nodes tss.
  Proof. reflexivity. Qed.

  Lemma stack_nodes_finish u ts ts' tss' :
    stack_nodes ((tree_cons u ts :: ts') :: tss') = u :: stack_nodes (ts :: ts' :: tss').
  Proof.
    rewrite !stack_nodes_cons. cbn [flat_map nodes_of]. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma stack_nodes_single t :
    stack_nodes [[t]] = nodes_of t.
  Proof. cbv [stack_nodes]. cbn [flat_map]. rewrite !app_nil_r. reflexivity. Qed.

  (* Along the DFS: one frame per open node plus the outer frame, and the nodes
     collected so far (in the finished trees and on the path) are exactly the
     distinct visited set. *)
  Lemma tree_of_invariant (r : V) seen tss pth (gg : graph) :
    dfs_fold_state on_untree_edge on_tree_edge on_finish
      r [r] ([] :: [[]]) seen tss pth gg ->
    length tss = S (length pth) /\
    NoDup (stack_nodes tss ++ pth) /\
    same_set (stack_nodes tss ++ pth) seen.
  Proof.
    intros HD. induction HD.
    - ssplit.
      + reflexivity.
      + rewrite !stack_nodes_cons. cbn [flat_map app].
        apply NoDup_cons; [ intro Hc; destruct Hc | apply NoDup_nil ].
      + rewrite !stack_nodes_cons. cbn [flat_map app]. apply same_set_refl.
    - cbv [on_tree_edge]. destruct IHHD as (Hlen & Hnodup & Hsame).
      match goal with H : set_contains _ _ = false |- _ =>
        apply set_contains_false in H; rename H into Hseen end.
      assert (Hvni : ~ In v (stack_nodes st ++ (u :: p))).
      { intro Hv. apply Hseen. apply (proj1 (Hsame v)). exact Hv. }
      ssplit.
      + cbn [length] in Hlen |- *. lia.
      + rewrite stack_nodes_cons. cbn [flat_map app].
        apply (Permutation_NoDup (l := v :: stack_nodes st ++ (u :: p))).
        * apply Permutation_middle.
        * apply NoDup_cons; [ exact Hvni | exact Hnodup ].
      + rewrite stack_nodes_cons. cbn [flat_map app].
        cbv [same_set] in Hsame |- *. intro a. specialize (Hsame a).
        rewrite !in_app_iff in Hsame |- *. cbn [In] in Hsame |- *. tauto.
    - cbv [on_untree_edge]. exact IHHD.
    - destruct IHHD as (Hlen & Hnodup & Hsame).
      destruct st as [| ts [| ts' tss']].
      + cbn [length] in Hlen. lia.
      + cbn [length] in Hlen. lia.
      + cbv [on_finish].
        assert (Hu_in : In u (stack_nodes (ts :: ts' :: tss') ++ (u :: p))).
        { apply in_or_app. right. left. reflexivity. }
        ssplit.
        * cbn [length] in Hlen |- *. lia.
        * rewrite stack_nodes_finish. cbn [app].
          apply (Permutation_NoDup (l := stack_nodes (ts :: ts' :: tss') ++ (u :: p))).
          -- apply Permutation_sym. apply Permutation_middle.
          -- exact Hnodup.
        * rewrite stack_nodes_finish. cbn [app].
          cbv [same_set] in Hsame |- *. intro a. specialize (Hsame a).
          rewrite in_app_iff in Hsame. cbn [In] in Hsame |- *. rewrite in_app_iff. tauto.
  Qed.

  Lemma tree_of_valid_tree (g : graph) u :
    valid_tree (tree_of g u).
  Proof.
    cbv [tree_of].
    destruct (dfs_fold on_untree_edge on_tree_edge on_finish g [[]] u) as [vs tss] eqn:E.
    apply dfs_fold_spec in E. fwd.
    simpl in Ep1. apply tree_of_invariant in Ep1. fwd.
    rewrite app_nil_r in Ep1p1.
    destruct tss as [| fr [| fr' tss']].
    - cbn [length] in Ep1p0. lia.
    - destruct fr as [| t [| t' fr'']].
      + cbv [valid_tree]. cbn [nodes_of flat_map].
        apply NoDup_cons; [ intro Hc; destruct Hc | apply NoDup_nil ].
      + cbv [valid_tree]. rewrite !stack_nodes_cons in Ep1p1. cbn [flat_map app] in Ep1p1.
        rewrite !app_nil_r in Ep1p1. exact Ep1p1.
      + cbv [valid_tree]. cbn [nodes_of flat_map].
        apply NoDup_cons; [ intro Hc; destruct Hc | apply NoDup_nil ].
    - cbn [length] in Ep1p0. lia.
  Qed.

  Definition graph_of_forest (ts : list tree) : graph :=
    fold_left graph.union (map graph_of ts) graph.empty.

  Lemma edge_graph_of_forest ts a b :
    graph.edge (graph_of_forest ts) a b <-> exists t, In t ts /\ graph.edge (graph_of t) a b.
  Proof.
    unfold graph_of_forest. rewrite graph.edge_fold_union. split.
    - intros [He | [gg [Hgg He]]].
      + destruct (graph.edge_empty _ _ He).
      + apply in_map_iff in Hgg. fwd. eauto.
    - intros. fwd. setoid_rewrite in_map_iff. eauto 6.
  Qed.

  Lemma graph_of_leaf v :
    graph_of (tree_cons v []) = graph.empty.
  Proof.
    apply graph.graph_ext. intros a b. rewrite graph.edge_empty_iff, edge_graph_of.
    cbn [map In]. graph.
  Qed.

  Lemma edge_graph_of_cons w c cs a b :
    graph.edge (graph_of (tree_cons w (c :: cs))) a b <->
      graph.edge (graph_of (tree_cons w cs)) a b \/ graph.edge (graph_of c) a b \/ (a = w /\ b = root c).
  Proof.
    rewrite !edge_graph_of. cbn [map In]. graph.
  Qed.

  Lemma edge_graph_of_forest_cons c cs a b :
    graph.edge (graph_of_forest (c :: cs)) a b <->
      graph.edge (graph_of c) a b \/ graph.edge (graph_of_forest cs) a b.
  Proof. rewrite !edge_graph_of_forest. cbn [In]. graph. Qed.

  (* Edges of the forest obtained by finishing the whole remaining DFS path. *)
  Fixpoint pedge (pth : list V) (tss : list (list tree)) (a b : V) : Prop :=
    match pth, tss with
    | n :: pth', f :: tss' =>
        graph.edge (graph_of (tree_cons n f)) a b
        \/ (match pth' with n' :: _ => a = n' /\ b = n | [] => False end)
        \/ pedge pth' tss' a b
    | [], f :: _ => graph.edge (graph_of_forest f) a b
    | _, _ => False
    end.

  Lemma pedge_sound root vs tss pth g' :
    dfs_fold_state on_untree_edge on_tree_edge on_finish
      root [root] ([] :: [[]]) vs tss pth g' ->
    forall a b, pedge pth tss a b -> graph.edge g' a b.
  Proof.
    intros HD. induction HD; intros a b Hp.
    - cbn [pedge graph_of_forest map fold_left] in Hp.
      rewrite graph_of_leaf, !graph.edge_empty_iff in Hp. tauto.
    - cbv [on_tree_edge] in Hp. cbn [pedge] in Hp.
      rewrite graph_of_leaf, graph.edge_empty_iff in Hp. rewrite graph.edge_put.
      graph.
    - cbv [on_untree_edge] in Hp. rewrite graph.edge_put. graph.
    - cbv [on_finish] in Hp. repeat Tactics.destruct_one_match_hyp; simpl in *;
        try solve [destruct p; contradiction].
      apply IHHD. destruct p; cbn [pedge] in *.
      + rewrite edge_graph_of_forest_cons in Hp. tauto.
      + rewrite edge_graph_of_cons in Hp. tauto.
  Qed.

  Lemma edge_leaf_False r a b :
    graph.edge (graph_of (tree_cons r [])) a b -> False.
  Proof.
    intro He. apply edge_graph_of in He. graph.
  Qed.

  Lemma graph_of_tree_of_subgraph g u :
    graph.subgraph (graph_of (tree_of g u)) g.
  Proof.
    cbv [tree_of]. Tactics.destruct_one_match.
    apply dfs_fold_spec in E. fwd. simpl in Ep1.
    intros a b He. apply Ep0.
    eapply pedge_sound; [ exact Ep1 | ].
    repeat Tactics.destruct_one_match_hyp;
        try solve [exfalso; eauto using edge_leaf_False].
    simpl. apply edge_graph_of_forest_cons. auto.
  Qed.

  Definition is_tree_alt g r :=
    exists t, valid_tree t /\ g = graph_of t /\ r = root t.

  Lemma all_reachable_graph_of t :
    graph.all_reachable (graph_of t) (root t).
  Proof.
    induction t as [v ts IH] using tree_ind.
    intros u w He. cbn [root] in *.
    apply edge_graph_of in He. destruct He as [[Hu Hw] | [s [Hs He]]].
    - subst u. apply graph.reaches_self.
    - rewrite Forall_forall in IH. specialize (IH s Hs u w He).
      eapply graph.reaches_step_before.
      + eapply graph.reaches_subgraph; [ | exact IH ].
        intros x y Hxy. eapply edge_child_mono; eauto.
      + apply edge_graph_of. left. split; [ reflexivity | ].
        apply in_map_iff. exists s. auto.
  Qed.

  Lemma node_is_target_or_root t x :
    In x (nodes_of t) ->
    x = root t \/ exists u, graph.edge (graph_of t) u x.
  Proof.
    induction t as [v ts IH] using tree_ind. cbn [nodes_of root]. intros [Hx | Hx].
    - left. congruence.
    - right. apply in_flat_map in Hx. destruct Hx as [s [Hs Hxs]].
      rewrite Forall_forall in IH. specialize (IH s Hs Hxs).
      destruct IH as [Hx | [u Hu]].
      + exists v. apply edge_graph_of. left. split; [ reflexivity | ].
        subst x. apply in_map_iff. exists s. auto.
      + exists u. eapply edge_child_mono; eauto.
  Qed.

  Lemma root_not_target t u :
    valid_tree t ->
    ~ graph.edge (graph_of t) u (root t).
  Proof.
    destruct t as [v ts]. cbn [root]. intros Hv He.
    apply edge_graph_of in He. destruct He as [[Hu Hb] | [s [Hs He]]].
    - apply in_map_iff in Hb. fwd. subst.
      eapply root_not_in_children; try eassumption.
      apply in_flat_map. eexists. split; [eassumption|]. apply nodes_of_root.
    - apply edge_nodes in He. apply (root_not_in_children v ts Hv).
      apply in_flat_map. fwd. eauto.
  Qed.

  Lemma unique_parent t u1 u2 x :
    valid_tree t ->
    graph.edge (graph_of t) u1 x ->
    graph.edge (graph_of t) u2 x ->
    u1 = u2.
  Proof.
    revert u1 u2 x. induction t as [v ts IH] using tree_ind. intros u1 u2 x Hv He1 He2.
    rewrite Forall_forall in IH.
    apply edge_graph_of in He1. apply edge_graph_of in He2.
    destruct He1 as [[Hu1 Hx1] | [s1 [Hs1 He1]]];
      destruct He2 as [[Hu2 Hx2] | [s2 [Hs2 He2]]].
    - congruence.
    - exfalso. apply in_map_iff in Hx1. destruct Hx1 as [s0 [Hr Hs0]].
      assert (Hss : s0 = s2).
      { eapply disjoint_children with (a := x); try eassumption.
        - rewrite <- Hr. apply nodes_of_root.
        - exact (proj2 (edge_nodes s2 u2 x He2)). }
      subst s0. apply (root_not_target s2 u2 (valid_tree_child v ts s2 Hv Hs2)).
      rewrite Hr. exact He2.
    - exfalso. apply in_map_iff in Hx2. destruct Hx2 as [s0 [Hr Hs0]].
      assert (Hss : s0 = s1).
      { eapply disjoint_children with (a := x); try eassumption.
        - rewrite <- Hr. apply nodes_of_root.
        - exact (proj2 (edge_nodes s1 u1 x He1)). }
      subst s0. apply (root_not_target s1 u1 (valid_tree_child v ts s1 Hv Hs1)).
      rewrite Hr. exact He1.
    - assert (Hss : s1 = s2).
      { eapply disjoint_children with (a := x); try eassumption.
        - exact (proj2 (edge_nodes s1 u1 x He1)).
        - exact (proj2 (edge_nodes s2 u2 x He2)). }
      subst s2. eapply (IH s1 Hs1).
      + eapply valid_tree_child; eassumption.
      + exact He1.
      + exact He2.
  Qed.

  Lemma num_nodes_graph_of t :
    valid_tree t ->
    graph.num_nodes (graph_of t) (root t) = length (nodes_of t).
  Proof.
    intro Hv. unfold graph.num_nodes. apply NoDup_same_length.
    - apply list_union_preserves_NoDup. apply graph.all_nodes_NoDup.
    - exact Hv.
    - intro x. rewrite In_list_union_spec, graph.all_nodes_spec. cbn [In]. split.
      + intros [[Hx | []] | [u [He | He]]].
        * subst x. apply nodes_of_root.
        * apply edge_nodes in He. fwd. assumption.
        * apply edge_nodes in He. fwd. assumption.
      + intro Hx. apply node_is_target_or_root in Hx. graph.
  Qed.

  Lemma num_edges_graph_of t :
    valid_tree t ->
    graph.num_edges (graph_of t) = length (flat_map nodes_of (children t)).
  Proof.
    intro Hv. unfold graph.num_edges.
    rewrite <- (length_map snd (graph.all_edges (graph_of t))).
    apply NoDup_same_length.
    - apply FinFun.Injective_map_NoDup_in; [ | apply graph.all_edges_NoDup ].
      intros [u1 w1] [u2 w2] Hin1 Hin2 Hsnd. cbn in Hsnd. subst w2.
      rewrite graph.In_all_edges in Hin1, Hin2. f_equal.
      eapply unique_parent; eassumption.
    - destruct t as [v ts]. cbn [children]. cbv [valid_tree] in Hv. cbn [nodes_of] in Hv.
      apply NoDup_cons_iff in Hv. exact (proj2 Hv).
    - intro x. rewrite graph.In_map_snd_all_edges. destruct t as [v ts]. cbn [children]. split.
      + intros [u He]. pose proof (edge_nodes _ _ _ He) as Hn. cbn [nodes_of] in Hn.
        destruct Hn as [_ Hx]. cbn [In] in Hx. destruct Hx as [Hx | Hx].
        * exfalso. subst x. apply (root_not_target (tree_cons v ts) u Hv). exact He.
        * exact Hx.
      + intro Hx.
        assert (Hin : In x (nodes_of (tree_cons v ts))) by (cbn [nodes_of]; right; exact Hx).
        destruct (node_is_target_or_root (tree_cons v ts) x Hin) as [Hr | [u Hu]].
        * exfalso. cbn [root] in Hr. subst x. apply (root_not_in_children v ts Hv). exact Hx.
        * exists u. exact Hu.
  Qed.

  Lemma is_tree_graph_of t :
    valid_tree t ->
    S (graph.num_edges (graph_of t)) = graph.num_nodes (graph_of t) (root t).
  Proof.
    intro Hv.
    rewrite num_nodes_graph_of by exact Hv.
    rewrite num_edges_graph_of by exact Hv.
    destruct t as [v ts]. cbn [nodes_of children]. reflexivity.
  Qed.

  (* The finished tree rooted at r sits alone in the outer frame once the DFS
     path is empty; while the path is nonempty its deepest node is r and the
     outer (bottom) frame is still empty. *)
  Definition root_inv (r : V) (pth : list V) (tss : list (list tree)) : Prop :=
    length tss = S (length pth) /\
    match pth with
    | [] => exists t, tss = [[t]] /\ root t = r
    | _ :: _ => last pth r = r /\ last tss [] = []
    end.

  Lemma tree_of_root_invariant (r : V) seen tss pth (gg : graph) :
    dfs_fold_state on_untree_edge on_tree_edge on_finish
      r [r] ([] :: [[]]) seen tss pth gg ->
    root_inv r pth tss.
  Proof.
    intros HD. induction HD.
    - cbv [root_inv]. split; [ reflexivity | ]. split; reflexivity.
    - cbv [on_tree_edge root_inv] in IHHD |- *. destruct IHHD as [Hlen Hrest]. split.
      + cbn [length] in Hlen |- *. lia.
      + destruct Hrest as [Hlp Hlt]. split.
        * rewrite last_cons. rewrite (last_cons_last_cons _ u p v r). exact Hlp.
        * rewrite last_cons. exact Hlt.
    - cbv [on_untree_edge]. exact IHHD.
    - cbv [root_inv] in IHHD |- *. destruct IHHD as [Hlen Hrest]. destruct p as [| u' p'].
      + destruct st as [| f0 [| f1 st']].
        1,2: cbn [length] in Hlen; lia.
        assert (st' = []).
        { destruct st' as [| a st'']; [ reflexivity | cbn [length] in Hlen; lia ]. }
        subst st'. destruct Hrest as [Hlp Hlt].
        cbn [last] in Hlp, Hlt. subst u. subst f1.
        cbv [on_finish]. split.
        * reflexivity.
        * exists (tree_cons r f0). split; reflexivity.
      + destruct st as [| f0 [| f1 st']].
        1,2: cbn [length] in Hlen; lia.
        assert (Hst' : st' <> []).
        { intro. subst st'. cbn [length] in Hlen. lia. }
        destruct Hrest as [Hlp Hlt]. cbv [on_finish]. split.
        * cbn [length] in Hlen |- *. lia.
        * split.
          -- rewrite last_cons in Hlp. rewrite (last_cons_last_cons _ u' p' u r) in Hlp.
             exact Hlp.
          -- rewrite (last_cons_nonempty _ (tree_cons u f0 :: f1) st' [] Hst').
             rewrite (last_cons_nonempty _ f0 (f1 :: st') []) in Hlt by discriminate.
             rewrite (last_cons_nonempty _ f1 st' [] Hst') in Hlt. exact Hlt.
  Qed.

  Lemma root_tree_of g u :
    root (tree_of g u) = u.
  Proof.
    cbv [tree_of]. Tactics.destruct_one_match.
    apply dfs_fold_spec in E. fwd. apply tree_of_root_invariant in Ep1.
    cbv [root_inv] in Ep1. fwd. reflexivity.
  Qed.

  Lemma is_tree_alt_is_tree g root :
    is_tree_alt g root ->
    graph.is_tree g root.
  Proof.
    cbv [is_tree_alt graph.is_tree]. intros. fwd. split.
    - apply all_reachable_graph_of.
    - apply is_tree_graph_of. assumption.
  Qed.

  Lemma nodes_of_tree_of g root :
    exists g',
      graph.reachable_subgraph g root g' /\
        forall n, In n (nodes_of (tree_of g root)) <-> In n (root :: graph.all_nodes g').
  Proof.
    cbv [tree_of].
    destruct (dfs_fold on_untree_edge on_tree_edge on_finish g [[]] root) as [vs tss] eqn:E.
    apply dfs_fold_spec in E. fwd.
    exists g'. split; [ exact Ep0 | ].
    pose proof Ep1 as Hvs. apply dfs_fold_state_vs_good in Hvs.
    pose proof Ep1 as Hr. apply tree_of_root_invariant in Hr. cbv [root_inv] in Hr. fwd.
    apply tree_of_invariant in Ep1. fwd.
    rewrite app_nil_r, stack_nodes_single in Ep1p2.
    intro n. cbn [nodes_of]. cbv [same_set] in Ep1p2, Hvs.
    rewrite (Ep1p2 n), (Hvs n). reflexivity.
  Qed.

  Lemma num_nodes_tree_of g root :
    graph.all_reachable g root ->
    length (nodes_of (tree_of g root)) = graph.num_nodes g root.
  Proof.
    intro Hall. destruct (nodes_of_tree_of g root) as [g' [Hrs Hnodes]].
    pose proof (graph.reachable_subgraph_all g root g' Hall Hrs) as Hg'. subst g'.
    unfold graph.num_nodes. apply NoDup_same_length.
    - exact (tree_of_valid_tree g root).
    - apply list_union_preserves_NoDup. apply graph.all_nodes_NoDup.
    - intro n. rewrite Hnodes, In_list_union_spec. cbn [In]. tauto.
  Qed.

  Lemma round_trip g u :
    graph.is_tree g u ->
    graph_of (tree_of g u) = g.
  Proof.
    intro Htree. pose proof Htree as Htree'. cbv [graph.is_tree] in Htree'.
    destruct Htree' as [Hall Hcount].
    apply graph.subgraph_eq; [ apply graph_of_tree_of_subgraph | ].
    pose proof (is_tree_graph_of (tree_of g u) (tree_of_valid_tree g u)) as Hcnt.
    rewrite (num_nodes_graph_of _ (tree_of_valid_tree g u)) in Hcnt.
    rewrite (num_nodes_tree_of g u Hall) in Hcnt. lia.
  Qed.

  Lemma is_tree_is_tree_alt g root :
    graph.is_tree g root ->
    is_tree_alt g root.
  Proof.
    intro Htree. cbv [is_tree_alt]. exists (tree_of g root). ssplit.
    - apply tree_of_valid_tree.
    - symmetry. apply round_trip. exact Htree.
    - symmetry. apply root_tree_of.
  Qed.

  Corollary many_edges g root :
    graph.all_reachable g root ->
    graph.num_nodes g root <= S (graph.num_edges g).
  Proof.
    intro Hall.
    pose proof (is_tree_graph_of (tree_of g root) (tree_of_valid_tree g root)) as Hcnt.
    rewrite (num_nodes_graph_of _ (tree_of_valid_tree g root)) in Hcnt.
    rewrite (num_nodes_tree_of g root Hall) in Hcnt.
    pose proof (graph.subgraph_num_edges _ _ (graph_of_tree_of_subgraph g root)) as Hmono.
    lia.
  Qed.
End __.
