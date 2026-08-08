From GraphSearch Require Import DFS GraphInterface List.
From coqutil Require Import Eqb Tactics.fwd Tactics Datatypes.List.
From Stdlib Require Import List Lia Permutation.
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
      { eapply disjoint_children; try eassumption.
        apply edge_nodes in He. fwd. assumption. }
      subst s'. exact He.
  Qed.

  Context {eqbV : Eqb V}.
  Context {eqbV_ok : Eqb_ok eqbV}.

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

  (* Along the DFS: one frame per open node plus the outer frame, and the nodes
     collected so far (in the finished trees and on the path) are exactly the
     distinct visited set. *)
  Lemma tree_of_invariant (r : V) seen tss pth (gg : graph) :
    dfs_fold_state (fun ts _ _ => ts) (fun ts _ _ => [] :: ts)
      (fun tss _ finished =>
         match tss with
         | ts :: ts' :: tss' => (tree_cons finished ts :: ts') :: tss'
         | _ => []
         end)
      r [r] ([] :: [[]]) seen tss pth gg ->
    length tss = S (length pth) /\
    NoDup (stack_nodes tss ++ pth) /\
    incl (stack_nodes tss ++ pth) seen.
  Proof.
    intros HD. induction HD.
    - ssplit.
      + reflexivity.
      + rewrite !stack_nodes_cons. cbn [flat_map app].
        apply NoDup_cons; [ intro Hc; destruct Hc | apply NoDup_nil ].
      + rewrite !stack_nodes_cons. cbn [flat_map app]. apply incl_refl.
    - cbv beta. destruct IHHD as (Hlen & Hnodup & Hincl).
      match goal with H : set_contains _ _ = false |- _ =>
        apply set_contains_false in H; rename H into Hseen end.
      assert (Hvni : ~ In v (stack_nodes st ++ (u :: p))).
      { intro Hv. apply Hseen. apply Hincl. exact Hv. }
      ssplit.
      + cbn [length] in Hlen |- *. lia.
      + rewrite stack_nodes_cons. cbn [flat_map app].
        apply (Permutation_NoDup (l := v :: stack_nodes st ++ (u :: p))).
        * apply Permutation_middle.
        * apply NoDup_cons; [ exact Hvni | exact Hnodup ].
      + rewrite stack_nodes_cons. cbn [flat_map app].
        intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
        * right. apply Hincl. apply in_or_app. left. exact Hx.
        * cbn [In] in Hx. destruct Hx as [Hv | Hx].
          -- left. exact Hv.
          -- right. apply Hincl. apply in_or_app. right. exact Hx.
    - cbv beta. exact IHHD.
    - destruct IHHD as (Hlen & Hnodup & Hincl).
      destruct st as [| ts [| ts' tss']].
      + cbn [length] in Hlen. lia.
      + cbn [length] in Hlen. lia.
      + cbv beta iota.
        assert (Hu_in : In u (stack_nodes (ts :: ts' :: tss') ++ (u :: p))).
        { apply in_or_app. right. left. reflexivity. }
        ssplit.
        * cbn [length] in Hlen |- *. lia.
        * rewrite stack_nodes_finish. cbn [app].
          apply (Permutation_NoDup (l := stack_nodes (ts :: ts' :: tss') ++ (u :: p))).
          -- apply Permutation_sym. apply Permutation_middle.
          -- exact Hnodup.
        * rewrite stack_nodes_finish. cbn [app].
          intros x Hx. destruct Hx as [Hu | Hx].
          -- subst x. apply Hincl. exact Hu_in.
          -- apply Hincl. apply in_app_or in Hx. apply in_or_app.
             destruct Hx as [Hx | Hx]; [ left; exact Hx | right; right; exact Hx ].
  Qed.

  Lemma tree_of_valid_tree (g : graph) u :
    valid_tree (tree_of g u).
  Proof.
    cbv [tree_of].
    destruct (dfs_fold (fun ts _ _ => ts) (fun ts _ _ => [] :: ts)
                (fun tss _ finished =>
                   match tss with
                   | ts :: ts' :: tss' => (tree_cons finished ts :: ts') :: tss'
                   | _ => []
                   end) g [[]] u) as [vs tss] eqn:E.
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

End __.
