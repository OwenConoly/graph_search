From GraphSearch Require Import GraphInterface Trees List Dag Examples.
From coqutil Require Import Eqb Tactics.fwd Tactics Datatypes.List.
From Stdlib Require Import List Sorting.Permutation Morphisms
  Relations.Relation_Operators Wellfounded.Transitive_Closure.
Import ListNotations.

Section __.
  Context {V : Type} {eqbV : Eqb V} {eqbV_ok : Eqb_ok eqbV}.
  Context {graph : graph.graph V} {graph_ok : graph.ok graph}.

  Lemma path_reachable_subgraph (g g' : graph) root u p :
    graph.reachable_subgraph g root g' ->
    graph.reaches g root u ->
    graph.path g u p ->
    graph.path g' u p.
  Proof.
    intros Hrs. revert u. induction p as [|x p' IH]; intros u Hrf Hp.
    - exact I.
    - destruct Hp as [He Hp']. cbn [graph.path]. split.
      + apply (proj2 (Hrs u x)). auto.
      + apply IH; eauto using graph.reaches_step.
  Qed.

  Lemma reaches_reachable_subgraph (g g' : graph) root u w :
    graph.reachable_subgraph g root g' ->
    graph.reaches g root u ->
    graph.reaches g u w ->
    graph.reaches g' u w.
  Proof.
    intros Hrs Hrf [p [Hp Hlast]]. exists p.
    split; eauto using path_reachable_subgraph.
  Qed.

  Lemma all_reachable_reachable_subgraph_self (g : graph) root :
    graph.all_reachable g root ->
    graph.reachable_subgraph g root g.
  Proof.
    intros Hall u w. split.
    - intro He. split; eauto.
    - intros [He _]. assumption.
  Qed.

  Lemma reachable_subgraph_all_reachable (g g' : graph) root :
    graph.reachable_subgraph g root g' ->
    graph.all_reachable g' root.
  Proof.
    intros Hrs u w He. apply Hrs in He. fwd.
    eapply reaches_reachable_subgraph; eauto using graph.reaches_self.
  Qed.

  Lemma reachable_subgraph_compose (g g' h : graph) root v :
    graph.reachable_subgraph g root g' ->
    graph.reaches g root v ->
    graph.reachable_subgraph g' v h ->
    graph.reachable_subgraph g v h.
  Proof.
    intros Hg Hrv Hh u w. rewrite (Hh u w), (Hg u w). split.
    - intros [[Hedge Hru] Hvu]. split.
      + assumption.
      + eapply graph.reaches_subgraph.
        * intros a b Hab. apply Hg in Hab. tauto.
        * assumption.
    - intros [Hedge Hvu]. split.
      + split.
        * assumption.
        * eapply graph.reaches_trans; eassumption.
      + eapply reaches_reachable_subgraph; eassumption.
  Qed.

  Lemma edge_confined (v : V) ts s a b :
    valid_tree (tree_cons v ts) ->
    In s ts ->
    In a (nodes_of s) ->
    graph.edge (graph_of (tree_cons v ts)) a b ->
    graph.edge (graph_of s) a b.
  Proof.
    intros Hval Hs Ha He. apply edge_graph_of in He.
    destruct He as [[Har Hb] | [s' [Hs' He]]].
    - exfalso. subst a. apply (root_not_in_children v ts Hval).
      apply in_flat_map. exists s. auto.
    - pose proof (edge_nodes s' a b He) as [Ha' _].
      assert (Hss : s = s') by (eapply disjoint_children; eassumption).
      subst s'. assumption.
  Qed.

  Lemma path_confined (v : V) ts s a p :
    valid_tree (tree_cons v ts) ->
    In s ts ->
    In a (nodes_of s) ->
    graph.path (graph_of (tree_cons v ts)) a p ->
    graph.path (graph_of s) a p /\ Forall (fun x => In x (nodes_of s)) p.
  Proof.
    intros Hval Hs. revert a. induction p as [|x p' IH]; intros a Ha Hp.
    - split; constructor.
    - destruct Hp as [He Hp'].
      assert (Hedge : graph.edge (graph_of s) a x) by (eapply edge_confined; eassumption).
      pose proof (edge_nodes s a x Hedge) as [_ Hx].
      destruct (IH x Hx Hp') as [Hpath Hall]. split.
      + cbn [graph.path]. split; assumption.
      + constructor; assumption.
  Qed.

  Lemma reaches_confined (v : V) ts s a u :
    valid_tree (tree_cons v ts) ->
    In s ts ->
    In a (nodes_of s) ->
    graph.reaches (graph_of (tree_cons v ts)) a u ->
    graph.reaches (graph_of s) a u /\ In u (nodes_of s).
  Proof.
    intros Hval Hs Ha [p [Hp Hlast]]. subst u.
    destruct (path_confined v ts s a p Hval Hs Ha Hp) as [Hpath Hall]. split.
    - exists p. split; [ assumption | reflexivity ].
    - destruct p as [|x p'].
      + assumption.
      + rewrite Forall_forall in Hall. apply Hall, In_last_cons.
  Qed.

  Lemma subgraph_child (v : V) ts s :
    In s ts ->
    graph.subgraph (graph_of s) (graph_of (tree_cons v ts)).
  Proof. intros Hs u w He. eapply edge_child_mono; eassumption. Qed.

  Lemma subtree_reachable_subgraph (t : tree V) v :
    valid_tree t ->
    In v (nodes_of t) ->
    exists t',
      valid_tree t' /\ root t' = v /\
      graph.reachable_subgraph (graph_of t) v (graph_of t').
  Proof.
    induction t as [r ts IH] using tree_ind. intros Hval Hin.
    cbn [nodes_of] in Hin. destruct Hin as [Hvr | Hin].
    - subst r. exists (tree_cons v ts). ssplit.
      + assumption.
      + reflexivity.
      + apply all_reachable_reachable_subgraph_self, all_reachable_graph_of.
    - apply in_flat_map in Hin. destruct Hin as [s [Hs Hvs]].
      rewrite Forall_forall in IH.
      destruct (IH s Hs (valid_tree_child r ts s Hval Hs) Hvs)
        as [t' [Hval' [Hroot' Hrs']]].
      exists t'. ssplit.
      + assumption.
      + assumption.
      + intros u w. rewrite (Hrs' u w). split.
        * intros [Hedge_s Hreach_s]. split.
          -- eapply edge_child_mono; eassumption.
          -- eapply graph.reaches_subgraph; eauto using subgraph_child.
        * intros [Hedge_t Hreach_t].
          destruct (reaches_confined r ts s v u Hval Hs Hvs Hreach_t) as [Hreach_s Hu_in].
          split.
          -- eapply edge_confined; eassumption.
          -- assumption.
  Qed.

  Lemma path_last_in_nodes (t : tree V) a p :
    In a (nodes_of t) ->
    graph.path (graph_of t) a p ->
    In (last p a) (nodes_of t).
  Proof.
    revert a. induction p as [|x p' IH]; intros a Ha Hp.
    - assumption.
    - destruct Hp as [He Hp']. rewrite last_cons.
      pose proof (edge_nodes t a x He) as [_ Hx]. apply IH; assumption.
  Qed.

  Lemma reaches_nodes_of (t : tree V) v :
    graph.reaches (graph_of t) (root t) v ->
    In v (nodes_of t).
  Proof.
    intros [p [Hp Hlast]]. subst v.
    eapply path_last_in_nodes; eauto using nodes_of_root.
  Qed.

  Lemma is_locally_tree_reaches (g : graph) root v :
    graph.reaches g root v ->
    graph.is_locally_tree g root ->
    graph.is_locally_tree g v.
  Proof.
    intros Hrv [g' [Hrs Hcount]].
    assert (Htree : graph.is_tree g' root).
    { split; eauto using reachable_subgraph_all_reachable. }
    apply is_tree_is_tree_alt in Htree.
    destruct Htree as [t [Hval [Hgt Hroott]]]. subst g'.
    assert (Hrv' : graph.reaches (graph_of t) root v).
    { eapply reaches_reachable_subgraph; eauto using graph.reaches_self. }
    assert (Hvin : In v (nodes_of t)).
    { apply reaches_nodes_of. rewrite <- Hroott. assumption. }
    destruct (subtree_reachable_subgraph t v Hval Hvin) as [t' [Hval' [Hroot' Hsub]]].
    exists (graph_of t'). split.
    - eapply reachable_subgraph_compose; eassumption.
    - rewrite <- Hroot'. apply is_tree_graph_of. assumption.
  Qed.

  Lemma tree_is_dag (t : tree V) :
    valid_tree t ->
    graph.is_dag (graph_of t).
  Proof.
    induction t as [r ts IH] using tree_ind. intros Hval x.
    rewrite Forall_forall in IH.
    assert (Htrans : forall s z,
               In s ts -> In z (nodes_of s) ->
               Acc (fun a b => graph.edge (graph_of s) b a) z ->
               Acc (fun a b => graph.edge (graph_of (tree_cons r ts)) b a) z).
    { intros s z Hs Hz Hacc.
      eapply subrel_Acc_strong with (P := fun w => In w (nodes_of s)).
      - exact Hacc.
      - exact Hz.
      - intros a b Hab Hb.
        assert (Hedge : graph.edge (graph_of s) b a) by (eapply edge_confined; eassumption).
        split; [ exact Hedge | exact (proj2 (edge_nodes s b a Hedge)) ]. }
    constructor. intros y Hy. apply edge_graph_of in Hy.
    destruct Hy as [[_ Hy] | [s [Hs Hxy]]].
    - apply in_map_iff in Hy. destruct Hy as [s' [Hroot Hs']]. subst y.
      apply Htrans with (s := s').
      + exact Hs'.
      + apply nodes_of_root.
      + apply IH; [ exact Hs' | eapply valid_tree_child; eassumption ].
    - pose proof (edge_nodes s x y Hxy) as [_ Hy_in].
      apply Htrans with (s := s).
      + exact Hs.
      + exact Hy_in.
      + apply IH; [ exact Hs | eapply valid_tree_child; eassumption ].
  Qed.

  Lemma is_locally_dag_alt (g g' : graph) root :
    graph.reachable_subgraph g root g' ->
    graph.is_dag g' ->
    graph.is_locally_dag g root.
  Proof.
    intros Hrs Hdag.
    eapply subrel_Acc_strong
      with (R2 := fun x y => graph.edge g' y x) (P := graph.reaches g root).
    - apply Hdag.
    - apply graph.reaches_self.
    - intros x y Hxy Hy. split.
      + apply (proj2 (Hrs y x)). split; [ exact Hxy | exact Hy ].
      + eapply graph.reaches_step; eassumption.
  Qed.

  Lemma is_locally_tree_is_locally_dag (g : graph) root :
    graph.is_locally_tree g root ->
    graph.is_locally_dag g root.
  Proof.
    intros [g' [Hrs Hcount]]. eapply is_locally_dag_alt; [ exact Hrs | ].
    assert (Htree : graph.is_tree g' root)
      by (split; [ eapply reachable_subgraph_all_reachable; exact Hrs | exact Hcount ]).
    apply is_tree_is_tree_alt in Htree.
    destruct Htree as [t [Hval [Hgt Hroott]]]. subst g'.
    exact (tree_is_dag t Hval).
  Qed.

  Lemma reaches_clos_trans (g : graph) a b :
    graph.reaches g a b ->
    a = b \/ clos_trans V (fun x y => graph.edge g y x) b a.
  Proof.
    intros [p [Hp Hlast]]. subst b. revert a Hp.
    induction p as [|x p' IH]; intros a Hp.
    - left. reflexivity.
    - destruct Hp as [He Hp']. rewrite last_cons. right.
      destruct (IH x Hp') as [Hx | Hct].
      + rewrite <- Hx. apply t_step. exact He.
      + eapply t_trans; [ exact Hct | apply t_step; exact He ].
  Qed.

  Lemma is_locally_tree_no_return (g : graph) root u w :
    graph.is_locally_tree g root ->
    graph.reaches g root u ->
    graph.edge g u w ->
    ~ graph.reaches g w u.
  Proof.
    intros Hlt Hru Hedge Hwu.
    pose proof (is_locally_tree_is_locally_dag g u
                  (is_locally_tree_reaches g root u Hru Hlt)) as Hacc.
    eapply Acc_not_symm with (x := u).
    - apply Acc_clos_trans. exact Hacc.
    - destruct (reaches_clos_trans g w u Hwu) as [Hwu_eq | Hct].
      + subst w. apply t_step. exact Hedge.
      + eapply t_trans; [ exact Hct | apply t_step; exact Hedge ].
  Qed.

  Lemma reaches_first_step (g : graph) u w :
    u <> w ->
    graph.reaches g u w ->
    exists v, graph.edge g u v /\ graph.reaches g v w.
  Proof.
    intros Hne [p [Hp Hlast]]. destruct p as [|x p'].
    - simpl in Hlast. congruence.
    - destruct Hp as [He Hp']. exists x. split.
      + exact He.
      + exists p'. split; [ exact Hp' | ]. rewrite last_cons in Hlast. exact Hlast.
  Qed.

  Lemma reaches_child_unique (g : graph) v target v1 v2 :
    graph.is_locally_tree g v ->
    graph.edge g v v1 -> graph.reaches g v1 target ->
    graph.edge g v v2 -> graph.reaches g v2 target ->
    v1 = v2.
  Proof.
    intros [g' [Hrs Hcount]] He1 Hr1 He2 Hr2.
    assert (Htree : graph.is_tree g' v)
      by (split; [ eapply reachable_subgraph_all_reachable; exact Hrs | exact Hcount ]).
    apply is_tree_is_tree_alt in Htree.
    destruct Htree as [t [Hval [Hgt Hroot]]]. subst g'.
    assert (Hself : graph.reaches g v v) by apply graph.reaches_self.
    assert (He1' : graph.edge (graph_of t) v v1)
      by (apply (proj2 (Hrs v v1)); split; [ exact He1 | exact Hself ]).
    assert (He2' : graph.edge (graph_of t) v v2)
      by (apply (proj2 (Hrs v v2)); split; [ exact He2 | exact Hself ]).
    assert (Hr1' : graph.reaches (graph_of t) v1 target).
    { eapply reaches_reachable_subgraph;
        [ exact Hrs
        | eapply graph.reaches_step; [ apply graph.reaches_self | exact He1 ]
        | exact Hr1 ]. }
    assert (Hr2' : graph.reaches (graph_of t) v2 target).
    { eapply reaches_reachable_subgraph;
        [ exact Hrs
        | eapply graph.reaches_step; [ apply graph.reaches_self | exact He2 ]
        | exact Hr2 ]. }
    destruct t as [r ts]. cbn [root] in Hroot. subst r.
    apply edge_graph_of in He1'. apply edge_graph_of in He2'.
    destruct He1' as [[_ Hin1] | [s [Hs He1s]]].
    2:{ exfalso. pose proof (edge_nodes s v v1 He1s) as [Hv_in _].
        apply (root_not_in_children v ts Hval). apply in_flat_map.
        exists s. split; [ exact Hs | exact Hv_in ]. }
    destruct He2' as [[_ Hin2] | [s [Hs He2s]]].
    2:{ exfalso. pose proof (edge_nodes s v v2 He2s) as [Hv_in _].
        apply (root_not_in_children v ts Hval). apply in_flat_map.
        exists s. split; [ exact Hs | exact Hv_in ]. }
    apply in_map_iff in Hin1. destruct Hin1 as [s1 [Hr1eq Hs1]].
    apply in_map_iff in Hin2. destruct Hin2 as [s2 [Hr2eq Hs2]].
    subst v1 v2.
    pose proof (reaches_confined v ts s1 (root s1) target Hval Hs1 (nodes_of_root s1) Hr1')
      as [_ Ht1].
    pose proof (reaches_confined v ts s2 (root s2) target Hval Hs2 (nodes_of_root s2) Hr2')
      as [_ Ht2].
    assert (s1 = s2) by (eapply disjoint_children; eassumption).
    subst s2. reflexivity.
  Qed.

  Context {X : Type}.

  Definition pebble_step (g : graph) (v : V) (ps1 ps2 : list (V * X)) : Prop :=
    exists rest x,
      Permutation ps1 ((v, x) :: rest) /\
      Permutation ps2 (map (fun v' => (v', x)) (graph.edges g v) ++ rest).

  Definition graph_incoming (g : graph) (target : V) (ps : list (V * X)) : list X :=
    map snd (filter (fun '(v, _) => graph.reachesb g v target) ps).

  #[export] Instance Permutation_graph_incoming (g : graph) (target : V) :
    Proper (@Permutation _ ==> @Permutation _) (graph_incoming g target).
  Proof.
    intros ps ps' Hp. cbv [graph_incoming].
    apply Permutation_map. apply Permutation_filter. exact Hp.
  Qed.

  Lemma graph_incoming_app (g : graph) target ps1 ps2 :
    graph_incoming g target (ps1 ++ ps2)
    = graph_incoming g target ps1 ++ graph_incoming g target ps2.
  Proof.
    cbv [graph_incoming]. rewrite filter_app, map_app. reflexivity.
  Qed.

  Lemma graph_incoming_cons (g : graph) target v x rest :
    graph_incoming g target ((v, x) :: rest)
    = (if graph.reachesb g v target then [x] else []) ++ graph_incoming g target rest.
  Proof.
    cbv [graph_incoming]. cbn [filter]. destruct (graph.reachesb g v target); reflexivity.
  Qed.

  Lemma graph_incoming_map_pair (g : graph) target x l :
    graph_incoming g target (map (fun v' => (v', x)) l)
    = map (fun _ => x) (filter (fun v' => graph.reachesb g v' target) l).
  Proof.
    induction l as [|v' l' IH]; [ reflexivity | ].
    cbn [map]. rewrite graph_incoming_cons, IH.
    cbn [filter]. destruct (graph.reachesb g v' target); reflexivity.
  Qed.

  Lemma graph_incoming_pebble_step (g : graph) v target ps1 ps2 :
    graph.is_locally_tree g v ->
    v <> target ->
    pebble_step g v ps1 ps2 ->
    Permutation (graph_incoming g target ps1) (graph_incoming g target ps2).
  Proof.
    intros Htree Hne [rest [x [Hp1 Hp2]]].
    rewrite Hp1, Hp2.
    rewrite graph_incoming_cons, graph_incoming_app, graph_incoming_map_pair.
    apply Permutation_app_tail.
    destr (graph.reachesb g v target).
    - destruct (reaches_first_step g v target Hne E) as [c [Hedge_c Hreach_c]].
      erewrite filter_eq_singleton.
      + simpl. reflexivity.
      + apply graph.edges_NoDup.
      + eassumption.
      + destr (graph.reachesb g c target); [ reflexivity | contradiction ].
      + intros. fwd. eapply reaches_child_unique; eassumption.
    - rewrite filter_eq_nil.
      + simpl. reflexivity.
      + intros a Ha. destr (graph.reachesb g a target); auto.
        exfalso. apply E. eapply graph.reaches_step_before; eassumption.
  Qed.
End __.
