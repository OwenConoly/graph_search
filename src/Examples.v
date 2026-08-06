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
  Proof. intros HP Hiff. destruct HP; constructor; tauto. Qed.

  Lemma empty_graph_empty_path (root : V) p :
    path (graph.edge graph.empty) root p ->
    p = [].
  Proof.
    destruct p; auto. simpl. intros H. fwd.
    apply graph.edge_empty in Hp0. contradiction.
  Qed.

  Lemma locally_tree_empty (root : V) :
    locally_tree (graph.edge graph.empty) root.
  Proof.
    cbv [locally_tree path_to]. intros n p1 p2 H1 H2. fwd.
    apply empty_graph_empty_path in H1p0, H2p0. subst. reflexivity.
  Qed.

  Hint Resolve reaches_step : core.
  Lemma reachable_subgraph_path (g g' : graph) root :
    reachable_subgraph root g' g ->
    forall first p,
      reaches (graph.edge g) root first ->
      path (graph.edge g) first p ->
      path (graph.edge g') first p.
  Proof.
    intros Hsub first p. revert first.
    induction p; intros first Hreach Hpath; auto.
    simpl in *. fwd. split; eauto. apply Hsub. auto.
  Qed.

  Lemma locally_tree_reachable_subgraph (g g' : graph) (root : V) :
    reachable_subgraph root g' g ->
    locally_tree (graph.edge g') root ->
    locally_tree (graph.edge g) root.
  Proof.
    intros Hsub.
    cbv [locally_tree path_to]. intros. fwd.
    eauto 6 using reachable_subgraph_path, reaches_self.
  Qed.

  Lemma locally_tree_put_unseen (g : graph) u v (root : V) :
    u <> v ->
    ~In v (graph.all_nodes g) ->
    locally_tree (graph.edge g) root ->
    locally_tree (graph.edge (graph.put g u v)) root.
  Proof.
    intros Huv Hin Hout. cbv [locally_tree]. intros.
    cbv [path_to] in *. fwd. revert p2 Hp1 H0p0.
    induction p1.
    assert (Hmono : forall x y, graph.edge g x y -> graph.edge (graph.put g u v) x y).
    { intros x y H. apply graph.edge_put. left. exact H. }
    assert (Hsink : forall w, ~ graph.edge (graph.put g u v) v w).
    { intros w Hw. apply graph.edge_put in Hw. destruct Hw as [Hw | [Hu _]].
      - eapply Hout; exact Hw.
      - apply Huv; exact Hu. }
    assert (Hkeep : forall a b, b <> v ->
                      graph.edge (graph.put g u v) a b -> graph.edge g a b).
    { intros a b Hb Hab. apply graph.edge_put in Hab. destruct Hab as [Hab | [_ Hbv]].
      - exact Hab.
      - congruence. }
    assert (Pkeep : forall first p, ~ In v p ->
                      path (graph.edge (graph.put g u v)) first p -> path (graph.edge g) first p).
    { intros first p. revert first. induction p as [|a p IH]; intros first Hnv Hpath.
      - exact I.
      - destruct Hpath as [He Hp]. split.
        + apply Hkeep; [ intro Heq; apply Hnv; left; exact Heq | exact He ].
        + apply IH; [ intro Hin'; apply Hnv; right; exact Hin' | exact Hp ]. }
    assert (Hlast_ne : forall p, ~ In v p -> last p root <> v).
    { intros p Hnv Hcontra. destruct p as [|a p'].
      - simpl in Hcontra. exact (Hrv Hcontra).
      - apply Hnv. rewrite <- Hcontra. apply In_last. congruence. }
    assert (decomp : forall p, path (graph.edge (graph.put g u v)) root p ->
              (~ In v p /\ path (graph.edge g) root p) \/
              (exists q, p = q ++ [v] /\ ~ In v q /\ path (graph.edge g) root q /\ last q root = u)).
    { intros p Hp. destruct (set_contains p v) eqn:Hsc.
      - apply set_contains_true in Hsc. right.
        assert (Hlast : last p root = v) by (eapply path_sink_last; eassumption).
        assert (Hpne : p <> []) by (intro Hnil; rewrite Hnil in Hsc; destruct Hsc).
        assert (Hp_eq : p = removelast p ++ [v]).
        { transitivity (removelast p ++ [last p root]).
          - apply app_removelast_last; exact Hpne.
          - rewrite Hlast; reflexivity. }
        rewrite Hp_eq in Hp. apply path_snoc in Hp. destruct Hp as [Hpq Hedge].
        apply graph.edge_put in Hedge.
        assert (Hqu : last (removelast p) root = u).
        { destruct Hedge as [Hedge | [Hu _]];
            [ exfalso; eapply Hin; exact Hedge | symmetry; exact Hu ]. }
        assert (Hnvq : ~ In v (removelast p)).
        { intro Hvq.
          assert (Hlv : last (removelast p) root = v) by (eapply path_sink_last; eassumption).
          congruence. }
        exists (removelast p). ssplit;
          [ exact Hp_eq | exact Hnvq | apply Pkeep; assumption | exact Hqu ].
      - apply set_contains_false in Hsc. left.
        split; [ exact Hsc | apply Pkeep; assumption ]. }
    split.
    - intros Htree n p1 p2 [Hp1 Hl1] [Hp2 Hl2].
      destruct (decomp p1 Hp1) as [[Hnv1 Hg1] | [q1 [Hq1 [Hnvq1 [Hgq1 Hqu1]]]]];
        destruct (decomp p2 Hp2) as [[Hnv2 Hg2] | [q2 [Hq2 [Hnvq2 [Hgq2 Hqu2]]]]].
      + apply (Htree n); split; assumption.
      + exfalso. apply (Hlast_ne p1 Hnv1). rewrite <- Hl1, Hl2, Hq2. apply last_last.
      + exfalso. apply (Hlast_ne p2 Hnv2). rewrite <- Hl2, Hl1, Hq1. apply last_last.
      + assert (Hq12 : q1 = q2)
          by (apply (Htree u); (split; [ assumption | symmetry; assumption ])).
        subst p1 p2. rewrite Hq12. reflexivity.
    - intros Htree'. eapply locally_tree_weaken; [ exact Hmono | exact Htree' ].
  Qed.

  Lemma duplicate_edge_not_locally_tree (g : graph) (root : V) u v :
    reaches (graph.edge g) root u ->
    reaches (graph.edge g) root v ->
    ~ graph.edge g u v ->
    ~ locally_tree (graph.edge (graph.put g u v)) root.
  Proof.
    intros [pu [Hpu Hlu]] [pv [Hpv Hlv]] Hnuv Htree.
    assert (Hmono : forall x y, graph.edge g x y -> graph.edge (graph.put g u v) x y).
    { intros x y H. apply graph.edge_put. left. exact H. }
    assert (Hsnoc : path (graph.edge (graph.put g u v)) root (pu ++ [v])).
    { apply path_snoc. split.
      - eapply path_weaken; [ exact Hmono | exact Hpu ].
      - rewrite <- Hlu. apply graph.edge_put. right. split; reflexivity. }
    assert (Heq : pv = pu ++ [v]).
    { apply (Htree v).
      - split.
        + eapply path_weaken.
          * exact Hmono.
          * exact Hpv.
        + exact Hlv.
      - split.
        + exact Hsnoc.
        + rewrite last_last. reflexivity. }
    rewrite Heq in Hpv. apply path_snoc in Hpv. destruct Hpv as [_ Hedge].
    rewrite <- Hlu in Hedge. contradiction.
  Qed.

  Lemma dfs_check_invariant (root : V) s pth (gg : graph) :
    dfs_fold_state (fun _ _ _ => false) (fun tree _ _ => tree) (fun tree _ _ => tree)
      root ([root], true) s pth gg ->
    Reflects (locally_tree (graph.edge gg) root) (snd s) /\
    same_set (root :: graph.all_nodes gg) (fst s) /\
    incl pth (fst s) /\
    (forall y, In y (fst s) -> reaches (graph.edge gg) root y).
  Proof.
    intros H. induction H.
    - simpl. ssplit.
      + constructor. apply locally_tree_empty.
      + rewrite graph.all_nodes_empty. cbv [same_set]. reflexivity.
      + apply incl_refl.
      + intros y [? | []]. subst. apply reaches_self.
    - destruct st. simpl in *. apply set_contains_false in H1. fwd.
      ssplit.
      + eapply Reflects_iff; [eassumption|].
        apply locally_tree_put_unseen; try assumption.
        * intros w Hw. apply HvA. apply graph.all_nodes_spec. exists w. right. exact Hw.
        * intros w Hw. apply HvA. apply graph.all_nodes_spec. exists w. left. exact Hw.
      + cbv [same_set] in *. intros a. specialize (IHp1 a). cbn [In] in IHp1 |- *.
        rewrite graph.all_nodes_put. split.
        * intros [Hr | [Hg | [Hu' | Hv']]].
          -- right. apply (proj1 IHp1). left. exact Hr.
          -- right. apply (proj1 IHp1). right. exact Hg.
          -- subst a. right. exact Hu_in.
          -- left. symmetry. exact Hv'.
        * intros [Hv' | Hsvs].
          -- right. right. right. symmetry. exact Hv'.
          -- apply (proj2 IHp1) in Hsvs.
             destruct Hsvs as [Hr | Hg]; [ left; exact Hr | right; left; exact Hg ].
      + apply incl_cons; [ left; reflexivity | apply incl_tl; exact IHp2 ].
      + intros y [<- | Hys].
        * eapply reaches_step.
          -- eapply reaches_weaken; [ | apply IHp3; exact Hu_in ].
             intros a c Hac. apply graph.edge_put. left. exact Hac.
          -- apply graph.edge_put. right. split; reflexivity.
        * eapply reaches_weaken; [ | apply IHp3; exact Hys ].
          intros a c Hac. apply graph.edge_put. left. exact Hac.
    - destruct st as [svs sb]. cbn [fst snd untree_edge_upd'] in IH |- *.
      cbn [already_seen] in Hseen. apply set_contains_true in Hseen. fwd.
      ssplit.
      + constructor. apply duplicate_edge_not_locally_tree.
        * apply IHp3. apply IHp2. left. reflexivity.
        * apply IHp3. exact Hseen.
        * exact Hnew.
      + cbv [same_set] in *. intros a. specialize (IHp1 a). cbn [In] in IHp1 |- *.
        rewrite graph.all_nodes_put. split.
        * intros [Hr | [Hg | [Hu' | Hv']]].
          -- apply (proj1 IHp1). left. exact Hr.
          -- apply (proj1 IHp1). right. exact Hg.
          -- subst a. apply IHp2. left. reflexivity.
          -- subst a. exact Hseen.
        * intros Hsvs. apply (proj2 IHp1) in Hsvs.
          destruct Hsvs as [Hr | Hg]; [ left; exact Hr | right; left; exact Hg ].
      + exact IHp2.
      + intros y Hys. eapply reaches_weaken; [ | apply IHp3; exact Hys ].
        intros a c Hac. apply graph.edge_put. left. exact Hac.
    - destruct st as [svs sb]. cbn [fst snd finish'] in IH |- *. fwd. ssplit.
      + exact IHp0.
      + exact IHp1.
      + apply incl_cons_inv in IHp2. exact (proj2 IHp2).
      + exact IHp3.
  Qed.

  Lemma check_tree_spec g root :
    Reflects (locally_tree (graph.edge g) root) (check_locally_tree g root).
  Proof.
    cbv [check_locally_tree].
    destruct (dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree) (fun tree _ _ => tree) g true root)
      as [l b] eqn:E.
    apply dfs_fold_spec in E. fwd.
    apply locally_tree_reachable_subgraph in Ep0.
    eapply Reflects_iff; [ | exact Ep0 ].
    simpl in Ep1. apply dfs_check_invariant in Ep1. exact (proj1 Ep1).
  Qed.

End __.
