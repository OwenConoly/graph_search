From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb.
From coqutil Require Import Tactics.destr Tactics.Tactics Tactics.fwd.
From GraphSearch Require Import GraphInterface.
From Stdlib Require Import Classical_Prop.
Import ListNotations.

Lemma fold_right_inv_NoDup {A B} (P : list B -> A -> Prop) (f : B -> A -> A) l a :
  NoDup l ->
  P [] a ->
  (forall a' b l', ~In b l' -> In b l -> P l' a' -> P (b :: l') (f b a')) ->
  P l (fold_right f a l).
Proof.
  intros H ? ?. induction l; simpl; auto. simpl in *. inversion_clear H. eauto 6.
Qed.

Section __.
  Context {V : Type}.

  Section path.
    Context (edge : V -> V -> Prop).

    Fixpoint path (first : V) (p : list V) :=
      match p with
      | [] => True
      | next :: p' => edge first next /\ path next p'
      end.

    Definition path_to first p last :=
      path first p /\ last = List.last p first.

    Definition reaches first last :=
      exists p, path_to first p last.

    Definition locally_tree root :=
      forall n p1 p2,
        path_to root p1 n ->
        path_to root p2 n ->
        p1 = p2.

    Definition reachable root :=
      forall u v, edge u v ->
             exists p, path_to root p u.
  End path.

  Context {eqbV : Eqb V}.
  Context {graph : graph.graph V}.
  Context {ok : graph.ok graph}.
  Context {eqb_ok : Eqb_ok eqbV}.

  Section fold.
    Context {state : Type}.
    Context (untree_edge_upd : state -> list V -> V -> state).
    Context (tree_edge_upd : state -> list V -> V -> state).
    Context (finish : state -> list V -> V -> state).

    Definition set_contains vs v :=
      List.existsb (eqb v) vs.

    Section with_graph.
      Context (g : graph).

      Definition graph_edge u v := In v (graph.edges g u).

      Definition state' : Type := list V * state.
      Definition untree_edge_upd' '(vs, st) v := (vs, untree_edge_upd st vs v).
      Definition tree_edge_upd' '(vs, st) v := (v :: vs, tree_edge_upd st vs v).
      Definition finish' '(vs, st) v := (vs, finish st vs v).

      Definition already_seen (st' : state') v :=
        let '(vs, _) := st' in set_contains vs v.

      Fixpoint dfs_fold' n st' v : state' :=
        match n with
        | S n' =>
            if already_seen st' v then untree_edge_upd' st' v else
              finish' (fold_left (dfs_fold' n') (graph.edges g v) (tree_edge_upd' st' v)) v
        | O => st'
        end.

      Definition dfs_fold st0 := dfs_fold' (3 + length (graph.sources g)) ([], st0).
    End with_graph.

    Inductive dfs_fold_state (root : V) (st0 : state') : state' -> list V (*current path*)-> graph (*explored edges*) -> Prop :=
    | dfs_init : dfs_fold_state _ _ st0 [root] graph.empty
    | dfs_tree_edge st u p g v :
      ~graph_edge g u v ->
      dfs_fold_state _ _ st (u :: p) g ->
      already_seen st v = false ->
      dfs_fold_state _ _ (tree_edge_upd' st v) (v :: u :: p) (graph.put g u v)
    | dfs_untree_edge st u p g v :
      dfs_fold_state _ _ st (u :: p) g ->
      ~graph_edge g u v ->
      already_seen st v = true ->
      dfs_fold_state _ _ (untree_edge_upd' st v) (u :: p) (graph.put g u v)
    | dfs_finish st u p g :
      dfs_fold_state _ _ st (u :: p) g ->
      dfs_fold_state _ _ (finish' st u) p g.

    Definition edge_upd' st v :=
      if already_seen st v then untree_edge_upd' st v else
        tree_edge_upd' st v.

    Lemma graph_edge_union g1 g2 x y :
      graph_edge (graph.union g1 g2) x y <-> graph_edge g1 x y \/ graph_edge g2 x y.
    Proof. cbv [graph_edge]. apply graph.edges_union. Qed.

    Lemma already_seen_tree_edge_upd st v y :
      already_seen st y = true -> already_seen (tree_edge_upd' st v) y = true.
    Proof.
      destruct st as [vs s]. cbn [already_seen tree_edge_upd']. simpl.
      intro H. rewrite H. destruct (eqb y v); reflexivity.
    Qed.

    Lemma already_seen_tree_edge_upd_self st v :
      already_seen (tree_edge_upd' st v) v = true.
    Proof.
      destruct st as [vs s]. cbn [already_seen tree_edge_upd']. simpl.
      destruct (@eqb_boolspec V eqbV eqb_ok v v); [reflexivity | congruence].
    Qed.

    Lemma already_seen_untree_edge_upd st v y :
      already_seen (untree_edge_upd' st v) y = already_seen st y.
    Proof. destruct st as [vs s]. reflexivity. Qed.

    Lemma already_seen_finish' st v y :
      already_seen (finish' st v) y = already_seen st y.
    Proof. destruct st as [vs s]. reflexivity. Qed.

    Lemma already_seen_mono root st0 st p g y :
      dfs_fold_state root st0 st p g ->
      already_seen st0 y = true ->
      already_seen st y = true.
    Proof.
      induction 1; intros.
      - assumption.
      - apply already_seen_tree_edge_upd. eauto.
      - rewrite already_seen_untree_edge_upd. eauto.
      - rewrite already_seen_finish'. eauto.
    Qed.

    Lemma set_contains_true v vs :
      set_contains vs v = true <-> In v vs.
    Proof. Admitted.

    Lemma set_contains_false v vs :
      set_contains vs v = false <-> ~In v vs.
    Proof. Admitted.

    Lemma already_seen_mono' root vs st0 vs' st p g :
      dfs_fold_state root (vs, st0) (vs', st) p g ->
      incl vs vs'.
    Proof.
      intros H1 ? H2. apply set_contains_true in H2. apply set_contains_true.
      eapply already_seen_mono with (st := (_, _)); eassumption.
    Qed.

    Hint Unfold graph_edge : core.
    Lemma dfs_target_seen root st0 st p g x y :
      dfs_fold_state root st0 st p g -> graph_edge g x y -> already_seen st y = true.
    Proof.
      intro H. revert x y.
      induction H; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. contradiction.
      - rewrite graph.edges_put in He. destruct He as [Hold | [_ Hvy]].
        + apply already_seen_tree_edge_upd. eauto.
        + subst y. apply already_seen_tree_edge_upd_self.
      - rewrite graph.edges_put in He. rewrite already_seen_untree_edge_upd.
        destruct He as [Hold | [_ Hvy]]; subst; eauto.
      - rewrite already_seen_finish'. eauto.
    Qed.

    Lemma dfs_path_seen root st0 st p g z :
      already_seen st0 root = true ->
      dfs_fold_state root st0 st p g ->
      In z p ->
      already_seen st z = true.
    Proof.
      intros Hroot H. revert z.
      induction H; intros z Hz.
      - destruct Hz; subst; contradiction || auto.
      - destruct Hz as [Hz|Hz].
        + subst. apply already_seen_tree_edge_upd_self.
        + apply already_seen_tree_edge_upd. eauto.
      - rewrite already_seen_untree_edge_upd. eauto.
      - rewrite already_seen_finish'. simpl in *. eauto.
    Qed.

    Lemma dfs_path_unseen root st0 st p g z :
      dfs_fold_state root st0 st p g -> In z p -> z = root \/ already_seen st0 z = false.
    Proof.
      intro H. revert z.
      induction H as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros z Hz.
      - destruct Hz as [<- | []]. left. reflexivity.
      - destruct Hz as [<- | Hz].
        + right. destruct (already_seen st0 v) eqn:E; [ | reflexivity ].
          pose proof (already_seen_mono _ _ _ _ _ _ Hrec E) as Hc. congruence.
        + apply IH. exact Hz.
      - apply IH. exact Hz.
      - apply IH. right. exact Hz.
    Qed.

    Lemma dfs_source_seen root st0 st p g x y :
      already_seen st0 root = true ->
      dfs_fold_state root st0 st p g -> graph_edge g x y -> already_seen st x = true.
    Proof.
      intros Hroot H. revert x y.
      induction H as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. destruct He.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxhd _]].
        + apply already_seen_tree_edge_upd. apply (IH x y). exact Hold.
        + subst x. apply already_seen_tree_edge_upd.
          apply (dfs_path_seen _ _ _ _ _ _ Hroot Hrec). apply in_eq.
      - rewrite graph.edges_put in He. rewrite already_seen_untree_edge_upd.
        destruct He as [Hold | [Hxhd _]].
        + apply (IH x y). exact Hold.
        + subst x.
          apply (dfs_path_seen _ _ _ _ _ _ Hroot Hrec). apply in_eq.
      - rewrite already_seen_finish'. apply (IH x y). exact He.
    Qed.

    Lemma dfs_source_init root st0 st p g x y :
      dfs_fold_state root st0 st p g -> graph_edge g x y ->
      x = root \/ already_seen st0 x = false.
    Proof.
      intro H. revert x y.
      induction H as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. destruct He.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxu0 _]].
        + apply (IH x y). exact Hold.
        + subst x. apply (dfs_path_unseen _ _ _ _ _ _ Hrec). apply in_eq.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxu0 _]].
        + apply (IH x y). exact Hold.
        + subst x. apply (dfs_path_unseen _ _ _ _ _ _ Hrec). apply in_eq.
      - apply (IH x y). exact He.
    Qed.

    Lemma dfs_fold_state_trans root st0 st st' p p' g g' u :
      dfs_fold_state root st0 st (u :: p) g ->
      already_seen st0 root = true ->
      graph.edges g u = [] ->
      dfs_fold_state u st st' p' g' ->
      dfs_fold_state root st0 st' (p' ++ p) (graph.union g g').
    Proof.
      intros H1 Hroot Hedges H2.
      induction H2 as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                        | st2 u0 p0 g0 v Hrec IH Hne Hseen
                        | st2 u2 p0 g0 Hrec IH ].
      - cbn [app]. rewrite graph.union_empty_r. exact H1.
      - cbn [app]. rewrite graph.union_put_r. apply dfs_tree_edge.
        + intro Hedge. apply graph_edge_union in Hedge. destruct Hedge as [Hg | Hg0].
          * pose proof (dfs_target_seen _ _ _ _ _ _ _ H1 Hg) as Hs.
            pose proof (already_seen_mono _ _ _ _ _ _ Hrec Hs) as Hs2.
            congruence.
          * exact (Hne Hg0).
        + exact IH.
        + exact Hseen.
      - cbn [app]. rewrite graph.union_put_r. apply dfs_untree_edge.
        + exact IH.
        + intro Hedge. apply graph_edge_union in Hedge. destruct Hedge as [Hg | Hg0].
          * pose proof (dfs_path_unseen _ _ _ _ _ _ Hrec (in_eq u0 p0)) as Hun.
            destruct Hun as [-> | Hun].
            -- cbv [graph_edge] in Hg. rewrite Hedges in Hg. destruct Hg.
            -- pose proof (dfs_source_seen _ _ _ _ _ _ _ Hroot H1 Hg) as Hsn. congruence.
          * exact (Hne Hg0).
        + exact Hseen.
      - cbn [app] in IH. eapply dfs_finish. exact IH.
    Qed.

    Definition graph_corresp vs vs' g g_acc :=
      (forall s, In s (graph.sources g_acc) -> In s vs'/\  ~In s vs) /\
        (forall u v,
            graph_edge g u v ->
            In u vs' ->
            ~ In u vs ->
            graph_edge g_acc u v) /\
        (forall u v, graph_edge g_acc u v -> graph_edge g u v).

    Lemma in_not_nil A x (l : list A) :
      In x l ->
      l <> nil.
    Proof. destruct l; simpl; congruence. Qed.

    Lemma graph_corresp_eq vs g g_acc :
      graph_corresp [] vs g g_acc ->
      (forall u v, graph_edge g_acc u v <-> graph_edge g u v /\ In u vs).
    Proof.
      cbv [graph_corresp]. intros. fwd. split.
      - intros. especialize Hp0.
        { apply graph.sources_spec. eapply in_not_nil. eassumption. }
        fwd. auto.
      - intros. fwd. auto.
    Qed.

    Definition weak_graph_corresp root root_edges vs vs' g g_acc :=
      (forall s, In s (graph.sources g_acc) -> In s vs'/\  ~In s vs) /\
        (forall u v,
            graph_edge g u v ->
            In u vs' ->
            ~ In u vs ->
            u <> root ->
            graph_edge g_acc u v) /\
        (forall v, graph_edge g_acc root v <-> In v root_edges) /\
        (forall u v, graph_edge g_acc u v -> graph_edge g u v).

    Definition no_long_paths g root vs n :=
      forall p,
        path (graph_edge g) root p ->
        NoDup (root :: p) ->
        Forall (fun v => ~In v vs) (root :: p) ->
        S (S (length p)) < n.

    Lemma no_long_paths_step g u v vs n :
      no_long_paths g u vs (S n) ->
      ~In u vs ->
      graph_edge g u v ->
      no_long_paths g v (u :: vs) n.
    Proof.
      cbv [no_long_paths]. intros H Hu He p Hp1 Hp2 Hp3.
      specialize (H (v :: p)). simpl in H. especialize H.
      - auto.
      - constructor; auto. intros H. rewrite Forall_forall in Hp3.
        eapply Hp3; simpl; eauto.
      - constructor; auto. eapply Forall_impl; [|eassumption].
        simpl. auto.
      - lia.
    Qed.

    Lemma no_long_paths_incl g u vs vs' n :
      no_long_paths g u vs n ->
      incl vs vs' ->
      no_long_paths g u vs' n.
    Proof.
      cbv [no_long_paths]. intros. apply H; auto.
      eapply Forall_impl; simpl; eauto. simpl. unfold not. auto.
    Qed.

    Lemma sources_empty :
      graph.sources (vertex := V) graph.empty = [].
    Proof. Admitted.

    Lemma sources_put g u v (u' : V) :
      In u' (graph.sources (graph.put g u v)) <-> In u' (graph.sources g) \/ u = u'.
    Proof. Admitted.

    Lemma sources_union g1 g2 (v : V) :
      In v (graph.sources (graph.union g1 g2)) <-> In v (graph.sources g1) \/ In v (graph.sources g2).
    Proof. Admitted.

    Lemma forall_not_in_nil A (l : list A) :
      (forall x, ~In x l) ->
      l = [].
    Proof. destruct l; auto. simpl. intros. exfalso. eapply H; auto. Qed.

    Lemma no_long_paths_nonzero g root vs n :
      no_long_paths g root vs n ->
      ~In root vs ->
      1 < n.
    Proof.
      cbv [no_long_paths]. intros H. specialize (H []). intro. subst.
      especialize H; simpl; auto.
      - constructor; auto. constructor.
      - lia.
    Qed.

    Lemma dfs_fold'_sound root vs n st0 g vs' st' :
      no_long_paths g root vs n ->
      set_contains vs root = false ->
      dfs_fold' g n (vs, st0) root = (vs', st') ->
      exists g_acc,
        dfs_fold_state root (tree_edge_upd' (vs, st0) root) (vs', st') [] g_acc /\
          graph_corresp vs vs' g g_acc.
    Proof.
      revert root vs st0 vs' st'. induction n.
      { intros *. intros Hn Hroot. exfalso. cbv [no_long_paths] in Hn.
        specialize (Hn []). simpl in Hn. especialize Hn; auto.
        - constructor; simpl; auto. constructor.
        - apply set_contains_false in Hroot. auto.
        - lia. }
      intros root vs st0 vs' st' Hn Hroot H.
      assert (n <> 0).
      { eapply no_long_paths_nonzero in Hn. 1: lia.
        apply set_contains_false. assumption. }
      simpl in H. cbv [edge_upd']. simpl. rewrite Hroot in *.
      cbv [finish'] in H. Tactics.destruct_one_match_hyp. fwd.
      eenough (exists g_acc, _ /\ weak_graph_corresp root (rev (graph.edges g root)) vs vs' g g_acc) as [g_acc H].
      { exists g_acc. split.
        - apply dfs_finish with (st := (_, _)). eapply (proj1 H).
        - destruct H as [_ H].
          cbv [graph_corresp].
          cbv [weak_graph_corresp] in H. fwd. split; auto. split; auto. intros.
          assert (u = root \/ u <> root) as [Hu|Hu] by apply classic.
          { subst. apply Hp2. rewrite <- in_rev. assumption. }
          apply Hp1; assumption. }
      rewrite <- fold_left_rev_right in E.
      revert vs' s E.
      apply fold_right_inv_NoDup.
      - apply NoDup_rev. apply graph.edges_NoDup.
      - intros. fwd. eexists. split; [constructor|].
        cbv [weak_graph_corresp]. split.
        { rewrite sources_empty. simpl. contradiction. }
        split; cycle 1.
        { cbv [graph_edge]. rewrite graph.edges_empty. simpl. split.
          - intros. split; auto.
          - intros * H.  rewrite graph.edges_empty in H. destruct H. }
        intros. exfalso. destruct H1; subst; auto.
      - intros * Hnotin Hin H * Hdfs. destruct a'.
        specialize (H _ _ eq_refl). fwd. apply in_rev in Hin.
        destruct (set_contains l b) eqn:Eb.
        { destruct n; [lia|]. simpl in Hdfs. rewrite Eb in Hdfs. fwd.
          eexists. split.
          - apply dfs_untree_edge with (st := (_, _)).
            + eassumption.
            + intro. apply Hnotin. cbv [weak_graph_corresp] in Hp1. fwd.
              apply Hp1p2. assumption.
            + simpl. assumption.
          - cbv [weak_graph_corresp] in *. fwd. ssplit.
            + cbv [incl]. intros v Hv. apply sources_put in Hv. destruct Hv; auto.
              subst. eapply already_seen_mono in Hp0.
              -- simpl in Hp0. apply set_contains_true in Hp0. split; [exact Hp0|].
                 apply set_contains_false in Hroot. assumption.
              -- simpl. rewrite eqb_refl_true by assumption. reflexivity.
            + intros. cbv [graph_edge]. rewrite graph.edges_put. left.
              apply Hp1p1; auto.
            + intros. cbv [graph_edge]. rewrite graph.edges_put.
              cbv [graph_edge] in Hp1p2. rewrite Hp1p2.
              simpl. split; intros [?|?]; fwd; auto.
            + intros * H. cbv [graph_edge] in H. rewrite graph.edges_put in H.
              destruct H as [H|H]; fwd; auto. }
        apply IHn in Hdfs.
        + fwd.
          cbv [tree_edge_upd'] in Hdfsp0. eexists. split.
          -- eapply dfs_fold_state_trans with (p' := nil).
             ++ apply dfs_tree_edge. 2: eassumption.
                --- intros H. cbv [weak_graph_corresp] in Hp1. fwd. apply Hp1p2 in H.
                    eauto.
                --- simpl. assumption.
             ++ simpl. rewrite eqb_refl_true by assumption. reflexivity.
             ++ apply forall_not_in_nil. intros. rewrite graph.edges_put.
                intros [H|H].
                --- cbv [weak_graph_corresp] in Hp1. fwd.
                    apply in_not_nil in H. Search graph.sources.
                    apply graph.sources_spec in H. apply Hp1p0 in H.
                    apply set_contains_false in Eb. fwd. auto.
                --- fwd. eapply already_seen_mono in Hp0; cycle 1.
                    { simpl. rewrite eqb_refl_true by assumption. reflexivity. }
                    simpl in Hp0. congruence.
             ++ eassumption.
          -- cbv [weak_graph_corresp]. cbv [weak_graph_corresp] in Hp1. fwd.
             apply already_seen_mono' in Hp0, Hdfsp0.
             ssplit.
             ++ cbv [incl]. intros v Hv. rewrite sources_union, sources_put in Hv.
                destruct Hv as [[Hv|Hv]|Hv].
                --- apply Hp1p0 in Hv. fwd. split; auto. apply Hdfsp0. simpl. auto.
                --- subst. split.
                    +++ apply Hdfsp0. simpl. right. apply Hp0. simpl. auto.
                    +++ apply set_contains_false in Hroot. exact Hroot.
                --- cbv [graph_corresp] in Hdfsp1. fwd. apply Hdfsp1p0 in Hv. fwd.
                    split; auto. intro. apply Hvp1. apply Hp0. simpl. auto.
             ++ intros. cbv [graph_edge]. rewrite graph.edges_union, graph.edges_put.
                assert (In u l \/ ~In u l) as [Hu|Hu] by apply classic.
                --- left. left. apply Hp1p1; auto.
                --- right. apply Hdfsp1; auto.
             ++ intros. cbv [graph_edge]. rewrite graph.edges_union, graph.edges_put.
                split.
                --- intros [[Hv|Hv]|Hv].
                    +++ simpl. right. apply Hp1p2. assumption.
                    +++ fwd. simpl. auto.
                    +++ cbv [graph_corresp] in Hdfsp1. fwd.
                        apply in_not_nil in Hv. apply graph.sources_spec in Hv.
                        apply Hdfsp1p0 in Hv. fwd. exfalso. apply Hvp1. apply Hp0.
                        simpl. auto.
                --- intros [Hv|Hv].
                    +++ subst. auto.
                    +++ left. left. apply Hp1p2. assumption.
             ++ intros. cbv [graph_edge] in H.
                rewrite graph.edges_union, graph.edges_put in H.
                destruct H as [[H|H]|H]; fwd; auto.
                cbv [graph_corresp] in Hdfsp1. fwd. auto.
        + eapply no_long_paths_incl.
          -- apply no_long_paths_step; try eassumption.
             apply set_contains_false in Hroot. exact Hroot.
          -- apply already_seen_mono' in Hp0. exact Hp0.
        + assumption.
    Qed.

    Lemma removelast_cons A (a b : A) l :
      removelast (a :: b :: l) = a :: removelast (b :: l).
    Proof. reflexivity. Qed.

    Lemma NoDup_removelast A (l : list A) :
      NoDup l ->
      NoDup (removelast l).
    Proof. Admitted.

    Lemma length_removelast_cons A (a : A) l :
      length (removelast (a :: l)) = length l.
    Proof. Admitted.

    Lemma path_in_graph g root p :
      path (graph_edge g) root p ->
      incl (removelast (root :: p)) (graph.sources g).
    Proof.
      revert root. induction p; intros root Hroot.
      - apply incl_nil_l.
      - simpl in Hroot. fwd. rewrite removelast_cons. apply List.incl_cons. 2: eauto.
        apply graph.sources_spec. eapply in_not_nil. eassumption.
    Qed.

    Lemma paths_limited g root :
      no_long_paths g root [] (S (S (S (length (graph.sources g))))).
    Proof.
      cbv [no_long_paths]. intros p H1 H2 _. apply path_in_graph in H1.
      apply NoDup_removelast in H2. eapply NoDup_incl_length in H2; [|eassumption].
      rewrite length_removelast_cons in H2. lia.
    Qed.

    Lemma dfs_fold_sound g st0 root vs st :
      dfs_fold g st0 root = (vs, st) ->
      exists g_acc,
        dfs_fold_state root (tree_edge_upd' ([], st0) root) (vs, st) [] g_acc /\
          (forall u v, graph_edge g_acc u v <-> graph_edge g u v /\ In u vs).
    Proof.
      intros H. apply dfs_fold'_sound in H; cycle 1.
      { apply paths_limited. }
      { reflexivity. }
      fwd. eauto using graph_corresp_eq.
    Qed.

  Lemma dfs_fold'_mono g n vs st root vs' st' :
    dfs_fold' g n (vs, st) root = (vs', st') ->
    incl vs vs'.
  Proof.
    revert vs st root vs' st'.
    induction n as [|m IH]; simpl; intros vs st root vs' st' H; fwd.
    - apply incl_refl.
    - destruct (set_contains vs root).
      + fwd. apply incl_refl.
      + cbv [finish'] in H. Tactics.destruct_one_match_hyp. fwd.
        revert vs' s E. apply fold_left_inv; simpl; intros; fwd; simpl; auto.
        -- apply incl_tl. apply incl_refl.
        -- destruct a. specialize (H0 _ _ eq_refl). apply IH in E. eauto using incl_tran.
  Qed.

  Lemma dfs_fold'_self g m vs st root vs' st' :
    0 < m ->
    dfs_fold' g m (vs, st) root = (vs', st') ->
    In root vs'.
  Proof.
    intros Hm H. destruct m as [|k]; [lia|]. simpl in H.
    destruct (set_contains vs root) eqn:Hc.
    - fwd. apply set_contains_true. assumption.
    - cbv [finish'] in H. Tactics.destruct_one_match_hyp. fwd.
      revert vs' s E. apply fold_left_inv; simpl; intros; fwd; simpl; auto.
      destruct a. especialize H0; eauto.
      eapply dfs_fold'_mono; eassumption.
  Qed.

  Lemma incl_cons A (a : A) l :
    incl l (a :: l).
  Proof. Admitted.

  Lemma last_cons A (l : list A) a d :
    last (a :: l) d = last l a.
  Proof.
    revert a d. induction l as [|b l' IH]; intros a d; [reflexivity|].
    change (last (b :: l') d = last (b :: l') a).
    rewrite (IH b d), (IH b a). reflexivity.
  Qed.

  Lemma visited_closed g n vs root u v st vs' st' :
    no_long_paths g root vs n ->
    dfs_fold' g n (vs, st) root = (vs', st') ->
    In u vs' ->
    graph_edge g u v ->
    In u vs \/ In v vs'.
  Proof.
    revert vs root u v st vs' st'.
    induction n as [|m IH]; intros vs root u v st vs' st' Hn H Hu He.
    - simpl in *. fwd. auto.
    - simpl in H. destruct (set_contains vs root) eqn:Hroot.
      + fwd. auto.
      + cbv [finish'] in *. Tactics.destruct_one_match_hyp. fwd.
        enough ((In u vs' -> In u vs \/ u = root /\ (In v (rev (graph.edges g root)) -> In v vs') \/ In v vs') /\ incl vs vs' /\ In root vs').
        { fwd. apply Hp0 in Hu. rewrite <- in_rev in Hu.
          destruct Hu as [?|[?|?]]; fwd; auto. }
        clear Hu. revert E. rewrite <- fold_left_rev_right.
        revert vs' s. apply fold_right_inv_NoDup.
        -- apply NoDup_rev. apply graph.edges_NoDup.
        -- intros. fwd. ssplit; simpl; auto using incl_cons. intros [Hx|Hx]; subst; auto.
           right. left. split; auto. contradiction.
        -- intros. destruct a'. specialize (H1 _ _ eq_refl). fwd.
           specialize IH with (2 := E).
           eassert (blah : _). 2: specialize IH with (1 := blah).
           { eapply no_long_paths_incl.
             - apply no_long_paths_step.
               + eassumption.
               + apply set_contains_false in Hroot. exact Hroot.
               + apply in_rev in H0. apply H0.
             - fwd. apply List.incl_cons; auto. }
           apply no_long_paths_nonzero in Hn.
           2: { apply set_contains_false. assumption. }
           pose proof E as E'. apply dfs_fold'_mono in E.
           apply dfs_fold'_self in E'; [|lia].
           ssplit; eauto using incl_tran.
           intros. eapply IH in H1; eauto. destruct H1; auto.
           apply H1p0 in H1. destruct H1 as [?|[?|?]]; fwd; simpl; auto.
           right. left. split; auto. intros [?|?]; subst; auto.
  Qed.

  Lemma edge_closed_reaches_in R u0 v0 vs :
    (forall u v, In u vs -> R u v -> In v vs) ->
    In u0 vs ->
    reaches R u0 v0 ->
    In v0 vs.
  Proof.
    intros H Hu0 Hreach. cbv [reaches path_to] in Hreach. fwd.
    revert u0 Hu0 Hreachp0. induction p; cbn [path]; intros u0 Hu0 Hreach; auto.
    fwd. destruct p; eauto. rewrite last_cons. apply IHp; eauto.
  Qed.

  Lemma reaches_self R u :
    reaches R u u.
  Proof. cbv [reaches]. exists nil. cbv [path_to]. simpl. auto. Qed.

  Lemma last_cons_last_cons A (a : A) l d1 d2 :
    last (a :: l) d1 = last (a :: l) d2.
  Proof. do 2 rewrite last_cons. reflexivity. Qed.

  Lemma reaches_step_before R u v w :
    reaches R v w ->
    R u v ->
    reaches R u w.
  Proof.
    cbv [reaches path_to]. intros. fwd. eexists (_ :: _). simpl. split; eauto.
    destruct p; try reflexivity. apply last_cons_last_cons.
  Qed.

  Lemma dfs_fold'_connected g n vs st0 st root u vs' :
    dfs_fold' g n (vs, st0) root = (vs', st) ->
    In u vs' ->
    In u vs \/ reaches (graph_edge g) root u.
  Proof.
    revert vs st0 st root u vs'.
    induction n; intros vs st0 st root u vs' H Hu.
    - simpl in H. fwd. auto.
    - simpl in H. destruct (set_contains vs root).
      + fwd. auto.
      + cbv [finish'] in *. Tactics.destruct_one_match_hyp. fwd.
        revert vs' s Hu E. apply fold_left_inv.
        -- intros vs' s Hu ?. fwd. destruct Hu as [Hu|Hu]; auto.
           subst. right. apply reaches_self.
        -- intros [vs0 s0] b Hb IH vs' s' Hu H. specialize IH with (2 := eq_refl).
           eapply IHn in H; [|eassumption]. destruct H as [H|H].
           ++ apply IH in H. destruct H as [H|H]; auto.
           ++ right. eapply reaches_step_before; eassumption.
  Qed.

  Lemma dfs_fold_connected g vs st0 st root u :
    dfs_fold g st0 root = (vs, st) ->
    In u vs ->
    reaches (graph_edge g) root u.
  Proof.
    intros H1 H2. eapply dfs_fold'_connected in H1; eauto.
    destruct H1 as [[]|?]. assumption.
  Qed.

  Lemma dfs_fold_explores_everything g st root vs u v st' :
    dfs_fold g st root = (vs, st') ->
    reaches (graph_edge g) root u ->
    graph_edge g u v ->
    In u vs.
  Proof.
    intros. cbv [dfs_fold plus] in H. eapply edge_closed_reaches_in; cycle 1.
    2: eassumption.
    { apply dfs_fold'_self in H; [|lia]. assumption. }
    intros. eapply visited_closed in H; eauto.
    { destruct H as [[]|?]. assumption. }
    apply paths_limited.
  Qed.

  Definition reachable_subgraph root g' g :=
    forall u v, graph_edge g' u v <-> graph_edge g u v /\ reaches (graph_edge g) root u.

  Definition dfs_fold_spec g st0 root vs st :
    dfs_fold g st0 root = (vs, st) ->
    exists g',
      reachable_subgraph root g' g /\
        dfs_fold_state root (tree_edge_upd' ([], st0) root) (vs, st) [] g'.
  Proof.
    intros H.
    pose proof dfs_fold_sound as H1. specialize H1 with (1 := H). fwd.
    pose proof dfs_fold_explores_everything as H2. specialize H2 with (1 := H).
    pose proof dfs_fold_connected as H3. specialize H3 with (1 := H).
    exists g_acc. split; [|assumption].
    cbv [reachable_subgraph].
    intros. split; intros He.
    - apply H1p1 in He. fwd. auto.
    - fwd. apply H1p1. eauto.
  Qed.
  End fold.
End __.
