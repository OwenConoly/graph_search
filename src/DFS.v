From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb.
From coqutil Require Import Tactics.destr Tactics.Tactics Tactics.fwd.
From GraphSearch Require Import List EdgeRel GraphInterface.
Import ListNotations.


Section __.
  Context {V : Type}.


  Context {eqbV : Eqb V}.
  Context {graph : graph.graph V}.
  Context {ok : graph.ok graph}.
  Context {eqb_ok : Eqb_ok eqbV}.

  Section fold.
    Context {state : Type}.
    Context (untree_edge_upd : state -> list V -> V -> state).
    Context (tree_edge_upd : state -> list V -> V -> state).
    Context (finish : state -> list V -> V -> state).


    Section with_graph.
      Context (g : graph).


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

    Inductive dfs_fold_state (root : V) vs0 st0 : list V (*seen*) -> state -> list V (*current path*)-> graph (*explored edges*) -> Prop :=
    | dfs_init : dfs_fold_state _ _ _ vs0 st0 [root] graph.empty
    | dfs_tree_edge vs st u p g v :
      ~graph.edge g u v ->
      dfs_fold_state _ _ _ vs st (u :: p) g ->
      set_contains vs v = false ->
      dfs_fold_state _ _ _ (v :: vs) (tree_edge_upd st vs v) (v :: u :: p) (graph.put g u v)
    | dfs_untree_edge vs st u p g v :
      dfs_fold_state _ _ _ vs st (u :: p) g ->
      ~graph.edge g u v ->
      set_contains vs v = true ->
      dfs_fold_state _ _ _ vs (untree_edge_upd st vs v) (u :: p) (graph.put g u v)
    | dfs_finish vs st u p g :
      dfs_fold_state _ _ _ vs st (u :: p) g ->
      dfs_fold_state _ _ _ vs (finish st vs u) p g.

    Lemma set_contains_cons_true v vs y :
      set_contains vs y = true -> set_contains (v :: vs) y = true.
    Proof. rewrite !set_contains_true. simpl. auto. Qed.

    Lemma set_contains_head v vs :
      set_contains (v :: vs) v = true.
    Proof. apply set_contains_true. left. reflexivity. Qed.

    Lemma seen_mono root vs0 st0 vs st p g y :
      dfs_fold_state root vs0 st0 vs st p g ->
      set_contains vs0 y = true ->
      set_contains vs y = true.
    Proof. intros H Hy. induction H; auto using set_contains_cons_true. Qed.

    Lemma seen_mono' root vs0 st0 vs st p g :
      dfs_fold_state root vs0 st0 vs st p g ->
      incl vs0 vs.
    Proof.
      intros H x Hx. apply set_contains_true. eapply seen_mono; try eassumption.
      apply set_contains_true. exact Hx.
    Qed.

    Hint Unfold graph.edge : core.
    Lemma dfs_target_seen root vs0 st0 vs st p g x y :
      dfs_fold_state root vs0 st0 vs st p g -> graph.edge g x y -> set_contains vs y = true.
    Proof.
      intro H. revert x y.
      induction H; intros x y He.
      - apply graph.edge_empty in He. contradiction.
      - apply graph.edge_put in He. destruct He as [Hold | [_ Hvy]].
        + apply set_contains_cons_true. eauto.
        + subst y. apply set_contains_head.
      - apply graph.edge_put in He. destruct He as [Hold | [_ Hvy]].
        + eauto.
        + subst y. assumption.
      - eauto.
    Qed.

    Lemma dfs_path_seen root vs0 st0 vs st p g z :
      set_contains vs0 root = true ->
      dfs_fold_state root vs0 st0 vs st p g ->
      In z p ->
      set_contains vs z = true.
    Proof.
      intros Hroot H. revert z.
      induction H; intros z Hz.
      - destruct Hz as [<- | []]. exact Hroot.
      - destruct Hz as [<- | Hz].
        + apply set_contains_head.
        + apply set_contains_cons_true. eauto.
      - eauto.
      - eauto using in_cons.
    Qed.

    Lemma dfs_path_unseen root vs0 st0 vs st p g z :
      dfs_fold_state root vs0 st0 vs st p g -> In z p -> z = root \/ set_contains vs0 z = false.
    Proof.
      intro H. revert z.
      induction H; intros z Hz.
      - destruct Hz as [<- | []]. left. reflexivity.
      - destruct Hz as [<- | Hz].
        + right. apply set_contains_false. intro Hin.
          match goal with He : dfs_fold_state _ _ _ _ _ _ _ |- _ =>
            apply (seen_mono' _ _ _ _ _ _ _ He) in Hin end.
          apply set_contains_true in Hin. congruence.
        + eauto.
      - eauto.
      - eauto using in_cons.
    Qed.

    Lemma dfs_source_seen root vs0 st0 vs st p g x y :
      set_contains vs0 root = true ->
      dfs_fold_state root vs0 st0 vs st p g -> graph.edge g x y -> set_contains vs x = true.
    Proof.
      intros Hroot H. revert x y.
      induction H; intros x y He.
      - apply graph.edge_empty in He. destruct He.
      - apply graph.edge_put in He. destruct He as [Hold | [Hxhd _]].
        + apply set_contains_cons_true. eauto.
        + subst x. apply set_contains_cons_true.
          eapply dfs_path_seen; [ exact Hroot | eassumption | apply in_eq ].
      - apply graph.edge_put in He. destruct He as [Hold | [Hxhd _]].
        + eauto.
        + subst x. eapply dfs_path_seen; [ exact Hroot | eassumption | apply in_eq ].
      - eauto.
    Qed.

    Lemma dfs_fold_state_trans root vs0 st0 vs st vs' st' p p' g g' u :
      dfs_fold_state root vs0 st0 vs st (u :: p) g ->
      set_contains vs0 root = true ->
      graph.edges g u = [] ->
      dfs_fold_state u vs st vs' st' p' g' ->
      dfs_fold_state root vs0 st0 vs' st' (p' ++ p) (graph.union g g').
    Proof.
      intros H1 Hroot Hedges H2.
      induction H2.
      - cbn [app]. rewrite graph.union_empty_r. exact H1.
      - cbn [app]. rewrite graph.union_put_r. apply dfs_tree_edge.
        + intro Hedge. apply graph.edge_union in Hedge. destruct Hedge as [Hg | Hg0].
          * pose proof (dfs_target_seen _ _ _ _ _ _ _ _ _ H1 Hg) as Hs.
            match goal with He : dfs_fold_state u _ _ _ _ _ _ |- _ =>
              pose proof (seen_mono _ _ _ _ _ _ _ _ He Hs) end.
            congruence.
          * contradiction.
        + eassumption.
        + eassumption.
      - cbn [app]. rewrite graph.union_put_r. apply dfs_untree_edge.
        + eassumption.
        + intro Hedge. apply graph.edge_union in Hedge. destruct Hedge as [Hg | Hg0].
          * match goal with He : dfs_fold_state u _ _ _ _ _ _ |- _ =>
              pose proof (dfs_path_unseen _ _ _ _ _ _ _ _ He (in_eq _ _)) as Hun end.
            destruct Hun as [-> | Hun].
            -- cbv [graph.edge] in Hg. rewrite Hedges in Hg. destruct Hg.
            -- pose proof (dfs_source_seen _ _ _ _ _ _ _ _ _ Hroot H1 Hg) as Hsn. congruence.
          * contradiction.
        + eassumption.
      - eapply dfs_finish. eassumption.
    Qed.

    Definition graph_corresp vs vs' (g g_acc : graph) :=
      (forall s, In s (graph.sources g_acc) -> In s vs'/\  ~In s vs) /\
        (forall u v,
            graph.edge g u v ->
            In u vs' ->
            ~ In u vs ->
            graph.edge g_acc u v) /\
        (forall u v, graph.edge g_acc u v -> graph.edge g u v).


    Lemma graph_corresp_eq vs g g_acc :
      graph_corresp [] vs g g_acc ->
      (forall u v, graph.edge g_acc u v <-> graph.edge g u v /\ In u vs).
    Proof.
      cbv [graph_corresp]. intros. fwd. split.
      - intros. especialize Hp0.
        { apply graph.sources_spec. eapply in_not_nil. eassumption. }
        fwd. auto.
      - intros. fwd. auto.
    Qed.

    Definition weak_graph_corresp root root_edges vs vs' (g g_acc : graph) :=
      (forall s, In s (graph.sources g_acc) -> In s vs'/\  ~In s vs) /\
        (forall u v,
            graph.edge g u v ->
            In u vs' ->
            ~ In u vs ->
            u <> root ->
            graph.edge g_acc u v) /\
        (forall v, graph.edge g_acc root v <-> In v root_edges) /\
        (forall u v, graph.edge g_acc u v -> graph.edge g u v).

    Definition no_long_paths (g : graph) root vs n :=
      forall p,
        path (graph.edge g) root p ->
        NoDup (root :: p) ->
        Forall (fun v => ~In v vs) (root :: p) ->
        S (S (length p)) < n.

    Lemma no_long_paths_step g u v vs n :
      no_long_paths g u vs (S n) ->
      ~In u vs ->
      graph.edge g u v ->
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
        dfs_fold_state root (root :: vs) (tree_edge_upd st0 vs root) vs' st' [] g_acc /\
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
      simpl in H. simpl. rewrite Hroot in *.
      cbv [finish'] in H. Tactics.destruct_one_match_hyp. fwd.
      eenough (exists g_acc, _ /\ weak_graph_corresp root (rev (graph.edges g root)) vs vs' g g_acc) as [g_acc H].
      { exists g_acc. split.
        - apply dfs_finish. eapply (proj1 H).
        - destruct H as [_ H].
          cbv [graph_corresp].
          cbv [weak_graph_corresp] in H. fwd. split; auto. split; auto. intros.
          destruct (eqb_boolspec _ u root) as [Hu | Hu].
          { subst. apply Hp2. rewrite <- in_rev. assumption. }
          apply Hp1; assumption. }
      rewrite <- fold_left_rev_right in E.
      revert vs' s E.
      apply fold_right_inv_NoDup.
      - apply NoDup_rev. apply graph.edges_NoDup.
      - intros. fwd. eexists. split; [constructor|].
        cbv [weak_graph_corresp]. split.
        { rewrite graph.sources_empty. simpl. contradiction. }
        split; cycle 1.
        { cbv [graph.edge]. rewrite graph.edges_empty. simpl. split.
          - intros. split; auto.
          - intros * H.  rewrite graph.edges_empty in H. destruct H. }
        intros. exfalso. destruct H1; subst; auto.
      - intros * Hnotin Hin H * Hdfs. destruct a'.
        specialize (H _ _ eq_refl). fwd. apply in_rev in Hin.
        destruct (set_contains l b) eqn:Eb.
        { destruct n; [lia|]. simpl in Hdfs. rewrite Eb in Hdfs. fwd.
          eexists. split.
          - apply dfs_untree_edge.
            + eassumption.
            + intro. apply Hnotin. cbv [weak_graph_corresp] in Hp1. fwd.
              apply Hp1p2. assumption.
            + simpl. assumption.
          - cbv [weak_graph_corresp] in *. fwd. ssplit.
            + cbv [incl]. intros v Hv. apply graph.sources_put in Hv. destruct Hv; auto.
              subst. eapply seen_mono in Hp0.
              -- apply set_contains_true in Hp0. split; [exact Hp0|].
                 apply set_contains_false in Hroot. assumption.
              -- apply set_contains_head.
            + intros. rewrite graph.edge_put. left.
              apply Hp1p1; auto.
            + intros. cbv [graph.edge]. rewrite graph.edges_put.
              cbv [graph.edge] in Hp1p2. rewrite Hp1p2.
              simpl. split; intros [?|?]; fwd; auto.
            + intros * H. apply graph.edge_put in H.
              destruct H as [H|H]; fwd; auto. }
        apply IHn in Hdfs.
        + fwd.
          eexists. split.
          -- eapply dfs_fold_state_trans with (p' := nil).
             ++ apply dfs_tree_edge. 2: eassumption.
                --- intros H. cbv [weak_graph_corresp] in Hp1. fwd. apply Hp1p2 in H.
                    eauto.
                --- simpl. assumption.
             ++ simpl. rewrite eqb_refl_true by assumption. reflexivity.
             ++ apply forall_not_in_nil. intros. rewrite graph.edges_put.
                intros [H|H].
                --- cbv [weak_graph_corresp] in Hp1. fwd.
                    apply in_not_nil in H.
                    apply graph.sources_spec in H. apply Hp1p0 in H.
                    apply set_contains_false in Eb. fwd. auto.
                --- fwd. eapply seen_mono in Hp0; cycle 1.
                    { apply set_contains_head. }
                    congruence.
             ++ eassumption.
          -- cbv [weak_graph_corresp]. cbv [weak_graph_corresp] in Hp1. fwd.
             apply seen_mono' in Hp0, Hdfsp0.
             ssplit.
             ++ cbv [incl]. intros v Hv. rewrite graph.sources_union, graph.sources_put in Hv.
                destruct Hv as [[Hv|Hv]|Hv].
                --- apply Hp1p0 in Hv. fwd. split; auto. apply Hdfsp0. simpl. auto.
                --- subst. split.
                    +++ apply Hdfsp0. simpl. right. apply Hp0. simpl. auto.
                    +++ apply set_contains_false in Hroot. exact Hroot.
                --- cbv [graph_corresp] in Hdfsp1. fwd. apply Hdfsp1p0 in Hv. fwd.
                    split; auto. intro. apply Hvp1. apply Hp0. simpl. auto.
             ++ intros. cbv [graph.edge]. rewrite graph.edges_union, graph.edges_put.
                destruct (set_contains l u) eqn:Hu;
                  [apply set_contains_true in Hu | apply set_contains_false in Hu].
                --- left. left. apply Hp1p1; auto.
                --- right. apply Hdfsp1; auto.
             ++ intros. cbv [graph.edge]. rewrite graph.edges_union, graph.edges_put.
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
             ++ intros. cbv [graph.edge] in H.
                rewrite graph.edges_union, graph.edges_put in H.
                destruct H as [[H|H]|H]; fwd; auto.
                cbv [graph_corresp] in Hdfsp1. fwd. auto.
        + eapply no_long_paths_incl.
          -- apply no_long_paths_step; try eassumption.
             apply set_contains_false in Hroot. exact Hroot.
          -- apply seen_mono' in Hp0. exact Hp0.
        + assumption.
    Qed.


    Lemma paths_limited g root :
      no_long_paths g root [] (S (S (S (length (graph.sources g))))).
    Proof.
      cbv [no_long_paths]. intros p H1 H2 _. apply graph.path_in_graph in H1.
      apply NoDup_removelast in H2. eapply NoDup_incl_length in H2; [|eassumption].
      rewrite length_removelast_cons in H2. lia.
    Qed.

    Lemma dfs_fold_sound g st0 root vs st :
      dfs_fold g st0 root = (vs, st) ->
      exists g_acc,
        dfs_fold_state root (root :: []) (tree_edge_upd st0 [] root) vs st [] g_acc /\
          (forall u v, graph.edge g_acc u v <-> graph.edge g u v /\ In u vs).
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


  Lemma visited_closed g n vs root u v st vs' st' :
    no_long_paths g root vs n ->
    dfs_fold' g n (vs, st) root = (vs', st') ->
    In u vs' ->
    graph.edge g u v ->
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
        -- intros. fwd. ssplit; simpl; auto using incl_cons_r. intros [Hx|Hx]; subst; auto.
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


  Lemma dfs_fold'_connected g n vs st0 st root u vs' :
    dfs_fold' g n (vs, st0) root = (vs', st) ->
    In u vs' ->
    In u vs \/ reaches (graph.edge g) root u.
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
    reaches (graph.edge g) root u.
  Proof.
    intros H1 H2. eapply dfs_fold'_connected in H1; eauto.
    destruct H1 as [[]|?]. assumption.
  Qed.

  Lemma dfs_fold_explores_everything g st root vs u v st' :
    dfs_fold g st root = (vs, st') ->
    reaches (graph.edge g) root u ->
    graph.edge g u v ->
    In u vs.
  Proof.
    intros. cbv [dfs_fold plus] in H. eapply edge_closed_reaches_in; cycle 1.
    2: eassumption.
    { apply dfs_fold'_self in H; [|lia]. assumption. }
    intros. eapply visited_closed in H; eauto.
    { destruct H as [[]|?]. assumption. }
    apply paths_limited.
  Qed.

  Definition reachable_subgraph root (g' g : graph) :=
    forall u v, graph.edge g' u v <-> graph.edge g u v /\ reaches (graph.edge g) root u.

  Definition dfs_fold_spec g st0 root vs st :
    dfs_fold g st0 root = (vs, st) ->
    exists g',
      reachable_subgraph root g' g /\
        dfs_fold_state root (root :: []) (tree_edge_upd st0 [] root) vs st [] g'.
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

  Hint Unfold In : incl.
  Hint Immediate incl_refl : incl.
  Hint Resolve incl_cons incl_tl : incl.

  (*TODO this could be much stronger.   i'll strengthen it when needed*)
  Lemma dfs_fold_state_p_good root st0 vs st p g :
    dfs_fold_state root [root] st0 vs st p g ->
    incl p vs.
  Proof.
    induction 1; auto with incl.
    apply incl_cons_inv in IHdfs_fold_state. fwd. auto.
  Qed.

  Lemma dfs_fold_state_vs_good root st0 vs st p g :
    dfs_fold_state root [root] st0 vs st p g ->
    same_set vs (root :: graph.all_nodes g).
  Proof.
    induction 1.
    - rewrite graph.all_nodes_empty. apply same_set_refl.
    - cbv [same_set] in *. simpl. intros. rewrite graph.all_nodes_put.
      rewrite IHdfs_fold_state. simpl.
      split; intros H'; repeat destruct H' as [H'|H']; subst; auto.
      apply dfs_fold_state_p_good in H0. apply incl_cons_inv in H0. fwd.
      apply IHdfs_fold_state in H0p0. simpl in H0p0. destruct H0p0; auto.
    - cbv [same_set] in *. simpl. intros. rewrite graph.all_nodes_put.
      rewrite IHdfs_fold_state. simpl.
      split; intros H'; repeat destruct H' as [H'|H']; subst; auto.
      + apply IHdfs_fold_state. eapply dfs_fold_state_p_good; [eassumption|].
        simpl. auto.
      + apply set_contains_true in H1. apply IHdfs_fold_state. auto.
    - assumption.
  Qed.
  End fold.
End __.
