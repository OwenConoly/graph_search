From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb.
From coqutil Require Import Tactics.destr Tactics.Tactics Tactics.fwd.
From GraphSearch Require Import GraphInterface.
From Stdlib Require Import Classical_Prop.
Import ListNotations.

Lemma fold_right_inv {A B} (P : list B -> A -> Prop) (f : B -> A -> A) l a :
  P [] a ->
  (forall a' b l', P l' a' -> P (b :: l') (f b a')) ->
  P l (fold_right f a l).
Proof. intros. induction l; simpl; auto. Qed.

Lemma fold_right_inv_NoDup {A B} (P : list B -> A -> Prop) (f : B -> A -> A) l a :
  NoDup l ->
  P [] a ->
  (forall a' b l', ~In b l' -> In b l -> P l' a' -> P (b :: l') (f b a')) ->
  P l (fold_right f a l).
Proof.
  intros H ? ?. induction l; simpl; auto. simpl in *. inversion_clear H. eauto 6.
Qed.

(* fold_left commutes with a function the step commutes with. *)
Lemma fold_left_hom {A B} (f : A -> B -> A) (k : A -> A) l :
  (forall a b, f (k a) b = k (f a b)) ->
  forall a, fold_left f l (k a) = k (fold_left f l a).
Proof.
  intro Hstep. induction l as [|b l' IH]; intro a; [reflexivity|].
  cbn [fold_left]. rewrite Hstep. apply IH.
Qed.

(* Binary version: relate two folds over the same list with different steps. *)
Lemma fold_left_invariant2 {A B C} (P : list C -> A -> B -> Prop)
      (f : A -> C -> A) (h : B -> C -> B) :
  forall l a b,
    P l a b ->
    (forall a' b' c l', P (c :: l') a' b' -> P l' (f a' c) (h b' c)) ->
    P [] (fold_left f l a) (fold_left h l b).
Proof.
  induction l as [|c l' IH]; intros a b HP Hstep; [exact HP|].
  cbn [fold_left]. apply IH; [apply Hstep; exact HP | exact Hstep].
Qed.

Lemma In_last {A} (l : list A) d :
  l <> [] -> In (last l d) l.
Proof.
  intro Hne. rewrite (app_removelast_last d Hne) at 2.
  apply in_or_app. right. left. reflexivity.
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

      Definition dfs_fold st0 := dfs_fold' (S (length (graph.sources g))) ([], st0).
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
      forall u v,
        graph_edge g u v ->
        In u vs' ->
        ~ In u vs ->
        graph_edge g_acc u v.

    Definition weak_graph_corresp root root_edges vs vs' g g_acc :=
      (forall s, In s (graph.sources g_acc) -> In s vs'/\  ~In s vs) /\
      (forall u v,
        graph_edge g u v ->
        In u vs' ->
        ~ In u vs ->
        u <> root ->
        graph_edge g_acc u v) /\
        (forall v, graph_edge g_acc root v <-> In v root_edges).

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

    Lemma in_not_nil A x (l : list A) :
      In x l ->
      l <> nil.
    Proof. destruct l; simpl; congruence. Qed.

    Lemma dfs_fold_sound1 root vs n st0 g vs' st' :
      no_long_paths g root vs n ->
      set_contains vs root = false ->
      dfs_fold' g n (vs, st0) root = (vs', st') ->
      exists g_acc,
        dfs_fold_state root (edge_upd' (vs, st0) root) (vs', st') [] g_acc /\
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
      { intro. subst. cbv [no_long_paths] in Hn.
        specialize (Hn []). simpl in Hn. especialize Hn; auto.
        - constructor; simpl; auto. constructor.
        - apply set_contains_false in Hroot. auto.
        - lia. }
      simpl in H. cbv [edge_upd']. simpl. rewrite Hroot in *.
      cbv [finish'] in H. Tactics.destruct_one_match_hyp. fwd.
      eenough (exists g_acc, _ /\ weak_graph_corresp root (rev (graph.edges g root)) vs vs' g g_acc) as [g_acc H].
      { exists g_acc. split.
        - apply dfs_finish with (st := (_, _)). eapply (proj1 H).
        - destruct H as [_ H].
          cbv [graph_corresp].
          cbv [weak_graph_corresp] in H. fwd. split; auto. intros.
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
        { cbv [graph_edge]. rewrite graph.edges_empty. simpl. intros. split; auto. }
        intros. exfalso. destruct H1; subst; auto.
      - intros * Hnotin Hin H * Hdfs. destruct a'. specialize (H _ _ eq_refl). fwd.
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
              simpl. split; intros [?|?]; fwd; auto. }
        apply IHn in Hdfs.
        + fwd.
          cbv [edge_upd'] in Hdfsp0. simpl in Hdfsp0. rewrite Eb in Hdfsp0.
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
        + eapply no_long_paths_incl.
          -- apply no_long_paths_step.
             +++ eassumption.
             +++ apply set_contains_false in Hroot. exact Hroot.
             +++ apply in_rev in Hin. apply Hin.
          -- apply already_seen_mono' in Hp0. exact Hp0.
        + assumption.
    Qed.

  End fold.

  Lemma dfs_fold'_seen {St} (u t f : St -> list V -> V -> St) g n st' v :
    already_seen st' v = true -> dfs_fold' u t f g (S n) st' v = untree_edge_upd' u st' v.
  Proof. intro H; cbn [dfs_fold']; rewrite H; reflexivity. Qed.

  Lemma dfs_fold'_S {St} (u t f : St -> list V -> V -> St) g n st' v :
    dfs_fold' u t f g (S n) st' v
    = if already_seen st' v then untree_edge_upd' u st' v
      else finish' f (fold_left (dfs_fold' u t f g n) (graph.edges g v) (tree_edge_upd' t st' v)) v.
  Proof. reflexivity. Qed.

  Definition tree_edge_accumulate (path_g: list V * graph) (_ : list V) (cur : V) :=
    let '(path, g) := path_g in
    (cur :: path,
      match path with
      | [] => g
      | prev :: _ => graph.put g prev cur
      end).

  Definition untree_edge_accumulate (path_g: list V * graph) (_ : list V) (cur : V) :=
    let '(path, g) := path_g in
    (path,
      match path with
      | [] => g
      | prev :: _ => graph.put g prev cur
      end).

  Definition finish_accumulate (path_g : list V * graph) (_ : list V) (_ : V) :=
    let '(path, g) := path_g in
    (tl path, g).

  Definition graph_accumulator := dfs_fold' untree_edge_accumulate tree_edge_accumulate finish_accumulate.

  Lemma graph_accumulator_spec g0 n vs path g w vs' path' g' :
   graph_accumulator g0 n (vs, (path, g)) w = (vs', (path', g')) ->
    path' = path /\ (forall u v,
                       graph_edge g' u v <-> graph_edge g u v \/
                                             In u vs' /\ ~In u vs /\ graph_edge g0 u v \/
                                             (n > 0 /\ exists path0, path = u :: path0 /\ v = w)).
  Proof.
    revert vs path g w vs' path' g'. induction n; intros vs path g w vs' path' g'.
    - simpl. intros. fwd. admit.
    - simpl. intros. destruct (set_contains vs w) eqn:Evs.
      + fwd. split; auto. intros. destruct path'.
        -- split; auto. intros [H|[H|H]]; fwd; auto.
           ++ exfalso. auto.
           ++ discriminate.
        -- cbv [graph_edge]. rewrite graph.edges_put. split; auto.
           ++ intros [H|H]; auto. fwd. right. right. split; [lia|eauto].
           ++ intros [H|[H|H]]; auto.
              --- fwd. exfalso. auto.
              --- fwd. auto.
      + cbv [finish'] in H. Tactics.destruct_one_match_hyp. fwd.
        cbv [finish_accumulate] in H0. Tactics.destruct_one_match_hyp. fwd.
        eenough (incl (w :: vs) vs' /\ l = w :: path /\ _). { exact (proj2 (proj2 H)). }
        revert vs' l g' E. apply fold_left_inv.
        -- intros. fwd. simpl. split; [apply incl_refl|]. split; [reflexivity|].
           split; [reflexivity|].
           intros. destruct path.
           ++ split; auto. intros [H|[H|H]]; fwd; auto.
              --- destruct Hp0; subst.
                  +++ (*easy*) admit.
                  +++ exfalso. auto.
              --- discriminate.
           ++ cbv [graph_edge]. rewrite graph.edges_put. split.
              --- intros [H|H]; auto. fwd. right. right. split; [lia|eauto].
              --- intros [H|[H|H]]; auto.
                  +++ fwd. exfalso. destruct Hp0; auto. subst. (*easy*) admit.
                  +++ fwd. auto.
        -- intros. destruct a as [? [? ?]]. specialize (H0 _ _ _ eq_refl).
           assert (incl l0 vs') by admit.
           apply IHn in E. fwd. split; [eauto using incl_tran|].
           split; [reflexivity|]. split; [reflexivity|]. intros. rewrite Ep1.
           split.
           ++ intros [H'|[H'|H']].
              --- apply H0p3 in H'. destruct H' as [H'|[H'|H']]; auto.
                  right. left. fwd. auto.
              --- fwd. right. left. ssplit; auto. intro.
                  Search (incl (_ :: _) _). apply incl_cons_inv in H0p0. fwd.
                  auto.
              --- fwd. right. left. ssplit; auto.
                  +++ apply incl_cons_inv in H0p0. fwd. auto.
                  +++ (*easy*) admit.
           ++ intros [H'|[H'|H']].
              --- rewrite H0p3. auto.
              --- assert (In u l0 \/ ~In u l0) as [?|?] by admit.
                  +++ fwd. rewrite H0p3. auto 10.
                  +++ fwd. rewrite H0p3. auto 10.
              --- fwd. rewrite H0p3. left. eauto 10.
  Admitted.

  Lemma last_cons (l : list V) a d :
    last (a :: l) d = last l a.
  Proof.
    revert a d. induction l as [|b l' IH]; intros a d; [reflexivity|].
    change (last (b :: l') d = last (b :: l') a).
    rewrite (IH b d), (IH b a). reflexivity.
  Qed.

  Lemma set_contains_iff_In vs v :
    set_contains vs v = true <-> In v vs.
  Proof.
    unfold set_contains. symmetry.
    apply (existsb_eqb_in (aeqb_dec := @eqb_boolspec V eqbV eqb_ok)).
  Qed.

  Lemma accum_visited_mono g n : forall s w a,
    In a (fst s) -> In a (fst (graph_accumulator g n s w)).
  Proof.
    unfold graph_accumulator.
    induction n as [|m IH]; intros [vs [path G]] w a Ha; cbn [fst] in Ha;
      cbn [dfs_fold' already_seen].
    - destruct (set_contains vs w);
        [cbn [untree_edge_upd' untree_edge_accumulate fst] | cbn [fst]]; exact Ha.
    - destruct (set_contains vs w).
      + cbn [untree_edge_upd' untree_edge_accumulate fst]. exact Ha.
      + cbv [finish']. Tactics.destruct_one_match. simpl.
        cbv [tree_edge_upd'] in E.
        revert l p E. apply fold_left_inv; simpl; intros; fwd; simpl; auto.
        destruct a0. especialize H0; eauto. eapply (IH (_, _)) in H0.
        rewrite E in H0. simpl in H0. assumption.
  Qed.

  Lemma accum_visited_self g m vs path G c :
    0 < m -> In c (fst (graph_accumulator g m (vs, (path, G)) c)).
  Proof.
    intro Hm. destruct m as [|k]; [lia|]. simpl.
    destruct (set_contains vs c) eqn:Hc.
    - cbn [untree_edge_upd' untree_edge_accumulate fst].
      apply set_contains_iff_In; exact Hc.
    - cbv [finish']. Tactics.destruct_one_match. simpl.
        cbv [tree_edge_upd'] in E.
        revert l p E. apply fold_left_inv; simpl; intros; fwd; simpl; auto.
        destruct a. especialize H0; eauto.
        eapply accum_visited_mono with (s := (_, _)) in H0. rewrite E in H0. exact H0.
  Qed.

  Lemma incl_cons A (a : A) l :
    incl l (a :: l).
  Proof. Admitted.

  Lemma accum_visited_closed g n : forall vs root,
    (forall p v, path_to (graph_edge g) root p v ->
       Forall (fun w => ~ In w vs) (root :: p) -> NoDup (root :: p) -> length p < n) ->
    forall x y junk,
      In x (fst (graph_accumulator g n (vs, junk) root)) ->
      ~ In x vs ->
      graph_edge g x y ->
      In y (fst (graph_accumulator g n (vs, junk) root)).
  Proof.
    induction n as [|m IH]; intros vs root Hfuel x y junk Hx Hnx He.
    - destruct (Hnx Hx).
    - simpl in Hx. simpl. destruct (set_contains vs root) eqn:Hroot.
      + simpl in Hx. contradiction.
      + remember (finish' _ _ _) as blah. destruct blah as (vs'&?).
        cbv [finish'] in Heqblah. Tactics.destruct_one_match_hyp. simpl in *. fwd.
        enough ((In x l -> x = root \/ In y l) /\ incl vs l /\ In root l).
        { fwd. apply Hp0 in Hx. destruct Hx; subst; auto. (*easy*) admit. }
        clear Hx. revert E. revert l p0. apply fold_left_inv.
        -- intros. fwd. split; simpl; auto using incl_cons. intros [Hx|Hx]; subst; auto.
           exfalso. auto.
        -- intros. destruct a. specialize (H0 _ _ eq_refl). fwd.
           split.
           2: { (*easy*) admit. }
           intros.
           assert (In x l0 \/ ~In x l0) as [?|?] by admit.
           { apply H0p0 in H1. assert (incl l0 l) by admit.
             destruct H1; eauto using incl_tran. }
           specialize (IH l0 b). epose proof (IH _) as IH. Unshelve.
           2: { intros. specialize (Hfuel (b :: p1) v). especialize Hfuel.
                - cbv [path_to]. cbv [path_to] in H2. rewrite last_cons. fwd.
                  simpl. auto.
                - constructor; auto.
                  + (*easy*) admit.
                  + (*easy*) admit.
                - (*easy*) admit.
                - simpl in Hfuel. lia. }
           epose proof (IH _ _ _) as IH. rewrite E in IH. simpl in IH.
           specialize (IH H0 H1 He). auto.
  Admitted.

  Lemma dfs_fold_correct root st0 g :
    (forall p v, path_to (graph_edge g) root p v ->
       length p < S (length (graph.sources g))) ->
    exists g',
      dfs_fold_state0 root (edge_upd'0 ([], st0) root)
        (dfs_fold untree_edge_upd tree_edge_upd finish g st0 root) [] g' /\
      restriction root [] g g'.
  Proof.
    intro Hbound. unfold dfs_fold. apply dfs_fold_sound.
    - reflexivity.
    - intros p v Hpt _. exact (Hbound p v Hpt).
  Qed.

  Definition check_tree :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree).
End __.
