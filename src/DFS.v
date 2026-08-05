From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb.
From coqutil Require Import Tactics.destr Tactics.Tactics Tactics.fwd.
From GraphSearch Require Import GraphInterface.
Import ListNotations.

Lemma fold_right_inv {A B} (P : list B -> A -> Prop) (f : B -> A -> A) l a :
  P [] a ->
  (forall a' b l', P l' a' -> P (b :: l') (f b a')) ->
  P l (fold_right f a l).
Proof. intros. induction l; simpl; auto. Qed.

Lemma fold_right_inv_NoDup {A B} (P : list B -> A -> Prop) (f : B -> A -> A) l a :
  NoDup l ->
  P [] a ->
  (forall a' b l', ~In b l' -> P l' a' -> P (b :: l') (f b a')) ->
  P l (fold_right f a l).
Proof.
  intros H ? ?. induction l; simpl; auto. inversion_clear H. eauto.
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
      forall u v,
        graph_edge g u v ->
        In u vs' ->
        ~ In u vs ->
        graph_edge g_acc u v.

    Definition weak_graph_corresp root root_edges vs vs' g g_acc :=
      (forall u v,
        graph_edge g u v ->
        In u vs' ->
        ~ In u vs ->
        u <> root ->
        graph_edge g_acc u v) /\
        (forall v, graph_edge g_acc root v <-> In v root_edges).

    Print path. Print reachable.
    Definition no_long_paths g root vs n :=
      forall p,
        path (graph_edge g) root p ->
        NoDup p ->
        Forall (fun v => ~In v vs) p ->
        S (length p) < n.

    Lemma dfs_fold_sound1 root vs n st0 g vs' st' :
      no_long_paths g root vs n ->
      set_contains vs root = false ->
      dfs_fold' g n (vs, st0) root = (vs', st') ->
      exists g_acc,
        dfs_fold_state root (edge_upd' (vs, st0) root) (vs', st') [] g_acc /\
          graph_corresp vs vs' g g_acc.
    Proof.
      revert root vs st0 vs' st'. induction n.
      { intros *. intros Hn. exfalso. cbv [no_long_paths] in Hn.
        specialize (Hn []). simpl in Hn.
        specialize (Hn ltac:(constructor) ltac:(constructor) ltac:(constructor)).
        lia. }
      intros root vs st0 vs' st' Hn Hroot H.
      assert (n <> 0).
      { intro. subst. cbv [no_long_paths] in Hn. specialize (Hn []).
        specialize (Hn ltac:(constructor) ltac:(constructor) ltac:(constructor)).
        lia. }
      simpl in H. cbv [edge_upd']. simpl. rewrite Hroot in *.
      cbv [finish'] in H. Tactics.destruct_one_match_hyp. fwd.
      eenough (exists g_acc, _ /\ weak_graph_corresp root (rev (graph.edges g root)) vs vs' g g_acc) as [g_acc H].
      { exists g_acc. split.
        - apply dfs_finish with (st := (_, _)). eapply (proj1 H).
        - destruct H as [_ H].
          cbv [graph_corresp]. intros.
          cbv [weak_graph_corresp] in H. fwd.
          assert (u = root \/ u <> root) as [Hu|Hu] by admit.
          { subst. apply Hp1. rewrite <- in_rev. assumption. }
          apply Hp0; assumption. }
      rewrite <- fold_left_rev_right in E.
      revert vs' s E.
      apply fold_right_inv_NoDup.
      - apply NoDup_rev. apply graph.edges_NoDup.
      - intros. fwd. eexists. split; [constructor|].
        cbv [weak_graph_corresp]. split; cycle 1.
        { cbv [graph_edge]. rewrite graph.edges_empty. simpl. intros. split; auto. }
        intros. exfalso. destruct H1; subst; auto.
      - intros * Hnotin H * Hdfs. destruct a'. specialize (H _ _ eq_refl). fwd.
        simpl in Hdfs.
        destruct (set_contains l b) eqn:Eb.
        { destruct n; [lia|]. simpl in Hdfs. rewrite Eb in Hdfs. fwd.
          eexists. split.
          - apply dfs_untree_edge with (st := (_, _)).
            + eassumption.
            + intro. apply Hnotin. cbv [weak_graph_corresp] in Hp1. fwd.
              apply Hp1p1. assumption.
            + simpl. assumption.
          - cbv [weak_graph_corresp] in *. fwd. split.
            + intros. cbv [graph_edge]. rewrite graph.edges_put. left.
              apply Hp1p0; auto.
            + intros. cbv [graph_edge]. rewrite graph.edges_put.
              cbv [graph_edge] in Hp1p1. rewrite Hp1p1.
              simpl. split; intros [?|?]; fwd; auto. }
        apply IHn in Hdfs.
        fwd.
        Tactics.destruct_one_match_hyp. fwd.
        fwd.
              constructor.
          cbv [dfs_fold'] in E.

        eexists.
        + constructor.
      destruct (set_contains vs root) eqn:Eroot.
      - fwd. eexists. split.
        + Print dfs_fold_state. econstructor. fwd. exists graph.empty. split.
        - pose proof dfs_finish. Print dfs_fold_state. constructor.


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
      + assert (HY : In a (fst (fold_left
          (dfs_fold' untree_edge_accumulate tree_edge_accumulate finish_accumulate g m)
          (graph.edges g w) (tree_edge_upd' tree_edge_accumulate (vs, (path, G)) w)))).
        { apply (fold_left_invariant (fun _ st => In a (fst st))).
          - cbn [tree_edge_upd' tree_edge_accumulate fst]. right. exact Ha.
          - intros st c l' Hst. apply IH. exact Hst. }
        revert HY.
        match goal with |- In a (fst ?X) -> In a (fst (finish' _ ?X _)) =>
          destruct X as [vsY sY] end.
        cbn [finish' fst]. exact (fun h => h).
  Qed.

  Lemma graph_accumulator_S g m vs path G w :
    graph_accumulator g (S m) (vs, (path, G)) w
    = if set_contains vs w
      then untree_edge_upd' untree_edge_accumulate (vs, (path, G)) w
      else finish' finish_accumulate (fold_left (graph_accumulator g m) (graph.edges g w)
             (tree_edge_upd' tree_edge_accumulate (vs, (path, G)) w)) w.
  Proof. reflexivity. Qed.

  Lemma accum_visited_self g m vs path G c :
    0 < m -> In c (fst (graph_accumulator g m (vs, (path, G)) c)).
  Proof.
    intro Hm. destruct m as [|k]; [lia|].
    rewrite graph_accumulator_S. destruct (set_contains vs c) eqn:Hc.
    - cbn [untree_edge_upd' untree_edge_accumulate fst].
      apply set_contains_iff_In; exact Hc.
    - assert (HY : In c (fst (fold_left (graph_accumulator g k) (graph.edges g c)
                               (tree_edge_upd' tree_edge_accumulate (vs, (path, G)) c)))).
      { apply (fold_left_invariant (fun _ st => In c (fst st))).
        - cbn [tree_edge_upd' tree_edge_accumulate fst]. left; reflexivity.
        - intros st c' l' Hst. apply accum_visited_mono; exact Hst. }
      revert HY.
      match goal with |- In c (fst ?F) -> In c (fst (finish' _ ?F _)) =>
        destruct F as [vsF sF] end.
      cbn [finish' fst]. exact (fun h => h).
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

  (*TODO*)
  (*from accum_visited_self we get that *)

  Context {state}
    (untree_edge_upd : state -> list V -> V -> state)
    (tree_edge_upd : state -> list V -> V -> state)
    (finish : state -> list V -> V -> state).

  Local Notation dfs_fold'0 := (dfs_fold' untree_edge_upd tree_edge_upd finish).
  Local Notation edge_upd'0 := (edge_upd' untree_edge_upd tree_edge_upd).
  Local Notation dfs_fold_state0 := (dfs_fold_state untree_edge_upd tree_edge_upd finish).

    cbn [already_seen] in Hroot.
    assert (Hedgeupd : edge_upd'0 (vs, st0) root = tree_edge_upd' tree_edge_upd (vs, st0) root).
    { unfold edge_upd'. cbn [already_seen]. rewrite Hroot. reflexivity. }
    assert (Habs : dfs_fold'0 g (S n') (vs, st0) root
      = finish' finish (fold_left (dfs_fold'0 g n') (graph.edges g root)
          (tree_edge_upd' tree_edge_upd (vs, st0) root)) root).
    { rewrite dfs_fold'_S. cbn [already_seen]. rewrite Hroot. reflexivity. }
    rewrite Hedgeupd, Habs.
    set (st_init := tree_edge_upd' tree_edge_upd (vs, st0) root) in *.
    rewrite graph_accumulator_S, Hroot. cbn [tree_edge_upd' tree_edge_accumulate].
    pose (P := fun (remaining : list V) (a : list V * state)
                   (b : list V * (list V * graph)) =>
      fst a = fst b /\ fst (snd b) = [root] /\
      dfs_fold_state0 root st_init a [root] (snd (snd b)) /\
      (forall x, In x remaining -> ~ graph_edge (snd (snd b)) root x) /\
      NoDup remaining /\ incl remaining (graph.edges g root)).
    assert (HP : P [] (fold_left (dfs_fold'0 g n') (graph.edges g root) st_init)
                      (fold_left (graph_accumulator g n') (graph.edges g root)
                         (root :: vs, ([root], graph.empty)))).
    { apply (fold_left_invariant2 P).
      - subst P; cbn beta. split; [|split; [|split; [|split; [|split]]]].
        + unfold st_init; cbn [tree_edge_upd' fst]; reflexivity.
        + reflexivity.
        + apply dfs_init.
        + intros x Hx. cbv [graph_edge]. cbn [snd]. rewrite graph.edges_empty. apply in_nil.
        + apply graph.edges_NoDup.
        + apply incl_refl.
      - intros a b w remaining' HP'. subst P; cbn beta in HP' |- *.
        destruct HP' as (Hfst & Hbpath & Hstate & Htrack & Hnodup & Hincl).
        destruct a as [vs_a s_a], b as [vs_b [p_b g_b]].
        cbn [fst snd] in Hfst, Hbpath, Hstate, Htrack |- *.
        subst vs_a p_b.
        assert (Hwni : ~ In w remaining') by (inversion Hnodup; auto).
        destruct n' as [|n''].
        + (* no fuel: the child is a no-op, whether seen or unseen *)
          change (dfs_fold'0 g 0 (vs_b, s_a) w) with (vs_b, s_a).
          change (graph_accumulator g 0 (vs_b, ([root], g_b)) w) with (vs_b, ([root], g_b)).
          split; [reflexivity | split; [reflexivity | split; [exact Hstate | split; [|split]]]].
          * intros x Hx. apply Htrack; right; exact Hx.
          * inversion Hnodup; auto.
          * intros y Hy; apply Hincl; right; exact Hy.
        + destruct (set_contains vs_b w) eqn:Hw.
          * (* seen: untree edge *)
            unfold graph_accumulator.
            rewrite (dfs_fold'_seen untree_edge_upd tree_edge_upd finish g n'' (vs_b, s_a) w)
              by (cbn [already_seen]; exact Hw).
            rewrite (dfs_fold'_seen untree_edge_accumulate tree_edge_accumulate finish_accumulate
                       g n'' (vs_b, ([root], g_b)) w) by (cbn [already_seen]; exact Hw).
            split; [|split; [|split; [|split; [|split]]]].
            -- cbn [untree_edge_upd' untree_edge_accumulate fst]. reflexivity.
            -- cbn [untree_edge_upd' untree_edge_accumulate fst snd]. reflexivity.
            -- replace (snd (snd (untree_edge_upd' untree_edge_accumulate (vs_b, ([root], g_b)) w)))
                 with (graph.put g_b root w) by reflexivity.
               apply dfs_untree_edge.
               ++ exact Hstate.
               ++ apply Htrack; apply in_eq.
               ++ cbn [already_seen]; exact Hw.
            -- cbn [untree_edge_upd' untree_edge_accumulate snd].
               intros x Hx Hedge. cbv [graph_edge] in Hedge.
               rewrite graph.edges_put in Hedge. destruct Hedge as [Hold | [_ Hxw]].
               ++ apply (Htrack x); [right; exact Hx | exact Hold].
               ++ subst x; contradiction.
            -- inversion Hnodup; auto.
            -- intros y Hy; apply Hincl; right; exact Hy.
          * (* unseen: explore *)
            assert (Hrootseen : set_contains vs_b root = true).
            { pose proof (already_seen_mono _ _ _ root st_init (vs_b, s_a) [root] g_b root Hstate) as Hm.
              cbn [already_seen] in Hm. apply Hm.
              unfold st_init; apply already_seen_tree_edge_upd_self. }
            assert (Hrw : root <> w) by (intro; subst; congruence).
            (* the IH for child w *)
            pose proof (IH w vs_b s_a ltac:(lia) Hw) as Hchild.
            revert Hchild.
            destruct (graph_accumulator g (S n'') (vs_b, ([], graph.empty)) w)
              as [vsw [pw g_w]] eqn:Ew.
            cbn [snd].
            assert (Hedgew : edge_upd'0 (vs_b, s_a) w = tree_edge_upd' tree_edge_upd (vs_b, s_a) w).
            { unfold edge_upd'. cbn [already_seen]. rewrite Hw. reflexivity. }
            rewrite Hedgew. intro Hchild.
            (* the outer edges list is empty for w *)
            assert (Hedges : graph.edges (graph.put g_b root w) w = []).
            { destruct (graph.edges (graph.put g_b root w) w) as [|y ys] eqn:E; [reflexivity|].
              exfalso.
              assert (Hin : graph_edge (graph.put g_b root w) w y)
                by (cbv [graph_edge]; rewrite E; left; reflexivity).
              cbv [graph_edge] in Hin. rewrite graph.edges_put in Hin.
              destruct Hin as [Hin | [Hwr _]]; [| congruence].
              pose proof (dfs_source_seen _ _ _ root st_init (vs_b, s_a) [root] g_b w y
                ltac:(unfold st_init; apply already_seen_tree_edge_upd_self) Hstate) as Hss.
              cbv [graph_edge] in Hss. specialize (Hss Hin).
              cbn [already_seen] in Hss. congruence. }
            (* build the dfs_fold_state via tree edge + trans *)
            assert (Hne : ~ graph_edge g_b root w).
            { intro Hedge.
              pose proof (dfs_target_seen _ _ _ root st_init (vs_b, s_a) [root] g_b root w Hstate Hedge) as Ht.
              cbn [already_seen] in Ht. congruence. }
            assert (Htree : dfs_fold_state0 root st_init
                              (tree_edge_upd' tree_edge_upd (vs_b, s_a) w) (w :: [root])
                              (graph.put g_b root w)).
            { apply dfs_tree_edge; [exact Hne | exact Hstate | cbn [already_seen]; exact Hw]. }
            pose proof (dfs_fold_state_trans _ _ _ root st_init (tree_edge_upd' tree_edge_upd (vs_b, s_a) w)
              (dfs_fold'0 g (S n'') (vs_b, s_a) w) [root] [] (graph.put g_b root w) g_w w
              Htree
              ltac:(unfold st_init; apply already_seen_tree_edge_upd_self)
              Hedges Hchild) as Htrans.
            cbn [app] in Htrans.
            (* now assemble P remaining' *)
            split; [|split; [|split; [|split; [|split]]]].
            -- apply (dfs_fold'_fst untree_edge_upd tree_edge_upd finish
                       untree_edge_accumulate tree_edge_accumulate finish_accumulate g (S n'')).
               reflexivity.
            -- apply accum_path_inv.
            -- rewrite (accum_step g n'' vs_b g_b root w Hw), Ew. cbn [snd]. exact Htrans.
            -- intros x Hx Hedge. rewrite (accum_step g n'' vs_b g_b root w Hw), Ew in Hedge.
               cbn [snd] in Hedge. cbv [graph_edge] in Hedge.
               rewrite graph.edges_union in Hedge. destruct Hedge as [He1 | He2].
               ++ rewrite graph.edges_put in He1. destruct He1 as [Hold | [_ Hxw]].
                  ** apply (Htrack x); [right; exact Hx | exact Hold].
                  ** subst x; contradiction.
               ++ pose proof (dfs_source_init _ _ _ w (tree_edge_upd' tree_edge_upd (vs_b, s_a) w)
                    (dfs_fold'0 g (S n'') (vs_b, s_a) w) [] g_w root x Hchild) as Hsi.
                  cbv [graph_edge] in Hsi. specialize (Hsi He2).
                  destruct Hsi as [Hrw' | Hunseen]; [congruence|].
                  cbn [already_seen] in Hunseen. simpl in Hunseen.
                  rewrite Hrootseen in Hunseen. destruct (eqb root w); discriminate.
            -- inversion Hnodup; auto.
            -- intros y Hy; apply Hincl; right; exact Hy. }
    subst P; cbn beta in HP.
    destruct HP as (_ & _ & Hstate & _).
    revert Hstate.
    destruct (fold_left (graph_accumulator g n') (graph.edges g root)
                (root :: vs, ([root], graph.empty))) as [vsF [pF gF]].
    cbn [finish' finish_accumulate snd]. intro Hstate.
    apply dfs_finish. exact Hstate.
  Qed.

  Lemma dfs_fold_sound root vs n st0 g :
    already_seen (vs, st0) root = false ->
    (forall p v, path_to (graph_edge g) root p v ->
       Forall (fun w => ~ In w vs) (root :: p) -> length p < n) ->
    exists g',
      dfs_fold_state0 root (edge_upd'0 (vs, st0) root)
        (dfs_fold'0 g n (vs, st0) root) [] g' /\
      restriction root vs g g'.
  Proof.
    intro Hroot. cbn [already_seen] in Hroot. intro Hfuel.
    exists (snd (snd (graph_accumulator g n (vs, ([], graph.empty)) root))).
    split.
    - assert (Hrootvs : ~ In root vs).
      { intro Hin. apply set_contains_iff_In in Hin. rewrite Hin in Hroot. discriminate. }
      assert (Hn : 0 < n).
      { pose proof (Hfuel [] root
          ltac:(unfold path_to; split; [exact I | reflexivity])
          ltac:(constructor; [exact Hrootvs | constructor])) as Hlen.
        cbn [length] in Hlen. lia. }
      pose proof (dfs_fold_sound1 root vs n st0 g Hn Hroot) as Hs1. revert Hs1.
      destruct (graph_accumulator g n (vs, ([], graph.empty)) root) as [vsF [pF gF]].
      intro Hs1. exact Hs1.
    - admit.
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
