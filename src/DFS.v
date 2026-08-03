From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb.
From coqutil Require Import Tactics.destr Tactics.Tactics.
From GraphSearch Require Import GraphInterface.
Import ListNotations.

(* Generic; belongs in a list util. Invariant indexed by the unprocessed suffix,
   so the step for the head knows it is still pending. *)
Lemma fold_left_invariant {A B} (P : list B -> A -> Prop) (f : A -> B -> A) :
  forall l a,
    P l a ->
    (forall a' b l', P (b :: l') a' -> P l' (f a' b)) ->
    P [] (fold_left f l a).
Proof.
  induction l as [|b l' IH]; intros a HP Hstep; [exact HP|].
  cbn [fold_left]. apply IH; [apply Hstep; exact HP | exact Hstep].
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
        if already_seen st' v then untree_edge_upd' st' v else
          match n with
          | S n' => finish' (fold_left (dfs_fold' n') (graph.edges g v) (tree_edge_upd' st' v)) v
          | O => st'
          end.

      Definition dfs_fold st0 := dfs_fold' (S (length (graph.sources g))) ([], st0).
    End with_graph.

    Inductive dfs_fold_state (root : V) (st0 : state') : state' -> list V (*current path*)-> graph (*explored edges*) -> Prop :=
    | dfs_init : dfs_fold_state _ _ st0 [] graph.empty
    | dfs_tree_edge st p g v :
      ~graph_edge g (hd root p) v ->
      dfs_fold_state _ _ st p g ->
      already_seen st v = false ->
      dfs_fold_state _ _ (tree_edge_upd' st v) (v :: p) (graph.put g (hd root p) v)
    | dfs_untree_edge st p g v :
      dfs_fold_state _ _ st p g ->
      ~graph_edge g (hd root p) v ->
      already_seen st v = true ->
      dfs_fold_state _ _ (untree_edge_upd' st v) p (graph.put g (hd root p) v)
    | dfs_finish st u p g :
      dfs_fold_state _ _ st (u :: p) g ->
      dfs_fold_state _ _ (finish' st u) p g.

  End fold.

  Context {ok : graph.ok graph}.
  Context {eqb_ok : Eqb_ok eqbV}.

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

  Definition graph_accumulator := dfs_fold' tree_edge_accumulate untree_edge_accumulate finish_accumulate.

  Context {state}
    (untree_edge_upd : state -> list V -> V -> state)
    (tree_edge_upd : state -> list V -> V -> state).

  Local Notation dfs_fold'0 := (dfs_fold' untree_edge_upd tree_edge_upd).

  Lemma dfs_fold_sound1 root vs n st0 g :
    dfs_fold_state root (edge_upd' (vs, st0) root) (dfs_fold' g n (vs, st0) root) [] (graph_accumulator g n (vs, st0) root).
  Proof. (*TODO*).


    Lemma graph_edge_union g1 g2 x y :
      graph_edge (graph.union g1 g2) x y <-> graph_edge g1 x y \/ graph_edge g2 x y.
    Proof. cbv [graph_edge]. apply graph.edges_union. Qed.

    From coqutil Require Import Tactics.fwd.
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

    Lemma already_seen_mono root st0 st p g y :
      dfs_fold_state root st0 st p g ->
      already_seen st0 y = true ->
      already_seen st y = true.
    Proof.
    (*   induction 1; eauto using already_seen_tree_edge_upd, already_seen_untree_edge_upd. *)
      (* Qed. *)
      Admitted.

    Lemma dfs_target_seen root st0 st p g x y :
      dfs_fold_state root st0 st p g -> graph_edge g x y -> already_seen st y = true.
    Proof.
      intro H. revert x y.
      induction H as [ | st2 p0 g0 v Hne Hrec IH Hseen
                       | st2 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. destruct He.
      - rewrite graph.edges_put in He. destruct He as [Hold | [_ Hvy]].
        + apply already_seen_tree_edge_upd. apply (IH x y). exact Hold.
        + subst y. apply already_seen_tree_edge_upd_self.
      - rewrite graph.edges_put in He. rewrite already_seen_untree_edge_upd.
        destruct He as [Hold | [_ Hvy]].
        + apply (IH x y). exact Hold.
        + subst y. exact Hseen.
      - apply (IH x y). exact He.
    Qed.

    Lemma dfs_path_seen root st0 st p g z :
      dfs_fold_state root st0 st p g -> In z p -> already_seen st z = true.
    Proof.
      intro H. revert z.
      induction H as [ | st2 p0 g0 v Hne Hrec IH Hseen
                       | st2 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros z Hz.
      - destruct Hz.
      - destruct Hz as [<- | Hz].
        + apply already_seen_tree_edge_upd_self.
        + apply already_seen_tree_edge_upd. apply IH. exact Hz.
      - rewrite already_seen_untree_edge_upd. apply IH. exact Hz.
      - apply IH. right. exact Hz.
    Qed.

    Lemma dfs_path_unseen root st0 st p g z :
      dfs_fold_state root st0 st p g -> In z p -> already_seen st0 z = false.
    Proof.
      intro H. revert z.
      induction H as [ | st2 p0 g0 v Hne Hrec IH Hseen
                       | st2 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros z Hz.
      - destruct Hz.
      - destruct Hz as [<- | Hz].
        + destruct (already_seen st0 v) eqn:E; [ | reflexivity ].
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
      induction H as [ | st2 p0 g0 v Hne Hrec IH Hseen
                       | st2 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. destruct He.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxhd _]].
        + apply already_seen_tree_edge_upd. apply (IH x y). exact Hold.
        + subst x. apply already_seen_tree_edge_upd.
          destruct p0 as [|z rest]; cbn [hd];
            [ exact (already_seen_mono _ _ _ _ _ _ Hrec Hroot)
            | apply (dfs_path_seen _ _ _ _ _ _ Hrec); apply in_eq ].
      - rewrite graph.edges_put in He. rewrite already_seen_untree_edge_upd.
        destruct He as [Hold | [Hxhd _]].
        + apply (IH x y). exact Hold.
        + subst x.
          destruct p0 as [|z rest]; cbn [hd];
            [ exact (already_seen_mono _ _ _ _ _ _ Hrec Hroot)
            | apply (dfs_path_seen _ _ _ _ _ _ Hrec); apply in_eq ].
      - apply (IH x y). exact He.
    Qed.

    Lemma dfs_fold_state_trans root st0 st st' p p' g g' u :
      dfs_fold_state root st0 st (u :: p) g ->
      already_seen st0 root = true ->
      graph.edges g u = [] ->
      dfs_fold_state u st st' p' g' ->
      dfs_fold_state root st0 st' (p' ++ u :: p) (graph.union g g').
    Proof.
      intros H1 Hroot Hedges H2.
      induction H2 as [ | st2 p0 g0 v Hne Hrec IH Hseen
                        | st2 p0 g0 v Hrec IH Hne Hseen
                        | st2 u2 p0 g0 Hrec IH ].
      - cbn [app]. rewrite graph.union_empty_r. exact H1.
      - assert (Hhd : hd root (p0 ++ u :: p) = hd u p0) by (destruct p0; reflexivity).
        cbn [app]. rewrite graph.union_put_r. rewrite <- Hhd.
        apply dfs_tree_edge.
        + rewrite Hhd. intro Hedge. apply graph_edge_union in Hedge.
          destruct Hedge as [Hg | Hg0].
          * pose proof (dfs_target_seen _ _ _ _ _ _ _ H1 Hg) as Hs.
            pose proof (already_seen_mono _ _ _ _ _ _ Hrec Hs) as Hs2.
            congruence.
          * exact (Hne Hg0).
        + exact IH.
        + exact Hseen.
      - assert (Hhd : hd root (p0 ++ u :: p) = hd u p0) by (destruct p0; reflexivity).
        rewrite graph.union_put_r. rewrite <- Hhd.
        apply dfs_untree_edge.
        + exact IH.
        + rewrite Hhd. intro Hedge. apply graph_edge_union in Hedge.
          destruct Hedge as [Hg | Hg0].
          * destruct p0 as [|z rest].
            -- cbv [graph_edge] in Hg. cbn [hd] in Hg. rewrite Hedges in Hg. destruct Hg.
            -- cbn [hd] in Hg.
               pose proof (dfs_path_unseen _ _ _ _ _ _ Hrec (in_eq z rest)) as Hun.
               pose proof (dfs_source_seen _ _ _ _ _ _ _ Hroot H1 Hg) as Hsn.
               congruence.
          * exact (Hne Hg0).
        + exact Hseen.
      - cbn [app] in IH. eapply dfs_finish. exact IH.
    Qed.

    Lemma dfs_fold'_seen G n st' v :
      already_seen st' v = true -> dfs_fold' G n st' v = untree_edge_upd' st' v.
    Proof. destruct n; intro H; cbn [dfs_fold']; rewrite H; reflexivity. Qed.

    Lemma dfs_source_init root st0 st p g x y :
      dfs_fold_state root st0 st p g -> graph_edge g x y ->
      x = root \/ already_seen st0 x = false.
    Proof.
      intro H. revert x y.
      induction H as [ | st2 p0 g0 v Hne Hrec IH Hseen
                       | st2 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. destruct He.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxhd _]].
        + apply (IH x y). exact Hold.
        + subst x. destruct p0 as [|z rest]; cbn [hd].
          * left. reflexivity.
          * right. apply (dfs_path_unseen _ _ _ _ _ _ Hrec). apply in_eq.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxhd _]].
        + apply (IH x y). exact Hold.
        + subst x. destruct p0 as [|z rest]; cbn [hd].
          * left. reflexivity.
          * right. apply (dfs_path_unseen _ _ _ _ _ _ Hrec). apply in_eq.
      - apply (IH x y). exact He.
    Qed.

    Lemma dfs_fold_child G n' root st_init st_acc g_acc b :
      already_seen st_init root = true ->
      dfs_fold_state root st_init st_acc [] g_acc ->
      ~ graph_edge g_acc root b ->
      (already_seen st_acc b = false ->
         exists g_b, dfs_fold_state b (tree_edge_upd' st_acc b) (dfs_fold' G n' st_acc b) [] g_b) ->
      exists g',
        dfs_fold_state root st_init (dfs_fold' G n' st_acc b) [] g' /\
        (forall x, x <> b -> ~ graph_edge g_acc root x -> ~ graph_edge g' root x).
    Proof.
      intros Hroot Hstate Hnb Hsub.
      assert (Hnb' : ~ graph_edge g_acc (hd root []) b) by (cbn [hd]; exact Hnb).
      destruct (already_seen st_acc b) eqn:Eb.
      - rewrite (dfs_fold'_seen G n' st_acc b Eb).
        exists (graph.put g_acc (hd root []) b). split.
        + apply dfs_untree_edge; assumption.
        + intros x Hxb Hx Hedge. cbv [graph_edge] in Hedge. cbn [hd] in Hedge.
          rewrite graph.edges_put in Hedge. destruct Hedge as [Hin | [_ Hbx]].
          * exact (Hx Hin).
          * congruence.
      - destruct (Hsub eq_refl) as [g_b Hb].
        assert (Hrs : already_seen st_acc root = true) by (eapply already_seen_mono; eassumption).
        assert (Hrb : root <> b) by (intro Hc; rewrite Hc in Hrs; congruence).
        assert (Hbedges : graph.edges (graph.put g_acc (hd root []) b) b = []).
        { cbn [hd].
          destruct (graph.edges (graph.put g_acc root b) b) as [|w l'] eqn:Ew; [reflexivity|].
          exfalso.
          assert (Hin : In w (graph.edges (graph.put g_acc root b) b)) by (rewrite Ew; apply in_eq).
          rewrite graph.edges_put in Hin. destruct Hin as [Hin | [Hc _]]; [ | exact (Hrb Hc)].
          pose proof (dfs_source_seen _ _ _ _ _ _ _ Hroot Hstate Hin) as Hcon. congruence. }
        exists (graph.union (graph.put g_acc (hd root []) b) g_b). split.
        + eapply dfs_finish.
          eapply dfs_fold_state_trans with
            (st := tree_edge_upd' st_acc b) (p := @nil V) (p' := @nil V) (u := b).
          * apply dfs_tree_edge; assumption.
          * exact Hroot.
          * exact Hbedges.
          * exact Hb.
        + intros x Hxb Hx Hedge.
          cbv [graph_edge] in Hedge. rewrite graph.edges_union in Hedge. cbn [hd] in Hedge.
          destruct Hedge as [Hput | Hgb].
          * rewrite graph.edges_put in Hput.
            destruct Hput as [Hin | [_ Hbx]]; [exact (Hx Hin) | congruence].
          * pose proof (dfs_source_init _ _ _ _ _ _ _ Hb Hgb) as Hsi.
            destruct Hsi as [Hc | Hun].
            -- exact (Hrb Hc).
            -- pose proof (already_seen_tree_edge_upd st_acc b root Hrs) as Ht2. congruence.
    Qed.

    Lemma dfs_fold_children G n' root st_init L :
      already_seen st_init root = true ->
      (forall st_acc b, In b L -> already_seen st_acc b = false ->
         exists g_b, dfs_fold_state b (tree_edge_upd' st_acc b) (dfs_fold' G n' st_acc b) [] g_b) ->
      forall st_acc g_acc,
        dfs_fold_state root st_init st_acc [] g_acc ->
        NoDup L ->
        (forall x, In x L -> ~ graph_edge g_acc root x) ->
        exists g',
          dfs_fold_state root st_init (fold_left (dfs_fold' G n') L st_acc) [] g'.
    Proof.
      intros Hroot Hchildren st_acc g_acc Hstate Hnodup Htrack.
      assert (HP :
        (fun (remaining : list V) (st : state') =>
           exists g, dfs_fold_state root st_init st [] g /\
                     (forall x, In x remaining -> ~ graph_edge g root x) /\
                     NoDup remaining /\ incl remaining L) [] (fold_left (dfs_fold' G n') L st_acc)).
      { apply (fold_left_invariant
          (fun (remaining : list V) (st : state') =>
             exists g, dfs_fold_state root st_init st [] g /\
                       (forall x, In x remaining -> ~ graph_edge g root x) /\
                       NoDup remaining /\ incl remaining L)
          (dfs_fold' G n') L st_acc).
        - exists g_acc. split; [exact Hstate|]. split; [exact Htrack|].
          split; [exact Hnodup | apply incl_refl].
        - intros a' b l' HPbl.
          destruct HPbl as [g_a [Hst [Htr [Hnd Hinc]]]].
          destruct (dfs_fold_child G n' root st_init a' g_a b Hroot Hst
                      (Htr b (in_eq b l')) (Hchildren a' b (Hinc b (in_eq b l'))))
                   as [g' [Hst' Htr']].
          exists g'. split; [exact Hst'|]. split; [| split].
          + intros x Hx. apply Htr'.
            * intro Heq. subst x. inversion Hnd. contradiction.
            * apply Htr. right. exact Hx.
          + inversion Hnd. assumption.
          + intros x Hx. apply Hinc. right. exact Hx. }
      destruct HP as [g' [Hst' _]]. exists g'. exact Hst'.
    Qed.

    Definition restriction root vs g g' :=
      forall u v, graph_edge g' u v <-> graph_edge g u v /\ (exists p, path_to (graph_edge g) root p u /\ Forall (fun w => ~In w vs) (root :: p)).

    Definition edge_upd' st v :=
      if already_seen st v then untree_edge_upd' st v else
        tree_edge_upd' st v.

    From coqutil Require Import Tactics.fwd.

    Lemma set_contains_iff_In vs v :
      set_contains vs v = true <-> In v vs.
    Proof.
      unfold set_contains. symmetry.
      apply (existsb_eqb_in (aeqb_dec := @eqb_boolspec V eqbV eqb_ok)).
    Qed.

  End fold.


  Lemma dfs_fold_sound root vs n st0 g :
    (forall p v,
        path_to (graph_edge g) root p v ->
        Forall (fun w => ~In w vs) (root :: p) ->
        length p < n) ->
    exists g',
      dfs_fold_state root (edge_upd' (vs, st0) root) (dfs_fold' g n (vs, st0) root) [] g' /\
        restriction root vs g g'.
    Proof.
      revert root vs st0. induction n.
      - intros root vs st0 H. simpl. cbv [edge_upd']. simpl.
        destruct (set_contains vs root) eqn:E.
        + exists graph.empty. split.
          * apply dfs_init.
          * cbv [restriction graph_edge]. intros u v.
            rewrite graph.edges_empty. cbn [In].
            split; [intros []|].
            intros (_ & p & _ & Hf).
            apply (Forall_inv Hf). apply set_contains_iff_In. exact E.
        + exfalso.
          enough (length (@nil V) < 0) by lia.
          apply (H [] root).
          * unfold path_to. split; [exact I | reflexivity].
          * constructor.
            -- intro Hin. apply set_contains_iff_In in Hin. congruence.
            -- constructor.
      - intros. simpl. cbv [edge_upd' already_seen].
        destruct (set_contains vs root) eqn:E.
        + eexists. split.
          { apply dfs_init. }
          cbv [restriction]. cbv [graph_edge]. intros. rewrite graph.edges_empty.
          simpl. split; [contradiction|]. intros. fwd.
          apply set_contains_iff_In in E. auto.
        + Check dfs_fold_state_trans. Search fold_left. destruct (graph.edges g root).
          -- admit.
          -- destruct l. 2: admit. simpl. eexists. split.
             ++ econstructor.
    Admitted.

  End fold.

  Definition check_tree :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree).
End __.
