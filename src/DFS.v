From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb.
From coqutil Require Import Tactics.destr Tactics.Tactics.
From GraphSearch Require Import GraphInterface.
Import ListNotations.

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

    Definition set_contains vs v :=
      List.existsb (eqb v) vs.

    Section with_graph.
      Context (g : graph).

      Definition graph_edge u v := In v (graph.edges g u).

      Definition state' : Type := list V * state.
      Definition untree_edge_upd' '(vs, st) v := (vs, untree_edge_upd st vs v).
      Definition tree_edge_upd' '(vs, st) v := (v :: vs, tree_edge_upd st vs v).

      Definition already_seen (st' : state') v :=
        let '(vs, _) := st' in set_contains vs v.

      Fixpoint dfs_fold' n st' v : state' :=
        if already_seen st' v then untree_edge_upd' st' v else
          match n with
          | S n' => fold_left (dfs_fold' n') (graph.edges g v) (tree_edge_upd' st' v)
          | O => st'
          end.

      Definition dfs_fold st0 := dfs_fold' (S (length (graph.sources g))) ([], st0).
    End with_graph.

    Inductive dfs_fold_state (root : V) (st0 : state') : state' -> list V (*current path*)-> list V (*finished vertices*) -> graph (*explored edges*) -> Prop :=
    | dfs_init : dfs_fold_state _ _ (tree_edge_upd' st0 root) [root] [] graph.empty
    | dfs_tree_edge st p dun g v :
      ~graph_edge g (hd root p) v ->
      dfs_fold_state _ _ st p dun g ->
      already_seen st v = false ->
      dfs_fold_state _ _ (tree_edge_upd' st v) (v :: p) dun (graph.put g (hd root p) v)
    | dfs_untree_edge st p dun g v :
      dfs_fold_state _ _ st p dun g ->
      ~graph_edge g (hd root p) v ->
      already_seen st v = true ->
      dfs_fold_state _ _ (untree_edge_upd' st v) p dun (graph.put g (hd root p) v)
    | dfs_finish st u p dun g :
      dfs_fold_state _ _ st (u :: p) dun g ->
      dfs_fold_state _ _ st p (u :: dun) g.

    Context {ok : graph.ok graph}.
    Context {eqb_ok : Eqb_ok eqbV}.

    Lemma graph_edge_put_edge g u v a b :
      graph_edge (graph.put g u v) a b <-> (a = u /\ b = v) \/ graph_edge g a b.
    Proof.
      cbv [graph_edge]. destr (eqb a u).
      - subst. destr (eqb b v).
        + subst. split; intros _; [left; split; reflexivity | apply graph.edges_put_same].
        + rewrite graph.edges_put_diff by congruence.
          split; [ intro; right; assumption
                 | intros [[_ ?]|?]; [congruence | assumption] ].
      - rewrite graph.edges_put_diff by congruence.
        split; [ intro; right; assumption
               | intros [[? _]|?]; [congruence | assumption] ].
    Qed.

    Lemma already_seen_untree st v x :
      already_seen (untree_edge_upd' st v) x = already_seen st x.
    Proof. destruct st as [vs s]. reflexivity. Qed.

    Lemma already_seen_tree st v x :
      already_seen (tree_edge_upd' st v) x = orb (eqb x v) (already_seen st x).
    Proof. destruct st as [vs s]. reflexivity. Qed.

    Lemma eqb_reflV x : eqb x x = true.
    Proof. destr (eqb x x); congruence. Qed.

    Lemma dfs_fold'_S g n st v :
      dfs_fold' g (S n) st v =
        if already_seen st v then untree_edge_upd' st v
        else fold_left (dfs_fold' g n) (graph.edges g v) (tree_edge_upd' st v).
    Proof. reflexivity. Qed.

    Lemma dfs_fold'_O g st v :
      dfs_fold' g 0 st v =
        if already_seen st v then untree_edge_upd' st v else st.
    Proof. reflexivity. Qed.

    (* explored edges only leave already-visited vertices *)
    Definition seen_closed (st : state') g :=
      forall x b, graph_edge g x b -> already_seen st x = true.

    (* number of not-yet-visited source vertices; the fuel measure *)
    Definition unseen_count (g : graph) (st : state') :=
      length (filter (fun u => negb (already_seen st u)) (graph.sources g)).

    Lemma filter_length_le {A} (f1 f2 : A -> bool) (l : list A) :
      (forall x, In x l -> f2 x = true -> f1 x = true) ->
      length (filter f2 l) <= length (filter f1 l).
    Proof.
      induction l as [|a l IH]; intros Hle; cbn [filter]; [cbn [length]; lia|].
      specialize (IH ltac:(intros x Hx; apply Hle; right; exact Hx)).
      destruct (f2 a) eqn:E2.
      - rewrite (Hle a (or_introl eq_refl) E2). cbn [length]. lia.
      - destruct (f1 a); cbn [length]; lia.
    Qed.

    Lemma filter_count_drop (f2 f1 : V -> bool) (l : list V) (v : V) :
      (forall x, x <> v -> f2 x = f1 x) ->
      f1 v = true -> f2 v = false -> In v l ->
      length (filter f2 l) < length (filter f1 l).
    Proof.
      induction l as [|a l IH]; intros Hoff Hf1 Hf2 Hin; [contradiction|].
      cbn [filter]. destr (eqb a v).
      - subst. rewrite Hf1, Hf2. cbn [length].
        assert (Hle : length (filter f2 l) <= length (filter f1 l)).
        { apply filter_length_le. intros x _ Hx. destr (eqb x v).
          + subst. rewrite Hf2 in Hx. discriminate.
          + rewrite <- Hoff by assumption. exact Hx. }
        lia.
      - rewrite (Hoff a ltac:(assumption)).
        destruct Hin as [Hav|Hin]; [subst; congruence|].
        specialize (IH Hoff Hf1 Hf2 Hin).
        destruct (f1 a); cbn [length]; lia.
    Qed.

    Lemma unseen_count_mono g st1 st2 :
      (forall x, already_seen st1 x = true -> already_seen st2 x = true) ->
      unseen_count g st2 <= unseen_count g st1.
    Proof.
      intros Hmono. apply filter_length_le. intros x _ Hx.
      destruct (already_seen st1 x) eqn:E1; [|reflexivity].
      apply Hmono in E1. rewrite E1 in Hx. discriminate Hx.
    Qed.

    Lemma unseen_count_push g st v :
      already_seen st v = false ->
      In v (graph.sources g) ->
      unseen_count g (tree_edge_upd' st v) < unseen_count g st.
    Proof.
      intros Hunseen Hsrc. unfold unseen_count.
      apply (filter_count_drop _ _ _ v).
      - intros x Hxv. rewrite already_seen_tree. destr (eqb x v); [congruence|reflexivity].
      - rewrite Hunseen. reflexivity.
      - rewrite already_seen_tree, eqb_reflV. reflexivity.
      - exact Hsrc.
    Qed.

    Lemma unseen_count_init g s :
      unseen_count g ([], s) = length (graph.sources g).
    Proof.
      unfold unseen_count.
      assert (H : forall l : list V, filter (fun u => negb (already_seen ([], s) u)) l = l).
      { induction l as [|a l IH]; [reflexivity|].
        cbn [filter]. replace (negb (already_seen ([], s) a)) with true by reflexivity.
        rewrite IH. reflexivity. }
      rewrite H. reflexivity.
    Qed.

    Lemma last_indep {A} (xs : list A) (x d1 d2 : A) :
      List.last (x :: xs) d1 = List.last (x :: xs) d2.
    Proof.
      revert x. induction xs as [|a xs' IH]; intros x.
      - reflexivity.
      - cbn [List.last]. apply IH.
    Qed.

    Lemma last_cons {A} (l : list A) (a d : A) :
      List.last (a :: l) d = List.last l a.
    Proof.
      destruct l as [|x xs]; [reflexivity | cbn [List.last]; apply last_indep].
    Qed.

    (* a closed visited set contains the endpoint of any path from a visited start *)
    Lemma closed_reaches (g : graph) (W : V -> bool) :
      (forall u b, W u = true -> graph_edge g u b -> W b = true) ->
      forall p first, path (graph_edge g) first p -> W first = true ->
                      W (List.last p first) = true.
    Proof.
      intros Hclosed. induction p as [|next p' IH]; intros first Hpath Hfirst.
      - exact Hfirst.
      - destruct Hpath as [Hedge Hpath'].
        rewrite last_cons. apply IH; [exact Hpath'|].
        exact (Hclosed first next Hfirst Hedge).
    Qed.

    (* One dfs_fold' step on an already-seen vertex: a back/cross edge. *)
    Lemma dfs_fold'_sound_seen (g : graph) root st0 v st1 p1 dun1 g1 :
      dfs_fold_state root st0 st1 p1 dun1 g1 ->
      already_seen st1 (hd root p1) = true ->
      seen_closed st1 g1 ->
      ~ graph_edge g1 (hd root p1) v ->
      already_seen st1 v = true ->
      (forall x b, graph_edge g1 x b -> graph_edge g x b) ->
      graph_edge g (hd root p1) v ->
      (forall u b, already_seen st1 u = true -> ~ In u p1 -> graph_edge g u b ->
                   graph_edge g1 u b) ->
      (forall u b, graph_edge g1 u b -> already_seen st1 b = true) ->
      exists dun2 g2,
        dfs_fold_state root st0 (untree_edge_upd' st1 v) p1 dun2 g2 /\
        (forall x, already_seen st1 x = true ->
                   already_seen (untree_edge_upd' st1 v) x = true) /\
        seen_closed (untree_edge_upd' st1 v) g2 /\
        (forall x b, graph_edge g1 x b -> graph_edge g2 x b) /\
        (forall x b, already_seen st1 x = true -> x <> hd root p1 ->
                     graph_edge g2 x b -> graph_edge g1 x b) /\
        (forall b, graph_edge g2 (hd root p1) b ->
                   graph_edge g1 (hd root p1) b \/ b = v) /\
        (forall x b, graph_edge g2 x b -> graph_edge g x b) /\
        already_seen (untree_edge_upd' st1 v) v = true /\
        (forall u b, already_seen (untree_edge_upd' st1 v) u = true -> ~ In u p1 ->
                     graph_edge g u b -> graph_edge g2 u b) /\
        graph_edge g2 (hd root p1) v /\
        (forall u b, graph_edge g2 u b -> already_seen (untree_edge_upd' st1 v) b = true).
    Proof.
      intros H0 Htop HI Hfresh Hseen Hg1real Hvreal HAe1 Htgtpre.
      exists dun1, (graph.put g1 (hd root p1) v).
      ssplit.
      - apply dfs_untree_edge; assumption.
      - intros x Hx. rewrite already_seen_untree. exact Hx.
      - intros x b Hxb. rewrite already_seen_untree.
        apply graph_edge_put_edge in Hxb. destruct Hxb as [[Hx _]|Hxb].
        + subst x. exact Htop.
        + apply HI in Hxb. exact Hxb.
      - intros x b Hxb. apply graph_edge_put_edge. right. exact Hxb.
      - intros x b _ Hxt Hxb. apply graph_edge_put_edge in Hxb.
        destruct Hxb as [[Hxe _]|Hxb]; [congruence | exact Hxb].
      - intros b Hb. apply graph_edge_put_edge in Hb.
        destruct Hb as [[_ Hbv]|Hb]; [right; exact Hbv | left; exact Hb].
      - intros x b Hxb. apply graph_edge_put_edge in Hxb.
        destruct Hxb as [[Hx Hb]|Hxb];
          [subst x b; exact Hvreal | apply Hg1real; exact Hxb].
      - rewrite already_seen_untree. exact Hseen.
      - intros u b Hu Hue Hub. rewrite already_seen_untree in Hu.
        apply graph_edge_put_edge. right. apply HAe1; assumption.
      - apply graph_edge_put_edge. left. split; reflexivity.
      - intros u b Hub. rewrite already_seen_untree.
        apply graph_edge_put_edge in Hub.
        destruct Hub as [[_ Hbv]|Hub];
          [subst b; exact Hseen | apply Htgtpre in Hub; exact Hub].
    Qed.

    (* Soundness + completeness of the child-list fold from a reachable
       configuration.  The single-vertex step is folded in: an already-seen
       child is a back/cross edge (dfs_fold'_sound_seen); an unseen child
       pushes and recurses through the fuel induction hypothesis.  Conclusions
       8-10 (children get recorded/visited, recorded edges have visited
       targets) drive the coverage argument, gated by [unseen_count g st' < n]. *)
    Lemma dfs_fold_edges_sound (g : graph) (root : V) (st0 : state')
          (Hnd : forall x, NoDup (graph.edges g x)) n :
      forall ws st' p dun' g',
        dfs_fold_state root st0 st' p dun' g' ->
        already_seen st' (hd root p) = true ->
        seen_closed st' g' ->
        (forall w, In w ws -> ~ graph_edge g' (hd root p) w) ->
        NoDup ws ->
        (forall x b, graph_edge g' x b -> graph_edge g x b) ->
        (forall w, In w ws -> graph_edge g (hd root p) w) ->
        (ws <> [] -> unseen_count g st' < n) ->
        (forall u b, already_seen st' u = true -> ~ In u p -> graph_edge g u b ->
                     graph_edge g' u b) ->
        (forall u b, graph_edge g' u b -> already_seen st' b = true) ->
        exists dun2 g2,
          dfs_fold_state root st0 (fold_left (dfs_fold' g n) ws st') p dun2 g2 /\
          (forall x, already_seen st' x = true ->
                     already_seen (fold_left (dfs_fold' g n) ws st') x = true) /\
          seen_closed (fold_left (dfs_fold' g n) ws st') g2 /\
          (forall x b, graph_edge g' x b -> graph_edge g2 x b) /\
          (forall x b, already_seen st' x = true -> x <> hd root p ->
                       graph_edge g2 x b -> graph_edge g' x b) /\
          (forall b, graph_edge g2 (hd root p) b ->
                     graph_edge g' (hd root p) b \/ In b ws) /\
          (forall x b, graph_edge g2 x b -> graph_edge g x b) /\
          (forall w, In w ws -> graph_edge g2 (hd root p) w) /\
          (forall u b, already_seen (fold_left (dfs_fold' g n) ws st') u = true ->
                       ~ In u p -> graph_edge g u b -> graph_edge g2 u b) /\
          (forall u b, graph_edge g2 u b ->
                       already_seen (fold_left (dfs_fold' g n) ws st') b = true).
    Proof.
      induction n as [|n' IHn].
      - intros ws st' p dun' g' Hstate Htop' HI' Hfr Hnodup Hg'real Hwsreal Hfuel' HAe' Htgtpre'.
        destruct ws as [|w ws].
        + cbn [fold_left]. exists dun', g'.
          ssplit.
          * exact Hstate.
          * intros x Hx; exact Hx.
          * exact HI'.
          * intros x b Hxb; exact Hxb.
          * intros x b _ _ Hxb; exact Hxb.
          * intros b Hb; left; exact Hb.
          * exact Hg'real.
          * intros w [].
          * exact HAe'.
          * exact Htgtpre'.
        + exfalso. assert (Hf : unseen_count g st' < 0) by (apply Hfuel'; discriminate). lia.
      - intros ws. induction ws as [|w ws IHws];
          intros st' p dun' g' Hstate Htop' HI' Hfr Hnodup Hg'real Hwsreal Hfuel' HAe' Htgtpre'.
        + cbn [fold_left]. exists dun', g'.
          ssplit.
          * exact Hstate.
          * intros x Hx; exact Hx.
          * exact HI'.
          * intros x b Hxb; exact Hxb.
          * intros x b _ _ Hxb; exact Hxb.
          * intros b Hb; left; exact Hb.
          * exact Hg'real.
          * intros w [].
          * exact HAe'.
          * exact Htgtpre'.
        + apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hnin Hndws].
          cbn [fold_left].
          assert (Hhead : exists dunw gw,
              dfs_fold_state root st0 (dfs_fold' g (S n') st' w) p dunw gw /\
              (forall x, already_seen st' x = true ->
                         already_seen (dfs_fold' g (S n') st' w) x = true) /\
              seen_closed (dfs_fold' g (S n') st' w) gw /\
              (forall x b, graph_edge g' x b -> graph_edge gw x b) /\
              (forall x b, already_seen st' x = true -> x <> hd root p ->
                           graph_edge gw x b -> graph_edge g' x b) /\
              (forall b, graph_edge gw (hd root p) b ->
                         graph_edge g' (hd root p) b \/ b = w) /\
              (forall x b, graph_edge gw x b -> graph_edge g x b) /\
              already_seen (dfs_fold' g (S n') st' w) w = true /\
              (forall u b, already_seen (dfs_fold' g (S n') st' w) u = true -> ~ In u p ->
                           graph_edge g u b -> graph_edge gw u b) /\
              graph_edge gw (hd root p) w /\
              (forall u b, graph_edge gw u b ->
                           already_seen (dfs_fold' g (S n') st' w) b = true)).
          { destruct (already_seen st' w) eqn:Eseen.
            - assert (Hres : dfs_fold' g (S n') st' w = untree_edge_upd' st' w)
                by (rewrite dfs_fold'_S, Eseen; reflexivity).
              rewrite Hres.
              apply (dfs_fold'_sound_seen g root st0 w st' p dun' g'
                       Hstate Htop' HI' (Hfr w (or_introl eq_refl)) Eseen
                       Hg'real (Hwsreal w (or_introl eq_refl)) HAe' Htgtpre').
            - assert (Hres : dfs_fold' g (S n') st' w
                             = fold_left (dfs_fold' g n') (graph.edges g w) (tree_edge_upd' st' w))
                by (rewrite dfs_fold'_S, Eseen; reflexivity).
              rewrite Hres. clear Hres.
              assert (Htw : w <> hd root p)
                by (intro Heq; rewrite <- Heq in Htop'; congruence).
              assert (Hpush : dfs_fold_state root st0 (tree_edge_upd' st' w) (w :: p) dun'
                                (graph.put g' (hd root p) w))
                by (apply dfs_tree_edge;
                    [apply (Hfr w (or_introl eq_refl)) | exact Hstate | exact Eseen]).
              assert (Htop2 : already_seen (tree_edge_upd' st' w) (hd root (w :: p)) = true).
              { cbn [hd]. rewrite already_seen_tree, eqb_reflV. reflexivity. }
              assert (Hclosed2 : seen_closed (tree_edge_upd' st' w) (graph.put g' (hd root p) w)).
              { intros x b Hxb. rewrite already_seen_tree. apply Bool.orb_true_iff. right.
                apply graph_edge_put_edge in Hxb. destruct Hxb as [[Hx _]|Hxb].
                - subst x. exact Htop'.
                - apply HI' in Hxb. exact Hxb. }
              assert (Hfr2 : forall w0, In w0 (graph.edges g w) ->
                               ~ graph_edge (graph.put g' (hd root p) w) (hd root (w :: p)) w0).
              { intros w0 _ Hc. cbn [hd] in Hc. apply graph_edge_put_edge in Hc.
                destruct Hc as [[Hwt _]|Hc].
                - exact (Htw Hwt).
                - apply HI' in Hc. congruence. }
              assert (Hg'real2 : forall x b,
                          graph_edge (graph.put g' (hd root p) w) x b -> graph_edge g x b).
              { intros x b Hxb. apply graph_edge_put_edge in Hxb.
                destruct Hxb as [[Hx Hb]|Hxb];
                  [subst x b; apply (Hwsreal w (or_introl eq_refl)) | apply Hg'real; exact Hxb]. }
              assert (Hwsreal2 : forall w0, In w0 (graph.edges g w) ->
                                   graph_edge g (hd root (w :: p)) w0).
              { intros w0 Hw0. cbn [hd]. exact Hw0. }
              assert (Hfuel2 : graph.edges g w <> [] ->
                                 unseen_count g (tree_edge_upd' st' w) < n').
              { intros Hne. assert (Hsrc : In w (graph.sources g))
                  by (apply graph.sources_spec; exact Hne).
                assert (Hpushlt : unseen_count g (tree_edge_upd' st' w) < unseen_count g st')
                  by (apply unseen_count_push; [exact Eseen | exact Hsrc]).
                assert (Hle : unseen_count g st' < S n') by (apply Hfuel'; discriminate).
                lia. }
              assert (HAe'2 : forall u b, already_seen (tree_edge_upd' st' w) u = true ->
                                ~ In u (w :: p) -> graph_edge g u b ->
                                graph_edge (graph.put g' (hd root p) w) u b).
              { intros u b Hu Hue Hub. rewrite already_seen_tree in Hu.
                apply Bool.orb_true_iff in Hu. destruct Hu as [Huw|Hu].
                - exfalso. assert (u = w) by (destr (eqb u w); congruence).
                  subst u. apply Hue. left. reflexivity.
                - apply graph_edge_put_edge. right. apply HAe'; [exact Hu | | exact Hub].
                  intro Hin. apply Hue. right. exact Hin. }
              assert (Htgtpre2 : forall u b,
                          graph_edge (graph.put g' (hd root p) w) u b ->
                          already_seen (tree_edge_upd' st' w) b = true).
              { intros u b Hub. rewrite already_seen_tree. apply Bool.orb_true_iff.
                apply graph_edge_put_edge in Hub. destruct Hub as [[_ Hbw]|Hub].
                - left. subst b. apply eqb_reflV.
                - right. apply Htgtpre' in Hub. exact Hub. }
              destruct (IHn (graph.edges g w) (tree_edge_upd' st' w) (w :: p) dun'
                            (graph.put g' (hd root p) w) Hpush Htop2 Hclosed2 Hfr2 (Hnd w)
                            Hg'real2 Hwsreal2 Hfuel2 HAe'2 Htgtpre2)
                as (dun2 & g2 & Hstate2 & Hmono2 & Hclosed2' & Hgmono2 & H62 & H72 & Hreal2
                      & Hwsedge2 & HAe22 & Htgt2).
              exists (w :: dun2), g2.
              ssplit.
              + apply dfs_finish. exact Hstate2.
              + intros x Hx. apply Hmono2.
                rewrite already_seen_tree, Hx, Bool.orb_true_r. reflexivity.
              + exact Hclosed2'.
              + intros x b Hxb. apply Hgmono2. apply graph_edge_put_edge. right. exact Hxb.
              + intros x b Hx Hxt Hxb.
                assert (Hxw : x <> w) by (intro Heq; subst x; congruence).
                assert (Hg'0 : graph_edge (graph.put g' (hd root p) w) x b).
                { apply H62;
                    [ rewrite already_seen_tree, Hx, Bool.orb_true_r; reflexivity
                    | cbn [hd]; exact Hxw
                    | exact Hxb ]. }
                apply graph_edge_put_edge in Hg'0.
                destruct Hg'0 as [[He _]|Hg'0]; [congruence | exact Hg'0].
              + intros b Hb.
                assert (Hg'0 : graph_edge (graph.put g' (hd root p) w) (hd root p) b).
                { apply H62;
                    [ rewrite already_seen_tree, Htop'; apply Bool.orb_true_r
                    | cbn [hd]; intro Heq; exact (Htw (eq_sym Heq))
                    | exact Hb ]. }
                apply graph_edge_put_edge in Hg'0.
                destruct Hg'0 as [[_ Hbw]|Hg'0]; [right; exact Hbw | left; exact Hg'0].
              + exact Hreal2.
              + apply Hmono2. rewrite already_seen_tree, eqb_reflV. reflexivity.
              + intros u b Hu Hue Hub. destr (eqb u w).
                -- subst. apply Hwsedge2. exact Hub.
                -- apply HAe22; [exact Hu | | exact Hub].
                   intro Hin. cbn [In] in Hin. destruct Hin as [Hwu|Hin].
                   ++ congruence.
                   ++ apply Hue; exact Hin.
              + apply Hgmono2. apply graph_edge_put_edge. left. split; reflexivity.
              + intros u b Hub. apply Htgt2 in Hub. exact Hub. }
          destruct Hhead as (dunw & gw & Hstatew & Hmonow & Hclosedw & Hgmonow & H6w & H7w
                & Hrealw & Hvvisw & HAe2w & Hparentw & Htgtw).
          assert (Htopw : already_seen (dfs_fold' g (S n') st' w) (hd root p) = true)
            by (apply Hmonow; exact Htop').
          assert (Hfrw : forall w0, In w0 ws -> ~ graph_edge gw (hd root p) w0).
          { intros w0 Hin0 Hc. apply H7w in Hc. destruct Hc as [Hc|Hc].
            - exact (Hfr w0 (or_intror Hin0) Hc).
            - subst w0. contradiction. }
          assert (Hfueltail : ws <> [] -> unseen_count g (dfs_fold' g (S n') st' w) < S n').
          { intros _. assert (Hle : unseen_count g st' < S n') by (apply Hfuel'; discriminate).
            pose proof (unseen_count_mono g st' (dfs_fold' g (S n') st' w) Hmonow). lia. }
          destruct (IHws (dfs_fold' g (S n') st' w) p dunw gw
                         Hstatew Htopw Hclosedw Hfrw Hndws Hrealw
                         (fun w0 Hin0 => Hwsreal w0 (or_intror Hin0)) Hfueltail HAe2w Htgtw)
            as (dun2 & g2 & Hstate2 & Hmono2 & Hclosed2 & Hgmono2 & H62 & H72 & Hreal2
                  & Hwsedge2 & HAe22 & Htgt2).
          exists dun2, g2. ssplit.
          * exact Hstate2.
          * intros x Hx. apply Hmono2. apply Hmonow. exact Hx.
          * exact Hclosed2.
          * intros x b Hxb. apply Hgmono2. apply Hgmonow. exact Hxb.
          * intros x b Hx Hxt Hxb.
            apply H6w; [exact Hx | exact Hxt |].
            apply H62; [ apply Hmonow; exact Hx | exact Hxt | exact Hxb ].
          * intros b Hb. apply H72 in Hb. destruct Hb as [Hb|Hb].
            -- apply H7w in Hb. destruct Hb as [Hb|Hb].
               ++ left. exact Hb.
               ++ right. left. symmetry. exact Hb.
            -- right. right. exact Hb.
          * exact Hreal2.
          * intros w0 Hin0. destruct Hin0 as [Hw0|Hin0].
            -- rewrite <- Hw0. apply Hgmono2. exact Hparentw.
            -- apply Hwsedge2. exact Hin0.
          * exact HAe22.
          * exact Htgt2.
    Qed.

    (* Top-level correctness: with all edge sources reachable from [root] and
       duplicate-free adjacency lists, [dfs_fold g st0 root] is a reachable
       configuration of [dfs_fold_state] whose explored graph is exactly [g]. *)
    Theorem dfs_fold_sound (g : graph) (root : V) (st0 : state)
            (Hnd : forall x, NoDup (graph.edges g x))
            (Hreach : reachable (graph_edge g) root) :
      exists p dun,
        dfs_fold_state root ([], st0) (dfs_fold g st0 root) p dun g.
    Proof.
      assert (Hseen : already_seen ([], st0) root = false) by reflexivity.
      assert (Hres : dfs_fold g st0 root
                     = fold_left (dfs_fold' g (length (graph.sources g)))
                                 (graph.edges g root) (tree_edge_upd' ([], st0) root)).
      { cbv [dfs_fold]. rewrite dfs_fold'_S, Hseen. reflexivity. }
      rewrite Hres.
      assert (Htop2 : already_seen (tree_edge_upd' ([], st0) root)
                        (hd root (root :: [])) = true).
      { cbn [hd]. rewrite already_seen_tree, eqb_reflV. reflexivity. }
      assert (Hclosed2 : seen_closed (tree_edge_upd' ([], st0) root) graph.empty).
      { intros x b Hxb. exfalso. cbv [graph_edge] in Hxb.
        rewrite graph.edges_empty in Hxb. exact Hxb. }
      assert (Hfr2 : forall w, In w (graph.edges g root) ->
                       ~ graph_edge graph.empty (hd root (root :: [])) w).
      { intros w _ Hc. cbv [graph_edge] in Hc.
        rewrite graph.edges_empty in Hc. exact Hc. }
      assert (Hereal : forall x b, graph_edge graph.empty x b -> graph_edge g x b).
      { intros x b Hxb. cbv [graph_edge] in Hxb.
        rewrite graph.edges_empty in Hxb. destruct Hxb. }
      assert (Hwsreal : forall w, In w (graph.edges g root) ->
                          graph_edge g (hd root (root :: [])) w).
      { intros w Hw. cbn [hd]. exact Hw. }
      assert (Hfuel : graph.edges g root <> [] ->
                        unseen_count g (tree_edge_upd' ([], st0) root)
                          < length (graph.sources g)).
      { intros Hne. assert (Hsrc : In root (graph.sources g))
          by (apply graph.sources_spec; exact Hne).
        pose proof (unseen_count_push g ([], st0) root Hseen Hsrc) as Hlt.
        rewrite unseen_count_init in Hlt. exact Hlt. }
      assert (HAe0 : forall u b, already_seen (tree_edge_upd' ([], st0) root) u = true ->
                       ~ In u (root :: []) -> graph_edge g u b -> graph_edge graph.empty u b).
      { intros u b Hu Hue _. exfalso. rewrite already_seen_tree in Hu.
        change (already_seen ([], st0) u) with false in Hu.
        rewrite Bool.orb_false_r in Hu.
        assert (u = root) by (destr (eqb u root); congruence). subst u.
        apply Hue. left. reflexivity. }
      assert (Htgt0 : forall u b, graph_edge graph.empty u b ->
                        already_seen (tree_edge_upd' ([], st0) root) b = true).
      { intros u b Hub. exfalso. cbv [graph_edge] in Hub.
        rewrite graph.edges_empty in Hub. exact Hub. }
      destruct (dfs_fold_edges_sound g root ([], st0) Hnd (length (graph.sources g))
                  (graph.edges g root) (tree_edge_upd' ([], st0) root) (root :: []) []
                  graph.empty
                  (dfs_init root ([], st0)) Htop2 Hclosed2 Hfr2 (Hnd root)
                  Hereal Hwsreal Hfuel HAe0 Htgt0)
        as (dun2 & g2 & Hstate2 & Hmono2 & _ & _ & _ & _ & Hreal2 & Hwsedge2 & HAe22 & Htgt2).
      set (R := fold_left (dfs_fold' g (length (graph.sources g)))
                          (graph.edges g root) (tree_edge_upd' ([], st0) root)) in *.
      assert (Hrootvis : already_seen R root = true).
      { apply Hmono2. rewrite already_seen_tree, eqb_reflV. reflexivity. }
      assert (Hclose : forall u b, already_seen R u = true -> graph_edge g u b ->
                         already_seen R b = true).
      { intros u b Hu Hub. apply (Htgt2 u b). destr (eqb u root).
        - subst. apply Hwsedge2. exact Hub.
        - apply HAe22; [exact Hu | cbn [In]; intro Hin; destruct Hin as [Hr|[]]; congruence
                       | exact Hub]. }
      assert (Hg2g : g2 = g).
      { apply graph.graph_ext. intros x. cbv [same_set incl]. split.
        - intros w Hin. apply (Hreal2 x w). exact Hin.
        - intros w Hin.
          assert (Hxvis : already_seen R x = true).
          { destruct (Hreach x w Hin) as [q [Hpath Hlast]]. rewrite Hlast.
            exact (closed_reaches g (fun u => already_seen R u) Hclose q root Hpath Hrootvis). }
          destr (eqb x root).
          + subst. apply Hwsedge2. exact Hin.
          + apply HAe22; [exact Hxvis | cbn [In]; intro Hin2; destruct Hin2 as [Hr|[]]; congruence
                         | exact Hin]. }
      rewrite Hg2g in Hstate2.
      exists (root :: []), dun2. exact Hstate2.
    Qed.

  End fold.

  Definition check_tree :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree).
End __.
