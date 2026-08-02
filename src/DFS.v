From Stdlib Require Import List Lia.
From coqutil Require Import Map.Interface Datatypes.List Datatypes.ListSet Eqb.
From coqutil Require Import Tactics.destr Tactics.Tactics.
Import ListNotations.

Section map.
  Context {key value : Type} {mp : map.map key value}.
  Implicit Type m : mp.

  Definition mupd_total d f m k :=
    match map.get m k with
    | Some v => map.put m k (f v)
    | None => map.put m k (f d)
    end.

  Definition get_or d m k :=
    match map.get m k with
    | Some v => v
    | None => d
    end.
End map.

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
  Context {graph : map.map V (list V)}.

  Section fold.
    Context {state : Type}.
    Context (untree_edge_upd : state -> list V -> V -> state).
    Context (tree_edge_upd : state -> list V -> V -> state).

    Definition set_contains vs v :=
      List.existsb (eqb v) vs.

    Section with_graph.
      Context (g : graph).

      Definition nodes :=
        map.fold (fun ns u v => list_union eqb (u :: v) ns) [] g.
      Definition edges u := get_or [] g u.
      Definition has_edge u v := set_contains (edges u) v.
      Definition put_edge u v := mupd_total [] (list_union eqb [v]) g u.

      Definition graph_node u := In u nodes.
      Definition graph_edge u v := In v (edges u).

      Definition state' : Type := list V * state.
      Definition untree_edge_upd' '(vs, st) v := (vs, untree_edge_upd st vs v).
      Definition tree_edge_upd' '(vs, st) v := (v :: vs, tree_edge_upd st vs v).

      Definition already_seen (st' : state') v :=
        let '(vs, _) := st' in set_contains vs v.

      Fixpoint dfs_fold' n st' v : state' :=
        if already_seen st' v then untree_edge_upd' st' v else
          match n with
          | S n' => fold_left (dfs_fold' n') (edges v) (tree_edge_upd' st' v)
          | O => st'
          end.

      Definition dfs_fold st0 := dfs_fold' (S (length (map.keys g))) ([], st0).
    End with_graph.

    Inductive dfs_fold_state (root : V) (st0 : state') : state' -> list V (*current path*)-> list V (*finished vertices*) -> graph (*explored edges*) -> Prop :=
    | dfs_init : dfs_fold_state _ _ st0 [] [] map.empty
    | dfs_tree_edge st p dun g v :
      ~graph_edge g (hd root p) v ->
      dfs_fold_state _ _ st p dun g ->
      already_seen st v = false ->
      dfs_fold_state _ _ (tree_edge_upd' st v) (v :: p) dun (put_edge g (hd root p) v)
    | dfs_untree_edge st p dun g v :
      dfs_fold_state _ _ st p dun g ->
      ~graph_edge g (hd root p) v ->
      already_seen st v = true ->
      dfs_fold_state _ _ (untree_edge_upd' st v) p dun (put_edge g (hd root p) v)
    | dfs_finish st u p dun g :
      dfs_fold_state _ _ st (u :: p) dun g ->
      dfs_fold_state _ _ st p (u :: dun) g.

    Context {ok : map.ok graph}.
    Context {eqb_ok : Eqb_ok eqbV}.

    Lemma set_contains_true_iff vs v :
      set_contains vs v = true <-> In v vs.
    Proof.
      cbv [set_contains]. rewrite existsb_exists. split.
      - intros (x & Hin & Hx). destr (eqb v x); congruence.
      - intros Hin. exists v. split; [assumption|]. destr (eqb v v); congruence.
    Qed.

    Lemma put_edge_eq g u v :
      put_edge g u v = map.put g u (list_union eqb [v] (edges g u)).
    Proof.
      cbv [put_edge mupd_total edges get_or]. destruct (map.get g u); reflexivity.
    Qed.

    Lemma edges_put_edge g u v a :
      edges (put_edge g u v) a =
        if eqb a u then list_union eqb [v] (edges g a) else edges g a.
    Proof.
      rewrite put_edge_eq. cbv [edges get_or]. destr (eqb a u).
      - subst. rewrite map.get_put_same. reflexivity.
      - rewrite map.get_put_diff by congruence. reflexivity.
    Qed.

    Lemma graph_edge_put_edge g u v a b :
      graph_edge (put_edge g u v) a b <-> (a = u /\ b = v) \/ graph_edge g a b.
    Proof.
      cbv [graph_edge]. rewrite edges_put_edge. destr (eqb a u).
      - subst. rewrite In_list_union_spec. cbn [In]. intuition congruence.
      - intuition congruence.
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
        else fold_left (dfs_fold' g n) (edges g v) (tree_edge_upd' st v).
    Proof. reflexivity. Qed.

    Lemma dfs_fold'_O g st v :
      dfs_fold' g 0 st v =
        if already_seen st v then untree_edge_upd' st v else st.
    Proof. reflexivity. Qed.

    (* explored edges only leave already-visited vertices *)
    Definition seen_closed (st : state') g :=
      forall x b, graph_edge g x b -> already_seen st x = true.

    (* One dfs_fold' step on an already-seen vertex: a back/cross edge. *)
    Lemma dfs_fold'_sound_seen root st0 v st1 p1 dun1 g1 :
      dfs_fold_state root st0 st1 p1 dun1 g1 ->
      already_seen st1 (hd root p1) = true ->
      seen_closed st1 g1 ->
      ~ graph_edge g1 (hd root p1) v ->
      already_seen st1 v = true ->
      exists dun2 g2,
        dfs_fold_state root st0 (untree_edge_upd' st1 v) p1 dun2 g2 /\
        (forall x, already_seen st1 x = true ->
                   already_seen (untree_edge_upd' st1 v) x = true) /\
        seen_closed (untree_edge_upd' st1 v) g2 /\
        (forall x b, graph_edge g1 x b -> graph_edge g2 x b) /\
        (forall x b, already_seen st1 x = true -> x <> hd root p1 ->
                     graph_edge g2 x b -> graph_edge g1 x b) /\
        (forall b, graph_edge g2 (hd root p1) b ->
                   graph_edge g1 (hd root p1) b \/ b = v).
    Proof.
      intros H0 Htop HI Hfresh Hseen.
      exists dun1, (put_edge g1 (hd root p1) v).
      split; [|split; [|split; [|split; [|split]]]].
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
    Qed.

    (* Soundness of the functional dfs_fold': whatever state it computes when
       exploring [v] from a reachable configuration is itself reachable.  The
       auxiliary conclusions are the invariants threaded through the induction. *)
    Lemma dfs_fold'_sound (g : graph) (root : V) (st0 : state')
          (Hnd : forall x, NoDup (edges g x)) n :
      forall v st1 p1 dun1 g1,
        dfs_fold_state root st0 st1 p1 dun1 g1 ->
        already_seen st1 (hd root p1) = true ->
        seen_closed st1 g1 ->
        ~ graph_edge g1 (hd root p1) v ->
        exists dun2 g2,
          dfs_fold_state root st0 (dfs_fold' g n st1 v) p1 dun2 g2 /\
          (forall x, already_seen st1 x = true ->
                     already_seen (dfs_fold' g n st1 v) x = true) /\
          seen_closed (dfs_fold' g n st1 v) g2 /\
          (forall x b, graph_edge g1 x b -> graph_edge g2 x b) /\
          (forall x b, already_seen st1 x = true -> x <> hd root p1 ->
                       graph_edge g2 x b -> graph_edge g1 x b) /\
          (forall b, graph_edge g2 (hd root p1) b ->
                     graph_edge g1 (hd root p1) b \/ b = v).
    Proof.
      induction n as [|n' IHn];
        intros v st1 p1 dun1 g1 H0 Htop HI Hfresh.
      - (* out of fuel *)
        destruct (already_seen st1 v) eqn:E.
        + assert (Hres : dfs_fold' g 0 st1 v = untree_edge_upd' st1 v)
            by (rewrite dfs_fold'_O, E; reflexivity).
          rewrite Hres. eapply dfs_fold'_sound_seen; eassumption.
        + assert (Hres : dfs_fold' g 0 st1 v = st1)
            by (rewrite dfs_fold'_O, E; reflexivity).
          rewrite Hres. exists dun1, g1.
          split; [|split; [|split; [|split; [|split]]]].
          * exact H0.
          * intros x Hx; exact Hx.
          * exact HI.
          * intros x b Hxb; exact Hxb.
          * intros x b _ _ Hxb; exact Hxb.
          * intros b Hb; left; exact Hb.
      - (* S n' : first prove soundness of folding over a child list *)
        assert (Hfold : forall ws st' p dun' g',
          dfs_fold_state root st0 st' p dun' g' ->
          already_seen st' (hd root p) = true ->
          seen_closed st' g' ->
          (forall w, In w ws -> ~ graph_edge g' (hd root p) w) ->
          NoDup ws ->
          exists dun2 g2,
            dfs_fold_state root st0 (fold_left (dfs_fold' g n') ws st') p dun2 g2 /\
            (forall x, already_seen st' x = true ->
                       already_seen (fold_left (dfs_fold' g n') ws st') x = true) /\
            seen_closed (fold_left (dfs_fold' g n') ws st') g2 /\
            (forall x b, graph_edge g' x b -> graph_edge g2 x b) /\
            (forall x b, already_seen st' x = true -> x <> hd root p ->
                         graph_edge g2 x b -> graph_edge g' x b) /\
            (forall b, graph_edge g2 (hd root p) b ->
                       graph_edge g' (hd root p) b \/ In b ws)).
        { intros ws. induction ws as [|w ws IHws];
            intros st' p dun' g' Hstate Htop' HI' Hfr Hnodup.
          - cbn [fold_left]. exists dun', g'.
            split; [|split; [|split; [|split; [|split]]]].
            + exact Hstate.
            + intros x Hx; exact Hx.
            + exact HI'.
            + intros x b Hxb; exact Hxb.
            + intros x b _ _ Hxb; exact Hxb.
            + intros b Hb; left; exact Hb.
          - apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hnin Hndws].
            cbn [fold_left].
            destruct (IHn w st' p dun' g' Hstate Htop' HI' (Hfr w (or_introl eq_refl)))
              as (dunw & gw & Hstatew & Hmonow & Hclosedw & Hgmonow & H6w & H7w).
            assert (Htopw : already_seen (dfs_fold' g n' st' w) (hd root p) = true)
              by (apply Hmonow; exact Htop').
            assert (Hfrw : forall w0, In w0 ws -> ~ graph_edge gw (hd root p) w0).
            { intros w0 Hin0 Hc. apply H7w in Hc. destruct Hc as [Hc|Hc].
              - exact (Hfr w0 (or_intror Hin0) Hc).
              - subst w0. contradiction. }
            destruct (IHws (dfs_fold' g n' st' w) p dunw gw
                           Hstatew Htopw Hclosedw Hfrw Hndws)
              as (dun2 & g2 & Hstate2 & Hmono2 & Hclosed2 & Hgmono2 & H62 & H72).
            exists dun2, g2.
            split; [|split; [|split; [|split; [|split]]]].
            + exact Hstate2.
            + intros x Hx. apply Hmono2. apply Hmonow. exact Hx.
            + exact Hclosed2.
            + intros x b Hxb. apply Hgmono2. apply Hgmonow. exact Hxb.
            + intros x b Hx Hxt Hxb.
              apply H6w; [exact Hx | exact Hxt |].
              apply H62; [ apply Hmonow; exact Hx | exact Hxt | exact Hxb ].
            + intros b Hb. apply H72 in Hb. destruct Hb as [Hb|Hb].
              * apply H7w in Hb. destruct Hb as [Hb|Hb].
                -- left. exact Hb.
                -- right. left. symmetry. exact Hb.
              * right. right. exact Hb. }
        (* now dispatch on whether [v] is already visited *)
        destruct (already_seen st1 v) eqn:E.
        + assert (Hres : dfs_fold' g (S n') st1 v = untree_edge_upd' st1 v)
            by (rewrite dfs_fold'_S, E; reflexivity).
          rewrite Hres. eapply dfs_fold'_sound_seen; eassumption.
        + assert (Hres : dfs_fold' g (S n') st1 v
                         = fold_left (dfs_fold' g n') (edges g v) (tree_edge_upd' st1 v))
            by (rewrite dfs_fold'_S, E; reflexivity).
          rewrite Hres. clear Hres.
          assert (Htv : v <> hd root p1)
            by (intro Heq; rewrite <- Heq in Htop; congruence).
          assert (Hpush : dfs_fold_state root st0 (tree_edge_upd' st1 v) (v :: p1) dun1
                            (put_edge g1 (hd root p1) v))
            by (apply dfs_tree_edge; assumption).
          assert (Htop2 : already_seen (tree_edge_upd' st1 v) (hd root (v :: p1)) = true).
          { cbn [hd]. rewrite already_seen_tree, eqb_reflV. reflexivity. }
          assert (Hclosed2 : seen_closed (tree_edge_upd' st1 v) (put_edge g1 (hd root p1) v)).
          { intros x b Hxb. rewrite already_seen_tree. apply Bool.orb_true_iff. right.
            apply graph_edge_put_edge in Hxb. destruct Hxb as [[Hx _]|Hxb].
            - subst x. exact Htop.
            - apply HI in Hxb. exact Hxb. }
          assert (Hfr2 : forall w, In w (edges g v) ->
                           ~ graph_edge (put_edge g1 (hd root p1) v) (hd root (v :: p1)) w).
          { intros w _ Hc. cbn [hd] in Hc. apply graph_edge_put_edge in Hc.
            destruct Hc as [[Hvt _]|Hc].
            - exact (Htv Hvt).
            - apply HI in Hc. congruence. }
          destruct (Hfold (edges g v) (tree_edge_upd' st1 v) (v :: p1) dun1
                          (put_edge g1 (hd root p1) v) Hpush Htop2 Hclosed2 Hfr2 (Hnd v))
            as (dun2 & g2 & Hstate2 & Hmono2 & Hclosed2' & Hgmono2 & H62 & H72).
          exists (v :: dun2), g2.
          split; [|split; [|split; [|split; [|split]]]].
          * apply dfs_finish. exact Hstate2.
          * intros x Hx. apply Hmono2.
            rewrite already_seen_tree, Hx, Bool.orb_true_r. reflexivity.
          * exact Hclosed2'.
          * intros x b Hxb. apply Hgmono2. apply graph_edge_put_edge. right. exact Hxb.
          * intros x b Hx Hxt Hxb.
            assert (Hxv : x <> v) by (intro Heq; subst x; congruence).
            assert (Hg' : graph_edge (put_edge g1 (hd root p1) v) x b).
            { apply H62;
                [ rewrite already_seen_tree, Hx, Bool.orb_true_r; reflexivity
                | cbn [hd]; exact Hxv
                | exact Hxb ]. }
            apply graph_edge_put_edge in Hg'.
            destruct Hg' as [[He _]|Hg']; [congruence | exact Hg'].
          * intros b Hb.
            assert (Hg' : graph_edge (put_edge g1 (hd root p1) v) (hd root p1) b).
            { apply H62;
                [ rewrite already_seen_tree, Htop; apply Bool.orb_true_r
                | cbn [hd]; intro Heq; exact (Htv (eq_sym Heq))
                | exact Hb ]. }
            apply graph_edge_put_edge in Hg'.
            destruct Hg' as [[_ Hbv]|Hg']; [right; exact Hbv | left; exact Hg'].
    Qed.

    (* Soundness lifted to a left fold over a child list. *)
    Lemma dfs_fold_edges_sound (g : graph) (root : V) (st0 : state')
          (Hnd : forall x, NoDup (edges g x)) n :
      forall ws st' p dun' g',
        dfs_fold_state root st0 st' p dun' g' ->
        already_seen st' (hd root p) = true ->
        seen_closed st' g' ->
        (forall w, In w ws -> ~ graph_edge g' (hd root p) w) ->
        NoDup ws ->
        exists dun2 g2,
          dfs_fold_state root st0 (fold_left (dfs_fold' g n) ws st') p dun2 g2 /\
          (forall x, already_seen st' x = true ->
                     already_seen (fold_left (dfs_fold' g n) ws st') x = true) /\
          seen_closed (fold_left (dfs_fold' g n) ws st') g2 /\
          (forall x b, graph_edge g' x b -> graph_edge g2 x b) /\
          (forall x b, already_seen st' x = true -> x <> hd root p ->
                       graph_edge g2 x b -> graph_edge g' x b) /\
          (forall b, graph_edge g2 (hd root p) b ->
                     graph_edge g' (hd root p) b \/ In b ws).
    Proof.
      intros ws. induction ws as [|w ws IHws];
        intros st' p dun' g' Hstate Htop' HI' Hfr Hnodup.
      - cbn [fold_left]. exists dun', g'.
        split; [|split; [|split; [|split; [|split]]]].
        + exact Hstate.
        + intros x Hx; exact Hx.
        + exact HI'.
        + intros x b Hxb; exact Hxb.
        + intros x b _ _ Hxb; exact Hxb.
        + intros b Hb; left; exact Hb.
      - apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hnin Hndws].
        cbn [fold_left].
        destruct (dfs_fold'_sound g root st0 Hnd n w st' p dun' g'
                    Hstate Htop' HI' (Hfr w (or_introl eq_refl)))
          as (dunw & gw & Hstatew & Hmonow & Hclosedw & Hgmonow & H6w & H7w).
        assert (Htopw : already_seen (dfs_fold' g n st' w) (hd root p) = true)
          by (apply Hmonow; exact Htop').
        assert (Hfrw : forall w0, In w0 ws -> ~ graph_edge gw (hd root p) w0).
        { intros w0 Hin0 Hc. apply H7w in Hc. destruct Hc as [Hc|Hc].
          - exact (Hfr w0 (or_intror Hin0) Hc).
          - subst w0. contradiction. }
        destruct (IHws (dfs_fold' g n st' w) p dunw gw
                       Hstatew Htopw Hclosedw Hfrw Hndws)
          as (dun2 & g2 & Hstate2 & Hmono2 & Hclosed2 & Hgmono2 & H62 & H72).
        exists dun2, g2.
        split; [|split; [|split; [|split; [|split]]]].
        + exact Hstate2.
        + intros x Hx. apply Hmono2. apply Hmonow. exact Hx.
        + exact Hclosed2.
        + intros x b Hxb. apply Hgmono2. apply Hgmonow. exact Hxb.
        + intros x b Hx Hxt Hxb.
          apply H6w; [exact Hx | exact Hxt |].
          apply H62; [ apply Hmonow; exact Hx | exact Hxt | exact Hxb ].
        + intros b Hb. apply H72 in Hb. destruct Hb as [Hb|Hb].
          * apply H7w in Hb. destruct Hb as [Hb|Hb].
            -- left. exact Hb.
            -- right. left. symmetry. exact Hb.
          * right. right. exact Hb.
    Qed.

    (* Top-level forward soundness: the state computed by [dfs_fold g st0 root]
       is a reachable configuration of [dfs_fold_state].  Adjacency lists are
       assumed duplicate-free, and [root] has no self-loop (the initial push of
       [root] would otherwise collide with a self-edge). *)
    Theorem dfs_fold_sound (g : graph) (root : V) (st0 : state)
            (Hnd : forall x, NoDup (edges g x))
            (Hroot : ~ In root (edges g root)) :
      exists p dun g2,
        dfs_fold_state root ([], st0) (dfs_fold g st0 root) p dun g2.
    Proof.
      assert (Hseen : already_seen ([], st0) root = false) by reflexivity.
      assert (Hres : dfs_fold g st0 root
                     = fold_left (dfs_fold' g (length (map.keys g)))
                                 (edges g root) (tree_edge_upd' ([], st0) root)).
      { cbv [dfs_fold]. rewrite dfs_fold'_S, Hseen. reflexivity. }
      rewrite Hres.
      assert (Hpush : dfs_fold_state root ([], st0) (tree_edge_upd' ([], st0) root)
                        (root :: []) [] (put_edge map.empty (hd root []) root)).
      { apply dfs_tree_edge.
        - intro Hc. cbv [graph_edge edges get_or] in Hc.
          rewrite map.get_empty in Hc. exact Hc.
        - apply dfs_init.
        - exact Hseen. }
      assert (Htop2 : already_seen (tree_edge_upd' ([], st0) root)
                        (hd root (root :: [])) = true).
      { cbn [hd]. rewrite already_seen_tree, eqb_reflV. reflexivity. }
      assert (Hclosed2 : seen_closed (tree_edge_upd' ([], st0) root)
                           (put_edge map.empty (hd root []) root)).
      { intros x b Hxb. apply graph_edge_put_edge in Hxb.
        rewrite already_seen_tree. apply Bool.orb_true_iff.
        destruct Hxb as [[Hx _]|Hxb].
        - left. subst x. apply eqb_reflV.
        - exfalso. cbv [graph_edge edges get_or] in Hxb.
          rewrite map.get_empty in Hxb. exact Hxb. }
      assert (Hfr2 : forall w, In w (edges g root) ->
                       ~ graph_edge (put_edge map.empty (hd root []) root)
                           (hd root (root :: [])) w).
      { intros w Hw Hc. apply graph_edge_put_edge in Hc. cbn [hd] in Hc.
        destruct Hc as [[_ Hwr]|Hc].
        - subst w. exact (Hroot Hw).
        - exfalso. cbv [graph_edge edges get_or] in Hc.
          rewrite map.get_empty in Hc. exact Hc. }
      destruct (dfs_fold_edges_sound g root ([], st0) Hnd (length (map.keys g))
                  (edges g root) (tree_edge_upd' ([], st0) root) (root :: []) []
                  (put_edge map.empty (hd root []) root)
                  Hpush Htop2 Hclosed2 Hfr2 (Hnd root))
        as (dun2 & g2 & Hstate2 & _).
      exists (root :: []), dun2, g2. exact Hstate2.
    Qed.

    (* The earlier target [dfs_fold'_reachable_spec] is subsumed by
       [dfs_fold'_sound] above (and lifted to the top level as [dfs_fold_sound]). *)

  End fold.

  Definition check_tree :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree).
End __.
