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
      dfs_fold_state _ _ st p g.

    Lemma graph_union_empty_r (g : graph) :
      graph.union g graph.empty = g.
    Proof. Admitted.

    Lemma graph_union_put_r (g1 g2 : graph) u v :
      graph.union g1 (graph.put g2 u v) = graph.put (graph.union g1 g2) u v.
    Proof. Admitted.

    Lemma dfs_fold_state_trans root st0 st st' p p' g g' u :
      dfs_fold_state root st0 st (u :: p) g ->
      dfs_fold_state u st st' p' g' ->
      dfs_fold_state root st0 st' (p' ++ u :: p) (graph.union g g').
    Proof.
      intros H. induction 1.
      - simpl. rewrite graph_union_empty_r. assumption.
      - simpl. rewrite graph_union_put_r.

        Print dfs_fold_state.

        econstructor. replace (graph.union g _) with graph.empty by admit.
      remember (u :: p) as p0 eqn:E. intros H.
      revert u p E.


    Context {ok : graph.ok graph}.
    Context {eqb_ok : Eqb_ok eqbV}.

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
          * eapply dfs_finish. constructor.
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
          { eapply dfs_finish. constructor. }
          cbv [restriction]. cbv [graph_edge]. intros. rewrite graph.edges_empty.
          simpl. split; [contradiction|]. intros. fwd.
          apply set_contains_iff_In in E. auto.
        + destruct (graph.edges g root).
          -- admit.
          -- destruct l. 2: admit. simpl. eexists. split.
             ++ econstructor.
    Admitted.

  End fold.

  Definition check_tree :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree).
End __.
