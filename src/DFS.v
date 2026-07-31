From Stdlib Require Import List.
From coqutil Require Import Map.Interface Datatypes.List Datatypes.ListSet Eqb.
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

    (*adding an edge from a different component should not change anything*)
    Print dfs_fold'.
    Print map.fold_spec.
    Print path.
    From Stdlib Require Import Lia.
    Lemma dfs_fold'_reachable_spec n root st0 g :
      forall u st1 p1 dun1 g1,
        dfs_fold_state root st0 st1 p1 dun1 g1 ->
        exists p2 dun2 g2,
          dfs_fold_state root st0 (dfs_fold' g n st1 u) p2 dun2 g2.
    Proof.
      induction n.
      - simpl. intros. Tactics.destruct_one_match.
        + do 3 eexists. constructor; [eassumption| |]. specialize (H [] ltac:(constructor) ltac:(constructor)).
        simpl in H. lia.
      - simpl. intros. subst. Tactics.destruct_one_match.
        +
        + cbv [already_seen]


      dfs_fold_state root st0
      P map.empty x0 ->
      (forall u v g x,
          has_edge g u v = false ->
          P g x ->
          P (put_edge g u v) ) ->
      forall g,
        reachable root g ->
        P g.

    (*not sure how to make this unugly*)

  End fold.

  Definition check_tree :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree).
End __.
