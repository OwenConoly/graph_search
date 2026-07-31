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
    Context (node : V -> Prop).
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
    Context (backedge_upd : state -> list V -> V -> state).
    Context (foreedge_upd : state -> list V -> V -> state).

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
      Definition backedge_upd' '(vs, st) v := (vs, backedge_upd st vs v).
      Definition foreedge_upd' '(vs, st) v := (v :: vs, foreedge_upd st vs v).

      Definition already_seen (st' : state') v :=
        let '(vs, _) := st' in set_contains vs v.

      Fixpoint dfs_fold' n st' v :=
        if already_seen st' v then backedge_upd' st' v else
          match n with
          | S n' => fold_left (dfs_fold' n') (edges v) (foreedge_upd' st' v)
          | O => st'
          end.

      Definition dfs_fold := dfs_fold' (S (length (map.keys g))).
    End with_graph.

    (*adding an edge from a different forest should not change anything*)
    Lemma dfs_fold_spec X (P : graph -> T -> Prop) x0 :
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
