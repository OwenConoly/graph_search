From Stdlib Require Import List.
From coqutil Require Import Map.Interface Datatypes.List Datatypes.ListSet.
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
  End path.

  Context {eqbV : V -> V -> bool}.
  Context {graph : map.map V (list V)}.

  Section fold.
    Context {state : Type}.
    Context (backedge_upd : state -> list V -> V -> state).
    Context (foreedge_upd : state -> list V -> V -> state).

    Definition set_contains vs v :=
      List.existsb (eqbV v) vs.

    Context (g : graph).

    Definition edges u :=
      match map.get g u with
      | Some vs => vs
      | None => []
      end.

    Definition state' : Type := list V * state.
    Definition backedge_upd' '(vs, st) v := (v :: vs, backedge_upd st vs v).
    Definition foreedge_upd' '(vs, st) v := (v :: vs, foreedge_upd st vs v).

    Definition already_seen (st' : state') v :=
      let '(vs, _) := st' in set_contains vs v.

    Fixpoint dfs_fold' n st' v :=
      if already_seen st' v then backedge_upd' st' v else
        match n with
        | S n' => fold_left (dfs_fold' n') (edges v) (foreedge_upd' st' v)
        | O => st'
        end.

    Definition dfs_fold := dfs_fold' (length (map.keys g)).
  End fold.

  Definition check_tree :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => true).
