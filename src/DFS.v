From Stdlib Require Import List.
From coqutil Require Import Map.Interface Datatypes.List Datatypes.ListSet.
Import ListNotations.

Section __.
  Context {V : Type}.
  Context {eqbV : V -> V -> bool}.
  Context {graph : map.map V (list V)}.
  Context {state : Type}.
  Context (backedge_upd : state -> list V -> V -> V -> state).
  Context (foreedge_upd : state -> list V -> V -> V -> state).

  Definition set_contains vs v :=
    List.existsb (eqbV v) vs.

  Context (g : graph).

  Definition edges u :=
    match map.get g u with
    | Some vs => vs
    | None => []
    end.

  Fixpoint dfs n vs v :=
    if set_contains vs v then vs else
      match n with
      | S n' => fold_left (dfs n') (v :: vs) (edges v)
      | O => vs
      end.
