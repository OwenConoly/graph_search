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

  (* union of m1 and m2; on a key in both, the value is f m1's-value m2's-value. *)
  Definition union_with (f : value -> value -> value) (m1 m2 : mp) : mp :=
    map.fold (fun acc k v2 =>
      match map.get acc k with
      | Some v1 => map.put acc k (f v1 v2)
      | None => map.put acc k v2
      end) m1 m2.
End map.

Section list.
  Context {A : Type}.

  Definition disjoint_lists (l1 l2 : list A) :=
    forall x, In x l1 -> In x l2 -> False.
End list.

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

  Context {eqbV : Eqb V}.
  Context {graph : map.map V (list V)}.

  Section fold.
    Definition set_contains vs v :=
      List.existsb (eqb v) vs.

    Inductive dfs_tree :=
    | node (name : V) (untree_edges : list V) (tree_edges : list dfs_tree).

    Definition name_of (t : dfs_tree) :=
      match t with
      | node name _ _ => name
      end.

    Fixpoint edges_of (t : dfs_tree) :=
      match t with
      | node u untree_edges tree_edges =>
          map (pair u) (untree_edges ++ map name_of tree_edges)
            ++ flat_map edges_of tree_edges
      end.

    Fixpoint nodes_of t :=
      match t with
      | node u _ tree_edges => u :: flat_map nodes_of tree_edges
      end.

    Definition valid_dfs_tree t :=
      NoDup (nodes_of t) /\ NoDup (edges_of t).

    Section with_graph.
      Context (g : graph).

      Definition edges u := get_or [] g u.
      Definition has_edge u v := set_contains (edges u) v.
      Definition put_edge u v := mupd_total [] (list_union eqb [v]) g u.

      Fixpoint dfs_tree_of' n (vs : list V) u : list V * dfs_tree :=
        match n with
        | S n' =>
            let '(vs', untree_edges, tree_edges) :=
              fold_left (fun '(vs', untree_edges, tree_edges) v =>
                           if set_contains vs' v then
                             (vs', v :: untree_edges, tree_edges)
                           else
                             let '(vs'', tree_edge) := dfs_tree_of' n' vs' v in
                             (vs'', untree_edges, tree_edge :: tree_edges))
                (edges u) (u :: vs, [], []) in
            (vs', node u untree_edges tree_edges)
        | O => (vs, node u [] [])
        end.

      Definition dfs_tree_of u :=
        snd (dfs_tree_of' (S (length (map.keys g))) [] u).
    End with_graph.

    Definition put_edges :=
      fold_left (fun g '(u, v) => put_edge g u v).

    (*true for connected graphs*)
    Lemma dfs_tree_of_spec g v :
      put_edges (edges_of (dfs_tree_of g v)) map.empty = g.
    Proof. Abort.
  End fold.
End __.
