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
    | node (name : V) (back_edges : list V) (fore_edges : list dfs_tree).

    Fixpoint valid_dfs_tree' (ctx : list V) (t : dfs_tree) :=
      match t with
      | node u back_edges fore_edges =>
          ~In u ctx /\
            NoDup back_edges /\
            Forall (fun v => In v ctx) back_edges /\
            Forall (fun P => P) (map (valid_dfs_tree' (u :: ctx)) fore_edges)
      end.

    Definition valid_dfs_tree := valid_dfs_tree' [].

    Section with_graph.
      Context (g : graph).

      Definition edges u := get_or [] g u.
      Definition has_edge u v := set_contains (edges u) v.
      Definition put_edge u v := mupd_total [] (list_union eqb [v]) g u.

      Fixpoint dfs_tree_of' n vs v :=
        if set_contains vs v then vs else
          match n with
          | S n' => fold_left (dfs_tree_of' n') (edges v) (v :: vs)
          | O => vs
          end.

      Definition dfs_tree_of := dfs_tree_of' (S (length (map.keys g))) [].
    End with_graph.

    Fixpoint graph_of' (parent : option V) (t : dfs_tree) :=
      match t with
      | node u back_edges fore_edges =>
          let g := fold_left (union_with (list_union eqb)) (map (graph_of' (Some u)) fore_edges) map.empty in
          let g' := fold_left (fun g v => put_edge g u v) back_edges g in
          match parent with
          | Some p => put_edge g' p u
          | None => g'
          end
      end.

    Definition graph_of := graph_of' None.

    (*true for connected graphs*)
    Lemma dfs_tree_of_spec g v :
      graph_of (fs_tree_of g v) = g.

  End with_graph.

    (* Lemma dfs_fold_spec X (P : graph -> T -> Prop) x0 : *)
    (*   P map.empty x0 -> *)
    (*   (forall u v g x, *)
    (*       has_edge g u v = false -> *)
    (*       P g x -> *)
    (*       P (put_edge g u v) ( *)
    (*not sure how to make this unugly*)

  End fold.

End __.
