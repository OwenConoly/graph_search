From Stdlib Require Import List.
Import ListNotations.

Definition same_set {A} (l1 l2 : list A) := incl l1 l2 /\ incl l2 l1.
(*closely following Map.Interface, because idk what i am doing*)
Module graph.
Class graph {vertex} := {
    rep : Type;
    edges: rep -> vertex -> list vertex;
    empty : rep;
    put : rep -> vertex -> vertex -> rep;
    remove : rep -> vertex -> vertex -> rep;
    sources : rep -> list vertex;
  }.
Arguments graph : clear implicits.
Global Coercion rep : graph >-> Sortclass.
Global Hint Mode graph + : typeclass_instances.
Local Hint Mode graph - : typeclass_instances.

Class ok {vertex} {graph : graph vertex} : Prop := {
    graph_ext : forall g1 g2, (forall v, same_set (edges g1 v) (edges g2 v)) -> g1 = g2;
    edges_empty : forall v, edges empty v = [];
    edges_put : forall g u u' v v', In v' (edges (put g u v) u') <-> In v' (edges g u') \/ u = u' /\ v = v';
    edges_remove : forall g u v u' v', In v' (edges (remove g u v) u') <-> In v' (edges g u') /\ (u <> u' \/ v <> v');
    sources_spec : forall g u, In u (sources g) <-> edges g u <> nil;
    edges_NoDup : forall g u, NoDup (edges g u);
  }.
Arguments ok {_} _.
End graph.
Global Coercion graph.rep : graph.graph >-> Sortclass.
