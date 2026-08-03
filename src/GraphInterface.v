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

Section ops.
  Context {vertex : Type} {graph : graph vertex} {ok : ok graph}.

  Definition put_edges g u vs :=
    fold_left (fun g v => put g u v) vs g.

  Definition union g1 g2 :=
    fold_left (fun g u => put_edges g u (edges g2 u)) (sources g2) g1.

  Lemma edges_put_edges g u vs u' v' :
    In v' (edges (put_edges g u vs) u') <->
      In v' (edges g u') \/ u = u' /\ In v' vs.
  Proof.
    unfold put_edges. revert g. induction vs as [|a vs IH]; intros g; cbn [fold_left].
    - cbn [In]. tauto.
    - rewrite IH, edges_put. cbn [In]. tauto.
  Qed.

  Lemma edges_fold_union ss g1 g2 u' v' :
    In v' (edges (fold_left (fun g u => put_edges g u (edges g2 u)) ss g1) u') <->
      In v' (edges g1 u') \/ In u' ss /\ In v' (edges g2 u').
  Proof.
    revert g1. induction ss as [|a ss IH]; intros g1; cbn [fold_left In].
    - tauto.
    - rewrite IH, edges_put_edges. cbn [In].
      split.
      + intros [[?|[-> ?]]|[? ?]]; auto 7.
      + intros [?|[[->|?] ?]]; auto 7.
  Qed.

  Lemma edges_union g1 g2 u' v' :
    In v' (edges (union g1 g2) u') <->
      In v' (edges g1 u') \/ In v' (edges g2 u').
  Proof.
    unfold union. rewrite edges_fold_union.
    split.
    - intros [H|[_ H]]; auto.
    - intros [H|H]; [auto|]. right. split; [|exact H].
      apply (proj2 (sources_spec g2 u')). intro Hnil. rewrite Hnil in H. exact H.
  Qed.

  Lemma union_empty_r g :
    union g empty = g.
  Proof.
    apply graph_ext. intro v. unfold same_set. split; intros x Hx.
    - rewrite edges_union, edges_empty in Hx.
      destruct Hx as [H|H]; [exact H | destruct H].
    - rewrite edges_union, edges_empty. left. exact Hx.
  Qed.

  Lemma union_put_r g1 g2 u v :
    union g1 (put g2 u v) = put (union g1 g2) u v.
  Proof.
    apply graph_ext. intro w. unfold same_set.
    assert (Hiff : forall x,
               In x (edges (union g1 (put g2 u v)) w)
               <-> In x (edges (put (union g1 g2) u v) w)).
    { intro x. rewrite !edges_union, !edges_put, !edges_union. tauto. }
    split; intros x Hx; [exact (proj1 (Hiff x) Hx) | exact (proj2 (Hiff x) Hx)].
  Qed.

  Lemma union_empty_l g :
    union empty g = g.
  Proof.
    apply graph_ext. intro v. unfold same_set. split; intros x Hx.
    - rewrite edges_union, edges_empty in Hx.
      destruct Hx as [H|H]; [destruct H | exact H].
    - rewrite edges_union, edges_empty. right. exact Hx.
  Qed.

  Lemma union_assoc g1 g2 g3 :
    union (union g1 g2) g3 = union g1 (union g2 g3).
  Proof.
    apply graph_ext. intro w. unfold same_set.
    assert (Hiff : forall x,
               In x (edges (union (union g1 g2) g3) w)
               <-> In x (edges (union g1 (union g2 g3)) w)).
    { intro x. rewrite !edges_union. tauto. }
    split; intros x Hx; [exact (proj1 (Hiff x) Hx) | exact (proj2 (Hiff x) Hx)].
  Qed.
End ops.
End graph.
Global Coercion graph.rep : graph.graph >-> Sortclass.
