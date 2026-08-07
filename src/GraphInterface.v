From Stdlib Require Import List.
From coqutil Require Import Tactics.fwd Datatypes.List Datatypes.ListSet Eqb.
From GraphSearch Require Import List EdgeRel.
Import ListNotations.

(*some dumb tactic that isn't even particularly related to graphs.*)
Ltac graph :=
  repeat match goal with
    | _ => progress (intros; fwd; cbn [In] in *; subst)
    | _ => contradiction || solve[eauto]
    | H: _ \/ _ |- _ => destruct H
    | |- _ <-> _ => split
    end.

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
    sources_NoDup : forall g, NoDup (sources g);
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
    - rewrite IH, edges_put_edges. graph.
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
    apply graph_ext. intro v. intro x.
    rewrite edges_union, edges_empty. cbn [In]. tauto.
  Qed.

  Lemma union_put_r g1 g2 u v :
    union g1 (put g2 u v) = put (union g1 g2) u v.
  Proof.
    apply graph_ext. intro w. intro x.
    rewrite !edges_union, !edges_put, !edges_union. tauto.
  Qed.

  Lemma union_empty_l g :
    union empty g = g.
  Proof.
    apply graph_ext. intro v. intro x.
    rewrite edges_union, edges_empty. cbn [In]. tauto.
  Qed.

  Lemma union_assoc g1 g2 g3 :
    union (union g1 g2) g3 = union g1 (union g2 g3).
  Proof.
    apply graph_ext. intro w. intro x.
    rewrite !edges_union. tauto.
  Qed.

  Lemma sources_empty :
    sources empty = @nil vertex.
  Proof.
    apply forall_not_in_nil. intros x Hx. apply sources_spec in Hx.
    rewrite edges_empty in Hx. apply Hx. reflexivity.
  Qed.

  Lemma sources_put g u v u' :
    In u' (sources (put g u v)) <-> In u' (sources g) \/ u = u'.
  Proof.
    rewrite !sources_spec, !neq_nil_iff_exists_in. split.
    - intros [x Hx]. rewrite edges_put in Hx.
      destruct Hx as [Hx | [Hu _]]; [left; exists x; exact Hx | right; exact Hu].
    - intros [[x Hx] | Hu].
      + exists x. rewrite edges_put. left. exact Hx.
      + subst u'. exists v. rewrite edges_put. right. split; reflexivity.
  Qed.

  Lemma sources_union g1 g2 v :
    In v (sources (union g1 g2)) <-> In v (sources g1) \/ In v (sources g2).
  Proof.
    rewrite !sources_spec, !neq_nil_iff_exists_in. split.
    - intros [x Hx]. rewrite edges_union in Hx.
      destruct Hx as [Hx | Hx]; [left | right]; exists x; exact Hx.
    - intros [[x Hx] | [x Hx]]; exists x; rewrite edges_union; auto.
  Qed.

  Definition edge (g : graph) u v :=
    In v (edges g u).

  Lemma edge_union g1 g2 x y :
    edge (union g1 g2) x y <-> edge g1 x y \/ edge g2 x y.
  Proof. cbv [edge]. apply edges_union. Qed.

  Lemma edge_fold_union (gs : list graph) (g0 : graph) a b :
    edge (fold_left union gs g0) a b <->
    edge g0 a b \/ exists g, In g gs /\ edge g a b.
  Proof.
    revert g0. induction gs as [|g gs IH]; intros g0; cbn [fold_left].
    - graph.
    - rewrite IH, edge_union. graph.
  Qed.

  Lemma edge_empty x y :
    ~ edge empty x y.
  Proof. cbv [edge]. rewrite edges_empty. apply in_nil. Qed.

  Lemma edge_put g u v x y :
    edge (put g u v) x y <-> edge g x y \/ u = x /\ v = y.
  Proof. cbv [edge]. apply edges_put. Qed.

  Lemma path_in_graph g root p :
    path (edge g) root p ->
    incl (removelast (root :: p)) (sources g).
  Proof.
    revert root. induction p; intros root Hroot.
    - apply incl_nil_l.
    - simpl in Hroot. fwd. rewrite removelast_cons. apply incl_cons. 2: eauto.
      apply sources_spec. eapply in_not_nil. eassumption.
  Qed.

  Definition reachable_subgraph (g : graph) root (g' : graph) :=
    forall u v, edge g' u v <-> edge g u v /\ reaches (edge g) root u.

  Context {eqbV : Eqb vertex} {eqbV_ok : Eqb_ok eqbV}.

  Definition all_nodes g :=
    dedup eqb (flat_map (fun u => u :: edges g u) (sources g)).

  Definition all_edges g :=
    flat_map (fun u => map (pair u) (edges g u)) (sources g).

  Lemma all_nodes_empty :
    all_nodes empty = [].
  Proof. unfold all_nodes. rewrite sources_empty. reflexivity. Qed.

  Lemma all_nodes_spec g u :
    In u (all_nodes g) <-> (exists v, edge g u v \/ edge g v u).
  Proof.
    unfold all_nodes.
    rewrite <- dedup_preserves_In by (exact eqb_boolspec).
    rewrite in_flat_map. cbv [edge].
    split.
    - intros [w [Hw Hin]]. cbn [In] in Hin.
      apply sources_spec in Hw. apply neq_nil_iff_exists_in in Hw.
      destruct Hin as [Heq | Hin].
      + subst w. destruct Hw as [x Hx]. exists x. left. exact Hx.
      + exists w. right. exact Hin.
    - intros [v [Hv | Hv]].
      + exists u. split.
        * apply sources_spec. eapply in_not_nil. exact Hv.
        * cbn [In]. left. reflexivity.
      + exists v. split.
        * apply sources_spec. eapply in_not_nil. exact Hv.
        * cbn [In]. right. exact Hv.
  Qed.

  Lemma all_nodes_put g u v u' :
    In u' (all_nodes (put g u v)) <->
      In u' (all_nodes g) \/ u' = u \/ u' = v.
  Proof.
    rewrite !all_nodes_spec. setoid_rewrite edge_put.
    graph.
  Qed.

  Lemma all_nodes_NoDup g :
    NoDup (all_nodes g).
  Proof. unfold all_nodes. apply NoDup_dedup. Qed.

  Lemma In_all_edges g a b :
    In (a, b) (all_edges g) <-> edge g a b.
  Proof.
    unfold all_edges, edge. rewrite in_flat_map. split.
    - intros [u [Hu Hin]]. apply in_map_iff in Hin. graph.
    - intro Hb. exists a. split.
      + apply sources_spec. eapply in_not_nil. exact Hb.
      + apply in_map_iff. eauto.
  Qed.

  Lemma all_edges_NoDup g :
    NoDup (all_edges g).
  Proof.
    unfold all_edges. apply NoDup_flat_map.
    - apply sources_NoDup.
    - intros u Hu. apply NoDup_map_NoDup_ForallPairs; [ | apply edges_NoDup ].
      intros x y _ _ Heq. congruence.
    - intros u1 u2 [a b] Hu1 Hu2 Hin1 Hin2.
      apply in_map_iff in Hin1. destruct Hin1 as [w1 [Heq1 _]].
      apply in_map_iff in Hin2. destruct Hin2 as [w2 [Heq2 _]].
      congruence.
  Qed.
  Definition num_nodes g root :=
    length (list_union eqb [root] (all_nodes g)).

  Definition num_edges g :=
    length (all_edges g).

  Definition is_tree g root :=
    all_reachable (edge g) root /\
      S (num_edges g) = num_nodes g root.

  Lemma num_edges_empty :
    num_edges empty = O.
  Proof. unfold num_edges, all_edges. rewrite sources_empty. reflexivity. Qed.

  Lemma num_nodes_empty root :
    num_nodes empty root = S O.
  Proof. unfold num_nodes. rewrite all_nodes_empty. reflexivity. Qed.

  Lemma num_edges_put g u v :
    ~edge g u v ->
    num_edges (put g u v) = S (num_edges g).
  Proof.
    intro Hne. unfold num_edges.
    transitivity (length ((u, v) :: all_edges g)).
    - apply NoDup_same_length.
      + apply all_edges_NoDup.
      + apply NoDup_cons.
        * rewrite In_all_edges. exact Hne.
        * apply all_edges_NoDup.
      + intros [a b]. rewrite In_all_edges, edge_put. cbn [In].
        rewrite In_all_edges, pair_equal_spec. tauto.
    - reflexivity.
  Qed.

  Lemma num_nodes_put01 g root u v :
    In u (root :: all_nodes g) ->
    ~In v (all_nodes g) ->
    v <> root ->
    num_nodes (put g u v) root = S (num_nodes g root).
  Proof.
    intros Hu Hv Hvr. cbn [In] in Hu. unfold num_nodes.
    transitivity (length (v :: list_union eqb [root] (all_nodes g))).
    - apply NoDup_same_length.
      + apply list_union_preserves_NoDup. apply all_nodes_NoDup.
      + apply NoDup_cons.
        * rewrite In_list_union_spec. cbn [In].
          intros [[Hr | []] | Hin]; [ congruence | exact (Hv Hin) ].
        * apply list_union_preserves_NoDup. apply all_nodes_NoDup.
      + intro x. rewrite In_list_union_spec, all_nodes_put. cbn [In].
        rewrite In_list_union_spec. cbn [In].
        split.
        * intros [Hr | [Hg | [Hxu | Hxv]]]; subst; tauto.
        * intros [Hxv | [Hr | Hg]]; subst; tauto.
    - reflexivity.
  Qed.

  Lemma num_nodes_put00 g root u v :
    In u (root :: all_nodes g) ->
    In v (root :: all_nodes g) ->
    num_nodes (put g u v) root = num_nodes g root.
  Proof.
    intros Hu Hv. unfold num_nodes. apply NoDup_same_length.
    - apply list_union_preserves_NoDup. apply all_nodes_NoDup.
    - apply list_union_preserves_NoDup. apply all_nodes_NoDup.
    - intro x. rewrite !In_list_union_spec, all_nodes_put. cbn [In] in *.
      split.
      + intros [Hr | [Hg | [Hxu | Hxv]]]; subst; tauto.
      + tauto.
  Qed.
End ops.
End graph.
Global Coercion graph.rep : graph.graph >-> Sortclass.
