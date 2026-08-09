From Stdlib Require Import List.
From coqutil Require Import Tactics.fwd Datatypes.List Datatypes.ListSet Eqb.
From GraphSearch Require Import List.
Import ListNotations.

(*some dumb tactic that isn't even particularly related to graphs.*)
Ltac graph :=
  repeat match goal with
    | |- ~ _ => intro
    | _ => progress (intros; fwd; cbn [In] in *; subst)
    | _ => contradiction || congruence || solve[eauto]
    | H: _ \/ _ |- _ => destruct H
    | |- _ <-> _ => split
    | |- _ /\ _ => split
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

Definition edge {vertex} {graph : graph vertex} (g : graph) u v :=
  In v (edges g u).

Class ok {vertex} {graph : graph vertex} : Prop := {
    graph_ext : forall g1 g2, (forall u v, edge g1 u v <-> edge g2 u v) -> g1 = g2;
    edge_empty : forall u v, ~edge graph.empty u v;
    edge_put : forall g u u' v v', edge (put g u v) u' v' <-> edge g u' v' \/ u = u' /\ v = v';
    edge_remove : forall g u v u' v', edge (remove g u v) u' v' <-> edge g u' v' /\ (u <> u' \/ v <> v');
    sources_spec : forall g u, In u (sources g) <-> exists v, edge g u v;
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

  Lemma edge_put_edges g u vs u' v' :
    edge (put_edges g u vs) u' v' <-> edge g u' v' \/ u = u' /\ In v' vs.
  Proof.
    unfold put_edges. revert g. induction vs as [|a vs IH]; intros g; cbn [fold_left].
    - cbn [In]. tauto.
    - rewrite IH, edge_put. cbn [In]. tauto.
  Qed.

  Lemma edge_union_fold ss g1 g2 u' v' :
    edge (fold_left (fun g u => put_edges g u (edges g2 u)) ss g1) u' v' <->
      edge g1 u' v' \/ In u' ss /\ edge g2 u' v'.
  Proof.
    revert g1. induction ss as [|a ss IH]; intros g1; cbn [fold_left].
    - cbn [In]. tauto.
    - rewrite IH, edge_put_edges. graph.
  Qed.

  Lemma edge_union g1 g2 u' v' :
    edge (union g1 g2) u' v' <-> edge g1 u' v' \/ edge g2 u' v'.
  Proof.
    unfold union. rewrite edge_union_fold, sources_spec. graph.
  Qed.

  Lemma edge_empty_iff u v :
    edge empty u v <-> False.
  Proof. split; [ exact (edge_empty u v) | intros [] ]. Qed.

  Lemma union_empty_r g :
    union g empty = g.
  Proof.
    apply graph_ext. intros u v. rewrite edge_union, edge_empty_iff. tauto.
  Qed.

  Lemma union_put_r g1 g2 u v :
    union g1 (put g2 u v) = put (union g1 g2) u v.
  Proof.
    apply graph_ext. intros w x. rewrite !edge_union, !edge_put, !edge_union. tauto.
  Qed.

  Lemma union_empty_l g :
    union empty g = g.
  Proof.
    apply graph_ext. intros u v. rewrite edge_union, edge_empty_iff. tauto.
  Qed.

  Lemma union_assoc g1 g2 g3 :
    union (union g1 g2) g3 = union g1 (union g2 g3).
  Proof.
    apply graph_ext. intros u v. rewrite !edge_union. tauto.
  Qed.

  Lemma sources_empty :
    sources empty = @nil vertex.
  Proof.
    apply forall_not_in_nil. intros x Hx. apply sources_spec in Hx.
    destruct Hx as [v Hv]. exact (edge_empty x v Hv).
  Qed.

  Lemma sources_put g u v u' :
    In u' (sources (put g u v)) <-> In u' (sources g) \/ u = u'.
  Proof.
    rewrite !sources_spec. setoid_rewrite edge_put. graph.
  Qed.

  Lemma sources_union g1 g2 v :
    In v (sources (union g1 g2)) <-> In v (sources g1) \/ In v (sources g2).
  Proof.
    rewrite !sources_spec. setoid_rewrite edge_union. graph.
  Qed.

  Lemma edge_in_sources g u v :
    edge g u v -> In u (sources g).
  Proof. intro H. apply sources_spec. eauto. Qed.

  Definition subgraph (g1 g2 : graph) :=
    forall u v, edge g1 u v -> edge g2 u v.

  Lemma edge_fold_union (gs : list graph) (g0 : graph) a b :
    edge (fold_left union gs g0) a b <->
    edge g0 a b \/ exists g, In g gs /\ edge g a b.
  Proof.
    revert g0. induction gs as [|g gs IH]; intros g0; cbn [fold_left].
    - graph.
    - rewrite IH, edge_union. graph.
  Qed.

  Lemma subgraph_put g u v :
    subgraph g (put g u v).
  Proof. intros x y H. apply edge_put. left. exact H. Qed.

  Fixpoint path (g : graph) (first : vertex) (p : list vertex) :=
    match p with
    | [] => True
    | next :: p' => edge g first next /\ path g next p'
    end.

  Definition path_to g first p last :=
    path g first p /\ last = List.last p first.

  Definition reaches g first last :=
    exists p, path_to g first p last.

  Definition all_reachable g root :=
    forall u v, edge g u v -> reaches g root u.

  Lemma reaches_self g u :
    reaches g u u.
  Proof. cbv [reaches]. exists nil. cbv [path_to]. simpl. auto. Qed.

  Lemma reaches_step_before g u v w :
    reaches g v w ->
    edge g u v ->
    reaches g u w.
  Proof.
    cbv [reaches path_to]. intros. fwd. eexists (_ :: _). simpl. split; eauto.
    destruct p; try reflexivity. apply last_cons_last_cons.
  Qed.

  Lemma edge_closed_reaches_in g u0 v0 vs :
    (forall u v, In u vs -> edge g u v -> In v vs) ->
    In u0 vs ->
    reaches g u0 v0 ->
    In v0 vs.
  Proof.
    intros H Hu0 Hreach. cbv [reaches path_to] in Hreach. fwd.
    revert u0 Hu0 Hreachp0. induction p; cbn [path]; intros u0 Hu0 Hreach; auto.
    fwd. destruct p; eauto. rewrite last_cons. apply IHp; eauto.
  Qed.

  Lemma path_subgraph g1 g2 first p :
    subgraph g1 g2 ->
    path g1 first p ->
    path g2 first p.
  Proof.
    intros HR. cbv [subgraph] in HR. revert first.
    induction p as [|a p IH]; intros first; cbn [path]; auto.
    intros [He Hp]. eauto.
  Qed.

  Lemma path_snoc g first p v :
    path g first (p ++ [v]) <-> path g first p /\ edge g (last p first) v.
  Proof.
    revert first. induction p as [|a p IH]; intros first.
    - simpl. tauto.
    - cbn [app path]. rewrite IH, last_cons. tauto.
  Qed.

  Lemma reaches_subgraph g1 g2 u v :
    subgraph g1 g2 ->
    reaches g1 u v ->
    reaches g2 u v.
  Proof.
    cbv [reaches path_to]. intros HR [p [Hp Hlast]].
    exists p. split; [eapply path_subgraph; eauto | exact Hlast].
  Qed.

  Lemma reaches_step g u v w :
    reaches g u v ->
    edge g v w ->
    reaches g u w.
  Proof.
    cbv [reaches path_to]. intros [p [Hp Hlast]] Hedge.
    exists (p ++ [w]). rewrite path_snoc, last_last. subst v.
    split; [split; assumption | reflexivity].
  Qed.

  Lemma path_sink_last g v first p :
    (forall w, ~ edge g v w) ->
    path g first p ->
    In v p ->
    last p first = v.
  Proof.
    intros Hsink. revert first. induction p as [|a p IH]; intros first Hpath Hin.
    - destruct Hin.
    - destruct Hpath as [He Hp]. rewrite last_cons. destruct Hin as [-> | Hin].
      + destruct p as [|b p']; [reflexivity|]. destruct Hp as [Hvb _].
        exfalso. eapply Hsink; exact Hvb.
      + apply IH; assumption.
  Qed.

  Lemma path_in_graph g root p :
    path g root p ->
    incl (removelast (root :: p)) (sources g).
  Proof.
    revert root. induction p; intros root Hroot.
    - apply incl_nil_l.
    - simpl in Hroot. fwd. rewrite removelast_cons. apply incl_cons. 2: eauto.
      apply sources_spec. eauto.
  Qed.

  Definition reachable_subgraph (g : graph) root (g' : graph) :=
    forall u v, edge g' u v <-> edge g u v /\ reaches g root u.

  Lemma reachable_subgraph_unique g root g1 g2 :
    reachable_subgraph g root g1 ->
    reachable_subgraph g root g2 ->
    g1 = g2.
  Proof.
    intros H1 H2. apply graph_ext. intros. cbv [reachable_subgraph] in *.
    rewrite H1, H2. reflexivity.
  Qed.

  Lemma reachable_subgraph_all (g : graph) root (g' : graph) :
    all_reachable g root ->
    reachable_subgraph g root g' ->
    g' = g.
  Proof.
    intros Hall Hrs. cbv [reachable_subgraph] in Hrs.
    apply graph_ext. intros u v. rewrite Hrs. split.
    - intros [He _]. exact He.
    - intro He. split; [ exact He | eapply Hall; exact He ].
  Qed.

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
    rewrite in_flat_map. setoid_rewrite sources_spec. graph.
  Qed.

  Lemma all_nodes_put g u v u' :
    In u' (all_nodes (put g u v)) <->
      In u' (all_nodes g) \/ u' = u \/ u' = v.
  Proof.
    rewrite !all_nodes_spec. setoid_rewrite edge_put. graph.
  Qed.

  Lemma all_nodes_NoDup g :
    NoDup (all_nodes g).
  Proof. unfold all_nodes. apply NoDup_dedup. Qed.

  Hint Unfold edge : core.
  Lemma In_all_edges g a b :
    In (a, b) (all_edges g) <-> edge g a b.
  Proof.
    unfold all_edges, edge. rewrite in_flat_map.
    setoid_rewrite in_map_iff. setoid_rewrite sources_spec.
    graph. eauto 10.
  Qed.

  Lemma In_map_snd_all_edges (g : graph) x :
    In x (map snd (all_edges g)) <-> exists u, edge g u x.
  Proof.
    rewrite in_map_iff. split.
    - intros [[u y] [Hs Hin]]. cbn in Hs. subst y.
      rewrite In_all_edges in Hin. eauto.
    - intros [u He]. exists (u, x). cbn. split; [ reflexivity | ].
      apply In_all_edges. exact He.
  Qed.

  Lemma all_edges_NoDup g :
    NoDup (all_edges g).
  Proof.
    unfold all_edges. apply NoDup_flat_map.
    - apply sources_NoDup.
    - intros u Hu. apply NoDup_map_NoDup_ForallPairs; [ | apply edges_NoDup ].
      intros x y _ _ Heq. congruence.
    - intros. rewrite in_map_iff in *. graph.
  Qed.

  Definition num_nodes g root :=
    length (list_union eqb [root] (all_nodes g)).

  Definition num_edges g :=
    length (all_edges g).

  Lemma subgraph_eq (g g' : graph) :
    subgraph g' g ->
    num_edges g' = num_edges g ->
    g' = g.
  Proof.
    intros Hsub Hlen. apply graph_ext. intros u v. split; [ exact (Hsub u v) | ].
    intro He. rewrite <- In_all_edges in He |- *.
    assert (Hincl : incl (all_edges g) (all_edges g')).
    { apply NoDup_length_incl.
      - apply all_edges_NoDup.
      - unfold num_edges in Hlen. rewrite Hlen. apply le_n.
      - intros [a b] Hab. rewrite In_all_edges in Hab |- *. apply Hsub. exact Hab. }
    exact (Hincl _ He).
  Qed.

  Lemma subgraph_num_edges (g1 g2 : graph) :
    subgraph g1 g2 ->
    num_edges g1 <= num_edges g2.
  Proof.
    intro Hsub. unfold num_edges. apply NoDup_incl_length.
    - apply all_edges_NoDup.
    - intros [a b] Hab. rewrite In_all_edges in Hab |- *. apply Hsub. exact Hab.
  Qed.

  Definition is_tree g root :=
    all_reachable g root /\
      S (num_edges g) = num_nodes g root.

  Definition is_locally_tree g root :=
    exists g', reachable_subgraph g root g' /\ S (num_edges g') = num_nodes g' root.

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
        * rewrite In_list_union_spec. graph.
        * apply list_union_preserves_NoDup. apply all_nodes_NoDup.
      + intro x. rewrite In_list_union_spec, all_nodes_put. cbn [In].
        rewrite In_list_union_spec. graph.
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
    - intro x. rewrite !In_list_union_spec, all_nodes_put.
      graph.
  Qed.
End ops.
End graph.
Global Coercion graph.rep : graph.graph >-> Sortclass.
