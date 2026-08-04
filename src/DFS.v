From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Eqb.
From coqutil Require Import Tactics.destr Tactics.Tactics.
From GraphSearch Require Import GraphInterface.
Import ListNotations.

(* Generic; belongs in a list util. Invariant indexed by the unprocessed suffix,
   so the step for the head knows it is still pending. *)
Lemma fold_left_invariant {A B} (P : list B -> A -> Prop) (f : A -> B -> A) :
  forall l a,
    P l a ->
    (forall a' b l', P (b :: l') a' -> P l' (f a' b)) ->
    P [] (fold_left f l a).
Proof.
  induction l as [|b l' IH]; intros a HP Hstep; [exact HP|].
  cbn [fold_left]. apply IH; [apply Hstep; exact HP | exact Hstep].
Qed.

(* fold_left commutes with a function the step commutes with. *)
Lemma fold_left_hom {A B} (f : A -> B -> A) (k : A -> A) l :
  (forall a b, f (k a) b = k (f a b)) ->
  forall a, fold_left f l (k a) = k (fold_left f l a).
Proof.
  intro Hstep. induction l as [|b l' IH]; intro a; [reflexivity|].
  cbn [fold_left]. rewrite Hstep. apply IH.
Qed.

(* Binary version: relate two folds over the same list with different steps. *)
Lemma fold_left_invariant2 {A B C} (P : list C -> A -> B -> Prop)
      (f : A -> C -> A) (h : B -> C -> B) :
  forall l a b,
    P l a b ->
    (forall a' b' c l', P (c :: l') a' b' -> P l' (f a' c) (h b' c)) ->
    P [] (fold_left f l a) (fold_left h l b).
Proof.
  induction l as [|c l' IH]; intros a b HP Hstep; [exact HP|].
  cbn [fold_left]. apply IH; [apply Hstep; exact HP | exact Hstep].
Qed.

Lemma In_last {A} (l : list A) d :
  l <> [] -> In (last l d) l.
Proof.
  intro Hne. rewrite (app_removelast_last d Hne) at 2.
  apply in_or_app. right. left. reflexivity.
Qed.

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
  Context {graph : graph.graph V}.
  Context {ok : graph.ok graph}.
  Context {eqb_ok : Eqb_ok eqbV}.

  Section fold.
    Context {state : Type}.
    Context (untree_edge_upd : state -> list V -> V -> state).
    Context (tree_edge_upd : state -> list V -> V -> state).
    Context (finish : state -> list V -> V -> state).

    Definition set_contains vs v :=
      List.existsb (eqb v) vs.

    Section with_graph.
      Context (g : graph).

      Definition graph_edge u v := In v (graph.edges g u).

      Definition state' : Type := list V * state.
      Definition untree_edge_upd' '(vs, st) v := (vs, untree_edge_upd st vs v).
      Definition tree_edge_upd' '(vs, st) v := (v :: vs, tree_edge_upd st vs v).
      Definition finish' '(vs, st) v := (vs, finish st vs v).

      Definition already_seen (st' : state') v :=
        let '(vs, _) := st' in set_contains vs v.

      Fixpoint dfs_fold' n st' v : state' :=
        if already_seen st' v then untree_edge_upd' st' v else
          match n with
          | S n' => finish' (fold_left (dfs_fold' n') (graph.edges g v) (tree_edge_upd' st' v)) v
          | O => st'
          end.

      Definition dfs_fold st0 := dfs_fold' (S (length (graph.sources g))) ([], st0).
    End with_graph.

    Inductive dfs_fold_state (root : V) (st0 : state') : state' -> list V (*current path*)-> graph (*explored edges*) -> Prop :=
    | dfs_init : dfs_fold_state _ _ st0 [root] graph.empty
    | dfs_tree_edge st u p g v :
      ~graph_edge g u v ->
      dfs_fold_state _ _ st (u :: p) g ->
      already_seen st v = false ->
      dfs_fold_state _ _ (tree_edge_upd' st v) (v :: u :: p) (graph.put g u v)
    | dfs_untree_edge st u p g v :
      dfs_fold_state _ _ st (u :: p) g ->
      ~graph_edge g u v ->
      already_seen st v = true ->
      dfs_fold_state _ _ (untree_edge_upd' st v) (u :: p) (graph.put g u v)
    | dfs_finish st u p g :
      dfs_fold_state _ _ st (u :: p) g ->
      dfs_fold_state _ _ (finish' st u) p g.

    Definition edge_upd' st v :=
      if already_seen st v then untree_edge_upd' st v else
        tree_edge_upd' st v.

    Lemma graph_edge_union g1 g2 x y :
      graph_edge (graph.union g1 g2) x y <-> graph_edge g1 x y \/ graph_edge g2 x y.
    Proof. cbv [graph_edge]. apply graph.edges_union. Qed.

    Lemma already_seen_tree_edge_upd st v y :
      already_seen st y = true -> already_seen (tree_edge_upd' st v) y = true.
    Proof.
      destruct st as [vs s]. cbn [already_seen tree_edge_upd']. simpl.
      intro H. rewrite H. destruct (eqb y v); reflexivity.
    Qed.

    Lemma already_seen_tree_edge_upd_self st v :
      already_seen (tree_edge_upd' st v) v = true.
    Proof.
      destruct st as [vs s]. cbn [already_seen tree_edge_upd']. simpl.
      destruct (@eqb_boolspec V eqbV eqb_ok v v); [reflexivity | congruence].
    Qed.

    Lemma already_seen_untree_edge_upd st v y :
      already_seen (untree_edge_upd' st v) y = already_seen st y.
    Proof. destruct st as [vs s]. reflexivity. Qed.

    Lemma already_seen_finish' st v y :
      already_seen (finish' st v) y = already_seen st y.
    Proof. destruct st as [vs s]. reflexivity. Qed.

    Lemma already_seen_mono root st0 st p g y :
      dfs_fold_state root st0 st p g ->
      already_seen st0 y = true ->
      already_seen st y = true.
    Proof.
      induction 1 as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intro Hy.
      - exact Hy.
      - apply already_seen_tree_edge_upd. apply IH. exact Hy.
      - rewrite already_seen_untree_edge_upd. apply IH. exact Hy.
      - rewrite already_seen_finish'. apply IH. exact Hy.
    Qed.

    Lemma dfs_target_seen root st0 st p g x y :
      dfs_fold_state root st0 st p g -> graph_edge g x y -> already_seen st y = true.
    Proof.
      intro H. revert x y.
      induction H as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. destruct He.
      - rewrite graph.edges_put in He. destruct He as [Hold | [_ Hvy]].
        + apply already_seen_tree_edge_upd. apply (IH x y). exact Hold.
        + subst y. apply already_seen_tree_edge_upd_self.
      - rewrite graph.edges_put in He. rewrite already_seen_untree_edge_upd.
        destruct He as [Hold | [_ Hvy]].
        + apply (IH x y). exact Hold.
        + subst y. exact Hseen.
      - rewrite already_seen_finish'. apply (IH x y). exact He.
    Qed.

    Lemma dfs_path_seen root st0 st p g z :
      already_seen st0 root = true ->
      dfs_fold_state root st0 st p g -> In z p -> already_seen st z = true.
    Proof.
      intros Hroot H. revert z.
      induction H as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros z Hz.
      - destruct Hz as [<- | []]. exact Hroot.
      - destruct Hz as [<- | Hz].
        + apply already_seen_tree_edge_upd_self.
        + apply already_seen_tree_edge_upd. apply IH. exact Hz.
      - rewrite already_seen_untree_edge_upd. apply IH. exact Hz.
      - rewrite already_seen_finish'. apply IH. right. exact Hz.
    Qed.

    Lemma dfs_path_unseen root st0 st p g z :
      dfs_fold_state root st0 st p g -> In z p -> z = root \/ already_seen st0 z = false.
    Proof.
      intro H. revert z.
      induction H as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros z Hz.
      - destruct Hz as [<- | []]. left. reflexivity.
      - destruct Hz as [<- | Hz].
        + right. destruct (already_seen st0 v) eqn:E; [ | reflexivity ].
          pose proof (already_seen_mono _ _ _ _ _ _ Hrec E) as Hc. congruence.
        + apply IH. exact Hz.
      - apply IH. exact Hz.
      - apply IH. right. exact Hz.
    Qed.

    Lemma dfs_source_seen root st0 st p g x y :
      already_seen st0 root = true ->
      dfs_fold_state root st0 st p g -> graph_edge g x y -> already_seen st x = true.
    Proof.
      intros Hroot H. revert x y.
      induction H as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. destruct He.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxhd _]].
        + apply already_seen_tree_edge_upd. apply (IH x y). exact Hold.
        + subst x. apply already_seen_tree_edge_upd.
          apply (dfs_path_seen _ _ _ _ _ _ Hroot Hrec). apply in_eq.
      - rewrite graph.edges_put in He. rewrite already_seen_untree_edge_upd.
        destruct He as [Hold | [Hxhd _]].
        + apply (IH x y). exact Hold.
        + subst x.
          apply (dfs_path_seen _ _ _ _ _ _ Hroot Hrec). apply in_eq.
      - rewrite already_seen_finish'. apply (IH x y). exact He.
    Qed.

    Lemma dfs_source_init root st0 st p g x y :
      dfs_fold_state root st0 st p g -> graph_edge g x y ->
      x = root \/ already_seen st0 x = false.
    Proof.
      intro H. revert x y.
      induction H as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                       | st2 u0 p0 g0 v Hrec IH Hne Hseen
                       | st2 u2 p0 g0 Hrec IH ]; intros x y He; cbv [graph_edge] in He.
      - rewrite graph.edges_empty in He. destruct He.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxu0 _]].
        + apply (IH x y). exact Hold.
        + subst x. apply (dfs_path_unseen _ _ _ _ _ _ Hrec). apply in_eq.
      - rewrite graph.edges_put in He. destruct He as [Hold | [Hxu0 _]].
        + apply (IH x y). exact Hold.
        + subst x. apply (dfs_path_unseen _ _ _ _ _ _ Hrec). apply in_eq.
      - apply (IH x y). exact He.
    Qed.

    Lemma dfs_fold_state_trans root st0 st st' p p' g g' u :
      dfs_fold_state root st0 st (u :: p) g ->
      already_seen st0 root = true ->
      graph.edges g u = [] ->
      dfs_fold_state u st st' p' g' ->
      dfs_fold_state root st0 st' (p' ++ p) (graph.union g g').
    Proof.
      intros H1 Hroot Hedges H2.
      induction H2 as [ | st2 u0 p0 g0 v Hne Hrec IH Hseen
                        | st2 u0 p0 g0 v Hrec IH Hne Hseen
                        | st2 u2 p0 g0 Hrec IH ].
      - cbn [app]. rewrite graph.union_empty_r. exact H1.
      - cbn [app]. rewrite graph.union_put_r. apply dfs_tree_edge.
        + intro Hedge. apply graph_edge_union in Hedge. destruct Hedge as [Hg | Hg0].
          * pose proof (dfs_target_seen _ _ _ _ _ _ _ H1 Hg) as Hs.
            pose proof (already_seen_mono _ _ _ _ _ _ Hrec Hs) as Hs2.
            congruence.
          * exact (Hne Hg0).
        + exact IH.
        + exact Hseen.
      - cbn [app]. rewrite graph.union_put_r. apply dfs_untree_edge.
        + exact IH.
        + intro Hedge. apply graph_edge_union in Hedge. destruct Hedge as [Hg | Hg0].
          * pose proof (dfs_path_unseen _ _ _ _ _ _ Hrec (in_eq u0 p0)) as Hun.
            destruct Hun as [-> | Hun].
            -- cbv [graph_edge] in Hg. rewrite Hedges in Hg. destruct Hg.
            -- pose proof (dfs_source_seen _ _ _ _ _ _ _ Hroot H1 Hg) as Hsn. congruence.
          * exact (Hne Hg0).
        + exact Hseen.
      - cbn [app] in IH. eapply dfs_finish. exact IH.
    Qed.

  End fold.

  (* The visited-set (fst) evolves independently of the state payload and ops. *)
  Lemma dfs_fold'_fst {S1 S2}
    (u1 t1 f1 : S1 -> list V -> V -> S1) (u2 t2 f2 : S2 -> list V -> V -> S2) g m :
    forall (st1 : list V * S1) (st2 : list V * S2) w,
      fst st1 = fst st2 ->
      fst (dfs_fold' u1 t1 f1 g m st1 w) = fst (dfs_fold' u2 t2 f2 g m st2 w).
  Proof.
    induction m as [|m' IH]; intros st1 st2 w Hfst;
      destruct st1 as [vs1 s1], st2 as [vs2 s2]; cbn [fst] in Hfst; subst vs2;
      cbn [dfs_fold' already_seen].
    - destruct (set_contains vs1 w); reflexivity.
    - destruct (set_contains vs1 w); [reflexivity|].
      assert (Hfold : fst (fold_left (dfs_fold' u1 t1 f1 g m') (graph.edges g w)
                            (tree_edge_upd' t1 (vs1, s1) w))
                    = fst (fold_left (dfs_fold' u2 t2 f2 g m') (graph.edges g w)
                            (tree_edge_upd' t2 (vs1, s2) w))).
      { apply (fold_left_invariant2 (fun _ a b => fst a = fst b)).
        - reflexivity.
        - intros a b c l' Hab. apply IH. exact Hab. }
      revert Hfold.
      destruct (fold_left (dfs_fold' u1 t1 f1 g m') (graph.edges g w)
                  (tree_edge_upd' t1 (vs1, s1) w)) as [vA sA].
      destruct (fold_left (dfs_fold' u2 t2 f2 g m') (graph.edges g w)
                  (tree_edge_upd' t2 (vs1, s2) w)) as [vB sB].
      cbn [finish' fst]. intro Hfold. exact Hfold.
  Qed.

  Lemma dfs_fold'_seen {St} (u t f : St -> list V -> V -> St) g n st' v :
    already_seen st' v = true -> dfs_fold' u t f g n st' v = untree_edge_upd' u st' v.
  Proof. destruct n; intro H; cbn [dfs_fold']; rewrite H; reflexivity. Qed.

  Lemma dfs_fold'_S {St} (u t f : St -> list V -> V -> St) g n st' v :
    dfs_fold' u t f g (S n) st' v
    = if already_seen st' v then untree_edge_upd' u st' v
      else finish' f (fold_left (dfs_fold' u t f g n) (graph.edges g v) (tree_edge_upd' t st' v)) v.
  Proof. reflexivity. Qed.

  Definition tree_edge_accumulate (path_g: list V * graph) (_ : list V) (cur : V) :=
    let '(path, g) := path_g in
    (cur :: path,
      match path with
      | [] => g
      | prev :: _ => graph.put g prev cur
      end).

  Definition untree_edge_accumulate (path_g: list V * graph) (_ : list V) (cur : V) :=
    let '(path, g) := path_g in
    (path,
      match path with
      | [] => g
      | prev :: _ => graph.put g prev cur
      end).

  Definition finish_accumulate (path_g : list V * graph) (_ : list V) (_ : V) :=
    let '(path, g) := path_g in
    (tl path, g).

  Definition graph_accumulator := dfs_fold' untree_edge_accumulate tree_edge_accumulate finish_accumulate.

  Lemma accum_path_inv g n vs path G w :
    fst (snd (graph_accumulator g n (vs, (path, G)) w)) = path.
  Proof.
    revert vs path G w. unfold graph_accumulator.
    induction n as [|n' IH]; intros vs path G w; cbn [dfs_fold'].
    - destruct (already_seen (vs, (path, G)) w);
        cbn [untree_edge_upd' untree_edge_accumulate fst snd]; destruct path; reflexivity.
    - destruct (already_seen (vs, (path, G)) w).
      + cbn [untree_edge_upd' untree_edge_accumulate fst snd]; destruct path; reflexivity.
      + match goal with
        | |- context[fold_left ?f ?l ?i] =>
          assert (Hfold : fst (snd (fold_left f l i)) = w :: path);
          [ apply (fold_left_invariant (fun _ s => fst (snd s) = w :: path));
            [ cbn [tree_edge_upd' tree_edge_accumulate fst snd]; destruct path; reflexivity
            | intros s' c l' Hs'; destruct s' as [vs' [path' G']];
              cbn [fst snd] in Hs'; subst path'; apply IH ]
          | ] end.
        revert Hfold.
        match goal with
        | |- _ -> fst (snd (finish' _ ?X _)) = _ => destruct X as [vsf [pathf Gf]]
        end.
        cbn [finish' finish_accumulate fst snd]. intros ->. reflexivity.
  Qed.

  Definition gframe (gacc : graph) (s : list V * (list V * graph)) :=
    (fst s, (fst (snd s), graph.union gacc (snd (snd s)))).

  Lemma accum_frame g n : forall gacc s w,
    graph_accumulator g n (gframe gacc s) w = gframe gacc (graph_accumulator g n s w).
  Proof.
    unfold graph_accumulator.
    induction n as [|n' IH]; intros gacc s w; destruct s as [vs [path X]];
      assert (Hgf : gframe gacc (vs, (path, X)) = (vs, (path, graph.union gacc X))) by reflexivity;
      rewrite Hgf; cbn [dfs_fold' already_seen].
    - destruct (set_contains vs w).
      + cbn [untree_edge_upd' untree_edge_accumulate]. unfold gframe.
        destruct path; cbn [fst snd];
          [reflexivity | rewrite graph.union_put_r; reflexivity].
      + unfold gframe. cbn [fst snd]. reflexivity.
    - destruct (set_contains vs w).
      + cbn [untree_edge_upd' untree_edge_accumulate]. unfold gframe.
        destruct path; cbn [fst snd];
          [reflexivity | rewrite graph.union_put_r; reflexivity].
      + assert (Htree : tree_edge_upd' tree_edge_accumulate (vs, (path, graph.union gacc X)) w
                      = gframe gacc (tree_edge_upd' tree_edge_accumulate (vs, (path, X)) w)).
        { unfold gframe. destruct path; cbn [tree_edge_upd' tree_edge_accumulate fst snd];
            [reflexivity | rewrite graph.union_put_r; reflexivity]. }
        assert (Hfin : forall s0, finish' finish_accumulate (gframe gacc s0) w
                                = gframe gacc (finish' finish_accumulate s0 w)).
        { intro s0. destruct s0 as [vs0 [p0 G0]]. unfold gframe.
          cbn [finish' finish_accumulate fst snd]. reflexivity. }
        rewrite Htree, (fold_left_hom _ (gframe gacc) _ (fun a b => IH gacc a b)).
        apply Hfin.
  Qed.

  Lemma graph_accumulator_union g n vs p g0 root :
    let '(vs'', (p'', g'')) := graph_accumulator g n (vs, (p, g0)) root in
    let '(vs', (p', g')) := graph_accumulator g n (vs, (p, graph.empty)) root in
    vs'' = vs' /\ p'' = p' /\ g'' = graph.union g0 g'.
  Proof.
    assert (Hgf : gframe g0 (vs, (p, graph.empty)) = (vs, (p, g0))).
    { unfold gframe. cbn [fst snd]. rewrite graph.union_empty_r. reflexivity. }
    pose proof (accum_frame g n g0 (vs, (p, graph.empty)) root) as H.
    rewrite Hgf in H.
    destruct (graph_accumulator g n (vs, (p, g0)) root) as [vs'' [p'' g'']].
    destruct (graph_accumulator g n (vs, (p, graph.empty)) root) as [vs' [p' g']].
    unfold gframe in H. cbn [fst snd] in H. injection H as -> -> ->. auto.
  Qed.

  Definition pbot (suffix : list V) (s : list V * (list V * graph)) :=
    (fst s, (fst (snd s) ++ suffix, snd (snd s))).

  Lemma accum_bottom g n : forall vs prefix suffix G c,
    prefix <> [] ->
    graph_accumulator g n (vs, (prefix ++ suffix, G)) c
    = pbot suffix (graph_accumulator g n (vs, (prefix, G)) c).
  Proof.
    assert (Hfin : forall suffix X c,
      fst (snd X) <> [] ->
      finish' finish_accumulate (pbot suffix X) c = pbot suffix (finish' finish_accumulate X c)).
    { intros sfx X c HX. destruct X as [vsX [pX GX]]. cbn [pbot fst snd] in *.
      destruct pX; [congruence|].
      cbn [finish' finish_accumulate app fst snd]. reflexivity. }
    unfold graph_accumulator.
    induction n as [|n' IH]; intros vs prefix suffix G c Hne;
      destruct prefix as [|a rest]; try congruence;
      cbn [dfs_fold' already_seen]; destruct (set_contains vs c).
    - cbn [untree_edge_upd' untree_edge_accumulate pbot fst snd app]. reflexivity.
    - cbn [pbot fst snd app]. reflexivity.
    - cbn [untree_edge_upd' untree_edge_accumulate pbot fst snd app]. reflexivity.
    - cbn [tree_edge_upd' tree_edge_accumulate app].
      match goal with
      | |- finish' _ (fold_left ?f ?l ?i1) _ = pbot _ (finish' _ (fold_left _ _ ?i2) _) =>
        assert (Hfold : fold_left f l i1 = pbot suffix (fold_left f l i2)
                        /\ fst (snd (fold_left f l i2)) <> [])
      end.
      { apply (fold_left_invariant2 (fun _ s1 s2 => s1 = pbot suffix s2 /\ fst (snd s2) <> [])).
        - cbn [pbot fst snd app]. split; [reflexivity | discriminate].
        - intros s1 s2 c' l' [-> Hne2]. destruct s2 as [vs2 [p2 G2]].
          cbn [pbot fst snd] in Hne2 |- *. split.
          + apply (IH vs2 p2 suffix G2 c' Hne2).
          + pose proof (accum_path_inv g n' vs2 p2 G2 c') as Hp.
            unfold graph_accumulator in Hp. rewrite Hp. exact Hne2. }
      destruct Hfold as [Hfold Hne2]. rewrite Hfold. apply Hfin. exact Hne2.
  Qed.

  Lemma accum_fold_frame g m gacc L s :
    fold_left (graph_accumulator g m) L (gframe gacc s)
    = gframe gacc (fold_left (graph_accumulator g m) L s).
  Proof. apply fold_left_hom. intros a b. apply accum_frame. Qed.

  Lemma accum_fold_bottom g m suffix L s :
    fst (snd s) <> [] ->
    fold_left (graph_accumulator g m) L (pbot suffix s)
    = pbot suffix (fold_left (graph_accumulator g m) L s).
  Proof.
    intro Hs.
    enough (H : fold_left (graph_accumulator g m) L (pbot suffix s)
                = pbot suffix (fold_left (graph_accumulator g m) L s)
                /\ fst (snd (fold_left (graph_accumulator g m) L s)) <> []) by apply H.
    apply (fold_left_invariant2 (fun _ s1 s2 => s1 = pbot suffix s2 /\ fst (snd s2) <> [])).
    - split; [reflexivity | exact Hs].
    - intros s1 s2 c l' [-> Hne2]. destruct s2 as [vs2 [p2 G2]].
      cbn [pbot fst snd] in Hne2 |- *. split.
      + apply accum_bottom. exact Hne2.
      + pose proof (accum_path_inv g m vs2 p2 G2 c) as Hp. rewrite Hp. exact Hne2.
  Qed.

  Lemma graph_accumulator_S g m vs path G w :
    graph_accumulator g (S m) (vs, (path, G)) w
    = if set_contains vs w
      then untree_edge_upd' untree_edge_accumulate (vs, (path, G)) w
      else finish' finish_accumulate (fold_left (graph_accumulator g m) (graph.edges g w)
             (tree_edge_upd' tree_edge_accumulate (vs, (path, G)) w)) w.
  Proof. reflexivity. Qed.

  Lemma accum_step g m vs g_acc root w :
    set_contains vs w = false ->
    snd (snd (graph_accumulator g (S m) (vs, ([root], g_acc)) w))
    = graph.union (graph.put g_acc root w)
                  (snd (snd (graph_accumulator g (S m) (vs, ([], graph.empty)) w))).
  Proof.
    intro Hw.
    assert (Hfinsnd : forall X, snd (snd (finish' finish_accumulate X w)) = snd (snd X)).
    { intro X. destruct X as [vsX [pX GX]]. reflexivity. }
    rewrite !graph_accumulator_S, Hw.
    cbn [tree_edge_upd' tree_edge_accumulate].
    rewrite !Hfinsnd.
    replace (w :: vs, ([w; root], graph.put g_acc root w))
      with (gframe (graph.put g_acc root w) (pbot [root] (w :: vs, ([w], graph.empty)))).
    2:{ unfold gframe, pbot. cbn [fst snd app]. rewrite graph.union_empty_r. reflexivity. }
    rewrite accum_fold_frame, accum_fold_bottom by discriminate.
    unfold gframe, pbot. cbn [fst snd]. reflexivity.
  Qed.

  Lemma last_cons (l : list V) a d :
    last (a :: l) d = last l a.
  Proof.
    revert a d. induction l as [|b l' IH]; intros a d; [reflexivity|].
    change (last (b :: l') d = last (b :: l') a).
    rewrite (IH b d), (IH b a). reflexivity.
  Qed.

  Lemma set_contains_iff_In vs v :
    set_contains vs v = true <-> In v vs.
  Proof.
    unfold set_contains. symmetry.
    apply (existsb_eqb_in (aeqb_dec := @eqb_boolspec V eqbV eqb_ok)).
  Qed.

  Definition reaches g vs s u :=
    exists p, path_to (graph_edge g) s p u /\ Forall (fun w => ~ In w vs) (s :: p).

  Lemma reaches_mono g vs1 vs2 s u :
    incl vs1 vs2 -> reaches g vs2 s u -> reaches g vs1 s u.
  Proof.
    intros Hincl [p [Hpath Hall]]. exists p. split; [exact Hpath|].
    eapply Forall_impl; [|exact Hall]. cbn beta.
    intros x Hx2 Hx1. apply Hx2, Hincl, Hx1.
  Qed.

  Lemma reaches_refl g vs w :
    ~ In w vs -> reaches g vs w w.
  Proof.
    intro Hw. exists []. split.
    - unfold path_to. cbn [path last]. split; [exact I | reflexivity].
    - constructor; [exact Hw | constructor].
  Qed.

  Lemma reaches_cons g vs w c u :
    ~ In w vs -> graph_edge g w c -> reaches g vs c u -> reaches g vs w u.
  Proof.
    intros Hw Hedge [p [[Hpath Hlast] Hall]]. exists (c :: p). split.
    - unfold path_to. cbn [path]. split.
      + split; [exact Hedge | exact Hpath].
      + rewrite last_cons. exact Hlast.
    - constructor; [exact Hw | exact Hall].
  Qed.

  Definition restriction root vs g g' :=
    forall u v, graph_edge g' u v <-> graph_edge g u v /\ reaches g vs root u.

  Lemma accum_visited_mono g n : forall s w a,
    In a (fst s) -> In a (fst (graph_accumulator g n s w)).
  Proof.
    unfold graph_accumulator.
    induction n as [|m IH]; intros [vs [path G]] w a Ha; cbn [fst] in Ha;
      cbn [dfs_fold' already_seen].
    - destruct (set_contains vs w);
        [cbn [untree_edge_upd' untree_edge_accumulate fst] | cbn [fst]]; exact Ha.
    - destruct (set_contains vs w).
      + cbn [untree_edge_upd' untree_edge_accumulate fst]. exact Ha.
      + assert (HY : In a (fst (fold_left
          (dfs_fold' untree_edge_accumulate tree_edge_accumulate finish_accumulate g m)
          (graph.edges g w) (tree_edge_upd' tree_edge_accumulate (vs, (path, G)) w)))).
        { apply (fold_left_invariant (fun _ st => In a (fst st))).
          - cbn [tree_edge_upd' tree_edge_accumulate fst]. right. exact Ha.
          - intros st c l' Hst. apply IH. exact Hst. }
        revert HY.
        match goal with |- In a (fst ?X) -> In a (fst (finish' _ ?X _)) =>
          destruct X as [vsY sY] end.
        cbn [finish' fst]. exact (fun h => h).
  Qed.

  Lemma accum_graph_mono g n : forall s w a b,
    graph_edge (snd (snd s)) a b ->
    graph_edge (snd (snd (graph_accumulator g n s w))) a b.
  Proof.
    unfold graph_accumulator.
    induction n as [|m IH]; intros [vs [path G]] w a b Hab; cbn [snd] in Hab;
      cbn [dfs_fold' already_seen].
    - destruct (set_contains vs w).
      + cbn [untree_edge_upd' untree_edge_accumulate snd]. destruct path as [|prev pr];
          [exact Hab | cbv [graph_edge] in *; rewrite graph.edges_put; left; exact Hab].
      + cbn [snd]. exact Hab.
    - destruct (set_contains vs w).
      + cbn [untree_edge_upd' untree_edge_accumulate snd]. destruct path as [|prev pr];
          [exact Hab | cbv [graph_edge] in *; rewrite graph.edges_put; left; exact Hab].
      + assert (HGF : graph_edge (snd (snd (fold_left
            (dfs_fold' untree_edge_accumulate tree_edge_accumulate finish_accumulate g m)
            (graph.edges g w) (tree_edge_upd' tree_edge_accumulate (vs, (path, G)) w)))) a b).
        { apply (fold_left_invariant (fun _ st => graph_edge (snd (snd st)) a b)).
          - cbn [tree_edge_upd' tree_edge_accumulate snd]. destruct path as [|prev pr];
              [exact Hab | cbv [graph_edge] in *; rewrite graph.edges_put; left; exact Hab].
          - intros st c l' Hst. apply IH. exact Hst. }
        revert HGF.
        match goal with |- graph_edge (snd (snd ?X)) a b ->
                           graph_edge (snd (snd (finish' _ ?X _))) a b =>
          destruct X as [vsX [pX GX]] end.
        cbn [finish' finish_accumulate snd]. exact (fun h => h).
  Qed.

  Lemma accum_seen g n vs path G w :
    set_contains vs w = true ->
    graph_accumulator g n (vs, (path, G)) w
    = (vs, (path, match path with [] => G | prev :: _ => graph.put G prev w end)).
  Proof.
    intro Hw. destruct n; unfold graph_accumulator; cbn [dfs_fold' already_seen]; rewrite Hw;
      cbn [untree_edge_upd' untree_edge_accumulate]; reflexivity.
  Qed.

  Lemma accum_spec g n : forall vs path G w,
    (forall p u, path_to (graph_edge g) w p u ->
       Forall (fun x => ~ In x vs) (w :: p) -> length p < n) ->
    (forall a, In a (fst (graph_accumulator g n (vs, (path, G)) w)) ->
       In a vs \/ reaches g vs w a) /\
    (forall a b, graph_edge (snd (snd (graph_accumulator g n (vs, (path, G)) w))) a b ->
       graph_edge G a b \/
       (exists p0 pr, path = p0 :: pr /\ a = p0 /\ b = w) \/
       (graph_edge g a b /\ reaches g vs w a)) /\
    (forall x y, In x (fst (graph_accumulator g n (vs, (path, G)) w)) -> ~ In x vs ->
       graph_edge g x y -> In y (fst (graph_accumulator g n (vs, (path, G)) w))) /\
    (forall x b, In x (fst (graph_accumulator g n (vs, (path, G)) w)) -> ~ In x vs ->
       graph_edge g x b ->
       graph_edge (snd (snd (graph_accumulator g n (vs, (path, G)) w))) x b) /\
    In w (fst (graph_accumulator g n (vs, (path, G)) w)) /\
    (forall p0 pr, path = p0 :: pr ->
       graph_edge (snd (snd (graph_accumulator g n (vs, (path, G)) w))) p0 w).
  Proof.
    induction n as [|m IH]; intros vs path G w Hfuel.
    - (* n = 0 *)
      destruct (set_contains vs w) eqn:Hw.
      + (* seen *)
        rewrite (accum_seen g 0 vs path G w Hw). cbn [fst snd].
        assert (Hwin : In w vs) by (apply set_contains_iff_In; exact Hw).
        split; [|split; [|split; [|split; [|split]]]].
        * intros a Ha; left; exact Ha.
        * intros a b Hab. destruct path as [|prev pr]; [left; exact Hab|].
          cbv [graph_edge] in Hab; rewrite graph.edges_put in Hab.
          destruct Hab as [H|[Hpa Hwb]]; [left; exact H|].
          right; left; exists prev, pr. split; [reflexivity|].
          split; [symmetry; exact Hpa | symmetry; exact Hwb].
        * intros x y Hx Hnx He; exfalso; auto.
        * intros x b Hx Hnx He; exfalso; auto.
        * exact Hwin.
        * intros p0 pr Hpath. destruct path as [|prev pr']; [discriminate Hpath|].
          injection Hpath as -> ->. cbv [graph_edge].
          rewrite graph.edges_put. right; auto.
      + (* unseen, no fuel: vacuous *)
        exfalso.
        assert (Hwni : ~ In w vs).
        { intro Hin. apply set_contains_iff_In in Hin. rewrite Hw in Hin. discriminate. }
        specialize (Hfuel [] w).
        assert (Hpt : path_to (graph_edge g) w [] w)
          by (unfold path_to; split; [exact I|reflexivity]).
        assert (Hfa : Forall (fun x => ~ In x vs) [w])
          by (constructor; [exact Hwni | constructor]).
        specialize (Hfuel Hpt Hfa). cbn [length] in Hfuel. lia.
    - (* n = S m *)
      destruct (set_contains vs w) eqn:Hw.
      + (* seen *)
        rewrite (accum_seen g (S m) vs path G w Hw). cbn [fst snd].
        assert (Hwin : In w vs) by (apply set_contains_iff_In; exact Hw).
        split; [|split; [|split; [|split; [|split]]]].
        * intros a Ha; left; exact Ha.
        * intros a b Hab. destruct path as [|prev pr]; [left; exact Hab|].
          cbv [graph_edge] in Hab; rewrite graph.edges_put in Hab.
          destruct Hab as [H|[Hpa Hwb]]; [left; exact H|].
          right; left; exists prev, pr. split; [reflexivity|].
          split; [symmetry; exact Hpa | symmetry; exact Hwb].
        * intros x y Hx Hnx He; exfalso; auto.
        * intros x b Hx Hnx He; exfalso; auto.
        * exact Hwin.
        * intros p0 pr Hpath. destruct path as [|prev pr']; [discriminate Hpath|].
          injection Hpath as -> ->. cbv [graph_edge].
          rewrite graph.edges_put. right; auto.
      + (* unseen: explore *)
        assert (Hwni : ~ In w vs).
        { intro Hin. apply set_contains_iff_In in Hin. rewrite Hw in Hin. discriminate. }
        pose (G1 := match path with [] => G | prev :: _ => graph.put G prev w end).
        assert (HeqR : graph_accumulator g (S m) (vs, (path, G)) w
          = finish' finish_accumulate
              (fold_left (graph_accumulator g m) (graph.edges g w)
                 (w :: vs, (w :: path, G1))) w).
        { unfold G1. rewrite graph_accumulator_S, Hw.
          cbn [tree_edge_upd' tree_edge_accumulate]. reflexivity. }
        rewrite HeqR.
        remember (fold_left (graph_accumulator g m) (graph.edges g w)
                    (w :: vs, (w :: path, G1))) as FL eqn:EFL.
        pose (P := fun (rem : list V) (st : list V * (list V * graph)) =>
          let '(Vs, (pth, GG)) := st in
          pth = w :: path /\
          incl vs Vs /\
          incl rem (graph.edges g w) /\
          In w Vs /\
          (forall a, In a Vs -> In a vs \/ reaches g vs w a) /\
          (forall x y, In x Vs -> ~ In x vs -> graph_edge g x y ->
             In y Vs \/ (x = w /\ In y rem)) /\
          (forall a b, graph_edge GG a b ->
             graph_edge G1 a b \/ (graph_edge g a b /\ reaches g vs w a)) /\
          (forall x b, In x Vs -> ~ In x vs -> graph_edge g x b ->
             graph_edge GG x b \/ (x = w /\ In b rem))).
        assert (HP : P [] FL).
        { rewrite EFL. apply (fold_left_invariant P).
          - (* base *)
            subst P; cbn beta.
            split; [reflexivity|].
            split; [intros a Ha; right; exact Ha|].
            split; [apply incl_refl|].
            split; [left; reflexivity|].
            split; [intros a [<-|Ha]; [right; apply reaches_refl; exact Hwni | left; exact Ha]|].
            split.
            + intros x y Hx Hnx He. destruct Hx as [<-|Hx]; [|exfalso; auto].
              right. split; [reflexivity|]. exact He.
            + split; [intros a b Hab; left; exact Hab|].
              intros x b Hx Hnx He. destruct Hx as [<-|Hx]; [|exfalso; auto].
              right. split; [reflexivity|]. exact He.
          - (* step *)
            intros st c l' HPst. subst P; cbn beta in HPst |- *.
            destruct st as [Vs [pth GG]].
            destruct HPst as (Hpth & HinclV & Hinclrem & HwV & HVs & Hclose & HEs & Hexp).
            subst pth.
            assert (Hgwc : graph_edge g w c) by (apply Hinclrem; left; reflexivity).
            assert (Hsubfuel : forall q u, path_to (graph_edge g) c q u ->
                      Forall (fun x => ~ In x Vs) (c :: q) -> length q < m).
            { intros q u [Hpath Hlast] Hall.
              assert (Hpt' : path_to (graph_edge g) w (c :: q) u).
              { unfold path_to. split.
                - split; [exact Hgwc | exact Hpath].
                - rewrite last_cons. exact Hlast. }
              assert (Hall' : Forall (fun x => ~ In x vs) (w :: c :: q)).
              { constructor; [exact Hwni|].
                eapply Forall_impl; [|exact Hall]. cbn beta.
                intros x Hx Hxvs. apply Hx; apply HinclV; exact Hxvs. }
              pose proof (Hfuel (c :: q) u Hpt' Hall') as Hlen. cbn [length] in Hlen. lia. }
            pose proof (IH Vs (w :: path) GG c Hsubfuel) as IHc.
            destruct (graph_accumulator g m (Vs, (w :: path, GG)) c)
              as [Vc [pthc Gc]] eqn:ESUB.
            assert (HmonoV : forall a, In a Vs -> In a Vc).
            { intros a Ha. pose proof (accum_visited_mono g m (Vs, (w :: path, GG)) c a Ha) as Hm.
              rewrite ESUB in Hm. cbn [fst] in Hm. exact Hm. }
            assert (HmonoG : forall a b, graph_edge GG a b -> graph_edge Gc a b).
            { intros a b Hab. pose proof (accum_graph_mono g m (Vs, (w :: path, GG)) c a b Hab) as Hm.
              rewrite ESUB in Hm. cbn [snd] in Hm. exact Hm. }
            cbn [fst snd] in IHc.
            destruct IHc as (iA & iB & iC & iD & iE & iF).
            assert (Hpthc : pthc = w :: path).
            { pose proof (accum_path_inv g m Vs (w :: path) GG c) as Hp.
              rewrite ESUB in Hp. cbn [fst snd] in Hp. exact Hp. }
            subst pthc. cbn beta.
            split; [reflexivity|].
            split; [intros a Ha; apply HmonoV; apply HinclV; exact Ha|].
            split; [intros a Ha; apply Hinclrem; right; exact Ha|].
            split; [apply HmonoV; exact HwV|].
            split.
            + (* I-Vsound *)
              intros a Ha. destruct (iA a Ha) as [HaV | Hreach].
              * apply HVs; exact HaV.
              * right. exact (reaches_cons g vs w c a Hwni Hgwc
                                (reaches_mono g vs Vs c a HinclV Hreach)).
            + split.
              * (* I-close' *)
                intros x y Hx Hnx He. destruct (set_contains Vs x) eqn:HxV.
                -- apply set_contains_iff_In in HxV.
                   destruct (Hclose x y HxV Hnx He) as [HyV | [Hxw Hyrem]].
                   ++ left. apply HmonoV; exact HyV.
                   ++ cbn [In] in Hyrem. destruct Hyrem as [Hyc | Hyl'].
                      ** left. subst y. exact iE.
                      ** right. split; [exact Hxw | exact Hyl'].
                -- assert (HxnV : ~ In x Vs)
                     by (intro Hin; apply set_contains_iff_In in Hin; congruence).
                   left. exact (iC x y Hx HxnV He).
              * split.
                -- (* I-Esound *)
                   intros a b Hab. destruct (iB a b Hab) as [HGG | [Hmid | Hreach]].
                   ++ destruct (HEs a b HGG) as [HG1 | Hrr]; [left; exact HG1 | right; exact Hrr].
                   ++ destruct Hmid as [p0 [pr [Heq [Ha Hb]]]].
                      injection Heq as Hp0 Hpr. subst p0. subst a. subst b.
                      right. split; [exact Hgwc | apply reaches_refl; exact Hwni].
                   ++ destruct Hreach as [Hreal HrV]. right. split; [exact Hreal|].
                      exact (reaches_cons g vs w c a Hwni Hgwc
                               (reaches_mono g vs Vs c a HinclV HrV)).
                -- (* I-explored' *)
                   intros x b Hx Hnx He. destruct (set_contains Vs x) eqn:HxV.
                   ++ apply set_contains_iff_In in HxV.
                      destruct (Hexp x b HxV Hnx He) as [HGGxb | [Hxw Hbrem]].
                      ** left. apply HmonoG; exact HGGxb.
                      ** cbn [In] in Hbrem. destruct Hbrem as [Hbc | Hbl'].
                         --- left. subst b. subst x. exact (iF w path eq_refl).
                         --- right. split; [exact Hxw | exact Hbl'].
                   ++ assert (HxnV : ~ In x Vs)
                        by (intro Hin; apply set_contains_iff_In in Hin; congruence).
                      left. exact (iD x b Hx HxnV He). }
        assert (Hmono : forall a b, graph_edge G1 a b -> graph_edge (snd (snd FL)) a b).
        { intros a b Hab. rewrite EFL.
          apply (fold_left_invariant (fun _ st => graph_edge (snd (snd st)) a b)).
          - cbn [snd]. exact Hab.
          - intros st c l' Hst. apply accum_graph_mono. exact Hst. }
        clear EFL. subst P. destruct FL as [VF [pthF GF]]. cbn beta in HP.
        destruct HP as (_ & _ & _ & HwVF & HVsF & HcloseF & HEsF & HexpF).
        cbn [snd] in Hmono. cbn [finish' finish_accumulate fst snd].
        split; [|split; [|split; [|split; [|split]]]].
        * intros a Ha. apply HVsF; exact Ha.
        * intros a b Hab. destruct (HEsF a b Hab) as [HG1 | Hrr].
          -- unfold G1 in HG1. destruct path as [|prev pr]; [left; exact HG1|].
             cbv [graph_edge] in HG1. rewrite graph.edges_put in HG1.
             destruct HG1 as [H | [Hpa Hwb]]; [left; exact H|].
             right; left. exists prev, pr. split; [reflexivity|].
             split; [symmetry; exact Hpa | symmetry; exact Hwb].
          -- right; right. exact Hrr.
        * intros x y Hx Hnx He.
          destruct (HcloseF x y Hx Hnx He) as [HyVF | [_ Hf]]; [exact HyVF | destruct Hf].
        * intros x b Hx Hnx He.
          destruct (HexpF x b Hx Hnx He) as [HGF | [_ Hf]]; [exact HGF | destruct Hf].
        * exact HwVF.
        * intros p0 pr Hpath. apply Hmono. unfold G1.
          destruct path as [|prev pr']; [discriminate Hpath|].
          injection Hpath as -> ->. cbv [graph_edge].
          rewrite graph.edges_put. right; auto.
  Qed.

  Lemma reaches_unseen g vs s u :
    reaches g vs s u -> ~ In u vs.
  Proof.
    intros [p [[Hpath Hlast] Hall]] Hin. subst u.
    rewrite Forall_forall in Hall.
    assert (Hlp : In (last p s) (s :: p)).
    { destruct p as [|a p']; [left; reflexivity | right; apply In_last; discriminate]. }
    exact (Hall (last p s) Hlp Hin).
  Qed.

  Lemma reaches_visited g vs s a vs' :
    In s vs' ->
    (forall x y, In x vs' -> ~ In x vs -> graph_edge g x y -> In y vs') ->
    reaches g vs s a -> In a vs'.
  Proof.
    intros Hs Hclose [p [Hpt Hall]]. revert s Hs Hpt Hall.
    induction p as [|c p' IH]; intros s Hs [Hpath Hlast] Hall.
    - cbn [last] in Hlast. subst a. exact Hs.
    - cbn [path] in Hpath. destruct Hpath as [Hedge Hpathc].
      pose proof (Forall_inv Hall) as Hs_nvs.
      pose proof (Forall_inv_tail Hall) as Hall'.
      assert (Hcvs' : In c vs') by exact (Hclose s c Hs Hs_nvs Hedge).
      apply (IH c Hcvs').
      + split; [exact Hpathc | rewrite last_cons in Hlast; exact Hlast].
      + exact Hall'.
  Qed.

  Lemma accum_restriction g n vs root :
    set_contains vs root = false ->
    (forall p v, path_to (graph_edge g) root p v ->
       Forall (fun w => ~ In w vs) (root :: p) -> length p < n) ->
    restriction root vs g (snd (snd (graph_accumulator g n (vs, ([], graph.empty)) root))).
  Proof.
    intros Hroot Hfuel.
    destruct (accum_spec g n vs [] graph.empty root Hfuel)
      as (_ & Bsound & Cclose & Dexp & Ewvis & _).
    intros u v. split.
    - intro Hedge'. destruct (Bsound u v Hedge') as [Hempty | [Hmid | Hgood]].
      + cbv [graph_edge] in Hempty. rewrite graph.edges_empty in Hempty. destruct Hempty.
      + destruct Hmid as [p0 [pr [Hcontra _]]]. discriminate Hcontra.
      + exact Hgood.
    - intros [Hedge Hreach].
      assert (Hunv : ~ In u vs) by exact (reaches_unseen g vs root u Hreach).
      assert (Huvis : In u (fst (graph_accumulator g n (vs, ([], graph.empty)) root)))
        by exact (reaches_visited g vs root u
                    (fst (graph_accumulator g n (vs, ([], graph.empty)) root))
                    Ewvis Cclose Hreach).
      exact (Dexp u v Huvis Hunv Hedge).
  Qed.

  Context {state}
    (untree_edge_upd : state -> list V -> V -> state)
    (tree_edge_upd : state -> list V -> V -> state)
    (finish : state -> list V -> V -> state).

  Local Notation dfs_fold'0 := (dfs_fold' untree_edge_upd tree_edge_upd finish).
  Local Notation edge_upd'0 := (edge_upd' untree_edge_upd tree_edge_upd).
  Local Notation dfs_fold_state0 := (dfs_fold_state untree_edge_upd tree_edge_upd finish).

  Lemma dfs_fold_sound1 root vs n st0 g :
    0 < n ->
    already_seen (vs, st0) root = false ->
    let '(_, (_, g_acc)) := graph_accumulator g n (vs, ([], graph.empty)) root in
    dfs_fold_state0 root
      (edge_upd'0 (vs, st0) root)
      (dfs_fold'0 g n (vs, st0) root)
      []
      g_acc.
  Proof.
    revert root vs st0. induction n as [|n' IH]; intros root vs st0 Hn Hroot; [lia|].
    cbn [already_seen] in Hroot.
    assert (Hedgeupd : edge_upd'0 (vs, st0) root = tree_edge_upd' tree_edge_upd (vs, st0) root).
    { unfold edge_upd'. cbn [already_seen]. rewrite Hroot. reflexivity. }
    assert (Habs : dfs_fold'0 g (S n') (vs, st0) root
      = finish' finish (fold_left (dfs_fold'0 g n') (graph.edges g root)
          (tree_edge_upd' tree_edge_upd (vs, st0) root)) root).
    { rewrite dfs_fold'_S. cbn [already_seen]. rewrite Hroot. reflexivity. }
    rewrite Hedgeupd, Habs.
    set (st_init := tree_edge_upd' tree_edge_upd (vs, st0) root) in *.
    rewrite graph_accumulator_S, Hroot. cbn [tree_edge_upd' tree_edge_accumulate].
    pose (P := fun (remaining : list V) (a : list V * state)
                   (b : list V * (list V * graph)) =>
      fst a = fst b /\ fst (snd b) = [root] /\
      dfs_fold_state0 root st_init a [root] (snd (snd b)) /\
      (forall x, In x remaining -> ~ graph_edge (snd (snd b)) root x) /\
      NoDup remaining /\ incl remaining (graph.edges g root)).
    assert (HP : P [] (fold_left (dfs_fold'0 g n') (graph.edges g root) st_init)
                      (fold_left (graph_accumulator g n') (graph.edges g root)
                         (root :: vs, ([root], graph.empty)))).
    { apply (fold_left_invariant2 P).
      - subst P; cbn beta. split; [|split; [|split; [|split; [|split]]]].
        + unfold st_init; cbn [tree_edge_upd' fst]; reflexivity.
        + reflexivity.
        + apply dfs_init.
        + intros x Hx. cbv [graph_edge]. cbn [snd]. rewrite graph.edges_empty. apply in_nil.
        + apply graph.edges_NoDup.
        + apply incl_refl.
      - intros a b w remaining' HP'. subst P; cbn beta in HP' |- *.
        destruct HP' as (Hfst & Hbpath & Hstate & Htrack & Hnodup & Hincl).
        destruct a as [vs_a s_a], b as [vs_b [p_b g_b]].
        cbn [fst snd] in Hfst, Hbpath, Hstate, Htrack |- *.
        subst vs_a p_b.
        assert (Hwni : ~ In w remaining') by (inversion Hnodup; auto).
        destruct (set_contains vs_b w) eqn:Hw.
        + (* seen: untree edge *)
          unfold graph_accumulator.
          rewrite (dfs_fold'_seen untree_edge_upd tree_edge_upd finish g n' (vs_b, s_a) w)
            by (cbn [already_seen]; exact Hw).
          rewrite (dfs_fold'_seen untree_edge_accumulate tree_edge_accumulate finish_accumulate
                     g n' (vs_b, ([root], g_b)) w) by (cbn [already_seen]; exact Hw).
          split; [|split; [|split; [|split; [|split]]]].
          * cbn [untree_edge_upd' untree_edge_accumulate fst]. reflexivity.
          * cbn [untree_edge_upd' untree_edge_accumulate fst snd]. reflexivity.
          * replace (snd (snd (untree_edge_upd' untree_edge_accumulate (vs_b, ([root], g_b)) w)))
              with (graph.put g_b root w) by reflexivity.
            apply dfs_untree_edge.
            -- exact Hstate.
            -- apply Htrack; apply in_eq.
            -- cbn [already_seen]; exact Hw.
          * cbn [untree_edge_upd' untree_edge_accumulate snd].
            intros x Hx Hedge. cbv [graph_edge] in Hedge.
            rewrite graph.edges_put in Hedge. destruct Hedge as [Hold | [_ Hxw]].
            -- apply (Htrack x); [right; exact Hx | exact Hold].
            -- subst x; contradiction.
          * inversion Hnodup; auto.
          * intros y Hy; apply Hincl; right; exact Hy.
        + (* unseen *)
          destruct n' as [|n''].
          * (* no fuel: no-op *)
            unfold graph_accumulator. cbn [dfs_fold' already_seen]. rewrite Hw.
            split; [reflexivity | split; [reflexivity | split; [exact Hstate | split; [|split]]]].
            -- intros x Hx. apply Htrack; right; exact Hx.
            -- inversion Hnodup; auto.
            -- intros y Hy; apply Hincl; right; exact Hy.
          * (* explored *)
            assert (Hrootseen : set_contains vs_b root = true).
            { pose proof (already_seen_mono _ _ _ root st_init (vs_b, s_a) [root] g_b root Hstate) as Hm.
              cbn [already_seen] in Hm. apply Hm.
              unfold st_init; apply already_seen_tree_edge_upd_self. }
            assert (Hrw : root <> w) by (intro; subst; congruence).
            (* the IH for child w *)
            pose proof (IH w vs_b s_a ltac:(lia) Hw) as Hchild.
            revert Hchild.
            destruct (graph_accumulator g (S n'') (vs_b, ([], graph.empty)) w)
              as [vsw [pw g_w]] eqn:Ew.
            cbn [snd].
            assert (Hedgew : edge_upd'0 (vs_b, s_a) w = tree_edge_upd' tree_edge_upd (vs_b, s_a) w).
            { unfold edge_upd'. cbn [already_seen]. rewrite Hw. reflexivity. }
            rewrite Hedgew. intro Hchild.
            (* the outer edges list is empty for w *)
            assert (Hedges : graph.edges (graph.put g_b root w) w = []).
            { destruct (graph.edges (graph.put g_b root w) w) as [|y ys] eqn:E; [reflexivity|].
              exfalso.
              assert (Hin : graph_edge (graph.put g_b root w) w y)
                by (cbv [graph_edge]; rewrite E; left; reflexivity).
              cbv [graph_edge] in Hin. rewrite graph.edges_put in Hin.
              destruct Hin as [Hin | [Hwr _]]; [| congruence].
              pose proof (dfs_source_seen _ _ _ root st_init (vs_b, s_a) [root] g_b w y
                ltac:(unfold st_init; apply already_seen_tree_edge_upd_self) Hstate) as Hss.
              cbv [graph_edge] in Hss. specialize (Hss Hin).
              cbn [already_seen] in Hss. congruence. }
            (* build the dfs_fold_state via tree edge + trans *)
            assert (Hne : ~ graph_edge g_b root w).
            { intro Hedge.
              pose proof (dfs_target_seen _ _ _ root st_init (vs_b, s_a) [root] g_b root w Hstate Hedge) as Ht.
              cbn [already_seen] in Ht. congruence. }
            assert (Htree : dfs_fold_state0 root st_init
                              (tree_edge_upd' tree_edge_upd (vs_b, s_a) w) (w :: [root])
                              (graph.put g_b root w)).
            { apply dfs_tree_edge; [exact Hne | exact Hstate | cbn [already_seen]; exact Hw]. }
            pose proof (dfs_fold_state_trans _ _ _ root st_init (tree_edge_upd' tree_edge_upd (vs_b, s_a) w)
              (dfs_fold'0 g (S n'') (vs_b, s_a) w) [root] [] (graph.put g_b root w) g_w w
              Htree
              ltac:(unfold st_init; apply already_seen_tree_edge_upd_self)
              Hedges Hchild) as Htrans.
            cbn [app] in Htrans.
            (* now assemble P remaining' *)
            split; [|split; [|split; [|split; [|split]]]].
            -- apply (dfs_fold'_fst untree_edge_upd tree_edge_upd finish
                       untree_edge_accumulate tree_edge_accumulate finish_accumulate g (S n'')).
               reflexivity.
            -- apply accum_path_inv.
            -- rewrite (accum_step g n'' vs_b g_b root w Hw), Ew. cbn [snd]. exact Htrans.
            -- intros x Hx Hedge. rewrite (accum_step g n'' vs_b g_b root w Hw), Ew in Hedge.
               cbn [snd] in Hedge. cbv [graph_edge] in Hedge.
               rewrite graph.edges_union in Hedge. destruct Hedge as [He1 | He2].
               ++ rewrite graph.edges_put in He1. destruct He1 as [Hold | [_ Hxw]].
                  ** apply (Htrack x); [right; exact Hx | exact Hold].
                  ** subst x; contradiction.
               ++ pose proof (dfs_source_init _ _ _ w (tree_edge_upd' tree_edge_upd (vs_b, s_a) w)
                    (dfs_fold'0 g (S n'') (vs_b, s_a) w) [] g_w root x Hchild) as Hsi.
                  cbv [graph_edge] in Hsi. specialize (Hsi He2).
                  destruct Hsi as [Hrw' | Hunseen]; [congruence|].
                  cbn [already_seen] in Hunseen. simpl in Hunseen.
                  rewrite Hrootseen in Hunseen. destruct (eqb root w); discriminate.
            -- inversion Hnodup; auto.
            -- intros y Hy; apply Hincl; right; exact Hy. }
    subst P; cbn beta in HP.
    destruct HP as (_ & _ & Hstate & _).
    revert Hstate.
    destruct (fold_left (graph_accumulator g n') (graph.edges g root)
                (root :: vs, ([root], graph.empty))) as [vsF [pF gF]].
    cbn [finish' finish_accumulate snd]. intro Hstate.
    apply dfs_finish. exact Hstate.
  Qed.

  Lemma dfs_fold_sound root vs n st0 g :
    already_seen (vs, st0) root = false ->
    (forall p v, path_to (graph_edge g) root p v ->
       Forall (fun w => ~ In w vs) (root :: p) -> length p < n) ->
    exists g',
      dfs_fold_state0 root (edge_upd'0 (vs, st0) root)
        (dfs_fold'0 g n (vs, st0) root) [] g' /\
      restriction root vs g g'.
  Proof.
    intro Hroot. cbn [already_seen] in Hroot. intro Hfuel.
    exists (snd (snd (graph_accumulator g n (vs, ([], graph.empty)) root))).
    split.
    - assert (Hrootvs : ~ In root vs).
      { intro Hin. apply set_contains_iff_In in Hin. rewrite Hin in Hroot. discriminate. }
      assert (Hn : 0 < n).
      { pose proof (Hfuel [] root
          ltac:(unfold path_to; split; [exact I | reflexivity])
          ltac:(constructor; [exact Hrootvs | constructor])) as Hlen.
        cbn [length] in Hlen. lia. }
      pose proof (dfs_fold_sound1 root vs n st0 g Hn Hroot) as Hs1. revert Hs1.
      destruct (graph_accumulator g n (vs, ([], graph.empty)) root) as [vsF [pF gF]].
      intro Hs1. exact Hs1.
    - apply accum_restriction; [exact Hroot | exact Hfuel].
  Qed.

  Definition check_tree :=
    dfs_fold (fun _ _ _ => false) (fun tree _ _ => tree).
End __.
