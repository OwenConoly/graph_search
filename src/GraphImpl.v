From Stdlib Require Import List Eqdep_dec.
From coqutil Require Import Map.Interface Map.Properties Eqb Tactics.destr.
From GraphSearch Require Import GraphInterface.
Import ListNotations.

Section GraphImpl.
  Context {V : Type}.
  Context {eqbV : Eqb V} {eqbV_ok : Eqb_ok eqbV}.
  Context {Vset : map.map V unit} {Vset_ok : map.ok Vset}.
  Context {M : map.map V Vset} {M_ok : map.ok M}.

  Definition set_at (m : M) (u : V) : Vset :=
    match map.get m u with
    | Some s => s
    | None => map.empty
    end.

  Definition put_raw (m : M) (u v : V) : M :=
    map.put m u (map.put (set_at m u) v tt).

  Definition nonemptyb (s : Vset) : bool :=
    match map.keys s with
    | [] => false
    | _ :: _ => true
    end.

  Definition remove_raw (m : M) (u v : V) : M :=
    match map.get m u with
    | None => m
    | Some s =>
        if nonemptyb (map.remove s v)
        then map.put m u (map.remove s v)
        else map.remove m u
    end.

  Lemma nonemptyb_true_iff s :
    nonemptyb s = true <-> map.keys s <> [].
  Proof.
    unfold nonemptyb. destruct (map.keys s); split; congruence.
  Qed.

  Lemma in_keys_iff (s : Vset) (k : V) :
    In k (map.keys s) <-> map.get s k <> None.
  Proof.
    split.
    - apply map.in_keys_inv.
    - intro H. destruct (map.get s k) as [u|] eqn:E; [| congruence].
      eapply map.in_keys. exact E.
  Qed.

  Lemma nonemptyb_put s v :
    nonemptyb (map.put s v tt) = true.
  Proof.
    apply nonemptyb_true_iff. intro Hnil.
    pose proof (map.in_keys (map.put s v tt) v tt (map.get_put_same _ _ _)) as Hin.
    rewrite Hnil in Hin. exact Hin.
  Qed.

  Lemma nonemptyb_false_get s x :
    nonemptyb s = false -> map.get s x = None.
  Proof.
    intro H. destruct (map.get s x) as [u|] eqn:E; [| reflexivity].
    exfalso.
    assert (nonemptyb s = true) as HT.
    { apply nonemptyb_true_iff. intro Hnil.
      pose proof (map.in_keys s x u E) as Hin. rewrite Hnil in Hin. exact Hin. }
    congruence.
  Qed.

  Definition wfb (m : M) : bool :=
    map.forallb (fun _ s => nonemptyb s) m.

  Lemma forallb_of_forall (f : V -> Vset -> bool) (m : M) :
    (forall k s, map.get m k = Some s -> f k s = true) ->
    map.forallb f m = true.
  Proof.
    intro Hall. unfold map.forallb.
    refine (map.fold_spec
              (fun m r => (forall k s, map.get m k = Some s -> f k s = true) -> r = true)
              _ true _ _ m Hall).
    - intros _. reflexivity.
    - intros k s m0 r Hnone IH Hput.
      assert (Hf : f k s = true) by (apply Hput; apply map.get_put_same).
      assert (Hr : r = true).
      { apply IH. intros k' s' Hg.
        assert (k' <> k) as Hne
            by (intro He; subst k'; rewrite Hnone in Hg; discriminate).
        apply Hput. rewrite map.get_put_diff by exact Hne. exact Hg. }
      rewrite Hr, Hf. reflexivity.
  Qed.

  Lemma wfb_spec m u s :
    wfb m = true -> map.get m u = Some s -> nonemptyb s = true.
  Proof.
    intros Hwf Hget. exact (map.get_forallb _ m Hwf u s Hget).
  Qed.

  Lemma wfb_empty : wfb (map.empty : M) = true.
  Proof.
    unfold wfb. apply forallb_of_forall. intros k s Hget.
    rewrite map.get_empty in Hget. discriminate.
  Qed.

  Lemma wfb_put_raw m u v :
    wfb m = true -> wfb (put_raw m u v) = true.
  Proof.
    intro Hwf. unfold wfb, put_raw. apply forallb_of_forall.
    intros k s Hget. rewrite map.get_put_dec in Hget. destr (eqb u k).
    - inversion Hget. subst s. apply nonemptyb_put.
    - exact (wfb_spec m k s Hwf Hget).
  Qed.

  Lemma wfb_remove_raw m u v :
    wfb m = true -> wfb (remove_raw m u v) = true.
  Proof.
    intro Hwf. unfold remove_raw.
    destruct (map.get m u) as [s|] eqn:Hu; [| exact Hwf].
    destruct (nonemptyb (map.remove s v)) eqn:Hne.
    - unfold wfb. apply forallb_of_forall. intros k t Hget.
      rewrite map.get_put_dec in Hget. destr (eqb u k).
      + inversion Hget. subst t. exact Hne.
      + exact (wfb_spec m k t Hwf Hget).
    - unfold wfb. apply forallb_of_forall. intros k t Hget.
      rewrite map.get_remove_dec in Hget. destr (eqb u k).
      + discriminate Hget.
      + exact (wfb_spec m k t Hwf Hget).
  Qed.

  Record graph_rep := { raw : M ; raw_wf : wfb raw = true }.

  Lemma eq_grep (x y : graph_rep) : raw x = raw y -> x = y.
  Proof.
    destruct x as [mx px], y as [my py]. simpl. intro Heq. subst my.
    f_equal. apply Eqdep_dec.UIP_dec. decide equality.
  Qed.

  Definition edges (g : graph_rep) (u : V) : list V :=
    match map.get (raw g) u with
    | Some s => map.keys s
    | None => []
    end.

  Definition empty : graph_rep := {| raw := map.empty ; raw_wf := wfb_empty |}.

  Definition put (g : graph_rep) (u v : V) : graph_rep :=
    {| raw := put_raw (raw g) u v ; raw_wf := wfb_put_raw (raw g) u v (raw_wf g) |}.

  Definition remove (g : graph_rep) (u v : V) : graph_rep :=
    {| raw := remove_raw (raw g) u v ; raw_wf := wfb_remove_raw (raw g) u v (raw_wf g) |}.

  Definition sources (g : graph_rep) : list V := map.keys (raw g).

  Definition mem (m : M) (u v : V) : Prop :=
    exists s, map.get m u = Some s /\ map.get s v <> None.

  Lemma in_edges_iff g u v :
    In v (edges g u) <-> mem (raw g) u v.
  Proof.
    unfold edges, mem. destruct (map.get (raw g) u) as [s|] eqn:E.
    - rewrite in_keys_iff. split.
      + intro H. exists s. split; [reflexivity | exact H].
      + intros [s0 [Hs0 Hv]]. inversion Hs0. subst s0. exact Hv.
    - split.
      + intro H. destruct H.
      + intros [s0 [Hs0 _]]. discriminate.
  Qed.

  Lemma get_set_at m u v :
    map.get (set_at m u) v <> None <-> exists s, map.get m u = Some s /\ map.get s v <> None.
  Proof.
    unfold set_at. destruct (map.get m u) as [s|] eqn:E.
    - split.
      + intro H. exists s. split; [reflexivity | exact H].
      + intros [s0 [Hs0 Hv]]. inversion Hs0. subst s0. exact Hv.
    - split.
      + intro H. rewrite map.get_empty in H. congruence.
      + intros [s0 [Hs0 _]]. discriminate.
  Qed.

  Lemma mem_put_raw m u v u' v' :
    mem (put_raw m u v) u' v' <-> mem m u' v' \/ (u = u' /\ v = v').
  Proof.
    unfold mem, put_raw. split.
    - intros [s [Hs Hv]]. rewrite map.get_put_dec in Hs. destr (eqb u u').
      + inversion Hs. subst s. clear Hs.
        rewrite map.get_put_dec in Hv. destr (eqb v v').
        * right. split; reflexivity.
        * left. exact (proj1 (get_set_at _ _ _) Hv).
      + left. exists s. split; [exact Hs | exact Hv].
    - intros [[s [Hs Hv]] | [Heu Hev]].
      + destr (eqb u u').
        * exists (map.put (set_at m u') v tt). split; [apply map.get_put_same|].
          rewrite map.get_put_dec. destr (eqb v v').
          -- discriminate.
          -- apply (proj2 (get_set_at _ _ _)). exists s. split; [exact Hs | exact Hv].
        * exists s. split.
          -- rewrite map.get_put_diff by (apply not_eq_sym; exact E). exact Hs.
          -- exact Hv.
      + subst u' v'. exists (map.put (set_at m u) v tt).
        split; [apply map.get_put_same|].
        rewrite map.get_put_same. discriminate.
  Qed.

  Lemma mem_remove_raw m u v u' v' :
    mem (remove_raw m u v) u' v' <-> mem m u' v' /\ (u <> u' \/ v <> v').
  Proof.
    unfold remove_raw. destruct (map.get m u) as [s|] eqn:Hu.
    - destruct (nonemptyb (map.remove s v)) eqn:Hne.
      + unfold mem. split.
        * intros [t [Ht Hv]]. rewrite map.get_put_dec in Ht. destr (eqb u u').
          -- inversion Ht. subst t. clear Ht.
             rewrite map.get_remove_dec in Hv. destr (eqb v v').
             ++ congruence.
             ++ split; [exists s; split; [exact Hu | exact Hv] | right; exact E].
          -- split; [exists t; split; [exact Ht | exact Hv] | left; exact E].
        * intros [[t [Ht Hv]] Hor]. destr (eqb u u').
          -- rewrite Hu in Ht. inversion Ht. subst t.
             exists (map.remove s v). split; [apply map.get_put_same|].
             rewrite map.get_remove_dec. destr (eqb v v').
             ++ destruct Hor as [H|H]; congruence.
             ++ exact Hv.
          -- exists t. split.
             ++ rewrite map.get_put_diff by (apply not_eq_sym; exact E). exact Ht.
             ++ exact Hv.
      + unfold mem. split.
        * intros [t [Ht Hv]]. rewrite map.get_remove_dec in Ht. destr (eqb u u').
          -- discriminate Ht.
          -- split; [exists t; split; [exact Ht | exact Hv] | left; exact E].
        * intros [[t [Ht Hv]] Hor]. destr (eqb u u').
          -- exfalso. rewrite Hu in Ht. inversion Ht. subst t.
             destruct Hor as [H|Hvv]; [congruence|].
             pose proof (nonemptyb_false_get (map.remove s v) v' Hne) as Hn0.
             rewrite map.get_remove_diff in Hn0 by (apply not_eq_sym; exact Hvv).
             congruence.
          -- exists t. split.
             ++ rewrite map.get_remove_diff by (apply not_eq_sym; exact E). exact Ht.
             ++ exact Hv.
    - unfold mem. split.
      + intros [t [Ht Hv]]. split; [exists t; split; [exact Ht | exact Hv]|].
        left. intro Heq. subst u'. rewrite Hu in Ht. discriminate.
      + intros [[t [Ht Hv]] _]. exists t. split; [exact Ht | exact Hv].
  Qed.

  Definition graph_map : graph.graph V :=
    {| graph.rep := graph_rep;
       graph.edges := edges;
       graph.empty := empty;
       graph.put := put;
       graph.remove := remove;
       graph.sources := sources |}.

  Global Instance graph_map_ok : graph.ok graph_map.
  Proof.
    split;
      cbn [graph.rep graph.edges graph.empty graph.put graph.remove graph.sources graph_map].
    - intros g1 g2 Hsame. apply eq_grep. apply map.map_ext. intro k.
      specialize (Hsame k). unfold same_set in Hsame.
      pose proof (fun a => proj1 (Hsame a)) as H12. pose proof (fun a => proj2 (Hsame a)) as H21.
      destruct (map.get (raw g1) k) as [s1|] eqn:E1;
        destruct (map.get (raw g2) k) as [s2|] eqn:E2.
      + f_equal. apply map.map_ext. intro x.
        assert (E1e : edges g1 k = map.keys s1) by (unfold edges; rewrite E1; reflexivity).
        assert (E2e : edges g2 k = map.keys s2) by (unfold edges; rewrite E2; reflexivity).
        rewrite E1e, E2e in H12, H21.
        destruct (map.get s1 x) as [u1|] eqn:Gx1;
          destruct (map.get s2 x) as [u2|] eqn:Gx2.
        * destruct u1, u2; reflexivity.
        * exfalso.
          assert (Hin : In x (map.keys s1)) by (apply in_keys_iff; rewrite Gx1; congruence).
          apply H12 in Hin. apply in_keys_iff in Hin. rewrite Gx2 in Hin. congruence.
        * exfalso.
          assert (Hin : In x (map.keys s2)) by (apply in_keys_iff; rewrite Gx2; congruence).
          apply H21 in Hin. apply in_keys_iff in Hin. rewrite Gx1 in Hin. congruence.
        * reflexivity.
      + exfalso.
        assert (E1e : edges g1 k = map.keys s1) by (unfold edges; rewrite E1; reflexivity).
        assert (E2e : edges g2 k = []) by (unfold edges; rewrite E2; reflexivity).
        rewrite E1e, E2e in H12.
        pose proof (wfb_spec (raw g1) k s1 (raw_wf g1) E1) as Hn.
        apply nonemptyb_true_iff in Hn.
        destruct (map.keys s1) as [|x0 xs] eqn:K; [congruence|].
        exact (H12 x0 (or_introl eq_refl)).
      + exfalso.
        assert (E1e : edges g1 k = []) by (unfold edges; rewrite E1; reflexivity).
        assert (E2e : edges g2 k = map.keys s2) by (unfold edges; rewrite E2; reflexivity).
        rewrite E1e, E2e in H21.
        pose proof (wfb_spec (raw g2) k s2 (raw_wf g2) E2) as Hn.
        apply nonemptyb_true_iff in Hn.
        destruct (map.keys s2) as [|x0 xs] eqn:K; [congruence|].
        exact (H21 x0 (or_introl eq_refl)).
      + reflexivity.
    - intro v. unfold edges, empty. cbn [raw]. rewrite map.get_empty. reflexivity.
    - intros g u u' v v'. rewrite !in_edges_iff.
      change (raw (put g u v)) with (put_raw (raw g) u v).
      rewrite mem_put_raw. reflexivity.
    - intros g u v u' v'. rewrite !in_edges_iff.
      change (raw (remove g u v)) with (remove_raw (raw g) u v).
      rewrite mem_remove_raw. reflexivity.
    - intros g u. unfold sources, edges.
      destruct (map.get (raw g) u) as [s|] eqn:E.
      + split.
        * intros _. apply nonemptyb_true_iff. exact (wfb_spec (raw g) u s (raw_wf g) E).
        * intros _. eapply map.in_keys. exact E.
      + split.
        * intro Hin. apply map.in_keys_inv in Hin. rewrite E in Hin. congruence.
        * intro H. congruence.
    - intros g u. unfold edges. destruct (map.get (raw g) u) as [s|] eqn:E.
      + apply map.keys_NoDup.
      + constructor.
  Qed.
End GraphImpl.
