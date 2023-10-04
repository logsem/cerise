
(** Composition of finite maps
    Might be merged into stdpp at some point,
    see https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/459 *)
From stdpp Require Import fin_maps fin_map_dom.
From cap_machine Require Import stdpp_img.

Definition map_compose {A B C MA MB} `{FA:FinMap A MA, FB:FinMap B MB}
  (m : MB C) (n : MA B) := omap (m !!.) n.
Infix "∘ₘ" := map_compose (at level 65, right associativity) : stdpp_scope.
Notation "(∘ₘ)" := map_compose (only parsing) : stdpp_scope.
Notation "( m ∘ₘ.)" := (map_compose m) (only parsing) : stdpp_scope.
Notation "(.∘ₘ m )" := (λ n, map_compose n m) (only parsing) : stdpp_scope.

(** * The [map_compose] operation *)
Section map_compose.
  Context {A MA B MB} `{FA:FinMap A MA} `{FB:FinMap B MB}.
  Context {C : Type}.
  Implicit Types (m : MB C) (n : MA B) (a : A) (b : B) (c : C).

  Lemma map_compose_lookup m n a : (m ∘ₘ n) !! a = n !! a ≫= λ b, m !! b.
  Proof. apply lookup_omap. Qed.

  Lemma map_compose_lookup_Some m n a c :
    (m ∘ₘ n) !! a = Some c ↔
    ∃ b, n !! a = Some b ∧ m !! b = Some c.
  Proof.
    rewrite map_compose_lookup.
    destruct (n !! a) as [b|] eqn:Hm; naive_solver.
  Qed.
  Lemma map_compose_lookup_Some_1 m n a c :
    (m ∘ₘ n) !! a = Some c →
    ∃ b, n !! a = Some b ∧ m !! b = Some c.
  Proof. by rewrite map_compose_lookup_Some. Qed.
  Lemma map_compose_lookup_Some_2 m n a b c :
    n !! a = Some b → m !! b = Some c →
    (m ∘ₘ n) !! a = Some c.
  Proof. intros. apply map_compose_lookup_Some. by exists b. Qed.

  Lemma map_compose_lookup_None m n a :
    (m ∘ₘ n) !! a = None ↔
    n !! a = None ∨ ∃ b, n !! a = Some b ∧ m !! b = None.
  Proof.
    rewrite map_compose_lookup.
    destruct (n!!a) as [b|] eqn:Hn; naive_solver.
  Qed.
  Lemma map_compose_lookup_None_1 m n a :
    (m ∘ₘ n) !! a = None →
    n !! a = None ∨ ∃ b, n !! a = Some b ∧ m !! b = None.
  Proof. apply map_compose_lookup_None. Qed.
  Lemma map_compose_lookup_None_2 m n a :
    (n !! a = None ∨ ∃ b, n !! a = Some b ∧ m !! b = None) →
    (m ∘ₘ n) !! a = None.
  Proof. apply map_compose_lookup_None. Qed.
  Lemma map_compose_lookup_None_2l m n a : n !! a = None → (m ∘ₘ n) !! a = None.
  Proof. intros. apply map_compose_lookup_None. by left. Qed.
  Lemma map_compose_lookup_None_2r m n a b :
    n !! a = Some b → m !! b = None → (m ∘ₘ n) !! a = None.
  Proof. intros. apply map_compose_lookup_None. naive_solver. Qed.

  Lemma map_compose_img_subseteq `{FinSet C D} m n : map_img (m ∘ₘ n) ⊆@{D} map_img m.
  Proof.
    intros c. rewrite !elem_of_map_img.
    setoid_rewrite map_compose_lookup_Some. naive_solver.
  Qed.

  Lemma map_compose_empty_r m : m ∘ₘ ∅ = (∅ : MA C).
  Proof. apply omap_empty. Qed.
  Lemma map_compose_empty_l n : (∅ : MB C) ∘ₘ n = (∅ : MA C).
  Proof.
    apply map_eq. intros k. rewrite map_compose_lookup, lookup_empty.
    destruct (n!!k); simpl; [apply lookup_empty|reflexivity].
  Qed.
  Lemma map_compose_empty_iff m n :
    m ∘ₘ n = ∅ ↔
    ∀ b, is_Some (m !! b) → (∃ a, n !! a = Some b) → False.
  Proof.
    rewrite map_empty. setoid_rewrite map_compose_lookup_None.
    split.
    - intros Hmn b [c Hbc] [a Hab]. destruct (Hmn a); naive_solver.
    - intros Hmn a. destruct (n !! a) as [b|] eqn:Hn; [right|by left].
      destruct (m !! b) eqn:Hm; naive_solver.
  Qed.

  Lemma map_compose_union_l m1 m2 n : (m1 ∪ m2) ∘ₘ n = (m1 ∘ₘ n) ∪ (m2 ∘ₘ n).
  Proof.
    apply map_eq. intros a. rewrite map_compose_lookup.
    destruct (n!!a) as [b|] eqn:Hn; simpl.
    - destruct (m1!!b) as [c|] eqn:Hm1.
      + rewrite (lookup_union_Some_l _ _ _ c Hm1). symmetry.
        apply lookup_union_Some_l. apply map_compose_lookup_Some. by exists b.
      + rewrite (lookup_union_r _ _ _ Hm1). symmetry.
        rewrite lookup_union_r; [|by apply (map_compose_lookup_None_2r m1 n a b)].
        by rewrite map_compose_lookup, Hn.
    - symmetry. rewrite lookup_union_None.
      split; by apply map_compose_lookup_None_2l.
  Qed.
  Lemma map_compose_union_r m n1 n2 :
    n1 ##ₘ n2 → m ∘ₘ (n1 ∪ n2) = (m ∘ₘ n1) ∪ (m ∘ₘ n2).
  Proof. intros Hs. by apply map_omap_union. Qed.

  Global Instance map_compose_mono_l n : Proper ((⊆) ==> (⊆)) (λ m, map_compose m n).
  Proof.
    intros m1 m2 Hinf. apply map_subseteq_spec. intros a c Ha.
    apply map_compose_lookup_Some. apply map_compose_lookup_Some in Ha as [b [Hn Hm]].
    exists b. split; [done|]. rewrite map_subseteq_spec in Hinf. by apply Hinf.
  Qed.
  Global Instance map_compose_mono_r m : Proper ((⊆@{MA B}) ==> (⊆)) (m ∘ₘ.).
  Proof. intros n1 n2 Hn1n2. by apply map_omap_mono. Qed.
  Global Instance map_compose_mono : Proper ((⊆@{MB C}) ==> (⊆@{MA B}) ==> (⊆)) (∘ₘ).
  Proof.
    intros m1 m2 Hm n1 n2 Hn. transitivity (map_compose m1 n2);
    [ by apply map_compose_mono_r | by apply map_compose_mono_l ].
  Qed.

  Lemma map_compose_disjoint m1 m2 n : m1 ##ₘ m2 → m1 ∘ₘ n ##ₘ m2 ∘ₘ n.
  Proof.
    intros Hdisj. rewrite map_disjoint_spec. intros a c1 c2 Ha1 Ha2.
    rewrite map_disjoint_spec in Hdisj. rewrite !map_compose_lookup in Ha1, Ha2.
    destruct (n!!a); [ apply (Hdisj _ _ _ Ha1 Ha2) | done].
  Qed.

  (** Alternative definition of [map_compose m n] by induction on [n] *)
  Lemma map_compose_alt m n :
    m ∘ₘ n = map_fold (λ a b (mn: MA C), match m !! b with
      | Some c => <[a:=c]> mn
      | None => mn
      end) ∅ n.
  Proof.
    apply (map_fold_ind (λ (mn : MA C) n, omap (m !!.) n = mn)).
    - apply map_compose_empty_r.
    - intros k b n' mn Hn' IH. rewrite omap_insert, <- IH.
      destruct (m!!b); [ done | by apply delete_notin, map_compose_lookup_None_2l ].
  Qed.

  Lemma map_compose_filter_subseteq_l (P : B*C → Prop) `{∀ x, Decision (P x)} m n :
    (filter P m) ∘ₘ n ⊆ m ∘ₘ n.
  Proof. apply map_compose_mono_l, map_filter_subseteq. Qed.
  Lemma map_compose_filter_subseteq_r (P : A*B → Prop) `{∀ x, Decision (P x)} m n :
    m ∘ₘ (filter P n) ⊆ m ∘ₘ n.
  Proof. apply map_compose_mono_r, map_filter_subseteq. Qed.

  Lemma map_compose_min_l `{FinSet B D, !RelDecision (∈@{D})} m n :
    m ∘ₘ n = (filter (λ '(b,_), b ∈ map_img (SA:=D) n) m) ∘ₘ n.
  Proof.
    apply map_eq. intro a. rewrite !map_compose_lookup.
    destruct (n!!a) eqn:Hn; [ simpl | done ].
    destruct (m!!b) eqn:Hm; symmetry.
    - apply map_filter_lookup_Some. split; [ done |].
      rewrite elem_of_map_img. by exists a.
    - apply map_filter_lookup_None. by left.
  Qed.
  Lemma map_compose_min_r m n :
    map_compose (FB:=FB) m n = map_compose (FB:=FB) m (filter (λ '(_,b), is_Some (m !! b)) n).
  Proof.
    apply map_eq. intro a. rewrite !map_compose_lookup.
    destruct (n!!a) eqn:Hn; simpl; symmetry.
    - destruct (m!!b) eqn:Hm.
      + apply bind_Some. exists b. split;
        [ by apply map_filter_lookup_Some | done ].
      + apply bind_None. left. apply map_filter_lookup_None. right.
        intros x Hx [z Hz]. by simplify_eq.
    - apply bind_None. left. apply map_filter_lookup_None. by left.
  Qed.

  Lemma map_compose_singleton_Some m a b c :
    m !! b = Some c →
    m ∘ₘ {[a := b]} = {[a := c]}.
  Proof. intros. by apply omap_singleton_Some. Qed.

  Lemma map_compose_singleton_None m a b :
    m !! b = None →
    m ∘ₘ {[a := b]} = ∅.
  Proof. intros. by apply omap_singleton_None. Qed.

  Lemma map_compose_singletons a b c : {[b := c]} ∘ₘ {[a := b]} = {[a := c]}.
  Proof. rewrite (map_compose_singleton_Some _ a b c); [done|apply lookup_insert]. Qed.
End map_compose.

Lemma map_compose_assoc `{FinMap A MA, FinMap B MB, FinMap C MC} {D}
    (m : MC D) (n : MB C) (o : MA B) :
  m ∘ₘ (n ∘ₘ o) = (m ∘ₘ n) ∘ₘ o.
Proof.
  apply map_eq. intros a. rewrite !map_compose_lookup.
  destruct (o!!a); [simpl|done]. by rewrite map_compose_lookup.
Qed.

Global Hint Extern 3 (_ ∘ₘ ?n ##ₘ _ ∘ₘ ?n) =>
  apply map_compose_disjoint : map_disjoint.

Section map_dom.
  Context `{FinMapDom K M D}.
  Lemma dom_omap_subseteq {A B} (f : A → option B) (m : M A) :
    dom (omap f m) ⊆ dom m.
  Proof.
    intros a. rewrite !elem_of_dom. intros [c Hm].
    apply lookup_omap_Some in Hm. naive_solver.
  Qed.
  Lemma map_compose_dom_subseteq {C} `{FinMap K' M'} (m: M' C) (n : M K') :
    dom (m ∘ₘ n : M C) ⊆@{D} dom n.
  Proof. apply dom_omap_subseteq. Qed.
  Lemma map_compose_min_r_dom {C} `{FinMap K' M', !RelDecision (∈@{D})} (m : M C) (n : M' K) :
    m ∘ₘ n = m ∘ₘ (filter (λ '(_,b), b ∈ dom m) n).
  Proof.
    rewrite map_compose_min_r. f_equal.
    apply map_filter_ext. intros. by rewrite elem_of_dom.
  Qed.

  (* Lemma map_compose_empty_iff_dom_img {C} `{FinMap K' M', !RelDecision (∈@{D})} (m : M C) (n : M' K) :
    m ∘ₘ n = ∅ ↔ dom m ## map_img n.
  Proof.
    rewrite map_compose_empty_iff. set_unfold.
    setoid_rewrite elem_of_dom. by setoid_rewrite elem_of_map_img.
  Qed. *)
End map_dom.
