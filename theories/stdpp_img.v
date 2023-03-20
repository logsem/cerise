(** This has been merged into stdpp,
    https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/444
    Remove when updating to stdpp 1.9.0

    It is an implementation of an image/codomain set for maps *)
From stdpp Require Import fin_maps.

(** Given a finite map [m : M] with keys [K] and values [A], the image [map_img m]
gives a finite set containing with the values [A] of [m]. The type of [map_img]
is generic to support different map and set implementations. A possible instance
is [SA:=gset A]. *)
Definition map_img `{FinMapToList K A M,
  Singleton A SA, Empty SA, Union SA} : M → SA := map_to_set (λ _ x, x).
Global Typeclasses Opaque map_img.

(** ** The [map_img] (image/codomain) operation *)
Section img.
  Context `{FinMap K M, FinSet A SA}.
  Implicit Types m : M A.
  Implicit Types x y : A.
  Implicit Types X : SA.

  (* avoid writing ≡@{D} everywhere... *)
  Notation map_img := (map_img (M:=M A) (SA:=SA)).

  Lemma elem_of_map_img m x : x ∈ map_img m ↔ ∃ i, m !! i = Some x.
  Proof. unfold map_img. rewrite elem_of_map_to_set. naive_solver. Qed.
  Lemma elem_of_map_img_1 m x : x ∈ map_img m → ∃ i, m !! i = Some x.
  Proof. apply elem_of_map_img. Qed.
  Lemma elem_of_map_img_2 m i x : m !! i = Some x → x ∈ map_img m.
  Proof. rewrite elem_of_map_img. eauto. Qed.

  Lemma not_elem_of_map_img m x : x ∉ map_img m ↔ ∀ i, m !! i ≠ Some x.
  Proof. rewrite elem_of_map_img. naive_solver. Qed.
  Lemma not_elem_of_map_img_1 m i x : x ∉ map_img m → m !! i ≠ Some x.
  Proof. rewrite not_elem_of_map_img. eauto. Qed.
  Lemma not_elem_of_map_img_2 m x : (∀ i, m !! i ≠ Some x) → x ∉ map_img m.
  Proof. apply not_elem_of_map_img. Qed.

  Lemma map_subseteq_img m1 m2 : m1 ⊆ m2 → map_img m1 ⊆ map_img m2.
  Proof.
    rewrite map_subseteq_spec. intros ? x.
    rewrite !elem_of_map_img. naive_solver.
  Qed.

  Lemma map_img_filter (P : K * A → Prop) `{!∀ ix, Decision (P ix)} m X :
    (∀ x, x ∈ X ↔ ∃ i, m !! i = Some x ∧ P (i, x)) →
    map_img (filter P m) ≡ X.
  Proof.
    intros HX x. rewrite elem_of_map_img, HX.
    unfold is_Some. by setoid_rewrite map_filter_lookup_Some.
  Qed.
  Lemma map_img_filter_subseteq (P : K * A → Prop) `{!∀ ix, Decision (P ix)} m :
    map_img (filter P m) ⊆ map_img m.
  Proof. apply map_subseteq_img, map_filter_subseteq. Qed.

  Lemma map_img_empty : map_img ∅ ≡ ∅.
  Proof.
    rewrite set_equiv. intros x. rewrite elem_of_map_img, elem_of_empty.
    setoid_rewrite lookup_empty. naive_solver.
  Qed.
  Lemma map_img_empty_iff m : map_img m ≡ ∅ ↔ m = ∅.
  Proof.
    split; [|intros ->; by rewrite map_img_empty].
    intros Hm. apply map_empty; intros i.
    apply eq_None_ne_Some; intros x ?%elem_of_map_img_2. set_solver.
  Qed.
  Lemma map_img_empty_inv m : map_img m ≡ ∅ → m = ∅.
  Proof. apply map_img_empty_iff. Qed.

  Lemma map_img_delete_subseteq i m : map_img (delete i m) ⊆ map_img m.
  Proof. apply map_subseteq_img, delete_subseteq. Qed.

  Lemma map_img_insert m i x :
    map_img (<[i:=x]> m) ≡ {[ x ]} ∪ map_img (delete i m).
  Proof.
    intros y. rewrite elem_of_union, !elem_of_map_img, elem_of_singleton.
    setoid_rewrite lookup_delete_Some. setoid_rewrite lookup_insert_Some.
    naive_solver.
  Qed.
  Lemma map_img_insert_notin m i x :
    m !! i = None → map_img (<[i:=x]> m) ≡ {[ x ]} ∪ map_img m.
  Proof. intros. by rewrite map_img_insert, delete_notin. Qed.

  Lemma map_img_insert_subseteq m i x :
    map_img (<[i:=x]> m) ⊆ {[ x ]} ∪ map_img m.
  Proof.
    rewrite map_img_insert. apply union_mono_l, map_img_delete_subseteq.
  Qed.
  Lemma elem_of_map_img_insert m i x : x ∈ map_img (<[i:=x]> m).
  Proof. apply elem_of_map_img. exists i. apply lookup_insert. Qed.
  Lemma elem_of_map_img_insert_ne m i x y :
    x ≠ y → x ∈ map_img (<[i:=y]> m) → x ∈ map_img m.
  Proof. intros ? ?%map_img_insert_subseteq. set_solver. Qed.

  Lemma map_img_singleton i x : map_img {[ i := x ]} ≡ {[ x ]}.
  Proof.
    apply set_equiv. intros y.
    rewrite elem_of_map_img. setoid_rewrite lookup_singleton_Some. set_solver.
  Qed.

  Lemma elem_of_map_img_union m1 m2 x :
    x ∈ map_img (m1 ∪ m2) →
    x ∈ map_img m1 ∨ x ∈ map_img m2.
  Proof.
    rewrite !elem_of_map_img. setoid_rewrite lookup_union_Some_raw. naive_solver.
  Qed.
  Lemma elem_of_map_img_union_l m1 m2 x :
    x ∈ map_img m1 → x ∈ map_img (m1 ∪ m2).
  Proof.
    rewrite !elem_of_map_img. setoid_rewrite lookup_union_Some_raw. naive_solver.
  Qed.
  Lemma elem_of_map_img_union_r m1 m2 x :
    m1 ##ₘ m2 → x ∈ map_img m2 → x ∈ map_img (m1 ∪ m2).
  Proof.
    intros. rewrite map_union_comm by done. by apply elem_of_map_img_union_l.
  Qed.
  Lemma elem_of_map_img_union_disjoint m1 m2 x :
    m1 ##ₘ m2 → x ∈ map_img (m1 ∪ m2) ↔ x ∈ map_img m1 ∨ x ∈ map_img m2.
  Proof.
    naive_solver eauto using elem_of_map_img_union,
      elem_of_map_img_union_l, elem_of_map_img_union_r.
  Qed.

  Lemma map_img_union_subseteq m1 m2 :
    map_img (m1 ∪ m2) ⊆ map_img m1 ∪ map_img m2.
  Proof. intros v Hv. apply elem_of_union, elem_of_map_img_union. exact Hv. Qed.
  Lemma map_img_union_subseteq_l m1 m2 : map_img m1 ⊆ map_img (m1 ∪ m2).
  Proof. intros v Hv. by apply elem_of_map_img_union_l. Qed.
  Lemma map_img_union_subseteq_r m1 m2 :
    m1 ##ₘ m2 → map_img m2 ⊆ map_img (m1 ∪ m2).
  Proof. intros Hdisj v Hv. by apply elem_of_map_img_union_r. Qed.
  Lemma map_img_union_disjoint m1 m2 :
    m1 ##ₘ m2 → map_img (m1 ∪ m2) ≡ map_img m1 ∪ map_img m2.
  Proof.
    intros Hdisj. apply set_equiv. intros x.
    rewrite elem_of_union. by apply elem_of_map_img_union_disjoint.
  Qed.

  Lemma map_img_finite m : set_finite (map_img m).
  Proof.
    induction m as [|i x m ? IH] using map_ind.
    - rewrite map_img_empty. apply empty_finite.
    - eapply set_finite_subseteq; [by apply map_img_insert_subseteq|].
      apply union_finite; [apply singleton_finite | apply IH].
  Qed.

  (** Alternative definition of [img] in terms of [map_to_list]. *)
  Lemma map_img_alt m : map_img m ≡ list_to_set (map_to_list m).*2.
  Proof.
    induction m as [|i x m ? IH] using map_ind.
    { by rewrite map_img_empty, map_to_list_empty. }
    by rewrite map_img_insert_notin, map_to_list_insert by done.
  Qed.

  Lemma map_img_singleton_inv m i x :
    map_img m ≡ {[ x ]} → m !! i = None ∨ m !! i = Some x.
  Proof.
    intros Hm. destruct (m !! i) eqn:Hmk; [|by auto].
    apply elem_of_map_img_2 in Hmk. set_solver.
  Qed.

  Lemma map_img_union_inv `{!RelDecision (∈@{SA})} X Y m :
    X ## Y →
    map_img m ≡ X ∪ Y →
    ∃ m1 m2, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ map_img m1 ≡ X ∧ map_img m2 ≡ Y.
  Proof.
    intros Hsep Himg.
    exists (filter (λ '(_,x), x ∈ X) m), (filter (λ '(_,x), x ∉ X) m).
    assert (filter (λ '(_,x), x ∈ X) m ##ₘ filter (λ '(_,x), x ∉ X) m).
    { apply map_disjoint_filter_complement. }
    split_and!.
    - symmetry. apply map_filter_union_complement.
    - done.
    - apply map_img_filter; intros x. split; [|naive_solver].
      intros. destruct (elem_of_map_img_1 m x); set_solver.
    - apply map_img_filter; intros x; split.
      + intros. destruct (elem_of_map_img_1 m x); set_solver.
      + intros (i & ?%elem_of_map_img_2 & ?). set_solver.
  Qed.

  Section leibniz.
    Context `{!LeibnizEquiv SA}.

    Lemma map_img_empty_L : map_img ∅ = ∅.
    Proof. unfold_leibniz. exact map_img_empty. Qed.

    Lemma map_img_empty_iff_L m : map_img m = ∅ ↔ m = ∅.
    Proof. unfold_leibniz. apply map_img_empty_iff. Qed.
    Lemma map_img_empty_inv_L m : map_img m = ∅ → m = ∅.
    Proof. apply map_img_empty_iff_L. Qed.

    Lemma map_img_singleton_L i x : map_img {[ i := x ]} = {[ x ]}.
    Proof. unfold_leibniz. apply map_img_singleton. Qed.

    Lemma map_img_insert_notin_L m i x :
      m !! i = None → map_img (<[i:=x]> m) = {[ x ]} ∪ map_img m.
    Proof. unfold_leibniz. apply map_img_insert_notin. Qed.

    Lemma map_img_union_disjoint_L m1 m2 :
      m1 ##ₘ m2 → map_img (m1 ∪ m2) = map_img m1 ∪ map_img m2.
    Proof. unfold_leibniz. apply map_img_union_disjoint. Qed.

    Lemma map_img_alt_L m : map_img m = list_to_set (map_to_list m).*2.
    Proof. unfold_leibniz. apply map_img_alt. Qed.

    Lemma map_img_singleton_inv_L m i x :
      map_img m = {[ x ]} → m !! i = None ∨ m !! i = Some x.
    Proof. unfold_leibniz. apply map_img_singleton_inv. Qed.

    Lemma map_img_union_inv_L `{!RelDecision (∈@{SA})} X Y m :
      X ## Y →
      map_img m = X ∪ Y →
      ∃ m1 m2, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ map_img m1 = X ∧ map_img m2 = Y.
    Proof. unfold_leibniz. apply map_img_union_inv. Qed.
  End leibniz.

  (** * Set solver instances *)
  Global Instance set_unfold_map_img_empty x :
    SetUnfoldElemOf x (map_img (∅:M A)) False.
  Proof. constructor. by rewrite map_img_empty, elem_of_empty. Qed.
  Global Instance set_unfold_map_img_singleton x i y :
    SetUnfoldElemOf x (map_img ({[i:=y]}:M A)) (x = y).
  Proof. constructor. by rewrite map_img_singleton, elem_of_singleton. Qed.
End img.

Lemma map_img_fmap `{FinMap K M, FinSet A SA, FinSet B SB} (f : A → B) (m : M A) :
  map_img (f <$> m) ≡@{SB} set_map (C:=SA) f (map_img m).
Proof.
  apply set_equiv. intros y. rewrite elem_of_map_img, elem_of_map.
  setoid_rewrite lookup_fmap. setoid_rewrite fmap_Some.
  setoid_rewrite elem_of_map_img. naive_solver.
Qed.
Lemma map_img_fmap_L `{FinMap K M, FinSet A SA, FinSet B SB, !LeibnizEquiv SB}
    (f : A → B) (m : M A) :
  map_img (f <$> m) =@{SB} set_map (C:=SA) f (map_img m).
Proof. unfold_leibniz. apply map_img_fmap. Qed.

Lemma map_img_kmap `{FinMap K M, FinMap K2 M2, FinSet A SA}
    (f : K → K2) `{!Inj (=) (=) f} m :
  map_img (kmap (M2:=M2) f m) ≡@{SA} map_img m.
Proof.
  apply set_equiv. intros x. rewrite !elem_of_map_img.
  setoid_rewrite (lookup_kmap_Some f). naive_solver.
Qed.
Lemma map_img_kmap_L `{FinMap K M, FinMap K2 M2, FinSet A SA, !LeibnizEquiv SA}
    (f : K → K2) `{!Inj (=) (=) f} m :
  map_img (kmap (M2:=M2) f m) =@{SA} map_img m.
Proof. unfold_leibniz. by apply map_img_kmap. Qed.
