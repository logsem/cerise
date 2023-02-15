(** This is a concept missing from stdpp, an image/codomain set for maps
    Hopefully it will get merged into stdpp and we can remove this from here.
    https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/444 *)
From Coq Require Import ssreflect.
From stdpp Require Import countable gmap list.

(** The function [img m] should yield the image/codomain of [m]. That is a finite
set of type [D] that contains the values that appear in [m].
[D] is an output of the typeclass, i.e., there can be only one instance per map
type [M]. *)
Class Img (M D : Type) := img: M → D.
Global Hint Mode Img ! - : typeclass_instances.
Global Instance: Params (@img) 3 := {}.
Global Arguments img : clear implicits.
Global Arguments img {_ _ _} !_ / : simpl nomatch, assert.


Class FinMapImg K A M D
  `{Img (M A) D, FMap M,
    ∀ A, Lookup K A (M A), ∀ A, Empty (M A), ∀ A, PartialAlter K A (M A),
    OMap M, Merge M, ∀ A, FinMapToList K A (M A), EqDecision K,
    ElemOf A D, Empty D, Singleton A D,
    Union D, Intersection D, Difference D} := {
  finmap_img_map :> FinMap K M;
  finmap_img_set :> Set_ A D;
  elem_of_img (m:M A) (v:A) : v ∈ img m <-> ∃ (k:K), m !! k = Some v
}.

Section fin_map_img.
  Context `{FinMapImg K A M D}.
  Implicit Types (m:M A) (k:K) (v:A).
  Infix "≡" := (@equiv D _) (at level 70).

  Lemma elem_of_img_2 m k v: m !! k = Some v -> v ∈ img m.
  Proof. intros Hmkv. rewrite elem_of_img. exists k. exact Hmkv. Qed.

  Lemma not_elem_of_img m v: v ∉ img m <-> ∀ k, m !! k ≠ Some v.
  Proof. rewrite elem_of_img. split.
    intros Hm k Hk. contradiction (Hm (ex_intro _ k Hk)).
    intros Hm [k Hk]. contradiction (Hm k Hk).
  Qed.
  Lemma not_elem_of_img_1 m v k: v ∉ img m -> m !! k ≠ Some v.
  Proof. intros Hm. apply not_elem_of_img. exact Hm. Qed.

  Lemma subseteq_img (m1 m2:M A): m1 ⊆ m2 -> img m1 ⊆ img m2.
  Proof.
    intros Hm v Hv. rewrite elem_of_img.
    apply elem_of_img in Hv as [k Hv]. exists k.
    rewrite map_subseteq_spec in Hm.
    apply (Hm k v Hv).
  Qed.

  Lemma img_filter (P : K * A → Prop) `{!∀ x, Decision (P x)} m (X:D):
    (∀ v, v ∈ X ↔ ∃ k, m !! k = Some v ∧ P (k, v)) →
    img (filter P m) ≡ X.
  Proof.
    intros HX i. rewrite elem_of_img HX.
    unfold is_Some. by setoid_rewrite map_filter_lookup_Some.
  Qed.
  Lemma img_filter_subseteq (P : K * A → Prop) `{!∀ x, Decision (P x)} m:
    img (filter P m) ⊆ img m.
  Proof. apply subseteq_img, map_filter_subseteq. Qed.

  Lemma img_empty: img (∅ : M A) ≡ ∅.
  Proof.
    rewrite set_equiv. intros x. split; intros Hempty.
    apply elem_of_img in Hempty. destruct Hempty as [k Hk].
    rewrite lookup_empty in Hk. discriminate.
    rewrite elem_of_empty in Hempty. contradiction Hempty.
  Qed.
  Lemma img_empty_iff m: img m ≡ ∅ ↔ m = ∅.
  Proof.
    split; [|intros ->; by rewrite img_empty].
    intros E. apply map_empty. intros i.
    destruct (m!!i) eqn:Hm. apply elem_of_img_2 in Hm. set_solver.
    reflexivity.
  Qed.
  Lemma img_empty_inv m: img m ≡ ∅ → m = ∅.
  Proof. apply img_empty_iff. Qed.

  Lemma img_insert k v m: img (<[k:=v]> m) ⊆ {[ v ]} ∪ img m.
  Proof.
    intros w Hw. apply elem_of_img in Hw as [k' Hw].
    apply lookup_insert_Some in Hw as [[Hkk' Hvw] | [Hkk' Hmk']].
    apply elem_of_union_l, elem_of_singleton. symmetry. apply Hvw.
    apply elem_of_union_r, elem_of_img. exists k'. apply Hmk'.
  Qed.
  Lemma elem_of_img_insert k v m: v ∈ img (<[k:=v]> m).
  Proof. apply elem_of_img. exists k. apply lookup_insert. Qed.
  Lemma elem_of_img_insert_ne k v w m: v ≠ w -> w ∈ img(<[k:=v]> m) -> w ∈ img m.
  Proof. rewrite !elem_of_img. intros Hv [k' Hk].
    destruct (decide (k=k')) as [Heq|Heq]. rewrite Heq lookup_insert in Hk.
    apply Some_inj in Hk. contradiction (Hv Hk).
    rewrite lookup_insert_ne in Hk. exact Heq. exists k'. exact Hk.
  Qed.
  Lemma img_insert_notin k v m: m!!k = None -> img (<[k:=v]> m) ≡ {[ v ]} ∪ img m.
  Proof.
    intros Hm w. rewrite elem_of_union !elem_of_img elem_of_singleton.
    setoid_rewrite lookup_insert_Some.
    split.
    intros [k' [[Hk Hv] | [Hk Hv]]]. left. done. right. exists k'. done.
    intros [Hv | [k' Hv]]. exists k. left. done. exists k'. right.
    destruct (decide (k=k')) as [Hk|Hk]. simplify_eq. done.
  Qed.

  Lemma img_singleton k v : img ({[ k := v ]} : M A) ≡ {[ v ]}.
  Proof.
    rewrite set_equiv. intros x.
    rewrite elem_of_img. rewrite elem_of_singleton.
    setoid_rewrite lookup_singleton_Some. set_solver.
  Qed.

  Lemma elem_of_img_union m1 m2 v:
    v ∈ img (m1 ∪ m2) ->
    v ∈ img m1 \/ v ∈ img m2.
  Proof.
    intros Hv12.
    (* destruct (elem_of_img (m1 ∪ m2) v) as . *)
    rewrite (elem_of_img (m1 ∪ m2) v) in Hv12.
    destruct Hv12 as [k Hv12].
    destruct (lookup_union_Some_raw m1 m2 k v) as [Hspec _].
    destruct (Hspec Hv12) as [Hm | [_ Hm]].
    left. 2: right.
    all: rewrite elem_of_img; exists k; exact Hm.
  Qed.
  Lemma img_union_subseteq m1 m2: img (m1 ∪ m2) ⊆ img m1 ∪ img m2.
  Proof. intros v Hv. apply elem_of_union, elem_of_img_union. exact Hv. Qed.
  Lemma img_union_subseteq_l m1 m2: img m1 ⊆ img (m1 ∪ m2).
  Proof.
    intros v Hv. apply elem_of_img in Hv as [k Hv].
    rewrite elem_of_img.
    exists k. apply lookup_union_Some_l. apply Hv.
  Qed.

  Lemma img_fmap `{Img (M B) D2, ElemOf B D2, Empty D2, Singleton B D2, Union D2, Intersection D2, Difference D2, !FinMapImg K B M D2}
        `{Elements A D, EqDecision A, !FinSet A D} (f: A -> B) m:
    img (f <$> m) ≡@{D2} set_map f (img m).
  Proof.
    apply set_equiv. intros v. rewrite elem_of_img elem_of_map.
    split. intros [k Hk]. rewrite lookup_fmap in Hk.
    destruct (m!!k) as [a|] eqn:Hm. exists a. split. apply Some_inj in Hk. done.
    apply elem_of_img_2 in Hm. done. discriminate.
    intros [a [Ha Hm]]. apply elem_of_img in Hm as [k Hk]. exists k.
    rewrite lookup_fmap Hk Ha. reflexivity.
  Qed.

  Lemma img_kmap `{Img (M2 A) D, FinMap K2 M2, !FinMapImg K2 A M2 D}
        (f: K -> K2) `{!Inj (=) (=) f} m:
    img (kmap (M2:=M2) f m) ≡ img m.
  Proof.
    apply set_equiv. intros v.
    split; intros Hv; rewrite elem_of_img; apply elem_of_img in Hv as [k Hv].
    apply lookup_kmap_Some in Hv as [k' [Hk' Hv]]. exists k'. done. done.
    exists (f k). rewrite lookup_kmap. done.
  Qed.

  Lemma img_finite m: set_finite (img m).
  Proof.
    induction m using map_ind.
    - rewrite img_empty. apply empty_finite.
    - apply (set_finite_subseteq _ _ (img_insert i x m)).
      apply union_finite. apply singleton_finite. apply IHm.
  Qed.

  Lemma img_list_to_map l:
    (∀ k v v', (k,v) ∈ l -> (k,v') ∈ l -> v = v') ->
    img (list_to_map l : M A) ≡ list_to_set l.*2.
  Proof.
    induction l as [|?? IH].
    - by rewrite img_empty.
    - intros Hl. destruct a as [k v]. simpl.
      assert (IH': img (list_to_map l: M A) ≡ list_to_set l.*2).
      { apply IH. intros k' v' v'' Hv' Hv''. apply (Hl k' v' v''); apply elem_of_list_further; assumption. }
      rewrite -IH'.
      destruct ((list_to_map l : M A)!!k) as [w|] eqn:Hw.
      assert (Hvw: v = w). apply (Hl k). apply elem_of_list_here.
      apply elem_of_list_further. apply elem_of_list_to_map_2. exact Hw.
      rewrite -Hvw in Hw.
      apply set_equiv. intros x. split.
      intros Hx. apply img_insert in Hx. done.
      intros Hx. apply elem_of_union in Hx as [Hv | Hx].
      apply elem_of_singleton in Hv. rewrite Hv. apply elem_of_img_insert.
      apply elem_of_img in Hx as [k' Hx].
      destruct (decide (k=k')). simplify_eq. apply elem_of_img_insert.
      apply elem_of_img. exists k'. rewrite lookup_insert_ne; assumption.
      rewrite img_insert_notin. exact Hw. reflexivity.
  Qed.

  (** Alternative definition of [img] in terms of [map_to_list]. *)
  Lemma img_alt m: img m ≡ list_to_set (map_to_list m).*2.
  Proof.
    rewrite <-(list_to_map_to_list m) at 1.
    rewrite img_list_to_map.
    intros k v v' Hv Hv'. rewrite !elem_of_map_to_list in Hv, Hv'.
    rewrite Hv in Hv'. apply Some_inj. exact Hv'.
    done.
  Qed.

  Lemma img_singleton_inv m v:
    img m ≡ {[ v ]} -> ∀ k, m !! k = None \/ m !! k = Some v.
  Proof.
    intros Hm k. destruct (m!!k) eqn:Hmk.
    right. apply elem_of_img_2 in Hmk. rewrite Hm elem_of_singleton in Hmk.
    rewrite Hmk. reflexivity.
    left. reflexivity.
  Qed.

  Lemma img_union_inv `{!RelDecision (∈@{D})} X Y m:
    X ## Y ->
    img m ≡ X ∪ Y ->
    ∃ m1 m2, m = m1 ∪ m2 /\ m1 ##ₘ m2 /\ img m1 ≡ X /\ img m2 ≡ Y.
  Proof.
    intros Hsep Himg.
    exists (filter (λ '(_,x), x ∈ X) m), (filter (λ '(_,x), x ∉ X) m).
    assert (Hdisj: filter (λ '(_, x), x ∈ X) m ##ₘ filter (λ '(_, x), x ∉ X) m).
    { apply map_disjoint_filter_complement. }
    split_and!.
    - symmetry. apply map_filter_union_complement.
    - apply Hdisj.
    - apply img_filter; intros v; split; [|naive_solver].
      intros Hv. apply (union_subseteq_l X Y) in Hv as Hv'. rewrite -Himg elem_of_img in Hv'.
      destruct Hv' as [k Hk]. exists k. done.
    - apply img_filter; intros v; split.
      + intros Hv.
        apply (union_subseteq_r X Y) in Hv as Hv'. rewrite -Himg elem_of_img in Hv'.
        destruct Hv' as [k Hk]. exists k. split. done.
        destruct (decide (v ∈ X)) as [Hx|Hx]. contradiction (Hsep v Hx Hv). done.
      + intros (k&Hk&Hv). apply elem_of_img_2 in Hk. set_solver.
  Qed.

  Section Leibniz.
    Context `{!LeibnizEquiv D}.

    Lemma img_empty_L: img (@empty (M A) _) = ∅.
    Proof. unfold_leibniz. exact img_empty. Qed.

    Lemma img_empty_iff_L m: img m = ∅ ↔ m = ∅.
    Proof. unfold_leibniz. apply img_empty_iff. Qed.
    Lemma img_empty_inv_L m: img m = ∅ → m = ∅.
    Proof. apply img_empty_iff_L. Qed.

    Lemma img_singleton_L k v: img ({[ k := v ]} : M A) = {[ v ]}.
    Proof. unfold_leibniz. apply img_singleton. Qed.

    Lemma img_insert_notin_L k v m: m!!k=None -> img (<[k:=v]> m) = {[ v ]} ∪ img m.
    Proof. unfold_leibniz. apply img_insert_notin. Qed.

    Lemma img_fmap_L `{Img (M B) D2, ElemOf B D2, Empty D2, Singleton B D2, Union D2, Intersection D2, Difference D2, !FinMapImg K B M D2}
          `{Elements A D, EqDecision A, !FinSet A D, !LeibnizEquiv D2} (f: A -> B) m:
      img (f <$> m) = set_map f (img m).
    Proof. unfold_leibniz. apply img_fmap. Qed.

    Lemma img_kmap_L `{Img (M2 A) D, FinMap K2 M2, !FinMapImg K2 A M2 D}
          (f: K -> K2) `{!Inj (=) (=) f} m:
      img (kmap (M2:=M2) f m) = img m.
    Proof. unfold_leibniz. apply img_kmap. done. Qed.

    Lemma img_list_to_map_L l:
      (∀ k v v', (k,v) ∈ l -> (k,v') ∈ l -> v = v') ->
      img (list_to_map l : M A) = list_to_set l.*2.
    Proof. unfold_leibniz. apply img_list_to_map. Qed.

    Lemma img_alt_L m: img m = list_to_set (map_to_list m).*2.
    Proof. unfold_leibniz. apply img_alt. Qed.

    Lemma img_singleton_inv_L m v:
      img m = {[ v ]} -> ∀ k, m !! k = None \/ m !! k = Some v.
    Proof. unfold_leibniz. apply img_singleton_inv. Qed.

    Lemma img_union_inv_L `{!RelDecision (∈@{D})} X Y m:
      X ## Y ->
      img m = X ∪ Y ->
      ∃ m1 m2, m = m1 ∪ m2 /\ m1 ##ₘ m2 /\ img m1 = X /\ img m2 = Y.
    Proof. unfold_leibniz. apply img_union_inv. Qed.
  End Leibniz.

  (** * Set solver instances *)
  Global Instance set_unfold_img_empty i : SetUnfoldElemOf i (img (∅:M A)) False.
  Proof. constructor. by rewrite img_empty elem_of_empty. Qed.
End fin_map_img.

Global Instance fin_map_img K A M D
  `{FinMapToList K A M, Singleton A D, Empty D, Union D}
: Img M D := map_to_set (fun _ a => a).
Global Instance gmap_img K A
  `{EqDecision K, Countable K, EqDecision A, Countable A}
: Img (gmap K A) (gset A) := fin_map_img K A (gmap K A) (gset A).

Global Instance fin_map_img_spec K A M D
  `{HFinMap:FinMap K M} `{HFinSet:FinSet A D} : FinMapImg K A M D.
Proof.
  split.
  exact HFinMap.
  apply fin_set_set.
  unfold img, fin_map_img.
  intros m v.
  rewrite elem_of_map_to_set.
  split.
  intros [k [v' [mk_v' v'_v]]]. exists k. rewrite v'_v in mk_v'. exact mk_v'.
  intros [k mk_v]. exists k. exists v. split. exact mk_v. reflexivity.
Qed.

Global Instance gmap_imp_spec K A
 `{EqDecision K, Countable K, EqDecision A, Countable A}
: FinMapImg K A (gmap K) (gset A) := fin_map_img_spec K A (gmap K) (gset A).
