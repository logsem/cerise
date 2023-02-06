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

  Lemma img_union:
    ∀ (m1 m2:M A) (v:A),
    v ∈ img (m1 ∪ m2) ->
    v ∈ img m1 \/ v ∈ img m2.
  Proof.
    intros m1 m2 v Hv12.
    (* destruct (elem_of_img (m1 ∪ m2) v) as . *)
    rewrite (elem_of_img (m1 ∪ m2) v) in Hv12.
    destruct Hv12 as [k Hv12].
    destruct (lookup_union_Some_raw m1 m2 k v) as [Hspec _].
    destruct (Hspec Hv12) as [Hm | [_ Hm]].
    left. 2: right.
    all: rewrite elem_of_img; exists k; exact Hm.
  Qed.

  Lemma img_union_l:
    ∀ (m1 m2:M A), img m1 ⊆ img (m1 ∪ m2).
  Proof.
    intros m1 m2 v Hv.
    apply elem_of_img in Hv as [k Hv].
    rewrite elem_of_img.
    exists k. apply lookup_union_Some_l. apply Hv.
  Qed.

  Lemma img_empty:
    img (@empty (M A) _) ≡@{D} ∅.
  Proof.
    rewrite set_equiv.
    intros x.
    split; intros Hempty.
    apply elem_of_img in Hempty. destruct Hempty as [k Hk].
    rewrite lookup_empty in Hk. discriminate.
    rewrite elem_of_empty in Hempty. contradiction Hempty.
  Qed.

  Lemma img_singleton (k:K) (v:A) : img ({[ k := v ]} : M A) ≡@{D} {[ v ]}.
  Proof.
    rewrite set_equiv. intros x.
    rewrite elem_of_img. rewrite elem_of_singleton.
    setoid_rewrite lookup_singleton_Some. set_solver.
  Qed.

  Lemma img_insert (k:K) (v:A) (m:M A) : img (<[k:=v]> m) ⊆ {[ v ]} ∪ img m.
  Proof.
    intros w Hw. apply elem_of_img in Hw as [k' Hw].
    apply lookup_insert_Some in Hw as [[Hkk' Hvw] | [Hkk' Hmk']].
    apply elem_of_union_l, elem_of_singleton. symmetry. apply Hvw.
    apply elem_of_union_r, elem_of_img. exists k'. apply Hmk'.
  Qed.

  Lemma elem_of_img_insert (k:K) (v:A) (m:M A) : v ∈ img (<[k:=v]> m).
  Proof. apply elem_of_img. exists k. apply lookup_insert. Qed.

  Lemma img_empty_L `{!LeibnizEquiv D}:
    img (@empty (M A) _) = ∅.
  Proof. unfold_leibniz. exact img_empty. Qed.

  Lemma img_singleton_L `{!LeibnizEquiv D} (k:K) (v:A) : img ({[ k := v ]} : M A) = {[ v ]}.
  Proof. unfold_leibniz. apply img_singleton. Qed.
End fin_map_img.

Global Instance fin_map_img K A M D
  `{FinMapToList K A M, Singleton A D, Empty D, Union D}
: Img M D := map_to_set (fun _ a => a).
Global Instance gmap_img K A
  `{EqDecision K, Countable K, EqDecision A, Countable A}
: Img (gmap K A) (gset A) := fin_map_img K A (gmap K A) (gset A).

Lemma elem_of_img_rev {K A M D} `{FinMapImg K A M D} :
  ∀ (m:M A) (k:K) (v:A), m !! k = Some v -> v ∈ img m.
Proof.
  intros m k v Hmkv. rewrite elem_of_img. exists k. exact Hmkv.
Qed.

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
