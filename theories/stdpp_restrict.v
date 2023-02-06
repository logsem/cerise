From Coq Require Import ssreflect.
From stdpp Require Import countable gmap list.

Section restrict_keys.
  Context {K M D} `{FinMap K M, ElemOf K D, !RelDecision (∈@{D})}.

  (** Restrict a map's keys to a given set *)
  Definition restrict_keys {A} (s:D) (m:M A) := filter (fun '(k,_) => k ∈ s) m.

  Lemma restrict_keys_filter {A} s (m:M A) :
    restrict_keys s m = filter (fun '(k,_) => k ∈ s) m.
  Proof. reflexivity. Qed.

  Lemma restrict_keys_lookup_Some {A} s (m:M A) k v:
    restrict_keys s m !! k = Some v <-> m !! k = Some v /\ k ∈ s.
  Proof. apply map_filter_lookup_Some. Qed.

  Lemma restrict_keys_lookup_Some_2 {A} s (m:M A) k v:
    m !! k = Some v -> k ∈ s -> restrict_keys s m !! k = Some v.
  Proof. intros. rewrite restrict_keys_lookup_Some. done. Qed.

  Lemma restrict_keys_lookup_None {A} s (m:M A) k:
    restrict_keys s m !! k = None <-> m !! k = None \/ k ∉ s.
  Proof.
    split. intros Hr.
    destruct (m!!k) eqn:Hm.
      destruct (decide (k ∈ s)) as [Heq|Heq].
        rewrite (restrict_keys_lookup_Some_2 _ m k _ Hm Heq) in Hr. discriminate.
        right. done.
      left. done.
    destruct (restrict_keys s m !! k) eqn:Hm; [ | reflexivity ].
    apply restrict_keys_lookup_Some in Hm as [Hmk Hp].
    intros [Hmk' | Hp'].
      rewrite -Hmk. exact Hmk'.
      contradiction (Hp' Hp).
  Qed.

  Lemma restrict_keys_lookup_None_2l {A} s (m:M A) k:
    m !! k = None -> restrict_keys s m !! k = None.
  Proof. intros. rewrite restrict_keys_lookup_None. left. done. Qed.

  Lemma restrict_keys_lookup_None_2r {A} s (m:M A) k:
    k ∉ s -> restrict_keys s m !! k = None.
  Proof. intros. rewrite restrict_keys_lookup_None. right. done. Qed.

  Lemma restrict_keys_subseteq {A} s (m:M A) :
    restrict_keys s m ⊆ m.
  Proof. apply map_filter_subseteq. Qed.

  Lemma restrict_keys_lookup {A} s (m:M A) k :
    restrict_keys s m !! k = (m !! k) ≫= λ v,
    match decide (k ∈ s) with
      |left _ => Some v
      |right _ => None
    end.
  Proof.
    destruct (m!!k) eqn:Hm.
    destruct (decide (k ∈ s)) as [Hk|Hk].
    simpl. rewrite restrict_keys_lookup_Some. done.
    simpl. apply restrict_keys_lookup_None_2r. done.
    simpl. apply restrict_keys_lookup_None_2l. done.
  Qed.

  Lemma restrict_keys_restrict_keys `{Empty D, Singleton K D,
    Union D, Intersection D, Difference D, !Set_ K D}
    {A} s s' (m:M A) :
    restrict_keys s (restrict_keys s' m) = restrict_keys (s ∩ s') m.
  Proof.
    unfold restrict_keys.
    rewrite map_filter_filter -map_filter_ext.
    intros. rewrite elem_of_intersection. done.
  Qed.

  Lemma restrict_keys_merge {A B C} s ml mr (f: option A -> option B -> option C) :
    restrict_keys s (merge f ml mr) =
    merge f (restrict_keys s ml) (restrict_keys s mr).
  Proof.
    apply map_eq. intros k.
    rewrite restrict_keys_lookup !lookup_merge !restrict_keys_lookup.
    destruct (ml!!k); destruct (mr!!k); destruct (decide (k∈ s)); simpl.
    all: match goal with
    | |- ?x ≫= _ = _ => destruct x; try reflexivity
    | |- _ => reflexivity
    end.
  Qed.

  Lemma restrict_keys_map_zip_with {A B C} s ml mr (f: A -> B -> C) :
    restrict_keys s (map_zip_with f ml mr) =
    map_zip_with f (restrict_keys s ml) (restrict_keys s mr).
  Proof. apply restrict_keys_merge. Qed.

  Lemma dom_restrict_keys_subseteq_l
    `{∀ A : Type, Dom (M A) D, Empty D, Singleton K D,
      Union D, Intersection D, Difference D, !FinMapDom K M D}
    {A} s (m:M A) :
    dom (restrict_keys s m) ⊆ s.
  Proof.
    intros x Hx. apply elem_of_dom in Hx as [y Hx].
    apply restrict_keys_lookup_Some in Hx as [_ Hx]. exact Hx.
  Qed.

  Lemma dom_restrict_keys_subseteq_r
    `{∀ A : Type, Dom (M A) D, Empty D, Singleton K D,
      Union D, Intersection D, Difference D, !FinMapDom K M D}
    {A} s (m:M A) :
    dom (restrict_keys s m) ⊆ dom m.
  Proof. apply subseteq_dom. apply restrict_keys_subseteq. Qed.
End restrict_keys.

Section restrict.
  Context {K M D} `{FinMapDom K M D, !RelDecision (∈@{D})}.

  (** Restrict m to only contain s's keys  *)
  Definition restrict {A B} (s:M A) (m: M B) := restrict_keys (dom s) m.

  Lemma restrict_lookup_Some {A B} (s:M A) (m: M B) k v :
    restrict s m !! k = Some v <-> m !! k = Some v /\ is_Some (s !! k).
  Proof. rewrite restrict_keys_lookup_Some elem_of_dom. done. Qed.

  Lemma restrict_lookup_Some_2 {A B} (s:M A) (m: M B) k v :
    m !! k = Some v -> is_Some(s !! k) -> restrict s m !! k = Some v.
  Proof. intros. rewrite restrict_lookup_Some. done. Qed.

  Lemma restrict_lookup_None {A B} (s:M A) (m: M B) k:
    restrict s m !! k = None <-> m !! k = None \/ s !! k = None.
  Proof. rewrite restrict_keys_lookup_None not_elem_of_dom. done. Qed.

  Lemma restrict_lookup_None_2l {A B} (s:M A) (m: M B) k:
    m !! k = None -> restrict s m !! k = None.
  Proof. intros. rewrite restrict_lookup_None. left. done. Qed.

  Lemma restrict_lookup_None_2r {A B} (s:M A) (m: M B) k:
    s !! k = None -> restrict s m !! k = None.
  Proof. intros. rewrite restrict_lookup_None. right. done. Qed.

  Lemma restrict_subseteq {A B} (s:M A) (m: M B) :
    restrict s m ⊆ m.
  Proof. apply restrict_keys_subseteq. Qed.

  Lemma dom_restrict {A B} (s:M A) (m: M B) :
    dom (restrict s m) ≡@{D} dom s ∩ dom m.
  Proof.
    rewrite set_equiv. intros k.
    rewrite elem_of_intersection !elem_of_dom.
    split.
    - intros [v Hv]. apply restrict_lookup_Some in Hv as [Hv2 Hv1].
      apply mk_is_Some in Hv2. done.
    - intros [Hv1 [v Hv2]]. exists v.
      rewrite restrict_keys_lookup_Some elem_of_dom.
      done.
  Qed.

  Lemma dom_restrict_L `{!LeibnizEquiv D} {A B} (s:M A) (m: M B) :
    dom (restrict s m) = dom s ∩ dom m.
  Proof. unfold_leibniz. apply dom_restrict. Qed.

  Lemma restrict_lookup {A B} (s:M A) (m: M B) k:
    restrict s m !! k = m !! k ≫= λ v, s !! k ≫= λ _, Some v.
  Proof.
    rewrite restrict_keys_lookup.
    destruct (m!!k); simpl. destruct (s!!k) eqn:Hm1;
    destruct (decide (k ∈ dom s)) as [Heq|Heq].
    reflexivity.
    rewrite not_elem_of_dom Hm1 in Heq. discriminate.
    rewrite elem_of_dom Hm1 in Heq. contradiction (is_Some_None Heq).
    reflexivity.
    reflexivity.
  Qed.

  Global Instance restrict_idemp {A} : IdemP (=@{M A}) restrict.
  Proof.
    intros m. apply map_eq. intros k. destruct (m!!k) eqn:Hm.
    apply (restrict_lookup_Some_2 _ _ _ _ Hm (mk_is_Some _ _ Hm)).
    apply (restrict_lookup_None_2l _ _ _ Hm).
  Qed.

  Lemma restrict_merge {A B B' B''} (s:M A) ml mr (f: option B -> option B' -> option B'') :
    restrict s (merge f ml mr) =
    merge f (restrict s ml) (restrict s mr).
  Proof. apply restrict_keys_merge. Qed.

  Lemma restrict_map_zip_with {A B B' B''} (s:M A) ml mr (f: B -> B' -> B'') :
    restrict s (map_zip_with f ml mr) =
    map_zip_with f (restrict s ml) (restrict s mr).
  Proof. apply restrict_merge. Qed.

  Lemma dom_restrict_subseteq_l {A B} (s:M A) (m:M B):
    dom (restrict s m) ⊆ dom s.
  Proof.
    intros x Hx. apply elem_of_dom in Hx as [y Hx].
    apply restrict_keys_lookup_Some in Hx as [_ Hx]. exact Hx.
  Qed.

  Lemma dom_restrict_subseteq_r {A B} (s:M A) (m:M B):
    dom (restrict s m) ⊆ dom m.
  Proof. apply subseteq_dom. apply restrict_subseteq. Qed.
End restrict.


(** map_zip ignores keys that aren't shared by both maps *)
Lemma map_zip_minimal {K M A B} `{FinMapDom K M D, !RelDecision (∈@{D})} (m1: M A) (m2: M B) :
  map_zip m1 m2 =
  map_zip (restrict m2 m1) (restrict m1 m2).
Proof.
  apply map_eq. intros k.
  rewrite !map_lookup_zip_with.
  destruct (m1 !! k) as [v1|] eqn:Hm1;
  destruct (m2 !! k) as [v2|] eqn:Hm2; simpl.
  - rewrite (restrict_lookup_Some_2 _ _ _ _ Hm2 (mk_is_Some _ _ Hm1)).
    rewrite (restrict_lookup_Some_2 _ _ _ _ Hm1 (mk_is_Some _ _ Hm2)).
    reflexivity.
  - rewrite (restrict_lookup_None_2r _ _ _ Hm2). reflexivity.
  - rewrite (restrict_lookup_None_2l _ _ _ Hm1). reflexivity.
  - rewrite (restrict_lookup_None_2r _ _ _ Hm2). reflexivity.
Qed.
