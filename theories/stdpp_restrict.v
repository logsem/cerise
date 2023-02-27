From Coq Require Import ssreflect.
From stdpp Require Import fin_maps fin_map_dom.

(** [restrict P m] is the sub-map of [m] that only contains keys that verify [P] *)
Definition restrict {K M} `{FinMap K M}
  (P : K → Prop) `{∀ k, Decision (P k)}
  {A} (m: M A) :=
  filter (λ '(k,_), P k) m.

(** [restrict_set s m] is the sub-map of [m] that only contains keys in set [s] *)
Definition restrict_set {K M D} `{FinMap K M, ElemOf K D, !RelDecision (∈@{D})}
  (s : D) {A} (m : M A) := restrict (.∈ s) m.

(** [restrict_map s m] is the sub-map of [m] that only contains keys
    that are also in map [s] *)
Definition restrict_map {K M} `{FinMap K M}
  {A B} (s : M A) (m : M B) :=
  restrict (λ k, is_Some(s!!k)) m.

Section restrict.
  Context {K M} `{FinMap K M}.

  Section simple_facts.
    Context (P : K → Prop) `{∀ k, Decision (P k)}.
    Context {A : Type}.
    Implicit Types (m : M A) (v : A) (k : K).

    (* In case we feel another definition would be better *)
    Lemma restrict_filter m : restrict P m = filter (λ '(k,_), P k) m.
    Proof. reflexivity. Qed.

    Lemma restrict_lookup_Some m k v :
      restrict P m !! k = Some v ↔ m !! k = Some v ∧ P k.
    Proof. apply map_filter_lookup_Some. Qed.

    Lemma restrict_lookup_Some_2 m k v :
      m !! k = Some v → P k → restrict P m !! k = Some v.
    Proof. intros. rewrite restrict_lookup_Some. done. Qed.

    Lemma restrict_lookup_None m k :
      restrict P m !! k = None ↔ m !! k = None ∨ ¬ P k.
    Proof.
      split. intros Hr.
      destruct (m!!k) eqn:Hm.
        destruct (decide (P k)) as [Heq|Heq].
          rewrite (restrict_lookup_Some_2 m k _ Hm Heq) in Hr. discriminate.
          right. done.
        left. done.
      destruct (restrict P m !! k) eqn:Hm; [ | reflexivity ].
      apply restrict_lookup_Some in Hm as [Hmk Hp].
      intros [Hmk' | Hp'].
        rewrite -Hmk. exact Hmk'.
        contradiction (Hp' Hp).
    Qed.

    Lemma restrict_lookup_None_2l m k :
      m !! k = None → restrict P m !! k = None.
    Proof. intros. rewrite restrict_lookup_None. left. done. Qed.

    Lemma restrict_lookup_None_2r m k :
      ¬ P k → restrict P m !! k = None.
    Proof. intros. rewrite restrict_lookup_None. right. done. Qed.

    Lemma restrict_subseteq m : restrict P m ⊆ m.
    Proof. apply map_filter_subseteq. Qed.

    Lemma dom_restrict_subseteq m
      `{∀ A : Type, Dom (M A) D, ElemOf K D, Empty D, Singleton K D,
      Union D, Intersection D, Difference D, !FinMapDom K M D} :
      dom (restrict P m) ⊆ dom m.
    Proof. apply subseteq_dom, restrict_subseteq. Qed.

    Lemma restrict_lookup m k :
      restrict P m !! k = (m !! k) ≫= λ v,
      match decide (P k) with
        |left _ => Some v
        |right _ => None
      end.
    Proof.
      destruct (m!!k) eqn:Hm.
      destruct (decide (P k)) as [Hk|Hk].
      simpl. rewrite restrict_lookup_Some. done.
      simpl. apply restrict_lookup_None_2r. done.
      simpl. apply restrict_lookup_None_2l. done.
    Qed.

    Lemma restrict_empty: restrict P (∅ : M A) = ∅.
    Proof.
      apply map_eq. intros i. rewrite lookup_empty.
      apply restrict_lookup_None_2l, lookup_empty.
    Qed.

    Lemma restrict_singleton k v :
      restrict P {[ k:=v ]} = match decide (P k) with
      |left _ => {[ k:=v ]}
      |right _ => ∅
      end.
    Proof. apply map_filter_singleton. Qed.

    Lemma restrict_union_complement m :
      restrict P m ∪ restrict (λ k, ¬ P k) m = m.
    Proof. apply map_filter_union_complement. Qed.

    Lemma restrict_empty_not_lookup m k :
      restrict P m = ∅ → P k → m!!k = None.
    Proof.
      rewrite map_empty. setoid_rewrite restrict_lookup_None.
      intros Hi HP. destruct (Hi k) as [Hi'|Hi']. exact Hi'.
      contradiction (Hi' HP).
    Qed.

    Lemma restrict_delete m i : restrict P (delete i m) = delete i (restrict P m).
    Proof. apply map_filter_delete. Qed.

    Lemma restrict_fmap {B} (f : B → A) (m : M B) :
      restrict P (f <$> m) = f <$> restrict P m.
    Proof. apply map_filter_fmap. Qed.

    Lemma dom_restrict_filter_dom
      `{∀ A : Type, Dom (M A) D, FinSet K D, !FinMapDom K M D} m :
      dom (restrict P m) ≡@{D} filter P (dom m).
    Proof.
      apply set_equiv. intros k.
      split; rewrite elem_of_filter !elem_of_dom.
      - intros [v Hv]. apply restrict_lookup_Some in Hv as [Hm Hp].
        split; done.
      - intros [Hv1 [v Hv2]]. exists v.
        rewrite restrict_lookup_Some. done.
    Qed.
    Lemma dom_restrict_filter_dom_L
      `{∀ A : Type, Dom (M A) D, FinSet K D, !FinMapDom K M D, !LeibnizEquiv D} m :
      dom (restrict P m) = filter P (dom m).
    Proof. unfold_leibniz. apply dom_restrict_filter_dom. Qed.
  End simple_facts.

  Lemma restrict_restrict
    (P Q : K → Prop) `{∀ k, Decision (P k)} `{∀ k, Decision (Q k)}
    {A} (m : M A) :
    restrict P (restrict Q m) = restrict (λ k, P k ∧ Q k) m.
  Proof. apply map_filter_filter. Qed.

  Lemma restrict_restrict_comm
    (P Q : K → Prop) `{∀ k, Decision (P k)} `{∀ k, Decision (Q k)}
    {A} (m : M A) :
    restrict P (restrict Q m) = restrict Q (restrict P m).
  Proof. apply map_filter_comm. Qed.

  Lemma restrict_merge
    (P : K → Prop) `{∀ k, Decision (P k)}
    {A B C} ml mr (f : option A → option B → option C) :
    restrict P (merge f ml mr) =
    merge f (restrict P ml) (restrict P mr).
  Proof.
    apply map_eq. intros k.
    rewrite restrict_lookup !lookup_merge !restrict_lookup.
    destruct (ml!!k); destruct (mr!!k); destruct (decide (P k)); simpl.
    all: match goal with
    | |- ?x ≫= _ = _ => destruct x; try reflexivity
    | |- _ => reflexivity
    end.
  Qed.

  Lemma restrict_map_zip_with
    (P : K → Prop) `{∀ k, Decision (P k)}
    {A B C} ml mr (f : A → B → C) :
    restrict P (map_zip_with f ml mr) =
    map_zip_with f (restrict P ml) (restrict P mr).
  Proof. apply restrict_merge. Qed.

  Lemma restrict_difference {A} (s : M A) (m : M A) :
    restrict (λ k, s!!k = None) m = m ∖ s.
  Proof.
    apply map_eq. intros k.
    rewrite restrict_lookup.
    destruct (m!!k) eqn:Hm. destruct (s!!k) eqn:Hs; simpl; symmetry.
    rewrite lookup_difference_None. rewrite Hs. right. done.
    rewrite lookup_difference_Some. split; done.
    simpl. symmetry. rewrite lookup_difference_None. left. done.
  Qed.

  (** Common case: restrict keys to elements of a set *)
  Section restrict_set.
    Context `{ElemOf K D, !RelDecision (∈@{D})}.

    Lemma dom_restrict_set_subseteq
      `{∀ A : Type, Dom (M A) D, Empty D, Singleton K D,
        Union D, Intersection D, Difference D, !FinMapDom K M D}
      {A} s (m : M A) :
      dom (restrict_set s m) ⊆ s.
    Proof.
      intros x Hx. apply elem_of_dom in Hx as [y Hx].
      apply restrict_lookup_Some in Hx as [_ Hx]. exact Hx.
    Qed.

    Lemma dom_restrict_set
      `{∀ A : Type, Dom (M A) D, Empty D, Singleton K D,
        Union D, Intersection D, Difference D, !FinMapDom K M D}
      {A} s (m : M A) :
      dom (restrict_set s m) ≡@{D} s ∩ dom m.
    Proof.
      apply set_equiv. intros k.
      rewrite elem_of_intersection !elem_of_dom.
      split.
      - intros [v Hv]. apply restrict_lookup_Some in Hv as [Hv2 Hv1].
        apply mk_is_Some in Hv2. done.
      - intros [Hv1 [v Hv2]]. exists v.
        rewrite restrict_lookup_Some. done.
    Qed.
    Lemma dom_restrict_set_L `{!LeibnizEquiv D}
      `{∀ A : Type, Dom (M A) D, Empty D, Singleton K D,
        Union D, Intersection D, Difference D, !FinMapDom K M D}
      {A} s (m : M A) :
      dom (restrict_set s m) = s ∩ dom m.
    Proof. unfold_leibniz. apply dom_restrict_set. Qed.

    Lemma restrict_set_restrict_set `{Empty D, Singleton K D,
      Union D, Intersection D, Difference D, !Set_ K D}
      {A} (s1 s2 : D) (m : M A) :
      restrict_set s1 (restrict_set s2 m) = restrict_set (s1 ∩ s2) m.
    Proof.
      unfold restrict_set.
      specialize (restrict_restrict (.∈ s1) (.∈ s2) m) as Hx. rewrite Hx.
      rewrite -map_filter_ext. intros. rewrite elem_of_intersection. done.
    Qed.
  End restrict_set.

  (** Another common case: restrict to keys present in another map *)
  Section restrict_map.
    Global Instance restrict_idemp {A} : IdemP (=@{M A}) restrict_map.
    Proof. intros m. apply map_filter_id. intros k v. done. Qed.

    Context `{∀ A : Type, Dom (M A) D, ElemOf K D, Empty D, Singleton K D,
      Union D, Intersection D, Difference D, !FinMapDom K M D, !RelDecision (∈@{D})}.

    Lemma restrict_map_restrict_set {A B} (s : M A) (m : M B) :
      restrict_map s m = restrict_set (dom s) m.
    Proof. apply map_filter_ext. intros. rewrite elem_of_dom. reflexivity. Qed.

    Lemma dom_restrict_map {A B} (s : M A) (m : M B) :
      dom (restrict_map s m) ≡@{D} dom s ∩ dom m.
    Proof. rewrite restrict_map_restrict_set. apply dom_restrict_set. Qed.
    Lemma dom_restrict_map_L `{!LeibnizEquiv D} {A B} (s:M A) (m: M B) :
      dom (restrict_map s m) = dom s ∩ dom m.
    Proof. unfold_leibniz. apply dom_restrict_map. Qed.

    Lemma dom_restrict_map_subseteq {A B} (s : M A) (m : M B) :
      dom (restrict_map s m) ⊆ dom s.
    Proof. rewrite restrict_map_restrict_set. apply dom_restrict_set_subseteq. Qed.
  End restrict_map.
End restrict.


(** map_zip ignores keys that aren't shared by both maps *)
Lemma map_zip_with_minimal {K M A B C} `{FinMapDom K M D, !RelDecision (∈@{D})}
  (m1 : M A) (m2 : M B) (f : A → B → C) :
  map_zip_with f m1 m2 =
  map_zip_with f (restrict_map m2 m1) (restrict_map m1 m2).
Proof.
  apply map_eq. intros k.
  rewrite !map_lookup_zip_with !restrict_lookup.
  destruct (m1 !! k) as [v1|] eqn:Hm1;
  destruct (m2 !! k) as [v2|] eqn:Hm2; reflexivity.
Qed.
