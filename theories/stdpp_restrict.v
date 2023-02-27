From Coq Require Import ssreflect.
From stdpp Require Import fin_maps fin_map_dom.

Definition restrict {K M} `{FinMap K M}
  {D} (P: K → D → Prop) s `{∀ k, Decision (P k s)}
  {A} (m: M A) :=
  filter (λ '(k,_), P k s) m.

Section restrict.
  Context {K M} `{FinMap K M}.

  Section simple_facts.
    Context {D} (P : K → D → Prop) s `{∀ k, Decision (P k s)}.
    Context {A : Type}.
    Implicit Types (m : M A) (v : A).

    (* In case we feel another definition would be better *)
    Lemma restrict_filter m : restrict P s m = filter (λ '(k,_), P k s) m.
    Proof. reflexivity. Qed.

    Lemma restrict_lookup_Some m k v :
      restrict P s m !! k = Some v ↔ m !! k = Some v ∧ P k s.
    Proof. apply map_filter_lookup_Some. Qed.

    Lemma restrict_lookup_Some_2 m k v :
      m !! k = Some v → P k s → restrict P s m !! k = Some v.
    Proof. intros. rewrite restrict_lookup_Some. done. Qed.

    Lemma restrict_lookup_None m k :
      restrict P s m !! k = None ↔ m !! k = None ∨ ¬ P k s.
    Proof.
      split. intros Hr.
      destruct (m!!k) eqn:Hm.
        destruct (decide (k ∈ s)) as [Heq|Heq].
          rewrite (restrict_lookup_Some_2 m k _ Hm Heq) in Hr. discriminate.
          right. done.
        left. done.
      destruct (restrict P s m !! k) eqn:Hm; [ | reflexivity ].
      apply restrict_lookup_Some in Hm as [Hmk Hp].
      intros [Hmk' | Hp'].
        rewrite -Hmk. exact Hmk'.
        contradiction (Hp' Hp).
    Qed.

    Lemma restrict_lookup_None_2l m k :
      m !! k = None → restrict P s m !! k = None.
    Proof. intros. rewrite restrict_lookup_None. left. done. Qed.

    Lemma restrict_lookup_None_2r m k :
      ¬ P k s → restrict P s m !! k = None.
    Proof. intros. rewrite restrict_lookup_None. right. done. Qed.

    Lemma restrict_subseteq m: restrict P s m ⊆ m.
    Proof. apply map_filter_subseteq. Qed.

    Lemma dom_restrict_subseteq m
      `{∀ A : Type, Dom (M A) D, ElemOf K D, Empty D, Singleton K D,
      Union D, Intersection D, Difference D, !FinMapDom K M D} :
      dom (restrict P s m) ⊆ dom m.
    Proof. apply subseteq_dom, restrict_subseteq. Qed.

    Lemma restrict_lookup m k :
      restrict P s m !! k = (m !! k) ≫= λ v,
      match decide (P k s) with
        |left _ => Some v
        |right _ => None
      end.
    Proof.
      destruct (m!!k) eqn:Hm.
      destruct (decide (P k s)) as [Hk|Hk].
      simpl. rewrite restrict_lookup_Some. done.
      simpl. apply restrict_lookup_None_2r. done.
      simpl. apply restrict_lookup_None_2l. done.
    Qed.

    Lemma restrict_empty: restrict P s (∅:M A) = ∅.
    Proof.
      apply map_eq. intros i. rewrite lookup_empty.
      apply restrict_lookup_None_2l, lookup_empty.
    Qed.

    Lemma restrict_singleton k v :
      restrict P s {[ k:=v ]} = match decide (P k s) with
      |left _ => {[ k:=v ]}
      |right _ => ∅
      end.
    Proof. apply map_filter_singleton. Qed.

    Lemma restrict_union_complement m :
      restrict P s m ∪ restrict (λ k s, ¬ P k s) s m = m.
    Proof. apply map_filter_union_complement. Qed.

    Lemma restrict_empty_not_lookup m k :
      restrict P s m = ∅ → P k s → m!!k = None.
    Proof.
      rewrite map_empty. setoid_rewrite restrict_lookup_None.
      intros Hi HP. destruct (Hi k) as [Hi'|Hi']. exact Hi'.
      contradiction (Hi' HP).
    Qed.

    Lemma restrict_delete m i : restrict P s (delete i m) = delete i (restrict P s m).
    Proof. apply map_filter_delete. Qed.

    Lemma restrict_fmap {B} (f : B → A) (m : M B) :
      restrict P s (f <$> m) = f <$> restrict P s m.
    Proof. apply map_filter_fmap. Qed.

    Lemma dom_restrict_filter_dom
      `{∀ A : Type, Dom (M A) D, FinSet K D, !FinMapDom K M D} m :
      dom (restrict P s m) ≡@{D} filter (λ k, P k s) (dom m).
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
      dom (restrict P s m) = filter (λ k, P k s) (dom m).
    Proof. unfold_leibniz. apply dom_restrict_filter_dom. Qed.
  End simple_facts.

  Lemma restrict_restrict
    {D1 D2} (P1 : K → D1 → Prop) (P2 : K → D2 → Prop) s1 s2
    `{∀ s1 k, Decision (P1 k s1)} `{∀ s2 k, Decision (P2 k s2)}
    {A} (m : M A) :
    restrict P1 s1 (restrict P2 s2 m) = restrict (λ k s, P1 k s1 ∧ P2 k s2) (s1,s2) m.
  Proof. apply map_filter_filter. Qed.

  Lemma restrict_restrict_comm
    {D1 D2} (P1 : K → D1 → Prop) (P2 : K → D2 → Prop) s1 s2
    `{∀ s1 k, Decision (P1 k s1)} `{∀ s2 k, Decision (P2 k s2)}
    {A} (m : M A) :
    restrict P1 s1 (restrict P2 s2 m) = restrict P2 s2 (restrict P1 s1 m).
  Proof.
    rewrite !restrict_restrict.
    apply map_filter_ext. intros. split; intros []; done.
  Qed.

  Lemma restrict_merge
    {D} (P: K → D → Prop) s `{∀ k, Decision (P k s)}
    {A B C} ml mr (f: option A → option B → option C) :
    restrict P s (merge f ml mr) =
    merge f (restrict P s ml) (restrict P s mr).
  Proof.
    apply map_eq. intros k.
    rewrite restrict_lookup !lookup_merge !restrict_lookup.
    destruct (ml!!k); destruct (mr!!k); destruct (decide (P k s)); simpl.
    all: match goal with
    | |- ?x ≫= _ = _ => destruct x; try reflexivity
    | |- _ => reflexivity
    end.
  Qed.

  Lemma restrict_map_zip_with
    {D} (P: K → D → Prop) s `{∀ k, Decision (P k s)}
    {A B C} ml mr (f: A → B → C) :
    restrict P s (map_zip_with f ml mr) =
    map_zip_with f (restrict P s ml) (restrict P s mr).
  Proof. apply restrict_merge. Qed.

  Lemma restrict_difference {A} (s:M A) (m:M A) :
    restrict (λ k s, s!!k = None) s m = m ∖ s.
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

    Definition restrict_set (s : D) {A} (m : M A) := restrict (∈) s m.

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
      {A} s1 s2 (m : M A) :
      restrict_set s1 (restrict_set s2 m) = restrict_set (s1 ∩ s2) m.
    Proof.
      unfold restrict_set.
      specialize (restrict_restrict (∈) (∈) s1 s2 m) as Hx. rewrite Hx. clear Hx.
      rewrite -map_filter_ext. intros. rewrite elem_of_intersection. done.
    Qed.
  End restrict_set.

  (** Another common case: restrict to keys present in another map *)
  Section restrict_map.
    Definition restrict_map {A B} (s : M A) (m : M B) :=
      restrict (λ k s, is_Some(s!!k)) s m.

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
