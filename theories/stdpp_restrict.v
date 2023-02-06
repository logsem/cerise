From Coq Require Import ssreflect.
From stdpp Require Import countable gmap list.

Section restrict_keys.
  Context {K M D} `{FinMap K M, ElemOf K D, !RelDecision (∈@{D})}.
  Context {A:Type}.

  (** Restrict a map's keys to a given set *)
  Definition restrict_keys (s:D) (m:M A) := filter (fun '(k,_) => k ∈ s) m.

  Lemma restrict_keys_lookup_Some s m k v :
    restrict_keys s m !! k = Some v <-> m !! k = Some v /\ k ∈ s.
  Proof. apply map_filter_lookup_Some. Qed.

  Lemma restrict_keys_lookup_Some_2 s m k v :
    m !! k = Some v -> k ∈ s -> restrict_keys s m !! k = Some v.
  Proof. intros. rewrite restrict_keys_lookup_Some. done. Qed.

  Lemma restrict_keys_lookup_None s m k:
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

  Lemma restrict_keys_lookup_None_2l s m k:
    m !! k = None -> restrict_keys s m !! k = None.
  Proof. intros. rewrite restrict_keys_lookup_None. left. done. Qed.

  Lemma restrict_keys_lookup_None_2r s m k:
    k ∉ s -> restrict_keys s m !! k = None.
  Proof. intros. rewrite restrict_keys_lookup_None. right. done. Qed.

  Lemma restrict_keys_subseteq s m :
    restrict_keys s m ⊆ m.
  Proof. apply map_filter_subseteq. Qed.
End restrict_keys.

Section restrict.
  Context {K M D} `{FinMapDom K M D, !RelDecision (∈@{D})}.
  Context {A B:Type}.

  (** Restrict a map's keys to another map's keys *)
  Definition restrict (ms:M B) (mm: M A) := restrict_keys (dom ms) mm.

  Lemma restrict_lookup_Some m1 m2 k v :
    restrict m1 m2 !! k = Some v <-> m2 !! k = Some v /\ is_Some (m1 !! k).
  Proof. rewrite restrict_keys_lookup_Some elem_of_dom. done. Qed.

  Lemma restrict_lookup_Some_2 m1 m2 k v :
    m2 !! k = Some v -> is_Some(m1 !! k) -> restrict m1 m2 !! k = Some v.
  Proof. intros. rewrite restrict_lookup_Some. done. Qed.

  Lemma restrict_lookup_None m1 m2 k:
    restrict m1 m2 !! k = None <-> m2 !! k = None \/ m1 !! k = None.
  Proof. rewrite restrict_keys_lookup_None not_elem_of_dom. done. Qed.

  Lemma restrict_lookup_None_2l m1 m2 k:
    m2 !! k = None -> restrict m1 m2 !! k = None.
  Proof. intros. rewrite restrict_lookup_None. left. done. Qed.

  Lemma restrict_lookup_None_2r m1 m2 k:
    m1 !! k = None -> restrict m1 m2 !! k = None.
  Proof. intros. rewrite restrict_lookup_None. right. done. Qed.

  Lemma restrict_subseteq m1 m2 :
    restrict m1 m2 ⊆ m2.
  Proof. apply restrict_keys_subseteq. Qed.


End restrict.

Global Instance restrict_idemp
       {K M A D} `{FinMapDom K M D, !RelDecision (∈@{D})}
  : IdemP (=@{M A}) restrict.
Proof.
  intros m. apply map_eq. intros k. destruct (m!!k) eqn:Hm.
  apply (restrict_lookup_Some_2 _ _ _ _ Hm (mk_is_Some _ _ Hm)).
  apply (restrict_lookup_None_2l _ _ _ Hm).
Qed.

(** map_zip ignores keys that aren't shared by both maps *)
Lemma map_zip_filter {K M A B} `{FinMapDom K M D, !RelDecision (∈@{D})} (m1: M A) (m2: M B) :
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
