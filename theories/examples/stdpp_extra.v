From stdpp Require Import countable.
From iris.base_logic Require Import invariants.

Lemma elements_list_to_set {A} `{Countable A} (l: list A) :
  NoDup l →
  elements (list_to_set l : gset A) ≡ₚ l.
Proof.
  induction l.
  - intros. rewrite list_to_set_nil elements_empty //.
  - intros ND. rewrite list_to_set_cons elements_union_singleton.
    + rewrite IHl //. eauto using NoDup_cons_12.
    + rewrite not_elem_of_list_to_set. by apply NoDup_cons_11.
Qed.

Lemma list_to_map_lookup_is_Some {A B} `{Countable A, EqDecision A} (l: list (A * B)) (a: A) :
  is_Some ((list_to_map l : gmap A B) !! a) ↔ a ∈ l.*1.
Proof.
  induction l.
  - cbn. split; by inversion 1.
  - cbn. rewrite lookup_insert_is_Some' elem_of_cons.
    split; intros [HH|HH]; eauto; rewrite -> IHl in *; auto.
Qed.

Lemma zip_app {A B} (l1 l1': list A) (l2 l2' : list B) :
  length l1 = length l2 ->
  zip (l1 ++ l1') (l2 ++ l2') = zip l1 l2 ++ zip l1' l2'.
Proof.
  revert l2. induction l1;intros l2 Hlen.
  - destruct l2;[|inversion Hlen]. done.
  - destruct l2;[inversion Hlen|]. simpl.
    f_equiv. auto. 
Qed.

Lemma length_zip_l {A B} (l1: list A) (l2: list B) :
  length l1 ≤ length l2 → length (zip l1 l2) = length l1.
Proof.
  revert l2. induction l1; intros l2 Hl2; auto.
  destruct l2; cbn in Hl2. exfalso; lia.
  cbn. rewrite IHl1; auto. lia.
Qed.

Lemma list_filter_app { A: Type } (P: A -> Prop) `{ forall x, Decision (P x) } l1 l2:
  @list_filter _ P _ (l1 ++ l2) = @list_filter _ P _ l1 ++ @list_filter _ P _ l2.
Proof.
  induction l1; simpl; auto.
  destruct (decide (P a)); auto.
  unfold filter. rewrite IHl1. auto.
Qed.

Lemma list_filter_forall { A: Type } (P: A -> Prop) `{ forall x, Decision (P x) } l:
  Forall P l ->
  @list_filter _ P _ l = l.
Proof.
  induction 1; auto.
  simpl. destruct (decide (P x)); rewrite /filter; try congruence.
Qed.
