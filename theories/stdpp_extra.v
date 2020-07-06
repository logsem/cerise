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

Lemma elem_of_gmap_dom {K V : Type} `{EqDecision K} `{Countable K}
      (m : gmap K V) (i : K) :
  is_Some (m !! i) ↔ i ∈ dom (gset K) m.
Proof.
  split.
  - intros [x Hsome].
    apply elem_of_dom. eauto.
  - intros Hin. by apply elem_of_dom in Hin.
Qed.

Lemma dom_map_imap_full {K A B}
      `{Countable A, EqDecision A, Countable B, EqDecision B, Countable K, EqDecision K}
      (f: K -> A -> option B) (m: gmap K A):
  (∀ k a, m !! k = Some a → is_Some (f k a)) →
  dom (gset K) (map_imap f m) = dom (gset K) m.
Proof.
  intros Hf.
  apply elem_of_equiv_L. intros k.
  rewrite -!elem_of_gmap_dom map_lookup_imap.
  destruct (m !! k) eqn:Hmk.
  - destruct (Hf k a Hmk) as [? Hfk]. cbn. rewrite Hfk. split; eauto.
  - cbn. split; inversion 1; congruence.
Qed.

Lemma dom_list_to_map_singleton {K V: Type} `{EqDecision K, Countable K} (x:K) (y:V):
  dom (gset K) (list_to_map [(x, y)] : gmap K V) = list_to_set [x].
Proof. rewrite dom_insert_L /= dom_empty_L. set_solver. Qed.

Lemma list_to_set_disj {A} `{Countable A, EqDecision A} (l1 l2: list A) :
  l1 ## l2 → (list_to_set l1: gset A) ## list_to_set l2.
Proof.
  intros * HH. rewrite elem_of_disjoint. intros x.
  rewrite !elem_of_list_to_set. rewrite elem_of_disjoint in HH |- *. eauto.
Qed.
