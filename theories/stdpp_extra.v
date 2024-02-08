From Coq Require Import ssreflect.
From stdpp Require Import countable gmap list.


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

Lemma list_filter_forall { A: Type } (P: A -> Prop) `{ forall x, Decision (P x) } l:
  Forall P l ->
  @list_filter _ P _ l = l.
Proof.
  induction 1; auto.
  simpl. destruct (decide (P x)); rewrite /filter; try congruence.
Qed.

Lemma dom_list_to_map_singleton {K V: Type} `{EqDecision K, Countable K} (x:K) (y:V):
  dom (list_to_map [(x, y)] : gmap K V) = list_to_set [x].
Proof. rewrite dom_insert_L /= dom_empty_L. set_solver. Qed.

Lemma list_to_set_disj {A} `{Countable A, EqDecision A} (l1 l2: list A) :
  l1 ## l2 → (list_to_set l1: gset A) ## list_to_set l2.
Proof.
  intros * HH. rewrite elem_of_disjoint. intros x.
  rewrite !elem_of_list_to_set. rewrite elem_of_disjoint in HH |- *. eauto.
Qed.

Lemma map_to_list_fst {A B : Type} `{EqDecision A, Countable A} (m : gmap A B) i :
  i ∈ (map_to_list m).*1 ↔ (∃ x, (i,x) ∈ (map_to_list m)).
Proof.
  split.
  - intros Hi.
    destruct (m !! i) eqn:Hsome.
    + exists b. by apply elem_of_map_to_list.
    + rewrite -(list_to_map_to_list m) in Hsome.
      eapply not_elem_of_list_to_map in Hsome. done.
  - intros [x Hix].
    apply elem_of_list_fmap.
    exists (i,x). auto.
Qed.

Lemma drop_S':
    forall A l n (a: A) l',
      drop n l = a::l' ->
      drop (S n) l = l'.
Proof.
  induction l; intros * HH.
  - rewrite drop_nil in HH. inversion HH.
  - simpl. destruct n.
    + rewrite drop_0 in HH. inversion HH.
      reflexivity.
    + simpl in HH. eapply IHl; eauto.
Qed.

Lemma disjoint_nil_l {A : Type} `{EqDecision A} (a : A) (l2 : list A) :
  [] ## l2.
Proof.
  apply elem_of_disjoint. intros x Hcontr. inversion Hcontr.
Qed.

Lemma disjoint_nil_r {A : Type} `{EqDecision A} (a : A) (l2 : list A) :
  l2 ## [].
Proof.
  apply elem_of_disjoint. intros x Hl Hcontr. inversion Hcontr.
Qed.

Lemma disjoint_cons {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
  a :: l1 ## l2 → a ∉ l2.
Proof.
  rewrite elem_of_disjoint =>Ha.
  assert (a ∈ a :: l1) as Hs; [apply elem_of_cons;auto;apply elem_of_nil|].
  specialize (Ha a Hs). done.
Qed.

Lemma disjoint_weak {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
  a :: l1 ## l2 → l1 ## l2.
Proof.
  rewrite elem_of_disjoint =>Ha a' Hl1 Hl2.
  assert (a' ∈ a :: l1) as Hs; [apply elem_of_cons;auto;apply elem_of_nil|].
  specialize (Ha a' Hs Hl2). done.
Qed.

Lemma disjoint_swap {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
  a ∉ l1 →
  a :: l1 ## l2 -> l1 ## a :: l2.
Proof.
  rewrite elem_of_disjoint =>Hnin Ha a' Hl1 Hl2.
  destruct (decide (a' = a)).
  - subst. contradiction.
  - apply Ha with a'.
    + apply elem_of_cons; by right.
    + by apply elem_of_cons in Hl2 as [Hcontr | Hl2]; [contradiction|].
Qed.

(* delete_list: delete a list of keys in a map *)

Fixpoint delete_list {K V : Type} `{Countable K, EqDecision K}
           (ks : list K) (m : gmap K V) : gmap K V :=
  match ks with
  | k :: ks' => delete k (delete_list ks' m)
  | [] => m
  end.

Lemma delete_list_insert {K V : Type} `{Countable K, EqDecision K}
      (ks : list K) (m : gmap K V) (l : K) (v : V) :
  l ∉ ks →
  delete_list ks (<[l:=v]> m) = <[l:=v]> (delete_list ks m).
Proof.
  intros Hnin.
  induction ks; auto.
  simpl.
  apply not_elem_of_cons in Hnin as [Hneq Hnin].
  rewrite -delete_insert_ne; auto.
  f_equal. by apply IHks.
Qed.

Lemma delete_list_delete {K V : Type} `{Countable K, EqDecision K}
      (ks : list K) (m : gmap K V) (l : K) :
  l ∉ ks →
  delete_list ks (delete l m) = delete l (delete_list ks m).
Proof.
  intros Hnin.
  induction ks; auto.
  simpl.
  apply not_elem_of_cons in Hnin as [Hneq Hnin].
  rewrite -delete_commute; auto.
  f_equal. by apply IHks.
Qed.

Lemma lookup_delete_list_notin {K V : Type} `{Countable K, EqDecision K}
      (ks : list K) (m : gmap K V) (l : K) :
  l ∉ ks →
  (delete_list ks m) !! l = m !! l.
Proof.
  intros HH; induction ks; simpl; auto.
  eapply not_elem_of_cons in HH. destruct HH.
  rewrite lookup_delete_ne; auto.
Qed.

Lemma delete_list_permutation {A B} `{Countable A, EqDecision A}
      (l1 l2: list A) (m: gmap A B):
  l1 ≡ₚ l2 → delete_list l1 m = delete_list l2 m.
Proof.
  induction 1.
  { reflexivity. }
  { cbn. rewrite IHPermutation //. }
  { cbn. rewrite delete_commute //. }
  { rewrite IHPermutation1 //. }
Qed.

Lemma delete_list_swap {A B : Type} `{EqDecision A, Countable A}
      (a a' : A) (l1 l2 : list A) (M : gmap A B) :
  delete a' (delete_list (l1 ++ a :: l2) M) =
  delete a (delete a' (delete_list (l1 ++ l2) M)).
Proof.
  induction l1.
  - apply delete_commute.
  - simpl. repeat rewrite (delete_commute _ _ a0).
    f_equiv. apply IHl1.
Qed.

(* Map difference for heterogeneous maps, and lemmas relating it to delete_list *)

Definition map_difference_het
  {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
  (m1: gmap A B) (m2: gmap A C): gmap A B
:=
  filter (fun '(k, v) => m2 !! k = None) m1.

Notation "m1 ∖∖ m2" := (map_difference_het m1 m2) (at level 40, left associativity).

Lemma map_eq' {A B} `{Countable A, EqDecision A, Countable B, EqDecision B}
  (m1 m2: gmap A B):
  m1 = m2 ↔ (forall k v, m1 !! k = Some v ↔ m2 !! k = Some v).
Proof.
  split. intros ->. done.
  intros Heq. apply map_eq. intro k. destruct (m2 !! k) eqn:HH.
  { by apply Heq. }
  { destruct (m1 !! k) eqn:HHH; auto. apply Heq in HHH. congruence. }
Qed.

Lemma difference_het_lookup_Some
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A) (v: B):
  (m1 ∖∖ m2) !! k = Some v ↔ m1 !! k = Some v ∧ m2 !! k = None.
Proof. by rewrite /map_difference_het map_lookup_filter_Some. Qed.

Lemma difference_het_lookup_None
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A) (v: B):
  (m1 ∖∖ m2) !! k = None ↔ m1 !! k = None ∨ is_Some (m2 !! k).
Proof.
  rewrite /map_difference_het map_lookup_filter_None.
  split; intros [HH1|HH2]; eauto.
  { destruct (m1 !! k) eqn:?; eauto; right.
    destruct (m2 !! k) eqn:?; eauto. exfalso. eapply HH2; eauto. }
  { destruct (m1 !! k) eqn:?; eauto; right.
    destruct (m2 !! k) eqn:?; eauto. destruct HH2 as [? ?]. congruence. }
Qed.

Lemma difference_het_empty
  {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
  (m: gmap A B):
  m ∖∖ (∅ : gmap A C) = m.
Proof.
  rewrite /map_difference_het map_eq'. intros k v.
  rewrite map_lookup_filter_Some. rewrite lookup_empty. set_solver.
Qed.

 Lemma difference_het_eq_empty
  {A B} `{Countable A, EqDecision A, Countable B, EqDecision B}
  (m: gmap A B):
  m ∖∖ m = (∅ : gmap A B).
Proof.
  rewrite /map_difference_het map_eq'. intros k v.
  rewrite map_lookup_filter_Some. rewrite lookup_empty. set_solver.
Qed.

Lemma difference_het_insert_r
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A) (v: C):
  m1 ∖∖ (<[ k := v ]> m2) = delete k (m1 ∖∖ m2).
Proof.
  intros.
  rewrite /map_difference_het map_eq'. intros k' v'.
  rewrite map_lookup_filter_Some lookup_delete_Some.
  rewrite map_lookup_filter_Some lookup_insert_None. set_solver.
Qed.

Lemma difference_het_insert_l
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A) (v: B):
  m2 !! k = None ->
  <[ k := v ]> m1 ∖∖ m2 = <[ k := v ]> (m1 ∖∖ m2).
Proof.
  intros.
  rewrite /map_difference_het map_eq'. intros k' v'.
  rewrite map_lookup_filter_Some lookup_insert_Some.
  rewrite -map_filter_insert_True;auto.
    by rewrite map_lookup_filter_Some lookup_insert_Some.
Qed.

Lemma difference_het_delete_assoc
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A):
  delete k (m1 ∖∖ m2) = (delete k m1) ∖∖ m2.
Proof.
  intros.
  rewrite /map_difference_het map_eq'. intros k' v'.
  rewrite map_lookup_filter_Some.
  rewrite -map_filter_delete;auto.
  rewrite map_lookup_filter_Some. set_solver.
Qed.

Lemma dom_difference_het
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C):
  dom (m1 ∖∖ m2) = dom m1 ∖ dom m2.
Proof.
  apply (@anti_symm _ _ subseteq).
  typeclasses eauto.
  { rewrite elem_of_subseteq. intro k.
    rewrite elem_of_dom. intros [v Hv].
    rewrite difference_het_lookup_Some in Hv *.
    destruct Hv as [? ?].
    rewrite elem_of_difference !elem_of_dom. split; eauto.
    intros [? ?]. congruence. }
  { rewrite elem_of_subseteq. intro k.
    rewrite elem_of_difference !elem_of_dom. intros [[v ?] Hcontra].
    exists v. rewrite difference_het_lookup_Some. split; eauto.
    destruct (m2 !! k) eqn:?; eauto. exfalso. apply Hcontra. eauto. }
Qed.

Lemma delete_elements_eq_difference_het
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C):
  delete_list (elements (dom m2)) m1 = m1 ∖∖ m2.
Proof.
  set (l := elements (dom m2)).
  assert (l ≡ₚ elements (dom m2)) as Hl by reflexivity.
  clearbody l. revert l Hl. revert m1. pattern m2. revert m2.
  apply map_ind.
  - intros m1 l. rewrite dom_empty_L elements_empty difference_het_empty.
    rewrite Permutation_nil_r. intros ->. reflexivity.
  - intros k v m2 Hm2k HI m1 l Hm1l.
    rewrite difference_het_insert_r.
    rewrite dom_insert in Hm1l *.
    move: Hm1l. rewrite elements_union_singleton.
    rewrite elem_of_dom; intros [? ?]; congruence.
    intros Hm1l.
    transitivity (delete k (delete_list (elements (dom m2)) m1)).
    { erewrite delete_list_permutation. 2: eauto. reflexivity. }
    { rewrite HI//. }
Qed.

(* rtc *)

Lemma rtc_implies {A : Type} (R Q : A → A → Prop) (x y : A) :
  (∀ r q, R r q → Q r q) →
  rtc R x y → rtc Q x y.
Proof.
  intros Himpl HR.
  induction HR.
  - done.
  - apply Himpl in H.
    apply rtc_once in H.
    apply rtc_transitive with y; auto.
Qed.

Lemma rtc_or_intro {A : Type} (R Q : A → A → Prop) (x y : A) :
  rtc (λ a b, R a b) x y →
  rtc (λ a b, R a b ∨ Q a b) x y.
Proof.
  intros HR. induction HR.
  - done.
  - apply rtc_transitive with y; auto.
    apply rtc_once. by left.
Qed.

Lemma rtc_or_intro_l {A : Type} (R Q : A → A → Prop) (x y : A) :
    rtc (λ a b, R a b) x y →
    rtc (λ a b, Q a b ∨ R a b) x y.
Proof.
  intros HR. induction HR.
  - done.
  - apply rtc_transitive with y; auto.
    apply rtc_once. by right.
Qed.

 (* Helper lemmas on list differences *)

Lemma not_elem_of_list {A : Type} `{EqDecision A} (a : A) (l x : list A) :
  a ∈ x → a ∉ list_difference l x.
Proof.
  intros Hax.
  rewrite /not.
  intros Hal.
  by apply elem_of_list_difference in Hal as [Ha' Hax_not].
Qed.

Lemma list_difference_nil {A : Type} `{EqDecision A} (l : list A) :
  list_difference l [] = l.
Proof.
  induction l; auto.
  simpl. f_equal.
  apply IHl.
Qed.

Lemma list_difference_length_cons {A : Type} `{EqDecision A}
      (l2 : list A) (a : A) :
  list_difference [a] (a :: l2) = [].
Proof.
  simpl.
  assert (a ∈ a :: l2); first apply elem_of_list_here.
  destruct (decide_rel elem_of a (a :: l2)); auto; last contradiction.
Qed.

Lemma list_difference_skip {A : Type} `{EqDecision A}
      (l1 l2 : list A) (b : A) :
  ¬ (b ∈ l1) →
  list_difference l1 (b :: l2) = list_difference l1 l2.
Proof.
  intros Hnin.
  induction l1; auto.
  apply not_elem_of_cons in Hnin.
  destruct Hnin as [Hne Hl1].
  simpl.
  destruct (decide_rel elem_of a (b :: l2)).
  - apply elem_of_cons in e.
    destruct e as [Hcontr | Hl2]; first congruence.
    destruct (decide_rel elem_of a l2); last contradiction.
      by apply IHl1.
  - apply not_elem_of_cons in n.
    destruct n as [Hne' Hl2].
    destruct (decide_rel elem_of a l2); first contradiction.
    f_equal.
      by apply IHl1.
Qed.

Lemma list_difference_nested {A : Type} `{EqDecision A}
      (l1 l1' l2 : list A) (b : A) :
  ¬ (b ∈ (l1 ++ l1')) →
  list_difference (l1 ++ b :: l1') (b :: l2) = list_difference (l1 ++ l1') l2.
Proof.
  intros Hnotin.
  induction l1.
  - simpl.
    assert (b ∈ (b :: l2)); first apply elem_of_list_here.
    destruct (decide_rel elem_of b (b :: l2)); last contradiction.
    rewrite list_difference_skip; auto.
  - simpl in *.
    apply not_elem_of_cons in Hnotin.
    destruct Hnotin as [Hne Hnotin].
    destruct (decide_rel elem_of a (b :: l2)).
    + apply elem_of_cons in e.
      destruct e as [Hcontr | Hl2]; first congruence.
      destruct (decide_rel elem_of a l2); last contradiction.
        by apply IHl1.
    + apply not_elem_of_cons in n.
      destruct n as [Hne' Hnotin'].
      destruct (decide_rel elem_of a l2); first contradiction.
      f_equal.
        by apply IHl1.
Qed.

Lemma list_difference_length_ni  {A : Type} `{EqDecision A}
      (l1 : list A) (b : A) :
  ¬ (b ∈ l1) →
  length (list_difference l1 [b]) = length l1.
Proof.
  intros Hna.
  destruct l1; auto.
  simpl.
  apply not_elem_of_cons in Hna.
  destruct Hna as [Hne Hna].
  destruct (decide_rel elem_of a [b]).
  - apply elem_of_list_singleton in e. congruence.
  - simpl. rewrite list_difference_skip; auto.
      by rewrite list_difference_nil.
Qed.

Lemma list_difference_single_length {A : Type} `{EqDecision A}
      (l1 : list A) (b : A) :
  b ∈ l1 →
  NoDup l1 →
  length (list_difference l1 [b]) =
  length l1 - 1.
Proof.
  intros Ha Hndup.
  induction l1; auto.
  destruct (decide (b = a)).
  - subst.
    assert (a ∈ a :: l1); first apply elem_of_list_here.
    rewrite ->NoDup_cons in Hndup. destruct Hndup as [Hni Hndup].
    assert (¬ (a ∈ l1)) as Hni'.
    { rewrite /not. intros Hin. contradiction. }
    simpl.
    assert (a ∈ [a]); first apply elem_of_list_here.
    destruct (decide_rel elem_of a [a]); last contradiction.
    rewrite Nat.sub_0_r.
    apply list_difference_length_ni; auto.
  - simpl.
    assert (¬ (a ∈ [b])).
    { rewrite /not. intros Hin. apply elem_of_list_singleton in Hin. congruence. }
    destruct (decide_rel elem_of a [b]); first contradiction.
    rewrite Nat.sub_0_r /=.
    inversion Hndup; subst.
    apply elem_of_cons in Ha.
    destruct Ha as [Hcontr | Ha]; first congruence.
    apply IHl1 in Ha as Heq; auto.
    rewrite Heq.
    destruct l1; first inversion Ha.
    simpl. lia.
Qed.

Lemma list_difference_app {A : Type} `{EqDecision A}
      (l1 l2 l2' : list A) :
  list_difference l1 (l2 ++ l2') = list_difference (list_difference l1 l2) l2'.
Proof.
  induction l1; auto.
  simpl. destruct (decide_rel elem_of a (l2 ++ l2')).
  - apply elem_of_app in e as [Hl2 | Hl2'].
    + destruct (decide_rel elem_of a l2); last contradiction.
      apply IHl1.
    + destruct (decide_rel elem_of a l2); first by apply IHl1.
      simpl.
      destruct (decide_rel elem_of a l2'); last contradiction.
      apply IHl1.
  - apply not_elem_of_app in n as [Hl2 Hl2'].
    destruct (decide_rel elem_of a l2); first contradiction.
    simpl.
    destruct (decide_rel elem_of a l2'); first contradiction.
    f_equal. apply IHl1.
Qed.

Lemma list_difference_Permutation {A : Type} `{EqDecision A} (l l1 l2 : list A) :
  l1 ≡ₚ l2 -> list_difference l l1 = list_difference l l2.
Proof.
  intros Hl.
  induction l; auto.
  simpl. rewrite IHl.
  destruct (decide_rel elem_of a l1).
  - apply elem_of_list_In in e.
    apply Permutation_in with _ _ _ a in Hl; auto.
    apply elem_of_list_In in Hl.
    destruct (decide_rel elem_of a l2);[|contradiction].
    done.
  - revert n; rewrite elem_of_list_In; intros n.
    assert (¬ In a l2) as Hnin.
    { intros Hcontr. apply Permutation_sym in Hl.
      apply Permutation_in with _ _ _ a in Hl; auto. }
    revert Hnin; rewrite -elem_of_list_In; intro Hnin.
    destruct (decide_rel elem_of a l2);[contradiction|].
    done.
Qed.

Lemma list_difference_length {A} `{EqDecision A} (l1 : list A) :
  forall l2, NoDup l1 -> NoDup l2 -> l2 ⊆+ l1 ->
  length (list_difference l1 l2) = length (l1) - length l2.
Proof.
  induction l1; intros l2 Hdup1 Hdup2 Hsub.
  - simpl. done.
  - simpl. destruct (decide_rel elem_of a l2).
    + apply submseteq_cons_r in Hsub as [Hcontr | [k [Hperm Hk] ] ].
      { apply elem_of_submseteq with (x:=a) in Hcontr;auto. apply NoDup_cons in Hdup1 as [Hnin ?].
        exfalso. by apply Hnin. }
      apply list_difference_Permutation with (l:=l1) in Hperm as Heq. rewrite Heq.
      apply NoDup_cons in Hdup1 as [Hnin ?].
      rewrite list_difference_skip; [intros Hcontr;by apply Hnin|].
      rewrite IHl1;auto.
      revert Hdup2. rewrite Hperm =>Hdup2. by apply NoDup_cons in Hdup2 as [? ?].
      rewrite Hperm /=. auto.
    + simpl. apply submseteq_cons_r in Hsub as [Hsub | Hcontr].
      rewrite IHl1;auto. assert (length l2 ≤ length l1).
      { apply submseteq_length. auto. }
      by apply NoDup_cons in Hdup1 as [? ?]; auto.
      by apply submseteq_length in Hsub; lia.
      destruct Hcontr as [l' [Hperm Hl'] ].
      exfalso. apply n. rewrite Hperm. constructor.
Qed.

Lemma list_to_set_difference A {_: EqDecision A} {_: Countable A} (l1 l2: list A):
  (list_to_set (list_difference l1 l2): gset A) = (list_to_set l1: gset A) ∖ (list_to_set l2: gset A).
Proof.
  revert l2. induction l1.
  - intro. cbn [list_difference list_to_set]. set_solver.
  - intros l2. cbn [list_difference list_to_set]. destruct (decide_rel elem_of a l2); set_solver.
Qed.

(* creates a gmap with domain from the list, all pointing to a default value *)
Fixpoint create_gmap_default {K V : Type} `{Countable K}
         (l : list K) (d : V) : gmap K V :=
  match l with
  | [] => ∅
  | k :: tl => <[k:=d]> (create_gmap_default tl d)
  end.

Lemma create_gmap_default_lookup {K V : Type} `{Countable K}
      (l : list K) (d : V) (k : K) :
  k ∈ l ↔ (create_gmap_default l d) !! k = Some d.
Proof.
  split.
  - intros Hk.
    induction l; inversion Hk.
    + by rewrite lookup_insert.
    + destruct (decide (a = k)); [subst; by rewrite lookup_insert|].
      rewrite lookup_insert_ne; auto.
  - intros Hl.
    induction l; inversion Hl.
    destruct (decide (a = k)); [subst;apply elem_of_list_here|].
    apply elem_of_cons. right.
    apply IHl. simplify_map_eq. auto.
Qed.

Lemma create_gmap_default_lookup_is_Some {K V} `{EqDecision K, Countable K} (l: list K) (d: V) x v:
  create_gmap_default l d !! x = Some v → x ∈ l ∧ v = d.
Proof.
  revert x v d. induction l as [| a l]; cbn.
  - done.
  - intros x v d. destruct (decide (a = x)) as [->|].
    + rewrite lookup_insert. intros; simplify_eq. repeat constructor.
    + rewrite lookup_insert_ne //. intros [? ?]%IHl. subst. repeat constructor; auto.
Qed.

Lemma create_gmap_default_dom {K V} `{EqDecision K, Countable K} (l: list K) (d: V):
  dom (create_gmap_default l d) = list_to_set l.
Proof.
  induction l as [| a l].
  - cbn. rewrite dom_empty_L //.
  - cbn [create_gmap_default list_to_set]. rewrite dom_insert_L // IHl //.
Qed.

Lemma create_gmap_default_lookup_None {K V : Type} `{Countable K}
  (l : list K) (d : V) (k : K) :
  k ∉ l →
  (create_gmap_default l d) !! k = None.
Proof.
  intros Hk.
  induction l;auto.
  simpl. apply not_elem_of_cons in Hk as [Hne Hk].
  rewrite lookup_insert_ne//. apply IHl. auto.
Qed.

Lemma create_gmap_default_permutation {K V : Type} `{Countable K}
  (l l' : list K) (d : V) :
  l ≡ₚ l' →
  (create_gmap_default l d) = (create_gmap_default l' d).
Proof.
  intros Hperm.
  apply map_eq. intros k.
  destruct (decide (k ∈ l)).
  - assert (k ∈ l') as e';[rewrite -Hperm;auto|].
    apply (create_gmap_default_lookup _ d) in e as ->.
    apply (create_gmap_default_lookup _ d) in e' as ->. auto.
  - assert (k ∉ l') as e';[rewrite -Hperm;auto|].
    apply (create_gmap_default_lookup_None _ d) in n as ->.
    apply (create_gmap_default_lookup_None _ d) in e' as ->. auto.
Qed.

Lemma fst_zip_prefix A B (l : list A) (k : list B) :
  (zip l k).*1 `prefix_of` l.
Proof.
  revert k. induction l; cbn; auto.
  destruct k; cbn.
  - apply prefix_nil.
  - apply prefix_cons; auto.
Qed.

Lemma prefix_of_nil A (l : list A) :
  l `prefix_of` [] →
  l = [].
Proof. destruct l; auto. by intros ?%prefix_nil_not. Qed.

Lemma in_prefix A (l1 l2 : list A) x :
  l1 `prefix_of` l2 →
  x ∈ l1 →
  x ∈ l2.
Proof.
  unfold prefix. intros [? ->] ?.
  apply elem_of_app. eauto.
Qed.

Lemma NoDup_prefix A (l1 l2 : list A) :
  NoDup l2 →
  l1 `prefix_of` l2 →
  NoDup l1.
Proof.
  intros H. revert l1. induction H.
  - intros * ->%prefix_of_nil. constructor.
  - intros l1. destruct l1.
    + intros _. constructor.
    + intros HH. rewrite (prefix_cons_inv_1 _ _ _ _ HH).
      apply prefix_cons_inv_2 in HH. constructor; eauto.
      intro Hx. pose proof (in_prefix _ _ _ _ HH Hx). done.
Qed.

Lemma take_lookup_Some_inv A (l : list A) (n i : nat) x :
  take n l !! i = Some x →
  i < n ∧ l !! i = Some x.
Proof.
  revert l i x. induction n; cbn.
  { intros *. inversion 1. }
  { intros *. destruct l; cbn. by inversion 1. destruct i; cbn.
    - intros; simplify_eq. split; auto. lia.
    - intros [? ?]%IHn. split. lia. auto. }
Qed.

Lemma NoDup_fst {A B : Type} (l : list (A*B)) :
  NoDup l.*1 -> NoDup l.
Proof.
  intros Hdup.
  induction l.
  - by apply NoDup_nil.
  - destruct a. simpl in Hdup. apply NoDup_cons in Hdup as [Hin Hdup].
    apply NoDup_cons. split;auto.
    intros Hcontr. apply Hin. apply elem_of_list_fmap.
    exists (a,b). simpl. split;auto.
Qed.

Lemma fst_elem_of_cons {A B} `{EqDecision A} (l : list A) (x : A) (l': list B) :
  x ∈ (zip l l').*1 →
  x ∈ l.
Proof. intros H. eapply in_prefix. eapply fst_zip_prefix. done. Qed.

Lemma length_fst_snd {A B} `{Countable A} (m : gmap A B) :
  length (map_to_list m).*1 = length (map_to_list m).*2.
Proof.
  induction m using map_ind.
  - rewrite map_to_list_empty. auto.
  - rewrite map_to_list_insert;auto. simpl. auto.
Qed.

Lemma map_to_list_delete {A B} `{Countable A} `{EqDecision A} (m : gmap A B) (i : A) (x : B) :
  ∀ l, (i,x) :: l ≡ₚ map_to_list m ->
       NoDup (i :: l.*1) →
       (map_to_list (delete i m)) ≡ₚ l.
Proof.
  intros l Hl Hdup.
  assert ((i,x) ∈ map_to_list m) as Hin.
  { rewrite -Hl. constructor. }
  assert (m !! i = Some x) as Hsome.
  { apply elem_of_map_to_list; auto. }
  apply NoDup_Permutation;auto.
  by apply NoDup_map_to_list.
  apply NoDup_fst. apply NoDup_cons in Hdup as [? ?]. by auto.
  intros [i0 x0]. split.
  - intros Hinx%elem_of_map_to_list.
    assert (i ≠ i0) as Hne;[intros Hcontr;subst;simplify_map_eq|simplify_map_eq].
    assert ((i0, x0) ∈ (i, x) :: l) as Hin'.
    { rewrite Hl. apply elem_of_map_to_list. auto. }
    apply elem_of_cons in Hin' as [Hcontr | Hin'];auto.
    simplify_eq.
  - intros Hinx. apply elem_of_map_to_list.
    assert (i ≠ i0) as Hne;[|simplify_map_eq].
    { intros Hcontr;subst.
      assert (NoDup ((i0, x) :: l)) as Hdup'.
      { rewrite Hl. apply NoDup_map_to_list. }
      assert (i0 ∈ l.*1) as HWInt.
      { apply elem_of_list_fmap. exists (i0,x0). simpl. split;auto. }
      apply NoDup_cons in Hdup as [Hcontr ?]. by apply Hcontr.
    }
    assert ((i0, x0) ∈ (i, x) :: l) as Hin'.
    { constructor. auto. }
    revert Hin'. rewrite Hl =>Hin'. apply elem_of_map_to_list in Hin'.
    auto.
Qed.

Lemma NoDup_map_to_list_fst (A B : Type) `{EqDecision A} `{Countable A}
       (m : gmap A B):
  NoDup (map_to_list m).*1.
Proof.
  induction m as [|i x m] using map_ind.
  - rewrite map_to_list_empty. simpl. by apply NoDup_nil.
  - rewrite map_to_list_insert;auto.
    simpl. rewrite NoDup_cons. split.
    + intros Hcontr%elem_of_list_fmap.
      destruct Hcontr as [ab [Heqab Hcontr] ].
      destruct ab as [a b]. subst. simpl in *.
      apply elem_of_map_to_list in Hcontr. rewrite Hcontr in H0. inversion H0.
    + auto.
Qed.

Lemma map_to_list_delete_fst {A B} `{Countable A} (m : gmap A B) (i : A) (x : B) :
  ∀ l, i :: l ≡ₚ (map_to_list m).*1 ->
       NoDup (i :: l) →
       (map_to_list (delete i m)).*1 ≡ₚ l.
Proof.
  intros l Hl Hdup.
  assert (i ∈ (map_to_list m).*1) as Hin.
  { rewrite -Hl. constructor. }
  apply NoDup_cons in Hdup as [Hnin Hdup].
  apply NoDup_Permutation;auto.
  apply NoDup_map_to_list_fst. done.
  set l' := zip l (repeat x (length l)).
  assert (l = l'.*1) as Heq;[rewrite fst_zip;auto;rewrite repeat_length;lia|].
  intros i0. split.
  - intros Hinx%elem_of_list_fmap.
    destruct Hinx as [ [? ?] [? Hinx] ]. simpl in *. subst a.
    apply elem_of_map_to_list in Hinx.
    destruct (decide (i = i0));[subst i;rewrite lookup_delete in Hinx;inversion Hinx|].
    rewrite lookup_delete_ne in Hinx;auto.
    apply elem_of_map_to_list in Hinx.
    assert (i0 ∈ (map_to_list m).*1) as Hinx'.
    { apply elem_of_list_fmap. exists (i0,b). split;auto. }
    revert Hinx'. rewrite -Hl =>Hinx'.
    by apply elem_of_cons in Hinx' as [Hcontr | Hinx'];[congruence|].
  - intros Hinx. assert (i ≠ i0) as Hne;[congruence|simplify_map_eq].
    assert (i0 ∈ i :: l) as Hin'.
    { constructor. auto. }
    revert Hin'. rewrite Hl =>Hin'.
    apply map_to_list_fst in Hin' as [x' Hx].
    apply elem_of_map_to_list in Hx.
    apply map_to_list_fst. exists x'. apply elem_of_map_to_list.
    rewrite lookup_delete_ne;auto.
Qed.

Lemma submseteq_list_difference {A} `{EqDecision A} (l1 l2 l3 : list A) :
  NoDup l1 → (∀ a, a ∈ l3 → a ∉ l1) → l1 ⊆+ l2 → l1 ⊆+ list_difference l2 l3.
Proof.
  intros Hdup Hnin Hsub.
  apply NoDup_submseteq;auto.
  intros x Hx. apply elem_of_list_difference.
  split.
  - eapply elem_of_submseteq;eauto.
  - intros Hcontr. apply Hnin in Hcontr. done.
Qed.

Lemma list_difference_cons {A} `{EqDecision A} (l1 l2 : list A) (a : A) :
  NoDup l1 → a ∈ l1 → a ∉ l2 → list_difference l1 l2 ≡ₚ a :: list_difference l1 (a :: l2).
Proof.
  revert l2 a. induction l1;intros l2 a' Hdup Hin1 Hin2.
  - inversion Hin1.
  - simpl. destruct (decide_rel elem_of a l2).
    + assert (a ≠ a') as Hne; [intros Hcontr;subst;contradiction|].
      rewrite decide_True. { apply elem_of_cons. right;auto. }
      apply IHl1;auto. apply NoDup_cons in Hdup as [? ?];auto.
      apply elem_of_cons in Hin1 as [? | ?];[congruence|auto].
    + destruct (decide (a = a'));subst.
      * apply NoDup_cons in Hdup as [Hnin Hdup].
        f_equiv. rewrite decide_True;[constructor|].
        rewrite list_difference_skip;auto.
      * apply NoDup_cons in Hdup as [Hnin Hdup].
        apply elem_of_cons in Hin1 as [? | ?];[congruence|auto].
        erewrite IHl1;eauto. rewrite decide_False.
        apply not_elem_of_cons;auto. apply Permutation_swap.
Qed.

Lemma list_to_set_map_to_list {K V : Type} `{EqDecision K} `{Countable K}
      (m : gmap K V) :
  list_to_set (map_to_list m).*1 = dom m.
Proof.
  induction m using map_ind.
  - rewrite map_to_list_empty dom_empty_L. auto.
  - rewrite map_to_list_insert// dom_insert_L. simpl. rewrite IHm. auto.
Qed.

(* The last element of a list is the same as a list where we drop fewer elements than the list *)
Lemma last_drop_lt {A : Type} (l : list A) (i : nat) (a : A) :
  i < (length l) → list.last l = Some a → list.last (drop i l) = Some a.
Proof.
  generalize i. induction l.
  - intros i' Hlen Hlast. inversion Hlast.
  - intros i' Hlen Hlast. destruct i'.
    + simpl. apply Hlast.
    + simpl; simpl in Hlen. apply IHl; first lia.
      assert (0 < length l) as Hl; first lia.
      destruct l; simpl in Hl; first by apply Nat.lt_irrefl in Hl. auto.
Qed.

Lemma last_lookup {A : Type} (l : list A) :
  list.last l = l !! (length l - 1).
Proof.
  induction l.
  - done.
  - simpl; rewrite {1}/last -/last.
    destruct l; auto.
    rewrite IHl. simpl. rewrite PeanoNat.Nat.sub_0_r. done.
Qed.

Lemma last_app_iff {A : Type} (l1 l2 : list A) a :
  list.last l2 = Some a <-> length l2 > 0 ∧ list.last (l1 ++ l2) = Some a.
Proof.
  split.
  - intros Hl2.
    induction l1.
    + destruct l2; inversion Hl2. simpl. split; auto. lia.
    + destruct IHl1 as [Hlt Hlast]. split; auto. simpl; rewrite {1}/last -/last. rewrite Hlast.
      destruct (l1 ++ l2); auto.
      inversion Hlast.
  - generalize l1. induction l2; intros l1' [Hlen Hl].
    + inversion Hlen.
    + destruct l2;[rewrite last_snoc in Hl; inversion Hl; done|].
      rewrite -(IHl2 (l1' ++ [a0])); auto.
      simpl. split;[lia|]. rewrite -app_assoc -cons_middle. done.
Qed.

Lemma last_app_eq {A : Type} (l1 l2 : list A) :
  length l2 > 0 ->
  list.last l2 = list.last (l1 ++ l2).
Proof.
  revert l1. induction l2;intros l1 Hlen.
  - inversion Hlen.
  - destruct l2.
    + rewrite last_snoc. done.
    + rewrite cons_middle app_assoc -(IHl2 (l1 ++ [a]));[simpl;lia|auto].
Qed.

Lemma rev_nil_inv {A} (l : list A) :
  rev l = [] -> l = [].
Proof.
  destruct l;auto.
  simpl. intros Hrev. exfalso.
  apply app_eq_nil in Hrev as [Hrev1 Hrev2].
  inversion Hrev2.
Qed.

Lemma rev_singleton_inv {A} (l : list A) (a : A) :
  rev l = [a] -> l = [a].
Proof.
  destruct l;auto.
  simpl. intros Hrev.
  destruct l.
  - simpl in Hrev. inversion Hrev. auto.
  - exfalso. simpl in Hrev.
    apply app_singleton in Hrev. destruct Hrev as [ [Hrev1 Hrev2] | [Hrev1 Hrev2] ].
    + destruct (rev l);inversion Hrev1.
    + inversion Hrev2.
Qed.

Lemma rev_lookup {A} (l : list A) (a : A) :
  rev l !! 0 = Some a <-> l !! (length l - 1) = Some a.
Proof.
  split; intros Hl.
  - rewrite -last_lookup.
    induction l.
    + inversion Hl.
    + simpl in Hl. simpl. destruct l.
      { simpl in Hl. inversion Hl. auto. }
      { apply IHl. rewrite lookup_app_l in Hl;[simpl;rewrite app_length /=;lia|]. auto. }
  - rewrite -last_lookup in Hl.
    induction l.
    + inversion Hl.
    + simpl. destruct l.
      { simpl. inversion Hl. auto. }
      { rewrite lookup_app_l;[simpl;rewrite app_length /=;lia|]. apply IHl. auto. }
Qed.

Lemma rev_cons_inv {A} (l l' : list A) (a : A) :
  rev l = a :: l' ->
  ∃ l'', l = l'' ++ [a].
Proof.
  intros Hrel.
  destruct l;inversion Hrel.
  assert ((a0 :: l) !! (length l) = Some a) as Hsome.
  { assert (length l = length (a0 :: l) - 1) as ->;[simpl;lia|]. apply rev_lookup. rewrite Hrel. constructor. }
  apply take_S_r in Hsome.
  exists (take (length l) (rev (rev l ++ [a0]))).
    simpl. rewrite rev_unit. rewrite rev_involutive. rewrite -Hsome /=.
    f_equiv. rewrite firstn_all. auto.
Qed.


Definition prod_op {A B : Type} :=
  λ (o1 : option A) (o2 : option B),
    match o1 with
    | Some b =>
        match o2 with
        | Some c => Some (b,c)
        | None => None
        end
    | None => None
    end.

Definition prod_merge {A B C : Type} `{Countable A} : gmap A B → gmap A C → gmap A (B * C) :=
  λ m1 m2, merge prod_op m1 m2.

Lemma prod_merge_empty_r
  {K A B} `{Countable K} (m1 : gmap K A) :
  (@prod_merge _ _ B _ _ m1 ∅) = ∅.
Proof.
  rewrite /prod_merge.
  rewrite merge_empty_r.
  rewrite /flip.
  rewrite /prod_op.
  induction m1 using map_ind.
  - apply omap_empty.
  - assert (((λ y : option A, match y with
                         | Some _ | _ => None
                         end) ∘ Some) x = (None : option (prod A B))) by done.
    apply omap_insert_None with (i := i) (m := m) in H1.
    rewrite IHm1 in H1.
    by rewrite delete_empty in H1.
Qed.

Lemma prod_merge_empty_l
  {K A B} `{Countable K} (m2 : gmap K B) :
  (@prod_merge _ A _ _ _ ∅ m2) = ∅.
Proof.
  rewrite /prod_merge.
  rewrite merge_empty_l.
  rewrite /prod_op.
  induction m2 using map_ind.
  - apply omap_empty.
  - assert (((λ _ : option B, None) ∘ Some) x = (None : option (prod A B))) by done.
    apply omap_insert_None with (i := i) (m := m) in H1.
    rewrite IHm2 in H1.
    by rewrite delete_empty in H1.
Qed.

Lemma prod_merge_insert
  {K A B} `{Countable K} (m1 : gmap K A) (m2 : gmap K B) (k : K) (a : A) (b : B) :
  prod_merge (<[k:=a]> m1) (<[k:=b]> m2) =
  <[k:=(a,b)]> (prod_merge m1 m2).
Proof.
  rewrite /prod_merge //=.
  erewrite insert_merge; eauto.
Qed.

Lemma snd_prod_merge_inv
  {K A B} `{Countable K} (m1 : gmap K A) (m2 : gmap K B) :
  dom m1 = dom m2 ->
  snd <$> prod_merge m1 m2 = m2.
Proof.
  move: m1.
  induction m2 as [| k v m2 Hm2_k IHm2 ] using map_ind
  ; intros m1 Hdom.
  - by rewrite prod_merge_empty_r fmap_empty.
  - assert (k ∈ dom m1) as Hk_indom_m1 by set_solver.
    apply elem_of_dom in Hk_indom_m1.
    destruct Hk_indom_m1 as [v1 Hm1_k].
    rewrite /prod_merge fmap_merge.
    apply map_eq.
    intros k'.
    rewrite lookup_merge.
    destruct (decide (k = k')) ; simplify_map_eq; first done.
    destruct (m1 !! k') as [v'|] eqn:Hm1_k'.
    + assert (k' ∈ dom m2) as Hk'_indom_m2.
      { rewrite dom_insert_L in Hdom.
        assert ( k' ∈ dom m1) as Hk'_indom_m1 by (apply elem_of_dom; eexists ; eauto).
        rewrite Hdom in Hk'_indom_m1.
        set_solver.
      }
      apply elem_of_dom in Hk'_indom_m2.
      destruct Hk'_indom_m2 as [v2 Hm2_k'].
      rewrite Hm2_k'.
      by simplify_map_eq.
    + assert (k' ∉ dom m2) as Hk'_notindom_m2.
      { rewrite dom_insert_L in Hdom.
        assert ( k' ∉ dom m1) as Hk'_notindom_m1 by (apply not_elem_of_dom; eauto).
        rewrite Hdom in Hk'_notindom_m1.
        set_solver.
      }
      apply not_elem_of_dom in Hk'_notindom_m2.
      by simplify_map_eq.
Qed.

Lemma lookup_prod_merge_snd {K A B} `{Countable K}
  (m1 : gmap K A) (m2 : gmap K B) va vb:
  prod_merge m1 m2 !! va = Some vb ->
  m2 !! va = Some (snd vb).
Proof.
  move: m1.
  induction m2 using map_ind; intros m1 Hprod.
  - rewrite prod_merge_empty_r lookup_empty // in Hprod.
  - destruct (decide (va = i)); simplify_map_eq.
    + rewrite lookup_merge in Hprod; simplify_map_eq.
      destruct (m1 !! i) eqn:Heq ; cbn in * ; [| congruence].
      destruct vb ; simplify_eq ; cbn in * ; done.
    + rewrite lookup_merge in Hprod; simplify_map_eq.
      destruct (m !! va) eqn: Heq_m
      ; cbn in *
      ; destruct (m1 !! va) eqn:Heq_m1
      ; simplify_map_eq; done.
Qed.

Lemma insert_inj {K A} `{Countable K, EqDecision K, Countable A, EqDecision A}
  (m1 m2 : gmap K A) (k : K) (v : A):
  m1 !! k = m2 !! k ->
  <[ k := v ]> m1 = <[ k := v ]> m2 ->
  m1 = m2.
Proof.
  intros Heq_k Heq_insert.
  apply map_eq.
  rewrite map_eq' in Heq_insert.
  intro k'.
  destruct (decide (k = k')) ; simplify_eq ; first done.
  destruct (m1 !! k') eqn:Hm1.
  - specialize (Heq_insert k' a).
    rewrite lookup_insert_ne //= lookup_insert_ne //= in Heq_insert.
    apply Heq_insert in Hm1. by rewrite Hm1.
  - destruct (m2 !! k') eqn:Hm2; last done.
    specialize (Heq_insert k' a).
    rewrite lookup_insert_ne //= lookup_insert_ne //= in Heq_insert.
    eapply Heq_insert in Hm2.
    rewrite Hm1 in Hm2 ; congruence.
Qed.

Lemma delete_subseteq_r
  {K A} `{Countable K, EqDecision K, Countable A, EqDecision A}
  (m1 m2 : gmap K A) (k : K) :
  m1 !! k = None → m1 ⊆ m2 → m1 ⊆ delete k m2.
Proof.
  intros.
  eapply map_subseteq_spec.
  intros k' v' Hk'.
  destruct (decide (k = k')) ; simplify_map_eq.
  by eapply lookup_weaken in Hk'.
Qed.

Lemma delete_subseteq_list_r
  {K A} `{Countable K, EqDecision K, Countable A, EqDecision A}
  (m1 m2 m3 : gmap K A) :
      m1 ##ₘ m3 → m1 ⊆ m2 → m1 ⊆ (m2 ∖ m3).
Proof.
  move: m1 m2.
  induction m3 as [|k v m3 Hm3_k IHm3] using map_ind
  ; intros m1 m2 Hdisjoint Hincl.
  - eapply map_subseteq_spec; intros k' v' Hk'.
    rewrite map_difference_empty.
    eapply lookup_weaken; eauto.
  - eapply map_subseteq_spec; intros k' v' Hm1_k'.
    assert (m2 !! k' = Some v') as Hm2_k' by (eapply lookup_weaken ; eauto).
    apply map_disjoint_insert_r in Hdisjoint.
    destruct Hdisjoint as [Hm1_k Hdisjoint].
    pose proof (delete_subseteq_r m1 m2 k Hm1_k Hincl) as Hdel.
    eapply IHm3 in Hdel; eauto.
    assert (k ≠ k') as Hneq_k by (intro ; simplify_map_eq).
    pose proof Hm1_k' as Hk'.
    rewrite lookup_difference.
    simplify_map_eq.
    eapply map_disjoint_Some_r in Hm1_k'; eauto.
    by rewrite Hm1_k'.
Qed.

Lemma insert_weaken
  {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type}
  (m m' : gmap K A) (k : K) (v : A) :
  <[k:=v]> m' ⊆ m -> m !! k = Some v.
Proof.
  intros Hincl.
  by eapply lookup_weaken; eauto; simplify_map_eq.
Qed.

Lemma delete_difference_assoc
  {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type}
  (m m' : gmap K A) (k' : K) :
  (delete k' m ∖ m') = delete k' (m ∖ m').
Proof.
  move: m k'.
  induction m' as [| k v m' Hm'_k IHm' ] using map_ind
  ; intros m k'.
  - by rewrite !map_difference_empty.
  - by rewrite -!delete_difference IHm' delete_commute.
Qed.



(* TODO: integrate into stdpp? *)
Lemma pair_eq_inv {A B} {y u : A} {z t : B} {x} :
    x = (y, z) -> x = (u, t) ->
    y = u ∧ z = t.
Proof. intros ->. inversion 1. auto. Qed.

(* TODO: integrate into stdpp? *)
Tactic Notation "simplify_pair_eq" :=
  repeat
    lazymatch goal with
    | H1 : ?x = (?y, ?z), H2 : ?x = (?u, ?t) |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 H2)); clear H2
    | H1 : (?y, ?z) = ?x, H2 : ?x = (?u, ?t) |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv (eq_sym H1) H2)); clear H2
    | H1 : ?x = (?y, ?z), H2 : (?u, ?t) = ?x |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 (eq_sym H2))); clear H2
    | H1 : (?y, ?z) = ?x, H2 : (?u, ?t) = ?x |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv (eq_sym H1) (eq_sym H2))); clear H2
    | |- _ => progress simplify_eq
    end.

(*----------------------- FIXME TEMPORARY ------------------------------------*)
(* This is a copy-paste from stdpp (fin_maps.v), plus a fix to avoid using
   "rewrite .. by .." that is not available when using ssreflect's rewrite. *)
(* TODO: upstream the fix into stdpp, and remove the code below whenever we
   upgrade to a version of stdpp that includes it *)

Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite lookup_insert in H || (rewrite lookup_insert_ne in H; [| by tac])
  | H : context[ (alter _ _ _) !! _] |- _ =>
    rewrite lookup_alter in H || (rewrite lookup_alter_ne in H; [| by tac])
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete in H || (rewrite lookup_delete_ne in H; [| by tac])
  | H : context[ {[ _ := _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton in H || (rewrite lookup_singleton_ne in H; [| by tac])
  | H : context[ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
  | H : context[ (omap _ _) !! _ ] |- _ => rewrite lookup_omap in H
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] =>
    rewrite lookup_insert || (rewrite lookup_insert_ne; [| by tac])
  | |- context[ (alter _ _ _) !! _ ] =>
    rewrite lookup_alter || (rewrite lookup_alter_ne; [| by tac])
  | |- context[ (delete _ _) !! _ ] =>
    rewrite lookup_delete || (rewrite lookup_delete_ne; [| by tac])
  | |- context[ {[ _ := _ ]} !! _ ] =>
    rewrite lookup_singleton || (rewrite lookup_singleton_ne; [| by tac])
  | |- context[ (_ <$> _) !! _ ] => rewrite lookup_fmap
  | |- context[ (omap _ _) !! _ ] => rewrite lookup_omap
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert (m !! i = Some x') as E by tac;
    rewrite E; clear E
  end.

Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map map_disjoint.

Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | H : {[ _ := _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ := _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    opose proof (lookup_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_weaken _ m2) in H1; [congruence|by tac]
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply map_union_cancel_l in H; [|by tac|by tac]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply map_union_cancel_r in H; [|by tac|by tac]
  | H : {[?i := ?x]} = ∅ |- _ => by destruct (map_non_empty_singleton i x)
  | H : ∅ = {[?i := ?x]} |- _ => by destruct (map_non_empty_singleton i x)
  | H : ?m !! ?i = Some _, H2 : ?m !! ?j = None |- _ =>
     unless (i ≠ j) by done;
     assert (i ≠ j) by (by intros ?; simplify_eq)
  end.
Tactic Notation "simplify_map_eq" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || simplify_map_eq by tac).
Tactic Notation "simplify_map_eq" :=
  simplify_map_eq by eauto with simpl_map map_disjoint.
Tactic Notation "simplify_map_eq" "/=" :=
  simplify_map_eq/= by eauto with simpl_map map_disjoint.
