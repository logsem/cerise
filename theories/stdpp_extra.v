From stdpp Require Import countable list.
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
Proof. by rewrite /map_difference_het map_filter_lookup_Some. Qed.

Lemma difference_het_lookup_None
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A) (v: B):
  (m1 ∖∖ m2) !! k = None ↔ m1 !! k = None ∨ is_Some (m2 !! k).
Proof.
  rewrite /map_difference_het map_filter_lookup_None.
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
  rewrite map_filter_lookup_Some. rewrite lookup_empty. set_solver.
Qed.

 Lemma difference_het_eq_empty
  {A B} `{Countable A, EqDecision A, Countable B, EqDecision B}
  (m: gmap A B):
  m ∖∖ m = (∅ : gmap A B).
Proof.
  rewrite /map_difference_het map_eq'. intros k v.
  rewrite map_filter_lookup_Some. rewrite lookup_empty. set_solver.
Qed.

Lemma difference_het_insert_r
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A) (v: C):
  m1 ∖∖ (<[ k := v ]> m2) = delete k (m1 ∖∖ m2).
Proof.
  intros.
  rewrite /map_difference_het map_eq'. intros k' v'.
  rewrite map_filter_lookup_Some lookup_delete_Some.
  rewrite map_filter_lookup_Some lookup_insert_None. set_solver.
Qed.

Lemma difference_het_insert_l
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A) (v: B):
  m2 !! k = None ->
  <[ k := v ]> m1 ∖∖ m2 = <[ k := v ]> (m1 ∖∖ m2).
Proof.
  intros.
  rewrite /map_difference_het map_eq'. intros k' v'.
  rewrite map_filter_lookup_Some lookup_insert_Some.
  rewrite -map_filter_insert;auto.
    by rewrite map_filter_lookup_Some lookup_insert_Some.
Qed.

Lemma difference_het_delete_assoc
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C) (k: A):
  delete k (m1 ∖∖ m2) = (delete k m1) ∖∖ m2.
Proof.
  intros.
  rewrite /map_difference_het map_eq'. intros k' v'.
  rewrite map_filter_lookup_Some.
  rewrite -map_filter_delete;auto.
  rewrite map_filter_lookup_Some. set_solver.
Qed.

Lemma dom_difference_het
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C):
  dom (gset A) (m1 ∖∖ m2) = dom (gset A) m1 ∖ dom (gset A) m2.
Proof.
  apply (anti_symm _).
  { rewrite elem_of_subseteq. intro k.
    rewrite -elem_of_gmap_dom. intros [v Hv].
    rewrite difference_het_lookup_Some in Hv * => Hv.
    destruct Hv as [? ?].
    rewrite elem_of_difference -!elem_of_gmap_dom. split; eauto.
    intros [? ?]. congruence. }
  { rewrite elem_of_subseteq. intro k.
    rewrite elem_of_difference -!elem_of_gmap_dom. intros [[v ?] Hcontra].
    exists v. rewrite difference_het_lookup_Some. split; eauto.
    destruct (m2 !! k) eqn:?; eauto. exfalso. apply Hcontra. eauto. }
Qed.

Lemma delete_elements_eq_difference_het
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C):
  delete_list (elements (dom (gset A) m2)) m1 = m1 ∖∖ m2.
Proof.
  set (l := elements (dom (gset A) m2)).
  assert (l ≡ₚ elements (dom (gset A) m2)) as Hl by reflexivity.
  clearbody l. revert l Hl. revert m1. pattern m2. revert m2.
  apply map_ind.
  - intros m1 l. rewrite dom_empty_L elements_empty difference_het_empty.
    rewrite Permutation_nil. intros ->. reflexivity.
  - intros k v m2 Hm2k HI m1 l Hm1l.
    rewrite difference_het_insert_r.
    rewrite dom_insert in Hm1l * => Hm1l.
    move: Hm1l. rewrite elements_union_singleton.
    2: rewrite -elem_of_gmap_dom; intros [? ?]; congruence.
    intros Hm1l.
    transitivity (delete k (delete_list (elements (dom (gset A) m2)) m1)).
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

Lemma list_difference_length {A : Type} `{EqDecision A}
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
    rewrite -minus_n_O.
    apply list_difference_length_ni; auto.
  - simpl.
    assert (¬ (a ∈ [b])).
    { rewrite /not. intros Hin. apply elem_of_list_singleton in Hin. congruence. }
    destruct (decide_rel elem_of a [b]); first contradiction.
    rewrite -minus_n_O /=.
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
  dom (gset K) (create_gmap_default l d) = list_to_set l.
Proof.
  induction l as [| a l].
  - cbn. rewrite dom_empty_L //.
  - cbn [create_gmap_default list_to_set]. rewrite dom_insert_L // IHl //.
Qed.

