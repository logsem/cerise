From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
From cap_machine Require Import stdpp_extra iris_extra cap_lang
     region rules_base rules rules_binary rules_binary_base.
From cap_machine.proofmode Require Import disjoint_regions_tactics.

Definition mkregion (r_start r_end: Addr) (contents: list Word): gmap Addr Word :=
  list_to_map (zip (finz.seq_between r_start r_end) contents).

Definition mbkregion (r_start r_end: Addr) (contents: list Word) (contents_spec: list Word): gmap Addr (Word * Word) :=
  list_to_map (zip (finz.seq_between r_start r_end) (zip contents contents_spec)).

Lemma zip_seq_between_lookup {A} (b e a : Addr) (l : list A) x :
  (b + length l = Some e)%a →
  (a, x) ∈ zip (finz.seq_between b e) l ↔ ∃ (i:nat), a = (b ^+ i)%a ∧ l !! i = Some x.
Proof.
  revert b e a x. induction l as [| x l].
  { intros * Hl. cbn.
    rewrite (_: b = e). 2: solve_addr.
    rewrite finz_seq_between_empty //. 2: solve_addr. cbn.
    split. by inversion 1. intros [? [? ?] ].  rewrite lookup_nil in H0. congruence. }
  { intros * Hl. cbn in *.
    rewrite finz_seq_between_cons. 2: solve_addr. cbn.
    split.
    { intros [HH|HH]%elem_of_cons.
      { simplify_eq. exists 0. split. solve_addr. constructor. }
      { eapply IHl in HH as [i [? ?] ].
        { exists (S i). split; solve_addr. }
        { solve_addr. } } }
    { intros [i [? H2] ]. destruct i.
      { cbn in H2. simplify_eq. rewrite (_: b ^+ 0%nat = b)%a. constructor. solve_addr. }
      { constructor. cbn in H2. apply IHl. solve_addr. exists i.
        split; solve_addr. } } }
Qed.

Lemma list_to_map_app {A} `{EqDecision A, Countable A} {B} (l1 l2: list (A * B)) :
  (list_to_map (l1 ++ l2) : gmap A B) = list_to_map l1 ∪ list_to_map l2.
Proof.
  revert l2. induction l1.
  { intros l2. rewrite /= left_id_L //. }
  { intros l2. rewrite /= IHl1 insert_union_l //. }
Qed.

Lemma mkregion_app l1 l2 b e :
  (b + length (l1 ++ l2))%a = Some e →
  mkregion b e (l1 ++ l2) =
  mkregion b (b ^+ length l1)%a l1 ∪ mkregion (b ^+ length l1)%a e l2.
Proof.
  rewrite /mkregion. rewrite length_app. intros HH.
  rewrite (finz_seq_between_split _ (b ^+ length l1)%a). 2: split; solve_addr.
  rewrite zip_app. 2: rewrite finz_seq_between_length /finz.dist; solve_addr.
  rewrite list_to_map_app //.
Qed.

Lemma mkregion_lookup (b e a : Addr) l x :
  (b + length l = Some e)%a →
  mkregion b e l !! a = Some x ↔ ∃ (i:nat), a = (b ^+ i)%a ∧ l !! i = Some x.
Proof.
  intros Hl. rewrite /mkregion.
  rewrite -elem_of_list_to_map. apply zip_seq_between_lookup; auto.
  rewrite fst_zip. apply finz_seq_between_NoDup.
  rewrite finz_seq_between_length /finz.dist. solve_addr.
Qed.

Lemma dom_mkregion_incl a e l:
  dom (mkregion a e l) ⊆ list_to_set (finz.seq_between a e).
Proof.
  rewrite /mkregion. generalize (finz.seq_between a e). induction l.
  { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L. apply empty_subseteq. }
  { intros ll. destruct ll as [| x ll].
    - cbn. rewrite dom_empty_L. done.
    - cbn [list_to_set zip zip_with list_to_map foldr fst snd]. rewrite dom_insert_L.
      set_solver. }
Qed.

Lemma dom_mkregion_incl_rev a e l:
  (a + length l = Some e)%a →
  list_to_set (finz.seq_between a e) ⊆ dom (mkregion a e l).
Proof.
  rewrite /mkregion. intros Hl.
  assert (length (finz.seq_between a e) = length l) as Hl'.
  { rewrite finz_seq_between_length /finz.dist. solve_addr. }
  clear Hl. revert Hl'. generalize (finz.seq_between a e). induction l.
  { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L.
    destruct l; [| inversion Hl']. cbn. apply empty_subseteq. }
  { intros ll Hll. destruct ll as [| x ll]; [by inversion Hll|].
    cbn [list_to_set zip zip_with list_to_map foldr fst snd].
    rewrite dom_insert_L. cbn in Hll. apply Nat.succ_inj in Hll.
    specialize (IHl ll Hll). set_solver. }
Qed.

Lemma dom_mkregion_eq a e l:
  (a + length l = Some e)%a →
  dom (mkregion a e l) = list_to_set (finz.seq_between a e).
Proof.
  intros Hlen. apply (anti_symm subseteq).
  - apply dom_mkregion_incl.
  - by apply dom_mkregion_incl_rev.
Qed.

Lemma in_dom_mkregion a e l k:
  k ∈ dom (mkregion a e l) →
  k ∈ finz.seq_between a e.
Proof.
  intros H.
  pose proof (dom_mkregion_incl a e l) as HH.
  rewrite elem_of_subseteq in HH.
  specialize (HH _ H). eapply @elem_of_list_to_set; eauto.
  typeclasses eauto.
Qed.

Lemma in_dom_mkregion' a e l k:
  (a + length l = Some e)%a →
  k ∈ finz.seq_between a e →
  k ∈ dom (mkregion a e l).
Proof.
  intros. rewrite dom_mkregion_eq // elem_of_list_to_set //.
Qed.


(* Note that this tactic can only be applied on the left of the disjointness condition *)
Ltac union_resolve_mkregion :=
  repeat (
      try lazymatch goal with
        | |- _ ∪ _ ⊆ _ =>
            etransitivity; [ eapply union_mono_l | eapply union_mono_r ]
        end;
      [ first [ apply dom_mkregion_incl | reflexivity ] |..]
    ).

(* overwrite `disjoint_map_to_list` ltac to also simplify list_to_map occurrences *)
Ltac disjoint_map_to_list :=
  rewrite (@map_disjoint_dom _ _ (gset Addr)) ?dom_union_L;
  eapply disjoint_mono_l;
  rewrite ?dom_list_to_map_singleton;
  union_resolve_mkregion;
  try match goal with |- _ ## dom (mkregion _ _ _) =>
                        eapply disjoint_mono_r; [ apply dom_mkregion_incl | ] end;
  try match goal with |- _ ## dom (list_to_map _ ) =>
                        rewrite dom_list_to_map_L end;
  rewrite -?list_to_set_app_L ?dom_list_to_map_singleton;
  apply stdpp_extra.list_to_set_disj.

Lemma mkregion_sepM_to_sepL2 `{Σ: gFunctors} (a e: Addr) l (φ: Addr → Word → iProp Σ) :
  (a + length l)%a = Some e →
  ⊢ ([∗ map] k↦v ∈ mkregion a e l, φ k v) -∗ ([∗ list] k;v ∈ (finz.seq_between a e); l, φ k v).
Proof.
  rewrite /mkregion. revert a e. induction l as [| x l].
  { cbn. intros. rewrite zip_with_nil_r /=. assert (a = e) as -> by solve_addr.
    rewrite /finz.seq_between finz_dist_0. 2: solve_addr. cbn. eauto. }
  { cbn. intros a e Hlen. rewrite finz_seq_between_cons. 2: solve_addr.
    cbn. iIntros "H". iDestruct (big_sepM_insert with "H") as "[? H]".
    { rewrite -not_elem_of_list_to_map /=.
      intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_finz_seq_between] ]%elem_of_list_fmap.
      solve_addr. }
    iFrame. iApply (IHl with "H"). solve_addr. }
Qed.

Lemma mkregion_prepare `{memG Σ} (a e: Addr) l :
  (a + length l)%a = Some e →
  ⊢ ([∗ map] k↦v ∈ mkregion a e l, k ↦ₐ v) ==∗ ([∗ list] k;v ∈ (finz.seq_between a e); l, k ↦ₐ v).
Proof.
  iIntros (?) "H". iDestruct (mkregion_sepM_to_sepL2 with "H") as "H"; auto.
Qed.

Lemma mkregion_prepare_spec `{cfgSG Σ} (a e: Addr) l :
  (a + length l)%a = Some e →
  ⊢ ([∗ map] k↦v ∈ mkregion a e l, k ↣ₐ v) ==∗ ([∗ list] k;v ∈ (finz.seq_between a e); l, k ↣ₐ v).
Proof.
  iIntros (?) "H". iDestruct (mkregion_sepM_to_sepL2 with "H") as "H"; auto.
Qed.


Lemma mkregion_sepM_to_sepL2_zip `{Σ: gFunctors} (a e: Addr) l l' (φ φ': Addr → Word → iProp Σ) :
  (a + length l)%a = Some e →
  (a + length l')%a = Some e →
  ([∗ map] k↦v ∈ mkregion a e l, φ k v) -∗
    ([∗ map] k↦v ∈ mkregion a e l', φ' k v) -∗
    ([∗ map] k↦v ∈ mbkregion a e l l', φ k v.1 ∗ φ' k v.2).
Proof.
  rewrite /mkregion. revert a e l'. induction l as [| x l].
  { cbn. intros. rewrite zip_with_nil_r /=. assert (a = e) as -> by solve_addr.
    rewrite /finz.seq_between /finz.dist /=. assert ((Z.to_nat (e - e)) = 0) as ->. lia. simpl.
    rewrite /mbkregion. rewrite finz_seq_between_empty;[|solve_addr]. eauto. }
  { cbn. intros a e l' Hlen Hlen'.
    assert (length l' = S (length l)) as Hleneq.
    { solve_addr. }
    destruct l';[inversion Hleneq|]. simpl in *.
    rewrite finz_seq_between_cons. 2: solve_addr.
    rewrite /mbkregion /=.
    cbn. iIntros "H H'". iDestruct (big_sepM_insert with "H") as "[? H]".
    { rewrite -not_elem_of_list_to_map /=.
      intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_finz_seq_between] ]%elem_of_list_fmap.
      solve_addr. }
    iDestruct (big_sepM_insert with "H'") as "[? H']".
    { rewrite -not_elem_of_list_to_map /=.
      intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_finz_seq_between] ]%elem_of_list_fmap.
      solve_addr. }
    rewrite (finz_seq_between_cons a). 2: solve_addr. simpl.
    iApply big_sepM_insert.
    { rewrite -not_elem_of_list_to_map /=.
      intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_finz_seq_between] ]%elem_of_list_fmap.
      solve_addr. }
    iFrame. iApply (IHl with "H H'"). solve_addr. solve_addr. }
Qed.

Lemma mbkregion_prepare `{memG Σ, cfgSG Σ} (a e : Addr) l l' :
  (a + length l)%a = Some e →
  (a + length l')%a = Some e →
  ([∗ map] k↦v ∈ mkregion a e l, k ↦ₐ v) -∗
  ([∗ map] k↦v ∈ mkregion a e l', k ↣ₐ v) ==∗
  ([∗ map] k↦v ∈ mbkregion a e l l', k ↦ₐ v.1 ∗ k ↣ₐ v.2).
Proof.
  iIntros (? ?) "H H'". iDestruct (mkregion_sepM_to_sepL2_zip with "H H'") as "H"; auto.
Qed.
