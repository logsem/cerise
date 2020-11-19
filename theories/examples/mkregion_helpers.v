From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
From cap_machine Require Import stdpp_extra iris_extra cap_lang
     region rules_base rules.
From cap_machine.examples Require Import disjoint_regions_tactics.

Definition mkregion (r_start r_end: Addr) (contents: list Word): gmap Addr Word :=
  list_to_map (zip (region_addrs r_start r_end) contents).

Lemma dom_mkregion_incl a e l:
  dom (gset Addr) (mkregion a e l) ⊆ list_to_set (region_addrs a e).
Proof.
  rewrite /mkregion. generalize (region_addrs a e). induction l.
  { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L. apply empty_subseteq. }
  { intros ll. destruct ll as [| x ll].
    - cbn. rewrite dom_empty_L. done.
    - cbn [list_to_set zip zip_with list_to_map foldr fst snd]. rewrite dom_insert_L.
      set_solver. }
Qed.

Lemma dom_mkregion_incl_rev a e l:
  (a + length l = Some e)%a →
  list_to_set (region_addrs a e) ⊆ dom (gset Addr) (mkregion a e l).
Proof.
  rewrite /mkregion. intros Hl.
  assert (length (region_addrs a e) = length l) as Hl'.
  { rewrite region_addrs_length /region_size. solve_addr. }
  clear Hl. revert Hl'. generalize (region_addrs a e). induction l.
  { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L.
    destruct l; [| inversion Hl']. cbn. apply empty_subseteq. }
  { intros ll Hll. destruct ll as [| x ll]; [by inversion Hll|].
    cbn [list_to_set zip zip_with list_to_map foldr fst snd].
    rewrite dom_insert_L. cbn in Hll. apply Nat.succ_inj in Hll.
    specialize (IHl ll Hll). set_solver. }
Qed.

Lemma dom_mkregion_eq a e l:
  (a + length l = Some e)%a →
  dom (gset Addr) (mkregion a e l) = list_to_set (region_addrs a e).
Proof.
  intros Hlen. apply (anti_symm _).
  - apply dom_mkregion_incl.
  - by apply dom_mkregion_incl_rev.
Qed.

Lemma in_dom_mkregion a e l k:
  k ∈ dom (gset Addr) (mkregion a e l) →
  k ∈ region_addrs a e.
Proof.
  intros H.
  pose proof (dom_mkregion_incl a e l) as HH.
  rewrite elem_of_subseteq in HH |- * => HH.
  specialize (HH _ H). eapply elem_of_list_to_set; eauto.
  Unshelve. typeclasses eauto.
Qed.

Lemma in_dom_mkregion' a e l k:
  (a + length l = Some e)%a →
  k ∈ region_addrs a e →
  k ∈ dom (gset Addr) (mkregion a e l).
Proof.
  intros. rewrite dom_mkregion_eq // elem_of_list_to_set //.
Qed.

Ltac disjoint_map_to_list :=
  rewrite (@map_disjoint_dom _ _ (gset Addr)) ?dom_union_L;
  eapply disjoint_mono_l;
  rewrite ?dom_list_to_map_singleton;
  repeat (
    try lazymatch goal with
        | |- _ ∪ _ ⊆ _ =>
          etransitivity; [ eapply union_mono_l | eapply union_mono_r ]
        end;
    [ first [ apply dom_mkregion_incl | reflexivity ] |..]
  );
  try match goal with |- _ ## dom _ (mkregion _ _ _) =>
    eapply disjoint_mono_r; [ apply dom_mkregion_incl |] end;
  rewrite -?list_to_set_app_L ?dom_list_to_map_singleton;
  apply stdpp_extra.list_to_set_disj.

Lemma mkregion_sepM_to_sepL2 `{Σ: gFunctors} (a e: Addr) l (φ: Addr → Word → iProp Σ) :
  (a + length l)%a = Some e →
  ⊢ ([∗ map] k↦v ∈ mkregion a e l, φ k v) -∗ ([∗ list] k;v ∈ (region_addrs a e); l, φ k v).
Proof.
  rewrite /mkregion. revert a e. induction l as [| x l].
  { cbn. intros. rewrite zip_with_nil_r /=. assert (a = e) as -> by solve_addr.
    rewrite /region_addrs region_size_0. 2: solve_addr. cbn. eauto. }
  { cbn. intros a e Hlen. rewrite region_addrs_cons. 2: solve_addr.
    cbn. iIntros "H". iDestruct (big_sepM_insert with "H") as "[? H]".
    { rewrite -not_elem_of_list_to_map /=.
      intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_region_addrs] ]%elem_of_list_fmap.
      solve_addr. }
    iFrame. iApply (IHl with "H"). solve_addr. }
Qed.

Lemma mkregion_prepare `{memG Σ} (a e: Addr) l :
  (a + length l)%a = Some e →
  ⊢ ([∗ map] k↦v ∈ mkregion a e l, k ↦ₐ v) ==∗ ([∗ list] k;v ∈ (region_addrs a e); l, k ↦ₐ v).
Proof.
  iIntros (?) "H". iDestruct (mkregion_sepM_to_sepL2 with "H") as "H"; auto.
Qed.
