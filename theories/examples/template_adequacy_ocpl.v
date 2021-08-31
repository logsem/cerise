From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample malloc macros_new.
From cap_machine.examples Require Export mkregion_helpers disjoint_regions_tactics.
From cap_machine.examples Require Import template_adequacy.

Module ocpl.
Include with_adv_and_link.

Record ocpl_library `{MachineParameters} := MkOcplLibrary {
  (* malloc library *)
  malloc_start : Addr;
  malloc_memptr : Addr;
  malloc_mem_start : Addr;
  malloc_end : Addr;

  malloc_code_size :
    (malloc_start + length malloc_subroutine_instrs)%a
    = Some malloc_memptr;

  malloc_memptr_size :
    (malloc_memptr + 1)%a = Some malloc_mem_start;

  malloc_mem_size :
    (malloc_mem_start <= malloc_end)%a;

  (* assertion fail library *)
  fail_start : Addr;
  fail_end : Addr;

  fail_size :
    (fail_start
     + (length assert_fail_instrs (* code of the subroutine *)
        + 1 (* pointer to the flag *))
    )%a
    = Some fail_end;

  fail_flag : Addr;
  fail_flag_next : Addr;
  fail_flag_size :
    (fail_flag + 1)%a = Some fail_flag_next;

  (* disjointness of the two libraries *)
  libs_disjoint :     ## [
      [fail_flag];
      region_addrs fail_start fail_end;
      region_addrs malloc_mem_start malloc_end;
      [malloc_memptr];
      region_addrs malloc_start malloc_memptr
     ]
}.

Definition malloc_library_content `{MachineParameters} (layout : ocpl_library) : gmap Addr Word :=
  (* code for the malloc subroutine *)
  mkregion (malloc_start layout) (malloc_memptr layout) malloc_subroutine_instrs
  (* Capability to malloc's memory pool, used by the malloc subroutine *)
  ∪ list_to_map [((malloc_memptr layout), WCap RWX (malloc_memptr layout) (malloc_end layout) (malloc_mem_start layout))]
  (* Malloc's memory pool, initialized to zero *)
  ∪ mkregion (malloc_mem_start layout) (malloc_end layout) (region_addrs_zeroes (malloc_mem_start layout) (malloc_end layout)).

Definition lib_entry_malloc `{MachineParameters} (layout : ocpl_library) : lib_entry :=
  {| lib_start := malloc_start layout;
     lib_end := malloc_end layout;
     lib_entrypoint := malloc_start layout;
     lib_full_content := malloc_library_content layout|}.

(* FAIL library entry *)
Definition fail_library_content `{MachineParameters} (layout : ocpl_library) : gmap Addr Word :=
  (* code for the failure subroutine *)
  (* tail contains pointer to the "failure" flag, set to 1 by the routine *)
  mkregion (fail_start layout) (fail_end layout) (assert_fail_instrs ++ [WCap RW (fail_flag layout) (fail_flag_next layout) (fail_flag layout)])
  ∪ list_to_map [((fail_flag layout), WInt 0%Z)] (* failure flag, initially set to 0 *).

Definition lib_entry_fail `{MachineParameters} (layout : ocpl_library) : lib_entry :=
  {| lib_start := fail_start layout;
     lib_end := fail_end layout;
     lib_entrypoint := fail_start layout;
     lib_full_content := fail_library_content layout |}.

(* full library *)
Definition library `{MachineParameters} (layout : ocpl_library) : lib :=
  {| priv_libs := [lib_entry_fail layout] ;
     pub_libs := [lib_entry_malloc layout] |}.

Definition OK_invariant `{MachineParameters} (layout : ocpl_library) (m : gmap Addr Word) : Prop :=
  ∀ w, m !! (fail_flag layout) = Some w → w = WInt 0%Z.

Definition OK_dom `{MachineParameters} (layout : ocpl_library) : gset Addr := {[ fail_flag layout ]}.

Program Definition OK_dom_correct `{MachineParameters} (layout : ocpl_library) :
  ∀ m m',
    (∀ a, a ∈ OK_dom layout → ∃ x, m !! a = Some x ∧ m' !! a = Some x) →
    OK_invariant layout m ↔ OK_invariant layout m'.
Proof.
  intros m m' Hdom.
  destruct Hdom with (fail_flag layout) as [w [Hw1 Hw2] ]. rewrite /OK_dom. set_solver.
  split;intros HOK;intros w' Hw';simplify_eq;apply HOK;auto.
Defined.

Definition flag_inv `{MachineParameters} (layout : ocpl_library) : memory_inv :=
  {| minv := OK_invariant layout;
     minv_dom := {[ fail_flag layout ]} ;
     minv_dom_correct := OK_dom_correct layout |}.

Lemma flag_inv_is_initial_memory `{MachineParameters} (layout : ocpl_library) trusted_prog adv_prog trusted_table adv_table m :
  is_initial_memory trusted_prog adv_prog (library layout) trusted_table adv_table m →
  minv (flag_inv layout) m.
Proof.
  intros Hinit. intros a Hin.
  destruct Hinit as (?&?&Hlibs&?&?&?&Hlibdisj).
  cbn in Hlibs. rewrite map_union_empty in Hlibs.
  assert ((fail_library_content layout) ⊆ m) as Hfail.
  { etrans;[|eauto]. apply map_union_subseteq_r. cbn in Hlibdisj.
    rewrite !map_union_empty in Hlibdisj. auto. }
  rewrite /fail_library_content in Hfail.
  assert (list_to_map [(fail_flag layout, WInt 0)] ⊆ m) as Hfail_flag.
  { etrans;[|eauto]. apply map_union_subseteq_r. disjoint_map_to_list.
    pose proof (libs_disjoint layout) as Hdisjoint.
    rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?).
    set_solver. }
  simpl in Hfail_flag.
  eapply (lookup_weaken _ _ (fail_flag layout) (WInt 0)) in Hfail_flag.
    by simplify_eq. by simplify_map_eq.
Qed.

Lemma flag_inv_sub `{MachineParameters} (layout : ocpl_library) :
  minv_dom (flag_inv layout) ⊆ dom (gset Addr) (lib_region (priv_libs (library layout))).
Proof.
  cbn. rewrite map_union_empty.
  intros Hinit. rewrite /fail_library_content.
  rewrite /= dom_union_L dom_insert_L dom_empty_L.
  rewrite union_empty_r. apply union_subseteq_r.
Qed.

(* TODO: move to iris extra *)
Lemma big_sepM_to_big_sepL2 (PROP : bi) (A B : Type) `{EqDecision A} `{Countable A}
      (φ: A -> B -> PROP) (l1: list A) (l2: list B):
      NoDup l1 -> length l1 = length l2 →
      ⊢ (([∗ map] y1↦y2 ∈ list_to_map (zip l1 l2), φ y1 y2) -∗
         ([∗ list] y1;y2 ∈ l1;l2, φ y1 y2))%I.
Proof.
  revert l2. iInduction (l1) as [|x l1] "IH"; iIntros (l2 Hnd Hlen) "H".
  - iSimpl. destruct l2;inversion Hlen. done.
  - destruct l2;inversion Hlen. simpl.
    inversion Hnd. subst.
    iDestruct (big_sepM_insert with "H") as "[A B]".
    + eapply not_elem_of_list_to_map.
      rewrite fst_zip; auto. lia.
    + iFrame. iApply ("IH" $! l2 H4 H1 with "B"); auto.
Qed.
Lemma map_filter_id :
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M
    → ∀ (A : Type) (P : K * A → Prop) (H7 : ∀ x : K * A, Decision (P x)) (m : M A),
      (∀ i x, m !! i = Some x → P (i, x)) → filter P m = m.
Proof.
  intros. apply map_eq.
  intros i. destruct (m !! i) eqn:Hsome.
  - apply map_filter_lookup_Some_2;auto.
  - apply map_filter_lookup_None_2;auto.
Qed.



Definition assertInv `{memG Σ, regG Σ, MachineParameters} (layout : ocpl_library) :=
  [[ fail_start layout, fail_end layout]]↦ₐ[[ assert_fail_instrs ++ [WCap RW (fail_flag layout) (fail_flag_next layout) (fail_flag layout)] ]]%I.
Definition mallocInv `{memG Σ, regG Σ, MachineParameters} (layout : ocpl_library) :=
  malloc_inv (malloc_start layout) (malloc_end layout).

Definition mallocN : namespace := nroot .@ "pub" .@ "malloc".
Definition failflagN : namespace := nroot .@ "priv" .@ "flag".

Theorem ocpl_template_adequacy `{MachineParameters} (Σ : gFunctors)
    (layout: ocpl_library)
    (P Adv: prog)
    (P_tbl : @tbl_priv P (library layout))
    (Adv_tbl : @tbl_pub Adv (library layout)) (r_adv : RegName)
    (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory P Adv (library layout) P_tbl Adv_tbl m →
  is_initial_registers P Adv (library layout) P_tbl Adv_tbl reg r_adv →
  Forall (λ w, is_cap w = false) (prog_instrs Adv) →

  let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom (flag_inv layout)) m in
  (∀ `{memG Σ', regG Σ', logrel_na_invs Σ', subG Σ Σ'} rmap,
      dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_adv ]} →
      ⊢ inv invN (minv_sep (flag_inv layout))
        ∗ na_inv logrel_nais mallocN (mallocInv layout)
        ∗ na_inv logrel_nais failflagN (assertInv layout)
        ∗ na_own logrel_nais ⊤
        ∗ PC ↦ᵣ WCap RWX (prog_lower_bound P_tbl) (prog_end P) (prog_start P)
        ∗ r_adv ↦ᵣ WCap RWX (prog_lower_bound Adv_tbl) (prog_end Adv) (prog_start Adv)
        ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
        (* P program and table *)
        ∗ (prog_lower_bound P_tbl) ↦ₐ (WCap RO (tbl_start P_tbl) (tbl_end P_tbl) (tbl_start P_tbl))
        ∗ ([∗ map] a↦w ∈ (tbl_region P_tbl), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ (prog_region P), a ↦ₐ w)
        (* Adv program and table *)
        ∗ (prog_lower_bound Adv_tbl) ↦ₐ (WCap RO (tbl_start Adv_tbl) (tbl_end Adv_tbl) (tbl_start Adv_tbl))
        ∗ ([∗ map] a↦w ∈ (tbl_region Adv_tbl), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ (prog_region Adv), a ↦ₐ w)

        -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  minv (flag_inv layout) m'.
Proof.
  set (Σ' := #[invΣ; gen_heapΣ Addr Word; gen_heapΣ RegName Word;
              na_invΣ; Σ]).
  intros ? ? ? ? Hspec.
  eapply (template_adequacy Σ');[eauto..|]; (* rewrite /invPreG. solve_inG. *)
    try typeclasses eauto.
  eapply flag_inv_is_initial_memory;eauto.
  eapply flag_inv_sub;eauto.
  intros. cbn.
  rewrite !map_union_empty.
  iIntros "(#Hflag & Hown & HPC & Hr_adv & Hrmap & Htbl & Htbl_r
           & Hprog & Htbl_adv & Htbl_adv_r & Hprog_adv & Hmalloc & Hfail)".

  (* allocate malloc invariant *)
  iMod (na_inv_alloc logrel_nais ⊤ mallocN (mallocInv layout)
          with "[Hmalloc]") as "#Hinv_malloc".
  { iNext. rewrite /mallocInv /malloc_inv. iExists (malloc_memptr layout), (malloc_mem_start layout).
    rewrite /malloc_library_content.
    iDestruct (big_sepM_union with "Hmalloc") as "[Hpubs Hinit]".
    { pose proof (libs_disjoint layout) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?).
      disjoint_map_to_list. set_solver. }
    iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hmid]".
    { pose proof (libs_disjoint layout) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?).
      disjoint_map_to_list. set_solver. }
    pose proof (malloc_code_size layout) as Hmalloc_size.
    pose proof (malloc_memptr_size layout) as Hmalloc_memptr_size.
    pose proof (malloc_mem_size layout) as Hmalloc_mem_size.
    iSplitL "Hpubs".
    iApply big_sepM_to_big_sepL2. apply region_addrs_NoDup.
    rewrite region_addrs_length /region_size.
    solve_addr +Hmalloc_size.
    assert (((malloc_start layout) ^+ length malloc_subroutine_instrs)%a = (malloc_memptr layout)) as ->
    ;[solve_addr+Hmalloc_size|iFrame].
    iSplit;[auto|]. iDestruct (big_sepM_insert with "Hmid") as "[$ _]";auto.
    iSplit;[|iPureIntro;solve_addr+Hmalloc_size Hmalloc_memptr_size Hmalloc_mem_size].
    iApply big_sepM_to_big_sepL2. apply region_addrs_NoDup.
    rewrite region_addrs_length replicate_length /region_size. solve_addr +Hmalloc_mem_size. iFrame. }

  (* allocate the flag invariant *)
  iMod (na_inv_alloc logrel_nais ⊤ failflagN (assertInv layout)
          with "[Hfail]") as "#Hinv_fail".
  { iNext. rewrite /assertInv /fail_library_content.
    rewrite -insert_union_r.
    pose proof (fail_flag_size layout) as Hfail_flag_size.
    pose proof (fail_size layout) as Hfail_size.
    rewrite map_union_empty map_filter_insert_not'.
    rewrite map_filter_id.
    - by iApply mkregion_sepM_to_sepL2.
    - intros i x Hx.
      assert (i ∈ region_addrs (fail_start layout) (fail_end layout)) as Hin.
      { eapply in_dom_mkregion. apply elem_of_gmap_dom. eauto. }
      intros Hcontr%elem_of_singleton_1. subst.
      pose proof (libs_disjoint layout) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?).
      set_solver.
    - simpl. intros Hcontr. apply Hcontr. apply elem_of_singleton. auto.
    - intros y _. intros Hcontr. apply Hcontr. apply elem_of_singleton. auto.
    - apply not_elem_of_dom.
      intros Hdom%in_dom_mkregion.
      pose proof (libs_disjoint layout) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?).
      set_solver. }

  iApply Hspec;[..|iFrame "∗ #"];auto. solve_inG.
Qed.

End ocpl.
