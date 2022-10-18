From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample malloc assert macros_new.
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

  (* assert library *)
  assert_start : Addr;
  assert_cap : Addr;
  assert_flag : Addr;
  assert_end : Addr;

  assert_code_size :
    (assert_start + length assert_subroutine_instrs)%a = Some assert_cap;
  assert_cap_size :
    (assert_cap + 1)%a = Some assert_flag;
  assert_flag_size :
    (assert_flag + 1)%a = Some assert_end;

  (* disjointness of the two libraries *)
  libs_disjoint : ## [
      finz.seq_between assert_start assert_end;
      finz.seq_between malloc_mem_start malloc_end;
      [malloc_memptr];
      finz.seq_between malloc_start malloc_memptr
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

(* assert library entry *)
Definition assert_library_content `{MachineParameters} (layout : ocpl_library) : gmap Addr Word :=
  (* code for the assert subroutine, followed by a capability to the assert flag
     and the flag itself, initialized to 0. *)
  mkregion (assert_start layout) (assert_cap layout) assert_subroutine_instrs
  ∪ list_to_map [(assert_cap layout, WCap RW (assert_flag layout) (assert_end layout) (assert_flag layout))]
  ∪ list_to_map [(assert_flag layout, WInt 0)] (* assert flag *).

Definition lib_entry_assert `{MachineParameters} (layout : ocpl_library) : lib_entry :=
  {| lib_start := assert_start layout;
     lib_end := assert_end layout;
     lib_entrypoint := assert_start layout;
     lib_full_content := assert_library_content layout |}.

(* full library *)
Definition library `{MachineParameters} (layout : ocpl_library) : lib :=
  {| priv_libs := [lib_entry_assert layout] ;
     pub_libs := [lib_entry_malloc layout] |}.

Definition OK_invariant `{MachineParameters} (layout : ocpl_library) (m : gmap Addr Word) : Prop :=
  ∀ w, m !! (assert_flag layout) = Some w → w = WInt 0%Z.

Definition OK_dom `{MachineParameters} (layout : ocpl_library) : gset Addr := {[ assert_flag layout ]}.

Program Definition OK_dom_correct `{MachineParameters} (layout : ocpl_library) :
  ∀ m m',
    (∀ a, a ∈ OK_dom layout → ∃ x, m !! a = Some x ∧ m' !! a = Some x) →
    OK_invariant layout m ↔ OK_invariant layout m'.
Proof.
  intros m m' Hdom.
  destruct Hdom with (assert_flag layout) as [w [Hw1 Hw2] ]. rewrite /OK_dom. set_solver.
  split;intros HOK;intros w' Hw';simplify_eq;apply HOK;auto.
Defined.

Definition flag_inv `{MachineParameters} (layout : ocpl_library) : memory_inv :=
  {| minv := OK_invariant layout;
     minv_dom := {[ assert_flag layout ]} ;
     minv_dom_correct := OK_dom_correct layout |}.

Lemma flag_inv_is_initial_memory `{MachineParameters} (layout : ocpl_library) trusted_prog adv_prog trusted_table adv_table m :
  is_initial_memory trusted_prog adv_prog (library layout) trusted_table adv_table m →
  minv (flag_inv layout) m.
Proof.
  intros Hinit. intros a Hin.
  destruct Hinit as (?&?&Hlibs&?&?&?&Hlibdisj).
  cbn in Hlibs. rewrite map_union_empty in Hlibs.
  assert ((assert_library_content layout) ⊆ m) as Hassert.
  { etrans;[|eauto]. apply map_union_subseteq_r. cbn in Hlibdisj.
    rewrite !map_union_empty in Hlibdisj. auto. }
  pose proof (assert_code_size layout). pose proof (assert_cap_size layout).
  pose proof (assert_flag_size layout).
  assert (list_to_map [(assert_flag layout, WInt 0)] ⊆ m) as Hassert_flag.
  { etrans;[|eauto]. eapply map_union_subseteq_r'. 2: done.
    pose proof (libs_disjoint layout) as Hdisjoint. disjoint_map_to_list.
    apply elem_of_disjoint. intro. rewrite elem_of_app !elem_of_finz_seq_between !elem_of_list_singleton.
    intros [ [? ?]|?] ->; solve_addr. }
  eapply (lookup_weaken _ _ (assert_flag layout) (WInt 0)) in Hassert_flag.
    by simplify_eq. by simplify_map_eq.
Qed.

Lemma flag_inv_sub `{MachineParameters} (layout : ocpl_library) :
  minv_dom (flag_inv layout) ⊆ dom (gset Addr) (lib_region (priv_libs (library layout))).
Proof.
  cbn. rewrite map_union_empty.
  intros ? Hinit. rewrite elem_of_singleton in Hinit |- * => ->.
  rewrite /assert_library_content.
  pose proof (assert_code_size layout). pose proof (assert_cap_size layout).
  pose proof (assert_flag_size layout).
  rewrite /= dom_union_L. apply elem_of_union_r.
  rewrite dom_insert_L. set_solver.
Qed.

Definition assertInv `{memG Σ, regG Σ, MachineParameters} (layout : ocpl_library) :=
  assert_inv (assert_start layout) (assert_flag layout) (assert_end layout).
Definition mallocInv `{memG Σ, regG Σ, MachineParameters} (layout : ocpl_library) :=
  malloc_inv (malloc_start layout) (malloc_end layout).

Definition mallocN : namespace := nroot .@ "pub" .@ "malloc".
Definition assertN : namespace := nroot .@ "priv" .@ "assert".

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
        ∗ na_inv logrel_nais assertN (assertInv layout)
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
  eapply (template_adequacy Σ');[eauto..|]; (* rewrite /invGpreS. solve_inG. *)
    try typeclasses eauto.
  eapply flag_inv_is_initial_memory;eauto.
  eapply flag_inv_sub;eauto.
  intros. cbn.
  rewrite !map_union_empty.
  iIntros "(#Hflag & Hown & HPC & Hr_adv & Hrmap & Htbl & Htbl_r
           & Hprog & Htbl_adv & Htbl_adv_r & Hprog_adv & Hmalloc & Hassert)".

  (* allocate malloc invariant *)
  iMod (na_inv_alloc logrel_nais ⊤ mallocN (mallocInv layout)
          with "[Hmalloc]") as "#Hinv_malloc".
  { iNext. rewrite /mallocInv /malloc_inv. iExists (malloc_memptr layout), (malloc_mem_start layout).
    rewrite /malloc_library_content.
    iDestruct (big_sepM_union with "Hmalloc") as "[Hpubs Hinit]".
    { pose proof (libs_disjoint layout) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?).
      disjoint_map_to_list. set_solver. }
    iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hmid]".
    { pose proof (libs_disjoint layout) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?).
      disjoint_map_to_list. set_solver. }
    pose proof (malloc_code_size layout) as Hmalloc_size.
    pose proof (malloc_memptr_size layout) as Hmalloc_memptr_size.
    pose proof (malloc_mem_size layout) as Hmalloc_mem_size.
    iSplitL "Hpubs".
    iApply big_sepM_to_big_sepL2. apply finz_seq_between_NoDup.
    rewrite finz_seq_between_length /finz.dist.
    solve_addr +Hmalloc_size.
    assert (((malloc_start layout) ^+ length malloc_subroutine_instrs)%a = (malloc_memptr layout)) as ->
    ;[solve_addr+Hmalloc_size|iFrame].
    iSplit;[auto|]. iDestruct (big_sepM_insert with "Hmid") as "[$ _]";auto.
    iSplit;[|iPureIntro;solve_addr+Hmalloc_size Hmalloc_memptr_size Hmalloc_mem_size].
    iApply big_sepM_to_big_sepL2. apply finz_seq_between_NoDup.
    rewrite finz_seq_between_length replicate_length /finz.dist. solve_addr +Hmalloc_mem_size. iFrame. }

  (* allocate the flag invariant *)
  iMod (na_inv_alloc logrel_nais ⊤ assertN (assertInv layout)
          with "[Hassert]") as "#Hinv_assert".
  { iNext. rewrite /assertInv /assert_inv /assert_library_content.
    iExists (assert_cap layout).
    pose proof (assert_code_size layout). pose proof (assert_cap_size layout).
    pose proof (assert_flag_size layout).
    rewrite map_filter_union.
    2: { disjoint_map_to_list. apply elem_of_disjoint. intro.
         rewrite elem_of_app elem_of_finz_seq_between !elem_of_list_singleton.
         intros [ [? ?]|?]; solve_addr. }
    iDestruct (big_sepM_union with "Hassert") as "[Hassert _]".
    { eapply map_filter_disjoint. typeclasses eauto. disjoint_map_to_list.
      apply elem_of_disjoint. intro.
      rewrite elem_of_app elem_of_finz_seq_between !elem_of_list_singleton.
      intros [ [? ?]|?]; solve_addr. }
    rewrite map_filter_id.
    2: { intros ? ? HH%elem_of_dom_2. rewrite !dom_union_L dom_mkregion_eq in HH.
         2: solve_addr. apply elem_of_union in HH.
         rewrite elem_of_singleton. destruct HH as [HH|HH].
         rewrite -> elem_of_list_to_set, elem_of_finz_seq_between in HH; solve_addr.
         rewrite -> dom_list_to_map_singleton, elem_of_list_to_set, elem_of_list_singleton in HH; solve_addr. }
    iDestruct (big_sepM_union with "Hassert") as "[Hassert Hcap]".
    { disjoint_map_to_list. apply elem_of_disjoint. intro.
      rewrite elem_of_finz_seq_between !elem_of_list_singleton. solve_addr. }
    iDestruct (mkregion_sepM_to_sepL2 with "Hassert") as "Hassert". solve_addr.
    rewrite (_: assert_cap layout = assert_start layout ^+ length assert_subroutine_instrs)%a. 2: solve_addr.
    iFrame "Hassert". iDestruct (big_sepM_insert with "Hcap") as "[Hcap _]". done.
    iFrame "Hcap". iPureIntro. repeat split; solve_addr. }

  iApply Hspec;[..|iFrame "∗ #"];auto. solve_inG.
Qed.

End ocpl.
