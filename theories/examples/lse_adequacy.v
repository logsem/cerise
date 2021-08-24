From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample malloc macros_new lse.
From cap_machine.examples Require Export mkregion_helpers disjoint_regions_tactics.
From cap_machine.examples Require Import template_adequacy.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Import with_adv_and_link.

Class memory_layout `{MachineParameters} := {
  (* Code of f *)
  f_region_start : Addr;
  f_start : Addr;
  f_end : Addr;
  f_size: (f_start + (length (roe_instrs 0 1 r_adv)) = Some f_end)%a;
  f_region_start_offset: (f_region_start + 1)%a = Some f_start;

  (* adversary code *)
  adv_region_start : Addr;
  adv_start : Addr;
  adv_end : Addr;
  adv_instrs : list Word;
  adv_size : (adv_start + (length adv_instrs) = Some adv_end)%a ;
  adv_region_start_offset: (adv_region_start + 1)%a = Some adv_start;

  (* malloc routine *)
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

  (* fail routine *)
  fail_start : Addr;
  fail_end : Addr;

  fail_size :
    (fail_start
     + (length assert_fail_instrs (* code of the subroutine *)
        + 1 (* pointer to the flag *))
    )%a
    = Some fail_end;

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 2)%a = Some link_table_end;

  (* adversary link table *)
  adv_link_table_start : Addr;
  adv_link_table_end : Addr;
  adv_link_table_size :
    (adv_link_table_start + 1)%a = Some adv_link_table_end;

  (* failure flag *)
  fail_flag : Addr;
  fail_flag_next : Addr;
  fail_flag_size :
    (fail_flag + 1)%a = Some fail_flag_next;

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
        region_addrs adv_region_start adv_end;
        region_addrs f_region_start f_end;
        [fail_flag];
        region_addrs link_table_start link_table_end;
        region_addrs adv_link_table_start adv_link_table_end;
        region_addrs fail_start fail_end;
        region_addrs malloc_mem_start malloc_end;
        [malloc_memptr];
        region_addrs malloc_start malloc_memptr
       ]
}.

Definition roe_prog `{memory_layout} : prog :=
  {| prog_start := f_start ;
     prog_end := f_end ;
     prog_instrs := (roe_instrs 0 1 r_adv) ;
     prog_size := f_size |}.

Definition adv_prog `{memory_layout} : prog :=
  {| prog_start := adv_start ;
     prog_end := adv_end ;
     prog_instrs := adv_instrs ;
     prog_size := adv_size |}.

(* MALLOC library entry *)
Definition malloc_library_content `{memory_layout} : gmap Addr Word :=
  (* code for the malloc subroutine *)
  mkregion malloc_start malloc_memptr malloc_subroutine_instrs
  (* Capability to malloc's memory pool, used by the malloc subroutine *)
  ∪ list_to_map [(malloc_memptr, WCap RWX malloc_memptr malloc_end malloc_mem_start)]
  (* Malloc's memory pool, initialized to zero *)
  ∪ mkregion malloc_mem_start malloc_end (region_addrs_zeroes malloc_mem_start malloc_end).

Definition lib_entry_malloc `{memory_layout} : lib_entry :=
  {| lib_start := malloc_start ;
     lib_end := malloc_end ;
     lib_entrypoint := malloc_start ;
     lib_full_content := malloc_library_content |}.

(* FAIL library entry *)
Definition fail_library_content `{memory_layout} : gmap Addr Word :=
  (* code for the failure subroutine *)
  (* tail contains pointer to the "failure" flag, set to 1 by the routine *)
  mkregion fail_start fail_end (assert_fail_instrs ++ [WCap RW fail_flag fail_flag_next fail_flag])
  ∪ list_to_map [(fail_flag, WInt 0%Z)] (* failure flag, initially set to 0 *).

Definition lib_entry_fail `{memory_layout} : lib_entry :=
  {| lib_start := fail_start ;
     lib_end := fail_end ;
     lib_entrypoint := fail_start ;
     lib_full_content := fail_library_content |}.

(* full library *)
Definition library `{memory_layout} : lib :=
  {| priv_libs := [lib_entry_fail] ;
     pub_libs := [lib_entry_malloc] |}.

Program Definition roe_table `{memory_layout} : @tbl_priv roe_prog library :=
  {| prog_lower_bound := f_region_start ;
     tbl_start := link_table_start ;
     tbl_end := link_table_end ;
     tbl_size := link_table_size ;
     tbl_prog_link := f_region_start_offset ;
     tbl_disj := _
  |}.
Next Obligation.
  intros. simpl.
  pose proof (regions_disjoint) as Hdisjoint.
  rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
  disjoint_map_to_list. set_solver.
Qed.

Program Definition adv_table `{memory_layout} : @tbl_pub adv_prog library :=
  {| prog_lower_bound := adv_region_start ;
     tbl_start := adv_link_table_start ;
     tbl_end := adv_link_table_end ;
     tbl_size := adv_link_table_size ;
     tbl_prog_link := adv_region_start_offset ;
     tbl_disj := _
  |}.
Next Obligation.
  intros. simpl.
  pose proof (regions_disjoint) as Hdisjoint.
  rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
  disjoint_map_to_list. set_solver.
Qed.


Definition OK_invariant `{MachineParameters} `{memory_layout} (m : gmap Addr Word) : Prop :=
  ∀ w, m !! fail_flag = Some w → w = WInt 0%Z.

Definition OK_dom `{MachineParameters} `{memory_layout} : gset Addr := {[ fail_flag ]}.

Program Definition OK_dom_correct `{MachineParameters} `{memory_layout} :
  ∀ m m',
    (∀ a, a ∈ OK_dom → ∃ x, m !! a = Some x ∧ m' !! a = Some x) →
    OK_invariant m ↔ OK_invariant m'.
Proof.
  intros m m' Hdom.
  destruct Hdom with fail_flag as [w [Hw1 Hw2] ]. set_solver.
  split;intros HOK;intros w' Hw';simplify_eq;apply HOK;auto.
Defined.

Definition flag_inv `{MachineParameters} `{memory_layout} : memory_inv :=
  {| minv := OK_invariant ;
     minv_dom := {[ fail_flag ]} ;
     minv_dom_correct := OK_dom_correct |}.

Lemma flag_inv_is_initial_memory `{memory_layout} m :
  is_initial_memory roe_prog adv_prog library roe_table adv_table m →
  minv flag_inv m.
Proof.
  intros Hinit. intros a Hin.
  destruct Hinit as (?&?&Hlibs&?&?&?&Hlibdisj).
  cbn in Hlibs. rewrite map_union_empty in Hlibs.
  assert (fail_library_content ⊆ m) as Hfail.
  { etrans;[|eauto]. apply map_union_subseteq_r. cbn in Hlibdisj.
    rewrite !map_union_empty in Hlibdisj. auto. }
  rewrite /fail_library_content in Hfail.
  assert (list_to_map [(fail_flag, WInt 0)] ⊆ m) as Hfail_flag.
  { etrans;[|eauto]. apply map_union_subseteq_r. disjoint_map_to_list.
    pose proof (regions_disjoint) as Hdisjoint.
    rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
    set_solver. }
  simpl in Hfail_flag.
  eapply (lookup_weaken _ _ fail_flag (WInt 0)) in Hfail_flag.
  by simplify_eq. by simplify_map_eq.
Qed.

Lemma flag_inv_sub `{memory_layout} :
  minv_dom flag_inv ⊆ dom (gset Addr) (lib_region (priv_libs library)).
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

Section roe_adequacy.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{memlayout: memory_layout}.

  Definition mallocN : namespace := nroot .@ "roe" .@ "malloc".

  Lemma roe_correct :
    Forall (λ w, is_cap w = false) adv_instrs →
    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom flag_inv) m in
  (∀ rmap,
      dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_adv ]} →
      ⊢ inv invN (minv_sep flag_inv)
        ∗ na_own logrel_nais ⊤
        ∗ PC ↦ᵣ WCap RWX (prog_lower_bound roe_table) (prog_end roe_prog) (prog_start roe_prog)
        ∗ r_adv ↦ᵣ WCap RWX (prog_lower_bound adv_table) (prog_end adv_prog) (prog_start adv_prog)
        ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
        (* P program and table *)
        ∗ (prog_lower_bound roe_table) ↦ₐ (WCap RO (tbl_start roe_table) (tbl_end roe_table) (tbl_start roe_table))
        ∗ ([∗ map] a↦w ∈ (tbl_region roe_table), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ (prog_region roe_prog), a ↦ₐ w)
        (* Adv program and table *)
        ∗ (prog_lower_bound adv_table) ↦ₐ (WCap RO (tbl_start adv_table) (tbl_end adv_table) (tbl_start adv_table))
        ∗ ([∗ map] a↦w ∈ (tbl_region adv_table), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ (prog_region adv_prog), a ↦ₐ w)
        (* filtered entries *)
        ∗ ([∗ map] a↦w ∈ (lib_region (pub_libs library)), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ filtered_map (lib_region (priv_libs library)), a ↦ₐ w)

        -∗ WP Seq (Instr Executable) {{ λ _, True }}).
  Proof.
    iIntros (Hints Hfilter rmap Hdom) "(#Hinv & Hown & HPC & Hr_adv & Hrmap & Hroe_link & Hroe_table & Hroe
                                 & Hadv_link & Hadv_table & Hadv & Hpubs & Hprivs)".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hrmapvalid]".
    simpl. rewrite !map_union_empty.

    (* setting up read only example program *)
    iAssert (roe (region_addrs f_start f_end) 0 1 r_adv) with "[Hroe] "as "Hroe".
    { rewrite /roe /prog_region /= /mkregion.
      iApply big_sepM_to_big_sepL2. apply region_addrs_NoDup.
      pose proof f_size as Hsize.
      rewrite region_addrs_length /region_size. solve_addr +Hsize.
      iFrame. }

    (* cleaning up the environment tables *)
    rewrite /tbl_region /mkregion /=.
    pose proof link_table_size as Hsize.
    assert (is_Some (link_table_start + 1)%a) as [link_table_mid Hmid]. solve_addr+Hsize.
    rewrite region_addrs_cons;[|solve_addr +Hsize].
    rewrite Hmid /= region_addrs_single /=;[|solve_addr +Hmid Hsize].
    pose proof adv_link_table_size as Hsize_adv.
    rewrite region_addrs_single /=;[|solve_addr +Hsize_adv].
    iDestruct (big_sepM_insert with "Hroe_table") as "[Hlink_table_start Hroe_table]".
    { rewrite lookup_insert_ne//. solve_addr +Hmid. }
    iDestruct (big_sepM_insert with "Hroe_table") as "[Hlink_table_mid _]";auto.
    iDestruct (big_sepM_insert with "Hadv_table") as "[Hadv_link_table_start _]";auto.

    (* allocate malloc invariant *)
    iMod (na_inv_alloc logrel_nais ⊤ mallocN (malloc_inv malloc_start malloc_end)
            with "[Hpubs]") as "#Hinv_malloc".
    { iNext. rewrite /malloc_inv. iExists malloc_memptr, malloc_mem_start.
      rewrite /malloc_library_content.
      iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hinit]".
      { pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
        disjoint_map_to_list. set_solver. }
      iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hmid]".
      { pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
        disjoint_map_to_list. set_solver. }
      pose proof malloc_code_size as Hmalloc_size.
      pose proof malloc_memptr_size as Hmalloc_memptr_size.
      pose proof malloc_mem_size as Hmalloc_mem_size.
      iSplitL "Hpubs".
      iApply big_sepM_to_big_sepL2. apply region_addrs_NoDup.
      rewrite region_addrs_length /region_size.  solve_addr +Hmalloc_size.
      assert ((malloc_start ^+ length malloc_subroutine_instrs)%a = malloc_memptr) as ->
      ;[solve_addr+Hmalloc_size|iFrame].
      iSplit;[auto|]. iDestruct (big_sepM_insert with "Hmid") as "[$ _]";auto.
      iSplit;[|iPureIntro;solve_addr+Hmalloc_size Hmalloc_memptr_size Hmalloc_mem_size].
      iApply big_sepM_to_big_sepL2. apply region_addrs_NoDup.
      rewrite region_addrs_length replicate_length /region_size. solve_addr +Hmalloc_mem_size. iFrame. }
    iDestruct (simple_malloc_subroutine_valid with "[$Hinv_malloc]") as "#Hmalloc_val".

    (* allocate adversary table *)
    iMod (inv_alloc (logN .@ adv_link_table_start) ⊤ (interp_ref_inv adv_link_table_start interp)
            with "[Hadv_link_table_start]") as "#Hadv_table_valid".
    { iNext. iExists _. iFrame. auto. }

    (* allocate validity of adversary *)
    pose proof adv_size as Hadv_size'.
    pose proof adv_region_start_offset as Hadv_region_offset.
    iDestruct (big_sepM_to_big_sepL2 with "Hadv") as "Hadv /=". apply region_addrs_NoDup.
    rewrite region_addrs_length /region_size /=. solve_addr+Hadv_size'.
    iMod (region_inv_alloc _ (region_addrs adv_region_start adv_end) (_::adv_instrs) with "[Hadv Hadv_link]") as "#Hadv".
    { rewrite (region_addrs_cons adv_region_start);[rewrite Hadv_region_offset /=|solve_addr +Hadv_region_offset Hadv_size'].
      iFrame. iSplit.
      { iApply fixpoint_interp1_eq. iSimpl. iClear "∗".
        rewrite region_addrs_single// /=. iSplit;[|done].
        iExists interp. iFrame "Hadv_table_valid". auto. }
      iApply big_sepL2_sep. iFrame. iApply big_sepL2_to_big_sepL_r.
      rewrite region_addrs_length /region_size /=. solve_addr+Hadv_size'.
      iApply big_sepL_forall. iIntros (k n Hin).
      revert Hints; rewrite Forall_forall =>Hints.
      assert (n ∈ adv_instrs) as HH%Hints;[apply elem_of_list_lookup;eauto|]. destruct n;inversion HH.
      iApply fixpoint_interp1_eq;eauto. }

    iAssert (interp (WCap RWX adv_region_start adv_end adv_start)) as "#Hadv_valid".
    { iClear "∗". iApply fixpoint_interp1_eq. iSimpl.
      iDestruct (big_sepL2_to_big_sepL_l with "Hadv") as "Hadv'".
      { rewrite region_addrs_length /region_size. solve_addr+Hadv_region_offset Hadv_size'. }
      iApply (big_sepL_mono with "Hadv'").
      iIntros (k y Hin) "Hint". iExists interp. iFrame. auto. }

    iApply (roe_spec with "[- $HPC $Hown $Hr_adv $Hroe_link $Hrmap $Hroe $Hinv_malloc
                              $Hlink_table_start $Hlink_table_mid $Hadv_valid]");auto.
    instantiate (1:=f_end).
    { intros mid Hmid'. split;auto. pose proof (f_region_start_offset) as HH. solve_addr+HH Hmid'. }
    { apply contiguous_between_of_region_addrs;auto. pose proof (f_size) as HH. solve_addr+HH. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { solve_addr. }

    iApply (inv_iff with "Hinv []"). iNext. iModIntro.
    iSplit.
    - rewrite /minv_sep /=. iIntros "HH". iDestruct "HH" as (m) "(Hm & %Heq & %HOK)".
      assert (is_Some (m !! fail_flag)) as [? Hlook].
      { apply elem_of_gmap_dom. rewrite Heq. apply elem_of_singleton. auto. }
      iDestruct (big_sepM_lookup _ _ fail_flag with "Hm") as "Hflag";eauto.
      apply HOK in Hlook as ->. iFrame.
    - iIntros "HH". iExists {[ fail_flag := WInt 0%Z ]}.
      rewrite big_sepM_singleton. iFrame.
      rewrite dom_singleton_L /minv_dom /=. iSplit;auto.
      rewrite /OK_invariant. iPureIntro. intros w Hw. simplify_map_eq. done.
  Qed.

End roe_adequacy.

Theorem template_adequacy `{memory_layout}
    (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory roe_prog adv_prog library roe_table adv_table m →
  is_initial_registers roe_prog adv_prog library roe_table adv_table reg r_adv →
  Forall (λ w, is_cap w = false) (prog_instrs adv_prog) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  (∀ w, m' !! fail_flag = Some w → w = WInt 0%Z).
Proof.
  intros ? ? Hints ?.
  set (Σ' := #[]).
  pose proof (template_adequacy Σ' roe_prog adv_prog library roe_table adv_table flag_inv) as Hadequacy.
  eapply Hadequacy;eauto.
  { apply flag_inv_is_initial_memory. auto. }
  { apply flag_inv_sub. }
  intros Σ ? ? ? ?. apply roe_correct. apply Hints.
Qed.
