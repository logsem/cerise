From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample malloc macros_new lse.
From cap_machine.examples Require Export mkregion_helpers disjoint_regions_tactics.
From cap_machine.examples Require Import template_adequacy template_adequacy_ocpl.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Import ocpl.

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
  l_malloc_start : Addr;
  l_malloc_memptr : Addr;
  l_malloc_mem_start : Addr;
  l_malloc_end : Addr;

  l_malloc_code_size :
    (l_malloc_start + length malloc_subroutine_instrs)%a
    = Some l_malloc_memptr;

  l_malloc_memptr_size :
    (l_malloc_memptr + 1)%a = Some l_malloc_mem_start;

  l_malloc_mem_size :
    (l_malloc_mem_start <= l_malloc_end)%a;

  (* fail routine *)
  l_assert_start : Addr;
  l_assert_cap : Addr;
  l_assert_flag : Addr;
  l_assert_end : Addr;

  l_assert_code_size :
    (l_assert_start + length assert_subroutine_instrs)%a = Some l_assert_cap;
  l_assert_cap_size :
    (l_assert_cap + 1)%a = Some l_assert_flag;
  l_assert_flag_size :
    (l_assert_flag + 1)%a = Some l_assert_end;

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

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
        finz.seq_between adv_region_start adv_end;
        finz.seq_between f_region_start f_end;
        finz.seq_between link_table_start link_table_end;
        finz.seq_between adv_link_table_start adv_link_table_end;
        finz.seq_between l_assert_start l_assert_end;
        finz.seq_between l_malloc_mem_start l_malloc_end;
        [l_malloc_memptr];
        finz.seq_between l_malloc_start l_malloc_memptr
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

Program Definition layout `{memory_layout} : ocpl_library :=
  {| (* malloc library *)
     malloc_start := l_malloc_start;
     malloc_memptr := l_malloc_memptr;
     malloc_mem_start := l_malloc_mem_start;
     malloc_end := l_malloc_end;

     malloc_code_size := l_malloc_code_size;

     malloc_memptr_size := l_malloc_memptr_size;

     malloc_mem_size := l_malloc_mem_size;

     (* assertion fail library *)
     assert_start := l_assert_start;
     assert_cap := l_assert_cap;
     assert_flag := l_assert_flag;
     assert_end := l_assert_end;

     assert_code_size := l_assert_code_size;
     assert_cap_size := l_assert_cap_size;
     assert_flag_size := l_assert_flag_size;

     (* disjointness of the two libraries *)
     libs_disjoint := _
  |}.
Next Obligation.
  intros.
  pose proof (regions_disjoint) as Hdisjoint.
  rewrite !disjoint_list_cons in Hdisjoint |- *.
  set_solver.
Qed.
Definition OCPLLibrary `{memory_layout} := library layout.

Program Definition roe_table `{memory_layout} : @tbl_priv roe_prog OCPLLibrary :=
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
  rewrite !disjoint_list_cons in Hdisjoint |- *.
  disjoint_map_to_list. set_solver.
Qed.

Program Definition adv_table `{memory_layout} : @tbl_pub adv_prog OCPLLibrary :=
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
  rewrite !disjoint_list_cons in Hdisjoint |- *.
  disjoint_map_to_list. set_solver.
Qed.

Section roe_adequacy.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{memlayout: memory_layout}.

  Lemma roe_correct :
    Forall (λ w, is_cap w = false) adv_instrs →
    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom (flag_inv layout)) m in
  (∀ rmap,
      dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
      ⊢ inv invN (minv_sep (flag_inv layout))
        ∗ na_inv logrel_nais mallocN (mallocInv layout)
        ∗ na_inv logrel_nais assertN (assertInv layout)
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

        -∗ WP Seq (Instr Executable) {{ λ _, True }}).
  Proof.
    iIntros (Hints Hfilter rmap Hdom) "(#Hinv & #Hmalloc & #Hassert & Hown & HPC & Hr_adv & Hrmap & Hroe_link & Hroe_table & Hroe
                                 & Hadv_link & Hadv_table & Hadv)".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hrmapvalid]".
    simpl.

    (* setting up read only example program *)
    iAssert (roe (finz.seq_between f_start f_end) 0 1 r_adv) with "[Hroe] "as "Hroe".
    { rewrite /roe /prog_region /= /mkregion.
      iApply big_sepM_to_big_sepL2. apply finz_seq_between_NoDup.
      pose proof f_size as Hsize.
      rewrite finz_seq_between_length /finz.dist. solve_addr +Hsize.
      iFrame. }

    (* cleaning up the environment tables *)
    rewrite /tbl_region /mkregion /=.
    pose proof link_table_size as Hsize.
    assert (is_Some (link_table_start + 1)%a) as [link_table_mid Hmid]. solve_addr+Hsize.
    rewrite finz_seq_between_cons;[|solve_addr +Hsize].
    rewrite (addr_incr_eq Hmid) /= finz_seq_between_singleton /=;[|solve_addr +Hmid Hsize].
    pose proof adv_link_table_size as Hsize_adv.
    rewrite finz_seq_between_singleton /=;[|solve_addr +Hsize_adv].
    iDestruct (big_sepM_insert with "Hroe_table") as "[Hlink_table_start Hroe_table]".
    { rewrite lookup_insert_ne//. solve_addr +Hmid. }
    iDestruct (big_sepM_insert with "Hroe_table") as "[Hlink_table_mid _]";auto.
    iDestruct (big_sepM_insert with "Hadv_table") as "[Hadv_link_table_start _]";auto.

    (* determine malloc validity *)
    iDestruct (simple_malloc_subroutine_valid with "[$Hmalloc]") as "#Hmalloc_val".

    (* allocate adversary table *)
    iMod (inv_alloc (logN .@ adv_link_table_start) ⊤ (interp_ref_inv adv_link_table_start interp)
            with "[Hadv_link_table_start]") as "#Hadv_table_valid".
    { iNext. iExists _. iFrame. auto. }

    (* allocate validity of adversary *)
    pose proof adv_size as Hadv_size'.
    pose proof adv_region_start_offset as Hadv_region_offset.
    iDestruct (big_sepM_to_big_sepL2 with "Hadv") as "Hadv /=". apply finz_seq_between_NoDup.
    rewrite finz_seq_between_length /finz.dist /=. solve_addr+Hadv_size'.
    iMod (region_inv_alloc _ (finz.seq_between adv_region_start adv_end) (_::adv_instrs) with "[Hadv Hadv_link]") as "#Hadv".
    { rewrite (finz_seq_between_cons adv_region_start);
        [rewrite (addr_incr_eq Hadv_region_offset) /=|solve_addr +Hadv_region_offset Hadv_size'].
      iFrame. iSplit.
      { iApply fixpoint_interp1_eq. iSimpl. iClear "∗".
        rewrite finz_seq_between_singleton// /=. iSplit;[|done].
        iExists interp. iFrame "Hadv_table_valid". auto. }
      iApply big_sepL2_sep. iFrame. iApply big_sepL2_to_big_sepL_r.
      rewrite finz_seq_between_length /finz.dist /=. solve_addr+Hadv_size'.
      iApply big_sepL_forall. iIntros (k n Hin).
      revert Hints; rewrite Forall_forall =>Hints.
      assert (n ∈ adv_instrs) as HH%Hints;[apply elem_of_list_lookup;eauto|]. destruct n;inversion HH.
      iApply fixpoint_interp1_eq;eauto. }

    iAssert (interp (WCap RWX adv_region_start adv_end adv_start)) as "#Hadv_valid".
    { iClear "∗". iApply fixpoint_interp1_eq. iSimpl.
      iDestruct (big_sepL2_to_big_sepL_l with "Hadv") as "Hadv'".
      { rewrite finz_seq_between_length /finz.dist. solve_addr+Hadv_region_offset Hadv_size'. }
      iApply (big_sepL_mono with "Hadv'").
      iIntros (k y Hin) "Hint". iExists interp. iFrame. auto. }

    iApply (roe_spec with "[- $HPC $Hown $Hr_adv $Hroe_link $Hrmap $Hroe $Hmalloc $Hassert
                              $Hlink_table_start $Hlink_table_mid $Hadv_valid]");auto.
    instantiate (1:=f_end).
    { intros mid Hmid'. split;auto. pose proof (f_region_start_offset) as HH. solve_addr+HH Hmid'. }
    { apply contiguous_between_of_region_addrs;auto. pose proof (f_size) as HH. solve_addr+HH. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { solve_addr. }
    { solve_ndisj. }

    iApply (inv_iff with "Hinv []"). iNext. iModIntro.
    iSplit.
    - rewrite /minv_sep /=. iIntros "HH". iDestruct "HH" as (m) "(Hm & %Heq & %HOK)".
      assert (is_Some (m !! l_assert_flag)) as [? Hlook].
      { apply elem_of_gmap_dom. rewrite Heq. apply elem_of_singleton. auto. }
      iDestruct (big_sepM_lookup _ _ l_assert_flag with "Hm") as "Hflag";eauto.
      apply HOK in Hlook as ->. iFrame.
    - iIntros "HH". iExists {[ l_assert_flag := WInt 0%Z ]}.
      rewrite big_sepM_singleton. iFrame.
      rewrite dom_singleton_L /minv_dom /=. iSplit;auto.
      rewrite /OK_invariant. iPureIntro. intros w Hw. simplify_map_eq. done.
  Qed.

End roe_adequacy.

Theorem roe_adequacy `{memory_layout}
    (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory roe_prog adv_prog OCPLLibrary roe_table adv_table m →
  is_initial_registers roe_prog adv_prog OCPLLibrary roe_table adv_table reg r_adv →
  Forall (λ w, is_cap w = false) (prog_instrs adv_prog) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  (∀ w, m' !! l_assert_flag = Some w → w = WInt 0%Z).
Proof.
  intros ? ? Hints ?.
  set (Σ' := #[]).
  pose proof (ocpl_template_adequacy Σ' layout roe_prog adv_prog roe_table adv_table) as Hadequacy.
  eapply Hadequacy;eauto.
  intros Σ ? ? ? ?. apply roe_correct. apply Hints.
Qed.
