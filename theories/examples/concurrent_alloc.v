From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine.examples Require Export mkregion_helpers
  disjoint_regions_tactics contiguous.
From cap_machine Require Import safe_malloc macros.
From cap_machine.examples Require Export template_adequacy_concurrency.
From cap_machine.examples Require Import template_adequacy_concurrency_ocpl.
From iris.program_logic Require Import adequacy.
Open Scope Z_scope.

Section concurrent_alloc.
  Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
          `{static_spinlock.lockG Σ, MP: MachineParameters}.

  Definition check_alloc_instrs' (f_m f_a : Z) : list Word :=
    (* code: *)
    malloc_instrs f_m 1 ++    (* Allocate a memory region*)
      encodeInstrsW [
        Store r_t1 42;        (* Store a secret in the region *)
        Mov r_t5 42 ;         (* Prepare the assert *)
        Load r_t4 r_t1
      ] ++ assert_instrs f_a ++
      encodeInstrsW [ Halt ].

  Definition check_alloc_instrs a_prog f_m f_a :=
    ([∗ list] a_i;w ∈ a_prog;(check_alloc_instrs' f_m f_a), a_i ↦ₐ w)%I.

  (* Invariant *)
  Definition c_mallocN : namespace := nroot .@ "concurrent_malloc".

  (* Malloc invariant *)
  Definition mallocN := (c_mallocN.@"malloc").
  Definition mallocN_inv b_m e_m γ :=
    inv mallocN (malloc_inv b_m e_m γ).


  Definition assertN := (c_mallocN.@"assert").
  Definition flagN := (c_mallocN.@"flag").
  Definition assertN_inv b_a e_a a_flag :=
    (inv assertN (assert_inv b_a a_flag e_a)
    ∗ inv flagN (a_flag ↦ₐ WInt 0%Z))%I.

  Lemma secret_prog_spec
    i
    p b e link1 a
    b_mem e_mem
    w4 w5
    EN φ :

    ExecPCPerm p →
    SubBounds b e link1 (link1 ^+ 3)%a ->
    contiguous_between a link1 (link1 ^+ 3)%a →
    (link1 + 3)%a = Some (link1 ^+ 3)%a ->
   withinBounds b_mem e_mem b_mem = true ->

    ((i, PC) ↦ᵣ WCap p b e link1
     ∗ (i, r_t1) ↦ᵣ WCap RWX b_mem e_mem b_mem
     ∗ (i, r_t4) ↦ᵣ w4
     ∗ (i, r_t5) ↦ᵣ w5
     ∗ codefrag link1 (encodeInstrsW [Store r_t1 42; Mov r_t5 42 ; Load r_t4 r_t1])
     ∗ b_mem ↦ₐ WInt 0
     ∗ ▷ ((i, PC) ↦ᵣ WCap p b e (link1 ^+ 3)%a
          ∗ (i, r_t1) ↦ᵣ WCap RWX b_mem e_mem b_mem
          ∗ (i, r_t4) ↦ᵣ WInt 42
          ∗ (i, r_t5) ↦ᵣ WInt 42
          ∗ codefrag link1 (encodeInstrsW [Store r_t1 42; Mov r_t5 42 ; Load r_t4 r_t1])
          ∗ b_mem ↦ₐ WInt 42
          -∗ WP (i, Seq (Instr Executable)) @ EN {{ φ }})%I
     ⊢  WP (i, Seq (Instr Executable)) @ EN {{ φ }}%I).
  Proof.
    iIntros (HPC_perm HPC_bounds Hcont Hlink1 HVmem)
              "(HPC & Hr1 & Hr4 & Hr5 & Hprog & Hmem & Hφ)".
    iInstr "Hprog".
    { apply isCorrectPC_intro; [solve_addr| auto]. }
    { transitivity (Some (link1 ^+1)%a) ; solve_addr ; done. }
    iInstr "Hprog".
    { apply isCorrectPC_intro; [solve_addr| auto]. }
    { transitivity (Some (link1 ^+2)%a) ; solve_addr ; done. }
    iInstr "Hprog".
    { apply isCorrectPC_intro; [solve_addr| auto]. }
    { split ; eauto. }
    { transitivity (Some (link1 ^+3)%a) ; solve_addr ; done. }
    iApply "Hφ" ; iFrame.
  Qed.

  Lemma prog_malloc_spec
    (i : CoreN)
    (a_prog : Addr)
    (rmap : gmap (CoreN * RegName) Word) (* resources *)
    a p b e a_first a_last (* pc *)
    f_m b_m e_m (* malloc *)
    f_a b_a e_a a_flag (* assert *)
    b_link a_link e_link (* linking *)
    malloc_entry assert_entry
    γ EN :

    ExecPCPerm p →
    SubBounds b e a_first a_last ->
    contiguous_between a a_first a_last →
    withinBounds b_link e_link malloc_entry = true →
    withinBounds b_link e_link assert_entry = true →
    (a_link + f_m)%a = Some malloc_entry →
    (a_link + f_a)%a = Some assert_entry →

    dom rmap =
      (all_registers_s_core i) ∖ {[ (i, PC)]} →
    ↑c_mallocN ⊆ EN ->

    ⊢ ( mallocN_inv b_m e_m γ
        ∗ assertN_inv b_a e_a a_flag

        ∗ b ↦ₐ WCap RO b_link e_link a_link
        ∗ malloc_entry ↦ₐ WCap E b_m e_m b_m
        ∗ assert_entry ↦ₐ WCap E b_a e_a b_a
        ∗ check_alloc_instrs a f_m f_a

        ∗ (i, PC) ↦ᵣ WCap p b e a_first
        ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
        -∗ WP (i, Seq (Instr Executable)) @ EN {{λ v, True ∨ ⌜v = (i, FailedV)⌝ }})%I.
  Proof.
    iIntros (HPC_perm HPC_bounds Hcont Hbounds_malloc Hbounds_assert
               Hmalloc_entry Hassert_entry Hdom HEN)
      "(#Hinv_malloc & #(Hinv_assert & Hinv_flag) & Hlink & Hmalloc_entry
              & Hassert_entry & Hprog & HPC & Hrmap)"
    ; rewrite /mallocN_inv /check_alloc_instrs /check_alloc_instrs'.

    (* Split the program *)
    iDestruct (contiguous_between_program_split with "Hprog") as
      (malloc_prog rest1 link1) "(Hmalloc_prog & Hprog & #Hcont1)"
    ;[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont1 & Hcont2 & Heqapp1 & Hlink1).

    iDestruct (contiguous_between_program_split with "Hprog") as
      (secret_prog rest2 link2) "(Hsecret_prog & Hprog & #Hcont2)"
    ;[apply Hcont2|].
    iDestruct "Hcont2" as %(Hcont3 & Hcont4 & Heqapp2 & Hlink2).

    iDestruct (contiguous_between_program_split with "Hprog") as
      (assert_prog rest3 link3) "(Hassert_prog & Hprog_halt & #Hcont3)"
    ;[apply Hcont4|].
    iDestruct "Hcont3" as %(Hcont5 & Hcont6 & Heqapp3 & Hlink3).

    (* Get the necessary resource - extract the registers *)
    (* r0 *)
    assert (is_Some (rmap !! (i,r_t0)))
      as [w0 Hw0]
           by (rewrite elem_of_gmap_dom Hdom; set_solver+).
    iDestruct (big_sepM_delete _ _ (i, r_t0) with "Hrmap") as "[Hr0 Hrmap]"
    ; first eauto.

    (* Malloc specification *)
    iApply ( malloc_spec with
             "[- $Hinv_malloc $Hmalloc_entry $HPC $Hr0 $Hrmap $Hlink]")
    ; eauto ; [| | solve_ndisj | iFrame].
    { rewrite /contiguous.isCorrectPC_range; intros.
      apply isCorrectPC_ExecPCPerm_InBounds ; auto.
      apply contiguous_between_bounds in Hcont2.
      solve_addr.
    }
    { rewrite dom_delete_L Hdom ; set_solver+. }
    iNext
    ; iIntros "(HPC & Hmalloc_prog & Hlink & Hmalloc_entry & Hmem & Hr0 & Hrmap)"
    ; iDestruct "Hmem" as (b_mem e_mem) "(%Hb_mem & Hr1 & Hmem)".


    (* Get the necessary resource - extract the registers *)
    (* r4 r5 *)
    (* Store secret + prepare assert *)
    iDestruct (big_sepL2_length with "Hsecret_prog") as %Hlength_secretprog.
    iAssert (codefrag link1 (encodeInstrsW [Store r_t1 42; Mov r_t5 42; Load r_t4 r_t1]))
      with "[Hsecret_prog]"
      as "Hsecret_prog".
    { rewrite /codefrag. simpl. rewrite /region_mapsto.
      simpl in *.
      replace secret_prog with (finz.seq_between link1 (link1 ^+ 3%nat)%a).
      done.
      symmetry; apply region_addrs_of_contiguous_between.
      replace (link1 ^+ 3%nat)%a with link2. done.
      apply contiguous_between_length in Hcont3.
      rewrite Hlength_secretprog in Hcont3.
      solve_addr. }


    assert (is_Some (rmap !! (i,r_t4))) as [w4 Hw4] by (rewrite elem_of_gmap_dom Hdom; set_solver+).
    iDestruct (big_sepM_delete _ _ (i, r_t4) with "Hrmap") as "[Hr4 Hrmap]".
    { do 2 (rewrite lookup_insert_ne ; last simplify_pair_eq).
      by rewrite lookup_insert.
    }
    assert (is_Some (rmap !! (i,r_t5))) as [w5 Hw5] by (rewrite elem_of_gmap_dom Hdom; set_solver+).
    iDestruct (big_sepM_delete _ _ (i, r_t5) with "Hrmap") as "[Hr5 Hrmap]".
    { rewrite lookup_delete_ne ; last simplify_pair_eq.
      do 3 (rewrite lookup_insert_ne ; last simplify_pair_eq).
      by rewrite lookup_insert.
    }

    iDestruct ( region_mapsto_single with "[$Hmem]") as "Hmem"
    ; [eauto |].
    iDestruct "Hmem" as (v) "[Hmem %Hb]".
    rewrite /region_addrs_zeroes in Hb.
    rewrite (_: finz.dist b_mem e_mem = 1%nat) in Hb.
    2: { replace e_mem with (b_mem ^+ 1)%a by solve_addr.
         match goal with
         | h: _ |- finz.dist ?b (?b^+?n)%a = ?n' =>
             let H := fresh in
             assert (H : (b+n)%f = Some (b ^+ n)%a) by solve_addr
             ; apply (finz_incr_iff_dist b (b ^+n)%a n') in H
             ; destruct H as [_ H] ; apply H
         end.
    }
    cbn in Hb ; inversion Hb ; subst ; clear Hb.

    iApply (secret_prog_spec with "[- $HPC $Hmem $Hsecret_prog $Hr1 $Hr4 $Hr5]").
    eauto.
    rewrite /SubBounds ; split ; try split ; try solve_addr.
    apply contiguous_between_bounds in Hcont3, Hcont4, Hcont5, Hcont6.
    solve_addr.
    replace (link1 ^+3)%a with link2 by solve_addr.
    eauto.
    solve_addr.
    replace e_mem with (b_mem ^+ 1)%a by solve_addr.
    apply withinBounds_InBounds; solve_addr.
    iNext ; iIntros "(HPC & Hr1 & Hr4 & Hr5 & Hsecret_prog & Hmem)".


    (* Get the necessary resource - extract the registers *)
    (* r2 r3 *)
    assert (is_Some (rmap !! (i,r_t2))) as [w2 Hw2] by (rewrite elem_of_gmap_dom Hdom; set_solver+).
    iDestruct (big_sepM_delete _ _ (i, r_t2) with "Hrmap") as "[Hr2 Hrmap]".
    { do 2 (rewrite lookup_delete_ne ; last simplify_pair_eq).
      by rewrite lookup_insert.
    }

    assert (is_Some (rmap !! (i,r_t3))) as [w3 Hw3] by (rewrite elem_of_gmap_dom Hdom; set_solver+).
    iDestruct (big_sepM_delete _ _ (i, r_t3) with "Hrmap") as "[Hr3 Hrmap]".
    { do 3 (rewrite lookup_delete_ne ; last simplify_pair_eq).
      rewrite lookup_insert_ne ; last simplify_pair_eq.
      by rewrite lookup_insert.
    }

    iDestruct (big_sepL2_length with "Hprog_halt") as %Hlength_halt.
    replace (link1 ^+ 3)%a with link2 by solve_addr ; eauto.
    simpl in Hlength_halt.


    iApply (assert_success
             with
             "[- $HPC $Hr0 $Hr1 $Hr2 $Hr3 $Hr4 $Hr5
             $Hassert_prog $Hinv_assert $Hassert_entry $Hlink]") ; eauto.
    { rewrite /contiguous.isCorrectPC_range; intros.
      apply isCorrectPC_ExecPCPerm_InBounds ; auto.
      apply contiguous_between_bounds in Hcont6.
      solve_addr.
    }
    solve_ndisj.
    iNext ; iIntros "(Hr0 & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & HPC
                      & Hassert_prog & Hlink & Hassert_entry)".


    assert (Ha_last : (link3 + 1%nat)%a = Some a_last).
    { apply contiguous_between_length in Hcont6.
      rewrite Hlength_halt in Hcont6. solve_addr.
    }
    replace rest3 with (finz.seq_between link3 (link3 ^+ 1%nat)%a).
    2: {
      symmetry; apply region_addrs_of_contiguous_between.
      replace (link3 ^+ 1%nat)%a with a_last. done. solve_addr.
    }
    rewrite finz_seq_between_singleton ; last solve_addr.

    cbn; iDestruct "Hprog_halt" as "[ Hprog_halt _ ]".
    wp_instr.
    iApply (wp_halt with "[$HPC $Hprog_halt]").
    by rewrite decode_encode_instrW_inv.
    { apply isCorrectPC_intro; [solve_addr| auto]. }
    iNext ; iIntros "(HPC & Hprog_halt)".
    cbn.
    by wp_pure ; wp_end.
  Qed.
End concurrent_alloc.



Section adequacy.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Class memory_layout `{MachineParameters} := {
  (* Code of f *)
  f_region_start : Addr;
  f_start : Addr;
  f_end : Addr;
  f_size: (f_start + (length (check_alloc_instrs' 0 1)) = Some f_end)%a;
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
    (l_malloc_memptr + 3)%a = Some l_malloc_mem_start;

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


Definition alloc_prog `{memory_layout} : prog :=
  {| prog_start := f_start ;
     prog_end := f_end ;
     prog_instrs := (check_alloc_instrs' 0 1) ;
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


Program Definition alloc_table `{memory_layout} : @tbl_priv alloc_prog OCPLLibrary :=
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



Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
  `{static_spinlock.lockG Σ, MP: MachineParameters}.

Definition assertInv (layout : ocpl_library) :=
  assert_inv (assert_start layout) (assert_flag layout) (assert_end layout).
Definition mallocInv (layout : ocpl_library) γ :=
  malloc_inv (malloc_start layout) (malloc_end layout) γ.


Context {mem_layout:memory_layout}.
Lemma alloc_correct (i : CoreN) γ:
  (∀ (rmap : (gmap (CoreN*RegName) Word)) ,
      dom rmap = (all_registers_s_core i) ∖ {[ (i, PC) ]} →
    ⊢
     inv flagN (assert_flag layout ↦ₐ WInt 0)
       ∗ inv mallocN (mallocInv layout γ)
       ∗ inv assertN (assertInv layout)
       ∗ (i, PC) ↦ᵣ WCap RWX (prog_lower_bound alloc_table) (prog_end alloc_prog) (prog_start alloc_prog)
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)

       (* P program and table *)
       ∗ (prog_lower_bound alloc_table) ↦ₐ (WCap RO (tbl_start alloc_table) (tbl_end alloc_table) (tbl_start alloc_table))
       ∗ ([∗ map] a↦w ∈ (tbl_region alloc_table), a ↦ₐ w)
       ∗ ([∗ map] a↦w ∈ (prog_region alloc_prog), a ↦ₐ w)
     -∗ WP (i, Seq (Instr Executable)) {{ fun _ => True }}%I).
Proof.
  iIntros (rmap Hdom) "(#Hinv & #Hmalloc & #Hassert & HPC & Hrmap & Hlink & Htable & Hprog)".
  iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hrmapvalid]".
  simpl.

  (* setting up example program *)
  iAssert (check_alloc_instrs (finz.seq_between f_start f_end) 0 1) with "[Hprog] "as "Hprog".
  { rewrite /check_alloc_instrs /prog_region /= /mkregion.
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
  iDestruct (big_sepM_insert with "Htable") as "[Hlink_table_start Htable]".
  { rewrite lookup_insert_ne ; first done. solve_addr +Hmid. }
  iDestruct (big_sepM_insert with "Htable") as "[Hlink_table_mid _]";auto.

  (* determine malloc validity *)
  iDestruct (simple_malloc_subroutine_valid with "[$Hmalloc]") as "#Hmalloc_val" .
  rewrite /mallocInv /assertInv.



  iApply (wp_wand with "[-]").
  - iApply (prog_malloc_spec with
             "[- $Hmalloc $Hassert $Hlink $Hlink_table_start $Hlink_table_mid $Hprog $HPC $Hrmap]");auto.
    apply ExecPCPerm_RWX.
    instantiate (1:=f_end).
    { split;auto
      ; pose proof (f_region_start_offset) as HH
      ; pose proof (f_size) as HH2.
      solve_addr+HH.
      split; solve_addr+HH2. }
    { apply contiguous_between_of_region_addrs;auto. pose proof (f_size) as HH. solve_addr+HH. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { solve_addr. }
  - by iIntros.
Qed.

Lemma adv_correct (i: CoreN) γ :
  Forall (λ w, is_cap w = false) adv_instrs →
  (∀ (rmap : (gmap (CoreN*RegName) Word)) ,
     dom rmap = (all_registers_s_core i) ∖ {[ (i, PC) ]} →
     ⊢ inv mallocN (mallocInv layout γ)
       ∗ (i, PC) ↦ᵣ WCap RWX (prog_lower_bound adv_table) (prog_end adv_prog) (prog_start adv_prog)
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)

       (* P program and table *)
       ∗ (prog_lower_bound adv_table) ↦ₐ (WCap RO (tbl_start adv_table) (tbl_end adv_table) (tbl_start adv_table))
       ∗ ([∗ map] a↦w ∈ (tbl_region adv_table), a ↦ₐ w)
       ∗ ([∗ map] a↦w ∈ (prog_region adv_prog), a ↦ₐ w)
       -∗ WP (i, Seq (Instr Executable)) {{ fun _ => True }}%I).
Proof.
  iIntros (Hints rmap Hdom) "(#Hmalloc & HPC & Hrmap & Hlink & Htable & Hprog)".
  iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hrmapvalid]".
  simpl.


  (* cleaning up the environment tables *)
  rewrite /tbl_region /mkregion /=.
  pose proof adv_link_table_size as Hsize_adv.
  rewrite finz_seq_between_singleton /=;[|solve_addr +Hsize_adv].
    iDestruct (big_sepM_insert with "Htable") as "[Hadv_link_table_start _]";auto.

  (* determine malloc validity *)
  iDestruct (simple_malloc_subroutine_valid with "[$Hmalloc]") as "#Hmalloc_val".


  (* allocate adversary table *)
  iMod (inv_alloc (logN .@ adv_link_table_start) ⊤ (interp_ref_inv adv_link_table_start interp)
         with "[Hadv_link_table_start]") as "#Hadv_table_valid".
  { iNext. iExists _; iFrame; auto. }

  (* allocate validity of adversary *)
  pose proof adv_size as Hadv_size'.
  pose proof adv_region_start_offset as Hadv_region_offset.
  iDestruct (big_sepM_to_big_sepL2 with "Hprog") as "Hadv". apply finz_seq_between_NoDup.
  rewrite finz_seq_between_length /finz.dist /=. solve_addr+Hadv_size'.
  iMod (region_inv_alloc _ (finz.seq_between adv_region_start adv_end) (_::adv_instrs) with "[Hadv Hlink]") as "#Hadv".
  { rewrite (finz_seq_between_cons adv_region_start);
      [rewrite (addr_incr_eq Hadv_region_offset) /=|solve_addr +Hadv_region_offset Hadv_size'].
    iFrame. iSplit.
    { iApply fixpoint_interp1_eq. iSimpl. iClear "∗".
      rewrite finz_seq_between_singleton /= ; last solve_addr.
      iSplit;[|done].
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

  iDestruct (jmp_to_unknown_adv with "Hadv_valid") as "#Hcont"; first by right.

  iDestruct (big_sepM_sep with "[$Hrmap $Hrmapvalid]") as "Hrmap".
  iAssert ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
  { iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn. iIntros "[? %Hw]".
    iFrame. destruct w; [| by inversion Hw]. rewrite fixpoint_interp1_eq //. }

  iApply (wp_wand with "[-]").
  { iApply "Hcont" ; cycle 1. iFrame. iPureIntro. assumption. }
    eauto.
Qed.
End adequacy.


Section adequacy.

Context (Σ: gFunctors).
Context {inv_preg: invGpreS Σ}.
Context {mem_preg: gen_heapGpreS Addr Word Σ}.
Program Definition CP := {| coreNum := 2 ;  corePos := _ |}.
Next Obligation. lia. Defined.
Context {reg_preg: gen_heapGpreS ((@CoreN CP) * RegName) Word Σ}.
Context `{static_spinlock.lockG Σ, MP: MachineParameters}.
Context {mem_layout:memory_layout}.

Theorem alloc_adequacy
    (m m': Mem) (reg reg': @Reg CP) (es: list cap_lang.expr) (i j : @CoreN CP):


  (* Machine with 2 cores identified by {0, 1} *)
  i = core_zero ->
  j = (i^+1)%f ->

  with_lib.is_initial_memory_with_adv alloc_prog adv_prog OCPLLibrary
    alloc_table adv_table m →
  with_lib.is_initial_registers alloc_prog OCPLLibrary alloc_table reg i →
  with_lib.is_initial_registers_adv adv_prog OCPLLibrary adv_table reg j →
  Forall (λ w, is_cap w = false) (prog_instrs adv_prog) →

  rtc (@erased_step cap_lang) (init_cores, (reg, m)) (es, (reg', m')) →
  (∀ w, m' !! l_assert_flag = Some w → w = WInt 0%Z).
Proof.
  intros Hi Hj Hmem  Hreg Hreg_adv Hadv_ints Hstep.
  assert ( Hn_cores : (@coreNum CP) = 2 )  by done.
  apply erased_steps_nsteps in Hstep as (n & κs & Hstep).

    (* We apply the Iris adequacy theorem, and we unfold the definition,
       generate the resources and unfold the definition *)
    (* Mostly boilerplates *)
    eapply (@wp_strong_adequacy Σ cap_lang _ _
             init_cores (reg,m) n κs es (reg', m')) ; last assumption.
    intros.

    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)" .
    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ CP Hinv reg_heapg.

    iExists (fun σ κs _ _ => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (map (fun _ => (fun _ => True)%I) (@all_cores CP)).
    iExists (fun _ => True)%I. cbn.
    iExists _.
    iFrame.

    cbn in *.
    rewrite /with_lib.is_initial_memory_with_adv in Hmem.

    (* Split the memory *)
    iDestruct (big_sepM_subseteq with "Hmem") as "Hmem".
    by apply Hmem.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem_prog Hmem_lib]".
    { cbn ; destruct Hmem as (?&?&?&?&?); eauto.
      rewrite /lib_region /= in H1,H2,H3,H4. eauto.
      rewrite map_union_empty.
      rewrite !map_union_empty in H2,H3,H4.
      apply map_disjoint_union_r in H2 ;destruct H2.
      apply map_disjoint_union_r in H3 ;destruct H3.
      apply map_disjoint_union_l_2
      ; apply map_disjoint_sym
      ; apply map_disjoint_union_l_2
      ; eauto.
    }
    iDestruct (big_sepM_union with "Hmem_prog") as "[Hmem_alloc Hmem_adv]".
    { cbn. destruct Hmem as (?&?&?&?&?); eauto. }
    iDestruct (big_sepM_union with "Hmem_lib") as "[Hmem_lib_malloc Hmem_lib_assert]".
    { cbn. destruct Hmem as (?&?&?&?&?); eauto.
      by rewrite /lib_region /= map_union_empty in H4.
    }
    rewrite map_union_empty.
    cbn.
    rewrite /malloc_library_content /=.
    rewrite /assert_library_content /=.




    iMod (@own_alloc _ (excl.exclR unitO) _ (excl.Excl ())) as (γ) "Hown" ; first done.
    (* Allocation of all the required invariants *)
    (* invariant malloc *)
    iMod (inv_alloc
            mallocN
            ⊤ (mallocInv layout γ)
           with "[Hmem_lib_malloc Hown]") as "#Hinv_malloc".

    { iNext. rewrite /mallocInv /malloc_inv.
      simpl.

      replace (l_malloc_start ^+ malloc_subroutine_instrs_length)%a
        with l_malloc_memptr.
      2 : { pose proof l_malloc_code_size as Ha.
            rewrite /malloc_subroutine_instrs_length ; cbn in*
            ; clear -Ha ; solve_addr. }
      iDestruct (big_sepM_union with "Hmem_lib_malloc") as
        "[Hmem_lib_malloc Hmalloc_mem_pool]".
      { pose proof (libs_disjoint layout) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint |- *.
        apply map_disjoint_union_l_2.
        apply mkregion_disjoints.
        clear ; pose proof l_malloc_memptr_size ; solve_addr.
        apply map_disjoint_insert_l_2.
        apply mkregion_lookup_none.
        clear ; pose proof l_malloc_memptr_size ; solve_addr.
        apply map_disjoint_insert_l_2.
        apply mkregion_lookup_none.
        clear ; pose proof l_malloc_memptr_size ; solve_addr.
        apply map_disjoint_insert_l_2.
        apply mkregion_lookup_none.
        clear ; pose proof l_malloc_memptr_size ; solve_addr.
        apply map_disjoint_empty_l.
      }
      iDestruct (big_sepM_union with "Hmem_lib_malloc") as "[Hmalloc_prog Hmalloc_caps]".
      { clear.
        apply map_disjoint_insert_r_2.
        apply mkregion_lookup_none.
        clear ; pose proof l_malloc_memptr_size ; solve_addr.
        apply map_disjoint_insert_r_2.
        apply mkregion_lookup_none.
        clear ; pose proof l_malloc_memptr_size ; solve_addr.
        apply map_disjoint_insert_r_2.
        apply mkregion_lookup_none.
        clear ; pose proof l_malloc_memptr_size ; solve_addr.
        apply map_disjoint_empty_r. }
      iDestruct (big_sepM_insert with "Hmalloc_caps") as "[Hmalloc_cap_lock Hmalloc_caps]".
      { pose proof l_malloc_memptr_size as Ha.
        do 2 (rewrite lookup_insert_ne ; last (clear -Ha ; solve_addr)).
        by simplify_map_eq. }
      iDestruct (big_sepM_insert with "Hmalloc_caps") as "[Hmalloc_lock Hmalloc_cap]".
      { pose proof l_malloc_memptr_size as Ha.
        rewrite lookup_insert_ne ; last (clear -Ha ; solve_addr).
        by simplify_map_eq. }
      iDestruct (big_sepM_insert with "Hmalloc_cap") as "[Hmalloc_cap _]".
      { set_solver. }


    iSplitL "Hmalloc_prog".
    { rewrite /codefrag /region_mapsto /mkregion.
      iDestruct (big_sepM_to_big_sepL2 with "Hmalloc_prog") as "Hprog".
      apply finz_seq_between_NoDup.
      cbn.
      rewrite finz_seq_between_length.
      clear ; pose proof l_malloc_code_size.
      cbn in *.
      replace l_malloc_memptr with (l_malloc_start ^+ 41)%a by solve_addr.
      solve_dist_finz.
      replace (l_malloc_start ^+ length malloc_subroutine_instrs)%a
        with l_malloc_memptr
             by (clear ; pose proof l_malloc_code_size
                 ; rewrite /malloc_subroutine_instrs_length ; cbn in*
                 ; solve_addr).
      iFrame.
    }
    iSplitL "Hmalloc_cap_lock".
    { iFrame. }
    iSplitR.
    { iPureIntro.
      clear.
      split.
      pose proof l_malloc_code_size.
      rewrite /malloc_subroutine_instrs_length ; cbn in* ; solve_addr.
      pose proof l_malloc_mem_size.
      pose proof l_malloc_memptr_size.
      solve_addr. }
    rewrite /static_spinlock.is_lock.
    iLeft ; iFrame.
    iExists l_malloc_mem_start.
    iFrame.
    iSplitL.
    { rewrite /region_mapsto /mkregion.
      iDestruct (big_sepM_to_big_sepL2 with "Hmalloc_mem_pool") as "Hmem".
      apply finz_seq_between_NoDup.
      by rewrite /region_addrs_zeroes replicate_length finz_seq_between_length.
      iFrame.
    }
    iPureIntro. clear.
    pose proof l_malloc_memptr_size.
    pose proof l_malloc_mem_size.
    solve_addr.
    }


    iDestruct (big_sepM_union with "Hmem_lib_assert") as "[Hmem_assert Hmem_flag]".
    { clear.
      apply map_disjoint_union_l_2.
      apply map_disjoint_insert_r_2 ; last apply map_disjoint_empty_r.
      apply mkregion_lookup_none.
      clear ; pose proof l_assert_cap_size ; solve_addr.
      apply map_disjoint_insert_l_2 ; last apply map_disjoint_empty_l.
      clear ; pose proof l_assert_cap_size.
      rewrite lookup_insert_ne ; last solve_addr.
      by simplify_map_eq.
    }
    (* invariant flag *)
    iMod (inv_alloc
            flagN
            ⊤ (assert_flag layout ↦ₐ WInt 0)
           with "[Hmem_flag]") as "#Hinv_flag".
    { iNext.
      rewrite /assert_flag ; simpl.
      iDestruct ( big_sepM_insert with "Hmem_flag" ) as "[flag _]".
      { set_solver. }
      iFrame.
    }
    (* invariant assert *)
    iMod (inv_alloc
            assertN
            ⊤ (assertInv layout)
           with "[Hmem_assert]") as "#Hinv_assert".
    { iNext.
      rewrite /assertInv /assert_inv /=; simpl.
    iDestruct (big_sepM_union with "Hmem_assert") as "[Hassert Hcap]".
    { apply map_disjoint_insert_r_2 ; last apply map_disjoint_empty_r.
      apply mkregion_lookup_none.
      clear ; pose proof l_assert_cap_size ; solve_addr.
    }
    iDestruct (big_sepM_insert with "Hcap") as "[Hcap _]".
    { set_solver. }
    iSplitL "Hassert".
    { rewrite /codefrag /region_mapsto /mkregion.
      iDestruct (big_sepM_to_big_sepL2 with "Hassert") as "Hprog".
      apply finz_seq_between_NoDup.
      cbn.
      rewrite finz_seq_between_length.
      clear ; pose proof l_assert_code_size.
      cbn in *.
      replace l_assert_cap with (l_assert_start ^+ 13)%a by solve_addr.
      solve_dist_finz.
      replace (l_assert_start ^+ length assert_subroutine_instrs)%a
        with l_assert_cap
             by (clear ; pose proof l_assert_code_size ; solve_addr ).
      iFrame.
    }
    { iExists l_assert_cap.
      pose proof l_assert_code_size.
      pose proof l_assert_cap_size.
      pose proof l_assert_flag_size.
      cbn in H0.
      iFrame "%∗".
    }
    }

    iSplitL.
    (** For all cores, prove that it executes completely and safely *)
    {
      (* Since we have a machine with 2 cores, split the list into 2 WP *)
      unfold CoreN in i,j,Hi,Hj.
      rewrite /init_cores /all_cores.
      clear Hn_cores ; assert ( Hn_cores : (@coreNum CP) = 2 ) by done.
      assert (Hcores: i ≠ j).
      { rewrite /core_zero in Hi ; cbn in *. solve_finz. }
      fold (@CoreN CP) in i,j.
      rewrite /core_zero in Hi.
      cbn in Hi,Hj.
      rewrite <- Hi; rewrite <- Hj ; clear Hi Hj.

      (* We separate the registers into two sets of registers:
         - the registers for i
         - the registers for j
       *)
      rewrite /with_lib.is_initial_registers in Hreg, Hreg_adv.
      destruct Hreg as (Hreg1_some & Hreg1_valid).
      destruct Hreg_adv as (Hreg2_some & Hreg2_valid).

      set (rmap_i := all_registers_s_core i).
      set (rmap_j := all_registers_s_core j).
      set (Pi:= (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) = i )).
      set (Pj:= (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) = j )).
      set (NPi := (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) ≠ i )).
      set (NPj := (λ v : CoreN * RegName * Word, (¬ Pj v)%type)).
      unfold Reg in reg, reg'.

      replace reg with
        (filter Pi reg ∪
           filter NPi reg)
        by apply map_filter_union_complement.
      assert (dom ( filter Pi reg ) = rmap_i).
      { subst rmap_i.
        erewrite <- dom_filter_L.
        reflexivity.
        intros.
        split; intros.
        { destruct i0.
          rewrite /all_registers_s_core in H0.
          apply elem_of_map_1 in H0.
          destruct H0 as (? & ? & ?). inversion H0 ; subst.
          destruct (decide (x = PC)) as [->|Hx] ; subst.
          - eexists ; split.
            eassumption.
            cbn ; auto.
          - destruct (Hreg1_valid x) as (? & ? & _); eauto.
            { clear -Hx. set_solver. }
        }
        { destruct H0 as (w & Hfilter & core_i0).
          destruct i0.
          cbn in core_i0. subst c.
          rewrite /all_registers_s_core.
          apply elem_of_map_2.
          apply all_registers_s_correct.
        }
      }
      set (regs_ni := filter NPi reg).
      replace regs_ni with
        (filter Pj regs_ni ∪
           filter NPj regs_ni)
      by (by rewrite map_filter_union_complement).
      assert (dom ( filter Pj regs_ni ) = rmap_j).
      { subst rmap_j.
        subst regs_ni.
        erewrite <- dom_filter_L.
        reflexivity.
        intros.
        split; intros.
        { destruct i0.
          rewrite /all_registers_s_core in H1.
          apply elem_of_map_1 in H1.
          destruct H1 as (? & ? & ?). inversion H1 ; subst.
          destruct (decide (x = PC)) as [->|Hx] ; subst.
          - eexists ; split.
            apply map_filter_lookup_Some_2.
            eassumption.
            subst NPi ; cbn ; auto.
            cbn ; auto.
          - destruct (Hreg2_valid x) as (? & ? & _); eauto.
            { clear -Hx. set_solver. }
            eexists ; split.
            apply map_filter_lookup_Some_2.
            eassumption.
            subst NPi ; cbn ; auto.
            cbn ; auto.
        }
        { destruct H1 as (w & Hfilter & core_i0).
          destruct i0.
          cbn in core_i0. subst c.
          rewrite /all_registers_s_core.
          apply elem_of_map_2.
          apply all_registers_s_correct.
        }
      }

      iDestruct (big_sepM_union with "Hreg") as "[Hreg_i Hreg]".
      {
        cbn.

        rewrite (map_filter_comm Pj NPi).
        rewrite (map_filter_comm NPj NPi).

        replace ( filter NPi (filter Pj reg) ∪ filter NPi (filter NPj reg) )
          with (filter NPi ((filter Pj reg) ∪ (filter NPj reg))).
        2: { eapply map_filter_union.
             apply map_disjoint_filter_complement. }
        replace (filter Pj reg ∪ filter NPj reg)
          with reg by (by rewrite map_filter_union_complement).
        apply map_disjoint_filter_complement.
      }
      iDestruct (big_sepM_union with "Hreg") as "[Hreg_j Hreg]".
      { apply map_disjoint_filter_complement. }
      iClear "Hreg".

      (* For each core, we prove the WP, using the specification previously
         defined *)
      iSplitL "Hmem_alloc Hreg_i".
      - (* We extracts the needed registers for the full_run_spec *)
      iDestruct (big_sepM_delete _ _ (i, PC) with "Hreg_i") as "[HPC_i Hreg_i]".
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.

      (* Apply the specification *)
      iApply (@alloc_correct _ CP _ _ _ _ _ _ _ (delete (i, PC) (filter Pi reg))
               with
               "[$HPC_i Hreg_i Hmem_alloc $Hinv_malloc $Hinv_flag $Hinv_assert]").
      { (* instantiate (1 := delete (i, PC) (filter Pi reg)). *)
        rewrite dom_delete_L.
        rewrite (regmap_full_dom_i _ i).
        reflexivity.
        intros. split.
        (* admit. *)
        destruct (decide (x = PC)) as [->|Hx] ; subst.
        - eexists; apply map_filter_lookup_Some_2 ; eauto.
          by subst Pi ; cbn.
        - feed pose proof (Hreg1_valid x) as HH.
        { apply not_elem_of_singleton_2. clear -Hx ; simplify_pair_eq. }
        destruct HH as (?&?&_).
        eexists; apply map_filter_lookup_Some_2 ; eauto.
        by subst Pi ; cbn.
        - intros.
          apply map_filter_lookup_None; right.
          intros ; subst Pi ; cbn; congruence.
      }
      iSplitL "Hreg_i".
      { iApply (big_sepM_mono with "Hreg_i"). intros r w Hr. cbn.
        apply lookup_delete_Some in Hr as [Hr_PC Hr].
        assert (Hr' := Hr).
        apply (map_filter_lookup_Some_1_2
                 (λ v : CoreN * RegName * Word, Pi v) reg r w) in Hr.
        subst Pi ; cbn in Hr.
        destruct r as [? r] ; inversion Hr ; subst.
        feed pose proof (Hreg1_valid r) as HH. clear -Hr_PC ; set_solver.
        destruct HH as [? (Hr_reg & Hcap)].
        iIntros ; iFrame ; iPureIntro.
        clear -Hr_reg Hr' Hcap.
        cbn in *.
        apply (map_filter_lookup_Some _ reg) in Hr'.
        destruct Hr' as [? _].
        simplify_map_eq. auto.
      }
      { rewrite /prog_tbl_region /tbl_region /=.
        iDestruct (big_sepM_union with "Hmem_alloc") as "[Halloc Htable]".
        { clear.
          pose proof regions_disjoint as Hdisjoint.
          rewrite !disjoint_list_cons in Hdisjoint |- *.
          disjoint_map_to_list. set_solver. }
        iFrame.
        rewrite /prog_lower_bound_region /prog_region.
        assert ( forall {A} (x:A) (y : list A) , x::y  = [x]++y) by auto.
        rewrite (H2 _ (WCap RO (tbl_start alloc_table) (tbl_end alloc_table)
                                (tbl_start alloc_table)) (prog_instrs alloc_prog)).
        rewrite mkregion_app /=.
        2: {
        pose proof f_region_start_offset; pose proof f_size; solve_addr.
        }
        iDestruct (big_sepM_union with "Halloc") as "[Hf_start Hmem]".
        { apply mkregion_disjoints ; solve_addr. }
        pose proof f_region_start_offset.
        replace (f_region_start ^+ 1%nat)%a with f_start by solve_addr.
        iFrame.
        iDestruct (mkregion_sepM_to_sepL2 with "Hf_start") as "Hfstart"
        ; first solve_addr.
        rewrite finz_seq_between_singleton.
        iDestruct "Hfstart" as "[? _]" ; iFrame.
        solve_addr.
      }

      (* The adversary code safely and completely executes *)
      - iSplitL ; [|done].
        iDestruct (big_sepM_delete _ _ (j, PC) with "Hreg_j") as "[HPC_j Hreg_j]".
        apply map_filter_lookup_Some_2.
        { subst regs_ni Pj Pi ; cbn.
          apply map_filter_lookup_Some_2 ; [eauto| cbn ; by apply not_eq_sym].
        }
        by subst Pj ; cbn.
        rewrite /prog_tbl_region.
        iApply (@adv_correct Σ CP memg regg _ _ _ j _
                 with
                 "[$HPC_j Hreg_j Hmem_adv $Hinv_malloc]").
        { eauto. }
        { instantiate (1 := delete (j, PC) (filter Pj regs_ni)).
          rewrite !dom_delete_L.
          set (X := all_registers_s_core j).
          rewrite /all_registers_s_core.
          unfold all_registers_s_core in X.
          replace ( dom (filter Pj regs_ni)) with X by set_solver.
          set_solver. }
        iSplitL "Hreg_j".
        { iApply (big_sepM_mono with "Hreg_j"). intros r w Hr. cbn.
          apply lookup_delete_Some in Hr as [Hr_PC Hr].
          assert (Hr' := Hr).
          apply (map_filter_lookup_Some_1_2 Pj regs_ni r w) in Hr.
          apply (map_filter_lookup_Some_1_1 _ regs_ni) in Hr'.
          subst.
          apply (map_filter_lookup_Some_1_1 _ reg) in Hr'.
          subst Pj ; cbn in Hr.

          destruct r as [? r] ; inversion Hr ; subst.
          feed pose proof (Hreg2_valid r) as HH. clear -Hr_PC ; set_solver.
          destruct HH as [? (Hr_reg & Hcap)].
          clear -Hr_reg Hr' Hcap.
          iIntros ; iFrame ; iPureIntro.
          cbn in *.
          simplify_map_eq. auto.
        }
        { rewrite /prog_tbl_region /tbl_region /=.
          iDestruct (big_sepM_union with "Hmem_adv") as "[Hadv Htable]".
        { clear.
          pose proof regions_disjoint as Hdisjoint.
          rewrite !disjoint_list_cons in Hdisjoint |- *.
          disjoint_map_to_list. set_solver. }
          iFrame.
          rewrite /prog_lower_bound_region.
          rewrite /prog_lower_bound_region /prog_region.
          assert ( forall {A} (x:A) (y : list A) , x::y  = [x]++y) by auto.
          rewrite (H2 _ (WCap RO (tbl_start adv_table) (tbl_end adv_table)
                           (tbl_start adv_table))
                     (prog_instrs adv_prog)).
          rewrite mkregion_app /=.
          2: {
            pose proof adv_region_start_offset; pose proof adv_size; solve_addr.
          }
          iDestruct (big_sepM_union with "Hadv") as "[Hs Hmem]".
          { apply mkregion_disjoints ; solve_addr. }
          pose proof adv_region_start_offset.
          replace (adv_region_start ^+ 1%nat)%a with adv_start by solve_addr.
          iFrame.
          iDestruct (mkregion_sepM_to_sepL2 with "Hs") as "Hs"
          ; first solve_addr.
          rewrite finz_seq_between_singleton.
          iDestruct "Hs" as "[? _]" ; iFrame.
          solve_addr.
        }
    }


    (** The invariant holds on the resulting memory *)
    iModIntro.
    iIntros (es' t2) "%Hes %Hlength_es %Hstuck [Hreg' Hmem'] Hopt _".

    iInv "Hinv_flag" as ">Hflag" "_".
    iDestruct (gen_heap_valid m' with "Hmem' Hflag") as "#%flag".
    iApply fupd_mask_intro_discard ; [set_solver|iPureIntro].
    intros.
    clear - flag H0. by simplify_map_eq.
    Unshelve.
    all: try typeclasses eauto.
Qed.
End adequacy.
