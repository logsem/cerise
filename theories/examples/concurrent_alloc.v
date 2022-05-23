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
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
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

    dom (gset (CoreN *RegName)) rmap =
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
    iDestruct (big_sepM_delete _ _ (i, r_t4) with "Hrmap") as "[Hr4 Hrmap]"
    ; first by simpl_map.

    assert (is_Some (rmap !! (i,r_t5))) as [w5 Hw5] by (rewrite elem_of_gmap_dom Hdom; set_solver+).
    iDestruct (big_sepM_delete _ _ (i, r_t5) with "Hrmap") as "[Hr5 Hrmap]"
    ; first by simpl_map.

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
    iDestruct (big_sepM_delete _ _ (i, r_t2) with "Hrmap") as "[Hr2 Hrmap]"
    ; first by simpl_map.

    assert (is_Some (rmap !! (i,r_t3))) as [w3 Hw3] by (rewrite elem_of_gmap_dom Hdom; set_solver+).
    iDestruct (big_sepM_delete _ _ (i, r_t3) with "Hrmap") as "[Hr3 Hrmap]"
    ; first by simpl_map.

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
