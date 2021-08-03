From iris.algebra Require Import agree auth gmap.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous fundamental.
From cap_machine Require Import dynamic_sealing interval list_new malloc.
From cap_machine Require Import solve_pure proofmode map_simpl.

Section interval_closure.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Definition interval f_m :=
    (makeint f_m) ++ imin ++ imax.

  Definition r_temp1 := r_t21.
  Definition r_temp2 := r_t22.
  Definition r_temp3 := r_t23.
  Definition r_temp4 := r_t24.
  Definition r_temp5 := r_t25.
  Definition r_temp6 := r_t26.


  Definition interval_closure f_m f_s offset_to_interval :=
    (* allocate the environment of the interval library *)
    malloc_instrs f_m 2%nat ++
    encodeInstrsW [ Mov r_temp1 r_t1 ] ++
    (* jump to the makeseal subroutine *)
    fetch_instrs f_s ++
    encodeInstrsW [ Mov r_temp6 r_t0;
                  Mov r_t0 PC;
                  Lea r_t0 3;
                  Jmp r_t1;
                  (* store entry points into interval library *)
                  Store r_temp1 r_t1;
                  Lea r_temp1 1;
                  Store r_temp1 r_t2;
                  Lea r_temp1 (-1)%Z;
                  (* prepare to create a closure around makeint *)
                  Mov r_t2 r_temp1;
                  Mov r_t1 PC;
                  Lea r_t1 offset_to_interval;
                  Mov r_temp2 r_t1] ++
    (* create closure around makeint and the seal environment *)
    crtcls_instrs f_m ++
    (* we will need to store the result somewhere safe *)
    encodeInstrsW [ Mov r_temp3 r_t1;
                  (* prepare to create a closure around imin *)
                  Mov r_t2 r_temp1;
                  Mov r_t1 r_temp2;
                  Lea r_t1 (strings.length (makeint f_m));
                  Mov r_temp2 r_t1] ++
    (* create closure around imin and the seal environment *)
    crtcls_instrs f_m ++
    (* we will need to store the result somewhere safe *)
    encodeInstrsW [ Mov r_temp4 r_t1;
                  (* prepare to create a closure around imax *)
                  Mov r_t2 r_temp1;
                  Mov r_t1 r_temp2;
                  Lea r_t1 (strings.length imin)] ++
    (* create closure around imin and the seal environment *)
    crtcls_instrs f_m ++
    encodeInstrsW [ Jmp r_temp6 ].

  Definition intN : namespace := nroot .@ "intervalN".
  Definition sealN : namespace := intN .@ "sealN".
  Definition sealLLN : namespace := intN .@ "sealLLN".

  Lemma interval_closure_functional_spec f_m f_s offset_to_interval offset_to_move
        a_first i_first s_first a_move
        pc_p pc_b pc_e
        s_p s_b s_e
        b_r e_r a_r malloc_r makeseal_r
        b_rs e_rs
        b_m e_m mallocN
        wret rmap Ψ Φ :

    (* PC assumptions *)
    ExecPCPerm pc_p →
    ExecPCPerm s_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (makeint f_m))%a →
    SubBounds pc_b pc_e i_first (i_first ^+ length (interval f_m))%a →
    SubBounds s_b s_e s_first (s_first ^+ length unseal_instrs
                                       ^+ length (seal_instrs 0)
                                       ^+ length (make_seal_preamble_instrs 0))%a →

    (* environment table: contains the makeseal entry, and malloc *)
    withinBounds b_r e_r malloc_r = true →
    withinBounds b_r e_r makeseal_r = true →
    (a_r + f_m)%a = Some malloc_r →
    (a_r + f_s)%a = Some makeseal_r →
    (b_rs + 1)%a = Some e_rs →

    (* offset between preamble and interval library *)
    (a_first + offset_to_move)%a = Some a_move →
    (a_move + offset_to_interval)%a = Some i_first →

    (* registers *)
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0]} →

    (* Code of the preamble *)
    codefrag a_first (interval_closure f_m f_s offset_to_interval)

    (* Code of the interval code *)
    ∗ codefrag i_first (interval f_m)

    (* Code and environment table of the seal library *)
    ∗ codefrag s_first (unseal_instrs ++ seal_instrs 0 ++ make_seal_preamble_instrs 0)
    ∗ s_b ↦ₐ WCap RO b_rs e_rs b_rs ∗ b_rs ↦ₐ WCap E b_m e_m b_m

    (* Environment table for interval library *)
    ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
    ∗ malloc_r ↦ₐ WCap E b_m e_m b_m
    ∗ makeseal_r ↦ₐ WCap E s_b s_e (s_first ^+ length unseal_instrs ^+ length (seal_instrs 0))%a
    (* Malloc invariant *)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)

    (* registers *)
    ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ r_t0 ↦ᵣ wret
    ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)

    (* NA inv token *)
    ∗ na_own logrel_nais ⊤

    (* continuation *)
    ∗ Ψ FailedV
    ∗ (∀ v, Ψ v -∗ Φ v)
    ∗ ▷ (PC ↦ᵣ updatePcPerm wret -∗ WP Seq (Instr Executable) {{ Ψ }} )


      ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hpc_p Hs_p Hbounds_preamble Hbounds_interval Hbounds_seal Hwb_mallocr Hwb_makesealr
                   Hlink_mallocr Hlink_makesealr Hsealtable Ha_move Hi_first Hdom).
    iIntros "(Hcode & Hinterval & Hseal & Hs_b & Hb_rs & Hpc_b & Hmalloc_r & Hmakeseal_r & #Hmalloc
              & HPC & Hr_t0 & Hregs & Hown & Hfailed & HΨ & HΦ)".

    rewrite /interval_closure.

    focus_block 0 "Hcode" as a_mid Ha_mid "Hblock" "Hcont".

    (* malloc *)
    iApply (wp_wand _ _ _ (λ v, (Ψ v ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)%I with "[- Hfailed HΨ]"); cycle 1.
    { iIntros (v) "[ [H1 | H1] | H1]";iApply "HΨ";iFrame; iSimplifyEq; iFrame. }
    iApply malloc_spec;iFrameCapSolve;[..|iFrame "Hmalloc Hown Hregs"];[auto|auto|clear;lia|..].
    iNext. iIntros "(HPC & Hblock & Hpc_b & Hmalloc_r & Henv & Hr_t0 & Hown & Hregs)".
    iDestruct "Henv" as (benv0 eenv Henvsize) "(Hr_t1 & Hbeenv)".

    (* malloc region cleanup *)
    assert (is_Some (benv0 + 1)%a) as [benv1 Henvincr];[solve_addr+Henvsize|].
    rewrite /region_addrs_zeroes /region_size.
    assert (Z.to_nat (eenv - benv0) = 2) as ->;[solve_addr+Henvsize|]. iSimpl in "Hbeenv".
    iDestruct (region_mapsto_cons with "Hbeenv") as "[Hbenv0 Hbeenv]";
      [eauto|solve_addr+Henvincr Henvsize|..].
    rewrite /region_mapsto region_addrs_single;[|solve_addr+Henvsize Henvincr].
    iDestruct "Hbeenv" as "[Hbenv1 _]".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    (* get some general purpose registers *)
    assert (is_Some (rmap !! r_temp1)) as [w Hr_temp1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete _ _ r_temp1 with "Hregs") as "[Hr_temp1 Hregs]".
    { rewrite !lookup_insert_ne// lookup_delete_ne//. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[by simplify_map_eq|].

    (* Mov r_temp1 r_t1 *)
    focus_block 1 "Hcode" as a_mid0 Ha_mid0 "Hblock" "Hcont".
    iInstr "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    (* fetch the makeseal capability *)
    focus_block 2 "Hcode" as a_mid1 Ha_mid1 "Hblock" "Hcont".
    iApply fetch_spec;iFrameCapSolve.
    iNext. iIntros "(HPC & Hblock & Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Hmakeseal_r)".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    (* prepare to jump to makeseal *)
    assert (is_Some (rmap !! r_temp6)) as [w0 Hr_temp6];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete _ _ r_temp6 with "Hregs") as "[Hr_temp6 Hregs]".
    { rewrite !lookup_delete_ne// !lookup_insert_ne// lookup_delete_ne//. }
    focus_block 3 "Hcode" as a_mid2 Ha_mid2 "Hblock" "Hcont".
    iGo "Hblock".

    (* reconstruct registers *)
    iDestruct (big_sepM_insert _ _ r_temp1 with "[$Hregs $Hr_temp1]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp6 with "[$Hregs $Hr_temp6]") as "Hregs"; [by simplify_map_eq|].

    repeat (rewrite -(delete_insert_ne _ r_t1)//); rewrite !(delete_commute _ _ r_t1)//;
    rewrite -(delete_insert_ne _ r_t1)// -(delete_insert_ne _ r_t1)// -(delete_insert_ne _ r_t1)//.
    rewrite insert_delete.

    repeat (rewrite -(delete_insert_ne _ r_t2)//); rewrite !(delete_commute _ _ r_t2)//.
    rewrite -(delete_insert_ne _ r_t2)//. rewrite insert_delete.

    do 4 (rewrite -(delete_insert_ne _ r_temp6)//). rewrite insert_delete.

    rewrite (delete_commute _ _ r_temp1)//. rewrite insert_delete.

    rewrite (insert_commute _ r_t2 r_t3)//. rewrite delete_insert_delete.
    do 2 (rewrite -(delete_insert_ne _ r_t3)//). rewrite insert_delete.

    rewrite (insert_commute _ r_temp1 r_t2)//. rewrite insert_insert.

    iApply make_seal_spec;iFrameCapSolve;[..|iFrame "Hmalloc Hb_rs Hown Hregs"].
    { rewrite !dom_insert_L. rewrite Hdom. set_solver+. }
    { solve_addr+Hsealtable. }
    { solve_addr+Hsealtable. }
    { solve_ndisj. }
    iNext. iIntros "(HPC & Hr_t0 & Hs_b & Hb_rs & Hseal_res & Hregs & Hseal & Hown)".
    iDestruct "Hseal_res" as (b1 e1 b2 e2 ll ll')
                               "(Hr_t1 & Hr_t2 & %He1 & %He2 & Hact1 & Hact2 & %Hll & HsealLL)".
    iDestruct "HsealLL" as (γ) "#HsealLL".

    (* get some registers *)
    rewrite !(insert_commute _ _ r_temp1)// !(delete_insert_ne _ _ r_temp1)//
            !(insert_commute _ _ r_temp1)//.
    assert (is_Some (rmap !! r_temp2)) as [w1 Hr_temp2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete _ _ r_temp2 with "Hregs") as "[Hr_temp2 Hregs]".
    { rewrite !lookup_insert_ne// !lookup_delete_ne// !lookup_insert_ne//. }
    rewrite delete_insert_ne//.
    iDestruct (big_sepM_delete _ _ r_temp1 with "Hregs") as "[Hr_temp1 Hregs]";[by simplify_map_eq|].
    rewrite delete_insert_delete.

    rewrite updatePcPerm_cap_non_E;[|inv Hpc_p;auto].
    iGo "Hblock". solve_addr+Henvsize Henvincr.
    iGo "Hblock". solve_addr+Henvsize Henvincr.
    iGo "Hblock". assert (benv1 + -1 = Some benv0)%a;[solve_addr+Henvsize Henvincr|]. eauto.
    
    (* We can now allocate the seal environment invariant *)
    iMod (na_inv_alloc _ _ sealN (seal_env benv0 benv1 ll ll' RX s_b s_e s_first b_m e_m b_rs e_rs)
            with "[Hact1 Hact2 Hb_rs Hs_b Hbenv0 Hbenv1 Hseal]") as "#?".
    { iNext. iFrame. iExists _,_,_,_,_. iFrame. repeat iSplit;eauto. }



End interval_closure.
