From iris.algebra Require Import agree auth gmap.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous fundamental.
From cap_machine Require Import arch_sealing interval_arch malloc interval_closure_arch.
From cap_machine Require Import solve_pure proofmode map_simpl register_tactics.

Section interval_client.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* r_t1 : interval input *)
  (* r_env : capability containing the three entry points: makeint, imin, imax *)
  (* pc_b : environment table containing the assert subroutine *)
  Definition check_interval f_a :=
    encodeInstrsW [ Mov r_temp1 r_t1;
                  Mov r_temp2 r_env;
                  Mov r_temp3 r_t0;
                  (* load imin subroutine *)
                  Lea r_env 1;
                  Load r_t2 r_env;
                  (* jmp to imin *)
                  Mov r_t0 PC;
                  Lea r_t0 3;
                  Jmp r_t2;
                  (* copy the result *)
                  Mov r_temp4 r_t1;
                  (* load imax subroutine *)
                  Lea r_temp2 2;
                  Load r_t2 r_temp2;
                  (* jmp to imax *)
                  Mov r_t1 r_temp1;
                  Mov r_t0 PC;
                  Lea r_t0 3;
                  Jmp r_t2;
                  (* compare the two results *)
                  Lt r_t4 r_t1 r_temp4; (* if r_t1 is 1 then z2 < z1, and the assert should fail *)
                  Mov r_t5 0]
                  ++ assert_instrs f_a ++ (* assert (r_t4 = r_t5) *)
                  (* register cleanup*)
    encodeInstrsW [ Mov r_temp1 0;
                  Mov r_temp2 0;
                  Mov r_t0 r_temp3;
                  Mov r_temp3 0;
                  Mov r_t20 0;
                  Mov r_t1 0;
                  Mov r_t2 0;
                  Jmp r_t0 ].

  (* the interval library environment must contain:
   (1) the activation code for makeint, imax, imin
   (2) a linking table with the assert subroutine *)

  (* the subroutines for makeint imax and imin will be
     in separate invariants. So will the relevant parts of its environment table *)

  Definition interval_env d1 d4 benv0 eenv p b e a f_m b1 e1 b2 e2 b3 e3: iProp Σ :=
    (∃ d2 d3, ⌜(d1 + 1 = Some d2 ∧ d2 + 1 = Some d3 ∧ d3 + 1 = Some d4)%a⌝
          ∗ d1 ↦ₐ WCap E b1 e1 b1
          ∗ d2 ↦ₐ WCap E b2 e2 b2
          ∗ d3 ↦ₐ WCap E b3 e3 b3 ∗
          let wvar := WCap RWX benv0 eenv benv0 in
          let wcode1 := WCap p b e a in
          let wcode2 := WCap p b e (a ^+ length (makeint f_m))%a in
          let wcode3 := WCap p b e (a ^+ length (makeint f_m) ^+ length (imin))%a in
          ⌜(b1 + 8)%a = Some e1 ∧ (b2 + 8)%a = Some e2 ∧ (b3 + 8)%a = Some e3⌝
          ∗ ⌜ExecPCPerm p ∧ SubBounds b e a (a ^+ length (makeint f_m) ^+ length imin
                                               ^+ length imax)%a⌝
          ∗ [[b1,e1]]↦ₐ[[activation_instrs wcode1 wvar]]
          ∗ [[b2,e2]]↦ₐ[[activation_instrs wcode2 wvar]]
          ∗ [[b3,e3]]↦ₐ[[activation_instrs wcode3 wvar]]
    )%I.



  Local Existing Instance interp_weakening.if_persistent.
  Lemma check_interval_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        iw (* input interval. If they are sealed intervals, the program crashes *)
        d1 d4 (* dynamically allocated interval environment *)
        a_first (* special adresses *)
        ι0 ι1 ι2 ι3 ι4 ι5 ι6 o (* invariant/gname names *)
        f_a b_r e_r a_r a_r' b_a e_a a_flag assertN (* assert environment *)
        rmap (* register map *)
        benv0 eenv p_i b_i e_i a_i f_m_i b1 e1 b2 e2 b3 e3 (* interval library *)
        ll ll' p_s b_s e_s a_s Φs(* nested seal environment *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (check_interval f_a))%a →

    (* environment table: required by the seal and malloc spec *)
    withinBounds b_r e_r a_r' = true →
    (a_r + f_a)%a = Some a_r' →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t1; r_t20]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset)ι2 ⊆ ⊤ ∖ ↑ι1) ->
    up_close (B:=coPset)ι0 ## ↑ι3 →
    up_close (B:=coPset)ι6 ## ↑ι0 →
    up_close (B:=coPset)ι6 ## ↑ι3 →
    up_close (B:=coPset)ι0 ## ↑ι5 →
    up_close (B:=coPset)ι6 ## ↑ι5 →
    up_close (B:=coPset)ι4 ⊆ ⊤ ∖ ↑ι1 →
    up_close (B:=coPset)ι1 ## ↑assertN →
    up_close (B:=coPset)ι4 ## ↑assertN →

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_t0 ↦ᵣ wret
       ∗ r_env ↦ᵣ WCap RWX d1 d4 d1
       ∗ r_t1 ↦ᵣ iw
       (* proof that the provided value has been validly sealed *)
       ∗ ▷ (if is_sealed_with_o iw o then valid_sealed iw o Φs else True)
       ∗ (∃ w, r_t20 ↦ᵣ w)
       ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
       (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment,
          and the interval library environment *)
       ∗ na_inv logrel_nais ι0 (seal_env benv0 eenv ll ll' p_s b_s e_s a_s)
       ∗ seal_state ι6 ll o isInterval
       ∗ na_inv logrel_nais ι2 (interval_env d1 d4 benv0 eenv p_i b_i e_i a_i f_m_i b1 e1 b2 e2 b3 e3)
       (* code for imin and imax subroutines *)
       ∗ na_inv logrel_nais ι3 (codefrag (a_i ^+ length (makeint f_m_i))%a imin)
       ∗ na_inv logrel_nais ι5 (codefrag ((a_i ^+ length (makeint f_m_i)) ^+ length imin)%a imax)
       (* token which states all non atomic invariants are closed *)
       ∗ na_own logrel_nais ⊤
       (* callback validity *)
       ∗ interp wret
       (* assert and environment table *)
       ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ WCap RO b_r e_r a_r ∗ a_r' ↦ₐ WCap E b_a e_a b_a)
       ∗ na_inv logrel_nais assertN (assert_inv b_a a_flag e_a)
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (codefrag a_first (check_interval f_a))
       (* the remaining registers are all valid *)
       ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i) }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r, full_map r ∧ registers_mapsto r
                         ∗ na_own logrel_nais ⊤ }}}.
  Proof.
    iIntros (Hvpc Hbounds Hwb Ha_r' Hdom Hι0 Hι1 Hι2 Hι3 Hι4 Hι5 Hι6 ? ? Φ)
            "(HPC & Hr_t0 & Hr_env & Hr_t1 & #Hseal_valid & Hr_t20 & Hregs & #Hseal_env & #HsealLL & #Hinterval_env & #Himin & #Himax &
              Hown & #Hwret_valid & #Htable & #Hassert & #Hcheck_interval & #Hregs_valid) HΦ".
    iMod (na_inv_acc with "Hcheck_interval Hown") as "(>Hcode & Hown & Hcls)";auto.
    iMod (na_inv_acc with "Hinterval_env Hown") as "(>Hint & Hown & Hcls')";[auto..|].
    iDestruct "Hint" as (d2 d3 (Hd2&Hd3&Hd4))
                          "(Hd1 & Hd2 & Hd3 & %Hcond & %Hi_pc & Hact1 & Hact2 & Hact3)".
    destruct Hcond as (He1 & He2 & He3).
    destruct Hi_pc as (Hvpci & Hboundsi).

    iExtractList "Hregs" [r_temp1;r_temp2;r_temp3;r_temp4;r_t2] as ["Hr_temp1";"Hr_temp2";"Hr_temp3";"Hr_temp4";"Hr_t2"].

    rewrite /check_interval.
    focus_block_0 "Hcode" as "Hblock" "Hcont".
    iGo "Hblock". split;auto. solve_addr+Hd2 Hd3 Hd4.
    iGo "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    iDestruct "Hr_t20" as (w5) "Hr_t20".
    iApply closure_activation_spec;iFrameAutoSolve. iFrame "Hact2".
    iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hact2)".

    rewrite updatePcPerm_cap_non_E;[|by inv Hvpci].
    iMod ("Hcls'" with "[$Hown Hact1 Hact2 Hact3 Hd1 Hd2 Hd3]") as "Hown".
    { iNext. iExists _,_. iFrame "Hact1 Hact2 Hact3". iFrame. auto. }
    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".
    iExtractList "Hregs" [r_t3;r_t4;r_t5] as ["Hr_t3";"Hr_t4";"Hr_t5"].
    iApply imin_spec;iFrameAutoSolve;[..|iFrame "HsealLL Hseal_env Himin Hown HΦ"];[|eauto..|].
    solve_addr+Hboundsi.
    iSplitR; [iExact "Hseal_valid"|].
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t5";[eauto|]. iSplitL "Hr_t20";[eauto|].
    iSplitR.
    { iNext. iIntros (Hcontr); inversion Hcontr. }
    iNext. iIntros "Hres".
    iDestruct "Hres" as (z1 z2 w)
                          "(%Heqiw & #His_int & HPC & Hr_t1 & Hr_t2
                          & Hr_t5 & Hr_t20 & Hr_env & Hr_t0 & Hown)".
    subst iw.

    iMod (na_inv_acc with "Hcheck_interval Hown") as "(>Hcode & Hown & Hcls)";auto.
    iMod (na_inv_acc with "Hinterval_env Hown") as "(>Hint & Hown & Hcls')";[auto..|].
    iDestruct "Hint" as (d2' d3' (Hd2'&Hd3'&Hd4'))
                          "(Hd1 & Hd2 & Hd3 & %Hcond & %Hi_pc & Hact1 & Hact2 & Hact3)".
    destruct Hcond as (He1' & He2' & He3').
    destruct Hi_pc as (Hvpci' & Hboundsi').
    simplify_eq.

    focus_block_0 "Hcode" as "Hblock" "Hcont".
    rewrite updatePcPerm_cap_non_E;[|by inv Hvpc].
    iGo "Hblock". instantiate (1:=d3). solve_addr +Hd2 Hd3 Hd4.
    iGo "Hblock". split;auto. solve_addr +Hd2 Hd3 Hd4.
    iGo "Hblock". unfocus_block "Hblock" "Hcont" as "Hcode".

    iApply closure_activation_spec;iFrameAutoSolve. iFrame "Hact3".
    iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hact3)".

    rewrite updatePcPerm_cap_non_E;[|by inv Hvpci].
    iMod ("Hcls'" with "[$Hown Hact1 Hact2 Hact3 Hd1 Hd2 Hd3]") as "Hown".
    { iNext. iExists _,_. iFrame "Hact1 Hact2 Hact3". iFrame. auto. }
    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".

    iApply imax_spec;iFrameAutoSolve;[..|iFrame "HsealLL Hseal_env Himax Hown"];[|eauto..|].
    solve_addr+Hboundsi.
    iSplitR; [iExact "Hseal_valid"|].
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t5";[eauto|]. iSplitL "Hr_t20";[eauto|].

    iSplitR;[|iSplitR].
    2: { iNext. iIntros (v). iIntros "H". iExact "H". }
    iNext. iIntros (Hcontr);inversion Hcontr.

    iNext. iIntros "Hres".
    iDestruct "Hres" as (z0 z3 w')
                          "(%Heq & #His_int' & HPC & Hr_t1 & Hr_t2 & Hr_t5
                           & Hr_t20 & Hr_env & Hr_t0 & Hown)".
    inv Heq.

    (* (* we must now use the sealLL invariant to conclude that w = w' *) *)
    (* iMod (na_inv_acc with "HsealLL Hown") as "(Hseal_inv & Hown & Hcls)";auto. *)
    (* iDestruct "Hseal_inv" as (hd) "(>Hll & Hhd)". *)
    (* iDestruct "Hhd" as (awvals) "(HisList & >Hexact & #Hintervals)". *)
    (* iDestruct (know_pref with "Hexact Hpref") as %Hprefix. *)
    (* iDestruct (know_pref with "Hexact Hpref'") as %Hprefix'. *)
    (* iAssert (▷ ⌜NoDup awvals.*1⌝)%I as "#>%HnoDup". *)
    (* { iNext. iApply isList_NoDup. iFrame. } *)
    (* rewrite Hincr in Hincr'. inv Hincr'. *)
    (* pose proof (elem_of_prefix_eq b01 w w' pbvals pbvals' awvals Hin Hin' Hprefix Hprefix' HnoDup) as <-. *)
    (* iMod ("Hcls" with "[$Hown Hll HisList Hexact]") as "Hown". *)
    (* { iNext. iExists _. iFrame. iExists _. iFrame. auto. } *)
    (* next, we can use isInterval property to conclude that z1 = z0 and z2 = z3 *)
    iDestruct (intervals_agree with "His_int His_int'") as %(Heq & Heq'). subst z0 z3.

    (* we can now finish the program, knowing that z1 <= z2 *)
    iMod (na_inv_acc with "Hcheck_interval Hown") as "(>Hcode & Hown & Hcls)";auto.
    rewrite updatePcPerm_cap_non_E;[|by inv Hvpc].
    focus_block_0 "Hcode" as "Hblock" "Hcont".
    iGo "Hblock". unfocus_block "Hblock" "Hcont" as "Hcode".

    iDestruct "His_int'" as (a1 a2 a3 _) "(_&_&%Hle)".
    assert (z2 <? z1 = false)%Z as ->. lia.

    focus_block 1 "Hcode" as a_mid Ha_mid "Hblock" "Hcont".
    iMod (na_inv_acc with "Htable Hown") as "(>(Hpc_b & Ha_r') & Hown & Hcls')";auto.
    iApply (assert_success with "[- $Hassert $Hown]");iFrameAutoSolve. solve_ndisj. by auto.
    iNext. iIntros "(HPC & Hr_t0 & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hblock & Hown & Hpc_b & Ha_r')".
    iMod ("Hcls'" with "[$Hown $Hpc_b $Ha_r']") as "Hown".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    iDestruct (jmp_to_unknown _ with "Hwret_valid") as "Hcallback_now".

    focus_block 2 "Hcode" as a_mid0 Ha_mid0 "Hblock" "Hcont".
    iGo "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".
    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".
    iInsertList "Hregs" [r_t5;r_t4;r_t3;r_t2;r_temp1;r_temp2;r_temp3;r_temp4;r_t1;r_t0;r_t20;r_env].

    iApply ("Hcallback_now" with "[] [$HPC Hregs $Hown]");cycle 1.
    { iApply big_sepM_sep. iFrame.
      repeat (iApply big_sepM_insert_2; first by iApply fixpoint_interp1_eq).
      iApply big_sepM_insert_2. iFrame "#".
      repeat (iApply big_sepM_insert_2; first by iApply fixpoint_interp1_eq).
      iFrame "#". }
    iPureIntro. rewrite !dom_insert_L Hdom. rewrite !singleton_union_difference_L. set_solver+.
  Qed.

End interval_client.
