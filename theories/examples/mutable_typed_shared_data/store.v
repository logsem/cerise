From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.
From cap_machine.examples.mutable_typed_shared_data Require Import dynamic_checks invariants.

Section store_int.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Definition store_global_macro_int_instrs :=
    dyn_typecheck_int_instrs r_t3 r_t4 r_t5 ++ encodeInstrsW [
      UnSeal r_t4 r_t1 r_t2;
      Store r_t4 r_t3
    ].

  (* Instructions to store a word `r_t2` in the seal `r_t1`, sealed by the hidden `WSealRange` *)
  (* This function will succeed only if the word in `r_t2` is an integer. *)
  (* > Otherwise, the machine will enter in a `Failed` state. *)
  (* This will return a new sealed value in `r_t1` and override the registers r_t2`, `r_t3`, `r_t4` and `r_t5`. *)
  Definition store_global_macro_int_closure_instrs (τ : OType) :=
    [ WSealRange (true, true) τ (τ ^+ 1)%ot τ ] ++ encodeInstrsW [
      Mov r_t3 r_t2;
      Mov r_t2 r_t1;
      Mov r_t1 PC;
      Lea r_t1 (-3)%Z;
      Load r_t1 r_t1
    ] ++ store_global_macro_int_instrs ++ encodeInstrsW [
      Mov r_t1 r_t2;
      Mov r_t2 0;
      Mov r_t3 0;
      Mov r_t4 0;
      Mov r_t5 0;
      Jmp r_t0
    ].


  Lemma store_global_macro_int_spec
    p_pc b_pc e_pc a_pc     (* PC *)
    a_cap                   (* Value capability *)
    p_seal b_seal e_seal τ  (* Seal capability *)
    v w4 w5                 (* Values in registers *)
    φ:

    let instrs := store_global_macro_int_instrs in
    let length := (length instrs) in

    ExecPCPerm p_pc →
    SubBounds b_pc e_pc a_pc (a_pc ^+ length)%a →

    permit_unseal p_seal = true →
    withinBounds b_seal e_seal τ = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →

    PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ codefrag a_pc instrs

      ∗ r_t1 ↦ᵣ WSealRange p_seal b_seal e_seal τ
      ∗ r_t2 ↦ᵣ WSealed τ (SCap RW a_cap (a_cap ^+ 1)%a a_cap)
      ∗ (∃ w, a_cap ↦ₐ w ∗ ⌜is_z w⌝)

      ∗ r_t3 ↦ᵣ v
      ∗ r_t4 ↦ᵣ w4
      ∗ r_t5 ↦ᵣ w5

      ∗ ▷ (PC ↦ᵣ WCap p_pc b_pc e_pc (a_pc ^+ length)%a
             ∗ codefrag a_pc instrs

             ∗ r_t1 ↦ᵣ WSealRange p_seal b_seal e_seal τ
             ∗ r_t2 ↦ᵣ WSealed τ (SCap RW a_cap (a_cap ^+ 1)%a a_cap)
             ∗ r_t3 ↦ᵣ v
             ∗ (∃ w, r_t4 ↦ᵣ w)
             ∗ (∃ w, r_t5 ↦ᵣ w)

             ∗ a_cap ↦ₐ v
             ∗ ⌜is_z v⌝

             -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (? ? Hexec ? ? ? ?)
      "(HPC & Hprog & Hr_t1 & Hr_t2 & Haddr & Hr_t3 & Hr_t4 & Hr_t5 & Hφ)".
    subst instrs length; simpl in *.
    iDestruct "Haddr" as (w) "[Ha_cap %]".

    focus_block_0 "Hprog" as "Hblock" "Hcont".

    iApply dyn_typecheck_int_spec; iFrameAutoSolve.
    iIntros "!> (HPC & Hblock & Hr_t3 & %Hvalue & Hr_t4 & Hr_t5)".
    iDestruct "Hr_t4" as (w4') "Hr_t4".
    iDestruct "Hr_t5" as (w5') "Hr_t5".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 1%nat "Hprog" as a_block Ha_block "Hblock" "Hcont".
    iGo "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hprog".

    iApply "Hφ".
    replace (a_block ^+ 2)%a with (a_pc ^+ 8)%a by solve_addr.
    iFrame.
    iSplitL "Hr_t4"; eauto.
  Qed.

  Lemma store_global_macro_int_closure_spec
    p_pc b_pc       (* PC *)
    a_cap           (* Value capability *)
    p_seal τ        (* Seal capability *)
    adv v w3 w4 w5  (* Values in registers *)
    φ:

    let instrs := store_global_macro_int_closure_instrs τ in
    let e_pc := (b_pc ^+ length instrs)%a in

    ExecPCPerm p_pc →
    ContiguousRegion b_pc (length instrs) →
    SubBounds b_pc e_pc (b_pc ^+ 1)%a (b_pc ^+ (length instrs))%a →

    permit_unseal p_seal = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →
    withinBounds τ (τ ^+ 1)%ot τ = true →

    PC ↦ᵣ WCap p_pc b_pc e_pc (b_pc ^+ 1)%a
      ∗ region_mapsto b_pc e_pc instrs

      ∗ r_t0 ↦ᵣ adv
      ∗ r_t1 ↦ᵣ WSealed τ (SCap RW a_cap (a_cap ^+ 1)%a a_cap)
      ∗ (∃ w, a_cap ↦ₐ w ∗ ⌜is_z w⌝)

      ∗ r_t2 ↦ᵣ v
      ∗ r_t3 ↦ᵣ w3
      ∗ r_t4 ↦ᵣ w4
      ∗ r_t5 ↦ᵣ w5

      ∗ ▷ (PC ↦ᵣ updatePcPerm adv
             ∗ region_mapsto b_pc e_pc instrs

             ∗ r_t0 ↦ᵣ adv
             ∗ r_t1 ↦ᵣ WSealed τ (SCap RW a_cap (a_cap ^+ 1)%a a_cap)
             ∗ (∃ w, a_cap ↦ₐ w ∗ ⌜is_z w⌝)

             ∗ r_t2 ↦ᵣ WInt 0
             ∗ r_t3 ↦ᵣ WInt 0
             ∗ r_t4 ↦ᵣ WInt 0
             ∗ r_t5 ↦ᵣ WInt 0

             -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (? ? ? Hbounds ? ? ? ?)
      "(HPC & Hprog & Hr_t0 & Hr_t1 & Haddr & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hφ)".

    iDestruct (region_mapsto_split b_pc e_pc (b_pc ^+ 1)%a _ _ with "Hprog") as "(Hseal & Hprog)"
      ; [ subst e_pc; solve_addr + | rewrite /finz.dist; solve_finz +Hbounds |].

    iDestruct (region_mapsto_single with "Hseal") as (seal) "(Hseal & %w)"
      ; [ solve_addr +Hbounds | case: w => <- ].

    match goal with
      |- context [ ([[ (b_pc ^+ 1)%a, _ ]] ↦ₐ [[ ?instrs ]])%I ] => set instrs' := instrs
    end.

    iAssert (codefrag (b_pc ^+ 1)%a instrs') with "[Hprog]" as "Hprog".
    { replace e_pc with ((b_pc ^+ 1) ^+ (length instrs'))%a
        ; [ iFrame | subst e_pc; solve_addr ]. }

    clear Hbounds.

    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hblock" "Hcont".

    iGo "Hblock".
    { transitivity (Some b_pc); [ solve_addr +H6 | eauto ]. }

    iInstr "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 1%nat "Hprog" as addr_block1 Haddr_block1 "Hblock" "Hcont".

    iApply (store_global_macro_int_spec with "[-]"); last iFrame; eauto.

    iIntros "!> (HPC & Hblock & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Haddr)".
    iDestruct "Hr_t4" as (w4') "Hr_t4".
    iDestruct "Hr_t5" as (w5') "Hr_t5".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 2%nat "Hprog" as addr_block2 Haddr_block2 "Hblock" "Hcont".

    iGo "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    iApply "Hφ"; iFrame.

    iAssert (codefrag b_pc _)%I with "[Hseal]" as "Hseal".
    { iDestruct (region_mapsto_cons with "[Hseal]") as "Hseal"; [| | iFrame | done ].
      { transitivity (Some (b_pc ^+ 1))%a; [ solve_addr +H4 | reflexivity ]. }
      { solve_addr +. }

      rewrite /region_mapsto finz_seq_between_empty; [ done | solve_addr + ]. }

    unfold codefrag; simpl.

    iDestruct (region_mapsto_split with "[$Hseal $Hprog]") as "Hprog";
      [ solve_addr + | rewrite /finz.dist; solve_finz |].

    replace ((b_pc ^+ 1) ^+ 19%nat)%a with (b_pc ^+ 20)%a by solve_addr.
    iFrame.
    iExists v; iFrame.
  Qed.

  Lemma store_global_macro_int_closure_spec_full
    p_pc b_pc  (* PC *)
    a_cap      (* Value capability *)
    p_seal τ   (* Seal capability *)
    adv v w3   (* Values in registers *)
    rmap:

    let instrs := store_global_macro_int_closure_instrs τ in
    let length := length instrs in
    let e_pc := (b_pc ^+ length)%a in

    ExecPCPerm p_pc →
    ContiguousRegion b_pc length →
    SubBounds b_pc e_pc b_pc (b_pc ^+ length)%a →

    permit_unseal p_seal = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →
    withinBounds τ (τ ^+ 1)%ot τ = true →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2; r_t3 ]} →

    ⊢ (PC ↦ᵣ WCap p_pc b_pc e_pc (b_pc ^+ 1)%a
      ∗ region_mapsto b_pc e_pc instrs

      ∗ r_t0 ↦ᵣ adv
      ∗ r_t1 ↦ᵣ WSealed τ (SCap RW a_cap (a_cap ^+ 1)%a a_cap)
      ∗ (∃ w, a_cap ↦ₐ w ∗ ⌜is_z w⌝)

      ∗ r_t2 ↦ᵣ v
      ∗ r_t3 ↦ᵣ w3

      ∗ seal_state sealN a_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i ∗ ⌜is_z w_i = true⌝)
      ∗ interp adv

      -∗ WP Seq (Instr Executable)
            {{ v,
                (⌜v = HaltedV⌝ → (∃ r: Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤))
                  ∨ ⌜ v = FailedV ⌝ }})%I.
  Proof.
    iIntros (? ? ? ? Hbounds ? ? ? ? Hdom)
      "(HPC & Hprog & Hr_t0 & Hr_t1 & Haddr & Hr_t2 & Hr_t3 & Hseal & Hna & Hrmap & #Hadv_interp)".

    iDestruct (jmp_to_unknown with "Hadv_interp") as "Cont".

    iExtractList "Hrmap" [r_t4; r_t5] as ["[Hr_t4 _]"; "[Hr_t5 _]"].

    iApply (store_global_macro_int_closure_spec with "[-]")
      ; last iFrame; eauto; [ solve_addr + |].

    iIntros "!> (HPC & Hprog & Hr_t0 & Hr_t1 & Haddr & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5)".

    iApply (wp_wand with "[-]"); [| iIntros (?) "?"; by iLeft ].

    iDestruct "Haddr" as (w') "Haddr".
    iMod (isIntSealed_alloc a_cap w' with "Haddr") as "Haddr".

    iApply "Cont"; eauto; iFrame; revgoals.
    { iAssert (⌜is_z (WInt 0) = true⌝)%I as "H"; [ done |].
      iCombine "Hr_t2 H" as "Hr_t2".
      iCombine "Hr_t3 H" as "Hr_t3".
      iCombine "Hr_t4 H" as "Hr_t4".
      iCombine "Hr_t5 H" as "Hr_t5".
      iInsertList "Hrmap" [r_t5; r_t4; r_t3; r_t2].

      iDestruct (big_sepM_mono _ (λ r w, r ↦ᵣ w ∗ interp w)%I with "[Hrmap]") as "Hrmap"; [| iFrame |].
      { iIntros (r w Hrmap) "(Hr & %Hr_int)".
        iFrame.
        destruct w; [| discriminate.. ].
        by rewrite fixpoint_interp1_eq. }

      iAssert (interp (WSealed τ (SCap RW a_cap (a_cap ^+ 1)%a a_cap)))%I as "#Hseal_interp".
      { iApply fixpoint_interp1_eq.
        iExists isIntSealed.
        repeat iSplit.
        - iPureIntro.
          apply isIntSealed_persistent.
        - iDestruct "Hseal" as "(_ & Hpred)".
          iFrame.
        - by iExists w'. }

      iCombine "Hr_t1 Hseal_interp" as "Hr_t1".
      iCombine "Hr_t0 Hadv_interp" as "Hr_t0".
      iInsertList "Hrmap" [r_t1; r_t0].

      iFrame. }

    iPureIntro.
    rewrite !dom_insert_L Hdom.
    rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
    set_solver +.
  Qed.

End store_int.
