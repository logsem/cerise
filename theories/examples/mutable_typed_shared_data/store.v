From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.
From cap_machine.examples.mutable_typed_shared_data Require Import dynamic_checks invariants.

Section store_cap.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (* Instructions to store a word `r_t3` in the seal `r_t2`, sealed by the `WSealRange` in `r_t1`. *)

  (* This function will succeed only if the word in `r_t3` is a capability. *)
  (* > Otherwise, the machine will enter in a `Failed` state. *)

  (* This will override the registers r_t4` and `r_t5`. *)
  (* > Beware: The registers are NOT cleared. *)
  Definition store_global_macro_cap_instrs :=
    dyn_typecheck_cap_instrs r_t3 r_t4 r_t5 ++ encodeInstrsW [
      UnSeal r_t4 r_t1 r_t2;
      Store r_t4 r_t3
    ].

  (* Instructions to store a word `r_t2` in the seal `r_t1`, sealed by the hidden `WSealRange` placed at `off_seal`. *)

  (* This function will succeed only if the word in `r_t2` is a capability. *)
  (* > Otherwise, the machine will enter in a `Failed` state. *)

  (* This will return a new sealed value in `r_t1` and override the registers r_t2`, `r_t3`, `r_t4` and `r_t5`. *)
  (* > Note: The new sealed value is the same as the old one, both keeping the new value. *)
  Definition store_global_macro_cap_closure_instrs (off_seal : Z) :=
    encodeInstrsW [
      Mov r_t3 r_t2;
      Mov r_t2 r_t1;
      Mov r_t1 PC;
      Lea r_t1 (off_seal - 2)%Z;
      Load r_t1 r_t1
    ] ++ store_global_macro_cap_instrs ++ encodeInstrsW [
      Mov r_t1 r_t2;
      Mov r_t2 0;
      Mov r_t3 0;
      Mov r_t4 0;
      Mov r_t5 0;
      Jmp r_t0
    ].

  Lemma store_global_macro_cap_spec
    p_pc b_pc e_pc a_pc       (* PC *)
    a_cap                     (* Address *)
    p_seal b_seal e_seal τ Φ  (* Seal capability *)
    v w4 w5                   (* Values in registers *)
    φ:

    let instrs := store_global_macro_cap_instrs in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in

    ExecPCPerm p_pc →
    SubBounds b_pc e_pc a_pc (a_pc ^+ (length instrs))%a →

    permit_unseal p_seal = true →
    withinBounds b_seal e_seal τ = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →

    PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ codefrag a_pc instrs

      ∗ r_t1 ↦ᵣ WSealRange p_seal b_seal e_seal τ
      ∗ r_t2 ↦ᵣ WSealed τ scap
      ∗ r_t3 ↦ᵣ v ∗ interp v
      ∗ r_t4 ↦ᵣ w4
      ∗ r_t5 ↦ᵣ w5

      ∗ ▷ (valid_sealed (WSealed τ scap) τ Φ)
      ∗ seal_pred_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ▷ (PC ↦ᵣ WCap p_pc b_pc e_pc (a_pc ^+ (length instrs))%a
             ∗ codefrag a_pc instrs

             ∗ r_t1 ↦ᵣ WSealRange p_seal b_seal e_seal τ
             ∗ r_t2 ↦ᵣ WSealed τ scap
             ∗ r_t3 ↦ᵣ v
             ∗ (∃ w, r_t4 ↦ᵣ w)
             ∗ (∃ w, r_t5 ↦ᵣ w)

             ∗ sealed_cap (WSealable scap)
             ∗ na_own logrel_nais ⊤

             -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (? ? Hexec ? ? ? ?)
      "(HPC & Hprog & Hr_t1 & Hr_t2 & Hr_t3 & #Hinterp & Hr_t4 & Hr_t5 & #Hseal_valid & Hseal_pred & Hna & Hφ)".
    subst instrs; simpl in *.

    focus_block_0 "Hprog" as "Hblock" "Hcont".

    iApply dyn_typecheck_cap_spec; iFrameAutoSolve.
    iIntros "!> (HPC & Hblock & Hr_t3 & %Hvalue & Hr_t4 & Hr_t5)".
    iDestruct "Hr_t4" as (w4') "Hr_t4".
    iDestruct "Hr_t5" as (w5') "Hr_t5".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 1%nat "Hprog" as a_block Ha_block "Hblock" "Hcont".

    iDestruct (seal_pred_valid_sealed_eq with "[$Hseal_pred] Hseal_valid") as "Heqv".

    iInstr "Hblock".

    iAssert (sealed_cap (WSealable scap)) as "#Hseal_cap".
    { iDestruct "Hseal_valid" as (x) "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (WSealable scap)).
      iRewrite "Heqv".
      iFrame "HΦ". }

    iMod (na_inv_acc with "Hseal_cap Hna") as "(Hseal & Hna & Hclose)"; [ solve_ndisj .. |].
    iDestruct "Hseal" as (w) "(>%Heq & Hseal)".
    iDestruct "Hseal" as (?) "(>Haddr & >% & _)".
    case: Heq => _ _ <-.

    iGo "Hblock".

    iMod ("Hclose" with "[Haddr $Hna]") as "Hna".
    { iExists _; iSplitR; [ done |].
      by iExists _; iFrame "∗ #". }

    unfocus_block "Hblock" "Hcont" as "Hprog".

    iApply "Hφ".
    replace (a_block ^+ 2)%a with (a_pc ^+ 7)%a by solve_addr.
    iFrame "∗ #".
    iSplitL "Hr_t4"; eauto.
  Qed.

  Lemma store_global_macro_cap_closure_spec (off_seal : Z)
    p_pc b_pc e_pc a_pc  (* PC *)
    a_seal a_cap         (* Addresses *)
    p_seal τ Φ           (* Seal capability *)
    adv v w3 w4 w5       (* Values in registers *)
    φ:

    let instrs := store_global_macro_cap_closure_instrs off_seal in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in

    ExecPCPerm p_pc →
    ContiguousRegion a_pc (length instrs) →
    SubBounds b_pc e_pc a_pc (a_pc ^+ (length instrs))%a →

    permit_unseal p_seal = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →
    withinBounds τ (τ ^+ 1)%ot τ = true →

    (a_pc + off_seal)%a = Some a_seal →
    withinBounds b_pc e_pc a_seal = true →

    PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ region_mapsto a_pc (a_pc ^+ length instrs)%a instrs

      ∗ a_seal ↦ₐ WSealRange p_seal τ (τ ^+ 1)%ot τ
      ∗ r_t0 ↦ᵣ adv
      ∗ r_t1 ↦ᵣ WSealed τ scap
      ∗ r_t2 ↦ᵣ v ∗ interp v
      ∗ r_t3 ↦ᵣ w3
      ∗ r_t4 ↦ᵣ w4
      ∗ r_t5 ↦ᵣ w5

      ∗ ▷ (valid_sealed (WSealed τ scap) τ Φ)
      ∗ seal_pred_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ▷ (PC ↦ᵣ updatePcPerm adv
             ∗ region_mapsto a_pc (a_pc ^+ length instrs)%a instrs

             ∗ r_t0 ↦ᵣ adv
             ∗ r_t1 ↦ᵣ WSealed τ scap
             ∗ r_t2 ↦ᵣ WInt 0
             ∗ r_t3 ↦ᵣ WInt 0
             ∗ r_t4 ↦ᵣ WInt 0
             ∗ r_t5 ↦ᵣ WInt 0

             ∗ sealed_cap (WSealable scap)
             ∗ na_own logrel_nais ⊤

             -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (? ? ? Hbounds ? ? ? ? ? ?)
      "(HPC & Hprog & Hseal & Hr_t0 & Hr_t1 & Hr_t2 & Hr_t3 & Hinterp & Hr_t4 & Hr_t5 & Hseal_valid & Hseal_pred & Hna & Hφ)".

    iAssert (codefrag a_pc instrs) with "[Hprog]" as "Hprog"; [ iFrame |].

    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hblock" "Hcont".

    iGo "Hblock".
    { transitivity (a_pc + off_seal)%a; [ solve_addr +H6 | eauto ]. }

    iInstr "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 1%nat "Hprog" as addr_block1 Haddr_block1 "Hblock" "Hcont".

    iApply store_global_macro_cap_spec; last iFrame "Hseal_valid ∗"; eauto.

    iIntros "!> (HPC & Hblock & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hseal_cap & Hna)".
    iDestruct "Hr_t4" as (w4') "Hr_t4".
    iDestruct "Hr_t5" as (w5') "Hr_t5".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 2%nat "Hprog" as addr_block2 Haddr_block2 "Hblock" "Hcont".

    iGo "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    iApply "Hφ"; iFrame.
  Qed.

  Lemma store_global_macro_cap_closure_spec_full (off_seal : Z)
    p_pc b_pc e_pc a_pc  (* PC *)
    a_seal a_cap         (* Addresses *)
    p_seal τ             (* Seal capability *)
    adv v w3             (* Values in registers *)
    rmap:

    let instrs := store_global_macro_cap_closure_instrs off_seal in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in

    ExecPCPerm p_pc →
    ContiguousRegion a_pc (length instrs) →
    SubBounds b_pc e_pc a_pc (a_pc ^+ (length instrs))%a →

    permit_unseal p_seal = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →
    withinBounds τ (τ ^+ 1)%ot τ = true →

    (a_pc + off_seal)%a = Some a_seal →
    withinBounds b_pc e_pc a_seal = true →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2; r_t3 ]} →

    ⊢ (PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ region_mapsto a_pc (a_pc ^+ length instrs)%a instrs

      ∗ a_seal ↦ₐ WSealRange p_seal τ (τ ^+ 1)%ot τ
      ∗ r_t0 ↦ᵣ adv ∗ interp adv
      ∗ r_t1 ↦ᵣ WSealed τ scap ∗ interp (WSealed τ scap)
      ∗ r_t2 ↦ᵣ v ∗ interp v
      ∗ r_t3 ↦ᵣ w3

      ∗ seal_pred_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i ∗ interp w_i)

      -∗ WP Seq (Instr Executable)
            {{ v,
                (⌜v = HaltedV⌝ → (∃ r: Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤))
                  ∨ ⌜ v = FailedV ⌝ }})%I.
  Proof.
    iIntros (? ? ? Hbounds ? ? ? ? ? ? Hdom)
      "(HPC & Hprog & Hseal & Hr_t0 & #Hadv_interp & Hr_t1 & #Hseal_interp & Hr_t2 & Hinterp & Hr_t3 & Hseal_state & Hna & Hrmap)".

    iDestruct (jmp_to_unknown with "Hadv_interp") as "Cont".

    iExtractList "Hrmap" [r_t4; r_t5] as ["[Hr_t4 _]"; "[Hr_t5 _]"].

    iAssert (∃ Φ, ▷ valid_sealed (WSealed τ scap) τ Φ)%I as (Φ) "-#Hseal_valid".
    { iDestruct (interp_valid_sealed with "Hseal_interp") as (Φ) "Hseal_valid".
      by iExists Φ. }

    iApply store_global_macro_cap_closure_spec; last iFrame; eauto.

    iIntros "!> (HPC & Hprog & Hr_t0 & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hseal_cap & Hna)".

    iApply (wp_wand with "[-]"); [| iIntros (?) "?"; by iLeft ].

    iApply "Cont"; [| iFrame "HPC Hna" ]; revgoals.
    { iAssert (interp (WInt 0)) as "Hinterp_int".
      { by rewrite !fixpoint_interp1_eq. }

      iCombine "Hr_t5 Hinterp_int" as "Hr_t5".
      iCombine "Hr_t4 Hinterp_int" as "Hr_t4".
      iCombine "Hr_t3 Hinterp_int" as "Hr_t3".
      iCombine "Hr_t2 Hinterp_int" as "Hr_t2".
      iCombine "Hr_t1 Hseal_interp" as "Hr_t1".
      iCombine "Hr_t0 Hadv_interp" as "Hr_t0".
      iInsertList "Hrmap" [r_t5; r_t4; r_t3; r_t2; r_t1; r_t0].

      iFrame. }

    iPureIntro.
    rewrite !dom_insert_L Hdom.
    rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
    set_solver +.
  Qed.

End store_cap.
