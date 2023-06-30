From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.
From cap_machine.examples.mutable_typed_shared_data Require Import dynamic_checks invariants.

Section load_cap.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (* Instructions to load in `r_t2` the capability store in the seal `r_t2`, sealed by the `WSealRange` in `r_t1`. *)
  (* > Beware: The registers are NOT cleared. *)
  Definition load_global_macro_cap_instrs :=
    encodeInstrsW [
      UnSeal r_t2 r_t1 r_t2;
      Load r_t2 r_t2
    ].

  (* Instructions to load in `r_t1` the capability store in the seal `r_t1`, sealed by the hidden `WSealRange` placed at `off_seal`. *)
  (* This will return a new sealed value in `r_t1` and override the registers r_t2`. *)
  Definition load_global_macro_cap_closure_instrs (off_seal : Z) :=
    encodeInstrsW [
      Mov r_t2 r_t1;
      Mov r_t1 PC;
      Lea r_t1 (off_seal - 1)%Z;
      Load r_t1 r_t1
    ] ++ load_global_macro_cap_instrs ++ encodeInstrsW [
      Mov r_t1 r_t2;
      Mov r_t2 0;
      Jmp r_t0
    ].

  Lemma load_global_macro_cap_spec
    p_pc b_pc e_pc a_pc       (* PC *)
    a_cap                     (* Address *)
    p_seal b_seal e_seal τ Φ  (* Seal capability *)
    φ:

    let instrs := load_global_macro_cap_instrs in
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

      ∗ ▷ (valid_sealed (WSealed τ scap) τ Φ)
      ∗ seal_pred_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ▷ (PC ↦ᵣ WCap p_pc b_pc e_pc (a_pc ^+ (length instrs))%a
             ∗ codefrag a_pc instrs

             ∗ r_t1 ↦ᵣ WSealRange p_seal b_seal e_seal τ
             ∗ (∃ w, r_t2 ↦ᵣ w ∗ ⌜is_cap w⌝ ∗ interp w)

             ∗ sealed_cap (WSealable scap)
             ∗ na_own logrel_nais ⊤

             -∗ WP Seq (Instr Executable) {{ λ v, φ v }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (? ? Hexec ? ? ? ?)
      "(HPC & Hprog & Hr_t1 & Hr_t2 & #Hseal_valid & Hseal_pred & Hna & Hφ)".
    subst instrs; simpl in *.

    codefrag_facts "Hprog".

    iDestruct (seal_pred_valid_sealed_eq with "[$Hseal_pred] Hseal_valid") as "Heqv".

    iInstr "Hprog".

    iAssert (sealed_cap (WSealable scap)) as "#Hseal_cap".
    { iDestruct "Hseal_valid" as (x) "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (WSealable scap)).
      iRewrite "Heqv".
      iFrame "HΦ". }

    iMod (na_inv_acc with "Hseal_cap Hna") as "(Hseal & Hna & Hclose)"; [ solve_ndisj .. |].
    iDestruct "Hseal" as (w) "(>%Heq & Hseal)".
    iDestruct "Hseal" as (?) "(>Haddr & >% & #Hseal_interp)".
    case: Heq => _ _ <-.

    iGo "Hprog".

    iMod ("Hclose" with "[Haddr Hseal_interp $Hna]") as "Hna".
    { iExists _; iSplitR; [ done |].
      by iExists _; iFrame "# ∗". }

    iApply "Hφ".
    iFrame.
    iSplitL "Hr_t2"; eauto.
  Qed.

  Lemma load_global_macro_cap_closure_spec (off_seal : Z)
    p_pc b_pc e_pc a_pc  (* PC *)
    a_seal a_cap         (* Addresses *)
    p_seal τ Φ           (* Seal capability *)
    adv w2               (* Values in registers *)
    φ:

    let instrs := load_global_macro_cap_closure_instrs off_seal in
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
      ∗ r_t2 ↦ᵣ w2

      ∗ ▷ (valid_sealed (WSealed τ scap) τ Φ)
      ∗ seal_pred_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ▷ (PC ↦ᵣ updatePcPerm adv
             ∗ region_mapsto a_pc (a_pc ^+ length instrs)%a instrs

             ∗ r_t0 ↦ᵣ adv
             ∗ (∃ w, r_t1 ↦ᵣ w ∗ ⌜is_cap w⌝ ∗ interp w)
             ∗ r_t2 ↦ᵣ WInt 0

             ∗ sealed_cap (WSealable scap)
             ∗ na_own logrel_nais ⊤

             -∗ WP Seq (Instr Executable) {{ λ v, φ v }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (? ? ? Hbounds ? ? ? ? ? ?)
      "(HPC & Hprog & Hseal & Hr_t0 & Hr_t1 & Hr_t2 & Hseal_valid & Hseal_pred & Hna & Hφ)".

    iAssert (codefrag a_pc instrs) with "[Hprog]" as "Hprog"; [ iFrame |].

    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hblock" "Hcont".

    iGo "Hblock".
    { transitivity (a_pc + off_seal)%a; [ solve_addr +H6 | eauto ]. }

    iInstr "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 1%nat "Hprog" as addr_block1 Haddr_block1 "Hblock" "Hcont".

    iApply load_global_macro_cap_spec; last iFrame "Hseal_valid ∗"; eauto.

    iIntros "!> (HPC & Hblock & Hr_t1 & Hr_t2 & Hseal_cap & Hna)".
    iDestruct "Hr_t2" as (v) "(Hr_t2 & ?)".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 2%nat "Hprog" as addr_block2 Haddr_block2 "Hblock" "Hcont".

    iInstr "Hblock".

    iGo "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    iApply "Hφ"; iFrame.
    by iExists _; iFrame.
  Qed.

  Lemma load_global_macro_cap_closure_spec_full (off_seal : Z)
    p_pc b_pc e_pc a_pc  (* PC *)
    a_seal a_cap         (* Addresses *)
    p_seal τ             (* Seal capability *)
    adv w2               (* Values in registers *)
    rmap:

    let instrs := load_global_macro_cap_closure_instrs off_seal in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in

    ExecPCPerm p_pc →
    ContiguousRegion a_pc (length instrs) →
    SubBounds b_pc e_pc a_pc (a_pc ^+ (length instrs))%a →

    permit_unseal p_seal = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →
    withinBounds τ (τ ^+ 1)%ot τ = true →

    (a_pc + off_seal)%a = Some a_seal →
    withinBounds b_pc e_pc a_seal = true →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →

    ⊢ (PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ region_mapsto a_pc (a_pc ^+ length instrs)%a instrs

      ∗ a_seal ↦ₐ WSealRange p_seal τ (τ ^+ 1)%ot τ
      ∗ r_t0 ↦ᵣ adv ∗ interp adv
      ∗ r_t1 ↦ᵣ WSealed τ scap ∗ interp (WSealed τ scap)
      ∗ r_t2 ↦ᵣ w2

      ∗ seal_pred_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i ∗ interp w_i)

      -∗ WP Seq (Instr Executable)
            {{ v, ⌜v = HaltedV⌝ → ∃ r: Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }})%I.
  Proof.
    iIntros (? ? ? Hbounds ? ? ? ? ? ? Hdom)
      "(HPC & Hprog & Hseal & Hr_t0 & #Hadv_interp & Hr_t1 & #Hseal_interp & Hr_t2 & Hseal_pred & Hna & Hrmap)".

    iDestruct (jmp_to_unknown with "Hadv_interp") as "Cont".

    iAssert (∃ Φ, ▷ valid_sealed (WSealed τ scap) τ Φ)%I as (Φ) "-#Hseal_valid".
    { iDestruct (interp_valid_sealed with "Hseal_interp") as (Φ) "Hseal_valid".
      by iExists Φ. }

    iApply load_global_macro_cap_closure_spec; last iFrame; eauto.

    iIntros "!> (HPC & Hprog & Hr_t0 & Hr_t1 & Hr_t2 & Hseal_cap & Hna)".
    iDestruct "Hr_t1" as (v) "(Hr_t1 & _ & Hinterp)".

    iApply "Cont"; [| iFrame "HPC Hna" ]; revgoals.
    { iAssert (interp (WInt 0)) as "Hinterp_int".
      { by rewrite !fixpoint_interp1_eq. }

      iCombine "Hr_t2 Hinterp_int" as "Hr_t2".
      iCombine "Hr_t1 Hinterp" as "Hr_t1".
      iCombine "Hr_t0 Hadv_interp" as "Hr_t0".
      iInsertList "Hrmap" [r_t0; r_t1; r_t2].

      iFrame. }

    iPureIntro.
    rewrite !dom_insert_L Hdom.
    rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
    set_solver +.
  Qed.

End load_cap.
