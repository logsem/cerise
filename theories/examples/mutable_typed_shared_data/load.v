From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.
From cap_machine.examples Require Import template_adequacy template_adequacy_ocpl.
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
  Definition load_global_macro_cap_closure_instrs (fptr_assert : Z) (off_seal : Z) :=
    encodeInstrsW [
      Mov r_t2 r_t1;
      Mov r_t1 PC;
      Lea r_t1 (off_seal - 1)%Z;
      Load r_t1 r_t1
    ] ++ load_global_macro_cap_instrs ++ encodeInstrsW [
      (* Prepare the registers for the `assert` macro. *)
      IsPtr r_t4 r_t2;
      Mov r_t5 1;
      (* Save registers *)
      Mov r_t6 r_t2
    ] ++ assert_instrs fptr_assert ++ encodeInstrsW [
      Mov r_t1 r_t6;
      Mov r_t6 0;
      Jmp r_t0
    ].

  (* Assert invariant *)
  Definition assert_inv b_a e_a a_flag :=
    na_inv logrel_nais ocpl.assertN (assert_inv b_a a_flag e_a).

  Definition flag_inv a_flag flagN := inv flagN (a_flag ↦ₐ WInt 0%Z).


  Lemma load_global_macro_cap_spec
    p_pc b_pc e_pc a_pc       (* PC *)
    a_cap                     (* Addresses *)
    p_seal b_seal e_seal τ Φ  (* Seal capability *)
    φ:

    let instrs := load_global_macro_cap_instrs in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in

    (* Validity PC *)
    ExecPCPerm p_pc →
    SubBounds b_pc e_pc a_pc (a_pc ^+ (length instrs))%a →

    (* Validity `WSealRange` *)
    permit_unseal p_seal = true →
    withinBounds b_seal e_seal τ = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →

    PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ codefrag a_pc instrs

      ∗ r_t1 ↦ᵣ WSealRange p_seal b_seal e_seal τ
      ∗ r_t2 ↦ᵣ WSealed τ scap

      (* Seal invariant *)
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
    p_pc b_pc e_pc a_pc               (* PC *)
    a_seal a_cap                      (* Addresses *)
    p_seal τ Φ                        (* Seal capability *)
    adv w2 w3 w4 w5 w6                (* Values in registers *)
    f_a b_a e_a a_flag flagN          (* Assert *)
    b_link a_link e_link assert_entry (* Linking *)
    φ:

    let instrs := load_global_macro_cap_closure_instrs f_a off_seal in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in

    (* Validity PC *)
    ExecPCPerm p_pc →
    ContiguousRegion a_pc (length instrs) →
    SubBounds b_pc e_pc a_pc (a_pc ^+ (length instrs))%a →

    (* Validity linking table *)
    (a_link + f_a)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true →

    (* Validity `WSealRange` *)
    permit_unseal p_seal = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →
    withinBounds τ (τ ^+ 1)%ot τ = true →

    (* Validity `WSealRange` location *)
    (a_pc + off_seal)%a = Some a_seal →
    withinBounds b_pc e_pc a_seal = true →

    PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ region_mapsto a_pc (a_pc ^+ length instrs)%a instrs

      ∗ a_seal ↦ₐ WSealRange p_seal τ (τ ^+ 1)%ot τ
      ∗ r_t0 ↦ᵣ adv
      ∗ r_t1 ↦ᵣ WSealed τ scap
      ∗ r_t2 ↦ᵣ w2
      ∗ r_t3 ↦ᵣ w3
      ∗ r_t4 ↦ᵣ w4
      ∗ r_t5 ↦ᵣ w5
      ∗ r_t6 ↦ᵣ w6

      (* Assert invariant *)
      ∗ assert_inv b_a e_a a_flag
      ∗ flag_inv a_flag flagN

      (* Linking table *)
      ∗ b_pc ↦ₐ WCap RO b_link e_link a_link
      ∗ assert_entry ↦ₐ WCap E b_a e_a b_a

      (* Seal invariant *)
      ∗ ▷ (valid_sealed (WSealed τ scap) τ Φ)
      ∗ seal_pred_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ▷ (PC ↦ᵣ updatePcPerm adv
             ∗ region_mapsto a_pc (a_pc ^+ length instrs)%a instrs

             ∗ r_t0 ↦ᵣ adv
             ∗ (∃ w, r_t1 ↦ᵣ w ∗ ⌜is_cap w⌝ ∗ interp w)
             ∗ r_t2 ↦ᵣ WInt 0
             ∗ r_t3 ↦ᵣ WInt 0
             ∗ r_t4 ↦ᵣ WInt 0
             ∗ r_t5 ↦ᵣ WInt 0
             ∗ r_t6 ↦ᵣ WInt 0

             ∗ sealed_cap (WSealable scap)
             ∗ na_own logrel_nais ⊤

             -∗ WP Seq (Instr Executable) {{ λ v, φ v }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (? ? ? Hbounds ? ? ? ? ? ? ? ?)
      "(HPC & Hprog & Hseal & Hr_t0 & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6 &
        Hassert_inv & Hflag_inv & Hlink & Hassert_link & Hseal_valid & Hseal_pred & Hna & Hφ)".

    iAssert (codefrag a_pc instrs) with "[Hprog]" as "Hprog"; [ iFrame |].

    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hblock" "Hcont".

    iGo "Hblock".
    { transitivity (a_pc + off_seal)%a; [ solve_addr +H8 | eauto ]. }

    iInstr "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 1%nat "Hprog" as addr_block1 Haddr_block1 "Hblock" "Hcont".

    iApply load_global_macro_cap_spec; last iFrame "Hseal_valid ∗"; eauto.

    iIntros "!> (HPC & Hblock & Hr_t1 & Hr_t2 & Hseal_cap & Hna)".
    iDestruct "Hr_t2" as (v) "(Hr_t2 & % & Hinterp)".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 2%nat "Hprog" as addr_block2 Haddr_block2 "Hblock" "Hcont".

    iGo "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 3%nat "Hprog" as addr_block3 Haddr_block3 "Hblock" "Hcont".

    iCombine "Hlink" "Hassert_link" as "Hlink".
    iMod (na_inv_alloc logrel_nais _ seal_capN with "Hlink") as "#Hlink_inv".

    iMod (na_inv_acc with "Hlink_inv Hna") as "(>(Hlink & Hassert_entry) & Hna & Hclose)"; [ solve_ndisj.. |].

    iApply assert_success; last iFrame; [ eauto .. | solve_ndisj | by destruct is_cap |].
    2: { apply contiguous_between_region_addrs; solve_addr +. }
    1: { split; eauto. solve_addr +H11 H13. }

    iIntros "!> (Hr_t0 & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & HPC & Hblock & Hna & Hlink & Hassert_entry)".

    iMod ("Hclose" with "[$Hna $Hlink $Hassert_entry]") as "Hna".

    iAssert (codefrag addr_block3 (assert_instrs f_a)) with "[$Hblock]" as "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 4%nat "Hprog" as addr_block4 Haddr_block4 "Hblock" "Hcont".

    iGo "Hblock".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    iApply "Hφ"; iFrame.
    by iExists _; iFrame.
  Qed.

  Lemma load_global_macro_cap_closure_spec_full (off_seal : Z)
    p_pc b_pc e_pc a_pc               (* PC *)
    a_seal a_cap                      (* Addresses *)
    p_seal τ                          (* Seal capability *)
    adv                               (* Values in registers *)
    f_a b_a e_a a_flag flagN          (* Assert *)
    b_link a_link e_link assert_entry (* Linking *)
    rmap:

    let instrs := load_global_macro_cap_closure_instrs f_a off_seal in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in

    (* Validity PC *)
    ExecPCPerm p_pc →
    ContiguousRegion a_pc (length instrs) →
    SubBounds b_pc e_pc a_pc (a_pc ^+ (length instrs))%a →

    (* Validity linking table *)
    (a_link + f_a)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true →

    (* Validity `WSealRange` *)
    permit_unseal p_seal = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →
    withinBounds τ (τ ^+ 1)%ot τ = true →

    (* Validity `WSealRange` location *)
    (a_pc + off_seal)%a = Some a_seal →
    withinBounds b_pc e_pc a_seal = true →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1 ]} →

    ⊢ (PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ region_mapsto a_pc (a_pc ^+ length instrs)%a instrs

      ∗ a_seal ↦ₐ WSealRange p_seal τ (τ ^+ 1)%ot τ
      ∗ r_t0 ↦ᵣ adv ∗ interp adv
      ∗ r_t1 ↦ᵣ WSealed τ scap ∗ interp (WSealed τ scap)

      (* Assert invariant *)
      ∗ assert_inv b_a e_a a_flag
      ∗ flag_inv a_flag flagN

      (* Linking table *)
      ∗ b_pc ↦ₐ WCap RO b_link e_link a_link
      ∗ assert_entry ↦ₐ WCap E b_a e_a b_a

      (* Seal invariant *)
      ∗ seal_pred_cap τ
      ∗ na_own logrel_nais ⊤

      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i ∗ interp w_i)

      -∗ WP Seq (Instr Executable)
            {{ v, ⌜v = HaltedV⌝ → ∃ r: Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }})%I.
  Proof.
    iIntros (? ? ? Hbounds ? ? ? ? ? ? ? ? Hdom)
      "(HPC & Hprog & Hseal & Hr_t0 & #Hadv_interp & Hr_t1 & #Hseal_interp &
        Hassert_inv & Hflag_inv & Hlink & Hassert_link & Hseal_pred & Hna & Hrmap)".

    iDestruct (jmp_to_unknown with "Hadv_interp") as "Cont".

    iExtractList "Hrmap" [r_t2; r_t3; r_t4; r_t5; r_t6]
      as ["[Hr_t2 _]"; "[Hr_t3 _]"; "[Hr_t4 _]"; "[Hr_t5 _]"; "[Hr_t6 _]"].

    iAssert (∃ Φ, ▷ valid_sealed (WSealed τ scap) τ Φ)%I as (Φ) "-#Hseal_valid".
    { iDestruct (interp_valid_sealed with "Hseal_interp") as (Φ) "Hseal_valid".
      by iExists Φ. }

    iApply load_global_macro_cap_closure_spec; last iFrame; eauto.

    iIntros "!> (HPC & Hprog & Hr_t0 & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6 & Hseal_cap & Hna)".
    iDestruct "Hr_t1" as (v) "(Hr_t1 & _ & Hinterp)".

    iApply "Cont"; [| iFrame "HPC Hna" ]; revgoals.
    { iAssert (interp (WInt 0)) as "Hinterp_int".
      { by rewrite !fixpoint_interp1_eq. }

      iCombine "Hr_t6 Hinterp_int" as "Hr_t6".
      iCombine "Hr_t5 Hinterp_int" as "Hr_t5".
      iCombine "Hr_t4 Hinterp_int" as "Hr_t4".
      iCombine "Hr_t3 Hinterp_int" as "Hr_t3".
      iCombine "Hr_t2 Hinterp_int" as "Hr_t2".
      iCombine "Hr_t1 Hinterp" as "Hr_t1".
      iCombine "Hr_t0 Hadv_interp" as "Hr_t0".
      iInsertList "Hrmap" [r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6].

      iFrame. }

    iPureIntro.
    rewrite !dom_insert_L Hdom.
    rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
    set_solver +.
  Qed.

End load_cap.
