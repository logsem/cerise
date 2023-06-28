From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.
From cap_machine.examples.mutable_typed_shared_data Require Import dynamic_checks invariants.

Section load_int.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (* Instructions to load in `r_t2` the integer store in the seal `r_t2`, sealed by the `WSealRange` in `r_t1`. *)
  (* > Beware: The registers are NOT cleared. *)
  Definition load_global_macro_int_instrs :=
    encodeInstrsW [
      UnSeal r_t2 r_t1 r_t2;
      Load r_t2 r_t2
    ].

  (* Instructions to load in `r_t1` the integer store in the seal `r_t1`, sealed by the hidden `WSealRange`. *)
  (* This will return a new sealed value in `r_t1` and override the registers r_t2`. *)
  Definition load_global_macro_int_closure_instrs (τ : OType) :=
    [ WSealRange (true, true) τ (τ ^+ 1)%ot τ ] ++ encodeInstrsW [
      Mov r_t2 r_t1;
      Mov r_t1 PC;
      Lea r_t1 (-2)%Z;
      Load r_t1 r_t1
    ] ++ load_global_macro_int_instrs ++ encodeInstrsW [
      Mov r_t1 r_t2;
      Mov r_t2 0;
      Jmp r_t0
    ].

  Lemma load_global_macro_int_spec
    p_pc b_pc e_pc a_pc       (* PC *)
    a_cap                     (* Address *)
    p_seal b_seal e_seal τ Φ  (* Seal capability *)
    φ:

    let instrs := load_global_macro_int_instrs in
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
      ∗ seal_pred_int τ
      ∗ na_own logrel_nais ⊤

      ∗ ▷ (PC ↦ᵣ WCap p_pc b_pc e_pc (a_pc ^+ (length instrs))%a
             ∗ codefrag a_pc instrs

             ∗ r_t1 ↦ᵣ WSealRange p_seal b_seal e_seal τ
             ∗ (∃ w, r_t2 ↦ᵣ w ∗ ⌜is_z w⌝)

             ∗ sealed_int (WSealable scap)
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

    iAssert (sealed_int (WSealable scap)) as "#Hseal_int".
    { iDestruct "Hseal_valid" as (x) "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (WSealable scap)).
      iRewrite "Heqv".
      iFrame "HΦ". }

    iMod (na_inv_acc with "Hseal_int Hna") as "(>Hseal & Hna & Hclose)"; [ solve_ndisj .. |].
    iDestruct "Hseal" as (w) "(%Heq & (% & Haddr & %))".
    case: Heq => _ _ <-.

    iGo "Hprog".

    iMod ("Hclose" with "[Haddr $Hna]") as "Hna".
    { iExists _; iSplitR; [ done |].
      by iExists _; iFrame. }

    iApply "Hφ".
    iFrame.
    iSplitL "Hr_t2"; eauto.
  Qed.

  Lemma load_global_macro_int_closure_spec
    p_pc b_pc   (* PC *)
    a_cap       (* Address *)
    p_seal τ Φ  (* Seal capability *)
    adv w2      (* Values in registers *)
    φ:

    let instrs := load_global_macro_int_closure_instrs τ in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in
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
      ∗ r_t1 ↦ᵣ WSealed τ scap
      ∗ r_t2 ↦ᵣ w2

      ∗ ▷ (valid_sealed (WSealed τ scap) τ Φ)
      ∗ seal_pred_int τ
      ∗ na_own logrel_nais ⊤

      ∗ ▷ (PC ↦ᵣ updatePcPerm adv
             ∗ region_mapsto b_pc e_pc instrs

             ∗ r_t0 ↦ᵣ adv
             ∗ (∃ w, r_t1 ↦ᵣ w ∗ ⌜is_z w⌝)
             ∗ r_t2 ↦ᵣ WInt 0

             ∗ sealed_int (WSealable scap)
             ∗ na_own logrel_nais ⊤

             -∗ WP Seq (Instr Executable) {{ λ v, φ v }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (? ? ? ? Hbounds ? ? ? ?)
      "(HPC & Hprog & Hr_t0 & Hr_t1 & Hr_t2 & Hseal_valid & Hseal_pred & Hna & Hφ)".

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

    iApply load_global_macro_int_spec; last iFrame "Hseal_valid ∗"; eauto.

    iIntros "!> (HPC & Hblock & Hr_t1 & Hr_t2 & Hseal_int & Hna)".
    iDestruct "Hr_t2" as (v) "(Hr_t2 & %)".

    unfocus_block "Hblock" "Hcont" as "Hprog".

    focus_block 2%nat "Hprog" as addr_block2 Haddr_block2 "Hblock" "Hcont".

    iInstr "Hblock".

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

    replace ((b_pc ^+ 1) ^+ 9%nat)%a with (b_pc ^+ 10)%a by solve_addr.
    iFrame.

    by iExists _; iFrame.
  Qed.

  Lemma load_global_macro_int_closure_spec_full
    p_pc b_pc  (* PC *)
    a_cap      (* Address *)
    p_seal τ   (* Seal capability *)
    adv w2     (* Values in registers *)
    rmap:

    let instrs := load_global_macro_int_closure_instrs τ in
    let scap := SCap RW a_cap (a_cap ^+ 1)%a a_cap in
    let e_pc := (b_pc ^+ length instrs)%a in

    ExecPCPerm p_pc →
    ContiguousRegion b_pc (length instrs) →
    SubBounds b_pc e_pc b_pc (b_pc ^+ (length instrs))%a →

    permit_unseal p_seal = true →
    withinBounds a_cap (a_cap ^+ 1)%a a_cap = true →
    withinBounds τ (τ ^+ 1)%ot τ = true →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →

    ⊢ (PC ↦ᵣ WCap p_pc b_pc e_pc (b_pc ^+ 1)%a
      ∗ region_mapsto b_pc e_pc instrs

      ∗ r_t0 ↦ᵣ adv ∗ interp adv
      ∗ r_t1 ↦ᵣ WSealed τ scap ∗ interp (WSealed τ scap)
      ∗ r_t2 ↦ᵣ w2

      ∗ seal_pred_int τ
      ∗ na_own logrel_nais ⊤

      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i ∗ ⌜is_z w_i⌝)

      -∗ WP Seq (Instr Executable)
            {{ v, ⌜v = HaltedV⌝ → ∃ r: Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }})%I.
  Proof.
    iIntros (? ? ? ? Hbounds ? ? ? ? Hdom)
      "(HPC & Hprog & Hr_t0 & #Hadv_interp & Hr_t1 & #Hseal_interp & Hr_t2 & Hseal_pred & Hna & Hrmap)".

    iDestruct (jmp_to_unknown with "Hadv_interp") as "Cont".

    iAssert (∃ Φ, ▷ valid_sealed (WSealed τ scap) τ Φ)%I as (Φ) "-#Hseal_valid".
    { iDestruct (interp_valid_sealed with "Hseal_interp") as (Φ) "Hseal_valid".
      by iExists Φ. }

    iApply load_global_macro_int_closure_spec; last iFrame; eauto; [ solve_addr + |].

    iIntros "!> (HPC & Hprog & Hr_t0 & Hr_t1 & Hr_t2 & Hseal_int & Hna)".
    iDestruct "Hr_t1" as (v) "Hr_t1".

    iApply "Cont"; eauto; iFrame; revgoals.
    { iAssert (⌜is_z (WInt 0)⌝)%I as "H"; [ done |].
      iCombine "Hr_t2 H" as "Hr_t2".
      iInsertList "Hrmap" [r_t2; r_t1].

      iDestruct (big_sepM_mono _ (λ r w, r ↦ᵣ w ∗ interp w)%I with "[Hrmap]") as "Hrmap"; [| iFrame |].
      { iIntros (r w Hrmap) "(Hr & %Hr_int)".
        iFrame.
        destruct w; [| by simpl in Hr_int.. ].
        by rewrite fixpoint_interp1_eq. }

      iCombine "Hr_t0 Hadv_interp" as "Hr_t0".
      iInsertList "Hrmap" [r_t0].

      iFrame. }

    iPureIntro.
    rewrite !dom_insert_L Hdom.
    rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
    set_solver +.
  Qed.

End load_int.
