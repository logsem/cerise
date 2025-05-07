From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{MP: MachineParameters}.
  Context `{reservedaddresses : ReservedAddresses}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Inductive Subseg_failure (lregs: LReg) (dst: RegName) (src1 src2: Z + RegName) : LReg → Prop :=
  | Subseg_fail_allowed lw :
      lregs !! dst = Some lw →
      is_mutable_rangeL lw = false →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_src1_nonaddr p b e a v:
      lregs !! dst = Some (LCap p b e a v) →
      addr_of_argumentL lregs src1 = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_src2_nonaddr p b e a v:
      lregs !! dst = Some (LCap p b e a v) →
      addr_of_argumentL lregs src2 = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_src1_nonotype p b e a:
      lregs !! dst = Some (LSealRange p b e a) →
      otype_of_argumentL lregs src1 = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_src2_nonotype p b e a:
      lregs !! dst = Some (LSealRange p b e a) →
      otype_of_argumentL lregs src2 = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_not_iswithin_cap p b e a v a1 a2 :
      lregs !! dst = Some (LCap p b e a v) →
      addr_of_argumentL lregs src1 = Some a1 →
      addr_of_argumentL lregs src2 = Some a2 →
      isWithin a1 a2 b e = false →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_incrPC_cap p b e a v a1 a2 :
      lregs !! dst = Some (LCap p b e a v) →
      p <> E →
      addr_of_argumentL lregs src1 = Some a1 →
      addr_of_argumentL lregs src2 = Some a2 →
      isWithin a1 a2 b e = true →
      incrementLPC (<[ dst := LCap p a1 a2 a v ]> lregs) = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_not_iswithin_sr p b e a a1 a2 :
      lregs !! dst = Some (LSealRange p b e a) →
      otype_of_argumentL lregs src1 = Some a1 →
      otype_of_argumentL lregs src2 = Some a2 →
      isWithin a1 a2 b e = false →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_incrPC_sr p b e a a1 a2 :
      lregs !! dst = Some (LSealRange p b e a) →
      otype_of_argumentL lregs src1 = Some a1 →
      otype_of_argumentL lregs src2 = Some a2 →
      isWithin a1 a2 b e = true →
      incrementLPC (<[ dst := LSealRange p a1 a2 a ]> lregs) = None →
      Subseg_failure lregs dst src1 src2 lregs.

  Inductive Subseg_spec (lregs: LReg) (dst: RegName) (src1 src2: Z + RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | Subseg_spec_success_cap p b e a v a1 a2:
      lregs !! dst = Some (LCap p b e a v) ->
      p <> E ->
      addr_of_argumentL lregs src1 = Some a1 ->
      addr_of_argumentL lregs src2 = Some a2 ->
      isWithin a1 a2 b e = true ->
      incrementLPC (<[ dst := LCap p a1 a2 a v]> lregs) = Some lregs' ->
      Subseg_spec lregs dst src1 src2 lregs' NextIV
  | Subseg_spec_success_sr p b e a v a1 a2:
      lregs !! dst = Some (LSealRange p b e a) ->
      otype_of_argumentL lregs src1 = Some a1 ->
      otype_of_argumentL lregs src2 = Some a2 ->
      isWithin a1 a2 b e = true ->
      incrementLPC (<[ dst := LSealRange p a1 a2 a ]> lregs) = Some lregs' ->
      Subseg_spec lregs dst src1 src2 lregs' NextIV
  | Subseg_spec_failure :
      Subseg_failure lregs dst src1 src2 lregs' →
      Subseg_spec lregs dst src1 src2 lregs' FailedV.

  Definition exec_optL_Subseg
    (lregs : LReg) (dst: RegName) (src1 src2: Z + RegName) : option LReg :=
    lwdst ← lregs !! dst ;
    match lwdst with
    | LCap p b e a v =>
        a1 ← addr_of_argumentL lregs src1 ;
        a2 ← addr_of_argumentL lregs src2 ;
        match p with
        | E => None
        | _ =>
            (if isWithin a1 a2 b e
              then
                lregs' ← incrementLPC ( <[dst := (LCap p a1 a2 a v) ]> lregs) ;
                Some lregs'
              else None)
        end
    | LSealRange p b e a =>
        o1 ← otype_of_argumentL lregs src1 ;
        o2 ← otype_of_argumentL lregs src2 ;
        if isWithin o1 o2 b e
        then
          lregs' ← incrementLPC ( <[dst := (LSealRange p o1 o2 a) ]> lregs) ;
          Some lregs'
        else None
    | _ => None
    end.

  Lemma wp_Subseg Ep pc_p pc_b pc_e pc_a pc_v lw dst src1 src2 lregs :
    decodeInstrWL lw = Subseg dst src1 src2 ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Subseg dst src1 src2) ⊆ dom lregs →

    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ Subseg_spec lregs dst src1 src2 lregs' retv ⌝ ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".

    cbn in Dregs.
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpc_a $Hmap Hφ]").
    iModIntro.
    iIntros (σ1) "(Hσ1 & Hmap &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hrpc & %Hmema & %Hcorrpc & %Hdecode) Hcred".

    iApply (wp_wp2 (φ1 := exec_optL_Subseg lregs dst src1 src2)).

    iDestruct (state_interp_transient_intro (lm:= ∅) with "[$Hmap $Hσ1]") as "Hσ".
    { by rewrite big_sepM_empty. }

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iIntros (lwdst) "Hσ %HdstL %Hdst".
    destruct lwdst; cbn in * ; simplify_eq; cycle 2.
    1,2: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
    1,2: iApply ("Hφ" with "[$Hpc_a $Hregs]").
    1,2: iPureIntro; eapply Subseg_spec_failure.
    1,2: by econstructor.

    destruct sb as [ p b e a v|p b e a]; cbn in * ; simplify_eq.
    - (* case LCap *)
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_addr_of_argument with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iSplit.
    { iIntros "Hσ %Heqn1 %Heqn2".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro; eapply Subseg_spec_failure; by econstructor.
    }
    iIntros ( b' ) "Hσ %Hsrc1L %Hsrc1".

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_addr_of_argument with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
     iSplit.
     { iIntros "Hσ %Heqn1 %Heqn2".
       iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
       iApply ("Hφ" with "[$Hpc_a $Hregs]").
       iPureIntro.
       eapply Subseg_spec_failure.
       by econstructor.
     }
     iIntros ( e' ) "Hσ %Hsrc2L %Hsrc2".
     destruct (decide (p = E)) as [HpE|HpnE]; subst.
     {
       iModIntro.
       iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
       iApply ("Hφ" with "[$Hpc_a $Hregs]").
       iPureIntro; econstructor; by eapply Subseg_fail_allowed.
     }
     rewrite !rewrite_invert_match_E; eauto.

     destruct (isWithin b' e' b e) eqn:Hwithin; cycle 1.
     {
       iModIntro.
       iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
       iApply ("Hφ" with "[$Hpc_a $Hregs]").
       iPureIntro; econstructor; by eapply Subseg_fail_not_iswithin_cap.
     }


     iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LCap p b' e' a v) with "Hσ") as "Hσ".
     { now set_solver. }
     { intros.
       eapply is_cur_lword_lea; eauto; eauto.
     }

      rewrite updatePC_incrementPC.
      iApply (wp_opt2_bind (k1 := fun x => Some x)).
      iApply wp_opt2_eqn_both.
      iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := <[ dst := LCap p b' e' a v]> lregs)).
      { now rewrite elem_of_dom (lookup_insert_dec HPC). }
      iFrame "Hσ".
      iSplit; cbn.
      + iIntros "Hσ %Hlin %Hin".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; constructor ; by eapply Subseg_fail_incrPC_cap.
      + iIntros (lrt' rs') "Hσ %Hlis %His".
        cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; by eapply Subseg_spec_success_cap.

    - (* case LSealRange *)
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_otype_of_argument with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iSplit.
    { iIntros "Hσ %Heqn1 %Heqn2".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro; eapply Subseg_spec_failure; by econstructor.
    }
    iIntros ( b' ) "Hσ %Hsrc1L %Hsrc1".

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_otype_of_argument with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
     iSplit.
     { iIntros "Hσ %Heqn1 %Heqn2".
       iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
       iApply ("Hφ" with "[$Hpc_a $Hregs]").
       iPureIntro.
       eapply Subseg_spec_failure.
       by econstructor.
     }
     iIntros ( e' ) "Hσ %Hsrc2L %Hsrc2".

     destruct (@isWithin ONum b' e' b e ) eqn:Hwithin; cycle 1.
     {
       iModIntro.
       iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
       iApply ("Hφ" with "[$Hpc_a $Hregs]").
       iPureIntro; econstructor; by eapply Subseg_fail_not_iswithin_sr.
     }


     iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LSealRange p b' e' a) with "Hσ") as "Hσ".
     { now set_solver. }
     { intros; by cbn. }

      rewrite updatePC_incrementPC.
      iApply (wp_opt2_bind (k1 := fun x => Some x)).
      iApply wp_opt2_eqn_both.
      iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := <[ dst := LSealRange p b' e' a]> lregs)).
      { now rewrite elem_of_dom (lookup_insert_dec HPC). }
      iFrame "Hσ".
      iSplit; cbn.
      + iIntros "Hσ %Hlin %Hin".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; constructor ; by eapply Subseg_fail_incrPC_sr.
      + iIntros (lrt' rs') "Hσ %Hlis %His".
        cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro.
        by eapply Subseg_spec_success_sr.
  Qed.

  Lemma wp_subseg_success E pc_p pc_b pc_e pc_a pc_v lw dst r1 r2 p b e a v n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ r1 ↦ᵣ LInt n1
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LCap p a1 a2 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_same E pc_p pc_b pc_e pc_a pc_v lw dst r1 p b e a v n1 a1 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 →
    p ≠ machine_base.E →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LCap p a1 a1 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_l E pc_p pc_b pc_e pc_a pc_v lw dst r2 p b e a v n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inl n1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LCap p a1 a2 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_r E pc_p pc_b pc_e pc_a pc_v lw dst r1 p b e a v n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LCap p a1 a2 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_lr E pc_p pc_b pc_e pc_a pc_v lw dst p b e a v n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inl n1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LCap p a1 a2 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_fail_lr E pc_p pc_b pc_e pc_a pc_v lw dst p b e a v n1 n2 a1 a2 :
    decodeInstrWL lw = Subseg dst (inl n1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    ¬ (p ≠ machine_base.E ∧ isWithin a1 a2 b e = true) →
    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ dst ↦ᵣ LCap p b e a v }}}
      Instr Executable @ E
      {{{ RET FailedV;
          ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
            ∗ ▷ (pc_a, pc_v) ↦ₐ lw
            ∗ ▷ dst ↦ᵣ LCap p b e a v }}}.
  Proof.
    iIntros (? ? ? ? Hncond ?) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [| | * Hfail].
    { (* Success (contradiction) *)
      exfalso. apply Hncond. simplify_map_eq. split; first done.
      by cbn in * ; simplify_eq. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure *)
      destruct Hfail; cbn in *; simplify_map_eq.
      all: iApply "Hφ"; iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_subseg_success_pc E pc_p pc_b pc_e pc_a pc_v lw r1 r2 n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg PC (inr r1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LInt n1
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a2 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ r2 ↦ᵣ LInt n2
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_same E pc_p pc_b pc_e pc_a pc_v lw r1 n1 a1 pc_a' :
    decodeInstrWL lw = Subseg PC (inr r1) (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 →
    pc_p ≠ machine_base.E →
    isWithin a1 a1 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a1 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_l E pc_p pc_b pc_e pc_a pc_v lw r2 n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg PC (inl n1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a2 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ LInt n2
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r2) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_r E pc_p pc_b pc_e pc_a pc_v lw r1 n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg PC (inr r1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a2 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_lr E pc_p pc_b pc_e pc_a pc_v lw n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg PC (inl n1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a2 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

  Lemma wp_subseg_success_sr E pc_p pc_b pc_e pc_a pc_v lw dst r1 r2 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a
        ∗ ▷ r1 ↦ᵣ LInt n1
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LSealRange p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with WCap (contradiction) *)
       simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_same_sr E pc_p pc_b pc_e pc_a pc_v lw dst r1 p b e a n1 a1 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LSealRange p a1 a1 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with LSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_l_sr E pc_p pc_b pc_e pc_a pc_v lw dst r2 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inl n1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LSealRange p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with LSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_r_sr E pc_p pc_b pc_e pc_a pc_v lw dst r1 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LSealRange p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with LSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_lr_sr E pc_p pc_b pc_e pc_a pc_v lw dst p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inl n1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LSealRange p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with LSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

End cap_lang_rules.
