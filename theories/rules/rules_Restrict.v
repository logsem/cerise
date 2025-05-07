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
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Inductive Restrict_failure (lregs: LReg) (dst: RegName) (src: Z + RegName) :=
  | Restrict_fail_src_nonz:
      z_of_argumentL lregs src = None →
      Restrict_failure lregs dst src
  | Restrict_fail_allowed lw:
      lregs !! dst = Some lw →
      is_mutable_rangeL lw = false →
      Restrict_failure lregs dst src
  | Restrict_fail_invalid_perm_cap p b e a v n:
      lregs !! dst = Some (LCap p b e a v) →
      p ≠ E →
      z_of_argumentL lregs src = Some n →
      PermFlowsTo (decodePerm n) p = false →
      Restrict_failure lregs dst src
  | Restrict_fail_PC_overflow_cap p b e a v n:
      lregs !! dst = Some (LCap p b e a v) →
      p ≠ E →
      z_of_argumentL lregs src = Some n →
      PermFlowsTo (decodePerm n) p = true →
      incrementLPC (<[ dst := LCap (decodePerm n) b e a v ]> lregs) = None →
      Restrict_failure lregs dst src
  | Restrict_fail_invalid_perm_sr p (b e a : OType) n:
      lregs !! dst = Some (LSealRange p b e a) →
      z_of_argumentL lregs src = Some n →
      SealPermFlowsTo (decodeSealPerms n) p = false →
      Restrict_failure lregs dst src
  | Restrict_fail_PC_overflow_sr p (b e a : OType) n:
      lregs !! dst = Some (LSealRange p b e a) →
      z_of_argumentL lregs src = Some n →
      SealPermFlowsTo (decodeSealPerms n) p = true →
      incrementLPC (<[ dst := LSealRange (decodeSealPerms n) b e a ]> lregs) = None →
      Restrict_failure lregs dst src.

  Inductive Restrict_spec (lregs: LReg) (dst: RegName) (src: Z + RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | Restrict_spec_success_cap p b e a v n:
      lregs !! dst = Some (LCap p b e a v) →
      p ≠ E ->
      z_of_argumentL lregs src = Some n →
      PermFlowsTo (decodePerm n) p = true →
      incrementLPC (<[ dst := LCap (decodePerm n) b e a v ]> lregs) = Some lregs' →
      Restrict_spec lregs dst src lregs' NextIV
  | Restrict_spec_success_sr p (b e a : OType) n:
      lregs !! dst = Some (LSealRange p b e a) →
      z_of_argumentL lregs src = Some n →
      SealPermFlowsTo (decodeSealPerms n) p = true →
      incrementLPC (<[ dst := LSealRange (decodeSealPerms n) b e a ]> lregs) = Some lregs' →
      Restrict_spec lregs dst src lregs' NextIV
  | Restrict_spec_failure:
      Restrict_failure lregs dst src →
      Restrict_spec lregs dst src lregs' FailedV.

  Definition exec_optL_Restrict
    (lregs : LReg) (dst: RegName) (src: Z + RegName) : option LReg :=
    n ← z_of_argumentL lregs src;
    lwdst ← lregs !! dst ;
    match lwdst with
    | LCap permPair b e a v =>
        match permPair with
        | E => None
        | _ => if PermFlowsTo (decodePerm n) permPair
              then
                lregs' ← incrementLPC ( <[dst := (LCap (decodePerm n) b e a v) ]> lregs) ;
                Some lregs'
              else None
        end
    | LSealRange p b e a =>
        if SealPermFlowsTo (decodeSealPerms n) p
        then
          lregs' ← incrementLPC ( <[dst := (LSealRange (decodeSealPerms n) b e a) ]> lregs) ;
          Some lregs'
        else None
    | _ => None
    end.

  Lemma wp_Restrict Ep pc_p pc_b pc_e pc_a pc_v lw dst src lregs :
    decodeInstrWL lw = Restrict dst src ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Restrict dst src) ⊆ dom lregs →

    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ Restrict_spec lregs dst src lregs' retv ⌝ ∗
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

    iApply (wp_wp2 (φ1 := exec_optL_Restrict lregs dst src)).

    iDestruct (state_interp_transient_intro (lm:= ∅) with "[$Hmap $Hσ1]") as "Hσ".
    { by rewrite big_sepM_empty. }

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_z_of_argument with "[Hφ Hpc_a Hcred $Hσ]"); first set_solver.
    iSplit.
    { iIntros "Hσ %Heqn1 %Heqn2".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply Restrict_spec_failure.
      by constructor.
    }
    iIntros ( n_perm ) "Hσ %HsrcL %Hsrc".

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iIntros (lwdst) "Hσ %HdstL %Hdst".

    destruct (decide (is_mutable_rangeL lwdst = true)) as [HmutRange|HmutRange]
    ; cycle 1.
    (* case LInt or LSealed : fail *)
    {
      rewrite not_true_iff_false in HmutRange.
      destruct_lword lwdst ; [ |  destruct p | | |] ; cbn in * ; simplify_eq.
      all: iModIntro.
      all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      all: iApply ("Hφ" with "[$Hpc_a $Hregs]").
      all: iPureIntro; econstructor; by eapply Restrict_fail_allowed.
    }

    destruct_lword lwdst ; cbn in * ; simplify_eq.
    - (* case LCap *)
      destruct (decide (p = E)) as [HpE|HnpE]; subst; first done.
      rewrite !rewrite_invert_match_E //=.
      destruct (PermFlowsTo (decodePerm n_perm) p) eqn:Hflow ; cycle 1.
      {
        destruct p ; cbn in * ; simplify_eq.
        all: iModIntro.
        all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        all: iApply ("Hφ" with "[$Hpc_a $Hregs]").
        all: iPureIntro; econstructor; by eapply Restrict_fail_invalid_perm_cap.
      }

      iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LCap (decodePerm n_perm) b e a v) with "Hσ") as "Hσ".
      { now set_solver. }
      { intros.
        eapply is_cur_lword_lea; eauto; eauto; apply isWithin_refl.
      }

      rewrite updatePC_incrementPC.
      iApply (wp_opt2_bind (k1 := fun x => Some x)).
      iApply wp_opt2_eqn_both.
      iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := <[ dst := LCap (decodePerm n_perm) b e a v]> lregs)).
      { now rewrite elem_of_dom (lookup_insert_dec HPC). }
      iFrame "Hσ".
      iSplit; cbn.
      + iIntros "Hσ %Hlin %Hin".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; constructor ; by eapply Restrict_fail_PC_overflow_cap.
      + iIntros (lrt' rs') "Hσ %Hlis %His".
        cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro.
        by eapply Restrict_spec_success_cap.

    - (* case LSealable *)
      destruct (SealPermFlowsTo (decodeSealPerms n_perm) p) eqn:Hflow ; cycle 1.
      {
        destruct p ; cbn in * ; simplify_eq.
        all: iModIntro.
        all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        all: iApply ("Hφ" with "[$Hpc_a $Hregs]").
        all: iPureIntro; econstructor; by eapply Restrict_fail_invalid_perm_sr.
      }

      iDestruct (update_state_interp_transient_from_regs_mod (dst := dst)
                   (lw2 := LSealRange (decodeSealPerms n_perm) b e a) with "Hσ") as "Hσ".
      { now set_solver. }
      { by intros; cbn. }

      rewrite updatePC_incrementPC.
      iApply (wp_opt2_bind (k1 := fun x => Some x)).
      iApply wp_opt2_eqn_both.
      iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := <[ dst := LSealRange (decodeSealPerms n_perm) b e a]> lregs)).
      { now rewrite elem_of_dom (lookup_insert_dec HPC). }
      iFrame "Hσ".
      iSplit; cbn.
      + iIntros "Hσ %Hlin %Hin".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; constructor ; by eapply Restrict_fail_PC_overflow_sr.
      + iIntros (lrt' rs') "Hσ %Hlis %His".
        cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro.
        by eapply Restrict_spec_success_sr.
  Qed.

  Lemma wp_restrict_success_reg_PC Ep pc_p pc_b pc_e pc_a pc_v pc_a' lw rv z:
    decodeInstrWL lw = Restrict PC (inr rv) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlowsTo (decodePerm z) pc_p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
         ∗ ▷ (pc_a, pc_v) ↦ₐ lw
         ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap (decodePerm z) pc_b pc_e pc_a' pc_v
           ∗ (pc_a, pc_v) ↦ₐ lw
           ∗ rv ↦ᵣ LInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc as [? ? ? ? ? ? Hvpc']; subst. inversion Hvpc'. naive_solver. }

     destruct Hspec as [| | * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       rewrite !insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.
     }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       destruct pc_p; congruence.
       incrementLPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_reg Ep pc_p pc_b pc_e pc_a pc_v pc_a' w r1 rv p b e a v z :
     decodeInstrWL w = Restrict r1 (inr rv) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) p = true →
     p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
         ∗ ▷ (pc_a, pc_v) ↦ₐ w
         ∗ ▷ r1 ↦ᵣ LCap p b e a v
         ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
           ∗ (pc_a, pc_v) ↦ₐ w
           ∗ rv ↦ᵣ LInt z
           ∗ r1 ↦ᵣ LCap (decodePerm z) b e a v }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows Hnp ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert
              (insert_commute _ PC r1) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_map_eq; eauto; try congruence.
      destruct p; congruence.
      incrementLPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z_PC Ep pc_p pc_b pc_e pc_a pc_v pc_a' lw z :
     decodeInstrWL lw = Restrict PC (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) pc_p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
         ∗ ▷ (pc_a, pc_v) ↦ₐ lw }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ LCap (decodePerm z) pc_b pc_e pc_a' pc_v
         ∗ (pc_a, pc_v) ↦ₐ lw }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc as [? ? ? ? ? ? Hvpc']; subst. inversion Hvpc'. naive_solver. }

     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       rewrite !insert_insert.
       iApply (regs_of_map_1 with "Hmap"). }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto.
       destruct pc_p; congruence.
       congruence.
       incrementLPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z Ep pc_p pc_b pc_e pc_a pc_v pc_a' lw r1 p b e a v z :
     decodeInstrWL lw = Restrict r1 (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) p = true →
     p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
         ∗ ▷ (pc_a, pc_v) ↦ₐ lw
         ∗ ▷ r1 ↦ᵣ LCap p b e a v }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
         ∗ (pc_a, pc_v) ↦ₐ lw
         ∗ r1 ↦ᵣ LCap (decodePerm z) b e a v }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows HpE ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc as [? ? ? ? ? ? Hvpc']; subst. inversion Hvpc'. naive_solver. }

     destruct Hspec as [| | * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert
               (insert_commute _ PC r1) // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       destruct p; congruence.
       incrementLPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

 Lemma wp_restrict_success_reg_sr Ep pc_p pc_b pc_e pc_a pc_v pc_a' lw r1 rv p (b e a : OType) z :
     decodeInstrWL lw = Restrict r1 (inr rv) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     SealPermFlowsTo (decodeSealPerms z) p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
         ∗ ▷ (pc_a, pc_v) ↦ₐ lw
         ∗ ▷ r1 ↦ᵣ LSealRange p b e a
         ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
           ∗ (pc_a, pc_v) ↦ₐ lw
           ∗ rv ↦ᵣ LInt z
           ∗ r1 ↦ᵣ LSealRange (decodeSealPerms z) b e a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
     { (* Success with WCap (contradiction) *)
       simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert
              (insert_commute _ PC r1) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_map_eq; eauto; try congruence.
      incrementLPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z_sr Ep pc_p pc_b pc_e pc_a pc_v pc_a' lw r1 p (b e a : OType) z :
     decodeInstrWL lw = Restrict r1 (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     SealPermFlowsTo (decodeSealPerms z) p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
         ∗ ▷ (pc_a, pc_v) ↦ₐ lw
         ∗ ▷ r1 ↦ᵣ LSealRange p b e a }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
         ∗ (pc_a, pc_v) ↦ₐ lw
         ∗ r1 ↦ᵣ LSealRange (decodeSealPerms z) b e a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc as [? ? ? ? ? ? Hvpc']; subst. inversion Hvpc'. naive_solver. }

     destruct Hspec as [| | * Hfail].
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert
               (insert_commute _ PC r1) // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementLPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

End cap_lang_rules.
