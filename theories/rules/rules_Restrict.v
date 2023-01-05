From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive Restrict_failure (regs: Reg) (dst: RegName) (src: Z + RegName) :=
  | Restrict_fail_src_nonz:
      z_of_argument regs src = None →
      Restrict_failure regs dst src
  | Restrict_fail_allowed w:
      regs !! dst = Some w →
      is_mutable_range w = false →
      Restrict_failure regs dst src
  | Restrict_fail_invalid_perm_cap p b e a n:
      regs !! dst = Some (WCap p b e a) →
      p ≠ E →
      z_of_argument regs src = Some n →
      PermFlowsTo (decodePerm n) p = false →
      Restrict_failure regs dst src
  | Restrict_fail_PC_overflow_cap p b e a n:
      regs !! dst = Some (WCap p b e a) →
      p ≠ E →
      z_of_argument regs src = Some n →
      PermFlowsTo (decodePerm n) p = true →
      incrementPC (<[ dst := WCap (decodePerm n) b e a ]> regs) = None →
      Restrict_failure regs dst src
  | Restrict_fail_invalid_perm_sr p b e a n:
      regs !! dst = Some (WSealRange p b e a) →
      z_of_argument regs src = Some n →
      SealPermFlowsTo (decodeSealPerms n) p = false →
      Restrict_failure regs dst src
  | Restrict_fail_PC_overflow_sr p b e a n:
      regs !! dst = Some (WSealRange p b e a) →
      z_of_argument regs src = Some n →
      SealPermFlowsTo (decodeSealPerms n) p = true →
      incrementPC (<[ dst := WSealRange (decodeSealPerms n) b e a ]> regs) = None →
      Restrict_failure regs dst src.

  Inductive Restrict_spec (regs: Reg) (dst: RegName) (src: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Restrict_spec_success_cap p b e a n:
      regs !! dst = Some (WCap p b e a) →
      p ≠ E ->
      z_of_argument regs src = Some n →
      PermFlowsTo (decodePerm n) p = true →
      incrementPC (<[ dst := WCap (decodePerm n) b e a ]> regs) = Some regs' →
      Restrict_spec regs dst src regs' NextIV
  | Restrict_spec_success_sr p b e a n:
      regs !! dst = Some (WSealRange p b e a) →
      z_of_argument regs src = Some n →
      SealPermFlowsTo (decodeSealPerms n) p = true →
      incrementPC (<[ dst := WSealRange (decodeSealPerms n) b e a ]> regs) = Some regs' →
      Restrict_spec regs dst src regs' NextIV
  | Restrict_spec_failure:
      Restrict_failure regs dst src →
      Restrict_spec regs dst src regs' FailedV.

  Lemma wp_Restrict Ep pc_p pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = Restrict dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of (Restrict dst src) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Restrict_spec regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    rewrite /exec /= Hdst /= in Hstep.

    destruct (z_of_argument regs src) as [wsrc|] eqn:Hwsrc;
      pose proof Hwsrc as H'wsrc; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Hwsrc, Hstep. destruct src as [| r0]; [ congruence |].
       feed destruct (Hri r0) as [r0v [Hr'0 Hr0]].
       { unfold regs_of_argument. set_solver+. }
       rewrite Hr0 Hr'0 in Hwsrc Hstep.
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
       { destruct_word r0v; cbn in Hstep; try congruence; by simplify_pair_eq. }
       iFailWP "Hφ" Restrict_fail_src_nonz. }
    apply (z_of_arg_mono _ r) in Hwsrc; auto. rewrite Hwsrc in Hstep; simpl in Hstep.

    destruct (is_mutable_range wdst) eqn:Hwdst.
     2: { (* Failure: wdst is not of the right type *)
       unfold is_mutable_range in Hwdst.
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
       { destruct wdst as [ | [p b e a | ] | ]; try by inversion Hwdst.
         all: try by simplify_pair_eq.
         destruct p; try congruence.
         simplify_pair_eq; auto. }
       iFailWP "Hφ" Restrict_fail_allowed. }

    (* Now the proof splits depending on the type of value in wdst *)
    destruct wdst as [ | [p b e a | p b e a] | ].
    1,4: inversion Hwdst.

     (* First, the case where r1v is a capability *)
     + destruct (perm_eq_dec p E); [ subst p |].
       { rewrite /is_mutable_range in Hwdst; congruence. }

       destruct (PermFlowsTo (decodePerm wsrc) p) eqn:Hflows; cycle 1.
       { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Restrict_fail_invalid_perm_cap. }
       rewrite /update_reg /= in Hstep.

       destruct (incrementPC (<[ dst := WCap (decodePerm wsrc) b e a ]> regs)) eqn:Hregs';
         pose proof Hregs' as H'regs'; cycle 1.
       {
         assert (incrementPC (<[ dst := WCap( decodePerm wsrc) b e a ]> r) = None) as HH.
         { eapply incrementPC_overflow_mono; first eapply Hregs'.
             by rewrite lookup_insert_is_Some'; eauto.
               by apply insert_mono; eauto. }
         apply (incrementPC_fail_updatePC _ m) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" Restrict_fail_PC_overflow_cap. }

       eapply (incrementPC_success_updatePC _ m) in Hregs'
         as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct p; cbn in Hstep; eauto. congruence. }
       simplify_pair_eq.

       iFrame.
       iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
     (* Now, the case where wsrc is a sealrange *)
     + destruct (SealPermFlowsTo (decodeSealPerms wsrc) p) eqn:Hflows; cycle 1.
       { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Restrict_fail_invalid_perm_sr. }
       rewrite /update_reg /= in Hstep.

       destruct (incrementPC (<[ dst := WSealRange (decodeSealPerms wsrc) b e a ]> regs)) eqn:Hregs';
         pose proof Hregs' as H'regs'; cycle 1.
       {
         assert (incrementPC (<[ dst := WSealRange (decodeSealPerms wsrc) b e a ]> r) = None) as HH.
         { eapply incrementPC_overflow_mono; first eapply Hregs'.
             by rewrite lookup_insert_is_Some'; eauto.
               by apply insert_mono; eauto. }
         apply (incrementPC_fail_updatePC _ m) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" Restrict_fail_PC_overflow_sr. }

       eapply (incrementPC_success_updatePC _ m) in Hregs'
         as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct p; cbn in Hstep; eauto. }
       simplify_pair_eq.

       iFrame.
       iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 2; eauto.
  Qed.

  Lemma wp_restrict_success_reg_PC Ep pc_p pc_b pc_e pc_a pc_a' w rv z:
    decodeInstrW w = Restrict PC (inr rv) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlowsTo (decodePerm z) pc_p = true →

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap (decodePerm z) pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w
           ∗ rv ↦ᵣ WInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [| | * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.
     }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       destruct pc_p; congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_reg Ep pc_p pc_b pc_e pc_a pc_a' w r1 rv p b e a z :
     decodeInstrW w = Restrict r1 (inr rv) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) p = true →
     p ≠ E →

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WCap p b e a
         ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w
           ∗ rv ↦ᵣ WInt z
           ∗ r1 ↦ᵣ WCap (decodePerm z) b e a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows Hnp ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert
              (insert_commute _ PC r1) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_map_eq; eauto; try congruence.
      destruct p; congruence.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z_PC Ep pc_p pc_b pc_e pc_a pc_a' w z :
     decodeInstrW w = Restrict PC (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) pc_p = true →

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap (decodePerm z) pc_b pc_e pc_a'
         ∗ pc_a ↦ₐ w }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert.
       iApply (regs_of_map_1 with "Hmap"). }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto.
       destruct pc_p; congruence.
       congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z Ep pc_p pc_b pc_e pc_a pc_a' w r1 p b e a z :
     decodeInstrW w = Restrict r1 (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) p = true →
     p ≠ E →

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WCap p b e a }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
         ∗ pc_a ↦ₐ w
         ∗ r1 ↦ᵣ WCap (decodePerm z) b e a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows HpE ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [| | * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert
               (insert_commute _ PC r1) // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       destruct p; congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

 Lemma wp_restrict_success_reg_sr Ep pc_p pc_b pc_e pc_a pc_a' w r1 rv p b e a z :
     decodeInstrW w = Restrict r1 (inr rv) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     SealPermFlowsTo (decodeSealPerms z) p = true →

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WSealRange p b e a
         ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w
           ∗ rv ↦ᵣ WInt z
           ∗ r1 ↦ᵣ WSealRange (decodeSealPerms z) b e a }}}.
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
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert
              (insert_commute _ PC r1) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_map_eq; eauto; try congruence.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z_sr Ep pc_p pc_b pc_e pc_a pc_a' w r1 p b e a z :
     decodeInstrW w = Restrict r1 (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     SealPermFlowsTo (decodeSealPerms z) p = true →

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WSealRange p b e a }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
         ∗ pc_a ↦ₐ w
         ∗ r1 ↦ᵣ WSealRange (decodeSealPerms z) b e a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [| | * Hfail].
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert
               (insert_commute _ PC r1) // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

End cap_lang_rules.
