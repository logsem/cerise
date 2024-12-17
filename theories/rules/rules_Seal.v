From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{MP: MachineParameters}.
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

  Inductive Seal_failure  (lregs: LReg) (dst: RegName) (src1 src2: RegName) : LReg → Prop :=
  | Seal_fail_sealr lw :
      lregs !! src1 = Some lw →
      is_sealrL lw = false →
      Seal_failure lregs dst src1 src2 lregs
  | Seal_fail_sealb lw :
      lregs !! src2 = Some lw →
      is_sealbL lw = false →
      Seal_failure lregs dst src1 src2 lregs
  | Seal_fail_bounds lw p b e a sb:
      lregs !! src1 = Some (LSealRange p b e a) →
      lregs !! src2 = Some (LWSealable sb) →
      (permit_seal p = false ∨ withinBounds b e a = false) →
      Seal_failure lregs dst src1 src2 lregs
  | Seal_fail_incrPC p b e a sb :
      lregs !! src1 = Some (LSealRange p b e a) →
      lregs !! src2 = Some (LWSealable sb) →
      permit_seal p = true →
      withinBounds b e a = true →
      incrementLPC (<[ dst := LWSealed a sb ]> lregs) = None →
      Seal_failure lregs dst src1 src2 lregs.

  Inductive Seal_spec (lregs: LReg) (dst: RegName) (src1 src2: RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | Seal_spec_success p b e a sb:
      lregs !! src1 = Some (LSealRange p b e a) →
      lregs !! src2 = Some (LWSealable sb) →
      permit_seal p = true →
      withinBounds b e a = true →
      incrementLPC (<[ dst := LWSealed a sb ]> lregs) = Some lregs' →
      Seal_spec lregs dst src1 src2 lregs' NextIV
  | Seal_spec_failure :
      Seal_failure lregs dst src1 src2 lregs' →
      Seal_spec lregs dst src1 src2 lregs' FailedV.

  Lemma wp_Seal Ep pc_p pc_b pc_e pc_a pc_v lw dst src1 src2 lregs :
    decodeInstrWL lw = Seal dst src1 src2 ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Seal dst src1 src2) ⊆ dom lregs →

    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ Seal_spec lregs dst src1 src2 lregs' retv ⌝ ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ". *)
  (*   iApply wp_lift_atomic_head_step_no_fork; auto. *)
  (*   iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl. *)
  (*   iDestruct "Hσ1" as "[Hr Hm]". *)
  (*   iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs. *)
  (*   have ? := lookup_weaken _ _ _ _ HPC Hregs. *)
  (*   iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto. *)
  (*   iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
  (*   iNext. iIntros (e2 σ2 efs Hpstep). *)
  (*   apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)). *)
  (*   iIntros "_". *)
  (*   iSplitR; auto. eapply step_exec_inv in Hstep; eauto. *)

  (*   specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. *)
  (*   odestruct (Hri src2) as [r2v [Hr'2 Hr2]]. by set_solver+. *)
  (*   pdestruct (Hri src1) as [r1v [Hr'1 Hr1]]. by set_solver+. *)
  (*   destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+. clear Hri. *)

  (*   rewrite /exec /= Hr2 Hr1 /= in Hstep. *)

  (*   (* Now we start splitting on the different cases in the Seal spec, and prove them one at a time *) *)
  (*    destruct (is_sealr r1v) eqn:Hr1v. *)
  (*    2:{ (* Failure: r2 is not a sealrange *) *)
  (*      assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*      { *)
  (*        unfold is_sealr in Hr1v. *)
  (*        destruct_word r1v; by simplify_pair_eq. *)
  (*      } *)
  (*       iFailWP "Hφ" Seal_fail_sealr. *)
  (*    } *)
  (*    destruct r1v as [ | [ | p b e a ] | ]; try inversion Hr1v. clear Hr1v. *)

  (*    destruct (is_sealb r2v) eqn:Hr2v. *)
  (*    2:{ (* Failure: r2 is not a sealrange *) *)
  (*      assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*      { *)
  (*        unfold is_sealed in Hr2v. *)
  (*        destruct_word r2v; by simplify_pair_eq. *)
  (*      } *)
  (*       iFailWP "Hφ" Seal_fail_sealb. *)
  (*    } *)
  (*    destruct r2v as [ | sb | ]; try inversion Hr2v. clear Hr2v. *)

  (*    destruct (permit_seal p && withinBounds b e a) eqn:HSA. *)
  (*    2 : { (* Failure: r2 is either not within bounds or doesnt allow sealing *) *)
  (*      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2. *)
  (*      apply andb_false_iff in HSA. *)
  (*      iFailWP "Hφ" Seal_fail_bounds. *)
  (*    } *)
  (*    apply andb_true_iff in HSA; destruct HSA as (Hps & Hwb). *)

  (*    destruct (incrementPC (<[ dst := (WSealed a sb) ]> regs)) as  [ regs' |] eqn:Hregs'. *)
  (*    2: { (* Failure: the PC could not be incremented correctly *) *)
  (*      assert (incrementPC (<[ dst := (WSealed a sb) ]> reg) = None). *)
  (*      { eapply incrementPC_overflow_mono; first eapply Hregs'. *)
  (*        by rewrite lookup_insert_is_Some'; eauto. *)
  (*        by apply insert_mono; eauto. } *)

  (*      rewrite incrementPC_fail_updatePC /= in Hstep; auto. *)
  (*      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2. *)
  (*      (* Update the heap resource, using the resource for r2 *) *)
  (*      iFailWP "Hφ" Seal_fail_incrPC. *)
  (*    } *)

  (*    (* Success *) *)
  (*    rewrite /update_reg /= in Hstep. *)
  (*    eapply (incrementPC_success_updatePC _ mem) in Hregs' *)
  (*      as (p1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->). *)
  (*    eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono. *)
  (*    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn. *)
  (*    iFrame. *)
  (*    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*    iFrame. iModIntro. iApply "Hφ". iFrame. *)
  (*    iPureIntro. eapply Seal_spec_success; eauto. *)
  (*    unfold incrementPC. by rewrite HPC'' Ha_pc'. *)
  (*    Unshelve. all: auto. *)
  (* Qed. *)
  Admitted.

  (* after pruning impossible or impractical options, 5 wp rules remain *)

  Lemma wp_seal_success E pc_p pc_b pc_e pc_a pc_v lw lw' dst r1 r2 p b e a sb pc_a' :
    decodeInstrWL lw = Seal dst r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ lw'
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a
        ∗ ▷ r2 ↦ᵣ LWSealable sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWSealed a sb
          ∗ r1 ↦ᵣ LSealRange p b e a
          ∗ r2 ↦ᵣ LWSealable sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_r1 E pc_p pc_b pc_e pc_a pc_v lw r1 r2 p b e a sb pc_a' :
    decodeInstrWL lw = Seal r1 r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a
        ∗ ▷ r2 ↦ᵣ LWSealable sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LWSealed a sb
          ∗ r2 ↦ᵣ LWSealable sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_r2 E pc_p pc_b pc_e pc_a pc_v lw r1 r2 p b e a sb pc_a' :
    decodeInstrWL lw = Seal r2 r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a
        ∗ ▷ r2 ↦ᵣ LWSealable sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LSealRange p b e a
          ∗ r2 ↦ᵣ LWSealed a sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ r2 PC) // insert_insert (insert_commute _ r1 r2) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

  (* the 2 rules where r2=PC (and d=r1 or d≠r2) are also admissible *)

  Lemma wp_seal_PC E pc_p pc_b pc_e pc_a pc_v lw lw' dst r1 p b e a pc_a' :
    decodeInstrWL lw = Seal dst r1 PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ lw'
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWSealed a (LSCap pc_p pc_b pc_e pc_a pc_v)
          ∗ r1 ↦ᵣ LSealRange p b e a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hr1") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ dst PC) // insert_insert (insert_commute _ dst r1) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

 Lemma wp_seal_PC_eq E pc_p pc_b pc_e pc_a pc_v lw lw' r1 p b e a pc_a' :
    decodeInstrWL lw = Seal r1 r1 PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LWSealed a (LSCap pc_p pc_b pc_e pc_a pc_v)
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ r1 PC) // !insert_insert.
      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_nosb_r2 E pc_p pc_b pc_e pc_a pc_v lw r1 r2 p b e a lw2 pc_a' :
    decodeInstrWL lw = Seal r2 r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →
    is_sealbL lw2 = false →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r1 ↦ᵣ LSealRange p b e a
          ∗ ▷ r2 ↦ᵣ lw2 }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hfalse ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; last by iApply "Hφ".
    { by simplify_map_eq. }
  Qed.

End cap_lang_rules.
