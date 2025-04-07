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

  Inductive EDeInit_fail : Prop :=
  | EDeInit_fail_no_valid_PC : EDeInit_fail
  | EDeInit_fail_no_seal_unseal_pair : EDeInit_fail.

  Inductive EDeInit_spec (etable etable' : ETable) (lregs lregs' : LReg) : cap_lang.val → Prop :=
  | EDeInit_success (tidx : TIndex) (eid : EIdentity) :
    etable !! tidx = Some eid →
    delete tidx etable = etable' →
    incrementLPC lregs = Some lregs' →
    EDeInit_spec etable etable' lregs lregs' NextIV
  | EDeInit_failure :
    EDeInit_fail →
    EDeInit_spec etable etable' lregs lregs' FailedV.

  (* TODO @Denis *)
  Lemma wp_edeinit E pc_p pc_b pc_e pc_a pc_v lw r lregs etable tidx eid :
    decodeInstrWL lw = EDeInit r →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EDeInit r) ⊆ dom lregs →
    (* TODO: EC register changes? *)

    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        enclave_cur tidx eid (* non-dup token asserting ownership over the enclave at etable index `tidx` *)
    }}}
      Instr Executable @ E
    {{{ lregs' etable' retv, RET retv;
        ⌜ EDeInit_spec etable etable' lregs lregs' retv⌝ ∗
        ([∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
   (*  iIntros (Hinstr Hvpc φ) "[Hpc Hpca] Hφ". *)
   (*  apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc. *)
   (*  iApply wp_lift_atomic_head_step_no_fork; auto. *)
   (*  iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl. *)
   (*  iDestruct "Hσ1" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv. *)
   (*  iDestruct (@gen_heap_valid with "Hr Hpc") as %?. *)
   (*  iDestruct (@gen_heap_valid with "Hm Hpca") as %?. *)
   (*  iModIntro. *)
   (*  iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
   (*  iIntros (e2 σ2 efs Hstep). *)
   (*  apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)). *)
   (*  iNext; iIntros "_". *)
   (*  iSplitR; auto. eapply step_exec_inv in Hstep; eauto. *)
   (*  2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v))) *)
   (*  ; eapply state_corresponds_reg_get_word ; eauto. *)
   (*  2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto. *)
   (*  cbn in Hstep; simplify_eq. *)
   (*  iModIntro. *)
   (*  iSplitR "Hφ Hpc Hpca"; last (iApply "Hφ" ; iFrame). *)
   (*  iExists lr, lm, vmap. *)
   (*  iFrame; auto. *)
   (* Qed. *)
  Admitted.

End cap_lang_rules.
