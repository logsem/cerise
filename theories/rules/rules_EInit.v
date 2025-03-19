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

  Inductive EInit_fail (lregs : LReg) (lmem : LMem) (ot : OType) : Prop :=
    (* Etable is now unbounded *)
    (* | EInit_fail_etable_full *)
    | EInit_fail_pc_overflow :
      incrementLPC lregs = None →
      EInit_fail lregs lmem ot
    | EInit_fail_otype_overflow :
      (ot + 2)%ot = None →
      EInit_fail lregs lmem ot
    | EInit_fail_ccap_not_unique :
      EInit_fail lregs lmem ot
    | EInit_fail_dcap_not_unique :
      EInit_fail lregs lmem ot
    | EInit_fail_ccap_not_a_cap :
      EInit_fail lregs lmem ot
    | EInit_fail_dcap_not_a_cap :
      EInit_fail lregs lmem ot
    | EInit_fail_ccap_no_rx :
      EInit_fail lregs lmem ot
    | EInit_fail_dcap_no_rw :
      EInit_fail lregs lmem ot.

  Inductive EInit_spec (lregs lregs' : LReg) (lmem lmem' : LMem) (n n' : nat) (tidx : TIndex) (eid : EIdentity) (ot : OType) (rs : RegName) : cap_lang.val → Prop :=
    | EInit_success_no_revoke code_b code_e code_a code_v data_b data_e data_a data_v vmap :
      incrementLPC lregs = Some lregs' → (* PC can be incremented *)
      n + 1 = n' → (* n is the value of the EC register, it can be incremented to n' *)
      eid = hash_lmemory_region lmem code_b code_e code_v → (* the hashed value `eid` corresponds to hashing the code capability's memory footprint *)
      (ot + 2)%ot = Some (ot ^+ 2)%ot → (* the otype can be incremented *)
      lregs !! rs = Some (LCap RX code_b code_e code_a code_v) → (* rs contains a valid capability *)
      lmem !! (code_b, code_v) = Some (LCap RW data_b data_e data_a data_v) → (* the base address of the code capability points to a valid data capability *)
      is_valid_updated_lmemory lmem (finz.seq_between code_b code_e) code_v lmem' → (* support revocation *) (* all memory in the code capability is "current" w.r.t. revocation *)
      is_valid_updated_lmemory lmem (finz.seq_between data_b data_e) data_v lmem' → (* support revocation *) (* all memory in the data capability is "current" w.r.t. revocation *)
      unique_in_registersL lregs rs (LCap RX code_b code_e code_a code_v) → (* the code capability in the rs register is unique across all other registers *)
      unique_in_memoryL lmem vmap (LCap RW data_b data_e data_a data_v) → (* the data capability at base address b of the code capability is unique across all of memory *)
      incrementLPC (<[ rs := next_version_lword (LCap E code_b code_e (code_b ^+ 1)%a code_v)]> lregs) = Some lregs' → (* the pc will be incremented and rs will point to a "current" sentry capability *)
      EInit_spec lregs lregs' lmem lmem' n n' tidx eid ot rs NextIV
    | EInit_failure :
      n = n' →
      EInit_fail lregs lmem ot →
      EInit_spec lregs lregs' lmem lmem' n n' tidx eid ot rs FailedV.

  (* TODO: Failure lmem does not contain none at code_b etc *)
  (* TODO: how to determine tidx *)
  (* TODO @Denis *)
  Lemma wp_einit E pc_p pc_b pc_e pc_a pc_v pc_a' lw
    lregs lmem tidx eid rs n :
    decodeInstrWL lw = EInit rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →
    regs_of (EInit rs) ⊆ dom lregs →

    {{{ ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y ∗
        ▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw ∗
        PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗ (pc_a, pc_v) ↦ₐ lw ∗
        EC⤇ n (* need a fragment for the EC register *)
        }}}
      Instr Executable @ E
    {{{ lregs' lmem' retv n' ot, RET retv;
        ⌜ EInit_spec lregs lregs' lmem lmem' n n' tidx eid ot rs retv⌝ ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v ∗
        [∗ map] la↦lw ∈ lmem', la ↦ₐ lw ∗
        [∗ map] k↦y ∈ lregs', k ↦ᵣ y ∗
        EC⤇ n' ∗ (* need to give back the fragment of EC *)
        if decide (retv = NextIV) then (* if EInit was successful *)
          (* gain a non-duplicable token that asserts ownership over the enclave at etable index `tidx` *)
          enclave_cur tidx eid
          (* @TODO Denis/June: seal predicates needed? *)
        else emp }}}.
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
