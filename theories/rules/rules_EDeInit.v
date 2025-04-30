From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{reservedaddresses : ReservedAddresses}.
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

  Inductive EDeInit_fail lregs : Prop :=
  | EDeInit_fail_no_valid_PC :
    incrementLPC lregs = None →
    EDeInit_fail lregs
  | EDeInit_fail_no_seal_unseal_pair :
    (*... → *)
    EDeInit_fail lregs.

  Inductive EDeInit_spec (lregs lregs' : LReg) r (tidx : TIndex) (eid : EIdentity) is_cur : cap_lang.val → Prop :=
  | EDeInit_success b e a:
    (b+2)%ot = Some e →
    lregs !! r = Some (LSealRange (true,true) b e a) →
    incrementLPC lregs = Some lregs' →
    is_cur = true →
    EDeInit_spec lregs lregs' r tidx eid is_cur NextIV
  | EDeInit_failure :
    EDeInit_fail lregs →
    lregs = lregs' →
    EDeInit_spec lregs lregs' r tidx eid is_cur FailedV.

  (* SealRange <-> Word *)
  Definition is_seal_range (w : option LWord) : bool :=
    match w with
    | Some (LSealRange (true,true) b e a) =>
        match (b+2)%ot with
        | Some b2 => (e =? b2)%ot
        | None => false
        end
    |  _ => false
    end.

  (* TODO @Denis *)
  Lemma wp_edeinit E pc_p pc_b pc_e pc_a pc_v lw r lregs tidx eid (is_cur : bool) :
    decodeInstrWL lw = EDeInit r →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EDeInit r) ⊆ dom lregs →
    (* TODO: EC register changes? *)

    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        if is_seal_range (lregs !! r) then
          (* non-dup token asserting ownership over the enclave at etable index `tidx` *)
          if is_cur then enclave_cur tidx eid else enclave_prev tidx
        else
          emp
    }}}
      Instr Executable @ E
    {{{ lregs' retv, RET retv;
        ⌜ EDeInit_spec lregs lregs' r tidx eid is_cur retv⌝ ∗
        enclave_prev tidx ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
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
