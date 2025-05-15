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

  Definition EInit_spec_success (lregs lregs' : LReg) (lmem lmem' : LMem) (tidx tidx_incr : TIndex) (eid : EIdentity) (ot : OType) (rs : RegName) : iProp Σ :=
    ∃ glmem code_b code_e code_a code_v data_b data_e data_a data_v ,
    ⌜incrementLPC lregs = Some lregs'⌝ ∗ (* PC can be incremented *)
    ⌜(tidx+1)%nat = tidx_incr⌝ ∗
    ⌜eid = hash_lmemory_region lmem code_b code_e code_v⌝ ∗ (* eid = hash(ccap) *)
    ⌜(ot + 2)%ot = Some (ot ^+ 2)%ot ⌝ ∗ (* there are still otypes left in the pool *)
    ⌜lregs !! rs = Some (LCap RX code_b code_e code_a code_v) ⌝ ∗ (* rs contains a valid capability *)
    ⌜lmem !! (code_b, code_v) = Some (LCap RW data_b data_e data_a data_v)⌝ ∗ (* the base address of the code capability points to a valid data capability *)
    ⌜is_valid_updated_lmemory glmem lmem (finz.seq_between code_b code_e) code_v lmem' ⌝ ∗ (* all memory in the code capability is "current" w.r.t. revocation *)
    ⌜is_valid_updated_lmemory glmem lmem (finz.seq_between data_b data_e) data_v lmem' ⌝ ∗ (* all memory in the data capability is "current" w.r.t. revocation *)
    ⌜unique_in_registersL lregs (Some rs) (LCap RX code_b code_e code_a code_v) ⌝ ∗ (* the code capability is unique across all registers (except where it is stored: in `rs`) *)
    ⌜unique_in_registersL lregs None      (LCap RW data_b data_e data_a data_v) ⌝ ∗ (* the data capability is unique across all registers *)
    ⌜incrementLPC (<[ rs := next_version_lword (LCap E code_b code_e (code_b ^+ 1)%a code_v)]> lregs) = Some lregs' ⌝ ∗ (* the pc will be incremented and rs will point to a "current" sentry capability *)
      enclave_cur tidx eid (* non-dup token asserting ownership over the enclave at etable index `tidx` *)
      (* @TODO Denis/June: seal predicates needed? *)
  .

      Definition EInit_spec_failure (lregs lregs' : LReg) (lmem lmem' : LMem) (tidx tidx_incr : TIndex) (eid : EIdentity) (ot : OType) (rs : RegName) : iProp Σ. Admitted.

  (*     lmem = lmem' → *)
  (*     (* ... *) *)

  Lemma wp_einit E pc_p pc_b pc_e pc_a pc_v pc_a' lw lregs lmem tidx eid rs :
    decodeInstrWL lw = EInit rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →
    regs_of (EInit rs) ⊆ dom lregs →

    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
        PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        EC⤇ tidx }}}

      Instr Executable @ E

    {{{ lregs' lmem' retv tidx' ot, RET retv;
        ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw) ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v ∗
        EC⤇ tidx' ∗

        (EInit_spec_success lregs lregs' lmem lmem' tidx tidx' eid ot rs
      ∨ EInit_spec_failure lregs lregs' lmem lmem' tidx tidx' eid ot rs)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hregs & >Hmem & HPCCap & HPCv & HECv) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap tbl_cur tbl_prev tbl_all)
                         "(Hr & Hm
                          & -> & Htbl_cur & Htbl_prev & Htbl_all
                          & HEC
                          & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
                          & %HLinv)"
    ; cbn in *.

    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as %Hregs.
    (* have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs. *)
    (* specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri. *)
    (* odestruct (Hri rs) as [lsrcv [Hlsrc' Hlsrc] ]; first by set_solver+. *)

    (* Derive necessary memory *)
    iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hmem.
    (* iDestruct (gen_mem_valid_inSepM lmem lm with "Hm Hmem") as %Hma; eauto. *)

    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    iNext; iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)))
    ; eapply state_corresponds_reg_get_word ; eauto.
    (* 2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto. *)
    cbn in Hstep; simplify_eq.
    iModIntro.
    iSplitR "Hφ HECv". (* not yet sure what is needed *)
    iExists lr, lm, vmap.
    iExists etable, tbl_prev, (etable ∪ tbl_prev).
    iFrame; auto.


    all: admit.
   (* Qed. *)
  Admitted.

End cap_lang_rules.
