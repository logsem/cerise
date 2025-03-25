From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac gmap.
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

  Inductive EStoreId_spec (lregs lregs' : LReg) (lmem lmem' : LMem) otype tidx : cap_lang.val -> Prop :=
  | EStoreId_spec_success:
    has_seal otype tidx → (* we associate a given table index with the provided otype *)
    EStoreId_spec lregs lregs' lmem lmem' otype tidx NextIV
  |EStoreId_spec_failure:
    EStoreId_spec lregs lregs' lmem lmem' otype tidx FailedV.

  (* TODO @Denis *)
  (* The EStoreId instruction fetches the machine's stored hash for a given OType.
     It is used by the client of an enclave to verify that a value signed by a given OType originates from code with a known hash `I`. *)
  (* Logically, the crux of this contract is that the post-condition contains a duplicable resource `enclave_all`,
     which states that an enclave has existed at some point in the past at some index `tidx` in the enclave table, and that this index corresponds to some hash/EIdentity `I` *)
  (* Essentially it gives us a partial view on the enclave table, since we now know that at a particular index, at some point, there was an enclave with a particular identity. *)
  (* In a later step of the verification, an invariant will allow us to trade this resource for the specific predicate that always holds for results signed by enclaves with that hash... *)
  (* This enables "learning" some information about the signed, yet unknown result: we will be able to establish that at least the above predicate will hold for it... *)
  Lemma wp_estoreid E pc_p pc_b pc_e pc_a pc_a' pc_v lw rd rs otype any lregs lmem :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
        PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        rs ↦ᵣ LWInt otype ∗
        rd ↦ᵣ any }}}
      Instr Executable @ E
    {{{ lregs' lmem' tidx retv, RET retv;
        ⌜ EStoreId_spec lregs lregs' lmem lmem' otype tidx retv⌝ ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        rs ↦ᵣ LWInt otype ∗
        [∗ map] k↦y ∈ lregs', k ↦ᵣ y ∗
        [∗ map] la↦lw ∈ lmem', la ↦ₐ lw ∗
        if decide (retv = NextIV) then
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v ∗
          ∃ (I : EIdentity),
            rd ↦ᵣ (LWInt I) ∗
            enclave_all tidx I (*!*)
        else
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
          rd ↦ᵣ any }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' φ) "(Hpc & Hpca & Hrs & Hrd) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=".
    iDestruct "Hσ1" as (lr lm vmap) "(% & % & % & Hr & Hm & %Hcur & Henc_cur & Henc_prev & Henc_all & HEC & %Hdisj & %Hdom & %Hdisj2 & %Union_all & %State)".
    all: admit.
    (* iDestruct (@gen_heap_valid with "Hr Hpc") as %?. *)
    (* iDestruct (@gen_heap_valid with "Hm Hpca") as %?. *)
    (* iModIntro. *)
    (* iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
    (* iIntros (e2 σ2 efs Hstep). *)
    (* apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)). *)
    (* iNext; iIntros "_". *)
    (* iSplitR; auto. *)
    (* iModIntro. *)
    (* rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v))). *)
    (* 2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto. *)
    (* cbn in Hstep; simplify_eq. *)
    (* iModIntro. *)
    (* iSplitR "Hφ Hpc Hpca". last (iApply "Hφ" ; iFrame). *)
   (*  iExists lr, lm, vmap. *)
   (*  iFrame; auto. *)
   (* Qed. *)
  Admitted.

End cap_lang_rules.
