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

  Inductive EStoreId_spec : cap_lang.val -> Prop :=
  | EStoreId_spec_success:
    EStoreId_spec NextIV
  |EStoreId_spec_failure:
    EStoreId_spec FailedV.

  Axiom has_lseal : Z -> ENum -> Prop.

  (* TODO @Denis *)
  Lemma wp_estoreid E pc_p pc_b pc_e pc_a pc_v lw rd rs otype any :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ rs ↦ᵣ LWInt otype
        ∗ rd ↦ᵣ any
    }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (pc_a, pc_v) ↦ₐ lw
        (* something with the pc increment *)
        ∗ rs ↦ᵣ LWInt otype
        ∗ (
          ⌜ retv = NextIV ⌝
          ∗ ∃ (id : EId), ∃ (enum : ENum),
              rd ↦ᵣ (LWInt id)
              ∗ (enclave_all enum id)
            ∗ ⌜ has_lseal otype enum ⌝
        ) ∨ (
          ⌜ retv = FailedV ⌝
          ∗ rd ↦ᵣ any
        )

    }}}.
  Proof.
    iIntros (Hinstr Hvpc φ) "(Hpc & Hpca & Hrs & Hrd) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    (* iDestruct "Hσ1" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv. *)
    (* iDestruct (@gen_heap_valid with "Hr Hpc") as %?. *)
    (* iDestruct (@gen_heap_valid with "Hm Hpca") as %?. *)
    (* iModIntro. *)
    (* iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
    (* iIntros (e2 σ2 efs Hstep). *)
    (* apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)). *)
    (* iNext; iIntros "_". *)
    (* iSplitR; auto. eapply step_exec_inv in Hstep; eauto. *)
    (* 2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v))) *)
    (* ; eapply state_corresponds_reg_get_word ; eauto. *)
    (* 2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto. *)
    (* cbn in Hstep; simplify_eq. *)
    (* iModIntro. *)
    (* iSplitR "Hφ Hpc Hpca". last (iApply "Hφ" ; iFrame). *)
   (*  iExists lr, lm, vmap. *)
   (*  iFrame; auto. *)
   (* Qed. *)
  Admitted.

End cap_lang_rules.
