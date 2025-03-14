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

  (* TODO @Denis *)
  (* The EStoreId instruction fetches the machine's stored hash for a given OType.
     It is used by the client of an enclave to verify that a value signed by a given OType originates from code with a known hash `I`. *)
  (* Logically, the crux of this contract is that the post-condition contains a duplicable resource `enclave_all`,
     which states that an enclave has existed at some point in the past at some index `tid` in the enclave table, and that this index corresponds to some hash/EIdentity `I` *)
  (* Essentially it gives us a partial view on the enclave table, since we now know that at a particular index, at some point, there was an enclave with a particular identity. *)
  (* In a later step of the verification, we will trade this resource for the specific predicate that always holds for results signed by enclaves with that hash... *)
  (* This enables "learning" some information about the signed, yet unknown result: we will be able to establish that at least the above predicate will hold for it... *)
  Lemma wp_estoreid_success_unknown E pc_p pc_b pc_e pc_a pc_a' pc_v lw rd rs otype any :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ rs ↦ᵣ LWInt otype
        ∗ rd ↦ᵣ any
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          (pc_a, pc_v) ↦ₐ lw
          ∗ rs ↦ᵣ LWInt otype
          ∗ ((⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ ∃ (I : EIdentity), ∃ (tid : TIndex),
                  rd ↦ᵣ (LWInt I)
                  ∗ (enclave_all tid I)
                  ∗ ⌜ has_seal otype tid ⌝
             )
             ∨
               (⌜ retv = FailedV ⌝
                ∗ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
                ∗ rd ↦ᵣ any
               )
            )

    }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' φ) "(Hpc & Hpca & Hrs & Hrd) Hφ".
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
