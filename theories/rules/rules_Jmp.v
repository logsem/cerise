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
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Lemma wp_jmp_success E pc_p pc_b pc_e pc_a pc_v pca_v lw r lw' :
    decodeInstrWL lw = Jmp r →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
         ∗ ▷ (pc_a, pca_v) ↦ₐ lw
         ∗ ▷ r ↦ᵣ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ updatePcPermL lw'
           ∗ (pc_a, pca_v) ↦ₐ lw
           ∗ r ↦ᵣ lw' }}}.
  Proof.
    iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr0 & Hm & %HLinv)"; simpl in HLinv.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?; auto.
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr0 Hr") as %Hr_r0.
    iDestruct (@gen_heap_valid with "Hr0 Hr") as %Hr_r0'.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    2: eapply state_phys_log_reg_get_word in H3; eauto.
    2: eapply state_phys_log_mem_get_word in H2; eauto.
    unfold exec, exec_opt in Hstep; cbn in *.
    eapply state_phys_log_reg_get_word in Hr_r0; eauto.
    rewrite Hr_r0 /= in Hstep; simplify_pair_eq.

    iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
    iSplitR "Hφ HPC Hpc_a Hr" ; [|by iApply "Hφ" ; iFrame].
    iExists _, lm, cur_map; iFrame; eauto; cbn.
    iPureIntro; econstructor; eauto
    ; [| by destruct HLinv as [_ ?]]
    ; destruct HLinv as [[Hstrips Hcur_reg] HmemInv]
    ; cbn in *.
    rewrite -updatePcPermL_spec.
    apply lreg_insert_respects_corresponds; [split ; auto|].
    apply is_cur_updatePcPermL.
    eapply lreg_read_iscur; eauto; split ; eauto.
  Qed.


  Lemma wp_jmp_successPC E pc_p pc_b pc_e pc_a pc_v pca_v lw :
    decodeInstrWL lw = Jmp PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ lw }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPermL (LCap pc_p pc_b pc_e pc_a pc_v)
            ∗ (pc_a, pca_v) ↦ₐ lw }}}.
  Proof.
    iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr0 & Hm & %HLinv)"; simpl in HLinv.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?; auto.
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %Hr_PC.
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %Hr_PC'.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    2: eapply state_phys_log_reg_get_word in Hr_PC; eauto.
    2: eapply state_phys_log_mem_get_word in H2; eauto.
    unfold exec, exec_opt in Hstep; cbn in *.
    eapply state_phys_log_reg_get_word in Hr_PC; eauto.
    rewrite Hr_PC /= in Hstep; simplify_pair_eq.

    iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
    iSplitR "Hφ HPC Hpc_a" ; [|by iApply "Hφ" ; iFrame].
    iExists _, lm, cur_map; iFrame; eauto; cbn.
    iPureIntro; econstructor; eauto
    ; [| by destruct HLinv as [_ ?]]
    ; destruct HLinv as [[Hstrips Hcur_reg] HmemInv]
    ; cbn in *.
    replace (match pc_p with
              | E => WCap RX pc_b pc_e pc_a
              | _ => WCap pc_p pc_b pc_e pc_a
              end)
      with (lword_get_word (match pc_p with
                            | E => LCap RX pc_b pc_e pc_a pc_v
                            | _ => LCap pc_p pc_b pc_e pc_a pc_v
                            end))
           by (destruct pc_p ; auto).
    apply lreg_insert_respects_corresponds ; [split ; auto|].
    destruct pc_p; (try by eapply lreg_read_iscur; eauto; split ; eauto).
    eapply is_cur_word_cap_change with (p':= machine_base.E) (a' := pc_a)
    ; by eapply lreg_read_iscur; eauto; split ; eauto.
  Qed.

End cap_lang_rules.
