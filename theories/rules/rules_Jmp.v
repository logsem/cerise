From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr. 
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma wp_jmp_success E pc_p pc_g pc_b pc_e pc_a w r w' pc_p':
    cap_lang.decode w = Jmp r →
    PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
         ∗ ▷ pc_a ↦ₐ[pc_p'] w
         ∗ ▷ r ↦ᵣ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ updatePcPerm w'
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ r ↦ᵣ w' }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto.
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr0 Hr") as %Hr_r0.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    rewrite /update_reg /= in Hstep. simplify_pair_eq. cbn.
    iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]". iFrame.
    iApply "Hφ". iFrame. rewrite /RegLocate Hr_r0. eauto.
  Qed.

  Lemma wp_jmp_successPC E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Jmp PC →
    PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
         ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ updatePcPerm (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))
           ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; cbn.
    iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto.
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %Hr_PC.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    rewrite /update_reg /= in Hstep. simplify_pair_eq. cbn.
    rewrite /RegLocate Hr_PC.
    iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]". iFrame.
    iApply "Hφ". by iFrame.
  Qed.

End cap_lang_rules.
