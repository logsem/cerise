From cap_machine Require Export rules_Jmp rules_binary_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.


Section cap_lang_spec_rules. 
  Context `{cfgSG Σ, MachineParameters, invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma step_jmp_success E K pc_p pc_b pc_e pc_a w r w' :
    decodeInstrW w = Jmp r →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r ↣ᵣ w'
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ updatePcPerm w'
        ∗ pc_a ↣ₐ w
        ∗ r ↣ᵣ w'. 
  Proof.
    iIntros (Hinstr Hvpc Hnclose) "(Hinv & Hj & >HPC & >Hpc_a & >Hr)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (@spec_heap_valid with "[$Hown $Hpc_a]") as %?; auto.
    iDestruct (@spec_regs_valid with "[$Hown $HPC]") as %?.
    iDestruct (@spec_regs_valid with "[$Hown $Hr]") as %Hr_r0.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.
    pose proof (Hstep' := Hstep). rewrite /exec /= in Hstep.

    rewrite /update_reg /= Hr_r0 /= in Hstep. simplify_pair_eq.
    simplify_eq.
    iMod (@regspec_mapsto_update with "Hown HPC") as "[Hown HPC]". 
    iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
    iFrame.
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto. 
      exists [];eapply step_atomic with (t1:=[]) (t2:=[]);eauto. 
      econstructor;eauto;constructor. simpl.
      eapply step_exec_instr with (c:=(NextI, (<[PC:=updatePcPerm w']> σr, σm)));
        [simplify_map_eq..|];eauto.
    }
    done. 
  Qed.

  Lemma wp_jmp_successPC E K pc_p pc_b pc_e pc_a w :
    decodeInstrW w = Jmp PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
    ={E}=∗  ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ updatePcPerm (WCap pc_p pc_b pc_e pc_a)
        ∗ pc_a ↣ₐ w.
  Proof.
    iIntros (Hinstr Hvpc Hnclose) "(Hinv & Hj & >HPC & >Hpc_a)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (@spec_heap_valid with "[$Hown $Hpc_a]") as %?; auto.
    iDestruct (@spec_regs_valid with "[$Hown $HPC]") as %Hr_PC.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.
    pose proof (Hstep' := Hstep). rewrite /exec /= in Hstep.

    rewrite /update_reg /= Hr_PC /= in Hstep. simplify_pair_eq.
    simplify_eq.
    iMod (@regspec_mapsto_update with "Hown HPC") as "[Hown HPC]". 
    iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
    iFrame.
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto. 
      exists [];eapply step_atomic with (t1:=[]) (t2:=[]);eauto. 
      econstructor;eauto;constructor. simpl.
      eapply step_exec_instr with (c:=(NextI, (<[PC:=updatePcPerm (WCap pc_p pc_b pc_e pc_a)]> σr, σm)));
        [simplify_map_eq..|];eauto.
    }
    done. 
  Qed.

End cap_lang_spec_rules. 
