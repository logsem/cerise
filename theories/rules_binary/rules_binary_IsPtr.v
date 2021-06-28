From cap_machine Require Export rules_binary_base rules_IsPtr.
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

  Lemma step_IsPtr Ep K pc_p pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = IsPtr dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of (IsPtr dst src) ⊆ dom _ regs →

    nclose specN ⊆ Ep →

    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⤇ fill K (of_val retv) ∗ ⌜ IsPtr_spec regs dst src regs' retv ⌝ ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hcls) "(#Hinv & Hj & Hpc_a & Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    have Hx := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.

    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.
    pose proof (Hstep' := Hstep). unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (Hri src) as [wsrc [Hwsrc Hwsrc']]; [set_solver+|]. simpl in Hwsrc'.

    assert (exec_opt (IsPtr dst src) (σr, σm) = updatePC (update_reg (σr, σm) dst (WInt (if is_cap wsrc then 1%Z else 0%Z)))) as HH.
    {  rewrite /= Hwsrc'. unfold is_cap; destruct wsrc; auto. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := WInt (if is_cap wsrc then 1%Z else 0%Z) ]> regs)) as [regs''|] eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=σm) in Hregs'.
      eapply updatePC_fail_incl with (m':=σm) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      rewrite Hregs' in Hstep. inv Hstep.
      iExists FailedV,_. iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
      iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
        simpl. prim_step_from_exec.
      }
      iModIntro. iPureIntro. econstructor; eauto.
    }

    eapply (incrementPC_success_updatePC _ σm) in H'regs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.

    simplify_pair_eq.
    iMod ((regspec_heap_update_inSepM _ _ _ dst (WInt (if is_cap wsrc then 1%Z else 0%Z))) with "Hown Hmap") as "[Hown Hmap]"; eauto.
    iMod ((regspec_heap_update_inSepM _ _ _ PC (WCap p' g' b' a'')) with "Hown Hmap") as "[Hown Hmap]"; eauto.
    iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
    iExists NextIV,_. iFrame.
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
      prim_step_from_exec.
    }
    iModIntro. iPureIntro. econstructor; eauto.
  Qed.

End cap_lang_spec_rules.
