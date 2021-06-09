From cap_machine Require Export rules_Jnz rules_binary_base.
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

  Lemma step_Jnz Ep K pc_p pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = Jnz dst src ->
    isCorrectPC (WCap (pc_p, pc_b, pc_e, pc_a)) →
    regs !! PC = Some (WCap (pc_p, pc_b, pc_e, pc_a)) →
    regs_of (Jnz dst src) ⊆ dom _ regs →

    nclose specN ⊆ Ep →

    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ ▷ pc_a ↣ₐ w ∗ ▷ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⌜ Jnz_spec regs dst src regs' retv ⌝ ∗
                            ⤇ fill K (of_val retv) ∗ pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs', k ↣ᵣ y. 
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hnclose) "(Hinv & Hj & >Hpc_a & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    have HPC' := regs_lookup_eq _ _ _ HPC.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a. 
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri src) as [wsrc [H'src Hsrc]]. by set_solver+.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    assert (Hstep':=Hstep). 
    destruct (nonZero wsrc) eqn:Hnz; pose proof Hnz as H'nz;
      cbn in Hstep; rewrite /RegLocate Hsrc Hdst Hnz in Hstep.
    { inv Hstep.
      iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hown Hmap") as "[Hr Hmap]"; eauto.
      iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hr Hj") as "[Hown Hj]".
      iExists NextIV,_. iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto. prim_step_from_exec. }
      iPureIntro. econstructor 3; eauto. }
    
    destruct (incrementPC regs) eqn:HX; pose proof HX as H'X; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=σm) in HX.
      eapply updatePC_fail_incl with (m':=σm) in HX; eauto. simplify_pair_eq.
      inv Hstep. iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
      iExists FailedV,_. iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto. 
        prim_step_from_exec. }
      iPureIntro; econstructor; eauto. }
    
    destruct (incrementPC_success_updatePC _ σm _ HX)
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=σm) in HuPC; eauto. simplify_pair_eq.
    iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hown Hmap") as "[Hown Hmap]"; eauto.
    iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto. prim_step_from_exec. }
    iExists NextIV,_. iFrame. iPureIntro. econstructor 2; eauto.
  Qed.
  

  Lemma step_jnz_success_next E K r1 r2 pc_p pc_b pc_e pc_a pc_a' w w1 :
    decodeInstrW w = Jnz r1 r2 →
    isCorrectPC (WCap (pc_p,pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap (pc_p,pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ w1
             ∗ ▷ r2 ↣ᵣ WInt 0%Z
    ={E}=∗ ⤇ fill K (Instr NextI)
         ∗ PC ↣ᵣ WCap (pc_p,pc_b,pc_e,pc_a')
         ∗ pc_a ↣ₐ w
         ∗ r1 ↣ᵣ w1
         ∗ r2 ↣ᵣ WInt 0%Z.
  Proof. 
    iIntros (Hinstr Hvpc Hpc_a' Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1 & >Hr2)".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_Jnz with "[$Hmap $Hown $Hj $Hpc_a]") as (retv regs' Hspec) "[Hj [Hpc_a Hmap] ]"; eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    
    destruct Hspec as [ | | ];eauto. 
    { incrementPC_inv;[|rewrite lookup_insert;eauto]. congruence. }
    { iFrame. incrementPC_inv. rewrite insert_insert. 
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto. rewrite lookup_insert in H7; simplify_eq. by iFrame. }
    { rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert in H5. simplify_eq. }
  Qed.

  Lemma step_jnz_success_jmp E K r1 r2 pc_p pc_b pc_e pc_a w w1 w2 :
    decodeInstrW w = Jnz r1 r2 →
    isCorrectPC (WCap (pc_p,pc_b,pc_e,pc_a)) →
    w2 ≠ WInt 0%Z →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap (pc_p,pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ w1
             ∗ ▷ r2 ↣ᵣ w2
    ={E}=∗ ⤇ fill K (Instr NextI)
         ∗ PC ↣ᵣ updatePcPerm w1
         ∗ pc_a ↣ₐ w
         ∗ r1 ↣ᵣ w1
         ∗ r2 ↣ᵣ w2.
  Proof.
    iIntros (Hinstr Hvpc Hne Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1 & >Hr2)".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_Jnz with "[$Hmap $Hown $Hj $Hpc_a]") as (retv regs' Hspec) "[Hj [Hpc_a Hmap] ]"; eauto; simplify_map_eq; eauto.
      by unfold regs_of; rewrite !dom_insert; set_solver+.
    
    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }
    
   destruct Hspec as [ | | ].
   { exfalso. rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert in H6. simplify_eq. congruence. }
   { exfalso. rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert in H6. simplify_eq. congruence. }
   { rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert in H6.
     rewrite lookup_insert_ne// lookup_insert in H7. 
     simplify_eq. rewrite insert_insert. iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto. by iFrame. 
   } 
  Qed.


End cap_lang_spec_rules. 
