From cap_machine Require Export rules_binary_base rules_Mov.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.


Section cap_lang_spec_rules. 
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.
      
  
  Lemma step_Mov Ep K pc_p pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = Mov dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of (Mov dst src) ⊆ dom _ regs →

    nclose specN ⊆ Ep →
    
    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⤇ fill K (of_val retv) ∗ ⌜ Mov_spec regs dst src regs' retv ⌝ ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
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
    
    assert (exists w, word_of_argument regs src = Some w) as [wsrc Hwsrc].
    { destruct src as [| r0]; eauto; cbn.
      destruct (Hri r0) as [? [? ?]]. set_solver+. eauto. }
    
    pose proof Hwsrc as Hwsrc'. eapply word_of_argument_Some_inv' in Hwsrc; eauto.

    assert (exec_opt (Mov dst src) (σr, σm) = updatePC (update_reg (σr, σm) dst wsrc)) as HH.
    { destruct Hwsrc as [ [? [? ?] ] | [? (? & ? & Hr') ] ]; simplify_eq; eauto.
      cbn. by rewrite /= Hr'. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := wsrc ]> regs)) as [regs''|] eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=σm) in Hregs'.
      eapply updatePC_fail_incl with (m':=σm) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      rewrite Hregs' in Hstep. simplify_pair_eq.
      iExists FailedV,_. iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
      iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
        prim_step_from_exec.
      }
      iModIntro. iPureIntro. econstructor; eauto.
    }

    eapply (incrementPC_success_updatePC _ σm) in H'regs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in Hstep. simplify_pair_eq. iFrame.

    iMod ((regspec_heap_update_inSepM _ _ _ dst wsrc) with "Hown Hmap") as "[Hown Hmap]"; eauto.
    iMod ((regspec_heap_update_inSepM _ _ _ PC (WCap p' g' b' a'')) with "Hown Hmap") as "[Hown Hmap]"; eauto.
    iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
    iExists NextIV,_. iFrame.
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
      prim_step_from_exec. 
    }
    iModIntro. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_move_success_reg_fromPC E K pc_p pc_b pc_e pc_a pc_a' w r1 wr1 :
    decodeInstrW w = Mov r1 (inr PC) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

     
    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ wr1
    ={E}=∗
         ⤇ fill K (of_val NextIV)
         ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
         ∗ pc_a ↣ₐ w
         ∗ r1 ↣ᵣ WCap pc_p pc_b pc_e pc_a.
  Proof. 
    iIntros (Hinstr Hvpc Hpca' Hclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1)".
    iDestruct (rules_binary_base.map_of_regs_2  with "HPC Hr1") as "[Hmap %]".
    iMod (step_Mov with "[$Hmap $Hpc_a $Hj $Hown]") as (retv regs') "(Hj & #Hspec & Hpc_a & Hmap)"; eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iDestruct "Hspec" as %Hspec.
    
    destruct Hspec as [|].
    { (* Success *)
      iFrame. incrementPC_inv; rewrite lookup_insert_ne// lookup_insert in H4. 
      rewrite /= lookup_insert in H3. simplify_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (rules_binary_base.regs_of_map_2 with "Hmap") as "(?&?)"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; [|rewrite lookup_insert_ne// lookup_insert;eauto]. congruence. }
  Qed.

  Lemma step_move_success_reg E K pc_p pc_b pc_e pc_a pc_a' w r1 wr1 rv wrv :
    decodeInstrW w = Mov r1 (inr rv) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ wr1
             ∗ ▷ rv ↣ᵣ wrv
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ pc_a ↣ₐ w
        ∗ r1 ↣ᵣ wrv
        ∗ rv ↣ᵣ wrv. 
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1 & >Hrv)".
    iDestruct (rules_binary_base.map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
    iMod (step_Mov with "[$Hmap $Hpc_a $Hj $Hown]") as (retv regs') "(Hj & #Hspec & Hpc_a & Hmap)"; eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iFrame. incrementPC_inv. rewrite lookup_insert_ne// lookup_insert in H6. 
      rewrite /= lookup_insert_ne// lookup_insert_ne// lookup_insert in H5. simplify_eq.
      rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ PC r1) // insert_insert.
      iDestruct (rules_binary_base.regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert;eauto]. congruence. }
  Qed.

   Lemma step_move_success_z E K pc_p pc_b pc_e pc_a pc_a' w r1 wr1 z :
    decodeInstrW w = Mov r1 (inl z) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ wr1
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ pc_a ↣ₐ w
        ∗ r1 ↣ᵣ WInt z.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1)".
    iDestruct (rules_binary_base.map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iMod (step_Mov with "[$Hmap $Hpc_a $Hj $Hown]") as (retv regs') "(Hj & #Hspec & Hpc_a & Hmap)"; eauto; simplify_map_eq; eauto.
      by unfold regs_of; rewrite !dom_insert; set_solver+. iDestruct "Hspec" as %Hspec.
    
    destruct Hspec as [|].
    { (* Success *)
      iFrame. simpl in *; incrementPC_inv; simplify_map_eq_alt.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (rules_binary_base.regs_of_map_2 with "Hmap") as "(?&?)"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; [|rewrite lookup_insert_ne// lookup_insert;eauto]. congruence. }
  Qed.
  

End cap_lang_spec_rules. 
