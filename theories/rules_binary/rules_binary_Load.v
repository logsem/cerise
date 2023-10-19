From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_Load rules_binary_base.


Section cap_lang_spec_rules. 
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma step_Load Ep K pc_p pc_b pc_e pc_a r1 r2 w mem regs :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of (Load r1 r2) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_map_or_true r2 regs mem →

    nclose specN ⊆ Ep →
    
    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ (▷ [∗ map] a↦w ∈ mem, a ↣ₐ w) ∗ (▷ [∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⤇ fill K (of_val retv) ∗ ⌜ Load_spec regs r1 r2 regs' mem retv ⌝ ∗ ([∗ map] a↦w ∈ mem, a ↣ₐ w)∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hnclose) "(#Hinv & Hj & >Hmem & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.

    (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     odestruct (Hri r2) as [r2v [Hr'2 Hr2]]. by set_solver+.
     odestruct (Hri r1) as [r1v [Hr'1 _]]. by set_solver+. clear Hri.
     (* Derive the PC in memory *)
     iDestruct (memspec_heap_valid_inSepM _ _ _ _ pc_a with "Hown Hmem") as %Hma; eauto.

     specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
     eapply step_exec_inv in Hstep; eauto. simpl in H1,Hr2,Hma.
     pose proof (Hstep' := Hstep).
     rewrite /exec /= Hr2 /= in Hstep.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct (is_cap r2v) eqn:Hr2v.
     2:{ (* Failure: r2 is not a capability *)
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
       {
         unfold is_cap in Hr2v.
         destruct_word r2v; try by simplify_pair_eq.
       }
       iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
       iMod ("Hclose" with "[Hown]") as "_".
       { iNext. iExists _,_;iFrame.
         iPureIntro. eapply rtc_r;eauto. prim_step_from_exec. }
       iExists (FailedV),_; iFrame. iModIntro. iFailCore Load_fail_const.
     }
     destruct r2v as [ | [p b e a | ] | ]; try inversion Hr2v. clear Hr2v.

     destruct (readAllowed p && withinBounds b e a) eqn:HRA.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       apply andb_false_iff in HRA.
       iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
       iMod ("Hclose" with "[Hown]") as "_".
       { iNext. iExists _,_;iFrame.
         iPureIntro. eapply rtc_r;eauto. prim_step_from_exec. }
       iExists (FailedV),_; iFrame. iModIntro. iFailCore Load_fail_bounds. 
     }
     apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_load_implies_loadv r2 mem regs p b e a) as (loadv & Hmema); auto.

     iDestruct (memspec_v_implies_m_v mem (σr,σm) _ b e a loadv with "Hmem Hown" ) as %Hma' ; auto.

     rewrite Hma' /= in Hstep.
     destruct (incrementPC (<[ r1 := loadv ]> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC (<[ r1 := loadv]> σr) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         by rewrite lookup_insert_is_Some'; eauto.
         by apply insert_mono; eauto. }

       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
       (* iMod ((regspec_heap_update_inSepM _ _ _ r1 loadv) with "Hown Hmap") as "[Hown Hmap]"; eauto. *)
       iMod ("Hclose" with "[Hown]") as "_".
       { iNext. iExists _,_;iFrame.
         iPureIntro. eapply rtc_r;eauto. clear Hmema.
         prim_step_from_exec. }
       iExists (FailedV),_; iFrame. iModIntro. iFailCore Load_fail_invalid_PC. 
     }

     (* Success *)
     rewrite /update_reg /= in Hstep.
     eapply (incrementPC_success_updatePC _ σm) in Hregs'
       as (p1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((regspec_heap_update_inSepM _ _ _ r1 loadv) with "Hown Hmap") as "[Hown Hmap]"; eauto.
     iMod ((regspec_heap_update_inSepM _ _ _ PC (WCap p1 b1 e1 a_pc1)) with "Hown Hmap") as "[Hown Hmap]"; eauto.
     iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
     iExists NextIV,_. iFrame.
     iMod ("Hclose" with "[Hown]") as "_".
     { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
      prim_step_from_exec. }
     iModIntro. iPureIntro. eapply Load_spec_success; auto.
    * split; auto.
      exact Hr'2.
      auto.
    * exact Hmema.
    * unfold incrementPC. by rewrite HPC'' Ha_pc'.
      Unshelve. all: auto.
  Qed. 

  Lemma step_load_success_same E K r1 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ WCap p b e a
             ∗ (if (a =? pc_a)%a then emp else ▷ a ↣ₐ w')
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ r1 ↣ᵣ (if (a =? pc_a)%a then w else w')
        ∗ pc_a ↣ₐ w
        ∗ (if (a =? pc_a)%a then emp else a ↣ₐ w'). 
  Proof. 
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hnclose)
            "(Hown & Hj & >HPC & >Hi & >Hr1 & Hr1a)".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater _ _ _ _ (λ a w, a ↣ₐ w)%I with "Hi Hr1a") as (mem) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %Hmem.

    iMod (step_Load with "[$Hown $Hj $Hmap $Hmem]") as (retv regs') "(Hj & #Hspec & Hmem & Hmap)"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. rewrite lookup_insert_ne// lookup_insert;eauto. }
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       destruct H2 as [Hrr2 _].
       rewrite lookup_insert_ne// lookup_insert in Hrr2. simplify_eq.
       incrementPC_inv. rewrite lookup_insert_ne// lookup_insert in H2. simplify_eq.
       iDestruct (memMap_resource_2gen_d with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem; iSplitL; auto. }
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. rewrite Hloadv. by iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma step_load_success_same_alt E K r1 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ WCap p b e a
             ∗ ▷ a ↣ₐ w'
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ r1 ↣ᵣ w'
        ∗ pc_a ↣ₐ w
        ∗ a ↣ₐ w'. 
  Proof. 
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1 & >Ha)".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iIntros (->%finz_to_z_eq). iDestruct (memspec_mapsto_valid_2 with "Ha Hpc_a") as %Hneq. done. }
    iMod (step_load_success_same with "[$HPC $Hpc_a $Hr1 $Hown $Hj Ha]") as "(?&?&?&?&?)";eauto;try rewrite Hfalse;by iFrame. 
  Qed.

  Lemma step_load_success E K r1 r2 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ w''  
             ∗ ▷ r2 ↣ᵣ WCap p b e a
             ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↣ₐ w')
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ r1 ↣ᵣ (if (eqb_addr a pc_a) then w else w')
        ∗ pc_a ↣ₐ w
        ∗ r2 ↣ᵣ WCap p b e a
        ∗ (if (eqb_addr a pc_a) then emp else a ↣ₐ w'). 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hnclose)
            "(Hown & Hj & >HPC & >Hi & >Hr1 & >Hr2 & Hr2a)".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_clater _ _ _ _ (λ a w, a ↣ₐ w)%I with "Hi Hr2a") as (mem) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %Hmem.

    iMod (step_Load with "[$Hown $Hj $Hmap $Hmem]") as (retv regs') "(Hj & #Hspec & Hmem & Hmap)"; eauto.
    { rewrite lookup_insert;eauto. }
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert. eauto. }
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H4 as [Hrr2 _]. simplify_map_eq_alt.
       iDestruct (memMap_resource_2gen_d with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H5) as Hloadv; eauto.
       simplify_map_eq_alt.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       by iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq_alt.
       destruct o;congruence. 
       incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert;eauto]. congruence. }
  Qed.

  Lemma step_load_success_alt E K r1 r2 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ w''  
             ∗ ▷ r2 ↣ᵣ WCap p b e a
             ∗ ▷ a ↣ₐ w'
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ r1 ↣ᵣ w'
        ∗ pc_a ↣ₐ w
        ∗ r2 ↣ᵣ WCap p b e a
        ∗ a ↣ₐ w'. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hnclose)
            "(Hown & Hj & >HPC & >Hi & >Hr1 & >Hr2 & >Hr2a)".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iIntros (->%finz_to_z_eq). iDestruct (memspec_mapsto_valid_2 with "Hr2a Hi") as %Hneq. done. }
    iMod (step_load_success with "[$Hown $Hj $HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;by iFrame. 
  Qed.
  
End cap_lang_spec_rules.
