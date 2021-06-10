From cap_machine Require Export rules_binary_base rules_Store.
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

  Ltac iFailStep_alt fail_type :=
    iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
    iMod ("Hclose" with "[Hown]") as "_";
    [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|];
    iExists (FailedV),_,_; iFrame;iModIntro;iFailCore fail_type.

  Lemma step_store Ep K
     pc_p pc_b pc_e pc_a
     r1 (r2 : Z + RegName) w mem regs :
   decodeInstrW w = Store r1 r2 →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
   regs_of (Store r1 r2) ⊆ dom _ regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true r1 regs mem →
   nclose specN ⊆ Ep →

   spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ (▷ [∗ map] a↦w ∈ mem, a ↣ₐ w) ∗ (▷ [∗ map] k↦y ∈ regs, k ↣ᵣ y)
   ={Ep}=∗ ∃ retv regs' mem', ⌜ Store_spec regs r1 r2 regs' mem mem' retv⌝ ∗
                           ⤇ fill K (of_val retv) ∗ ([∗ map] a↦w ∈ mem', a ↣ₐ w) ∗ [∗ map] k↦y ∈ regs', k ↣ᵣ y. 
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore Hnclose) "(Hinv & Hj & >Hmem & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    feed destruct (Hri r1) as [r1v [Hr'1 Hr1]]. by set_solver+.
    pose proof (regs_lookup_eq _ _ _ Hr'1) as Hr''1.
    iDestruct (memspec_heap_valid_inSepM _ _ _ _ pc_a with "Hown Hmem") as %Hma; eauto.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.    
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.

     simpl in Hr1, Hma. option_locate_mr σm σr.
     assert (Hstep':=Hstep). cbn in Hstep. rewrite Hσrr1 in Hstep.
     
     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct r1v as  [| p b e a ] eqn:Hr1v.
     { (* Failure: r1 is not a capability *)
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
           by (destruct r2; inversion Hstep; auto).
       iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
       iMod ("Hclose" with "[Hown]") as "_".
       { iNext. iExists _,_;iFrame.
         iPureIntro. eapply rtc_r;eauto. prim_step_from_exec. }
       iExists (FailedV),_,_; iFrame. iModIntro.
       iPureIntro. econstructor; eauto. econstructor; eauto. 
     }
     
     destruct (writeAllowed p && withinBounds b e a) eqn:HWA.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
        assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
         by (destruct r2; inversion Hstep; auto).
       apply andb_false_iff in HWA.
       iFailStep_alt Store_fail_bounds.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).

     destruct (word_of_argument regs r2) as [ storev | ] eqn:HSV.
     2: {
       destruct r2 as [z | r2].
       - cbn in HSV; inversion HSV.
       - destruct (Hri r2) as [r0v [Hr0 _] ]. by set_solver+.
         cbn in HSV. rewrite Hr0 in HSV. inversion HSV.
     }
     assert (word_of_argument σr r2 = Some(storev)) as HSVr.
     { destruct r2; cbn in HSV. inversion HSV; simpl in H3;auto;by rewrite H3.
       destruct (Hri r) as [r0v [Hregs0 Hr0] ].  by set_solver+.
       rewrite -Hr0 in Hregs0; rewrite Hregs0 in HSV. exact HSV.
     }

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_store_implies_storev r1 r2 mem regs p b e a storev) as (oldv & Hmema); auto.

     (* Given this, prove that a is also present in the memory itself *)
     iDestruct (memspec_v_implies_m_v mem (σr,σm) _ b e a oldv with "Hmem Hown" ) as %Hma ; auto.

     (* Regardless of whether we increment the PC, the memory will change: destruct on the PC later *)
     assert (updatePC (update_mem (σr, σm) a storev) = (c, σ2)) as HH.
      { destruct r2.
       - cbv in HSVr; inversion HSVr; subst storev. done.
       - destruct (σr !r! r) eqn:Hr0.
         * destruct (Hri r) as [r0v [Hregs01 Hr01] ]. by set_solver+.
           assert(is_Some( σr !! r )) as Hrr0. by exists r0v.
           pose proof (regs_lookup_inl_eq σr r z Hrr0 Hr0) as Hr0'.
           simpl in HSVr; rewrite Hr0' in HSVr.
           inversion HSVr; subst storev. done.
         * epose proof (regs_lookup_inr_eq σr r _ _ _ _ Hr0) as Hr0'.
           simpl in HSVr; rewrite Hr0' in HSVr; inversion HSVr. auto. 
      }
      iMod ((memspec_heap_update_inSepM _ _ _ a storev) with "Hown Hmem") as "[Hown Hmem]"; eauto.
      
      destruct (incrementPC regs ) as [ regs' |] eqn:Hregs'.
      2: { (* Failure: the PC could not be incremented correctly *)
        assert (incrementPC σr = None).
        { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. }
        rewrite incrementPC_fail_updatePC /= in HH; auto.
        inversion HH. subst.
        iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
          iMod ("Hclose" with "[Hown]") as "_";
          [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|];
          iExists (FailedV),_,_; iFrame;iModIntro. 
        iPureIntro. eapply Store_spec_failure_incr;eauto.
        - split;eauto. 
        - constructor. auto. 
      }
      
     (* Success *)
      clear Hstep. rewrite /update_mem /= in HH.
      eapply (incrementPC_success_updatePC _ (<[a:=storev]> σm)) in Hregs'
        as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & HuPC & ->).
      eapply (updatePC_success_incl _ (<[a:=storev]> σm)) in HuPC. 2: by eauto.
      rewrite HuPC in HH; clear HuPC; inversion HH; clear HH; subst c σ2. cbn.
      iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hown Hmap") as "[Hown Hmap]"; eauto.
      iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
      iExists NextIV,_,_. iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
        prim_step_from_exec. }
      
      iPureIntro. eapply Store_spec_success; eauto.
        * split; auto. exact Hr'1. all: auto.
        * unfold incrementPC. rewrite a_pc1 HPC''.  auto. 
  Qed.

  Lemma step_store_success_reg E K pc_p pc_b pc_e pc_a pc_a' w dst src w'
         p b e a w'' :
      decodeInstrW w = Store dst (inr src) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds b e a = true →
     nclose specN ⊆ E →
     
     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗  ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ src ↣ᵣ w''
              ∗ ▷ dst ↣ᵣ WCap p b e a
              ∗ ▷ a ↣ₐ w'
     ={E}=∗ ⤇ fill K (Instr NextI)
         ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
         ∗ pc_a ↣ₐ w
         ∗ src ↣ᵣ w''
         ∗ dst ↣ᵣ WCap p b e a
         ∗ a ↣ₐ w''. 
  Proof.
    iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] Hnclose)
            "(Hown & Hj & >HPC & >Hi & >Hsrc & >Hdst & >Hsrca)".
    iDestruct (rules_binary_base.map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.
    
    iMod (step_store _ _ pc_p with "[$Hown $Hj $Hmap $Hmem]") as (retv regs' mem' Hspec) "(Hj & Hmem & Hregs)";
      eauto; simplify_map_eq_alt; try rewrite lookup_insert; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert;eauto. }

    destruct Hspec. 
     { (* Success *)
       destruct H7 as [Hrr2 _]. simpl in *. simplify_map_eq_alt. simplify_map_eq. 
       rewrite insert_commute // insert_insert.
       iDestruct (rules_binary_base.memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq_alt.
       rewrite insert_insert.
       iDestruct (rules_binary_base.regs_of_map_3 with "[$Hregs]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. done. }
     { (* Failure (contradiction) *)
       destruct H7; simpl in *; simplify_map_eq_alt.
       destruct o. all: try congruence.
     }
     { (* Failure (contradiction) *)
       destruct H7,H10; simpl in *; simplify_map_eq_alt. simplify_map_eq.
       incrementPC_inv;[|rewrite lookup_insert;eauto]. congruence. 
     }
    Qed.

  Lemma step_store_success_z E K pc_p pc_b pc_e pc_a pc_a' w dst z w'
         p b e a :
     decodeInstrW w = Store dst (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds b e a = true →
     nclose specN ⊆ E →

     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ dst ↣ᵣ WCap p b e a
              ∗ ▷ a ↣ₐ w'
     ={E}=∗ ⤇ fill K (Instr NextI)
         ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
         ∗ pc_a ↣ₐ w
         ∗ dst ↣ᵣ WCap p b e a
         ∗ a ↣ₐ WInt z.
  Proof.
    iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] Hnclose)
            "(Hown & Hj & >HPC & >Hi & >Hdst & >Hsrca)".
    iDestruct (rules_binary_base.map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.
    
    iMod (step_store _ _ pc_p with "[$Hown $Hj $Hmap $Hmem]") as (retv regs' mem' Hspec) "(Hj & Hmem & Hregs)";
      eauto; simplify_map_eq_alt; try rewrite lookup_insert; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      rewrite lookup_insert_ne// lookup_insert. eauto. }
    
    destruct Hspec. 
     { (* Success *)
       iFrame. 
       destruct H5 as [Hrr2 _]. simplify_map_eq_alt.
       rewrite insert_commute // insert_insert.
       iDestruct (rules_binary_base.memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv. simpl in *. 
       simplify_map_eq_alt.
       rewrite insert_insert.
       iDestruct (rules_binary_base.regs_of_map_2 with "[$Hregs]") as "[HPC Hdst]"; eauto. by iFrame. }
     { (* Failure (contradiction) *)
       destruct H5; simplify_map_eq_alt. 
       destruct o. all: try congruence.
     }
     { (* Failure (contradiction) *)
       destruct H5,H8; simplify_map_eq; eauto. incrementPC_inv;[|rewrite lookup_insert;eauto]. 
       congruence. 
     }
  Qed.
  
  
End cap_lang_spec_rules. 
