From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_Lea rules_binary_base.


Section cap_lang_spec_rules. 
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma step_lea Ep K pc_p pc_b pc_e pc_a r1 w arg (regs: Reg) :
     decodeInstrW w = Lea r1 arg →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
     regs_of (Lea r1 arg) ⊆ dom _ regs →

     nclose specN ⊆ Ep →

     spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ ▷ pc_a ↣ₐ w ∗ ▷ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
     ={Ep}=∗ ∃ retv regs', ⤇ fill K (of_val retv) ∗ ⌜ Lea_spec regs r1 arg regs' retv ⌝ ∗ pc_a ↣ₐ w
                             ∗ [∗ map] k↦y ∈ regs', k ↣ᵣ y.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hnclose) "(Hinv & Hj & >Hpc_a & >Hmap)".
     iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
     iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
     iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     iDestruct (@spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a; auto.
     iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
     specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
     eapply step_exec_inv in Hstep; eauto.
     pose proof (Hstep' := Hstep). unfold exec in Hstep.

     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.

     feed destruct (Hri r1) as [r1v [Hr'1 Hr1]]. by set_solver+.
     cbn in Hstep.
     rewrite Hr1 /= in Hstep.

     destruct (z_of_argument regs arg) as [ argz |] eqn:Harg;
       pose proof Harg as Harg'; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Harg, Hstep. destruct arg as [| r0]; [ congruence |].
       feed destruct (Hri r0) as [r0v [Hr'0 Hr0]].
       { unfold regs_of_argument. set_solver+. }
       rewrite Hr0 Hr'0 in Harg Hstep.
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
       { destruct_word r0v; cbn in Hstep; try congruence; by simplify_pair_eq. }
       iFailStep Lea_fail_rv_nonconst. }
     apply (z_of_arg_mono _ σr) in Harg; auto. rewrite Harg in Hstep; cbn in Hstep.

     destruct (is_mutable_range r1v) eqn:Hr1v.
     2: { (* Failure: r1v is not of the right type *)
       unfold is_mutable_range in Hr1v.
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
       { destruct r1v as [ | [p b e a | ] | ]; try by inversion Hr1v.
         all: try by simplify_pair_eq.
         destruct p; try congruence.
         simplify_pair_eq; auto. }
       iFailStep Lea_fail_allowed. }

     (* Now the proof splits depending on the type of value in r1v *)
     destruct r1v as [ | [p b e a | p b e a] | ].
     1,4: inversion Hr1v.

     (* First, the case where r1v is a capability *)
     + destruct (perm_eq_dec p E); [ subst p |].
       { rewrite /is_mutable_range in Hr1v; congruence. }

       destruct (a + argz)%a as [ a' |] eqn:Hoffset; cycle 1.
       { (* Failure: offset is too large *)
         assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailStep Lea_fail_overflow_cap. }

       rewrite /update_reg /= in Hstep.
       destruct (incrementPC (<[ r1 := WCap p b e a' ]> regs)) as [ regs' |] eqn:Hregs';
         pose proof Hregs' as Hregs'2; cycle 1.
       { (* Failure: incrementing PC overflows *)
         assert (incrementPC (<[ r1 := WCap p b e a' ]> σr) = None) as HH.
         { eapply incrementPC_overflow_mono; first eapply Hregs'.
             by rewrite lookup_insert_is_Some'; eauto.
               by apply insert_mono; eauto. }
         apply (incrementPC_fail_updatePC _ σm) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailStep Lea_fail_overflow_PC_cap. }

       (* Success *)
       eapply (incrementPC_success_updatePC _ σm) in Hregs'
         as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
       rewrite HuPC in Hstep; clear HuPC.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct p; cbn in Hstep; eauto. congruence. }
       simplify_pair_eq.

       iFrame.
       iMod ((regspec_heap_update_inSepM _ _ _ r1) with "Hown Hmap") as "[Hr Hmap]"; eauto.
       iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hr Hj") as "[Hown Hj]".
       iExists NextIV,_. iFrame.
       iMod ("Hclose" with "[Hown]") as "_".
       { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
         prim_step_from_exec. }
       iModIntro. iPureIntro.
       eapply Lea_spec_success_cap; eauto.
    (* Now, the case where r1v is a sealrange *)
    + destruct (a + argz)%ot as [ a' |] eqn:Hoffset; cycle 1.
       { (* Failure: offset is too large *)
         assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailStep Lea_fail_overflow_sr. }

       rewrite /update_reg /= in Hstep.
       destruct (incrementPC (<[ r1 := WSealRange p b e a' ]> regs)) as [ regs' |] eqn:Hregs';
         pose proof Hregs' as Hregs'2; cycle 1.
       { (* Failure: incrementing PC overflows *)
         assert (incrementPC (<[ r1 := WSealRange p b e a' ]> σr) = None) as HH.
         { eapply incrementPC_overflow_mono; first eapply Hregs'.
             by rewrite lookup_insert_is_Some'; eauto.
               by apply insert_mono; eauto. }
         apply (incrementPC_fail_updatePC _ σm) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailStep Lea_fail_overflow_PC_sr. }

       (* Success *)
       eapply (incrementPC_success_updatePC _ σm) in Hregs'
         as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
       rewrite HuPC in Hstep; clear HuPC.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct p; cbn in Hstep; eauto. }
       simplify_pair_eq.

       iFrame.
       iMod ((regspec_heap_update_inSepM _ _ _ r1) with "Hown Hmap") as "[Hr Hmap]"; eauto.
       iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hr Hj") as "[Hown Hj]".
       iExists NextIV,_. iFrame.
       iMod ("Hclose" with "[Hown]") as "_".
       { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
         prim_step_from_exec. }
       iModIntro. iPureIntro.
       eapply Lea_spec_success_sr; eauto. Unshelve. all: auto.
   Qed.


   Lemma step_lea_success_z Ep K pc_p pc_b pc_e pc_a pc_a' w r1 p b e a z a' :
     decodeInstrW w = Lea r1 (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →

     nclose specN ⊆ Ep →

     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ r1 ↣ᵣ WCap p b e a
     ={Ep}=∗ ⤇ fill K (of_val NextIV)
          ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↣ₐ w
          ∗ r1 ↣ᵣ WCap p b e a'.
   Proof. 
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1)".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_lea with "[$Hmap $Hown $Hj $Hpc_a]") as (retv regs') "(Hj & #Hspec & Hpc_a & Hmap)"; eauto;[rewrite lookup_insert;eauto|..].
     by rewrite !dom_insert; set_solver+.
     iDestruct "Hspec" as %Hspec.
     
     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
       iFrame. incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite insert_commute // insert_insert insert_commute // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. by iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct p; congruence.
       congruence.
       Unshelve. all: auto.
     }
   Qed.

   Lemma step_lea_success_reg Ep K pc_p pc_b pc_e pc_a pc_a' w r1 rv p b e a z a' :
     decodeInstrW w = Lea r1 (inr rv) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →
     nclose specN ⊆ Ep →

     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ r1 ↣ᵣ WCap p b e a
              ∗ ▷ rv ↣ᵣ WInt z
     ={Ep}=∗ ⤇ fill K (Instr NextI)
          ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↣ₐ w
          ∗ rv ↣ᵣ WInt z
          ∗ r1 ↣ᵣ WCap p b e a'.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1 & >Hrv)".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iMod (step_lea with "[$Hmap $Hown $Hj $Hpc_a]") as (retv regs') "(Hj & #Hspec & Hpc_a & Hmap)"; eauto;[rewrite lookup_insert;eauto|..].
     by rewrite !dom_insert; set_solver+.
     iDestruct "Hspec" as %Hspec.
     
     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
        iFrame. incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite (insert_commute _ PC r1) // insert_insert.
       rewrite (insert_commute _ r1 PC) // (insert_commute _ r1 rv) // insert_insert.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct p; congruence.
       congruence.
     }
    Unshelve. all: auto.
   Qed.

End cap_lang_spec_rules. 
