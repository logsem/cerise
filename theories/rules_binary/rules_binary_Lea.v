From cap_machine Require Export rules_Lea rules_binary_base.
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

  Lemma step_lea Ep K pc_p pc_b pc_e pc_a r1 w arg (regs: Reg) :
     decodeInstrW w = Lea r1 arg →
     isCorrectPC (WCap (pc_p, pc_b, pc_e, pc_a)) →
     regs !! PC = Some (WCap (pc_p, pc_b, pc_e, pc_a)) →
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
     pose proof (regs_lookup_eq _ _ _ HPC) as HPC'.
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     iDestruct (@spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a; auto.
     iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
     specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
     eapply step_exec_inv in Hstep; eauto.

     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.

     feed destruct (Hri r1) as [r1v [Hr'1 Hr1]]. by set_solver+.
     pose proof (regs_lookup_eq _ _ _ Hr1) as Hr1'.
     assert (Hstep':=Hstep). 
     cbn in Hstep. rewrite Hr1' in Hstep.
     destruct r1v as [| (([p b] & e) & a) ] eqn:Hr1v.
     { (* Failure: r1 is not a capability *)
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
           by (destruct arg; inversion Hstep; auto). 
       iFailStep Lea_fail_r1_noncap. 
     }

     destruct (perm_eq_dec p E); [ subst p |].
     { (* Failure: r1.p is Enter *)
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
       { destruct arg; inversion Hstep; subst; eauto. }
       iFailStep Lea_fail_p_E. }
     
     destruct (z_of_argument regs arg) as [ argz |] eqn:Harg;
       pose proof Harg as Harg'; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Harg. destruct arg as [| r0]; [ congruence |].
       feed destruct (Hri r0) as [r0v [Hr'0 Hr0]].
       { unfold regs_of_argument. set_solver+. }
       rewrite /RegLocate Hr0 Hr'0 in Harg Hstep.
       destruct r0v; [ congruence |].
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
         by (destruct p; inversion Hstep; eauto).
       iFailStep Lea_fail_rv_nonconst. }

     destruct (a + argz)%a as [ a' |] eqn:Hoffset; cycle 1.
     { (* Failure: offset is too large *)
       unfold z_of_argument in Harg. destruct arg as [ z | r0].
       { inversion Harg; subst z. rewrite Hoffset in Hstep.
         assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
         iFailStep Lea_fail_overflow. }
       { feed destruct (Hri r0) as [r0v [Hr'0 Hr0]].
         by unfold regs_of_argument; set_solver+.
         rewrite /RegLocate Hr'0 Hr0 in Harg Hstep.
         destruct r0v; [| congruence]. inversion Harg; subst z.
         rewrite Hoffset in Hstep.
         assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
         iFailStep Lea_fail_overflow. } }

     assert ((c, σ2) = updatePC (update_reg (σr, σm) r1 (WCap (p, b, e, a')))) as HH.
     { unfold z_of_argument in Harg. destruct arg as [ z | r0 ].
       { inversion Harg; subst z. rewrite Hoffset in Hstep.
         destruct p; auto; try congruence; destruct (Addr_le_dec a' a); try congruence; auto; solve_addr. }
       { feed destruct (Hri r0) as [r0v [Hr'0 Hr0]].
         by unfold regs_of_argument; set_solver+.
         rewrite /RegLocate Hr'0 Hr0 in Harg Hstep.
         destruct r0v; [| congruence]. inversion Harg; subst z.
         rewrite Hoffset in Hstep.
         destruct p; auto; try congruence; destruct (Addr_le_dec a' a); try congruence; auto; solve_addr. } }
     clear Hstep. rewrite /update_reg /= in HH.

     destruct (incrementPC (<[ r1 := WCap (p, b, e, a') ]> regs)) as [ regs' |] eqn:Hregs';
       pose proof Hregs' as Hregs'2; cycle 1.
     { (* Failure: incrementing PC overflows *)
       assert (incrementPC (<[ r1 := WCap ((p, b, e, a'))]> σr) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         by rewrite lookup_insert_is_Some'; eauto.
         by apply insert_mono; eauto. }
       rewrite incrementPC_fail_updatePC //= in HH; inversion HH; subst.
       iMod (@regspec_heap_update_inSepM with "Hown Hmap") as "[Hown Hmap]"; eauto.
       iFailStep Lea_fail_overflow_PC. }
     
     (* Success *)

     eapply (incrementPC_success_updatePC _ σm) in Hregs'
       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
     rewrite HuPC in HH; clear HuPC; inversion HH; clear HH; subst c σ2. cbn.
     iFrame.
     iMod ((regspec_heap_update_inSepM _ _ _ r1) with "Hown Hmap") as "[Hr Hmap]"; eauto.
     iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hr Hj") as "[Hown Hj]".
     iExists NextIV,_. iFrame.
     iMod ("Hclose" with "[Hown]") as "_".
     { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
       prim_step_from_exec. }
     iModIntro. iPureIntro.
     eapply Lea_spec_success; eauto.

     Unshelve. all: assumption.
   Qed.


   Lemma step_lea_success_z Ep K pc_p pc_b pc_e pc_a pc_a' w r1 p b e a z a' :
     decodeInstrW w = Lea r1 (inl z) →
     isCorrectPC (WCap (pc_p,pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →

     nclose specN ⊆ Ep →

     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗ ▷ PC ↣ᵣ WCap (pc_p,pc_b,pc_e,pc_a)
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ r1 ↣ᵣ WCap (p,b,e,a)
     ={Ep}=∗ ⤇ fill K (of_val NextIV)
          ∗ PC ↣ᵣ WCap (pc_p,pc_b,pc_e,pc_a')
          ∗ pc_a ↣ₐ w
          ∗ r1 ↣ᵣ WCap (p,b,e,a').
   Proof. 
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1)".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_lea with "[$Hmap $Hown $Hj $Hpc_a]") as (retv regs') "(Hj & #Hspec & Hpc_a & Hmap)"; eauto;[rewrite lookup_insert;eauto|..].
     by rewrite !dom_insert; set_solver+.
     iDestruct "Hspec" as %Hspec.
     
     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       incrementPC_inv; 
       rewrite insert_commute // insert_insert insert_commute // insert_insert. simpl in *. 
       simplify_map_eq_alt. iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. by iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; eauto; simpl in *; simplify_map_eq_alt. 
       incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert;eauto]. congruence. 
     }
   Qed.

   Lemma step_lea_success_reg Ep K pc_p pc_b pc_e pc_a pc_a' w r1 rv p b e a z a' :
     decodeInstrW w = Lea r1 (inr rv) →
     isCorrectPC (WCap (pc_p,pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →
     nclose specN ⊆ Ep →

     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗ ▷ PC ↣ᵣ WCap (pc_p,pc_b,pc_e,pc_a)
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ r1 ↣ᵣ WCap (p,b,e,a)
              ∗ ▷ rv ↣ᵣ WInt z
     ={Ep}=∗ ⤇ fill K (Instr NextI)
          ∗ PC ↣ᵣ WCap (pc_p,pc_b,pc_e,pc_a')
          ∗ pc_a ↣ₐ w
          ∗ rv ↣ᵣ WInt z
          ∗ r1 ↣ᵣ WCap (p,b,e,a').
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1 & >Hrv)".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iMod (step_lea with "[$Hmap $Hown $Hj $Hpc_a]") as (retv regs') "(Hj & #Hspec & Hpc_a & Hmap)"; eauto;[rewrite lookup_insert;eauto|..].
     by rewrite !dom_insert; set_solver+.
     iDestruct "Hspec" as %Hspec.
     
     destruct Hspec as [| * Hfail ].
     { (* Success *)
       incrementPC_inv; simpl in *; simplify_map_eq_alt.
       rewrite (insert_commute _ PC r1) // insert_insert.
       rewrite (insert_commute _ r1 PC) // (insert_commute _ r1 rv) // insert_insert.
       iFrame. iModIntro. iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; simpl in *; simplify_eq; eauto; simplify_map_eq_alt.
       incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert;eauto]. congruence.
     }
   Qed.

End cap_lang_spec_rules. 
