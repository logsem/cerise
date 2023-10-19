From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_Restrict rules_binary_base.

Section cap_lang_spec_rules.
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma step_Restrict Ep K pc_p pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = Restrict dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of (Restrict dst src) ⊆ dom regs →

    nclose specN ⊆ Ep →

    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⌜ Restrict_spec regs dst src regs' retv ⌝ ∗ ⤇ fill K (of_val retv) ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
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

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+. cbn in Hdst.
    rewrite /exec_opt /= Hdst /= in Hstep.

    destruct (z_of_argument regs src) as [wsrc|] eqn:Hwsrc;
      pose proof Hwsrc as H'wsrc; cycle 1.
    { destruct src as [| r0]; cbn in Hwsrc; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hwsrc.
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { cbn in Hr0.  destruct_word r0v; try congruence; cbn in Hstep; rewrite Hr0 /= in Hstep; by simplify_pair_eq. }
      iFailStep Restrict_fail_src_nonz. }
    apply (z_of_arg_mono _ σr) in Hwsrc; auto. rewrite /= Hwsrc in Hstep; simpl in Hstep.

    destruct (is_mutable_range wdst) eqn:Hwdst.
     2: { (* Failure: wdst is not of the right type *)
       unfold is_mutable_range in Hwdst.
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
       { destruct wdst as [ | [p b e a | ] | ]; try by inversion Hwdst.
         all: try by simplify_pair_eq.
         destruct p; try congruence.
         simplify_pair_eq; auto. }
       iFailStep Restrict_fail_allowed. }

    destruct wdst as [ | [p b e a | p b e a] | ].
    1,4: inversion Hwdst.
    (* First, the case where r1v is a capability *)
    + destruct (perm_eq_dec p E); [ subst p |].
       { rewrite /is_mutable_range in Hwdst; congruence. }

       destruct (PermFlowsTo (decodePerm wsrc) p) eqn:Hflows; cycle 1.
       { destruct p; try congruence; inv Hstep ; iFailStep Restrict_fail_invalid_perm_cap. }
       rewrite /update_reg /= in Hstep.

       destruct (incrementPC (<[ dst := WCap (decodePerm wsrc) b e a ]> regs)) eqn:Hregs';
         pose proof Hregs' as H'regs'; cycle 1.
       {
         assert (incrementPC (<[ dst := WCap( decodePerm wsrc) b e a ]> σr) = None) as HH.
         { eapply incrementPC_overflow_mono; first eapply Hregs'.
             by rewrite lookup_insert_is_Some'; eauto.
               by apply insert_mono; eauto. }
         apply (incrementPC_fail_updatePC _ σm) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailStep Restrict_fail_PC_overflow_cap. }

       eapply (incrementPC_success_updatePC _ σm) in Hregs'
         as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct p; cbn in Hstep; eauto. congruence. }
       simplify_pair_eq.

       iFrame.
      iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hr Hmap]"; eauto.
      iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hr Hj") as "[Hown Hj]".
      iExists NextIV,_. iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
        prim_step_from_exec.
      }
      iModIntro. iPureIntro. econstructor; eauto.
   (* Now, the case where wsrc is a sealrange *)
   + destruct (SealPermFlowsTo (decodeSealPerms wsrc) p) eqn:Hflows; cycle 1.
       { destruct p; try congruence; inv Hstep ; iFailStep Restrict_fail_invalid_perm_sr. }
       rewrite /update_reg /= in Hstep.

       destruct (incrementPC (<[ dst := WSealRange (decodeSealPerms wsrc) b e a ]> regs)) eqn:Hregs';
         pose proof Hregs' as H'regs'; cycle 1.
       {
         assert (incrementPC (<[ dst := WSealRange (decodeSealPerms wsrc) b e a ]> σr) = None) as HH.
         { eapply incrementPC_overflow_mono; first eapply Hregs'.
             by rewrite lookup_insert_is_Some'; eauto.
               by apply insert_mono; eauto. }
         apply (incrementPC_fail_updatePC _ σm) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailStep Restrict_fail_PC_overflow_sr. }

       eapply (incrementPC_success_updatePC _ σm) in Hregs'
         as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct p; cbn in Hstep; eauto. }
       simplify_pair_eq.
       iFrame.
      iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hr Hmap]"; eauto.
      iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hr Hj") as "[Hown Hj]".
      iExists NextIV,_. iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
        prim_step_from_exec.
      }
      iModIntro. iPureIntro. econstructor 2; eauto. Unshelve. all: try done.
  Qed.

  Lemma step_restrict_success_z Ep K pc_p pc_b pc_e pc_a pc_a' w r1 p b e a z :
     decodeInstrW w = Restrict r1 (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) p = true →
     p ≠ E →
     nclose specN ⊆ Ep →

     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ r1 ↣ᵣ WCap p b e a
     ={Ep}=∗ ⤇ fill K (Instr NextI)
         ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
         ∗ pc_a ↣ₐ w
         ∗ r1 ↣ᵣ WCap (decodePerm z) b e a.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hflows HpE Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1)".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iMod (step_Restrict with "[$Hown $Hj $Hmap $Hpc_a]") as (retv regs' Hspec) "(Hj & Hpc_a & Hregs)";
      eauto; simplify_map_eq_alt; try rewrite lookup_insert; eauto.
      by unfold regs_of; rewrite !dom_insert; set_solver+.

     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [| | * Hfail].
     { (* Success *)
       iFrame. incrementPC_inv; simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert
               (insert_commute _ PC r1) // insert_insert.
       iDestruct (regs_of_map_2 with "Hregs") as "(?&?)"; eauto; by iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       destruct p; congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
 Qed.

End cap_lang_spec_rules.
