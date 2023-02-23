From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_Subseg rules_binary_base.


Section cap_lang_spec_rules. 
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  
  Lemma step_Subseg Ep K pc_p pc_b pc_e pc_a w dst src1 src2 regs :
    decodeInstrW w = Subseg dst src1 src2 ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →

    nclose specN ⊆ Ep →
    
    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ ▷ pc_a ↣ₐ w ∗ ▷ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗ ⤇ fill K (of_val retv) ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hnclose) "(Hinv & Hj & >Hpc_a & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a. 
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    pose proof (Hstep' := Hstep). rewrite /exec /= Hdst /= in Hstep.

    destruct (is_mutable_range wdst) eqn:Hwdst.
     2: { (* Failure: wdst is not of the right type *)
       unfold is_mutable_range in Hwdst.
       assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
       { destruct wdst as [ | [p b e a | ] | ]; try by inversion Hwdst.
         all: try by simplify_pair_eq.
         destruct p; try congruence.
         repeat destruct (addr_of_argument σr _); cbn in Hstep; simplify_pair_eq; auto. }
       iFailStep Subseg_fail_allowed. }

    (* Now the proof splits depending on the type of value in wdst *)
    destruct wdst as [ | [p b e a | p b e a] | ].
    1,4: inversion Hwdst.

    (* First, the case where wdst is a capability *)
    +
      destruct (perm_eq_dec p E); [ subst p |].
       { rewrite /is_mutable_range in Hwdst; congruence. }

      destruct (addr_of_argument regs src1) as [a1|] eqn:Ha1;
      pose proof Ha1 as H'a1; cycle 1.
    { destruct src1 as [| r1] eqn:?; cbn in Ha1, Hstep.
      { rewrite Ha1 /= in Hstep.
        assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
        { repeat case_match; inv Hstep; auto. }

        iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
          iMod ("Hclose" with "[Hown]") as "_";
          [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|]. 
        iExists (FailedV),_; iFrame;iModIntro;iFailCore Subseg_fail_src1_nonaddr.
      } 
      subst src1. destruct (Hri r1) as [r1v [Hr'1 Hr1]].
        by unfold regs_of_argument; set_solver+.
      rewrite /addr_of_argument /= Hr'1 in Ha1.
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { destruct r1v.
        all: unfold addr_of_argument, z_of_argument at 2 in Hstep.
        all: rewrite Hr1 ?Ha1 /= in Hstep.
        all: inv Hstep; auto.
      }
      repeat case_match; try congruence; try rename c into c0.
      all: iFailStep Subseg_fail_src1_nonaddr. 
    }
    apply (addr_of_arg_mono _ σr) in Ha1; auto. rewrite Ha1 /= in Hstep.

    eapply addr_of_argument_Some_inv' in Ha1 as [z1 [Hz1 Hz1']]; eauto.

    destruct (addr_of_argument regs src2) as [a2|] eqn:Ha2;
      pose proof Ha2 as H'a2; cycle 1.
    { destruct src2 as [| r2] eqn:?; cbn in Ha2, Hstep.
      { rewrite Ha2 /= in Hstep.
        assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
        { repeat case_match; inv Hstep; auto. }
        iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
          iMod ("Hclose" with "[Hown]") as "_";
          [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|]. 
        iExists (FailedV),_; iFrame;iModIntro;iFailCore Subseg_fail_src2_nonaddr. }
      subst src2. destruct (Hri r2) as [r2v [Hr'2 Hr2]].
        by unfold regs_of_argument; set_solver+.
      rewrite /addr_of_argument /= Hr'2 in Ha2.
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { destruct r2v.
        all: unfold addr_of_argument, z_of_argument  in Hstep.
        all: rewrite Hr2 ?Ha2 /= in Hstep.
        all: inv Hstep; auto. }
      repeat case_match; try congruence; try rename c into c0.
      all: iFailStep Subseg_fail_src2_nonaddr. }
    apply (addr_of_arg_mono _ σr) in Ha2; auto. rewrite Ha2 /= in Hstep.
      rewrite /update_reg /= in Hstep.

      destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1.
      { destruct p; try congruence; inv Hstep ; iFailStep Subseg_fail_not_iswithin_cap. }

      destruct (incrementPC (<[ dst := (WCap p a1 a2 a) ]> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      { assert (incrementPC (<[ dst := (WCap p a1 a2 a) ]> σr) = None) as HH.
        { eapply incrementPC_overflow_mono; first eapply Hregs'.
            by rewrite lookup_insert_is_Some'; eauto.
              by apply insert_mono; eauto. }
        apply (incrementPC_fail_updatePC _ σm) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
            by (destruct p; inversion Hstep; auto).
        iFailStep Subseg_fail_incrPC_cap. }

      eapply (incrementPC_success_updatePC _ σm) in Hregs'
        as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { destruct p; cbn in Hstep; eauto. congruence. }
      simplify_pair_eq. iFrame.
      iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
      iMod ((regspec_heap_update_inSepM _ _ _ PC (WCap p' g' b' a'')) with "Hown Hmap") as "[Hown Hmap]"; eauto.
      iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
      iExists NextIV,_. iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
        prim_step_from_exec.
      }
      iModIntro. iPureIntro. econstructor; eauto.
  (* Now, the case where wsrc is a capability *)
    + destruct (otype_of_argument regs src1) as [a1|] eqn:Ha1;
        pose proof Ha1 as H'a1; cycle 1.
      { destruct src1 as [| r1] eqn:?; cbn in Ha1, Hstep.
        { rewrite Ha1 /= in Hstep.
          assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
          { repeat case_match; inv Hstep; auto. }
          iFailStep Subseg_fail_src1_nonotype. }
        subst src1. destruct (Hri r1) as [r1v [Hr'1 Hr1]].
          by unfold regs_of_argument; set_solver+.
          rewrite /otype_of_argument /= Hr'1 in Ha1.
          assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
          { destruct r1v ; simplify_pair_eq.
            all: unfold otype_of_argument, z_of_argument at 2 in Hstep.
            all: rewrite /= Hr1 ?Ha1 /= in Hstep.
            all: inv Hstep; auto.
          }
          destruct_word r1v; try congruence.
          cbn in Hstep.
          all: try by iFailStep Subseg_fail_src1_nonotype. }
      apply (otype_of_arg_mono _ σr) in Ha1; auto. rewrite Ha1 /= in Hstep.

      destruct (otype_of_argument regs src2) as [a2|] eqn:Ha2;
        pose proof Ha2 as H'a2; cycle 1.
      { destruct src2 as [| r2] eqn:?; cbn in Ha2, Hstep.
        { rewrite Ha2 /= in Hstep.
          assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
          { repeat case_match; inv Hstep; auto. }
          iFailStep Subseg_fail_src2_nonotype. }
        subst src2. destruct (Hri r2) as [r2v [Hr'2 Hr2]].
          by unfold regs_of_argument; set_solver+.
          rewrite /otype_of_argument /= Hr'2 in Ha2.
          assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
          { destruct r2v ; simplify_pair_eq.
            all: unfold otype_of_argument, z_of_argument  in Hstep.
            all: rewrite /= Hr2 ?Ha2 /= in Hstep.
            all: inv Hstep; auto.
          }
          repeat case_match; try congruence.
          all: iFailStep Subseg_fail_src2_nonotype. }
      apply (otype_of_arg_mono _ σr) in Ha2; auto. rewrite Ha2 /= in Hstep.
      rewrite /update_reg /= in Hstep.

      destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1.
      { destruct p; try congruence; inv Hstep ; iFailStep Subseg_fail_not_iswithin_sr. }

      destruct (incrementPC (<[ dst := (WSealRange p a1 a2 a) ]> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      { assert (incrementPC (<[ dst := (WSealRange p a1 a2 a) ]> σr) = None) as HH.
        { eapply incrementPC_overflow_mono; first eapply Hregs'.
            by rewrite lookup_insert_is_Some'; eauto.
              by apply insert_mono; eauto. }
        apply (incrementPC_fail_updatePC _ σm) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->)
            by (destruct p; inversion Hstep; auto).
        iFailStep Subseg_fail_incrPC_sr. }

      eapply (incrementPC_success_updatePC _ σm) in Hregs'
        as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { destruct p; cbn in Hstep; eauto. }
      simplify_pair_eq. iFrame.
      iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
      iMod ((regspec_heap_update_inSepM _ _ _ PC (WCap p' g' b' a'')) with "Hown Hmap") as "[Hown Hmap]"; eauto.
      iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
      iExists NextIV,_. iFrame.
      iMod ("Hclose" with "[Hown]") as "_".
      { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
        prim_step_from_exec.
      }
      iModIntro. iPureIntro. econstructor 2; eauto.
  Qed.

  Lemma step_subseg_success E K pc_p pc_b pc_e pc_a w dst r1 r2 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →
    
    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ dst ↣ᵣ WCap p b e a
             ∗ ▷ r1 ↣ᵣ WInt n1
             ∗ ▷ r2 ↣ᵣ WInt n2
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ pc_a ↣ₐ w
        ∗ r1 ↣ᵣ WInt n1
        ∗ r2 ↣ᵣ WInt n2
        ∗ dst ↣ᵣ WCap p a1 a2 a.
  Proof. 
    iIntros (Hinstr Hvpc [Hn1 Hn2] Hpne Hwb Hpc_a' Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2)".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iMod (step_Subseg with "[$Hown $Hj $Hpc_a $Hmap]") as (retv regs' Hspec) "(Hj & Hpc_a & Hmap)";simplify_map_eq;eauto. 
    by unfold regs_of; rewrite !dom_insert; set_solver+.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; by iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

End cap_lang_spec_rules.
