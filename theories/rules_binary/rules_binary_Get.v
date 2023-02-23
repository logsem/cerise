From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_Get rules_binary_base.

Section cap_lang_spec_rules. 
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma step_Get Ep K pc_p pc_b pc_e pc_a w get_i dst src regs :
    decodeInstrW w = get_i →
    is_Get get_i dst src →

    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of get_i ⊆ dom regs →

    nclose specN ⊆ Ep →
    
    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ ▷ pc_a ↣ₐ w ∗ ▷ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⤇ fill K (of_val retv) ∗ ⌜ Get_spec (decodeInstrW w) regs dst src regs' retv ⌝ ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hdecode Hinstr Hvpc HPC Dregs Hnclose) "(Hinv & Hj & >Hpc_a & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a. 
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.
    pose proof (Hstep' := Hstep). unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    erewrite regs_of_is_Get in Hri; eauto.
    destruct (Hri src) as [wsrc [H'src Hsrc]]. by set_solver+.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.
    destruct (denote get_i wsrc) as [z | ] eqn:Hwsrc.
    2 : { (* Failure: src is not of the right word type *)
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr in Hstep; cbn in Hstep.
        all: rewrite Hsrc /= in Hstep.
        all : destruct wsrc as [ | [  |  ] | ]; try (inversion Hstep; auto);
          rewrite /denote /= in Hwsrc; rewrite Hinstr in Hwsrc; congruence. }
      rewrite Hdecode. iFailStep Get_fail_src_denote. }

    assert (exec_opt get_i (σr, σm) = updatePC (update_reg (σr, σm) dst (WInt z))) as HH.
    { destruct_or! Hinstr; clear Hdecode; subst get_i; cbn in Hstep |- *.
      all: rewrite /update_reg Hsrc /= in Hstep |-*; auto.
      all : destruct wsrc as [ | [  |  ] | ]; inversion Hwsrc; auto.
    }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := WInt z ]> regs))
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    { (* Failure: incrementing PC overflows *)
      apply incrementPC_fail_updatePC with (m:=σm) in Hregs'.
      eapply updatePC_fail_incl with (m':=σm) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      rewrite Hregs' in Hstep. inv Hstep.
      iFailStep Get_fail_overflow_PC. }

    (* Success *)

    eapply (incrementPC_success_updatePC _ σm) in Hregs'
        as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.

    simplify_pair_eq. iFrame.
    iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
    iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hown Hmap") as "[Hown Hmap]"; eauto. 
    iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
    iExists NextIV,_. iFrame.
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
      prim_step_from_exec. }
    iModIntro. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_Get_success E K get_i dst src pc_p pc_b pc_e pc_a w wdst wsrc z pc_a' :
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wsrc = Some z →
    nclose specN ⊆ E →
    
    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ src ↣ᵣ wsrc
             ∗ ▷ dst ↣ᵣ wdst
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ pc_a ↣ₐ w
        ∗ src ↣ᵣ wsrc
        ∗ dst ↣ᵣ WInt z.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote Hnlose) "(#Hown & Hj & >HPC & >Hpc_a & >Hsrc & >Hdst)".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iMod (step_Get with "[$Hmap $Hj $Hown $Hpc_a]") as (retv regs') "(Hj & #Hspec & Hpc_a & Hmap)"; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as [| * Hfail].
    { (* Success *)
      iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "[? [? ?]]"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

End cap_lang_spec_rules. 
