From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr. 
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive PromoteU_failure (regs: Reg) (dst: RegName): Prop :=
  | PromoteU_fail_const n:
      regs !! dst = Some (inl n) ->
      PromoteU_failure regs dst
  | PromoteU_fail_E g b e a:
      regs !! dst = Some (inr ((E, g), b, e, a)) ->
      PromoteU_failure regs dst
  | PromoteU_fail_incrementPC p g b e a:
      p <> E ->
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      incrementPC (<[ dst := inr (promote_perm p, g, b, min a e, a) ]> regs) = None ->
      PromoteU_failure regs dst.

  Inductive PromoteU_spec (regs: Reg) (dst: RegName) (regs': Reg): cap_lang.val → Prop :=
  | PromoteU_spec_success p g b e a:
      p <> E ->
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      incrementPC (<[ dst := inr (promote_perm p, g, b, min a e, a) ]> regs) = Some regs' ->
      PromoteU_spec regs dst regs' NextIV
  | PromoteU_spec_failure:
      PromoteU_failure regs dst ->
      PromoteU_spec regs dst regs' FailedV.

  Lemma wp_PromoteU Ep pc_p pc_g pc_b pc_e pc_a pc_p' dst w regs :
   cap_lang.decode w = PromoteU dst →
   PermFlows pc_p pc_p' →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (PromoteU dst) ⊆ dom _ regs →

   {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ PromoteU_spec regs dst regs' retv⌝ ∗
       pc_a ↦ₐ[pc_p'] w ∗
       [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
     iIntros (Hinstr Hfl Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
     pose proof (regs_lookup_eq _ _ _ HPC) as HPC'.
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %Hpc_a; auto.
     iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.

     feed destruct (Hri dst) as [rdstv [Hdst' Hdst]]. by set_solver+.
     pose proof (regs_lookup_eq _ _ _ Hdst) as Hrdst'.
     cbn in Hstep. rewrite Hrdst' in Hstep.
     destruct rdstv as [| (([[p g] b] & e) & a) ] eqn:Hdstv.
     { (* Failure: dst is not a capability *)
       inv Hstep.
       iFailWP "Hφ" PromoteU_fail_const. }

     destruct (perm_eq_dec p E).
     { subst p. inv Hstep.
       iFailWP "Hφ" PromoteU_fail_E. }

     destruct (incrementPC (<[ dst := inr ((promote_perm p, g), b, min a e, a) ]> regs)) as [ regs' |] eqn:Hregs'; cycle 1.
     { assert (incrementPC (<[ dst := inr ((promote_perm p, g, b, min a e, a))]> r) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         by rewrite lookup_insert_is_Some'; eauto.
         by apply insert_mono; eauto. }
       rewrite incrementPC_fail_updatePC //= in Hstep; inversion Hstep; subst.
       iMod (@gen_heap_update_inSepM with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFailWP "Hφ" PromoteU_fail_incrementPC. }

     generalize Hregs'; intros HH.
     eapply (incrementPC_success_updatePC _ m) in Hregs'
       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep. subst c σ2. cbn.
     iFrame. iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
     econstructor; eauto.
     Unshelve. auto.
  Qed.

End cap_lang_rules.
