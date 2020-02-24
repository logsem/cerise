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

  Instance option_dec_eq `(A_dec : ∀ x y : B, Decision (x = y)) (o o': option B) : Decision (o = o').
  Proof. solve_decision. Qed.

  (* Conditionally unify on the read register value *)
  Definition read_reg_inr  (regs : Reg) (r : RegName) p g b e a :=
    regs !! r = Some (inr ((p, g), b, e, a)) ∨ ∃ z, regs !! r = Some(inl z).

  Definition reg_allows_load (regs : Reg) (r : RegName) p g b e a  :=
    regs !! r = Some (inr ((p, g), b, e, a)) ∧
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true.

  Global Instance reg_allows_load_dec_eq  (regs : Reg) (r : RegName) p g b e a : Decision (reg_allows_load regs r p g b e a).
  Proof.
    unfold reg_allows_load. destruct (regs !! r). destruct s.
    - right. intros Hfalse; destruct Hfalse; by exfalso.
    - assert (Decision (Some (inr (A:=Z) p0) = Some (inr (p, g, b, e, a)))) as Edec.
      refine (option_dec_eq _ _ _). intros.
      refine (sum_eq_dec _ _); unfold EqDecision; intros. refine (cap_dec_eq x0 y0).
      solve_decision.
    - solve_decision.
  Qed.

  Inductive Load_failure (regs: Reg) (r1 r2: RegName) (mem : PermMem):=
  | Load_fail_const z:
      regs !r! r2 = inl z ->
      Load_failure regs r1 r2 mem
  | Load_fail_bounds p g b e a:
      regs !r! r2 = inr ((p, g), b, e, a) ->
      (readAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false) →
      Load_failure regs r1 r2 mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC p p' g b e a loadv:
      regs !r! r2 = inr ((p, g), b, e, a) ->
      mem !! a = Some(p', loadv) →
      incrementPC (<[ r1 := loadv ]> regs) = None ->
      Load_failure regs r1 r2 mem
  .

  Inductive Load_spec
    (regs: Reg) (r1 r2: RegName)
    (regs': Reg) (retv: cap_lang.val) (mem : PermMem) : Prop
  :=
  | Load_spec_success p p' g b e a loadv :
    retv = NextIV ->
    reg_allows_load regs r2 p g b e a →
    mem !! a = Some(p', loadv) →
    incrementPC
      (<[ r1 := loadv ]> regs) = Some regs' ->
    Load_spec regs r1 r2 regs' retv mem

  | Load_spec_failure :
    retv = FailedV ->
    Load_failure regs r1 r2 mem ->
    Load_spec regs r1 r2 regs' retv mem.

  Definition allow_load_map_or_true r (regs : Reg) (mem : PermMem):=
    ∃ p g b e a, read_reg_inr regs r p g b e a ∧
      if decide (reg_allows_load regs r p g b e a) then
        ∃ p' w, mem !! a = Some (p', w) ∧ PermFlows p p'
      else True.

   Lemma wp_load Ep
     pc_p pc_g pc_b pc_e pc_a pc_p'
     r1 r2 w mem regs :
   cap_lang.decode w = Load r1 r2 →
   PermFlows pc_p pc_p' →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   (∀ (ri: RegName), is_Some (regs !! ri)) →
   mem !! pc_a = Some (pc_p', w) →
   allow_load_map_or_true r2 regs mem →

   {{{ (▷ [∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 regs' retv mem⌝ ∗
         ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hnep Hri Hmem_pc HaLoad φ) "(>Hmem & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "[Hr Hm] /=". destruct σ1; simpl.
     assert (pc_p' ≠ O).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }

     iAssert (⌜ r = regs ⌝)%I with "[Hr Hmap]" as %<-.
     { iApply (gen_heap_valid_allSepM with "[Hr]"); eauto. }
     (* Derive the pointsto for the PC *)
     iDestruct ((big_sepM_delete _ _ pc_a _ Hmem_pc) with "Hmem") as "[Hpc_a Hmem]".
     iDestruct "Hpc_a" as (p w0) "[% Hpc_a]". symmetry in H2; inversion H2; simplify_eq.
     iDestruct (gen_heap_valid_cap with "Hm Hpc_a") as %?; auto.
     option_locate_mr m r.
     iModIntro.

     iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep.
     destruct Hpstep as (-> & -> & (c & -> & Hstep)). iSplitR; auto.
     inversion Hstep as [| ? ? ? ? ?].
     { cbn in H2. rewrite HPC in H2. congruence. }
     assert (p = pc_p /\ g = pc_g /\ b = pc_b /\ e = pc_e /\ a = pc_a) as (-> & -> & -> & -> & ->).
     { cbn in *. rewrite HPC in H2. by inversion H2. }
     clear H2 H3. cbn in H4. rewrite Hpc_a in H4.
     assert (i = Load r1 r2) as ->. { by rewrite Hinstr in H4. } clear H4.
     destruct c0 as [xx1 xx2]; cbn in H7, H8; subst xx1 xx2. subst φ0.
     cbn [fst snd].
     cbn in H5.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct (r !r! r2) as  [| (([[p g] b] & e) & a) ] eqn:Hr2v.
     { (* Failure: r2 is not a capability *)

       symmetry in H5; inversion H5; clear H5. subst c σ2.
       cbn. iFrame.
       iSpecialize ("Hφ" $! r FailedV). iApply "Hφ".
       iFrame. iSplitR.
       - iPureIntro. eapply Load_spec_failure; auto. eapply Load_fail_const; eauto.
       - iDestruct ((big_sepM_delete _ _ pc_a) with "[Hpc_a Hmem]") as "Hmem"; eauto.
         simpl; iSplitL "Hpc_a"; auto.
     }

     destruct (readAllowed p && withinBounds ((p, g), b, e, a)) eqn:HRA; rewrite HRA in H5.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
       symmetry in H5; inversion H5; clear H5. subst c σ2.
       cbn. iFrame.
       iSpecialize ("Hφ" $! r FailedV). iApply "Hφ".
       iFrame. iSplitR.
       - iPureIntro. eapply Load_spec_failure; auto. eapply Load_fail_bounds; eauto.
         by apply andb_false_iff in HRA.
       - iDestruct ((big_sepM_delete _ _ pc_a) with "[Hpc_a Hmem]") as "Hmem"; eauto.
       simpl; iSplitL "Hpc_a"; auto.
     }

     (* Possible todo: map update without opening the map resources? Probably quite involved for the relatively low reusability *)
     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     iAssert (∃ p' loadv, ⌜mem !! a = Some(p', loadv)⌝ ∗ ⌜PermFlows p p'⌝)%I as %(p' & loadv & Hmema & HPFp).
     {
       unfold allow_load_map_or_true in HaLoad.
       destruct HaLoad as (?&?&?&?&?&[Hrr | Hrl]&?Hmem).
       - assert (Hrr' := Hrr). option_locate_mr_once m r. rewrite Hr2 in Hr2v; inversion Hr2v; subst.
         case_decide as HAL.
         * auto.
         * unfold reg_allows_load in HAL. apply andb_true_iff in HRA.
           destruct HAL; auto.
       - destruct Hrl as [z Hrl]. option_locate_mr m r. by congruence.
     }

     (* Given this, prove that a is also present in the memory itself *)
     iAssert (⌜m !m! a = loadv⌝)%I  with "[Hpc_a Hmem Hm]" as %Hma.
     {
       destruct (decide (a = pc_a)).
       - destruct e0.
         iDestruct (gen_heap_valid_cap with "Hm Hpc_a") as %?; auto.
         rewrite Hmema in Hmem_pc; inversion Hmem_pc. by option_locate_mr_once m r.
       - (*Ugly assert since iDestruct doesnt manage*)
         iAssert ((∃ (p0 : Perm) (w0 : Word), ⌜(p',loadv) = (p0, w0)⌝ ∗ a ↦ₐ[p0] w0)  ∗ ([∗ map] k↦y ∈ (delete a (delete pc_a mem)), ∃ (p0 : Perm) (w0 : Word), ⌜y = (p0, w0)⌝ ∗ k ↦ₐ[p0] w0))%I with "[Hmem]" as "[Hmem_a Hmem]".
         {rewrite -(big_sepM_delete _ _ a); auto. by rewrite lookup_delete_ne. }
         iDestruct "Hmem_a" as (p1 w1) "[% Hmem_a]". symmetry in H2; inversion H2; simplify_eq.
         iDestruct (gen_heap_valid_cap with "Hm Hmem_a") as %?; auto.
         {
          apply andb_true_iff in HRA; destruct HRA as (HRA & _); unfold readAllowed in HRA.
          destruct (decide (p = O)); first by simplify_eq.
          destruct (decide (p' = O)); last by simplify_eq. rewrite e0 in HPFp.
          destruct p; by exfalso.
          }
         by option_locate_mr_once m r.
     }

     rewrite Hma in H5.
     destruct (decide (∃ regs', incrementPC (<[ r1 := loadv ]> r) = Some regs')) as [[r' HIncrS]| HIncrN ].
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC (<[r1:=loadv]> r) = None) as HPCFail.
       {
         destruct (incrementPC (<[r1:=loadv]> r)); last by auto.
         destruct HIncrN. by exists r0.
       }
       rewrite incrementPC_fail_updatePC /= in H5; auto.
       symmetry in H5; inversion H5; clear H5. subst c σ2.
       cbn. iFrame.
       (* Update the heap resource, using the resource for r2 *)
       destruct (Hri r1) as [r0v Hr0].
       iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame.

       iSpecialize ("Hφ" $! (<[r1:=loadv]> r) FailedV). iApply "Hφ".
       iFrame. iSplitR.
       - iPureIntro. eapply Load_spec_failure; auto. eapply Load_fail_invalid_PC; eauto.
       - iDestruct ((big_sepM_delete _ _ pc_a) with "[Hpc_a Hmem]") as "Hmem"; eauto. simpl; iSplitL "Hpc_a"; auto.
     }

     (* Success *)
     clear Hstep. rewrite /update_reg /= in H5.
     eapply (incrementPC_success_updatePC _ m) in HIncrS
       as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     rewrite HuPC in H5; clear HuPC; inversion H5; clear H5; subst c σ2. cbn.
     iFrame.
     iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iSplitR "Hpc_a Hmem".
     - iPureIntro.  eapply Load_spec_success; auto.
       * split; auto. apply (regs_lookup_inr_eq r r2); auto.
         exact Hr2v.
         by apply andb_true_iff in HRA.
       * exact Hmema.
       * unfold incrementPC. by rewrite HPC'' Ha_pc'.
     - iDestruct ((big_sepM_delete _ _ pc_a) with "[Hpc_a Hmem]") as "Hmem"; eauto.
       simpl; iSplitL "Hpc_a"; auto.
   Qed.

  Lemma wp_load_success E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a'
        pc_p' p' :
    cap_lang.decode w = Load r1 r2 →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ w''  
          ∗ ▷ r2 ↦ᵣ inr ((p,g),b,e,a)
          ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↦ₐ[p'] w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ (if (eqb_addr a pc_a) then w else w')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ inr ((p,g),b,e,a)
             ∗ (if (eqb_addr a pc_a) then emp else a ↦ₐ[p'] w') }}}. 
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc [Hra Hwb] Hpca' Hne1 φ)
            "(>Hpc & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    assert (p' ≠ O) as Ho'.
    { destruct p'; auto. destruct p; inversion Hfl'. inversion Hra. }
    (* iDestruct (@gen_heap_valid_cap with "Hm Hr2a") as %?; auto.  *)
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto.
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r. 
    assert (<[r1:=m !m! a]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) r1 (MemLocate m a))).2,[].
      rewrite /updatePC Hpc_new1 /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r2)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence. 
      rewrite /withinBounds in Hwb; rewrite Hr2 Hra Hwb /updatePC /= Hpc_new1.
      by rewrite Hpca' /update_reg /=.
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      destruct (a =? pc_a)%a eqn:Heq.
      + iModIntro. iNext.
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hr2 Hra Hwb /update_reg /updatePC /= Hpc_new1 /=.
        inv_head_step.
        rewrite Hr2 Hra Hwb /= /update_reg /updatePC /= Hpc_new1 /update_reg /= in Hstep. 
        iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
        iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
        iSpecialize ("Hφ" with "[Hpc Hr1 Hr2 Hi Hr2a]"); iFrame.
        apply Z.eqb_eq,z_of_eq in Heq. by rewrite Heq.
        auto.
      + iModIntro. iNext.
        iDestruct (@gen_heap_valid_cap with "Hm Hr2a") as %?; auto.
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hr2 Hra Hwb /update_reg /updatePC /= Hpc_new1 /=.
        inv_head_step.
        rewrite Hr2 Hra Hwb /= /update_reg /updatePC /= Hpc_new1 /update_reg /= in Hstep. 
        iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
        iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
        iSpecialize ("Hφ" with "[Hpc Hr1 Hr2 Hi Hr2a]"); iFrame.
        option_locate_mr m r. rewrite Ha. done. auto. 
  Qed.

  Lemma wp_load_success_same E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a'
        pc_p' p' :
    cap_lang.decode w = Load r1 r1 →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
          ∗ (if (a =? pc_a)%a then emp else ▷ a ↦ₐ[p'] w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ (if (a =? pc_a)%a then w else w')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if (a =? pc_a)%a then emp else a ↦ₐ[p'] w') }}}. 
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc [Hra Hwb] Hpca' Hne1 φ)
            "(>Hpc & >Hi & >Hr1 & Hr1a) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    assert (p' ≠ O) as Ho'.
    { destruct p'; auto. destruct p; inversion Hfl'. inversion Hra. }
    (* iDestruct (@gen_heap_valid_cap with "Hm Hr1a") as %?; auto.  *)
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r. 
    assert (<[r1:=m !m! a]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) r1 (MemLocate m a))).2,[].
      rewrite /updatePC Hpc_new1 /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r1)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence. 
      rewrite /withinBounds in Hwb; rewrite Hr1 Hra Hwb /updatePC /= Hpc_new1.
        by rewrite Hpca' /update_reg /=.
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)
      destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq,z_of_eq in Heq as ->. 
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hr1 Hra Hwb /update_reg /updatePC /= Hpc_new1 /=.
        inv_head_step.
        iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
        iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
        iSpecialize ("Hφ" with "[Hpc Hr1 Hi Hr1a]"); iFrame.  
        iModIntro. done.
      + iDestruct "Hr1a" as ">Hr1a".
        iDestruct (@gen_heap_valid_cap with "Hm Hr1a") as %?; auto. 
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        option_locate_mr m r. 
        rewrite Hr1 Hra Hwb /update_reg /updatePC /= Hpc_new1 /=.
        inv_head_step.
        iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
        iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
        iSpecialize ("Hφ" with "[Hpc Hr1 Hi Hr1a]"); iFrame.  
        iModIntro. done.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a p' g' b' e' a' a'' pc_p' p'' :
    cap_lang.decode w = Load PC r2 →
    PermFlows pc_p pc_p' →
    PermFlows p p'' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r2 ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ[p''] inr ((p',g'),b',e',a') }}} 
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((p',g'),b',e',a'')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ inr ((p,g),b,e,a)
             ∗ a ↦ₐ[p''] inr ((p',g'),b',e',a') }}}. 
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc [Hra Hwb] Ha'' φ)
            "(>Hpc & >Hi & >Hr2 & >Hr2a) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    assert (p'' ≠ O) as Ho'.
    { destruct p''; auto. destruct p; inversion Hfl'. inversion Hra. }
    iDestruct (@gen_heap_valid_cap with "Hm Hr2a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r. 
    assert (<[PC:=m !m! a]> r !r! PC = m !m! a)
      as Hpc_new1.
    { rewrite (locate_eq_reg _ _ (r !r! PC)); eauto. } 
    iApply fupd_frame_l. 
    iSplit.
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) PC (MemLocate m a))).2,[].
      rewrite /updatePC Hpc_new1 Ha /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load PC r2)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence. 
      rewrite /withinBounds in Hwb; rewrite Hr2 Hra Hwb /updatePC /= Hpc_new1.
        by rewrite Ha /update_reg /= Ha''.
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hr2 Hra Hwb /update_reg /updatePC /= Hpc_new1 Ha Ha'' /= insert_insert.
      inv_head_step.
      iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
      iSpecialize ("Hφ" with "[Hpc Hi Hr2 Hr2a]"); iFrame.  
      iModIntro. done. 
  Qed.

  Lemma wp_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' pc_p' :
    cap_lang.decode w = Load r1 PC →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ w'' }}} 
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ w }}}. 
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpc_a' Hne φ)
            "(>Hpc & >Hi & >Hr1) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r. 
    assert (<[r1:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a) = true).
    { by apply Is_true_eq_true,(isCorrectPC_ra_wb _ pc_g). }
    iApply fupd_frame_l. 
    iSplit.
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) r1 (MemLocate m pc_a))).2,[].
      rewrite /updatePC Hpc_a Hpc_new1 Hpc_a' /=. 
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 PC)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence.
        by rewrite /update_reg /updatePC HPC H1 Hpc_a Hpc_new1 Hpc_a' /=. 
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /update_reg /updatePC HPC H1 Hpc_a Hpc_new1 Hpc_a' /=. 
      inv_head_step.
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
      iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
      iSpecialize ("Hφ" with "[Hpc Hi Hr1]"); iFrame.  
      iModIntro. done. 
  Qed.  

  Lemma wp_load_fail1 E r1 r2 pc_p pc_g pc_b pc_e pc_a w p g b e a pc_p' :
    cap_lang.decode w = Load r1 r2 →

    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ∧
    (readAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ r2 ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
                          ∗ pc_a ↦ₐ[pc_p'] w
                          ∗ r2 ↦ᵣ inr ((p,g),b,e,a) }}}.
  Proof.
    intros Hinstr Hfl [Hvpc [Hnra | Hnwb]];
      (iIntros (φ) "(HPC & Hpc_a & Hr2) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid with "Hr Hr2") as %?;
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
       option_locate_mr m r).  
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }               
    - iApply fupd_frame_l.
      iSplit.
      + rewrite /reducible.
        iExists [], (Instr Failed), (r,m), [].
        iPureIntro.
        constructor.
        apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r2)
                               (Failed,_));
          eauto; simpl; try congruence.
          by rewrite Hr2 Hnra /=.
      + (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
        iModIntro.
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
        rewrite Hr2 Hnra /=.
        iFrame. iNext. iModIntro.
        iSplitR; auto. iApply "Hφ". iFrame.
    - destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr.
    - simpl in *.
      iApply fupd_frame_l.
      iSplit.
      + rewrite /reducible.
        iExists [], (Instr Failed), (r,m), [].
        iPureIntro.
        constructor.
        apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r2)
                               (Failed,_));
          eauto; simpl; try congruence.
          by rewrite Hr2 Hnwb andb_false_r.
      + (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
        iModIntro.
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
        rewrite Hr2 Hnwb andb_false_r.
        iFrame. iNext.
        iSplitR; auto. iApply "Hφ". iFrame. auto. 
  Qed.

  Lemma wp_load_fail2 E r1 r2 pc_p pc_g pc_b pc_e pc_a w n pc_p' :
    cap_lang.decode w = Load r1 r2 →

    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ r2 ↦ᵣ inl n }}}
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, pc_a)
                          ∗ pc_a ↦ₐ[pc_p'] w
                          ∗ r2 ↦ᵣ inl n }}}.
  Proof.
    intros Hinstr Hfl Hvpc.
    iIntros (φ) "(HPC & Hpc_a & Hr2) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
        iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?;
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?;
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
     option_locate_mr m r.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }     
    iApply fupd_frame_l. iSplit.
    - rewrite /reducible.
      iExists [], (Instr Failed), (r,m), [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r2)
                              (Failed,_));
        eauto; simpl; try congruence.
        by rewrite Hr2.
    - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
      iModIntro.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      rewrite Hr2 /=.
      iFrame. iNext. iModIntro. 
      iSplitR; eauto. iApply "Hφ". iFrame. 
  Qed.

  Lemma wp_load_fail3 E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Load PC PC →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ w
                          ∗ pc_a ↦ₐ[pc_p'] w }}}. 
  Proof.
    iIntros (Hinstr Hfl Hvpc φ)
            "(>Hpc & >Hi) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }     
    option_locate_mr m r. 
    assert (<[PC:=m !m! pc_a]> r !r! PC = m !m! pc_a)
      as Hpc_new1.
    { rewrite (locate_eq_reg _ _ (r !r! PC)); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a) = true).
    { apply Is_true_eq_true. by apply (isCorrectPC_ra_wb _ pc_g). }
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [],(Instr Failed), (_,m), [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load PC PC)
                             (Failed,_));
        eauto; simpl; try congruence.
      rewrite HPC H1 /updatePC /update_reg /= Hpc_new1 Hpc_a.
      destruct w; auto.
      rewrite cap_lang.decode_cap_fail in Hinstr. 
      inversion Hinstr. 
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite HPC H1 /updatePC /update_reg /= Hpc_new1 Hpc_a.
      destruct w.
      + inv_head_step.
        iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]". iFrame. 
        iModIntro. iSplitR; auto. iApply "Hφ". iFrame. 
      + rewrite cap_lang.decode_cap_fail in Hinstr. 
        inversion Hinstr. 
  Qed.

  Lemma wp_load_fail4 E src pc_p pc_g pc_b pc_e pc_a w p g b e a p' g' b' e' a'
        pc_p' p'' :
    cap_lang.decode w = Load PC src →
    PermFlows pc_p pc_p' →
    PermFlows p p'' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (a' + 1)%a = None →
    PC ≠ src →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ src ↦ᵣ inr ((p,g),b,e,a)
          ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↦ₐ[p''] inr ((p',g'),b',e',a')) }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ (if (eqb_addr a pc_a) then w else inr ((p',g'),b',e',a'))
                          ∗ pc_a ↦ₐ[pc_p'] w
                          ∗ src ↦ᵣ inr ((p,g),b,e,a)
                          ∗ (if (eqb_addr a pc_a) then emp else a ↦ₐ[p''] inr ((p',g'),b',e',a')) }}}. 
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc [Hra Hwb] Hnone Hne φ)
            "(>Hpc & >Hi & >Hsrc & Ha) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    assert (p'' ≠ O) as Ho'.
    { destruct p''; auto. destruct p; inversion Hfl'. inversion Hra. }
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto.
    destruct (a =? pc_a)%a eqn:Heq.
    { apply Z.eqb_eq, z_of_eq in Heq. 
      option_locate_mr m r. 
      assert (<[PC:=m !m! a]> r !r! PC = m !m! a)
        as Hpc_new1.
      { rewrite (locate_eq_reg _ _ (r !r! PC)); eauto. }
      iApply fupd_frame_l. 
      iSplit.  
      - rewrite /reducible. 
        iExists [],(Instr Failed), (_,m), [].
        iPureIntro.
        constructor.
        apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load PC src)
                               (Failed,_));
          eauto; simpl; try congruence. simpl in *. 
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Heq Hpc_a.
        destruct w; auto.
        rewrite decode_cap_fail in Hinstr. inversion Hinstr. 
      - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Heq Hpc_a /=.
        destruct w;
          last (rewrite decode_cap_fail in Hinstr;inversion Hinstr); simpl.
        iFrame. iSplitR; auto.
        iMod (@gen_heap_update with "Hr Hpc") as "[Hr Hpc]". iFrame.
        iModIntro. iApply "Hφ". iFrame. 
    }
    { iDestruct "Ha" as ">Ha". 
      iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto.
      option_locate_mr m r. 
      assert (<[PC:=m !m! a]> r !r! PC = m !m! a)
        as Hpc_new1.
      { rewrite (locate_eq_reg _ _ (r !r! PC)); eauto. }
      iApply fupd_frame_l. 
      iSplit.  
      - rewrite /reducible. 
        iExists [],(Instr Failed), (_,m), [].
        iPureIntro.
        constructor.
        apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load PC src)
                               (Failed,_));
          eauto; simpl; try congruence. simpl in *. 
        by rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Ha Hnone.
      - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Ha Hnone /=.
        iFrame. iSplitR; auto.
        iMod (@gen_heap_update with "Hr Hpc") as "[Hr Hpc]". iFrame.
        iModIntro. iApply "Hφ". iFrame. 
    }
  Qed.

  Lemma wp_load_fail5 E src pc_p pc_g pc_b pc_e pc_a w p g b e a z pc_p' p' :
    cap_lang.decode w = Load PC src →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    PC ≠ src →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ src ↦ᵣ inr ((p,g),b,e,a)
          ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↦ₐ[p'] inl z) }}} 
      Instr Executable @ E
      {{{ RET FailedV; (if (eqb_addr a pc_a) then PC ↦ᵣ w else PC ↦ᵣ inl z)
                          ∗ pc_a ↦ₐ[pc_p'] w
                          ∗ src ↦ᵣ inr ((p,g),b,e,a)
                          ∗ (if (eqb_addr a pc_a) then emp else a ↦ₐ[p'] inl z) }}}. 
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc [Hra Hwb] Hne φ)
            "(>Hpc & >Hi & >Hsrc & Ha) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    assert (p' ≠ O) as Ho'.
    { destruct p'; auto. destruct p; inversion Hfl'. inversion Hra. }
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto.
    destruct (a =? pc_a)%a eqn:Heq.
    { apply Z.eqb_eq,z_of_eq in Heq.
      option_locate_mr m r. 
      assert (<[PC:=m !m! a]> r !r! PC = m !m! a)
        as Hpc_new1.
      { rewrite (locate_eq_reg _ _ (r !r! PC)); eauto. }
      iApply fupd_frame_l.
      assert (∃ z, w = inl z) as [z' ->].
      { destruct w; eauto. by rewrite decode_cap_fail in Hinstr. }
      iSplit.  
      - rewrite /reducible.
        iExists [],(Instr Failed), ((<[PC:= m !m! a]> r),m), [].
        iPureIntro.
        constructor.
        apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load PC src)
                               (Failed,_));
          eauto; simpl; try congruence. simpl in *.
          (* destruct (decide (pc_a = a)); simplify_eq.  *)
          (* + rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1.  *)
          by rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Heq Hpc_a.
      - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 /= Heq Hpc_a.
        iFrame. iSplitR; auto.
        iMod (@gen_heap_update with "Hr Hpc") as "[Hr Hpc]". iFrame.
        iModIntro. iApply "Hφ". iFrame.
    }
    { iDestruct "Ha" as ">Ha".  
      iDestruct (@gen_heap_valid_cap with "Hm Ha") as "%"; auto.
       option_locate_mr m r. 
       assert (<[PC:=m !m! a]> r !r! PC = m !m! a)
         as Hpc_new1.
       { rewrite (locate_eq_reg _ _ (r !r! PC)); eauto. }
       iApply fupd_frame_l.
       iSplit.  
      - rewrite /reducible.
        iExists [],(Instr Failed), ((<[PC:= m !m! a]> r),m), [].
        iPureIntro.
        constructor.
        apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load PC src)
                               (Failed,_));
          eauto; simpl; try congruence. simpl in *.
        (* destruct (decide (pc_a = a)); simplify_eq.  *)
        (* + rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1.  *)
        by rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Ha.
      - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Ha /=.
        iFrame. iSplitR; auto.
        iMod (@gen_heap_update with "Hr Hpc") as "[Hr Hpc]". iFrame.
        iModIntro. iApply "Hφ". iFrame.
    }
  Qed.

  Lemma wp_load_fail6 E dst pc_p pc_g pc_b pc_e pc_a w w' pc_p' :
    cap_lang.decode w = Load dst PC →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    PC ≠ dst →
    (pc_a + 1)%a = None →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ dst ↦ᵣ w' }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
                          ∗ pc_a ↦ₐ[pc_p'] w
                          ∗ dst ↦ᵣ w }}}. 
  Proof.
    iIntros (Hinstr Hfl Hvpc Hne Hpc_a' φ)
            "(>Hpc & >Hi & >Hdst) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto. 
    option_locate_mr m r. 
    assert (∀ a, <[dst:=m !m! a]> r !r! PC = r !r! PC)
      as Hpc_new1.
    { intros a.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a) = true).
    { by apply Is_true_eq_true,(isCorrectPC_ra_wb _ pc_g). }
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [],(Instr Failed), (_,m), [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load dst PC)
                             (Failed,_));
        eauto; simpl; try congruence. simpl in *.
      rewrite HPC H1 /updatePC /update_reg Hpc_new1 HPC Hpc_a' /=. eauto. 
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite HPC H1 /updatePC /update_reg Hpc_new1 HPC Hpc_a' Hpc_a /=.
      iFrame. iSplitR; auto.
      iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]". iFrame.
      iModIntro. iApply "Hφ". iFrame. 
  Qed.

  Lemma wp_load_fail7 E src dst pc_p pc_g pc_b pc_e pc_a w w' p g b e a w'' pc_p' p' :
    cap_lang.decode w = Load dst src →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    PC ≠ dst →
    (pc_a + 1)%a = None →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ src ↦ᵣ inr ((p,g),b,e,a)
          ∗ (if (a =? pc_a)%a then emp else ▷ a ↦ₐ[p'] w'')
          ∗ ▷ dst ↦ᵣ w' }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
                          ∗ pc_a ↦ₐ[pc_p'] w
                          ∗ src ↦ᵣ inr ((p,g),b,e,a)
                          ∗ (if (a =? pc_a)%a then emp else a ↦ₐ[p'] w'')
                          ∗ dst ↦ᵣ (if (a =? pc_a)%a then w else w'') }}}. 
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc [Hra Hwb] Hne Hpc_a' φ)
            "(>Hpc & >Hi & >Hsrc & Ha & >Hdst) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    assert (p' ≠ O) as Ho'.
    { destruct p'; auto. destruct p; inversion Hfl'. inversion Hra. }
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto. 
    (* iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto.  *)
    option_locate_mr m r. 
    assert (∀ a, <[dst:=m !m! a]> r !r! PC = r !r! PC)
      as Hpc_new1.
    { intros a0.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a) = true).
    { by apply Is_true_eq_true,(isCorrectPC_ra_wb _ pc_g). }
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [],(Instr Failed), (_,m), [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load dst src)
                             (Failed,_));
        eauto; simpl; try congruence. simpl in *.
      rewrite Hsrc Hra Hwb /= /updatePC /update_reg Hpc_new1 HPC Hpc_a' /=. eauto. 
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)
      destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq,z_of_eq in Heq as ->. 
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg Hpc_new1 HPC Hpc_a' Hpc_a /=.
        iFrame. iSplitR; auto.
        iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]". iFrame.
        iModIntro. iApply "Hφ". iFrame.
      + iDestruct "Ha" as ">Ha".
        iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto.
        option_locate_mr m r.
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg Hpc_new1 HPC Hpc_a' Ha /=.
        iFrame. iSplitR; auto.
        iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]". iFrame.
        iModIntro. iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail8 E src pc_p pc_g pc_b pc_e pc_a w w' p g b e a w'' pc_p' p' :
    cap_lang.decode w = Load src src →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    PC ≠ src →
    (pc_a + 1)%a = None →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ src ↦ᵣ inr ((p,g),b,e,a)
          ∗ if (a =? pc_a)%a then emp else ▷ a ↦ₐ[p'] w'' }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
                          ∗ pc_a ↦ₐ[pc_p'] w
                          ∗ src ↦ᵣ (if (a =? pc_a)%a then w else w'')
                          ∗ if (a =? pc_a)%a then emp else a ↦ₐ[p'] w'' }}}. 
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc [Hra Hwb] Hne Hpc_a' φ)
            "(>Hpc & >Hi & >Hsrc & Ha) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    assert (p' ≠ O) as Ho'.
    { destruct p'; auto. destruct p; inversion Hfl'. inversion Hra. }
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hi") as %?; auto. 
    (* iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto. *)
    option_locate_mr m r. 
    assert (∀ a, <[src:=m !m! a]> r !r! PC = r !r! PC)
      as Hpc_new1.
    { intros a0.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a) = true).
    { by apply Is_true_eq_true,(isCorrectPC_ra_wb _ pc_g). }
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [],(Instr Failed), (_,m), [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load src src)
                             (Failed,_));
        eauto; simpl; try congruence. simpl in *.
      rewrite Hsrc Hra Hwb /= /updatePC /update_reg Hpc_new1 HPC Hpc_a' /=. eauto. 
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq,z_of_eq in Heq as ->. 
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg Hpc_new1 HPC Hpc_a Hpc_a' /=.
        iFrame. iSplitR; auto.
        iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]". iFrame.
        iModIntro. iApply "Hφ". iFrame.
      + iDestruct "Ha" as ">Ha". 
        iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto.
        iModIntro. iNext. 
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        option_locate_mr m r. 
        rewrite Hsrc Hra Hwb /= /updatePC /update_reg Hpc_new1 HPC Hpc_a' Ha /=.
        iFrame. iSplitR; auto.
        iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]". iFrame.
        iModIntro. iApply "Hφ". iFrame.
  Qed.

End cap_lang_rules.
