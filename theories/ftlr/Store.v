From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel monotone.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation WORLD := (leibnizO (STS_states * STS_rels)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  Ltac option_locate_mr m r :=
    repeat match goal with
           | H : m !! ?a = Some ?w |- _ => let Ha := fresh "H"a in
                                         assert (m !m! a = w) as Ha; [ by (unfold MemLocate; rewrite H) | clear H]
           | H : r !! ?a = Some ?w |- _ => let Ha := fresh "H"a in
                                         assert (r !r! a = w) as Ha; [ by (unfold RegLocate; rewrite H) | clear H]
           end.

  Ltac inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1 :=
    match goal with
    | H : cap_lang.prim_step (Instr Executable) (r, m) _ ?e1 ?σ2 _ |- _ =>
      let σ := fresh "σ" in
      let e' := fresh "e'" in
      let σ' := fresh "σ'" in
      let Hstep' := fresh "Hstep'" in
      let He0 := fresh "He0" in
      let Ho := fresh "Ho" in
      let He' := fresh "H"e' in
      let Hσ' := fresh "H"σ' in
      let Hefs := fresh "Hefs" in
      let φ0 := fresh "φ" in
      let p0 := fresh "p" in
      let g0 := fresh "g" in
      let b0 := fresh "b" in
      let e2 := fresh "e" in
      let a0 := fresh "a" in
      let i := fresh "i" in
      let c0 := fresh "c" in
      let HregPC := fresh "HregPC" in
      let Hi := fresh "H"i in
      let Hexec := fresh "Hexec" in 
      inversion Hstep as [ σ e' σ' Hstep' He0 Hσ Ho He' Hσ' Hefs |?|?|?]; 
      inversion Hstep' as [φ0 | φ0 p0 g0 b0 e2 a0 i c0 HregPC ? Hi Hexec];
      (simpl in *; try congruence );
      subst e1 σ2 φ0 σ' e' σ; try subst c0; simpl in *;
      try (rewrite HPC in HregPC;
           inversion HregPC;
           repeat match goal with
                  | H : _ = p0 |- _ => destruct H
                  | H : _ = g0 |- _ => destruct H
                  | H : _ = b0 |- _ => destruct H
                  | H : _ = e2 |- _ => destruct H
                  | H : _ = a0 |- _ => destruct H
                  end ; destruct Hi ; clear HregPC ;
           rewrite Hpc_a Hinstr /= ;
           rewrite Hpc_a Hinstr in Hstep)
    end.
  
  Lemma wp_store_success_z_PC E pc_p pc_p' pc_g pc_b pc_e pc_a pc_a' w z :
     cap_lang.decode w = Store PC (inl z) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] (inl z) }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hwa ϕ) "(>HPC & >Hpc_a) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     apply isCorrectPC_ra_wb in Hvpc as Hrawb.
     apply Is_true_eq_true, andb_true_iff in Hrawb as [Hra Hwb]. 
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc as [?????? Heq]; subst.
         destruct Heq as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) pc_a (inl z))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store PC (inl z))
                              (NextI,_)); eauto; simpl; try congruence.
       inversion Hvpc as [????? [Hwb1 Hwb2] ]; subst.
       by rewrite HPC Hwa Hwb /= /updatePC /update_mem /= HPC Hpca'.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hwa Hwb /= /updatePC /update_mem /update_reg HPC Hpca' /=.
       iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
       { apply PermFlows_trans with pc_p;auto. }
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame; eauto.
   Qed.

   Lemma wp_store_success_reg_PC E src wsrc pc_p pc_p' pc_g pc_b pc_e pc_a pc_a' w :
     cap_lang.decode w = Store PC (inr src) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     (isLocalWord wsrc = false ∨ (pc_p = RWL ∨ pc_p = RWLX)) ->

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ src ↦ᵣ wsrc }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] wsrc
              ∗ src ↦ᵣ wsrc }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hwa Hlocal ϕ) "(>HPC & >Hpc_a & >Hsrc) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     apply isCorrectPC_ra_wb in Hvpc as Hrawb.
     apply Is_true_eq_true, andb_true_iff in Hrawb as [Hra Hwb]. 
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc as [?????? Heq]; subst.
         destruct Heq as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) pc_a _)).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store PC (inr src))
                              (NextI,_)); eauto; simpl; try congruence.
       inversion Hvpc as [????? [Hwb1 Hwb2] ]. subst p g b e a. 
       rewrite Hsrc HPC Hwa Hwb /= /updatePC /update_mem /= HPC Hpca'.
       destruct wsrc; eauto. destruct c,p,p,p. 
       destruct Hlocal as [Hl | Hpc_p].
       + by simpl in Hl; rewrite Hl.
       + destruct (isLocal l); auto.
         destruct Hpc_p as [-> | ->]; auto. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hsrc Hwa Hwb /= /updatePC /update_mem /update_reg HPC Hpca' /=.
       destruct wsrc; eauto; simpl.
       + iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
         { apply PermFlows_trans with pc_p;auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame; eauto. 
       + destruct c,p,p,p.
         destruct Hlocal as [Hl | Hpc_p].
         * simpl in Hl; rewrite Hl /=.
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
           { apply PermFlows_trans with pc_p;auto. destruct l; auto. inversion Hl. }
           iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
           iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame; eauto. 
         * destruct Hpc_p as [-> | ->].
           { destruct (isLocal l); simpl;
             (iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto;
               [apply PermFlows_trans with RWL;auto;destruct l; auto|];
               iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame; eauto).
           }
           { destruct (isLocal l); simpl;
             (iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto;
               [apply PermFlows_trans with RWLX;auto;destruct l; auto|];
               iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame; eauto).
           }
   Qed.

   Lemma wp_store_fail_z_PC_1 E z pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Store PC (inl z) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    writeAllowed pc_p = true ∧ withinBounds (pc_p, pc_g, pc_b, pc_e, pc_a) = true →
    (pc_a + 1)%a = None →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc [Hwa Hwb] Hnext.
     iIntros (φ) "(HPC & Hpc_a) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     option_locate_mr m r.
     iApply fupd_frame_l. iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,(update_mem (r, m) pc_a (inl z)).2), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store PC (inl z))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb. by rewrite HPC Hwa Hwb /updatePC /= HPC Hnext.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite HPC Hwa Hwb /updatePC /= HPC Hnext.
       iNext.
       iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
       { destruct pc_p,pc_p'; inversion Hwa; inversion Hfl; auto. }
       { apply PermFlows_trans with pc_p;auto. }
       iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".  
   Qed.

   Lemma wp_store_fail_reg_PC_1 E src wsrc pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Store PC (inr src) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    writeAllowed pc_p = true ∧ withinBounds (pc_p, pc_g, pc_b, pc_e, pc_a) = true →
    (isLocalWord wsrc = false ∨ (pc_p = RWL ∨ pc_p = RWLX)) → 
    (pc_a + 1)%a = None →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ src ↦ᵣ wsrc }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc [Hwa Hwb] Hlocal Hnext.
     iIntros (φ) "(HPC & Hpc_a & Hsrc) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid with "Hr Hsrc") as %?;
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     option_locate_mr m r.
     iApply fupd_frame_l. iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,(update_mem (r, m) pc_a wsrc).2), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store PC (inr src))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb. rewrite HPC Hsrc Hwa Hwb /updatePC /= HPC Hnext.
       destruct wsrc; eauto. destruct c,p,p,p. simpl in Hlocal. 
       destruct Hlocal as [Hl | Hpc_p].
       + by rewrite Hl.
       + destruct (isLocal l); auto. destruct Hpc_p as [-> | ->]; auto. 
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite HPC Hsrc Hwa Hwb /updatePC /= HPC Hnext.
       iNext.
       destruct wsrc; eauto; simpl.
       + iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
         { destruct pc_p,pc_p'; inversion Hwa; inversion Hfl; auto. }
         { apply PermFlows_trans with pc_p;auto. }
         iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
       + destruct c,p,p,p. simpl in Hlocal. 
         destruct Hlocal as [Hl | Hpc_p].
         * rewrite Hl /=.
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
           { destruct pc_p,pc_p'; inversion Hwa; inversion Hfl; auto. }
           { apply PermFlows_trans with pc_p;auto. destruct l; auto. inversion Hl. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         * destruct (isLocal l) eqn:Hl; auto.
           { destruct Hpc_p as [-> | ->]; simpl.
             - iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
               { destruct pc_p'; inversion Hfl; auto. }
               { apply PermFlows_trans with RWL;auto. destruct l; auto. }
               iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
             - iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
               { destruct pc_p'; inversion Hfl; auto. }
               { apply PermFlows_trans with RWLX;auto. destruct l; auto. }
               iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
           }
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
           { destruct pc_p,pc_p'; inversion Hwa; inversion Hfl; auto. }
           { apply PermFlows_trans with pc_p;auto. destruct l; auto. inversion Hl. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
   Qed.

    Lemma wp_store_fail_PC_PC_1 E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Store PC (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    writeAllowed pc_p = true ∧ withinBounds (pc_p, pc_g, pc_b, pc_e, pc_a) = true →
    (isLocal pc_g = false ∨ (pc_p = RWL ∨ pc_p = RWLX)) → 
    (pc_a + 1)%a = None →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc [Hwa Hwb] Hlocal Hnext.
     iIntros (φ) "(HPC & Hpc_a) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     option_locate_mr m r.
     iApply fupd_frame_l. iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,(update_mem (r, m) pc_a _).2), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store PC (inr PC))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb. rewrite HPC Hwa Hwb /updatePC /= HPC Hnext.
       destruct Hlocal as [Hl | Hpc_p].
       + by rewrite Hl.
       + destruct (isLocal pc_g); auto. destruct Hpc_p as [-> | ->]; auto. 
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite HPC Hwa Hwb /updatePC /= HPC Hnext.
       iNext.
       destruct Hlocal as [Hl | Hpc_p].
       + rewrite Hl /=.
         iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
         { destruct pc_p,pc_p'; inversion Hwa; inversion Hfl; auto. }
         { apply PermFlows_trans with pc_p;auto. destruct pc_g; auto. inversion Hl. }
         iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
       + destruct (isLocal pc_g) eqn:Hl; auto.
         { destruct Hpc_p as [-> | ->]; simpl.
           - iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
             { destruct pc_p'; inversion Hfl; auto. }
             { apply PermFlows_trans with RWL;auto. destruct pc_g; auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
           - iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
             { destruct pc_p'; inversion Hfl; auto. }
             { apply PermFlows_trans with RWLX;auto. destruct pc_g; auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
         iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
         { destruct pc_p,pc_p'; inversion Hwa; inversion Hfl; auto. }
         { apply PermFlows_trans with pc_p;auto. destruct pc_g; auto. inversion Hl. }
         iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
   Qed. 
         
   Lemma wp_store_fail_PC3 E src pc_p pc_g pc_b pc_e pc_a w p' g' b' e' a' pc_p' :
     cap_lang.decode w = Store PC (inr src) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     writeAllowed pc_p = true ->
     withinBounds ((pc_p, pc_g), pc_b, pc_e, pc_a) = true →
     isLocal g' = true ->
     pc_p <> RWLX ->
     pc_p <> RWL ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ src ↦ᵣ inr ((p',g'),b',e',a') }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hwa Hwb Hloc Hnrwlx Hnrwl;
     (iIntros (φ) "(HPC & Hpc_a & Hsrc) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hsrc") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store PC (inr src))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb. rewrite HPC Hwa Hwb Hsrc Hloc /=. 
       destruct pc_p; try congruence.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite HPC Hwa Hwb Hsrc Hloc /=. 
       assert (X: match pc_p with
                    | RWL | RWLX =>
                        updatePC (update_mem (r, m) pc_a (inr (p', g', b', e', a')))
                    | _ => (Failed, (r, m))
                    end = (Failed, (r, m))) by (destruct pc_p; congruence).
       repeat rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_store_fail_PC_PC3 E pc_p pc_g pc_b pc_e pc_a w pc_p' :
     cap_lang.decode w = Store PC (inr PC) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     writeAllowed pc_p = true ->
     withinBounds ((pc_p, pc_g), pc_b, pc_e, pc_a) = true →
     isLocal pc_g = true ->
     pc_p <> RWLX ->
     pc_p <> RWL ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hwa Hwb Hloc Hnrwlx Hnrwl;
     (iIntros (φ) "(HPC & Hpc_a) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store PC (inr PC))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb. rewrite HPC Hwa Hwb Hloc /=. 
       destruct pc_p; try congruence.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite HPC Hwa Hwb Hloc /=. 
       assert (X: match pc_p with
                    | RWL | RWLX =>
                            updatePC (update_mem (r, m) pc_a
                                                 (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
                    | _ => (Failed, (r, m))
                    end = (Failed, (r, m))) by (destruct pc_p; congruence).
       repeat rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_store_success_reg_PC_same E pc_p pc_g pc_b pc_e pc_a pc_a' w w' pc_p' :
     cap_lang.decode w = Store PC (inr PC) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true ∧ withinBounds ((pc_p, pc_g), pc_b, pc_e, pc_a) = true →
     (isLocal pc_g = false ∨ (pc_p = RWLX ∨ pc_p = RWL)) →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] inr ((pc_p,pc_g),pc_b,pc_e,pc_a) }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' [Hwa Hwb] Hcond ϕ)
             "(>HPC & >Hpc_a ) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) pc_a (RegLocate r PC))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store PC (inr PC))
                              (NextI,_)); eauto; simpl; try congruence.
       simpl in Hwb.
       rewrite HPC Hwa Hwb /= /updatePC /update_mem /= HPC Hpca'.
       destruct Hcond as [Hfalse | Hlocal].
       + simpl in Hfalse. rewrite Hfalse. auto.
       + destruct (isLocal pc_g); auto.
         destruct Hlocal as [Hp | Hp]; simplify_eq; auto. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hwa Hwb /= /updatePC /update_mem /= HPC Hpca' /=.
       iSplitR; auto.
       destruct Hcond as [Hfalse | Hlocal].
       + rewrite Hfalse /=.
         iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
         { apply PermFlows_trans with pc_p; auto.
           destruct pc_p,pc_g; inversion Hwa; inversion Hfalse; auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
       + destruct (isLocal pc_g); simpl. 
         { destruct Hlocal as [Hp | Hp]; simplify_eq. 
           + assert (pc_p' = RWLX) as ->.
             { destruct pc_p'; auto; inversion Hfl. }
             iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]";
               [auto|destruct pc_g; auto|].
             iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
           + destruct pc_p'; inversion Hfl;
               (iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]";
                [auto|destruct pc_g; auto|];
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
                iSpecialize ("Hϕ" with "[-]"); iFrame; eauto). 
         } 
         iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto. 
         { apply PermFlows_trans with pc_p; auto. 
           destruct pc_p; inversion Hwa; destruct pc_g; inversion Hlocal;
             try congruence; auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
   Qed. 

   Lemma wp_store_fail_z2 E dst z pc_p pc_g pc_b pc_e pc_a w pc_p' p g b e a p' wa :
    cap_lang.decode w = Store dst (inl z) →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    writeAllowed p = true ∧ withinBounds (p, g, b, e, a) = true →
    (pc_a + 1)%a = None →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ if (a =? pc_a)%a then emp else a ↦ₐ[p'] wa }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hfl' Hvpc [Hwa Hwb] Hnext.
     iIntros (φ) "(HPC & Hpc_a & Hdst & Ha) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     option_locate_mr m r.
     iApply fupd_frame_l. iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,(update_mem (r, m) a (inl z)).2), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store dst (inl z))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb. by rewrite Hdst Hwa Hwb /updatePC /= HPC Hnext.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite Hdst Hwa Hwb /updatePC /= HPC Hnext.
       iNext.
       destruct (a =? pc_a)%a eqn:Heq. 
       + apply eqb_prop in Heq. rewrite Heq. ssimpl. 

       + iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
       { destruct p,p'; inversion Hwa; inversion Hfl; auto. }
       { apply PermFlows_trans with p;auto. }
       iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".  
   Qed.
   
  Lemma store_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm) 
        (g : Locality) (b e a : Addr) (w : Word) (dst : RegName) (src : Z + RegName) :
      p = RX ∨ p = RWX ∨ p = RWLX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a <= e)%a
    → PermFlows p p'
    → p' ≠ O
    → cap_lang.decode w = Store dst src
    -> □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
             full_map a2
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (a0, a1)) (a2 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a3, a4, a5, a6, a7)]> a2)
          -∗ region (a0, a1)
          -∗ sts_full a0 a1
          -∗ na_own logrel_nais ⊤
          -∗ ⌜a3 = RX ∨ a3 = RWX ∨ a3 = RWLX⌝
             → □ (∃ p'0 : Perm, ⌜PermFlows a3 p'0⌝
                    ∧ ([∗ list] a8 ∈ region_addrs a5 a6, read_write_cond a8 p'0 interp))
                 -∗ interp_conf a0 a1)
    -∗ ([∗ list] a0 ∈ region_addrs b e, read_write_cond a0 p' interp)
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (fs, fr)) (r !r! r1))
    -∗ read_write_cond a p' interp
    -∗ ▷ future_mono (λ Wv : prodO WORLD (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2)
    -∗ ▷ ((fixpoint interp1) (fs, fr)) w
    -∗ sts_full fs fr
    -∗ na_own logrel_nais ⊤
    -∗ open_region a (fs, fr)
    -∗ a ↦ₐ[p'] w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (fs' : STS_states) (fr' : STS_rels),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                           ∗ na_own logrel_nais ⊤
                                           ∗ sts_full fs' fr' ∗ region (fs', fr') }} }}.
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    (* for the successful writes from PC, we want to show that 
         the region can be closed again *)
    iAssert (((fixpoint interp1) (fs, fr)) (inr ((p,g),b,e,a)))%I
        as "#HPCw".
    { (* rewrite (fixpoint_interp1_eq _ (inr _)) /=.  *)
      (* destruct Hp as [-> | [-> | ->] ]; *)
      (* (iExists _,_,_,_; iSplitR;[eauto|]; *)
      (*  iExists p';do 2 (iSplit; auto); *)
      (*  iAlways;iIntros (a' r' W' Hin) "Hfuture"; *)
      (*  iNext; destruct W' as [fs' fr'];  *)
      (*  iExists _,_; do 2 (iSplitR; [auto|]);  *)
      (*  iIntros "(#[Hfull Hreg'] & Hmap & Hr & Hsts & Hna) /=";  *)
      (*  iExists _,_,_,_,_; iSplit;[eauto|]; *)
      (*  iApply ("IH" with "Hfull Hreg' Hmap Hr Hsts Hna"); auto). *)
      admit. 
    }
    destruct (reg_eq_dec dst PC).
    - subst dst.
       destruct Hp as [-> | Hp].
       { (* if p is RX, write is not allowed *)
         iApply (wp_store_fail1' with "[$HPC $Ha]"); eauto.
         iNext. iIntros (_).
         iApply wp_pure_step_later; auto. iNext.
         iApply wp_value. iIntros. discriminate. }
      destruct src.
      + (* successful inl write into a *)
        destruct (a + 1)%a eqn:Hnext. 
        { (* successful PC increment *)
          iApply (wp_store_success_z_PC with "[$HPC $Ha]"); eauto;
            [by destruct Hp as [-> | ->]|].
          iNext. iIntros "[HPC Ha]".
          iApply wp_pure_step_later; auto; iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
          { iSplitR;[auto|]. rewrite (fixpoint_interp1_eq _ (inl _)) /=. eauto. }
          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
            as "Hmap"; [by rewrite lookup_delete|].
          rewrite insert_delete. 
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; auto. 
        }
        { (* failure to increment PC *)
          iApply (wp_store_fail_z_PC_1 with "[$HPC $Ha]"); eauto.
          { split; [destruct Hp as [-> | ->]; auto|].
            destruct Hbae as [Hb He]. 
            apply andb_true_iff; split; apply Zle_is_le_bool; auto. 
          }
          iNext. iIntros (_).
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate.
        }
      + destruct (Hsome r0) as [wdst Hsomedst].
        destruct (reg_eq_dec r0 PC).
        * simplify_eq.
          destruct Hp as [-> | ->].
          ** destruct (isLocal g) eqn:Hlocal.
             *** (* failure: trying to write a local word without perm *)
               iApply (wp_store_fail_PC_PC3 with "[$HPC $Ha]"); eauto.
               { destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write into a: word is not local *)
                   iApply (wp_store_success_reg_PC_same with "[$HPC $Ha]"); eauto.
                   { split; auto. destruct Hbae as [Hb He]. 
                     apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
                   iNext. iIntros "[HPC Ha]".
                   iApply wp_pure_step_later; auto; iNext.
                   iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
                   { iSplitR;[auto|simpl].
                     rewrite (fixpoint_interp1_eq _ (inr _)) /=. eauto. }
                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|].
                   rewrite insert_delete. 
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                     iFrame "#"; auto. 
                 }
                 { (* failure to increment PC *)
                   destruct g; inversion Hlocal; auto.
                   iApply (wp_store_fail_PC_PC_1 with "[$HPC $Ha]"); eauto.
                   { split;auto. destruct Hbae as [Hb He]. 
                     apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
                   iNext. iIntros (_).
                   iApply wp_pure_step_later; auto. iNext.
                   iApply wp_value. iIntros. discriminate.
                 }
          ** destruct (a + 1)%a eqn:Hnext.
             { (* successful write into a: perm is local allowed *)
               iApply (wp_store_success_reg_PC_same with "[$HPC $Ha]"); eauto.
               { split; auto. destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros "[HPC Ha]".
               iApply wp_pure_step_later; auto; iNext.
               iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
               { iSplitR;[auto|]. rewrite (fixpoint_interp1_eq _ (inr _)) /=. eauto. }
               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|].
               rewrite insert_delete. 
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                 iFrame "#"; auto. 
             }
             { (* failure to increment PC *)
               iApply (wp_store_fail_PC_PC_1 with "[$HPC $Ha]"); eauto.
               { split;auto. destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.                   
             }
        * iDestruct ((big_sepM_delete _ _ r0) with "Hmap")
            as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
          destruct Hp as [-> | ->]. 
          ** destruct (isLocalWord wdst) eqn:Hlocal.
             *** (* failure: trying to write a local word without perm *)
               destruct wdst; first inversion Hlocal. destruct c,p,p,p.
               iApply (wp_store_fail_PC3 with "[$HPC $Ha $Hdst]"); eauto.
               { destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write into a: word is not local *)
                   iApply (wp_store_success_reg_PC with "[$HPC $Ha $Hdst]"); eauto.
                   iNext. iIntros "[HPC [Ha Hr0 ]]".
                   iApply wp_pure_step_later; auto; iNext.
                   iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
                   { iSplitR;[auto|simpl]. iSpecialize ("Hreg" $! r0 n). 
                     by rewrite /RegLocate Hsomedst. }
                   iDestruct ((big_sepM_insert) with "[$Hmap $Hr0]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   rewrite -delete_insert_ne; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                     iFrame "#"; auto.
                   - iPureIntro. intros r1.
                     destruct (decide (r0 = r1)); subst;
                       [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                   - iIntros (r1 Hne).
                     destruct (decide (r0 = r1)); subst; rewrite /RegLocate;
                       [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                     iSpecialize ("Hreg" $! r1 n). by rewrite Hsomedst.
                     iSpecialize ("Hreg" $! r1 Hne).
                     destruct (r !! r1); auto. 
                 }
                 { (* failure to increment PC *)
                   iApply (wp_store_fail_reg_PC_1 with "[$HPC $Ha $Hdst]"); eauto.
                   { split;auto. destruct Hbae as [Hb He]. 
                     apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
                   iNext. iIntros (_).
                   iApply wp_pure_step_later; auto. iNext.
                   iApply wp_value. iIntros. discriminate.       
                 }
          ** destruct (a + 1)%a eqn:Hnext.
             { (* successful write into a: perm is local allowed *)
               iApply (wp_store_success_reg_PC with "[$HPC $Ha $Hdst]"); eauto.
               iNext. iIntros "[HPC [Ha Hdst]]".
               iApply wp_pure_step_later; auto; iNext.
               iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
               { iSplitR;[auto|simpl]. iSpecialize ("Hreg" $! r0 n). 
                   by rewrite /RegLocate Hsomedst. }
               iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               rewrite -delete_insert_ne; auto.
               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                 iFrame "#"; auto.
               - iPureIntro. intros r1.
                 destruct (decide (r0 = r1)); subst;
                   [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
               - iIntros (r1 Hne).
                 destruct (decide (r0 = r1)); subst; rewrite /RegLocate;
                   [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                 iSpecialize ("Hreg" $! r1 n). by rewrite Hsomedst.
                 iSpecialize ("Hreg" $! r1 Hne).
                 destruct (r !! r1); auto.
             }
             { (* failure to increment PC *)
               iApply (wp_store_fail_reg_PC_1 with "[$HPC $Ha $Hdst]"); eauto.
               { split;auto. destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.       
             }
    - destruct (Hsome dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap")
        as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
      destruct wdst.
      { (* if dst does not contain cap, fail *)
        iApply (wp_store_fail2 with "[HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iIntros. discriminate. }
      destruct c,p0,p0,p0.
      case_eq (writeAllowed p0
               && withinBounds (p0,l,a2,a1,a0));  
        intros Hconds.
      + apply andb_true_iff in Hconds as [Hwa Hwb].
        destruct src.
        * destruct (a + 1)%a eqn:Hnext.
          { (* successful write into a0 *)
            destruct (decide (a = a0));[subst|].
            { admit. }
            { iDestruct (region_open_prepare with "Hr") as "Hr".
              iDestruct ("Hreg" $! dst n) as "#Hvdst".
              rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; apply Zle_is_le_bool; auto. }
              { destruct p0; inversion Hwa; auto. }
              iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                as (wa0) "(Hr & Ha0 & % & _)";
                [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
              iApply (wp_store_success_z with "[$HPC $Hdst $Ha $Ha0]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
              iApply wp_pure_step_later; auto. iNext.
              (* close the region *)
              iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..].
              { iSplitR;[auto|simpl]. rewrite (fixpoint_interp1_eq _ (inl _)). eauto. }
              iDestruct (region_open_prepare with "Hr") as "Hr". 
              iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
              iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               rewrite -delete_insert_ne; auto.
               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
              (* apply IH *)
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                 iFrame "#"; auto.
              - iPureIntro. intros r1.
                destruct (decide (dst = r1)); subst;
                  [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              - iIntros (r1 Hne).
                destruct (decide (dst = r1)); subst; rewrite /RegLocate;
                  [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                iSpecialize ("Hreg" $! r1 Hne).
                destruct (r !! r1); auto.
            } 
          }
          { (* failure to increment PC *)
            
          }
        * destruct (reg_eq_dec PC r0),(reg_eq_dec dst r0);
            first congruence; subst. 
          ** (* successful store of PC into a0 *)
            admit.
          ** case_eq (negb (isLocal l) || match p with
                                         | RWL | RWLX => true
                                         | _ => false end); intros Hconds'. 
             *** (* successful write from r0 into a0 *)
               admit.
             *** (* locality failure *)
               admit.
          ** destruct (Hsome r0) as [wsrc Hsomesrc].
             assert (delete PC r !! r0 = Some wsrc).
             { rewrite lookup_delete_ne; auto. }
             iDestruct ((big_sepM_delete _ _ r0) with "Hmap")
               as "[Hsrc Hmap]"; [rewrite lookup_delete_ne; eauto|].
             destruct wsrc.
             *** (* successful write from r0 into a0 *)
               admit.
             *** case_eq (negb (isLocalWord (inr c)) || match p0 with
                                                       | RWL | RWLX => true
                                                       | _ => false end); intros Hconds'. 
                 **** (* successful write from r0 into a0 *)
                   admit.
                 **** (* locality failure *)
                   admit.
      + (* write failure, either wrong permission or not within range *)
        admit.
  Admitted. 
             
   
End fundamental.