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

   Lemma wp_store_fail_reg_PC_2 E dst w' pc_p pc_g pc_b pc_e pc_a p g b e a w pc_p' p' :
    cap_lang.decode w = Store dst (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    writeAllowed p = true ∧ withinBounds (p, g, b, e, a) = true →
    (isLocal pc_g = false ∨ (p = RWL ∨ p = RWLX)) → 
    (pc_a + 1)%a = None →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr (p,g,b,e,a)
            ∗ if (pc_a =? a)%a then ⌜PermFlows p pc_p'⌝ else ⌜PermFlows p p'⌝ ∗ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc [Hwa Hwb] Hlocal Hnext.
     iIntros (φ) "(HPC & Hpc_a & Hsrc & Ha) Hφ".
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
       iExists [],(Instr Failed), (r,(update_mem (r, m) a (inr (pc_p,pc_g,pc_b,pc_e,pc_a))).2), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store dst (inr PC))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb. rewrite HPC Hdst Hwa Hwb /updatePC /update_mem /= HPC Hnext.
       destruct pc_g; eauto; simpl.
       destruct Hlocal as [Hl | Hpc_p].
       + destruct p; auto; inversion Hl. 
       + destruct Hpc_p as [-> | ->]; auto. 
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite HPC Hdst Hwa Hwb /updatePC /= HPC Hnext.
       iNext.
       destruct pc_g; eauto; simpl.
       + destruct (pc_a =? a)%a eqn:Heq.
         { iDestruct "Ha" as %Hfl'.
           apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
           { destruct p,pc_p'; inversion Hwa; inversion Hfl; auto. }
           { apply PermFlows_trans with p;auto. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
         { iDestruct "Ha" as (Hfl') "Ha".
           iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
           { destruct p,p'; inversion Hwa; inversion Hfl; auto. }
           { apply PermFlows_trans with p;auto. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
       + simpl in Hlocal. destruct Hlocal as [Hcontr | Hlocal]; [inversion Hcontr|].
         destruct (pc_a =? a)%a eqn:Heq.
         { iDestruct "Ha" as %Hfl'.
           apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
           destruct Hlocal as [-> | ->]; simpl.
           * iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
             { destruct pc_p'; inversion Hfl; auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
           * iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
             { destruct pc_p'; inversion Hfl; auto. }
             { apply PermFlows_trans with RWLX;auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
         { iDestruct "Ha" as (Hfl') "Ha".
           apply Z.eqb_neq in Heq. 
           destruct Hlocal as [-> | ->]; simpl.
           * iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
             { destruct p'; inversion Hfl'; auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
           * iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
             { destruct p'; inversion Hfl'; auto. }
             { apply PermFlows_trans with RWLX;auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
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
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    writeAllowed p = true ∧ withinBounds (p, g, b, e, a) = true →
    (pc_a + 1)%a = None →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ if (a =? pc_a)%a then ⌜PermFlows p pc_p'⌝ else
                ⌜PermFlows p p'⌝ ∗ a ↦ₐ[p'] wa }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc [Hwa Hwb] Hnext.
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
       + apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq. simpl.
         iDestruct "Ha" as %Ha.
         iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
         { destruct pc_p,pc_p'; inversion Ha; auto.
           inversion Hvpc as [?????? [Hcontr | [Hcontr | Hcontr] ] ]; inversion Hcontr. }
         { apply PermFlows_trans with p;auto. }
         iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".  
       + iDestruct "Ha" as (Hfl') "Ha". 
         iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
         { destruct p,p'; inversion Hwa; inversion Hfl; auto. }
         { apply PermFlows_trans with p;auto. }
         iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".  
   Qed.

    Lemma wp_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e pc_p' :
     cap_lang.decode w = Store dst (inl z) →
     PermFlows pc_p pc_p' →
     PermFlows p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, pc_a) = true →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] (inl z)
              ∗ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}}.
   Proof.
     iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hne ϕ) "(>HPC & >Hpc_a & >Hdst) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) pc_a (inl z))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store dst (inl z))
                              (NextI,_)); eauto; simpl; try congruence.
       simpl in Hwb.
       by rewrite Hdst Hwa Hwb /= /updatePC /update_mem /= HPC Hpca'.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hwa Hwb /= /updatePC /update_mem /update_reg /= HPC Hpca'.
       iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
       { apply PermFlows_trans with p;auto. }
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame; eauto.
   Qed.

   Lemma wp_store_success_reg' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a pc_p' p' :
      cap_lang.decode w = Store dst (inr PC) →
      PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     (isLocal pc_g = false ∨ (p = RWLX ∨ p = RWL)) →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ if (a =? pc_a)%a
             then ⌜PermFlows p pc_p'⌝
             else ⌜PermFlows p p'⌝ ∗ ▷ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] (if (a =? pc_a)%a
                               then (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))
                               else w)
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ if (a =? pc_a)%a
                then emp
                else a ↦ₐ[p'] (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' [Hwa Hwb] Hcond ϕ)
             "(>HPC & >Hpc_a & >Hdst & Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) a (RegLocate r PC))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store dst (inr PC))
                              (NextI,_)); eauto; simpl; try congruence.
       simpl in Hwb.
       rewrite Hdst Hwa Hwb /= /updatePC /update_mem /= HPC Hpca'.
       destruct Hcond as [Hfalse | Hlocal].
       + destruct pc_g; auto; simpl. inversion Hfalse. 
       + destruct pc_g; auto. destruct Hlocal as [Hp | Hp]; simplify_eq; auto. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hwa Hwb /= /updatePC /update_mem /= HPC Hpca' /=.
       iSplitR; auto.
       destruct pc_g; auto; simpl.
       + destruct (a =? pc_a)%a eqn:Heq.
         * apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
           iDestruct "Ha" as %Hfl'. 
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]".
           { destruct p; inversion Hwa; auto. }
           { apply PermFlows_trans with p; auto. }
           iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
           iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
         * apply Z.eqb_neq in Heq.
           iDestruct "Ha" as (Hfl') ">Ha". 
           iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]".
           { destruct p'; auto. destruct p; inversion Hwa; auto. }
           { apply PermFlows_trans with p; auto. }
           iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
           iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
       + destruct Hcond as [Hfalse | Hlocal].
         { simpl in Hfalse. inversion Hfalse. }
         destruct (a =? pc_a)%a eqn:Heq.
         * apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
           iDestruct "Ha" as %Hfl'. 
           destruct Hlocal as [Hp | Hp]; simplify_eq; simpl.           
           { iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; simpl; auto. 
             { apply PermFlows_trans with RWLX;auto. }
             iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[-]"); iFrame; eauto. }
           { iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; simpl; auto. 
             iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[-]"); iFrame; eauto. }
         * apply Z.eqb_neq in Heq.
           iDestruct "Ha" as (Hfl') ">Ha".
           destruct Hlocal as [Hp | Hp]; simplify_eq; simpl.      
           { iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; simpl; auto.
             { destruct p'; auto. }
             { apply PermFlows_trans with RWLX;auto. }
             iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
           }
           { iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; simpl; auto.
             { destruct p'; auto. }
             iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
           }
   Qed.

   Lemma wp_store_fail3' E dst pc_p pc_g pc_b pc_e pc_a w p g b e a pc_p' :
     cap_lang.decode w = Store dst (inr PC) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     writeAllowed p = true ->
     withinBounds ((p, g), b, e, a) = true →
     isLocal pc_g = true ->
     p <> RWLX ->
     p <> RWL ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hwa Hwb Hloc Hnrwlx Hnrwl;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hsrc) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
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
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store dst (inr PC))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst Hwa. simpl in Hwb. rewrite Hwb HPC. simpl.
       destruct pc_g; inversion Hloc. simpl. 
       destruct p; try congruence.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. rewrite Hwa. simpl in Hwb. rewrite Hwb. simpl.
       rewrite HPC. rewrite Hloc.
       assert (X: match p with
                    | RWL | RWLX =>
                        updatePC (update_mem (r, m) a (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
                    | _ => (Failed, (r, m))
                    end = (Failed, (r, m))) by (destruct p; congruence).
       repeat rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_store_success_reg_same' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e pc_p' :
     cap_lang.decode w = Store dst (inr dst) →
     PermFlows pc_p pc_p' →
     PermFlows p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, pc_a) = true →
     (isLocal g = false ∨ (p = RWLX ∨ p = RWL)) →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] inr (p, g, b, e, pc_a)
              ∗ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}}.
   Proof.
     iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hcond Hne ϕ) "(>HPC & >Hpc_a & >Hdst) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) pc_a (RegLocate r dst))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store dst (inr dst))
                              (NextI,_)); eauto; simpl; try congruence.
       simpl in Hwb.
       rewrite Hdst Hwa Hwb /= /updatePC /update_mem /= HPC Hpca'.
       destruct Hcond as [Hfalse | Hlocal].
       + simpl in Hfalse. rewrite Hfalse. auto.
       + destruct (isLocal g); auto.
         destruct Hlocal as [Hp | Hp]; simplify_eq; auto. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hwa Hwb /= /updatePC /update_mem /= HPC Hpca' /=.
       iSplitR; auto.
       destruct Hcond as [Hfalse | Hlocal].
       + rewrite Hfalse /=.
         iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
         { apply PermFlows_trans with p; auto.
           destruct p,g; inversion Hwa; inversion Hfalse; auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
       + destruct (isLocal g); simpl. 
         { destruct Hlocal as [Hp | Hp]; simplify_eq. 
           + assert (pc_p' = RWLX) as ->.
             { destruct pc_p'; auto; inversion Hfl'. }
             iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]";
               [auto|destruct g; auto|].
             iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
           + destruct pc_p'; inversion Hfl';
               (iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]";
                [auto|destruct g; auto|];
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
                iSpecialize ("Hϕ" with "[-]"); iFrame; eauto). 
         } 
         iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto. 
         { apply PermFlows_trans with p; auto. 
           destruct p; inversion Hwa; destruct g; inversion Hlocal; try congruence; auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
   Qed.

   Lemma wp_store_fail_same_None E r0 w' pc_p pc_g pc_b pc_e pc_a p g b e a w pc_p' p' :
    cap_lang.decode w = Store r0 (inr r0) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    writeAllowed p = true ∧ withinBounds (p, g, b, e, a) = true →
    (isLocal g = false ∨ (p = RWL ∨ p = RWLX)) → 
    (pc_a + 1)%a = None →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r0 ↦ᵣ inr ((p,g),b,e,a)
            ∗ if (pc_a =? a)%a then ⌜PermFlows p pc_p'⌝ else ⌜PermFlows p p'⌝ ∗ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc [Hwa Hwb] Hlocal Hnext.
     iIntros (φ) "(HPC & Hpc_a & Hr0 & Ha) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid with "Hr Hr0") as %?;
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     option_locate_mr m r.
     iApply fupd_frame_l. iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,(update_mem (r, m) a _).2), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store r0 (inr r0))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb. rewrite Hr0 Hwa Hwb /updatePC /= HPC Hnext.
       destruct Hlocal as [Hl | Hpc_p].
       + by rewrite Hl.
       + destruct (isLocal g); auto. destruct Hpc_p as [-> | ->]; auto. 
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite Hr0 Hwa Hwb /updatePC /= HPC Hnext.
       iNext.
       destruct g; simpl.
       + destruct (pc_a =? a)%a eqn:Heq. 
         { apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
           iDestruct "Ha" as %Hfl'. 
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
           { destruct p,pc_p'; inversion Hwa; inversion Hfl'; auto. }
           { apply PermFlows_trans with p;auto. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
         { apply Z.eqb_neq in Heq.
           iDestruct "Ha" as (Hfl') "Ha". 
           iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
           { destruct p,p'; inversion Hwa; inversion Hfl'; auto. }
           { apply PermFlows_trans with p;auto. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
       + destruct Hlocal as [Hl | Hpc_p]; first inversion Hl.
         destruct Hpc_p as [-> | ->]; simpl.
         { destruct (pc_a =? a)%a eqn:Heq. 
           { apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
             iDestruct "Ha" as %Hfl'. 
             iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
             { destruct pc_p'; inversion Hwa; inversion Hfl'; auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
           }
           { apply Z.eqb_neq in Heq.
             iDestruct "Ha" as (Hfl') "Ha". 
             iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
             { destruct p';inversion Hfl'; auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
           }
         }
         { destruct (pc_a =? a)%a eqn:Heq. 
           { apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
             iDestruct "Ha" as %Hfl'. 
             iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
             { destruct pc_p'; inversion Hwa; inversion Hfl'; auto. }
             { simpl. destruct pc_p'; inversion Hfl'. auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
           }
           { apply Z.eqb_neq in Heq.
             iDestruct "Ha" as (Hfl') "Ha". 
             iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
             { destruct p';inversion Hfl'; auto. }
             { destruct p'; inversion Hfl'; auto. }
             iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
           }
         }
   Qed.

   Lemma wp_store_fail3_same E r0 pc_p pc_g pc_b pc_e pc_a w p g b e a pc_p' :
     cap_lang.decode w = Store r0 (inr r0) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     writeAllowed p = true ->
     withinBounds ((p, g), b, e, a) = true →
     isLocal g = true ->
     p <> RWLX ->
     p <> RWL ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r0 ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hwa Hwb Hloc Hnrwlx Hnrwl;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hsrc) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
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
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store r0 (inr r0))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hr0 Hwa. simpl in Hwb. rewrite Hwb. simpl.
       destruct g; inversion Hloc. simpl. 
       destruct p; try congruence.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hr0. rewrite Hwa. simpl in Hwb. rewrite Hwb. simpl.
       rewrite Hloc.
       assert (X: match p with
                    | RWL | RWLX =>
                        updatePC (update_mem (r, m) a (inr (p, g, b, e, a)))
                    | _ => (Failed, (r, m))
                    end = (Failed, (r, m))) by (destruct p; congruence).
       repeat rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. simpl. by iApply "Hφ".
   Qed.

    Lemma wp_store_fail_None E dst src w' w'' pc_p pc_g pc_b pc_e pc_a w p g b e a pc_p' p' :
    cap_lang.decode w = Store dst (inr src) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    writeAllowed p = true ∧ withinBounds (p, g, b, e, a) = true →
    (isLocalWord w'' = false ∨ (p = RWL ∨ p = RWLX)) → 
    (pc_a + 1)%a = None →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ src ↦ᵣ w''
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ if (a =? pc_a)%a
             then ⌜PermFlows p pc_p'⌝
             else ⌜PermFlows p p'⌝ ∗ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc [Hwa Hwb] Hlocal Hnext.
     iIntros (φ) "(HPC & Hdst & Hsrc & Hpc_a & Ha) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
     iDestruct (@gen_heap_valid with "Hr Hsrc") as %?;                                              
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     option_locate_mr m r.
     iApply fupd_frame_l. iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,(update_mem (r, m) a _).2), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store dst (inr src))
                              (Failed,_));
         eauto; simpl; try congruence.
       simpl in Hwb.
       rewrite Hdst Hsrc Hwa Hwb /updatePC /= HPC Hnext.
       destruct w''; eauto. destruct c,p0,p0,p0. 
       destruct l; auto. 
       destruct Hlocal as [Hcontr | Hpc_p]; [inversion Hcontr|]. destruct Hpc_p as [-> | ->]; auto. 
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       simpl in Hwb. rewrite Hdst Hsrc Hwa Hwb /updatePC /= HPC Hnext.
       iNext. destruct w''; simpl.
       + destruct (a =? pc_a)%a eqn:Heq.
         { apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
           iDestruct "Ha" as %Hfl'. 
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
           { destruct p,pc_p'; auto; inversion Hfl'; auto. }
           { apply PermFlows_trans with pc_p;auto. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
         { iDestruct "Ha" as (Hfl') "Ha". 
           iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
           { destruct p,p'; auto; inversion Hfl'; auto. }
           { apply PermFlows_trans with p;auto. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
       + destruct c,p0,p0,p0.
         destruct l; simpl.
         * destruct (a =? pc_a)%a eqn:Heq.
         { apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
           iDestruct "Ha" as %Hfl'. 
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
           { destruct p,pc_p'; auto; inversion Hfl'; auto. }
           { apply PermFlows_trans with p;auto. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
         { iDestruct "Ha" as (Hfl') "Ha". 
           iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
           { destruct p,p'; auto; inversion Hfl'; auto. }
           { apply PermFlows_trans with p;auto. }
           iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
         }
         * destruct Hlocal as [Hcontr | Hp];[inversion Hcontr|].
           destruct Hp as [-> | ->].
           { destruct (a =? pc_a)%a eqn:Heq.
             { apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
               iDestruct "Ha" as %Hfl'. 
               iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
               { destruct pc_p'; auto; inversion Hfl'; auto. }
               iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
             }
             { iDestruct "Ha" as (Hfl') "Ha". 
               iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
               { destruct p'; auto; inversion Hfl'; auto. }
               iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
             }
           }
           { destruct (a =? pc_a)%a eqn:Heq.
             { apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
               iDestruct "Ha" as %Hfl'. 
               iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
               { destruct pc_p'; auto; inversion Hfl'; auto. }
               { apply PermFlows_trans with RWLX;auto. }
               iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
             }
             { iDestruct "Ha" as (Hfl') "Ha". 
               iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
               { destruct p'; auto; inversion Hfl'; auto. }
               { apply PermFlows_trans with RWLX;auto. }
               iModIntro. iSplitR;[auto|]. iFrame. by iApply "Hφ".
             }
           }
   Qed.

   Lemma wp_store_success_reg_same_a E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src 
         p g b e pc_p' w'' :
      cap_lang.decode w = Store dst (inr src) →
      PermFlows pc_p pc_p' →
      PermFlows p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, pc_a) = true →
     (isLocalWord w'' = false ∨ (p = RWLX ∨ p = RWL)) →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ inr ((p,g),b,e,pc_a)}}}.
   Proof.
     iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hcond Hne ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst; inversion Hvpc as [?????? Ho]; subst.
         destruct Ho as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) pc_a (RegLocate r src))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store dst (inr src))
                              (NextI,_)); eauto; simpl; try congruence.
       simpl in Hwb.
       rewrite Hdst Hwa Hwb /= Hsrc /updatePC /update_mem /= HPC Hpca'.
       destruct w''; auto.
       destruct c,p0,p0,p0. destruct Hcond as [Hfalse | Hlocal].
       + simpl in Hfalse. rewrite Hfalse. auto.
       + destruct (isLocal l); auto.
         destruct Hlocal as [Hp | Hp]; simplify_eq; auto. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hwa Hwb /= Hsrc /updatePC /update_mem /= HPC Hpca' /=.
       iSplitR; auto.
       destruct w''; auto; simpl.
       + iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]".
         { destruct p; inversion Hwa; auto. }
         { apply PermFlows_trans with p; auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
       + destruct c,p0,p0,p0. destruct Hcond as [Hfalse | Hlocal].
         { simpl in Hfalse. rewrite Hfalse.
           iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]";
             [auto|apply PermFlows_trans with p; auto;
             destruct p,l; auto; inversion Hwa; inversion Hfalse| ].
           iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
           iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
         }
         { destruct (isLocal l); simpl.
           - destruct Hlocal as [Hp | Hp]; simplify_eq. 
             + assert (pc_p' = RWLX) as ->.
               { destruct pc_p'; auto; inversion Hfl'. }
               iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]";
                 [auto|destruct l; auto|].
               iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
                iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
             + destruct pc_p'; inversion Hfl';
                 (iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]";
                 [auto|destruct l; auto|];
                 iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
                 iSpecialize ("Hϕ" with "[-]"); iFrame; eauto). 
           - (iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]";
              [auto|apply PermFlows_trans with p;destruct p,l; inversion Hwa; auto;
                    destruct Hlocal as [Hcontr | Hcontr]; inversion Hcontr|];
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
              iSpecialize ("Hϕ" with "[-]"); iFrame; eauto).
         }
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
    { rewrite (fixpoint_interp1_eq _ (inr _)) /=.
      destruct Hp as [-> | [-> | ->] ];
      (iExists _,_,_,_; iSplitR;[eauto|];
       iExists p';do 2 (iSplit; auto);
       iAlways;iIntros (a' r' W' Hin) "Hfuture";
       iNext; destruct W' as [fs' fr'];
       iExists _,_; do 2 (iSplitR; [auto|]);
       iIntros "(#[Hfull Hreg'] & Hmap & Hr & Hsts & Hna) /=";
       iExists _,_,_,_,_; iSplit;[eauto|];
       iApply ("IH" with "Hfull Hreg' Hmap Hr Hsts Hna"); auto).
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
            { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; apply Zle_is_le_bool; auto. }
              { destruct p0; inversion Hwa; auto. }
              rewrite /read_write_cond. 
              iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]". 
              iApply (wp_store_success_same with "[$HPC $Ha $Hdst]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iApply wp_pure_step_later; auto. iNext.
              (* close the region *)
              iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr".
              { iSplitR;[auto|simpl]. rewrite (fixpoint_interp1_eq _ (inl _)). eauto. }
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
            destruct (decide (a = a0));[subst|].
            - iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; apply Zle_is_le_bool; auto. }
              { destruct p0; inversion Hwa; auto. }
              rewrite /read_write_cond. 
              iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]". 
              iApply (wp_store_fail_z2 with "[$Ha $HPC $Hdst]"); eauto.
              { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros. discriminate.
            - iDestruct (region_open_prepare with "Hr") as "Hr".
              iDestruct ("Hreg" $! dst n) as "#Hvdst".
              rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; apply Zle_is_le_bool; auto. }
              { destruct p0; inversion Hwa; auto. }
              iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                as (wa0) "(Hr & Ha0 & % & _)";
                [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
              iApply (wp_store_fail_z2 with "[$Ha $HPC $Hdst Ha0]"); eauto.
              { destruct (a0 =? a)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|].
                iFrame. auto. }
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros. discriminate.
          } 
        * destruct (reg_eq_dec PC r0),(reg_eq_dec dst r0);
            first congruence; subst. 
          ** case_eq (negb (isLocal g) || match p0 with
                                         | RWL | RWLX => true
                                         | _ => false end); intros Hconds'.
             { destruct (a + 1)%a eqn:Hnext.
               { (* successful write from PC into a0 *)               
                 destruct (decide (a = a0));[subst|].
                 { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                   iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                   { apply andb_true_iff in Hwb as [Hle Hge].
                     split; apply Zle_is_le_bool; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   rewrite /read_write_cond. 
                   iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                   iApply (wp_store_success_reg' with "[$HPC $Ha $Hdst]"); eauto;
                     (destruct (a0 =? a0)%a eqn:Hcontr;
                       [auto|by apply Z.eqb_neq in Hcontr]).
                   { destruct g; auto. right.
                     rewrite orb_false_l in Hconds'.
                     destruct p0; auto; inversion Hconds'. }
                   iNext. iIntros "(HPC & Ha & Hdst & _)".
                   iApply wp_pure_step_later; auto. iNext.
                   (* close the region *)
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
                   iApply (wp_store_success_reg' with "[$HPC $Ha $Hdst Ha0]"); eauto;
                     (destruct (a0 =? a)%a eqn:Hcontr;
                      [by apply Z.eqb_eq, z_of_eq in Hcontr|auto]).
                   { destruct g; auto. right. rewrite orb_false_l in Hconds'.
                     destruct p0;auto;inversion Hconds'. }
                   iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
                   iApply wp_pure_step_later; auto. iNext.
                   (* close the region *)
                   iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                     [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..];auto.
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
                 destruct (decide (a = a0));[subst|].
                 { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                   iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                   { apply andb_true_iff in Hwb as [Hle Hge].
                     split; apply Zle_is_le_bool; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   rewrite /read_write_cond. 
                   iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                   iApply (wp_store_fail_reg_PC_2 with "[$HPC $Ha $Hdst]"); eauto.
                   { destruct g; auto. rewrite orb_false_l in Hconds'. right.
                     destruct p0; auto; inversion Hconds'. }
                   { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                   iNext. iIntros. iApply wp_pure_step_later; auto.
                   iNext. iApply wp_value. iIntros. discriminate.
                 } 
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
                   iApply (wp_store_fail_reg_PC_2 with "[$HPC $Ha $Hdst Ha0]"); eauto.
                   { destruct g; auto. rewrite orb_false_l in Hconds'. right.
                     destruct p0; auto; inversion Hconds'. }
                   { destruct (a =? a0)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|auto]. }
                   iNext. iIntros. iApply wp_pure_step_later; auto.
                   iNext. iApply wp_value. iIntros. discriminate.
                 }
               }
             }
             { (* condition failure *)
               revert Hconds'. rewrite orb_false_iff =>Hlocal.
               destruct Hlocal as [Hg Hp0]. 
               iApply (wp_store_fail3' with "[$HPC $Ha $Hdst]"); eauto;
                 [destruct g|destruct p0|destruct p0|];auto. 
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value. iIntros. discriminate.
             }
          ** case_eq (negb (isLocal l) || match p0 with
                                         | RWL | RWLX => true
                                         | _ => false end); intros Hconds'. 
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write from r0 into a0 *)
                   destruct (decide (a = a0));[subst|].
                   { iDestruct ("Hreg" $! r0 _) as "Hdstv". rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond. 
                     iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                     iApply (wp_store_success_reg_same' with "[$HPC $Ha $Hdst]"); eauto.
                     { destruct l; auto. revert Hconds'. rewrite orb_false_l =>Hp0.
                       right. destruct p0; inversion Hp0; auto. }
                     iNext. iIntros "(HPC & Ha & Hdst)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Hdstv]") as "Hr"; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                       iFrame "#"; auto.
                     - iPureIntro. intros r1.
                       destruct (decide (r0 = r1)); subst;
                         [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                     - iIntros (r1 Hne).
                       destruct (decide (r0 = r1)); subst; rewrite /RegLocate;
                         [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                       iSpecialize ("Hreg" $! r1 Hne).
                       destruct (r !! r1); auto.
                   }
                   { iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct ("Hreg" $! r0 n) as "#Hvdst".
                     rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                       as (wa0) "(Hr & Ha0 & % & _)";
                       [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
                     iApply (wp_store_success_reg_same with "[$HPC $Ha $Hdst $Ha0]"); eauto.
                     { destruct l; auto. revert Hconds'. rewrite orb_false_l =>Hp0.
                       right. destruct p0; inversion Hp0; auto. }
                     iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                       [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..]; auto.
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
                       destruct (decide (r0 = r1)); subst;
                         [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                     - iIntros (r1 Hne).
                       destruct (decide (r0 = r1)); subst; rewrite /RegLocate;
                         [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                       iSpecialize ("Hreg" $! r1 Hne).
                       destruct (r !! r1); auto.
                   }
                 }
                 { (* failure to increment *)
                   destruct (decide (a = a0));[subst|].
                   { iDestruct ("Hreg" $! r0 _) as "Hdstv". rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond. 
                     iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                     iApply (wp_store_fail_same_None with "[$HPC $Ha $Hdst]"); eauto.
                     { destruct l; auto. rewrite orb_false_l in Hconds'. right.
                       destruct p0; auto; inversion Hconds'. }
                     { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value. iIntros. discriminate.
                 } 
                 { iDestruct (region_open_prepare with "Hr") as "Hr".
                   iDestruct ("Hreg" $! r0 n) as "#Hvdst".
                   rewrite /RegLocate Hsomedst.
                   iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                   { apply andb_true_iff in Hwb as [Hle Hge].
                     split; apply Zle_is_le_bool; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                     as (wa0) "(Hr & Ha0 & % & _)";
                     [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
                   iApply (wp_store_fail_same_None with "[$HPC $Ha $Hdst Ha0]"); eauto.
                   { destruct l; auto. rewrite orb_false_l in Hconds'. right.
                     destruct p0; auto; inversion Hconds'. }
                   { destruct (a =? a0)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|auto]. }
                   iNext. iIntros. iApply wp_pure_step_later; auto.
                   iNext. iApply wp_value. iIntros. discriminate.
                 }
               }
             *** (* locality failure *)
               revert Hconds'. rewrite orb_false_iff =>Hlocal.
               destruct Hlocal as [Hg Hp0]. 
               iApply (wp_store_fail3_same with "[$HPC $Ha $Hdst]"); eauto;
                 [destruct l|destruct p0|destruct p0|];auto. 
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value. iIntros. discriminate.
          ** destruct (Hsome r0) as [wsrc Hsomesrc].
             assert (delete PC r !! r0 = Some wsrc).
             { rewrite lookup_delete_ne; auto. }
             iDestruct ((big_sepM_delete _ _ r0) with "Hmap")
               as "[Hsrc Hmap]"; [rewrite lookup_delete_ne; eauto|].
             destruct wsrc.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write from r0 into a0 *)
                   destruct (decide (a = a0));[subst|].
                   { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond. 
                     iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                     iApply (wp_store_success_reg_same_a with "[$HPC $Ha $Hsrc $Hdst]"); eauto.
                     iNext. iIntros "(HPC & Ha & Hsrc & Hdst)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Harel']") as "Hr".
                     { iSplitR;[auto|]. rewrite (fixpoint_interp1_eq _ (inl _)). eauto. }
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     do 2 (rewrite -delete_insert_ne; auto).
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                       iFrame "#"; auto.
                     - iPureIntro. intros r1.
                       destruct (decide (r0 = r1)); subst.
                       + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                       + destruct (decide (dst = r1)); subst.
                         * rewrite lookup_insert. eauto.
                         * do 2 (rewrite lookup_insert_ne;auto).
                     - iIntros (r1 Hne).
                       destruct (decide (r0 = r1)),(decide (dst = r1)); subst; rewrite /RegLocate;
                         [rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto;
                         rewrite (fixpoint_interp1_eq _ (inl _));eauto|
                          rewrite lookup_insert_ne;auto;rewrite lookup_insert;
                          rewrite (fixpoint_interp1_eq _ (inl _));eauto|rewrite lookup_insert;auto|
                          do 2 (rewrite lookup_insert_ne;auto)].
                       iSpecialize ("Hreg" $! r1 Hne).
                       destruct (r !! r1); auto.
                   }
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
                     iApply (wp_store_success_reg with "[$HPC $Ha $Ha0 $Hsrc $Hdst]"); eauto.
                     iNext. iIntros "(HPC & Ha & Hsrc & Hdst & Ha0)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                       [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..]; auto.
                     { rewrite (fixpoint_interp1_eq _ (inl _)). eauto. }
                     iDestruct (region_open_prepare with "Hr") as "Hr". 
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     do 2 (rewrite -delete_insert_ne; auto).
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                       iFrame "#"; auto.
                     - iPureIntro. intros r1.
                       destruct (decide (r0 = r1)); subst.
                       + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                       + destruct (decide (dst = r1)); subst.
                         * rewrite lookup_insert. eauto.
                         * do 2 (rewrite lookup_insert_ne;auto).
                     - iIntros (r1 Hne).
                       destruct (decide (r0 = r1)),(decide (dst = r1)); subst; rewrite /RegLocate;
                         [rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto;
                         rewrite (fixpoint_interp1_eq _ (inl _));eauto|
                          rewrite lookup_insert_ne;auto;rewrite lookup_insert;
                          rewrite (fixpoint_interp1_eq _ (inl _));eauto|rewrite lookup_insert;auto|
                          do 2 (rewrite lookup_insert_ne;auto)].
                       iSpecialize ("Hreg" $! r1 Hne).
                       destruct (r !! r1); auto.
                   }
                 }
                 { (* failed to increment PC *)
                   destruct (decide (a = a0));[subst|].
                   { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond. 
                     iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                     iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc]"); eauto.
                     { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value. iIntros. discriminate.
                   } 
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
                     iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc Ha0]"); eauto.
                     { destruct (a0 =? a)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|auto]. }
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value. iIntros. discriminate.
                   }
                 }
             *** case_eq (negb (isLocalWord (inr c)) || match p0 with
                                                       | RWL | RWLX => true
                                                       | _ => false end); intros Hconds'. 
                 **** destruct (a + 1)%a eqn:Hnext.
                      { (* successful write from r0 into a0 *)
                        destruct (decide (a = a0));[subst|].
                        { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                          iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                          { apply andb_true_iff in Hwb as [Hle Hge].
                            split; apply Zle_is_le_bool; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          rewrite /read_write_cond. 
                          iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                          iApply (wp_store_success_reg_same_a with "[$HPC $Ha $Hsrc $Hdst]"); eauto.
                          { destruct c,p1,p1,p1,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          iNext. iIntros "(HPC & Ha & Hsrc & Hdst)".
                          iApply wp_pure_step_later; auto. iNext.
                          (* close the region *)
                          iDestruct ("Hreg" $! r0 _) as "Hc". rewrite Hsomesrc. 
                          iDestruct (region_close with "[$Hr $Ha $Hmono $Harel']") as "Hr"; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          do 2 (rewrite -delete_insert_ne; auto).
                          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          (* apply IH *)
                          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                            iFrame "#"; auto.
                          - iPureIntro. intros r1.
                            destruct (decide (r0 = r1)); subst.
                            + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                            + destruct (decide (dst = r1)); subst.
                              * rewrite lookup_insert. eauto.
                              * do 2 (rewrite lookup_insert_ne;auto).
                          - iIntros (r1 Hne).
                            destruct (decide (r0 = r1)),(decide (dst = r1)); subst; rewrite /RegLocate;
                              [rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto;
                               rewrite (fixpoint_interp1_eq _ (inl _));eauto|
                               rewrite lookup_insert_ne;auto;rewrite lookup_insert;
                               rewrite (fixpoint_interp1_eq _ (inr _));eauto|rewrite lookup_insert;auto|
                               do 2 (rewrite lookup_insert_ne;auto)].
                            iSpecialize ("Hreg" $! r1 Hne).
                            destruct (r !! r1); auto.
                        }
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
                          iApply (wp_store_success_reg with "[$HPC $Ha $Ha0 $Hsrc $Hdst]"); eauto.
                          { destruct c,p2,p2,p2,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          iNext. iIntros "(HPC & Ha & Hsrc & Hdst & Ha0)".
                          iApply wp_pure_step_later; auto. iNext.
                          (* close the region *)
                          iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                            [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..]; auto.
                          { iSplitR; eauto. iSpecialize ("Hreg" $! r0 _). rewrite Hsomesrc. auto. }
                          iDestruct (region_open_prepare with "Hr") as "Hr". 
                          iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          do 2 (rewrite -delete_insert_ne; auto).
                          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          (* apply IH *)
                          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                            iFrame "#"; auto.
                          - iPureIntro. intros r1.
                            destruct (decide (r0 = r1)); subst.
                            + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                            + destruct (decide (dst = r1)); subst.
                              * rewrite lookup_insert. eauto.
                              * do 2 (rewrite lookup_insert_ne;auto).
                          - iIntros (r1 Hne).
                            iDestruct ("Hreg" $! r0 _) as "Hc". rewrite Hsomesrc. 
                            destruct (decide (r0 = r1)),(decide (dst = r1)); subst; rewrite /RegLocate;
                              [rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto;
                               rewrite (fixpoint_interp1_eq _ (inr c));eauto|
                               rewrite lookup_insert_ne;auto;rewrite lookup_insert;
                               rewrite (fixpoint_interp1_eq _ (inr c));eauto|rewrite lookup_insert;auto|
                               do 2 (rewrite lookup_insert_ne;auto)].
                            iSpecialize ("Hreg" $! r1 Hne).
                            destruct (r !! r1); auto.
                        }
                      }
                      { (* failed to increment PC *)
                        destruct (decide (a = a0));[subst|].
                        { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                          iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                          { apply andb_true_iff in Hwb as [Hle Hge].
                            split; apply Zle_is_le_bool; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          rewrite /read_write_cond. 
                          iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                          iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc]"); eauto.
                          { destruct c,p1,p1,p1,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value. iIntros. discriminate.
                        } 
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
                          iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc Ha0]"); eauto.
                          { destruct c,p2,p2,p2,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          { destruct (a0 =? a)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|auto]. }
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value. iIntros. discriminate.
                        }
                      }
                 **** (* locality failure *)
                   apply orb_false_iff in Hconds'. 
                   destruct c,p1,p1,p1.
                   destruct Hconds' as [Hl0 Hp0]. 
                   iApply (wp_store_fail3 with "[$HPC $Hdst $Hsrc $Ha]"); eauto.
                   { by apply negb_false_iff. }
                   { destruct p0; auto; inversion Hp0. }
                   { destruct p0; auto; inversion Hp0. }
                   iNext. iIntros. iApply wp_pure_step_later; auto.
                   iNext. iApply wp_value. iIntros. discriminate.
      + (* write failure, either wrong permission or not within range *)
        iApply (wp_store_fail1 with "[$HPC $Ha $Hdst]"); eauto.  
        { by apply andb_false_iff in Hconds. }
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iIntros. discriminate.
        Unshelve. auto. 
        
        
  Admitted. 
             
   
End fundamental.