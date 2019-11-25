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

  Ltac inv_head_step :=
    repeat match goal with
           | _ => progress simplify_map_eq/= (* simplify memory stuff *)
           | H : to_val _ = Some _ |- _ => apply of_to_val in H
           | H : _ = of_val ?v |- _ =>
             is_var v; destruct v; first[discriminate H|injection H as H]
           | H : cap_lang.prim_step ?e _ _ _ _ _ |- _ =>
             try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
             (*    and can thus better be avoided. *)
             let φ := fresh "φ" in 
             inversion H as [| φ]; subst φ; clear H
           end.

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
           { destruct p,pc_p'; auto; inversion Hfl'; auto. }
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

   
  Lemma wp_store_success_local_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a p' g' b' e' a' pc_p' p'' :
    cap_lang.decode w = Store dst (inr src) →
    PermFlows pc_p pc_p' →
    PermFlows p p'' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     isLocal g' = true ∧ (p = RWLX ∨ p = RWL) →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ src ↦ᵣ inr ((p',g'),b',e',a')
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ[p''] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ src ↦ᵣ inr ((p',g'),b',e',a')
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ[p''] inr ((p',g'),b',e',a') }}}.
   Proof.
     iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] [Hlocal Hp] Hne ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork_determ; auto. simpl.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (p'' ≠ O) as Hp''. 
     { destruct p''; auto. inversion Hfl'. destruct p; inversion H2. 
       destruct Hp as [Hcontr | Hcontr]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto. 
     option_locate_mr m r.
     iModIntro.
     iExists [],(Instr _),(updatePC (update_mem (r,m) a (RegLocate r src))).2,[].
     iSplit.
     - iPureIntro. econstructor 1.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store dst (inr src))
                              (NextI,_)); eauto; simpl; try congruence.
       simpl in Hwb.
       rewrite Hdst Hwa Hwb /= Hsrc Hlocal.
       destruct Hp as [Hp | Hp]; try contradiction;
         by rewrite Hp /updatePC /update_mem /= HPC Hpca'.
     - iNext. rewrite /updatePC /update_mem /= HPC /update_reg /= Hpca' /=.
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
       rewrite Hsrc. rewrite /LeastPermUpd /PermFlows; destruct g';
         apply PermFlows_trans with p; auto. destruct Hp as [Hp | Hp]; rewrite Hp; auto.
       rewrite Hsrc. 
       iSpecialize ("Hϕ" with "[HPC Ha Hpc_a Hsrc Hdst]"); iFrame; eauto.
   Qed.

   Lemma wp_store_success_z_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a z pc_p' p' :
     cap_lang.decode w = Store dst (inr src) →
     PermFlows pc_p pc_p' →
     PermFlows p p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ src ↦ᵣ inl z
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ src ↦ᵣ inl z
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ[p'] inl z }}}.
   Proof.
     iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hne ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (p' ≠ O) as Hp''. 
     { destruct p'; auto. inversion Hfl'. destruct p; inversion H2. 
       inversion Hwa. }
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?;auto. 
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) a (RegLocate r src))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store dst (inr src))
                              (NextI,_)); eauto; simpl; try congruence.
       simpl in Hwb.
       by rewrite Hdst Hwa Hwb /= Hsrc /updatePC /update_mem /= HPC Hpca'.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hwa Hwb /= Hsrc /updatePC /update_mem /= HPC Hpca' /=.
       iSplitR; auto. 
       iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]".
       { destruct p; inversion Hwa; auto. }
       { apply PermFlows_trans with p; auto. }
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
   Qed.

    Lemma wp_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' pc_p' p' :
      cap_lang.decode w = Store dst (inr src) →
      PermFlows pc_p pc_p' →
      PermFlows p p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     (isLocalWord w'' = false ∨ (p = RWLX ∨ p = RWL)) →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ[p'] w'' }}}.
   Proof.
     iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hcond Hne ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (p' ≠ O) as Hp''. 
     { destruct p'; auto. inversion Hfl'. destruct p; inversion H2. 
       inversion Hwa. }
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto. 
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) a (RegLocate r src))).2, [].
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
       + iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]".
         { destruct p; inversion Hwa; auto. }
         { apply PermFlows_trans with p; auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
       + destruct c,p0,p0,p0. destruct Hcond as [Hfalse | Hlocal].
         { simpl in Hfalse. rewrite Hfalse.
           iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]";
             [auto|apply PermFlows_trans with p; auto;
             destruct p,l; auto; inversion Hwa; inversion Hfalse| ].
           iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
           iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
         }
         { destruct (isLocal l); simpl.
           - destruct Hlocal as [Hp | Hp]; simplify_eq. 
             + assert (p' = RWLX) as ->.
               { destruct p'; auto; inversion Hfl'. }
               iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]";
                 [auto|destruct l; auto|].
               iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
                iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
             + destruct p'; inversion Hfl';
                 (iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]";
                 [auto|destruct l; auto|];
                 iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
                 iSpecialize ("Hϕ" with "[-]"); iFrame; eauto). 
           - (iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]";
              [auto|apply PermFlows_trans with p;destruct p,l; inversion Hwa; auto; inversion Hlocal; inversion H2|]; 
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
              iSpecialize ("Hϕ" with "[-]"); iFrame; eauto).
         }
   Qed.

   Lemma wp_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a pc_p' p' :
     cap_lang.decode w = Store dst (inr dst) →
     PermFlows pc_p pc_p' →
     PermFlows p p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     (isLocal g = false ∨ (p = RWLX ∨ p = RWL)) →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ[p'] inr ((p,g),b,e,a) }}}.
   Proof.
     iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hcond Hne ϕ) "(>HPC & >Hpc_a & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (p' ≠ O) as Hp''. 
     { destruct p'; auto. inversion Hfl'. destruct p; inversion H2. 
       inversion Hwa. }
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto. 
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) a (RegLocate r dst))).2, [].
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
         iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
         { apply PermFlows_trans with p; auto.
           destruct p,g; inversion Hwa; inversion Hfalse; auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
       + destruct (isLocal g); simpl. 
         { destruct Hlocal as [Hp | Hp]; simplify_eq. 
           + assert (p' = RWLX) as ->.
             { destruct p'; auto; inversion Hfl'. }
             iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]";
               [auto|destruct g; auto|].
             iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
               iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
           + destruct p'; inversion Hfl';
               (iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]";
                [auto|destruct g; auto|];
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
                iSpecialize ("Hϕ" with "[-]"); iFrame; eauto). 
         } 
         iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto. 
         { apply PermFlows_trans with p; auto. 
           destruct p; inversion Hwa; destruct g; inversion Hlocal; inversion H2; auto. }
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
   Qed. 

   Lemma wp_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a pc_p' p' :
     cap_lang.decode w = Store dst (inl z) →
     PermFlows pc_p pc_p' →
     PermFlows p p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ[p'] inl z }}}.
   Proof.
     iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hne ϕ) "(>HPC & >Hpc_a & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (p' ≠ O) as Hp''. 
     { destruct p'; auto. inversion Hfl'. destruct p; inversion H2. 
       inversion Hwa. }
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?;auto. 
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) a (inl z))).2, [].
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
       iMod (@gen_heap_update_cap with "Hm Ha") as "[$ Ha]"; auto.
       { apply PermFlows_trans with p;auto. }
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[HPC Ha Hpc_a Hdst]"); iFrame; eauto.
   Qed.

   
  Lemma wp_store_fail1 E dst src pc_p pc_g pc_b pc_e pc_a w p g b e a pc_p' :
    cap_lang.decode w = Store dst src →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    (writeAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    intros Hinstr Hfl Hvpc HnwaHnwb;
      (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
       option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [],(Instr Failed), (r,m), [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store dst src)
                             (Failed,_));
        eauto; simpl; try congruence.
      rewrite Hdst. destruct HnwaHnwb as [Hnwa | Hnwb].
      + rewrite Hnwa; simpl; auto.
        destruct src; auto.
      + simpl in Hnwb. rewrite Hnwb.
        rewrite andb_comm; simpl; auto.
        destruct src; auto.
    - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
      iModIntro.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      rewrite Hdst. destruct HnwaHnwb as [Hnwa | Hnwb].
      + rewrite Hnwa; simpl. destruct src; simpl.
        * iFrame. iNext. iModIntro.
          iSplitR; auto. by iApply "Hφ".
        * iFrame. iNext. iModIntro. 
          iSplitR; auto. by iApply "Hφ".
      + simpl in Hnwb. rewrite Hnwb.
        rewrite andb_comm; simpl.
        destruct src; simpl.
        * iFrame. iNext. iModIntro. 
          iSplitR; auto. by iApply "Hφ".
        * iFrame. iNext. iModIntro.
          iSplitR; auto. by iApply "Hφ".
  Qed.

  Lemma wp_store_fail1' E src pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Store PC src →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    (writeAllowed pc_p = false ∨ withinBounds ((pc_p,pc_g),pc_b,pc_e,pc_a) = false) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    intros Hinstr Hfl Hvpc HnwaHnwb;
      (iIntros (φ) "(HPC & Hpc_a) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
       option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [],(Instr Failed), (r,m), [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store PC src)
                             (Failed,_));
        eauto; simpl; try congruence.
      rewrite HPC. destruct HnwaHnwb as [Hnwa | Hnwb].
      + rewrite Hnwa; simpl; auto.
        destruct src; auto.
      + simpl in Hnwb. rewrite Hnwb.
        rewrite andb_comm; simpl; auto.
        destruct src; auto.
    - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
      iModIntro.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      rewrite HPC. destruct HnwaHnwb as [Hnwa | Hnwb].
      + rewrite Hnwa; simpl. destruct src; simpl.
        * iFrame. iNext. iModIntro.
          iSplitR; auto. by iApply "Hφ".
        * iFrame. iNext. iModIntro. 
          iSplitR; auto. by iApply "Hφ".
      + simpl in Hnwb. rewrite Hnwb.
        rewrite andb_comm; simpl.
        destruct src; simpl.
        * iFrame. iNext. iModIntro. 
          iSplitR; auto. by iApply "Hφ".
        * iFrame. iNext. iModIntro.
          iSplitR; auto. by iApply "Hφ".
  Qed.

  Lemma wp_store_fail2 E dst src pc_p pc_g pc_b pc_e pc_a w n pc_p' :
    cap_lang.decode w = Store dst src →
    PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inl n}}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc.
     iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
     option_locate_mr m r.
     iApply fupd_frame_l. iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,m), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store dst src)
                              (Failed,_));
         eauto; simpl; try congruence.
         destruct src; simpl; by rewrite Hdst.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst /=.
       destruct src; simpl.
       + iFrame. iNext. iModIntro.
         iSplitR; auto. by iApply "Hφ".
       + iFrame. iNext. iModIntro.
         iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_store_fail3 E dst src pc_p pc_g pc_b pc_e pc_a w p g b e a p' g' b' e' a' pc_p' :
     cap_lang.decode w = Store dst (inr src) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     writeAllowed p = true ->
     withinBounds ((p, g), b, e, a) = true →
     isLocal g' = true ->
     p <> RWLX ->
     p <> RWL ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ src ↦ᵣ inr ((p',g'),b',e',a') }}}
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
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store dst (inr src))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. rewrite Hwa. simpl in Hwb. rewrite Hwb. simpl.
       rewrite Hsrc. rewrite Hloc.
       destruct p; try congruence.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. rewrite Hwa. simpl in Hwb. rewrite Hwb. simpl.
       rewrite Hsrc. rewrite Hloc.
       assert (X: match p with
                    | RWL | RWLX =>
                        updatePC (update_mem (r, m) a (inr (p', g', b', e', a')))
                    | _ => (Failed, (r, m))
                    end = (Failed, (r, m))) by (destruct p; congruence).
       repeat rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

End cap_lang_rules.