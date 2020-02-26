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

  Lemma wp_restrict_success_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w rv z a' pc_p' :
    cap_lang.decode w = Restrict PC (inr rv) →
    PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PermPairFlowsTo (decodePermPair z) (pc_p,pc_g) = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ inr (decodePermPair z,pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ rv ↦ᵣ inl z }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a & >Hrv) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr Hrv") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),((<[PC:=inr (decodePermPair z, pc_b, pc_e, pc_a')]> r), m), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Restrict PC (inr rv))
                              (NextI,_)); eauto; simpl; try congruence.
       rewrite Hrv HPC Hflows.
       rewrite /updatePC /update_reg /= /RegLocate lookup_insert Hpca'.
       destruct (decodePermPair z); rewrite insert_insert; auto.
       inv Hvpc; auto. destruct H7 as [Heq | [Heq | Heq]]; subst pc_p; auto.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hrv /= Hflows.
       rewrite /updatePC /update_reg /RegLocate lookup_insert Hpca' /=.
       destruct (decodePermPair z); rewrite insert_insert.
       inv Hvpc. destruct H8 as [Heq | [Heq | Heq]]; subst pc_p;
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
       iSpecialize ("Hϕ" with "[HPC Hrv Hpc_a]"); iFrame; eauto.
   Qed.

   Lemma wp_restrict_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv p g b e a z
         pc_p' :
     cap_lang.decode w = Restrict r1 (inr rv) →
     PermFlows pc_p pc_p' → 
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PermPairFlowsTo (decodePermPair z) (p,g) = true →
     r1 ≠ PC →
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET match p with E => FailedV | _ => NextIV end;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,match p with E => pc_a | _ => pc_a' end)
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ rv ↦ᵣ inl z
              ∗ r1 ↦ᵣ inr (match p with E => (p, g) | _ => decodePermPair z end,b,e,a) }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hflows Hne1 ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     iDestruct (@gen_heap_valid with "Hr Hrv") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(match p with E => _ | _ => _ end), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Restrict r1 (inr rv))
                              (match p with E => Failed | _ => NextI end,_)); eauto; simpl; try congruence.
       rewrite Hrv Hr1 Hflows /updatePC /update_reg /= /RegLocate lookup_insert_ne; auto.
       rewrite /RegLocate in HPC. rewrite HPC Hpca'. destruct p; reflexivity.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hr1 Hrv /= Hflows /updatePC /update_reg /RegLocate lookup_insert_ne; auto.
       rewrite /RegLocate in HPC. rewrite HPC Hpca' /=.
       destruct p;
         try (iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]";
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
              iSpecialize ("Hϕ" with "[HPC Hr1 Hrv Hpc_a]"); iFrame; eauto).
       simpl. iFrame. iModIntro. iSplitR; auto.
       iApply "Hϕ". iFrame.
   Qed.

   Lemma wp_restrict_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w z pc_p' :
     cap_lang.decode w = Restrict PC (inl z) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PermPairFlowsTo (decodePermPair z) (pc_p,pc_g) = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ inr (decodePermPair z,pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ[pc_p'] w }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_reg (r,m) PC (inr (decodePermPair z, pc_b, pc_e,pc_a)))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Restrict PC (inl z))
                              (NextI,_)); eauto; simpl; try congruence.
       rewrite HPC Hflows /updatePC /update_reg /= /RegLocate lookup_insert Hpca' /=.
       destruct (decodePermPair z). auto.
       inv Hvpc. destruct H7 as [? | [? | ?]]; subst pc_p; auto.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC /= Hflows /updatePC /update_reg /RegLocate lookup_insert Hpca' /=.
       destruct (decodePermPair z); rewrite insert_insert.
       inv Hvpc. destruct H8 as [? | [? | ?]]; subst pc_p;
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
       iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame; eauto.
   Qed.

   Lemma wp_restrict_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 p g b e a z pc_p' :
     cap_lang.decode w = Restrict r1 (inl z) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PermPairFlowsTo (decodePermPair z) (p,g) = true →
     r1 ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
     {{{ RET match p with E => FailedV | _ => NextIV end;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,match p with E => pc_a | _ => pc_a' end)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r1 ↦ᵣ inr (match p with E => (p, g) | _ => decodePermPair z end,b,e,a) }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hflows Hne1 ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     option_locate_mr m r.
     assert (<[r1:=inr (decodePermPair z,b,e,a)]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),match p with E => _ | _ => _ end, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Restrict r1 (inl z))
                              (match p with E => _ | _ => _ end,_)); eauto; simpl; try congruence.
       rewrite Hr1 Hflows /updatePC /update_reg /= Hpc_new1 Hpca'. destruct p; reflexivity.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr1 /= Hflows.
       rewrite /updatePC /update_reg Hpc_new1 Hpca' /=.
       destruct p; try (
         iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]";
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto).
       simpl. iModIntro; iFrame. iSplitR; auto. iApply "Hϕ"; iFrame.
   Qed.

   Lemma wp_restrict_failPC1 Ep pc_p pc_g pc_b pc_e pc_a w n pc_p':
     cap_lang.decode w = Restrict PC (inl n) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     PermPairFlowsTo (decodePermPair n) (pc_p,pc_g) = false ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hflows;
     (iIntros (φ) "(HPC & Hpc_a) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
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
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict PC (inl n))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite HPC Hflows. destruct pc_p; reflexivity.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hflows /=.
       iFrame. iNext. iModIntro.
       iSplitR; auto. destruct pc_p; simpl; iFrame; by iApply "Hφ".
   Qed.

   Lemma wp_restrict_failPCreg1 Ep pc_p pc_g pc_b pc_e pc_a w n r1 pc_p' :
     cap_lang.decode w = Restrict PC (inr r1) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     PermPairFlowsTo (decodePermPair n) (pc_p,pc_g) = false →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r1 ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hflows;
     (iIntros (φ) "(HPC & Hpc_a & Hr1) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hr1") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict PC (inr r1))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite HPC Hr1 Hflows. destruct pc_p; reflexivity.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hr1 Hflows /=.
       iFrame. iNext. iModIntro.
       iSplitR; auto. destruct pc_p; simpl; iFrame; by iApply "Hφ".
   Qed.

   Lemma wp_restrict_failPC1' Ep pc_p pc_g pc_b pc_e pc_a w n pc_p' :
     cap_lang.decode w = Restrict PC (inl n) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     PermPairFlowsTo (decodePermPair n) (pc_p,pc_g) = true →
     (pc_a + 1)%a = None ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hflows Ha';
     (iIntros (φ) "(HPC & Hpc_a) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
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
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict PC (inl n))
                              (Failed, match pc_p with E => _ | _ => _ end));
         eauto; simpl; try congruence.
       rewrite HPC Hflows /updatePC /= /RegLocate lookup_insert Ha'.
       case_eq (decodePermPair n); intros; auto. rewrite <- H1. destruct pc_p; reflexivity.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iMod (@gen_heap_update with "Hr HPC") as "[Hr HPC]".
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_a.
       rewrite HPC Hflows /updatePC /= /RegLocate lookup_insert Ha' /=.
       iNext. iModIntro.
       iSplitR; auto.
       rewrite /update_reg. simpl. case_eq (decodePermPair n); intros; auto. rewrite <- H2.
       destruct pc_p; simpl; iFrame; try iApply "Hφ"; auto.
       inv Hvpc. destruct H9 as [? | [? | ?]]; congruence.
   Qed.

   Lemma wp_restrict_failPCreg1' Ep pc_p pc_g pc_b pc_e pc_a w n a' r1 pc_p' :
     cap_lang.decode w = Restrict PC (inr r1) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     PermPairFlowsTo (decodePermPair n) (pc_p,pc_g) = true →
     (pc_a + 1)%a = None ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r1 ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hflows Ha';
     (iIntros (φ) "(HPC & Hpc_a & Hr1) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hr1") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict PC (inr r1))
                              (Failed, match pc_p with E => _ | _ => _ end));
         eauto; simpl; try congruence.
       rewrite HPC Hr1 Hflows /updatePC /= /RegLocate lookup_insert Ha'.
       case_eq (decodePermPair n); intros; rewrite <- H1; auto.
       destruct pc_p; reflexivity.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iMod (@gen_heap_update with "Hr HPC") as "[Hr HPC]".
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_a.
       rewrite HPC Hr1 Hflows /updatePC /= /RegLocate lookup_insert Ha'.
       case_eq (decodePermPair n); intros; rewrite <- H2.
       iFrame. iNext. iModIntro.
       iSplitR; auto. destruct pc_p; simpl; iFrame; try iApply "Hφ"; auto.
       inv Hvpc. destruct H9 as [? | [? | ?]]; congruence.
   Qed.

   Lemma wp_restrict_fail1 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a n pc_p' :
     cap_lang.decode w = Restrict dst (inl n) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     PermPairFlowsTo (decodePermPair n) (p,g) = false →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hflows;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
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
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inl n))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst Hflows. auto. destruct p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hflows.
       iFrame. iNext. iModIntro.
       iSplitR; auto. destruct p; simpl; iFrame; by iApply "Hφ".
   Qed.

   Lemma wp_restrict_fail1' Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a n a' pc_p' :
     cap_lang.decode w = Restrict dst (inl n) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     PermPairFlowsTo (decodePermPair n) (p,g) = true →
     (pc_a + 1)%a = None ->
     dst <> PC ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hflows Ha' Hnepc;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
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
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inl n))
                              (Failed, match p with E => _ | _ => _ end));
         eauto; simpl; try congruence.
       rewrite Hdst Hflows /updatePC /= /RegLocate lookup_insert_ne; auto.
       rewrite /RegLocate in HPC. rewrite HPC Ha'. destruct p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       destruct (perm_eq_dec p E).
       + subst p. iModIntro.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
         rewrite Hdst /=. iNext. iModIntro. iSplitR; iFrame; auto.
         by iApply "Hφ".
       + iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
         iModIntro.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
         rewrite Hdst Hflows /updatePC /= /RegLocate lookup_insert_ne; auto.
         rewrite /RegLocate in HPC. rewrite HPC Ha'.
         iNext. iModIntro. iSplitR; auto.
         destruct p; simpl; iFrame; try (by iApply "Hφ"); congruence.
   Qed.

   Lemma wp_restrict_fail2 E dst src pc_p pc_g pc_b pc_e pc_a w n pc_p' :
     cap_lang.decode w = Restrict dst src →
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
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst src)
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

   Lemma wp_restrict_fail4 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg n pc_p' :
     cap_lang.decode w = Restrict dst (inr rg) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     PermPairFlowsTo (decodePermPair n) (p,g) = false →
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ rg ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hflows;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inr rg))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. rewrite Hrg. rewrite Hflows. destruct p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. rewrite Hrg. rewrite Hflows.
       iFrame. iNext. iModIntro.
       destruct p; simpl; iFrame; iSplitR; auto; by iApply "Hφ".
   Qed.

   Lemma wp_restrict_fail4' Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg n pc_p' :
     cap_lang.decode w = Restrict dst (inr rg) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     PermPairFlowsTo (decodePermPair n) (p,g) = true →
     (pc_a + 1)%a = None ->
     dst <> PC ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ rg ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hflows Ha' Hne;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inr rg))
                              (Failed,match p with E => _ | _ => _ end));
         eauto; simpl; try congruence.
       rewrite Hdst. rewrite Hrg. rewrite Hflows /updatePC /= /RegLocate lookup_insert_ne; auto.
       rewrite /RegLocate in HPC. rewrite HPC Ha'. destruct p; reflexivity.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       destruct (perm_eq_dec p E).
       + subst p; simpl. iModIntro.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
         rewrite Hdst Hrg /=. iNext. iModIntro. iSplitR; iFrame; auto.
         by iApply "Hφ".
       + iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
         iModIntro.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
         rewrite Hdst. rewrite Hrg. rewrite Hflows /updatePC /= /RegLocate lookup_insert_ne; auto.
         rewrite /RegLocate in HPC. rewrite HPC Ha'.
         iNext. iModIntro. iSplitR; auto.
         destruct p; simpl; iFrame; try iApply "Hφ"; auto; congruence.
   Qed.

   Lemma wp_restrict_failPC5 Ep pc_p pc_g pc_b pc_e pc_a w rg x pc_p' :
     cap_lang.decode w = Restrict PC (inr rg) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ rg ↦ᵣ inr x }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc;
     (iIntros (φ) "(HPC & Hpc_a & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict PC (inr rg))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite HPC. rewrite Hrg. auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC. rewrite Hrg. 
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_restrict_fail5 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg x pc_p' :
     cap_lang.decode w = Restrict dst (inr rg) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ rg ↦ᵣ inr x }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inr rg))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. rewrite Hrg. auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. rewrite Hrg.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_restrict_fail6 Ep dst pc_p pc_g pc_b pc_e pc_a w pc_p' :
     cap_lang.decode w = Restrict dst (inr PC) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc;
     (iIntros (φ) "(HPC & Hpc_a) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
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
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inr PC))
                              (Failed,_));
         eauto; simpl; try congruence.
       destruct (r !r! dst); auto.
       rewrite HPC. destruct c, p, p, p, p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC.
       destruct (r !r! dst); simpl;
       iFrame; iNext; iModIntro.
       iSplitR; auto. by iApply "Hφ".
       destruct c, p, p, p, p; simpl; iSplitR; auto; iFrame; by iApply "Hφ".
   Qed.

   Lemma wp_restrict_fail7 Ep dst pc_p pc_g pc_b pc_e pc_a w x pc_p' :
     cap_lang.decode w = Restrict dst (inr dst) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr x }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
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
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inr dst))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst.
       destruct x, p, p, p, p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst.
       iSplitR; auto. iNext. iModIntro.
       destruct x, p, p, p, p; simpl; auto; iFrame; by iApply "Hφ".
   Qed.

End cap_lang_rules.
