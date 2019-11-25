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

  Lemma wp_move_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 z pc_p' :
    cap_lang.decode w = Mov r1 (inl z) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inl z }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    assert (<[r1:=inl z]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),(updatePC (update_reg (r,m) r1 (inl z))).2, [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Mov r1 (inl z))
                             (NextI,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= Hpc_new1 Hpca'.  
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= Hpc_new1 Hpca' /=.  
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]". 
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]". 
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 rv wrv pc_p' :
    cap_lang.decode w = Mov r1 (inr rv) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ wr1
          ∗ ▷ rv ↦ᵣ wrv }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ wrv
             ∗ rv ↦ᵣ wrv }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    iDestruct (@gen_heap_valid with "Hr Hrv") as %?.
    option_locate_mr m r.
    assert (<[r1:=wrv]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),(updatePC (update_reg (r,m) r1 wrv)).2, [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Mov r1 (inr rv))
                             (NextI,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= Hrv Hpc_new1 Hpca'.  
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= Hrv Hpc_new1 Hpca' /=.  
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]". 
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]". 
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a Hrv]"); iFrame; eauto.
  Qed.

  Lemma wp_move_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 pc_p' :
    cap_lang.decode w = Mov r1 (inr r1) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ wr1 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    assert (<[r1:=wr1]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),(updatePC (update_reg (r,m) r1 wr1)).2, [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Mov r1 (inr r1))
                             (NextI,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= Hr1 Hpc_new1 Hpca'.  
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= Hr1 Hpc_new1 Hpca' /=.  
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]". 
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_success_reg_samePC E pc_p pc_g pc_b pc_e pc_a pc_a' w pc_p' :
    cap_lang.decode w = Mov PC (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_, [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Mov PC (inr PC))
                              (_,_)); eauto; simpl; try congruence.
      rewrite /updatePC /update_reg /= /RegLocate lookup_insert.
      rewrite /RegLocate in HPC. rewrite HPC Hpca'. eauto.
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      rewrite /updatePC /update_reg /= /RegLocate lookup_insert.
      rewrite /RegLocate in HPC. rewrite HPC Hpca' /=.
      rewrite insert_insert.
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
      iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_success_reg_toPC E pc_p pc_g pc_b pc_e pc_a w r1 p g b e a a' pc_p' :
    cap_lang.decode w = Mov PC (inr r1) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (a + 1)%a = Some a' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((p,g),b,e,a')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inr ((p,g),b,e,a) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_, [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Mov PC (inr r1))
                              (NextI,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= Hr1 /RegLocate lookup_insert Hpca'.
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= Hr1 /RegLocate lookup_insert Hpca' /=.
      rewrite insert_insert.
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_success_reg_fromPC E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 pc_p' :
    cap_lang.decode w = Mov r1 (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    assert (<[r1:=inr ((pc_p,pc_g),pc_b,pc_e,pc_a)]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),(updatePC (update_reg (r,m) r1 (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)))).2, [].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Mov r1 (inr PC))
                             (NextI,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= HPC Hpc_new1 Hpca' /=.  
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= HPC Hpc_new1 Hpca' /=.  
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]". 
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]". 
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_fail_z E pc_p pc_g pc_b pc_e pc_a w r1 wr1 z pc_p' :
    cap_lang.decode w = Mov r1 (inl z) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inl z }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    assert (<[r1:=inl z]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_, [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Mov r1 (inl z))
                              (_,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= Hpc_new1 Hpca'.  
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= Hpc_new1 Hpca' /=.  
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]". 
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_fail_reg E pc_p pc_g pc_b pc_e pc_a w r1 wr1 rv wrv pc_p' :
    cap_lang.decode w = Mov r1 (inr rv) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ wr1
          ∗ ▷ rv ↦ᵣ wrv }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ wrv
             ∗ rv ↦ᵣ wrv }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    iDestruct (@gen_heap_valid with "Hr Hrv") as %?.
    option_locate_mr m r.
    assert (<[r1:=wrv]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_, [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Mov r1 (inr rv))
                              (_,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= Hrv Hpc_new1 Hpca'.  
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= Hrv Hpc_new1 Hpca' /=.  
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a Hrv]"); iFrame; eauto.
  Qed.

  Lemma wp_move_fail_reg_same E pc_p pc_g pc_b pc_e pc_a w r1 wr1 pc_p' :
    cap_lang.decode w = Mov r1 (inr r1) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ wr1 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    assert (<[r1:=wr1]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_, [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Mov r1 (inr r1))
                              (_,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= Hr1 Hpc_new1 Hpca'.  
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= Hr1 Hpc_new1 Hpca' /=.  
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]". 
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_fail_reg_samePC E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Mov PC (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_, [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Mov PC (inr PC))
                              (_,_)); eauto; simpl; try congruence.
      rewrite /updatePC /update_reg /= /RegLocate lookup_insert.
      rewrite /RegLocate in HPC. rewrite HPC Hpca'. eauto.
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      rewrite /updatePC /update_reg /= /RegLocate lookup_insert.
      rewrite /RegLocate in HPC. rewrite HPC Hpca' /=.
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
      iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_fail_reg_toPC E pc_p pc_g pc_b pc_e pc_a w r1 p g b e a pc_p' :
    cap_lang.decode w = Mov PC (inr r1) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (a + 1)%a = None →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((p,g),b,e,a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inr ((p,g),b,e,a) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_, [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Mov PC (inr r1))
                              (_,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= Hr1 /RegLocate lookup_insert Hpca'.
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= Hr1 /RegLocate lookup_insert Hpca' /=.
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
  Qed.

  Lemma wp_move_fail_reg_toPC2 E pc_p pc_g pc_b pc_e pc_a w nr1 z pc_p' :
    cap_lang.decode w = Mov PC nr1 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ (match nr1 with inr r1 => (r1 ↦ᵣ inl z) | inl m => ⌜m = z⌝ end) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inl z
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (match nr1 with inr r1 => r1 ↦ᵣ inl z | inl m => ⌜m = z⌝ end) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iAssert (⌜match nr1 with inl m => m = z | inr r1 => r !! r1 = Some (inl z) end⌝)%I with "[Hr Hr1]" as %?.
    { destruct nr1; auto.
      iDestruct (@gen_heap_valid with "Hr Hr1") as %?. auto. }
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible. destruct nr1.
      { iExists [], (Instr _),_, [].
        iPureIntro.
        constructor.
        eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                                (Mov PC _)
                                (_,_)); eauto; simpl; try congruence.
        rewrite Hpc_a. eauto.
        rewrite /updatePC /update_reg /= /RegLocate lookup_insert; eauto. }
      { iExists [], (Instr _),_, [].
        iPureIntro.
        constructor.
        eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                                (Mov PC _)
                                (_,_)); eauto; simpl; try congruence.
        rewrite Hpc_a. eauto.
        rewrite /updatePC /update_reg /= /RegLocate lookup_insert H4; eauto. }
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= /RegLocate.
      destruct nr1.
      { rewrite lookup_insert /=. subst z0.
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame; eauto. }
      { rewrite lookup_insert /= H4.
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto. }
  Qed.

  Lemma wp_move_fail_reg_fromPC E pc_p pc_g pc_b pc_e pc_a w r1 wr1 pc_p' :
    cap_lang.decode w = Mov r1 (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    assert (<[r1:=inr ((pc_p,pc_g),pc_b,pc_e,pc_a)]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),(updatePC (update_reg (r,m) r1 (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)))).2, [].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Mov r1 (inr PC))
                              (_,_)); eauto; simpl; try congruence.
        by rewrite /updatePC /update_reg /= HPC Hpc_new1 Hpca' /=.  
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite /updatePC /update_reg /= HPC Hpc_new1 Hpca' /=.  
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]". 
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
  Qed.

End cap_lang_rules.