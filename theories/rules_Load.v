From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
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

  Lemma wp_load_success E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    cap_lang.decode w = Load r1 r2 →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''  
          ∗ ▷ r2 ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ w' 
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ inr ((p,g),b,e,a)
             ∗ a ↦ₐ w' }}}. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hne1 φ)
            "(>Hpc & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hm Hr2a") as %?.
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r. 
    assert (<[r1:=m !m! a]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) r1 (MemLocate m a))).2,[].
      rewrite /updatePC Hpc_new1 Ha /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r2)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence. 
      rewrite /withinBounds in Hwb; rewrite Hr2 Hra Hwb /updatePC /= Hpc_new1.
        by rewrite Hpca' /update_reg /= Ha.
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hr2 Hra Hwb /update_reg /updatePC /= Hpc_new1 /=.
      inv_head_step.
      rewrite Hr2 Hra Hwb /= /update_reg /updatePC /= Hpc_new1 /update_reg /= in Hstep. 
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
      iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
      iSpecialize ("Hφ" with "[Hpc Hr1 Hr2 Hi Hr2a]"); iFrame.  
      iModIntro. done. 
  Qed.

  Lemma wp_load_success_same E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    cap_lang.decode w = Load r1 r1 →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ w
             ∗ a ↦ₐ w' }}}. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hne1 φ)
            "(>Hpc & >Hi & >Hr1 & >Hr1a) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hm Hr1a") as %?.
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r. 
    assert (<[r1:=m !m! a]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) r1 (MemLocate m a))).2,[].
      rewrite /updatePC Hpc_new1 Ha /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r1)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence. 
      rewrite /withinBounds in Hwb; rewrite Hr1 Hra Hwb /updatePC /= Hpc_new1.
        by rewrite Hpca' /update_reg /= Ha.
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hr1 Hra Hwb /update_reg /updatePC /= Hpc_new1 /=.
      inv_head_step.
      iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
      iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
      iSpecialize ("Hφ" with "[Hpc Hr1 Hi Hr1a]"); iFrame.  
      iModIntro. done. 
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a p' g' b' e' a' a'' :
    cap_lang.decode w = Load PC r2 →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ inr ((p',g'),b',e',a') }}} 
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((p',g'),b',e',a'')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ inr ((p,g),b,e,a)
             ∗ a ↦ₐ inr ((p',g'),b',e',a') }}}. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Ha'' φ)
            "(>Hpc & >Hi & >Hr2 & >Hr2a) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hm Hr2a") as %?.
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
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

  Lemma wp_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' :
    cap_lang.decode w = Load r1 PC →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w'' }}} 
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ w
             ∗ r1 ↦ᵣ w }}}. 
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hne φ)
            "(>Hpc & >Hi & >Hr1) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r. 
    assert (<[r1:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <=? pc_e)%a) = true). 
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

  Lemma wp_load_fail1 E r1 r2 pc_p pc_g pc_b pc_e pc_a w p g b e a :
    cap_lang.decode w = Load r1 r2 →

    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ∧
    (readAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ w
           ∗ r2 ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
                          ∗ pc_a ↦ₐ w
                          ∗ r2 ↦ᵣ inr ((p,g),b,e,a) }}}.
  Proof.
    intros Hinstr [Hvpc [Hnra | Hnwb]];
      (iIntros (φ) "(HPC & Hpc_a & Hr2) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
                                                      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
                                                                                                       iDestruct (@gen_heap_valid with "Hr Hr2") as %?;
                                                                                                                                                      option_locate_mr m r).
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

  Lemma wp_load_fail2 E r1 r2 pc_p pc_g pc_b pc_e pc_a w n:
    cap_lang.decode w = Load r1 r2 →

    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ w
           ∗ r2 ↦ᵣ inl n }}}
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, pc_a)
                          ∗ pc_a ↦ₐ w
                          ∗ r2 ↦ᵣ inl n }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "(HPC & Hpc_a & Hr2) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
        iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?;
                                                   iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
                                                                                                    iDestruct (@gen_heap_valid with "Hr Hr2") as %?;
                                                                                                                                                   option_locate_mr m r.
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

  Lemma wp_load_fail3 E pc_p pc_g pc_b pc_e pc_a w :
    cap_lang.decode w = Load PC PC →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ w
                          ∗ pc_a ↦ₐ w }}}. 
  Proof.
    iIntros (Hinstr Hvpc φ)
            "(>Hpc & >Hi) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    option_locate_mr m r. 
    assert (<[PC:=m !m! pc_a]> r !r! PC = m !m! pc_a)
      as Hpc_new1.
    { rewrite (locate_eq_reg _ _ (r !r! PC)); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <=? pc_e)%a) = true).
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

  Lemma wp_load_fail4 E src pc_p pc_g pc_b pc_e pc_a w p g b e a p' g' b' e' a' :
    cap_lang.decode w = Load PC src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (a' + 1)%a = None →
    PC ≠ src →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ src ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ inr ((p',g'),b',e',a') }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((p',g'),b',e',a')
                          ∗ pc_a ↦ₐ w
                          ∗ src ↦ᵣ inr ((p,g),b,e,a)
                          ∗ a ↦ₐ inr ((p',g'),b',e',a') }}}. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hnone Hne φ)
            "(>Hpc & >Hi & >Hsrc & >Ha) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hm Ha") as %?.
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
      rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Ha Hnone. eauto. 
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Ha Hnone /=.
      iFrame. iSplitR; auto.
      iMod (@gen_heap_update with "Hr Hpc") as "[Hr Hpc]". iFrame.
      iModIntro. iApply "Hφ". iFrame. 
  Qed.

  Lemma wp_load_fail5 E src pc_p pc_g pc_b pc_e pc_a w p g b e a z :
    cap_lang.decode w = Load PC src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    PC ≠ src →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ src ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ inl z }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inl z
                          ∗ pc_a ↦ₐ w
                          ∗ src ↦ᵣ inr ((p,g),b,e,a)
                          ∗ a ↦ₐ inl z }}}. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hne φ)
            "(>Hpc & >Hi & >Hsrc & >Ha) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hm Ha") as %?.
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
      rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Ha. eauto. 
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hsrc Hra Hwb /= /updatePC /update_reg /= Hpc_new1 Ha /=.
      iFrame. iSplitR; auto.
      iMod (@gen_heap_update with "Hr Hpc") as "[Hr Hpc]". iFrame.
      iModIntro. iApply "Hφ". iFrame. 
  Qed.

  Lemma wp_load_fail6 E dst pc_p pc_g pc_b pc_e pc_a w w' :
    cap_lang.decode w = Load dst PC →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    PC ≠ dst →
    (pc_a + 1)%a = None →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ dst ↦ᵣ w' }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
                          ∗ pc_a ↦ₐ w
                          ∗ dst ↦ᵣ w }}}. 
  Proof.
    iIntros (Hinstr Hvpc Hne Hpc_a' φ)
            "(>Hpc & >Hi & >Hdst) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    option_locate_mr m r. 
    assert (∀ a, <[dst:=m !m! a]> r !r! PC = r !r! PC)
      as Hpc_new1.
    { intros a.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <=? pc_e)%a) = true). 
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

  Lemma wp_load_fail7 E src dst pc_p pc_g pc_b pc_e pc_a w w' p g b e a w'' :
    cap_lang.decode w = Load dst src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    PC ≠ dst →
    (pc_a + 1)%a = None →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ src ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ w''
          ∗ ▷ dst ↦ᵣ w' }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
                          ∗ pc_a ↦ₐ w
                          ∗ src ↦ᵣ inr ((p,g),b,e,a)
                          ∗ a ↦ₐ w''
                          ∗ dst ↦ᵣ w'' }}}. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hne Hpc_a' φ)
            "(>Hpc & >Hi & >Hsrc & >Ha & >Hdst) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hm Ha") as %?.
    option_locate_mr m r. 
    assert (∀ a, <[dst:=m !m! a]> r !r! PC = r !r! PC)
      as Hpc_new1.
    { intros a0.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <=? pc_e)%a) = true). 
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
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hsrc Hra Hwb /= /updatePC /update_reg Hpc_new1 HPC Hpc_a' Ha /=.
      iFrame. iSplitR; auto.
      iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]". iFrame.
      iModIntro. iApply "Hφ". iFrame. 
  Qed.

  Lemma wp_load_fail8 E src pc_p pc_g pc_b pc_e pc_a w w' p g b e a w'' :
    cap_lang.decode w = Load src src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    PC ≠ src →
    (pc_a + 1)%a = None →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ src ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ w'' }}} 
      Instr Executable @ E
      {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
                          ∗ pc_a ↦ₐ w
                          ∗ src ↦ᵣ w''
                          ∗ a ↦ₐ w'' }}}. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hne Hpc_a' φ)
            "(>Hpc & >Hi & >Hsrc & >Ha) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hm Ha") as %?.
    option_locate_mr m r. 
    assert (∀ a, <[src:=m !m! a]> r !r! PC = r !r! PC)
      as Hpc_new1.
    { intros a0.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    assert (readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <=? pc_e)%a) = true). 
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
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hsrc Hra Hwb /= /updatePC /update_reg Hpc_new1 HPC Hpc_a' Ha /=.
      iFrame. iSplitR; auto.
      iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]". iFrame.
      iModIntro. iApply "Hφ". iFrame. 
  Qed.

End cap_lang_rules.