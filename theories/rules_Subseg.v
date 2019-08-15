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

  Lemma wp_subseg_success E pc_p pc_g pc_b pc_e pc_a pc_a' w dst r1 r2 p g b e a n1 n2 a1 a2:
    cap_lang.decode w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ r1 ↦ᵣ inl n1
          ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ w
             ∗ r1 ↦ᵣ inl n1
             ∗ r2 ↦ᵣ inl n2
             ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' [Hn1 Hn2] Hpne Hdstne Hwb ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r.
    assert (<[dst:=inr (p, g, a1, a2, a)]>
            r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),
      (updatePC (update_reg (r,m) dst (inr ((p, g), a1, a2, a)))).2,[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst (inr r1) (inr r2))
                             (cap_lang.NextI,_)); eauto; simpl; try congruence.
      rewrite Hdst. destruct p; (try congruence;
                                   by rewrite Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1 Hpca').
    - destruct p; try congruence;
        ((*iMod (fupd_intro_mask' ⊤) as "H"; eauto;*)
          iModIntro; iNext;
          iIntros (e1 σ2 efs Hstep);
          inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
          rewrite Hdst Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 Hpca' /=;
                  inv_head_step;
          iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
          iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
          iSpecialize ("Hϕ" with "[HPC Hdst Hr1 Hr2 Hpc_a]"); iFrame;
          iModIntro; done).
  Qed.

  Lemma wp_subseg_success_pc E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 n1 n2 a1 a2:
    cap_lang.decode w = Subseg PC (inr r1) (inr r2) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ inl n1
          ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,pc_a')
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' [Hn1 Hn2] Hpne Hwb ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r.
    assert (<[PC:=inr (pc_p, pc_g, a1, a2, pc_a)]>
            r !r! PC = inr (pc_p, pc_g, a1, a2, pc_a))
      as Hpc_new1; first by rewrite /RegLocate lookup_insert.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),
      (updatePC (update_reg (r,m) PC (inr ((pc_p, pc_g), a1, a2, pc_a)))).2,[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg PC (inr r1) (inr r2))
                             (cap_lang.NextI,_)); eauto; simpl; try congruence.
      rewrite HPC. destruct pc_p; (try congruence;
                                     by rewrite Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1 Hpca').
    - destruct pc_p; try congruence;
        ((*iMod (fupd_intro_mask' ⊤) as "H"; eauto;*)
          iModIntro; iNext;
          iIntros (e1 σ2 efs Hstep);
          inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
          rewrite HPC Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 Hpca' /= insert_insert;
          inv_head_step;
          rewrite HPC Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 Hpca' /= insert_insert
            in Hstep;
          iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
          iSpecialize ("Hϕ" with "[HPC]"); iFrame;
          iModIntro; done).
  Qed.

End cap_lang_rules.