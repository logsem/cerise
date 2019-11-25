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

  Lemma wp_jmp_success E pc_p pc_g pc_b pc_e pc_a w r w' pc_p':
    cap_lang.decode w = Jmp r →
    PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r ↦ᵣ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ updatePcPerm w'
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ r ↦ᵣ w' }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
    option_locate_mr m r0.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _), (<[PC:=updatePcPerm w']> r0, m),[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a (Jmp r)
                             (cap_lang.NextI,_)); eauto; simpl; try congruence.
        by rewrite Hr /updatePcPerm /update_reg /=.
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
      rewrite Hr /=.
      inv_head_step.
      rewrite /update_reg /= in Hstep.
      iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
      iSpecialize ("Hφ" with "[HPC Hpc_a Hr]"); iFrame.
      iModIntro. done.
  Qed.

  Lemma wp_jmp_successPC E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Jmp PC →
    PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ updatePcPerm (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))
           ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _), (<[PC:=updatePcPerm (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))]> r, m),[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Jmp PC)
                             (cap_lang.NextI,_)); eauto; simpl; try congruence.
        by rewrite HPC /updatePcPerm /update_reg /=.
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      rewrite HPC /=.
      inv_head_step.
      rewrite /update_reg /= in Hstep.
      iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
      iSpecialize ("Hφ" with "[HPC Hpc_a]"); iFrame.
      iModIntro. done.
  Qed.

End cap_lang_rules.
  