From cap_machine.rules Require Export rules_base
     rules_Get rules_Load rules_AddSubLt
     rules_Lea rules_Mov rules_IsPtr
     rules_Restrict rules_Jmp rules_Jnz
     rules_Subseg rules_Store. 
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

(* --------------------------------------------------------------------------------- *)
 (* -------------------------------- SUCCESS RULES ---------------------------------- *)

     
 (* --------------------------------------------------------------------------------- *)
 (* ----------------------------------- FAIL RULES ---------------------------------- *)

  Lemma wp_notCorrectPC:
    forall E w,
      ~ isCorrectPC w ->
      {{{ PC ↦ᵣ w }}}
        Instr Executable @ E
        {{{ RET FailedV; PC ↦ᵣ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    option_locate_mr m r.
    rewrite -HPC in Hnpc.
    iApply fupd_frame_l.
    iSplit.
    + rewrite /reducible.
      iExists [], (Instr Failed : cap_lang.expr), (r,m), [].
      iPureIntro.
      constructor. 
      apply (step_exec_fail (r,m)); eauto.
    + (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
      iModIntro.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      iFrame. iNext.
      iModIntro. iSplitR; auto. iApply "Hϕ". iFrame. 
  Qed.


 (* --------------------------------------------------------------------------------- *)
 (* ----------------------------------- ATOMIC RULES -------------------------------- *)

   Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a w pc_p' :
     cap_lang.decode w = Halt →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
     {{{ RET HaltedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ[pc_p'] w }}}.
   Proof.
     intros Hinstr Hfl Hvpc.
     iIntros (φ) "[Hpc Hpca] Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpca") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     option_locate_mr m r.
     iModIntro.
     iSplitR.
     - rewrite /reducible.
       iExists [],(Instr Halted),(r,m),[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a Halt
                              (Halted,_));
         eauto; simpl; try congruence.
     - iIntros (e2 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       iFrame.
       iNext. iModIntro. iSplitR; eauto.
       iApply "Hφ".
       iFrame.
   Qed.

   Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a w pc_p' :
     cap_lang.decode w = Fail →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
     {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ[pc_p'] w }}}.
   Proof.
     intros Hinstr Hfl Hvpc.
     iIntros (φ) "[Hpc Hpca] Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpca") as %?.
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     option_locate_mr m r.
     iModIntro.
     iSplitR.
     - rewrite /reducible.
       iExists [],(Instr Failed),(r,m),[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a Fail
                              (Failed,_));
         eauto; simpl; try congruence.
     - iIntros (e2 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       iFrame.
       iNext. iModIntro. iSplitR; eauto.
       iApply "Hφ".
       iFrame.
    Qed.


 (* --------------------------------------------------------------------------------- *)
 (* ----------------------------------- PURE RULES ---------------------------------- *)
  
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_exec_pure := intros ?; apply nsteps_once, pure_head_step_pure_step;
                                constructor; [solve_exec_safe|]; intros;
                                (match goal with
                                | H : head_step _ _ _ _ _ _ |- _ => inversion H end).
 
  Global Instance pure_seq_failed :
    PureExec True 1 (Seq (Instr Failed)) (Instr Failed).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_halted :
    PureExec True 1 (Seq (Instr Halted)) (Instr Halted).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_done :
    PureExec True 1 (Seq (Instr NextI)) (Seq (Instr Executable)).
  Proof. by solve_exec_pure. Qed.
    
    
End cap_lang_rules. 