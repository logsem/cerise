From cap_machine Require Export lang.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac auth gmap agree.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invG Σ;
  mem_gen_memG :> gen_heapG Addr Word Σ;
}.
(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invG Σ;
  reg_gen_regG :> gen_heapG RegName Word Σ; (* TODO: change this to agreement  *)
(*                                              instead of exclusive agreement *)
                  }.

(* Class regG Σ := RegG { *)
(*    reg_invG : invG Σ; *)
(*    reg_gen_regG :> gen_regG RegName Word Σ }. *)

  

(* invariants for memory, and a state interpretation for (mem,reg) *)
Instance memG_irisG `{memG Σ, regG Σ} : irisG cap_lang Σ := {
  iris_invG := mem_invG;
  state_interp σ κs _ := ((gen_heap_ctx σ.1) ∗ (gen_heap_ctx σ.2))%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

(* Points to predicates *)
Notation "r ↦ᵣ{ q } w" := (mapsto (L:=RegName) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (mapsto (L:=RegName) (V:=Word) r 1 w) (at level 20) : bi_scope.

Notation "a ↦ₐ { q } w" := (mapsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ { q }  w") : bi_scope.
Notation "a ↦ₐ w" := (mapsto (L:=Addr) (V:=Word) a 1 w) (at level 20) : bi_scope.

Lemma heap_mapsto_notduplicable `{memG Σ} a w :
  (a ↦ₐ w ∗ a ↦ₐ w → False)%I. 
Proof.
  iIntros "[Ha1 Ha2]".
  iCombine "Ha1 Ha2" as "Ha".
  iDestruct (mapsto_valid with "Ha") as %Hf. contradiction.  
Qed.

(* temporary and permanent invariants *)
Inductive inv_kind := T | F. 
Definition logN : namespace := nroot .@ "logN".

Definition inv_cap `{memG Σ, regG Σ, inG Σ fracR} (t : inv_kind) P (ι : namespace) (γ : gname) :=
  match t with
  | T => inv ι (P ∨ (own γ 1%Qp))%I
  | F => inv ι P
  end. 

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr. 
  Implicit Types e : option Addr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word. 


  Lemma locate_ne_reg reg r1 r2 w w' :
    r1 ≠ r2 → reg !r! r1 = w → <[r2:=w']> reg !r! r1 = w.
  Proof.
    intros. rewrite /RegLocate.
    rewrite lookup_partial_alter_ne; eauto.
  Qed.

  Lemma locate_ne_mem mem a1 a2 w w' :
    a1 ≠ a2 → mem !m! a1 = w → <[a2:=w']> mem !m! a1 = w.
  Proof.
    intros. rewrite /MemLocate.
    rewrite lookup_partial_alter_ne; eauto.
  Qed. 

  Ltac inv_head_step :=
    repeat match goal with
           | _ => progress simplify_map_eq/= (* simplify memory stuff *)
           | H : to_val _ = Some _ |- _ => apply of_to_val in H
           | H : _ = of_val ?v |- _ =>
             is_var v; destruct v; first[discriminate H|injection H as H]
           | H : prim_step ?e _ _ _ _ _ |- _ =>
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
    | H : cap_lang.prim_step Executable (r, m) _ ?e1 ?σ2 _ |- _ =>
      let e0 := fresh "e" in
      let σ := fresh "σ" in
      let o := fresh "o" in
      let e' := fresh "e'" in
      let σ' := fresh "σ'" in
      let Hstep' := fresh "Hstep'" in
      let He0 := fresh "H"e0 in
      let Ho := fresh "H"o in
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
      inversion H as [e0 σ o e' σ' Hstep' He0 Ho He' Hσ' Hefs];
      inversion Hstep' as [φ0 | φ0 p0 g0 b0 e2 a0 i c0 HregPC ? Hi Hexec];
        (simpl in *; try congruence );
      subst e1 σ2 φ0 σ' e' o σ; try subst c0; simpl in *;
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
 (* ----------------------------------- FAIL RULES ---------------------------------- *)
  
  
   Lemma wp_load_fail r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a :
    cap_lang.decode w = Load r1 r2 →

    (¬ isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))) ∨
    (isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ∧
     (readAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ w
           ∗ r1 ↦ᵣ w''  
           ∗ r2 ↦ᵣ inr ((p,g),b,e,a)
           ∗ a ↦ₐ w' }}}
      Executable
    {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr [Hnpc | [Hvpc [Hnra | Hnwb]]];
     (iIntros (φ) "(HPC & Hpc_a & Hr1 & Hr2 & Ha) Hφ";
       iApply wp_lift_step_fupd; eauto;
       iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hm Ha") as %?;
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
       iDestruct (@gen_heap_valid with "Hr Hr2") as %?;
       option_locate_mr m r).
     - rewrite -HPC in Hnpc. 
       iApply fupd_frame_l. 
       iSplit.
       + rewrite /reducible.
         iExists [], (Failed : cap_lang.expr), (r,m), [].
         iPureIntro.
         constructor.
         apply (step_exec_fail (r,m)); eauto.
       + iMod (fupd_intro_mask' ⊤) as "H"; eauto.
         iModIntro. 
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
         iFrame. iModIntro. iNext.
         iApply fupd_frame_l. iFrame.
         iApply wp_value. by iApply "Hφ". 
     - iApply fupd_frame_l. 
       iSplit.
       + rewrite /reducible.
         iExists [], Failed, (r,m), [].
         iPureIntro.
         constructor.
         apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r2)
                                (Failed,_));
           eauto; simpl; try congruence. 
           by rewrite Hr2 Hnra /=.
       + iMod (fupd_intro_mask' ⊤) as "H"; eauto.
       iModIntro. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hr2 Hnra /=.
       iFrame. iModIntro. iNext.
       iApply fupd_frame_l. iFrame.
       iApply wp_value. by iApply "Hφ".
     - simpl in *. 
       iApply fupd_frame_l. 
       iSplit.
       + rewrite /reducible.
         iExists [], Failed, (r,m), [].
         iPureIntro.
         constructor.
         apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r2)
                                (Failed,_));
           eauto; simpl; try congruence.
           by rewrite Hr2 Hnwb andb_false_r. 
       + iMod (fupd_intro_mask' ⊤) as "H"; eauto.
         iModIntro. 
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
         rewrite Hr2 Hnwb andb_false_r. 
         iFrame. iModIntro. iNext.
         iApply fupd_frame_l. iFrame.
         iApply wp_value. by iApply "Hφ".
   Qed.


 (* --------------------------------------------------------------------------------- *)
 (* -------------------------------- SUCCESS RULES ---------------------------------- *)
   
   Lemma wp_load_success r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a φ :
    cap_lang.decode w = Load r1 r2 →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    r1 ≠ PC →
    
    ▷ ( PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(pc_a + 1)%Z) ∗ r1 ↦ᵣ w' -∗
      WP Executable {{ φ }} )
    ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
    ∗ pc_a ↦ₐ w
    ∗ r1 ↦ᵣ w''  
    ∗ r2 ↦ᵣ inr ((p,g),b,e,a)
    ∗ a ↦ₐ w'
    ⊢
    WP Executable {{ φ }}.
   Proof.
     intros Hinstr Hvpc [Hra Hwb] Hne1. 
     iIntros "(Hφ & Hpc & Hi & Hr1 & Hr2 & Hr2a)".
     iApply wp_lift_step_fupd; eauto.
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
       iExists [], Executable, (updatePC (update_reg (r,m) r1 (MemLocate m a))).2,[].
       rewrite /updatePC Hpc_new1 Ha /update_reg /=.
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Load r1 r2)
                              (Executable,_));
         eauto; simpl; try congruence. 
        rewrite /withinBounds in Hwb; rewrite Hr2 Hra Hwb /updatePC /= Hpc_new1.
          by rewrite /update_reg /= Ha.
     - iMod (fupd_intro_mask' ⊤) as "H"; eauto.
       iModIntro. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr2 Hra Hwb /update_reg /updatePC /= Hpc_new1 /=.
       inv_head_step.
       rewrite Hr2 Hra Hwb /= /update_reg /updatePC /= Hpc_new1 /update_reg /= in Hstep. 
       iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
       iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
       iSpecialize ("Hφ" with "[Hpc Hr1]"); iFrame.  
       iModIntro. iNext. iFrame. 
   Qed.        

   
   Lemma wp_jmp_success pc_p pc_g pc_b pc_e pc_a w r g b e a φ :
     cap_lang.decode w = Jmp r →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     ▷ ( PC ↦ᵣ inr ((RX,g),b,e,a) -∗  WP Executable {{ φ }} )
       ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
       ∗ pc_a ↦ₐ w
       ∗ r ↦ᵣ inr ((E,g),b,e,a)
       ⊢
       WP Executable {{ φ }}.
   Proof.
     intros Hinstr Hvpc.
     iIntros "(Hφ & HPC & Hpc_a & Hr)".
     iApply wp_lift_step_fupd; eauto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr0 Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
     option_locate_mr m r0.
     iApply fupd_frame_l. 
     iSplit.
     - rewrite /reducible.
       iExists [],Executable,(<[PC:=inr (RX, g, b, e, a)]> r0, m),[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a (Jmp r)
                              (Executable,_)); eauto; simpl; try congruence.
         by rewrite Hr /updatePcPerm /update_reg /=.
     - iMod (fupd_intro_mask' ⊤) as "H"; eauto.
       iModIntro. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hr /updatePcPerm /=.
       inv_head_step.
       rewrite Hr /updatePcPerm /update_reg /= in Hstep.
       iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
       iSpecialize ("Hφ" with "[HPC]"); iFrame.  
       iModIntro. iNext. iFrame. 
   Qed.
   

   Lemma wp_subseg_success pc_p pc_g pc_b pc_e pc_a w dst r1 r2 p g b e a n1 n2 φ :
     cap_lang.decode w = Subseg dst (inr r1) (inr r2) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     p ≠ E →
     dst ≠ PC →
     isWithin n1 n2 b e = true →
     
     ▷ ( PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(pc_a + 1)%Z)
            ∗ dst ↦ᵣ inr (p, g, n1, if (n2 =? -42)%Z then None else Some n2, a)
            -∗  WP Executable {{ φ }} )
       ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
       ∗ pc_a ↦ₐ w
       ∗ dst ↦ᵣ inr ((p,g),b,e,a)
       ∗ r1 ↦ᵣ inl n1
       ∗ r2 ↦ᵣ inl n2      
       ⊢
       WP Executable {{ φ }}.
   Proof.
     intros Hinstr Hvpc Hpne Hdstne Hwb.
     iIntros "(Hφ & HPC & Hpc_a & Hdst & Hr1 & Hr2)".
     iApply wp_lift_step_fupd; eauto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
     option_locate_mr m r.
     assert (<[dst:=inr (p, g, n1, if (n2 =? -42)%Z then None
                                   else Some n2, a)]>
             r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
     iApply fupd_frame_l. 
     iSplit.
     - rewrite /reducible.
       iExists [],Executable,
       (updatePC (update_reg (r,m) dst (inr ((p, g), n1,
            if Z.eqb n2 (-42)%Z then None else Some n2, a)))).2,[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Subseg dst (inr r1) (inr r2))
                              (Executable,_)); eauto; simpl; try congruence.
       rewrite Hdst. destruct p; (try congruence;
       by rewrite Hr1 Hr2 Hwb /updatePC /update_reg /= Hpc_new1).
     - destruct p; try congruence;
        (iMod (fupd_intro_mask' ⊤) as "H"; eauto;
         iModIntro;
         iIntros (e1 σ2 efs Hstep);
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
         rewrite Hdst Hr1 Hr2 Hwb /updatePC /update_reg Hpc_new1 /=;
         inv_head_step;
         rewrite Hdst Hr1 Hr2 Hwb /updatePC /update_reg Hpc_new1 /= in Hstep;
         iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hφ" with "[HPC Hdst]"); iFrame;
         iModIntro; iNext; iFrame).
   Qed.

   Lemma wp_subseg_success_pc pc_p pc_g pc_b pc_e pc_a w r1 r2 n1 n2 φ :
     cap_lang.decode w = Subseg PC (inr r1) (inr r2) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     pc_p ≠ E →
     isWithin n1 n2 pc_b pc_e = true →
     
     ▷ ( PC ↦ᵣ inr ((pc_p,pc_g),n1,if (n2 =? -42)%Z then None else Some n2,(pc_a + 1)%Z)
            -∗  WP Executable {{ φ }} )
       ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
       ∗ pc_a ↦ₐ w
       ∗ r1 ↦ᵣ inl n1
       ∗ r2 ↦ᵣ inl n2      
       ⊢
       WP Executable {{ φ }}.
   Proof.
     intros Hinstr Hvpc Hpne Hwb.
     iIntros "(Hφ & HPC & Hpc_a & Hr1 & Hr2)".
     iApply wp_lift_step_fupd; eauto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
     option_locate_mr m r.
     assert (<[PC:=inr (pc_p, pc_g, n1, if (n2 =? -42)%Z then None
                                   else Some n2, pc_a)]>
             r !r! PC = inr (pc_p, pc_g, n1, if (n2 =? -42)%Z then None
                                   else Some n2, pc_a))
       as Hpc_new1; first by rewrite /RegLocate lookup_insert. 
     iApply fupd_frame_l. 
     iSplit.
     - rewrite /reducible.
       iExists [],Executable,
       (updatePC (update_reg (r,m) PC (inr ((pc_p, pc_g), n1,
            if Z.eqb n2 (-42)%Z then None else Some n2, pc_a)))).2,[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Subseg PC (inr r1) (inr r2))
                              (Executable,_)); eauto; simpl; try congruence.
       rewrite HPC. destruct pc_p; (try congruence;
       by rewrite Hr1 Hr2 Hwb /updatePC /update_reg /= Hpc_new1).
     - destruct pc_p; try congruence;
        (iMod (fupd_intro_mask' ⊤) as "H"; eauto;
         iModIntro;
         iIntros (e1 σ2 efs Hstep);
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
         rewrite HPC Hr1 Hr2 Hwb /updatePC /update_reg Hpc_new1 /= insert_insert;
         inv_head_step;
         rewrite HPC Hr1 Hr2 Hwb /updatePC /update_reg Hpc_new1 /= insert_insert
           in Hstep;
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hφ" with "[HPC]"); iFrame;
         iModIntro; iNext; iFrame).
   Qed.

   Lemma wp_IsPtr_success_S pc_p pc_g pc_b pc_e pc_a w dst r ptr w' φ :
     cap_lang.decode w = IsPtr dst r →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     dst ≠ PC →  

      ▷ ( PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(pc_a+1)%Z) ∗ dst ↦ᵣ inl 1%Z
            -∗  WP Executable {{ φ }} )
       ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
       ∗ pc_a ↦ₐ w
       ∗ r ↦ᵣ inr ptr
       ∗ dst ↦ᵣ w'
       ⊢
       WP Executable {{ φ }}.
   Proof.
     intros Hinstr Hvpc Hne.
     iIntros "(Hφ & HPC & Hpc_a & Hr & Hdst)".
     iApply wp_lift_step_fupd; eauto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr0 Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
     iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr0 Hdst") as %?.
     option_locate_mr m r0.
     assert (<[dst:=inl 1%Z]> r0 !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a))) as Hpc_new1.
     { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
     iApply fupd_frame_l. 
     iSplit.
     - rewrite /reducible.
       iExists [], Executable,(<[PC:=inr (pc_p, pc_g, pc_b, pc_e, (pc_a + 1)%Z)]> (<[dst:=inl 1%Z]> r0), m), [].
       iPureIntro.
       constructor. 
       apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a
                              (IsPtr dst r)
                              (Executable,_)); eauto; simpl; try congruence.
         by rewrite Hr /update_reg /updatePC /= Hpc_new1 /update_reg /updatePC /=.
     - iMod (fupd_intro_mask' ⊤) as "H"; eauto.
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr /updatePC /update_reg /= Hpc_new1 /=.
       iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
       iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
       iSpecialize ("Hφ" with "[HPC Hdst]"); iFrame.
       iModIntro. iNext. iFrame.
   Qed.

   Lemma wp_IsPtr_success_F pc_p pc_g pc_b pc_e pc_a w dst r z w' φ :
     cap_lang.decode w = IsPtr dst r →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     dst ≠ PC →  

      ▷ ( PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(pc_a+1)%Z) ∗ dst ↦ᵣ inl 0%Z
            -∗  WP Executable {{ φ }} )
       ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
       ∗ pc_a ↦ₐ w
       ∗ r ↦ᵣ inl z
       ∗ dst ↦ᵣ w'
       ⊢
       WP Executable {{ φ }}.
   Proof.
     intros Hinstr Hvpc Hne.
     iIntros "(Hφ & HPC & Hpc_a & Hr & Hdst)".
     iApply wp_lift_step_fupd; eauto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr0 Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
     iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr0 Hdst") as %?.
     option_locate_mr m r0.
     assert (<[dst:=inl 0%Z]> r0 !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a))) as Hpc_new1.
     { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
     iApply fupd_frame_l. 
     iSplit.
     - rewrite /reducible.
       iExists [], Executable,(<[PC:=inr (pc_p, pc_g, pc_b, pc_e, (pc_a + 1)%Z)]> (<[dst:=inl 0%Z]> r0), m), [].
       iPureIntro.
       constructor. 
       apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a
                              (IsPtr dst r)
                              (Executable,_)); eauto; simpl; try congruence.
       by rewrite Hr /update_reg /updatePC /= Hpc_new1 /update_reg /updatePC /=.
     - iMod (fupd_intro_mask' ⊤) as "H"; eauto.
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr /updatePC /update_reg /= Hpc_new1 /=.
       iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
       iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
       iSpecialize ("Hφ" with "[HPC Hdst]"); iFrame.
       iModIntro. iNext. iFrame.
   Qed.


   Lemma wp_store_success_local pc_p pc_g pc_b pc_e pc_a w dst src w'
         p g b e a p' g' b' e' a' φ :
     cap_lang.decode w = Store dst (inr src) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     isLocal g' = true ∧ (p = RWLX ∨ p = RWL) → 
     dst ≠ PC →

     ▷ ( PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(pc_a+1)%Z) ∗ a ↦ₐ inr ((p',g'),b',e',a') 
            -∗  WP Executable {{ φ }} )
       ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
       ∗ pc_a ↦ₐ w
       ∗ src ↦ᵣ inr ((p',g'),b',e',a')
       ∗ dst ↦ᵣ inr ((p,g),b,e,a)  
       ∗ a ↦ₐ w'
       ⊢
       WP Executable {{ φ }}.
   Proof.
     intros Hinstr Hvpc [Hwa Hwb] [Hlocal Hp] Hne; simpl in *. 
     iIntros "(Hφ & HPC & Hpc_a & Hsrc & Hdst & Ha)".
     iApply wp_lift_step_fupd; eauto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid with "Hm Ha") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l. 
     iSplit.
     - rewrite /reducible.
       iExists [],Executable,(updatePC (update_mem (r,m) a (RegLocate r src))).2, [].
       iPureIntro.
       constructor. 
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store dst (inr src))
                              (Executable,_)); eauto; simpl; try congruence.
       rewrite Hdst Hwa Hwb /= Hsrc Hlocal.
       destruct Hp as [Hp | Hp]; try contradiction;
         by rewrite Hp /updatePC /update_mem /= HPC.
     - iMod (fupd_intro_mask' ⊤) as "H"; eauto.
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hwa Hwb /= Hsrc Hlocal.
       destruct Hp as [Hp | Hp]; try contradiction;
       ( rewrite Hp /updatePC /update_mem /= HPC /update_reg /=;
         iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]";
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hφ" with "[HPC Ha]"); iFrame; eauto ). 
   Qed. 
       
         
   (* Store dst (inr src) => *)
   (*    match RegLocate (reg φ) dst with *)
   (*    | inl n => (Failed, φ) *)
   (*    | inr ((p, g), b, e, a) => *)
   (*      if writeAllowed p && withinBounds ((p, g), b, e, a) then *)
   (*        match RegLocate (reg φ) src with *)
   (*        | inl n => updatePC (update_mem φ a (RegLocate (reg φ) src)) *)
   (*        | inr ((_, g'), _, _, _) => if isLocal g' then *)
   (*                                     match p with *)
   (*                                     | RWLX | RWL => updatePC (update_mem φ a (RegLocate (reg φ) src)) *)
   (*                                     | _ => (Failed, φ) *)
   (*                                     end *)
   (*                                   else updatePC (update_mem φ a (RegLocate (reg φ) src)) *)
   (*        end *)
   (*      else (Failed, φ) *)
   (*    end *)
       
       
 (* --------------------------------------------------------------------------------- *)
 (* ----------------------------------- ATOMIC RULES -------------------------------- *)

   Lemma wp_halt pc_p pc_g pc_b pc_e pc_a w :
     cap_lang.decode w = Halt →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ w }}}
       Executable 
     {{{ RET HaltedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ w }}}.
   Proof.
     intros Hinstr Hvpc. 
     iIntros (φ) "[Hpc Hpca] Hφ".
     iApply wp_lift_atomic_step_fupd; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
     option_locate_mr m r. 
     iModIntro.
     iSplitR.
     - rewrite /reducible. 
       iExists [],Halted,(r,m),[].       
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a Halt
                              (Halted,_));
         eauto; simpl; try congruence.
     - iIntros (e2 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       iFrame.
       iModIntro. iNext. iModIntro. iSplitL; eauto. 
       iApply "Hφ".
       iFrame.
   Qed.

End cap_lang_rules. 