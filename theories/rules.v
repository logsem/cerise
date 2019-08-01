From cap_machine Require Export lang.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invG Σ;
  mem_gen_memG :> gen_heapG Addr Word Σ; }.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invG Σ;
  reg_gen_regG :> gen_heapG RegName Word Σ; }.


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

(* temporary and permanent invariants *)
Inductive inv_kind := T | P. 
Definition logN : namespace := nroot .@ "logN".

Definition inv_cap `{memG Σ, regG Σ, inG Σ fracR} (t : inv_kind) iP (ι : namespace) (γ : gname) :=
  match t with
  | T => inv ι (iP ∨ (own γ 1%Qp))%I
  | P => inv ι iP
  end. 

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


  Lemma locate_ne_reg reg r1 r2 w w' :
    r1 ≠ r2 → reg !r! r1 = w → <[r2:=w']> reg !r! r1 = w.
  Proof.
    intros. rewrite /RegLocate.
    rewrite lookup_partial_alter_ne; eauto.
  Qed.

  Lemma locate_eq_reg reg r1 w w' :
    reg !r! r1 = w → <[r1:=w']> reg !r! r1 = w'.
  Proof.
    intros. rewrite /RegLocate.
    rewrite lookup_partial_alter; eauto.
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

  Lemma wp_geta_success E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w' src p g b e a :
    cap_lang.decode w = GetA dst src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ dst ↦ᵣ w'
          ∗ ▷ src ↦ᵣ (inr ((p,g),b,e,a)) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
           ∗ pc_a ↦ₐ w
           ∗ dst ↦ᵣ inl (z_of a)
           ∗ src ↦ᵣ (inr ((p,g),b,e,a)) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hdst & >Hsrc) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    option_locate_mr m r. 
    assert (∀ w, <[dst:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
    { intros.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) dst (inl (z_of a)))).2,[].
      rewrite /updatePC Hpc_new1 /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (GetA dst src)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence.
      destruct a.
      by rewrite Hsrc /updatePC /update_reg /= Hpc_new1 Hpca'.       
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      destruct a. 
      rewrite Hsrc /updatePC /update_reg /= Hpc_new1 Hpca'. 
      inv_head_step.
      iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
      iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
      iSpecialize ("Hφ" with "[Hpc Hdst Hsrc Hi]"); iFrame.  
      iModIntro. done. 
  Qed.

  Lemma wp_getb_success E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w' src p g b e a :
    cap_lang.decode w = GetB dst src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ dst ↦ᵣ w'
          ∗ ▷ src ↦ᵣ (inr ((p,g),b,e,a)) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
           ∗ pc_a ↦ₐ w
           ∗ dst ↦ᵣ inl (z_of b)
           ∗ src ↦ᵣ (inr ((p,g),b,e,a)) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hdst & >Hsrc) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    option_locate_mr m r. 
    assert (∀ w, <[dst:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
    { intros.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) dst (inl (z_of b)))).2,[].
      rewrite /updatePC Hpc_new1 /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (GetB dst src)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence.
      destruct b.
      by rewrite Hsrc /updatePC /update_reg /= Hpc_new1 Hpca'.       
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      destruct b. 
      rewrite Hsrc /updatePC /update_reg /= Hpc_new1 Hpca'. 
      inv_head_step.
      iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
      iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
      iSpecialize ("Hφ" with "[Hpc Hdst Hsrc Hi]"); iFrame.  
      iModIntro. done. 
  Qed.

  Lemma wp_gete_success_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst p g b e a :
    cap_lang.decode w = GetE dst dst →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ dst ↦ᵣ (inr ((p,g),b,e,a)) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
           ∗ pc_a ↦ₐ w
           ∗ dst ↦ᵣ inl (z_of e) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hdst) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    option_locate_mr m r. 
    assert (∀ w, <[dst:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
    { intros.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) dst (inl (z_of e)))).2,[].
      rewrite /updatePC Hpc_new1 /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (GetE dst dst)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence.
      destruct e.
      by rewrite /updatePC /update_reg /= Hdst Hpc_new1 Hpca'.       
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      destruct e. 
      rewrite /updatePC /update_reg /= Hdst Hpc_new1 Hpca'.       
      inv_head_step.
      iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
      iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
      iSpecialize ("Hφ" with "[Hpc Hdst Hi]"); iFrame.  
      iModIntro. done. 
  Qed.

  Lemma wp_gete_success E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w' p g b e a :
    cap_lang.decode w = GetE dst src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ src ↦ᵣ (inr ((p,g),b,e,a))
          ∗ ▷ dst ↦ᵣ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
           ∗ pc_a ↦ₐ w
           ∗ dst ↦ᵣ inl (z_of e)
           ∗ src ↦ᵣ (inr ((p,g),b,e,a)) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hsrc & >Hdst) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hi") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
    option_locate_mr m r. 
    assert (∀ w, <[dst:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
    { intros.
      rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
    iApply fupd_frame_l. 
    iSplit.  
    - rewrite /reducible. 
      iExists [], (Instr _), (updatePC (update_reg (r,m) dst (inl (z_of e)))).2,[].
      rewrite /updatePC Hpc_new1 /update_reg /=.
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (GetE dst src)
                             (cap_lang.NextI,_));
        eauto; simpl; try congruence.
      destruct e.
      by rewrite /updatePC /update_reg /= Hsrc Hpc_new1 Hpca'.  
    - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
      iModIntro. iNext. 
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      destruct e. 
      rewrite /updatePC /update_reg /= Hsrc Hpc_new1 Hpca'.  
      inv_head_step.
      iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
      iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
      iSpecialize ("Hφ" with "[Hpc Hdst Hsrc Hi]"); iFrame.  
      iModIntro. done. 
  Qed.
  
  Lemma wp_sub_success_z_z E r1 z1 z2 pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
    cap_lang.decode w = Sub r1 (inl z1) (inl z2) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w' }}}
      Instr Executable @ E
    {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ inl (z1 - z2)%Z
             ∗ pc_a ↦ₐ w }}}. 
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hr1) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hi") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     option_locate_mr m r. 
     assert (∀ w, <[r1:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { intros.
       rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l. 
     iSplit.  
     - rewrite /reducible. 
       iExists [], (Instr _), (updatePC (update_reg (r,m) r1 _)).2,[].
       rewrite /updatePC Hpc_new1 /update_reg /=.
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Sub r1 (inl z1) (inl z2))
                              (cap_lang.NextI,_));
         eauto; simpl; try congruence.
       rewrite /updatePC /= Hpc_new1 Hpca' /update_reg /=. eauto. 
     - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
       iModIntro. iNext. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite /updatePC /= Hpc_new1 Hpca' /update_reg /=.
       inv_head_step.
       iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
       iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
       iSpecialize ("Hφ" with "[Hpc Hr1 Hi]"); iFrame.  
       iModIntro. done. 
  Qed.

  Lemma wp_sub_success_r_r_src_same E r2 r1 pc_p pc_g pc_b pc_e pc_a pc_a' w z1 z2 :
    cap_lang.decode w = Sub r2 (inr r1) (inr r2) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    r2 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ inl z1
          ∗ ▷ r1 ↦ᵣ inl z2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r2 ↦ᵣ inl (z2 - z1)%Z
             ∗ r1 ↦ᵣ inl z2
             ∗ pc_a ↦ₐ w }}}. 
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hr2 & >Hr1) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hi") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
     option_locate_mr m r. 
     assert (∀ w, <[r2:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { intros.
       rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l. 
     iSplit.  
     - rewrite /reducible. 
       iExists [], (Instr _), (updatePC (update_reg (r,m) r2 _)).2,[].
       rewrite /updatePC Hpc_new1 /update_reg /=.
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Sub r2 (inr r1) (inr r2))
                              (cap_lang.NextI,_));
         eauto; simpl; try congruence.
       rewrite /updatePC /= Hr1 Hr2 Hpc_new1 Hpca' /update_reg /=. eauto.
     - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
       iModIntro. iNext. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite /updatePC /= Hr1 Hr2 Hpc_new1 Hpca' /update_reg /=.
       inv_head_step.
       iMod (@gen_heap_update with "Hr Hr2") as "[Hr Hr2]".
       iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
       iSpecialize ("Hφ" with "[Hpc Hr1 Hr2 Hi]"); iFrame.  
       iModIntro. done. 
  Qed.

  Lemma wp_sub_success_r_r_dst_same E r2 r1 pc_p pc_g pc_b pc_e pc_a pc_a' w z1 z2 :
    cap_lang.decode w = Sub r1 (inr r1) (inr r2) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ inl z1
          ∗ ▷ r1 ↦ᵣ inl z2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r2 ↦ᵣ inl z1
             ∗ r1 ↦ᵣ inl (z2 - z1)%Z
             ∗ pc_a ↦ₐ w }}}. 
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hr2 & >Hr1) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hi") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
     option_locate_mr m r. 
     assert (∀ w, <[r1:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { intros.
       rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l. 
     iSplit.  
     - rewrite /reducible. 
       iExists [], (Instr _), (updatePC (update_reg (r,m) r1 _)).2,[].
       rewrite /updatePC Hpc_new1 /update_reg /=.
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Sub r1 (inr r1) (inr r2))
                              (cap_lang.NextI,_));
         eauto; simpl; try congruence.
       rewrite /updatePC /= Hr1 Hr2 Hpc_new1 Hpca' /update_reg /=. eauto.
     - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
       iModIntro. iNext. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite /updatePC /= Hr1 Hr2 Hpc_new1 Hpca' /update_reg /=.
       inv_head_step.
       iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
       iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
       iSpecialize ("Hφ" with "[Hpc Hr1 Hr2 Hi]"); iFrame.  
       iModIntro. done. 
  Qed.

  Lemma wp_sub_success_r_z_dst_same E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w z1 z2 :
    cap_lang.decode w = Sub r1 (inr r1) (inl z2) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ inl z1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ inl (z1 - z2)%Z
             ∗ pc_a ↦ₐ w }}}. 
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hr1) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hi") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     option_locate_mr m r. 
     assert (∀ w, <[r1:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { intros.
       rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l. 
     iSplit.  
     - rewrite /reducible. 
       iExists [], (Instr _), (updatePC (update_reg (r,m) r1 _)).2,[].
       rewrite /updatePC Hpc_new1 /update_reg /=.
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Sub r1 (inr r1) (inl z2))
                              (cap_lang.NextI,_));
         eauto; simpl; try congruence.
       rewrite /updatePC /= Hr1  Hpc_new1 Hpca' /update_reg /=. eauto.
     - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
       iModIntro. iNext. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite /updatePC /= Hr1 Hpc_new1 Hpca' /update_reg /=.
       inv_head_step.
       iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
       iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
       iSpecialize ("Hφ" with "[Hpc Hr1 Hi]"); iFrame.  
       iModIntro. done. 
  Qed.

  Lemma wp_lt_success E dst r1 z1 r2 z2 pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
    cap_lang.decode w = cap_lang.Lt dst (inr r1) (inr r2) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ dst ↦ᵣ w'
          ∗ ▷ r1 ↦ᵣ inl z1
          ∗ ▷ r2 ↦ᵣ inl z2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ w
             ∗ dst ↦ᵣ inl (Z.b2z (z1 <? z2)%Z)
             ∗ r1 ↦ᵣ inl z1
             ∗ r2 ↦ᵣ inl z2 }}}.
  Proof. 
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hdst & >Hr1 & >Hr2) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hi") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
     option_locate_mr m r. 
     assert (∀ w, <[dst:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { intros.
       rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l. 
     iSplit.  
     - rewrite /reducible. 
       iExists [], (Instr _), (updatePC (update_reg (r,m) dst _)).2,[].
       rewrite /updatePC Hpc_new1 /update_reg /=.
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (cap_lang.Lt dst (inr r1) (inr r2))
                              (cap_lang.NextI,_));
         eauto; simpl; try congruence.
       rewrite Hr1 Hr2 /updatePC /= Hpc_new1 Hpca' /update_reg /=. eauto. 
     - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
       iModIntro. iNext. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr1 Hr2 /updatePC /= Hpc_new1 Hpca' /update_reg /=.
       inv_head_step.
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
       iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
       iSpecialize ("Hφ" with "[Hpc Hdst Hr1 Hr2 Hi]"); iFrame.  
       iModIntro. done. 
  Qed.

  Lemma wp_add_success_r_z_same E r1 z1 z2 pc_p pc_g pc_b pc_e pc_a pc_a' w :
    cap_lang.decode w = cap_lang.Add r1 (inr r1) (inl z2) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ PC →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ inl z1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ inl (z1 + z2)%Z
             ∗ pc_a ↦ₐ w }}}. 
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hne φ)
            "(>Hpc & >Hi & >Hr1) Hφ". 
    iApply wp_lift_atomic_head_step_no_fork; auto.    
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hi") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     option_locate_mr m r. 
     assert (∀ w, <[r1:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { intros.
       rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l. 
     iSplit.  
     - rewrite /reducible. 
       iExists [], (Instr _), (updatePC (update_reg (r,m) r1 _)).2,[].
       rewrite /updatePC Hpc_new1 /update_reg /=.
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (cap_lang.Add r1 (inr r1) (inl z2))
                              (cap_lang.NextI,_));
         eauto; simpl; try congruence.
       rewrite Hr1 /updatePC /= Hpc_new1 Hpca' /update_reg /=. eauto. 
     - (* iMod (fupd_intro_mask' E ∅) as "H"; first solve_ndisj.  *)       
       iModIntro. iNext. 
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr1 /updatePC /= Hpc_new1 Hpca' /update_reg /=.
       inv_head_step.
       iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]".
       iMod (@gen_heap_update with "Hr Hpc") as "[$ Hpc]".
       iSpecialize ("Hφ" with "[Hpc Hr1 Hi]"); iFrame.  
       iModIntro. done. 
  Qed.
  
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

  (* If a points to a capability, the load into PC success is its address can be incr *)
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
  
   Lemma wp_jmp_success E pc_p pc_g pc_b pc_e pc_a w r w':
     cap_lang.decode w = Jmp r →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r ↦ᵣ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ updatePcPerm w' ∗ pc_a ↦ₐ w ∗ r ↦ᵣ w' }}}.
   Proof.
     iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr0 Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
     option_locate_mr m r0.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _), (<[PC:=_]> r0, m),[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a (Jmp r)
                              (cap_lang.NextI,_)); eauto; simpl; try congruence.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hr /updatePcPerm /=.
       iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
       iSpecialize ("Hφ" with "[HPC Hr Hpc_a]"); iFrame.
       by iModIntro. 
   Qed.

   Lemma wp_jnz_success_jmp E r1 r2 pc_p pc_g pc_b pc_e pc_a w w1 w2 :
     cap_lang.decode w = Jnz r1 r2 →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     w2 ≠ inl 0%Z →
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ w1
           ∗ ▷ r2 ↦ᵣ w2 }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ updatePcPerm w1
              ∗ pc_a ↦ₐ w
              ∗ r1 ↦ᵣ w1
              ∗ r2 ↦ᵣ w2 }}}.
   Proof.
     iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _), (<[PC:=updatePcPerm w1]> r, m),[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Jnz r1 r2)
                              (cap_lang.NextI,_)); eauto; simpl; try congruence.
       rewrite Hr2 Hr1 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
       destruct w2; auto.
       assert (Zneq_bool z 0 = true); [destruct z; try contradiction; done|]. 
       by rewrite H1. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hr2 Hr1 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
       destruct w2;
         [assert (Zneq_bool z 0 = true); [destruct z; try contradiction; done|];
          rewrite H2 /=|];
         (inv_head_step;
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hφ" with "[HPC Hr1 Hr2 Hpc_a]"); iFrame;
         by iModIntro). 
   Qed.

   Lemma wp_jnz_success_next E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_a' w :
     cap_lang.decode w = Jnz r1 r2 →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r2 ↦ᵣ inl 0%Z }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ r2 ↦ᵣ inl 0%Z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _), (<[PC:=inr ((pc_p,pc_g),pc_b,pc_e,pc_a')]> r, m),[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Jnz r1 r2)
                              (cap_lang.NextI,_)); eauto; simpl; try congruence.
       rewrite Hr2 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
       by rewrite Hpc_a' /update_reg /=.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hr2 /updatePC HPC Hpc_a' /=. 
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hφ" with "[HPC Hr2 Hpc_a]"); iFrame.
         by iModIntro. 
   Qed.          
     

   Lemma wp_restrict_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst p g b e a z p' g' :
     cap_lang.decode w = Restrict dst (inl z) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     decodePermPair z = (p',g') →
     PermPairFlowsTo (p',g') (p,g) = true →
     dst ≠ PC →
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ E
     {{{ RET NextIV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
                        ∗ pc_a ↦ₐ w
                        ∗ dst ↦ᵣ inr ((p',g'),b,e,a) }}}.
   Proof. 
     iIntros (Hinstr Hvpc Hpc_a' Hdcp Hflow Hne ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     option_locate_mr m r.
     assert (∀ w, <[dst:=w]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     {intros. rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _), (_, m),[].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inl z))
                              (cap_lang.NextI,_)); eauto; simpl; try congruence.
       by rewrite Hdst Hdcp Hflow /updatePC /= Hpc_new1 Hpc_a' /update_reg /=. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hdcp Hflow /updatePC /= Hpc_new1 Hpc_a' /update_reg /=. 
       inv_head_step.
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hφ" with "[HPC Hdst Hpc_a]"); iFrame.
       iModIntro. done.
   Qed.
   
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
              ∗ dst ↦ᵣ inr (p, g, a1, if (a2 =? -42)%a then A MemNum eq_refl else a2, a)
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
     assert (<[dst:=inr (p, g, a1, if (a2 =? -42)%a then (A MemNum eq_refl)
                                   else a2, a)]>
             r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),
       (updatePC (update_reg (r,m) dst (inr ((p, g), a1,
            if (a2 =? (-42))%a then (A MemNum eq_refl) else a2, a)))).2,[].
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
           PC ↦ᵣ inr ((pc_p,pc_g),a1,if (a2 =? -42)%a then (A MemNum eq_refl) else a2,pc_a')
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
     assert (<[PC:=inr (pc_p, pc_g, a1, if (a2 =? -42)%a then (A MemNum eq_refl)
                                   else a2, pc_a)]>
             r !r! PC = inr (pc_p, pc_g, a1, if (a2 =? -42)%a then (A MemNum eq_refl)
                                   else a2, pc_a))
       as Hpc_new1; first by rewrite /RegLocate lookup_insert.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),
       (updatePC (update_reg (r,m) PC (inr ((pc_p, pc_g), a1,
            if (a2 =? (-42))%a then (A MemNum eq_refl) else a2, pc_a)))).2,[].
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

   Lemma wp_IsPtr_success_S E pc_p pc_g pc_b pc_e pc_a pc_a' w dst r ptr w' :
     cap_lang.decode w = IsPtr dst r →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     dst ≠ PC →

       {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↦ₐ w
             ∗ ▷ r ↦ᵣ inr ptr
             ∗ ▷ dst ↦ᵣ w'
       }}}
       Instr Executable @ E {{{ RET NextIV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a') ∗ dst ↦ᵣ inl 1%Z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr & >Hdst) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
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
       iExists [], (Instr _),(<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a')]> (<[dst:=inl 1%Z]> r0), m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a
                              (IsPtr dst r)
                              (NextI,_)); eauto; simpl; try congruence.
         by rewrite Hr /update_reg /updatePC /= Hpc_new1 Hpca' /update_reg /updatePC /=.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr /updatePC /update_reg /= Hpc_new1 Hpca' /=.
       iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
       iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[HPC Hdst]"); iFrame.
       iModIntro. done.
   Qed.

   Lemma wp_IsPtr_success_F E pc_p pc_g pc_b pc_e pc_a pc_a' w dst r z w':
     cap_lang.decode w = IsPtr dst r →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r ↦ᵣ inl z
           ∗ ▷ dst ↦ᵣ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
           ∗ dst ↦ᵣ inl 0%Z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hne Φ) "(>HPC & >Hpc_a & >Hr & >Hdst) HΦ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
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
       iExists [], (Instr _), (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a')]> (<[dst:=inl 0%Z]> r0), m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a
                              (IsPtr dst r)
                              (NextI,_)); eauto; simpl; try congruence.
       by rewrite Hr /update_reg /updatePC /= Hpc_new1 Hpca' /update_reg /updatePC /=.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr /updatePC /update_reg /= Hpc_new1 Hpca' /=.
       iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
       iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
       iSpecialize ("HΦ" with "[HPC Hdst]"); iFrame.
       iModIntro. done.
   Qed.

   Lemma wp_store_success_local_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a p' g' b' e' a' :
     cap_lang.decode w = Store dst (inr src) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     isLocal g' = true ∧ (p = RWLX ∨ p = RWL) →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ inr ((p',g'),b',e',a')
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ a ↦ₐ inr ((p',g'),b',e',a') }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] [Hlocal Hp] Hne ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
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
       iExists [], (Instr _),(updatePC (update_mem (r,m) a (RegLocate r src))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store dst (inr src))
                              (NextI,_)); eauto; simpl; try congruence.
       simpl in Hwb.
       rewrite Hdst Hwa Hwb /= Hsrc Hlocal.
       destruct Hp as [Hp | Hp]; try contradiction;
         by rewrite Hp /updatePC /update_mem /= HPC Hpca'.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Hwa Hwb /= Hsrc Hlocal.
       destruct Hp as [Hp | Hp]; try contradiction;
       ( rewrite Hp /updatePC /update_mem /= HPC /update_reg /= Hpca';
         iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]";
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hϕ" with "[HPC Ha]"); iFrame; eauto ).
   Qed.

   Lemma wp_store_success_z_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a z :
     cap_lang.decode w = Store dst (inr src) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ inl z
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ inl z
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ inl z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] Hne ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
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
       iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]".
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
   Qed.

    Lemma wp_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' :
     cap_lang.decode w = Store dst (inr src) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     (isLocalWord w'' = false ∨ (p = RWLX ∨ p = RWL)) →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ w'' }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] Hcond Hne ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
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
       + iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]".
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
       + destruct c,p0,p0,p0. destruct Hcond as [Hfalse | Hlocal].
         { simpl in Hfalse. rewrite Hfalse.
           iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]".
           iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
           iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
         }
         { destruct (isLocal l); simpl.
           - destruct Hlocal as [Hp | Hp]; simplify_eq; simpl;
             (iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]";
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
              iSpecialize ("Hϕ" with "[-]"); iFrame; eauto).
           - (iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]";
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
              iSpecialize ("Hϕ" with "[-]"); iFrame; eauto).
         }
   Qed.

   Lemma wp_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a :
     cap_lang.decode w = Store dst (inr dst) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     (isLocal g = false ∨ (p = RWLX ∨ p = RWL)) →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ inr ((p,g),b,e,a) }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] Hcond Hne ϕ) "(>HPC & >Hpc_a & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid with "Hm Ha") as %?.
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
         iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]".
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
       + destruct (isLocal g); simpl. 
         { destruct Hlocal as [Hp | Hp]; simplify_eq; simpl;
             (iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]";
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
              iSpecialize ("Hϕ" with "[-]"); iFrame; eauto).
         } 
         iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]".
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[-]"); iFrame; eauto.
   Qed. 

   Lemma wp_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a :
     cap_lang.decode w = Store dst (inl z) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     dst ≠ PC →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ inl z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] Hne ϕ) "(>HPC & >Hpc_a & >Hdst & >Ha) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
     iDestruct (@gen_heap_valid with "Hm Ha") as %?.
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
       iMod (@gen_heap_update with "Hm Ha") as "[$ Ha]".
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[HPC Ha Hpc_a Hdst]"); iFrame; eauto.
   Qed.

   Lemma wp_lea_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv p g b e a z a' :
     cap_lang.decode w = Lea r1 (inr rv) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ PC → p ≠ E →
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ rv ↦ᵣ inl z
              ∗ r1 ↦ᵣ inr ((p,g),b,e,a') }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hne1 Hnep ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     iDestruct (@gen_heap_valid with "Hr Hrv") as %?.
     option_locate_mr m r.
     assert (<[r1:=inr ((p,g),b,e,a')]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_reg (r,m) r1 (inr ((p,g),b,e,a')))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Lea r1 (inr rv))
                              (NextI,_)); eauto; simpl; try congruence.
       rewrite Hrv Hr1.
       destruct p; try contradiction;
         by rewrite Ha' /updatePC /update_reg /= Hpc_new1 Hpca'. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr1 Hrv /= Ha'.
       destruct p; try contradiction; 
         rewrite /updatePC /update_reg Hpc_new1 Hpca' /= ;
         iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]";
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hϕ" with "[HPC Hr1 Hrv Hpc_a]"); iFrame; eauto. 
   Qed.
   
   Lemma wp_lea_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 p g b e a z a' :
     cap_lang.decode w = Lea r1 (inl z) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ PC → p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ inr ((p,g),b,e,a') }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hne1 Hnep ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
     iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
     option_locate_mr m r.
     assert (<[r1:=inr ((p,g),b,e,a')]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
       as Hpc_new1.
     { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. } 
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_reg (r,m) r1 (inr ((p,g),b,e,a')))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Lea r1 (inl z))
                              (NextI,_)); eauto; simpl; try congruence.
       rewrite Hr1.
       destruct p; try contradiction;
         by rewrite Ha' /updatePC /update_reg /= Hpc_new1 Hpca'. 
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite Hr1 /= Ha'.
       destruct p; try contradiction; 
         rewrite /updatePC /update_reg Hpc_new1 Hpca' /= ;
         iMod (@gen_heap_update with "Hr Hr1") as "[Hr Hr1]";
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame; eauto.
   Qed.


   Lemma wp_move_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 z :
     cap_lang.decode w = Mov r1 (inl z) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PC ≠ r1 →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ wr1 }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ inl z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
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

   Lemma wp_move_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 rv wrv :
     cap_lang.decode w = Mov r1 (inr rv) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PC ≠ r1 →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ wr1
           ∗ ▷ rv ↦ᵣ wrv }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ wrv
            ∗ rv ↦ᵣ wrv }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
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

   Lemma wp_move_success_reg_fromPC E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 :
     cap_lang.decode w = Mov r1 (inr PC) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PC ≠ r1 →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ wr1 }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?.
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
     
 (* --------------------------------------------------------------------------------- *)
 (* ----------------------------------- FAIL RULES ---------------------------------- *)

  Lemma wp_notCorrectPC:
    forall E pc_p pc_g pc_b pc_e pc_a,
      ~ isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
      {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) }}}
        Instr Executable @ E
        {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) }}}.
  Proof.
    intros until 0. intros Hnpc.
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

   Lemma wp_store_fail1 E dst src pc_p pc_g pc_b pc_e pc_a w p g b e a :
     cap_lang.decode w = Store dst src →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     (writeAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false) →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc HnwaHnwb;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      option_locate_mr m r).
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

   Lemma wp_store_fail2 E dst src pc_p pc_g pc_b pc_e pc_a w n:
     cap_lang.decode w = Store dst src →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inl n}}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc.
     iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
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

   Lemma wp_store_fail3 E dst src pc_p pc_g pc_b pc_e pc_a w p g b e a p' g' b' e' a':
     cap_lang.decode w = Store dst (inr src) →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     writeAllowed p = true ->
     withinBounds ((p, g), b, e, a) = true →
     isLocal g' = true ->
     p <> RWLX ->
     p <> RWL ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ src ↦ᵣ inr ((p',g'),b',e',a') }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc Hwa Hwb Hloc Hnrwlx Hnrwl;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hsrc) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hsrc") as %?;
      option_locate_mr m r).
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

   Lemma wp_lea_fail1 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a n:
     cap_lang.decode w = Lea dst (inl n) →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     (p = E \/ (a + n)%a = None) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc HpHa;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      option_locate_mr m r).
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst (inl n))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. destruct (perm_eq_dec p E).
       + subst p; auto.
       + destruct HpHa as [Hp | Ha]; try congruence.
         rewrite Ha. destruct p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. assert (X:match p with
                              | E => (Failed, (r, m))
                              | _ =>
                                match (a + n)%a with
                                | Some a' =>
                                  updatePC (update_reg (r, m) dst (inr (p, g, b, e, a')))
                                | None => (Failed, (r, m))
                                end
                              end = (Failed, (r, m))).
       { destruct (perm_eq_dec p E).
         - subst p; auto.
         - destruct HpHa as [Hp | Ha]; try congruence.
           rewrite Ha. destruct p; auto. }
       repeat rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_lea_fail2 E dst src pc_p pc_g pc_b pc_e pc_a w n:
     cap_lang.decode w = Lea dst src →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inl n}}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc.
     iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
     iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
     option_locate_mr m r.
     iApply fupd_frame_l. iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,m), [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst src)
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

   Lemma wp_lea_fail3 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg:
     cap_lang.decode w = Lea dst (inr rg) →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     p = E ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc Hp;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      option_locate_mr m r).
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst (inr rg))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. subst p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. subst p.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.
   
   Lemma wp_lea_fail4 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg n:
     cap_lang.decode w = Lea dst (inr rg) →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     p <> E ->
     (a + n)%a = None ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ rg ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc Hp Ha;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      option_locate_mr m r).
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst (inr rg))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. rewrite Hrg. rewrite Ha.
       destruct p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. rewrite Hrg. rewrite Ha.
       assert (X: match p with | O | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct p; auto).
       rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_lea_fail5 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg x:
     cap_lang.decode w = Lea dst (inr rg) →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     p <> E ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ rg ↦ᵣ inr x }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc Hp;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      option_locate_mr m r).
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst (inr rg))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. rewrite Hrg.
       destruct p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. rewrite Hrg.
       assert (X: match p with | O | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct p; auto).
       rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_restrict_fail1 E dst src pc_p pc_g pc_b pc_e pc_a w n:
     cap_lang.decode w = Restrict dst src →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inl n }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      option_locate_mr m r).
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst src)
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. destruct src; auto.
     - iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst.
       assert (X: match src with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct src; auto).
       rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_restrict_fail2 E dst src pc_p pc_g pc_b pc_e pc_a w permPair b e a x:
     cap_lang.decode w = Restrict dst (inr src) →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ dst ↦ᵣ inr (permPair, b, e, a)
            ∗ src ↦ᵣ inr x }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hsrc) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hsrc") as %?;
      option_locate_mr m r).
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Restrict dst (inr src))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. rewrite Hsrc. auto.
     - iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. rewrite Hsrc.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_add_sub_lt_fail1 E dst r1 pc_p pc_g pc_b pc_e pc_a w x y:
     cap_lang.decode w = cap_lang.Add dst (inr r1) y \/ cap_lang.decode w = Sub dst (inr r1) y \/ cap_lang.decode w = Lt dst (inr r1) y →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ inr x }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc;
     (iIntros (φ) "(HPC & Hpc_a & Hr1) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hr1") as %?;
      option_locate_mr m r).
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       destruct Hinstr as [Hinstr | [Hinstr | Hinstr]].
       + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (cap_lang.Add dst (inr r1) y)
                              (Failed,_));
         eauto; simpl; try congruence.
         rewrite Hr1. destruct y; auto.
       + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Sub dst (inr r1) y)
                              (Failed,_));
         eauto; simpl; try congruence.
         rewrite Hr1. destruct y; auto.
       + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lt dst (inr r1) y)
                              (Failed,_));
         eauto; simpl; try congruence.
         rewrite Hr1. destruct y; auto.
     - iModIntro.
       iIntros (e1 σ2 efs Hstep). destruct Hinstr as [Hinstr | [Hinstr | Hinstr]];
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       + rewrite Hr1. assert (X: match y with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct y; auto).
         rewrite X.
         iFrame. iNext. iModIntro.
         iSplitR; auto. by iApply "Hφ".
       + rewrite Hr1. assert (X: match y with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct y; auto).
         rewrite X.
         iFrame. iNext. iModIntro.
         iSplitR; auto. by iApply "Hφ".
       + rewrite Hr1. assert (X: match y with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct y; auto).
         rewrite X.
         iFrame. iNext. iModIntro.
         iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_add_sub_lt_fail2 E dst r2 pc_p pc_g pc_b pc_e pc_a w x y:
     cap_lang.decode w = cap_lang.Add dst x (inr r2) \/ cap_lang.decode w = Sub dst x (inr r2) \/ cap_lang.decode w = Lt dst x (inr r2) →

     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ w
            ∗ r2 ↦ᵣ inr y }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hvpc;
     (iIntros (φ) "(HPC & Hpc_a & Hr2) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?;
      iDestruct (@gen_heap_valid with "Hr Hr2") as %?;
      option_locate_mr m r).
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       destruct Hinstr as [Hinstr | [Hinstr | Hinstr]].
       + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (cap_lang.Add dst x (inr r2))
                              (Failed,_));
         eauto; simpl; try congruence.
         rewrite Hr2. destruct x; auto. destruct (r !r! r0); auto.
       + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Sub dst x (inr r2))
                              (Failed,_));
         eauto; simpl; try congruence.
         rewrite Hr2. destruct x; auto. destruct (r !r! r0); auto.
       + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lt dst x (inr r2))
                              (Failed,_));
         eauto; simpl; try congruence.
         rewrite Hr2. destruct x; auto. destruct (r !r! r0); auto.
     - iModIntro.
       iIntros (e1 σ2 efs Hstep). destruct Hinstr as [Hinstr | [Hinstr | Hinstr]];
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       + rewrite Hr2. assert (X: match x with
                  | inl _ => (Failed, (r, m))
                  | inr r1 => match r !r! r1 with
                              | inl _ | _ => (Failed, (r, m))
                              end
                                 end = (Failed, (r, m))).
         { destruct x; auto. destruct (r !r! r0); auto. }
         rewrite X.
         iFrame. iNext. iModIntro.
         iSplitR; auto. by iApply "Hφ".
       + rewrite Hr2. assert (X: match x with
                  | inl _ => (Failed, (r, m))
                  | inr r1 => match r !r! r1 with
                              | inl _ | _ => (Failed, (r, m))
                              end
                                 end = (Failed, (r, m))).
         { destruct x; auto. destruct (r !r! r0); auto. }
         rewrite X.
         iFrame. iNext. iModIntro.
         iSplitR; auto. by iApply "Hφ".
       + rewrite Hr2. assert (X: match x with
                  | inl _ => (Failed, (r, m))
                  | inr r1 => match r !r! r1 with
                              | inl _ | _ => (Failed, (r, m))
                              end
                                 end = (Failed, (r, m))).
         { destruct x; auto. destruct (r !r! r0); auto. }
         rewrite X.
         iFrame. iNext. iModIntro.
         iSplitR; auto. by iApply "Hφ".
   Qed.

       
       
 (* --------------------------------------------------------------------------------- *)
 (* ----------------------------------- ATOMIC RULES -------------------------------- *)

   Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a w :
     cap_lang.decode w = Halt →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ w }}}
       Instr Executable @ E
     {{{ RET HaltedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ w }}}.
   Proof.
     intros Hinstr Hvpc.
     iIntros (φ) "[Hpc Hpca] Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
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

   Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a w :
     cap_lang.decode w = Fail →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     
     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ w }}}
       Instr Executable @ E
     {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ w }}}.
   Proof.
     intros Hinstr Hvpc.
     iIntros (φ) "[Hpc Hpca] Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
     iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
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

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------- DERIVED MACRO RULES ----------------------------- *)

  (* ------------------------------------ STACK -------------------------------------- *)
  Lemma wp_push_success_z Ep r r_stk pc_p pc_g pc_b pc_e pc_a pc_a1 pc_a2 w w' z wa
    g b e a a' φ :
    cap_lang.decode w = Lea r_stk (inl 1%Z) →
    cap_lang.decode w' = Store r_stk (inr r) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a1 →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a1)) →
    (pc_a1 + 1)%a = Some pc_a2 →
    withinBounds (RWLX,g,b,e,a') = true →
                
    (a + 1)%a = Some a' →
    r_stk ≠ PC → 

    ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
      ∗ ▷ pc_a ↦ₐ w
      ∗ ▷ pc_a1 ↦ₐ w'
      ∗ ▷ r_stk ↦ᵣ inr ((RWLX,g),b,e,a)
      ∗ ▷ r ↦ᵣ inl z
      ∗ ▷ a' ↦ₐ wa
      ∗ ▷ ▷ ( PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a2)
                 ∗ pc_a ↦ₐ w
                 ∗ pc_a1 ↦ₐ w'
                 ∗ r_stk ↦ᵣ inr ((RWLX,g),b,e,a')
                 ∗ r ↦ᵣ inl z
                 ∗ a' ↦ₐ inl z -∗ WP Seq (Instr Executable) @ Ep {{ φ }}) ⊢
      WP Seq (Instr Executable) @ Ep {{ φ }}. 
  Proof.
    intros Hil His Hvpca Ha1 Hvpca1 Ha2 Hwb Ha' Hne.
    iIntros "(HPC & Hpc_a & Hpc_a1 & Hr_stk & Hr & Ha' & Hφ)". 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ pc_a _ _ _ RWLX with "[-Hpc_a1 Hr Ha' Hφ]");
      eauto. iFrame.
    iNext. iIntros "(HPC & Hpc_a & Hr_stk) /=".
    iApply wp_pure_step_later. eauto. iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_reg _ _ _ _ _ pc_a1 _ _ _ _ _ RWLX with "[-Hφ Hpc_a]");
      eauto. iFrame.
    iNext. iIntros "(HPC & Hpc_a1 & Hr & Hr_stk & Ha') /=".
    iApply wp_pure_step_later; auto. iNext. 
    iApply "Hφ". iFrame. 
  Qed. 
 
    
    
End cap_lang_rules. 