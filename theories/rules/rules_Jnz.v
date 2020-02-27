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

  Inductive Jnz_spec (regs: Reg) (dst src: RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Jnz_spec_failure w:
      regs !! src = Some w ->
      nonZero w = false ->
      incrementPC regs = None ->
      regs = regs' ->
      Jnz_spec regs dst src regs' FailedV
  | Jnz_spec_success1 w:
      regs !! src = Some w ->
      nonZero w = false ->
      incrementPC regs = Some regs' ->
      Jnz_spec regs dst src regs' NextIV
  | Jnz_spec_success2 w w':
      regs !! src = Some w ->
      regs !! dst = Some w' ->
      nonZero w = true ->
      <[PC := updatePcPerm w' ]> regs = regs' ->
      Jnz_spec regs dst src regs' NextIV.
  
  Lemma wp_Jnz Ep pc_p pc_g pc_b pc_e pc_a pc_p' w dst src regs :
    cap_lang.decode w = Jnz dst src ->

    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    (∀ (ri: RegName), is_Some (regs !! ri)) →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
          ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Jnz_spec regs dst src regs' retv ⌝ ∗
          pc_a ↦ₐ[pc_p'] w ∗
          [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc HPC Hri φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst; destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    pose proof (regs_lookup_eq _ _ _ HPC) as HPC'.
    iAssert (⌜ r = regs ⌝)%I with "[Hr Hmap]" as %->.
    { iApply (gen_heap_valid_allSepM with "[Hr]"); eauto. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %Hpc_a; auto.
    (*option_locate_mr m r.*) iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    destruct (Hri src) as [wsrc Hsrc].
    destruct (Hri dst) as [wdst Hdst].
    destruct (nonZero wsrc) eqn:Hnz; cbn in Hstep; rewrite /RegLocate Hsrc Hdst Hnz in Hstep.
    { inv Hstep. simpl.
      iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame.
      iPureIntro. econstructor 3; eauto. }
    destruct (incrementPC regs) eqn:HX; cycle 1.
    { rewrite (incrementPC_fail_updatePC _ _ HX) in Hstep.
      inv Hstep. iFrame. iApply "Hφ". iFrame.
      iPureIntro; econstructor; eauto. }
    destruct (incrementPC_success_updatePC _ m _ HX)
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    rewrite HuPC in Hstep. inv Hstep.
    simpl. iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iApply "Hφ". iFrame.
    iPureIntro. econstructor 2; eauto.
  Qed.

  Lemma wp_jnz_success_jmp E r1 r2 pc_p pc_g pc_b pc_e pc_a w w1 w2 pc_p' :
    cap_lang.decode w = Jnz r1 r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    w2 ≠ inl 0%Z →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ w1
          ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w1
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ w1
             ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
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

  Lemma wp_jnz_success_jmp2 E r2 pc_p pc_g pc_b pc_e pc_a w w2 pc_p' :
    cap_lang.decode w = Jnz r2 r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    w2 ≠ inl 0%Z →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w2
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _), (<[PC :=updatePcPerm w2]> r, m),[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Jnz r2 r2)
                             (cap_lang.NextI,_)); eauto; simpl; try congruence.
      rewrite Hr2 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
      destruct w2; auto.
      assert (Zneq_bool z 0 = true); [destruct z; try contradiction; done|]. 
        by rewrite H1. 
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
      rewrite Hr2 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
      destruct w2;
        [assert (Zneq_bool z 0 = true); [destruct z; try contradiction; done|];
         rewrite H2 /=|];
        (inv_head_step;
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hφ" with "[HPC Hr2 Hpc_a]"); iFrame;
           by iModIntro). 
  Qed.

  Lemma wp_jnz_success_jmpPC E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Jnz PC PC →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    
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
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _), (<[PC:=updatePcPerm (inr (pc_p, pc_g, pc_b, pc_e, pc_a))]> r, m),[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Jnz PC PC)
                             (cap_lang.NextI,_)); eauto; simpl; try congruence.
      rewrite HPC /= /updatePcPerm /update_reg /updatePC /=. auto.
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
      rewrite HPC /updatePcPerm /update_reg /updatePC HPC /=.
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
      iSpecialize ("Hφ" with "[HPC Hpc_a]"); iFrame. auto.
  Qed.
  
  Lemma wp_jnz_success_jmpPC1 E r2 pc_p pc_g pc_b pc_e pc_a w w2 pc_p' :
    cap_lang.decode w = Jnz PC r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    w2 ≠ inl 0%Z →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _), (<[PC:=updatePcPerm (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))]> r, m),[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Jnz PC r2)
                             (cap_lang.NextI,_)); eauto; simpl; try congruence.
      rewrite Hr2 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
      destruct w2; auto.
      assert (Zneq_bool z 0 = true); [destruct z; try contradiction; done|]. 
        by rewrite H1. 
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
      rewrite Hr2 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
      destruct w2;
        [assert (Zneq_bool z 0 = true); [destruct z; try contradiction; done|];
         rewrite H2 /=|];
        (inv_head_step;
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hφ" with "[HPC Hr2 Hpc_a]"); iFrame;
           by iModIntro). 
  Qed.

  Lemma wp_jnz_success_jmpPC2 E r1 pc_p pc_g pc_b pc_e pc_a w w1 pc_p' :
    cap_lang.decode w = Jnz r1 PC →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w1
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _), (<[PC:=updatePcPerm w1]> r, m),[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Jnz r1 PC)
                             (cap_lang.NextI,_)); eauto; simpl; try congruence.
      rewrite Hr1 /updatePcPerm /update_reg /updatePC HPC /= /nonZero. auto.
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
      rewrite Hr1 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
      iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
      iSpecialize ("Hφ" with "[HPC Hr1 Hpc_a]"); iFrame. auto.
  Qed.
  
  Lemma wp_jnz_success_next E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_a' w pc_p' :
    cap_lang.decode w = Jnz r1 r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r2 ↦ᵣ inl 0%Z }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ inl 0%Z }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
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

  Lemma wp_jnz_fail_next E r1 r2 pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Jnz r1 r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r2 ↦ᵣ inl 0%Z }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ inl 0%Z }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _), (r, m),[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Jnz r1 r2)
                              (_,_)); eauto; simpl; try congruence.
      rewrite Hr2 /updatePcPerm /update_reg /updatePC HPC /= /nonZero.
        by rewrite Hpc_a' /update_reg /=. 
    - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
      iModIntro. iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep HPC.
      rewrite Hr2 /updatePC HPC Hpc_a' /=. 
      iSpecialize ("Hφ" with "[HPC Hr2 Hpc_a]"); iFrame.
        by iModIntro.
  Qed.

End cap_lang_rules.