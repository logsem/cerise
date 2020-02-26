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

  Inductive IsPtr_spec (regs: Reg) (dst src: RegName) (regs': Reg): cap_lang.val -> Prop :=
  | IsPtr_spec_success:
      incrementPC (<[ dst := match regs !! src with Some (inr _) => inl 1%Z | _ => inl 0%Z end]> regs) = Some regs' ->
      IsPtr_spec regs dst src regs' NextIV
  | IsPtr_spec_failure:
      IsPtr_spec regs dst src regs' FailedV.
  
  Lemma wp_IsPtr Ep pc_p pc_g pc_b pc_e pc_a pc_p' w dst src regs :
    cap_lang.decode w = IsPtr dst src ->

    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    (∀ (ri: RegName), is_Some (regs !! ri)) →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
          ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ IsPtr_spec regs dst src regs' retv ⌝ ∗
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
    destruct (incrementPC (<[ dst := match wsrc with inl _ => inl 0%Z | inr _ => inl 1%Z end ]> regs)) as [regs'|] eqn:Hregs'; cycle 1.
    { assert (c = Failed /\ σ2 = ((<[ dst := match wsrc with inl _ => inl 0%Z | inr _ => inl 1%Z end ]> regs), m)) as (-> & ->).
      { cbn in Hstep. rewrite /RegLocate Hsrc in Hstep.
        destruct wsrc; rewrite (incrementPC_fail_updatePC _ _ Hregs') in Hstep; inv Hstep; auto. }
      iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ"; iFrame.
      iPureIntro. econstructor 2. }

    cbn in Hstep. rewrite /RegLocate Hsrc in Hstep.
    assert ((c, σ2) = updatePC (update_reg (regs, m) dst (match wsrc with inl _ => inl 0%Z | inr _ => inl 1%Z end))) as HH.
    { destruct wsrc; auto. }

    eapply (incrementPC_success_updatePC _ m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    rewrite HuPC in HH; clear HuPC; inversion HH; clear HH; subst c σ2. cbn.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
    econstructor 1; eauto.
    by rewrite Hsrc /incrementPC HPC'' Ha_pc'.
  Qed.

   Lemma wp_IsPtr_successPC E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w' pc_p' :
     cap_lang.decode w = IsPtr dst PC →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     dst ≠ PC →

       {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↦ₐ[pc_p'] w
             ∗ ▷ dst ↦ᵣ w'
       }}}
         Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ dst ↦ᵣ inl 1%Z }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hdst) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
     iDestruct (@gen_heap_valid with "Hr0 Hdst") as %?.
     option_locate_mr m r0.
     assert (HPC: r !r! PC = inr (pc_p, pc_g, pc_b, pc_e, pc_a)) by (unfold RegLocate; rewrite H2; auto).
     assert (<[dst:=inl 1%Z]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a))) as Hpc_new1.
     { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a')]> (<[dst:=inl 1%Z]> r), m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (IsPtr dst PC)
                              (NextI,_)); eauto; simpl; try congruence.
       by rewrite HPC /update_reg /updatePC /= Hpc_new1 Hpca' /update_reg /updatePC /=.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
       rewrite HPC /updatePC /update_reg /= Hpc_new1 Hpca' /=.
       iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
       iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a]"); iFrame.
       iModIntro. done.
   Qed.

   Lemma wp_IsPtr_success E pc_p pc_g pc_b pc_e pc_a pc_a' w dst r wr w' pc_p' :
     cap_lang.decode w = IsPtr dst r →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     dst ≠ PC →

       {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↦ₐ[pc_p'] w
             ∗ if reg_eq_dec r dst then ▷ r ↦ᵣ wr else ▷ r ↦ᵣ wr ∗ ▷ dst ↦ᵣ w'
       }}}
         Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ if reg_eq_dec r dst then r ↦ᵣ inl (match wr with inr _ => 1%Z | inl _ => 0%Z end) else r ↦ᵣ wr ∗ dst ↦ᵣ inl (match wr with inr _ => 1%Z | inl _ => 0%Z end) }}}.
   Proof.
     destruct (reg_eq_dec r dst). 
     { subst dst.
       iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr) Hϕ".
       iApply wp_lift_atomic_head_step_no_fork; auto.
       iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
       iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
       iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
       iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
       option_locate_mr m r0.
       assert (<[r:=inl (match wr with inr _ => 1%Z | inl _ => 0%Z end)]> r0 !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a))) as Hpc_new1.
       { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
       iApply fupd_frame_l.
       iSplit.
       - rewrite /reducible.
         iExists [], (Instr _),(<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a')]> (<[r:=inl (match wr with inr _ => 1%Z | inl _ => 0%Z end)]> r0), m), [].
         iPureIntro.
         constructor.
         apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a
                                (IsPtr r r)
                                (NextI,_)); eauto; simpl; try congruence.
         destruct wr; by rewrite Hr /update_reg /updatePC /= Hpc_new1 Hpca' /update_reg /updatePC /=.
       - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
         iModIntro. iNext.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep Hpc_new1.
         destruct wr; rewrite Hr /updatePC /update_reg /= Hpc_new1 Hpca' /=.
         iMod (@gen_heap_update with "Hr0 Hr") as "[Hr0 Hdst]".
         iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a]"); iFrame.
         iModIntro. done.
         iMod (@gen_heap_update with "Hr0 Hr") as "[Hr0 Hdst]".
         iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a]"); iFrame.
         iModIntro. done. }
     { clear n.
       iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr & >Hdst) Hϕ".
       iApply wp_lift_atomic_head_step_no_fork; auto.
       iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
       iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
       iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
       iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
       iDestruct (@gen_heap_valid with "Hr0 Hdst") as %?.
       option_locate_mr m r0.
       assert (<[dst:=inl (match wr with inr _ => 1%Z | inl _ => 0%Z end)]> r0 !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a))) as Hpc_new1.
       { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
       iApply fupd_frame_l.
       iSplit.
       - rewrite /reducible.
         iExists [], (Instr _),(<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a')]> (<[dst:=inl (match wr with inr _ => 1%Z | inl _ => 0%Z end)]> r0), m), [].
         iPureIntro.
         constructor.
         apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a
                                (IsPtr dst r)
                                (NextI,_)); eauto; simpl; try congruence.
         destruct wr; by rewrite Hr /update_reg /updatePC /= Hpc_new1 Hpca' /update_reg /updatePC /=.
       - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
         iModIntro. iNext.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep Hpc_new1.
         destruct wr; rewrite Hr /updatePC /update_reg /= Hpc_new1 Hpca' /=.
         iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
         iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a Hr]"); iFrame.
         iModIntro. done.
         iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
         iMod (@gen_heap_update with "Hr0 HPC") as "[$ HPC]".
         iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a Hr]"); iFrame.
         iModIntro. done. }
   Qed.

   Lemma wp_IsPtr_fail_PC E pc_p pc_g pc_b pc_e pc_a w src w' pc_p' :
     cap_lang.decode w = IsPtr PC src →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

     {{{ (if reg_eq_dec PC src then
            ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) else
            ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ ▷ src ↦ᵣ w')
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
       }}}
         Instr Executable @ E
       {{{ RET FailedV;
           (if reg_eq_dec PC src then PC ↦ᵣ inl 1%Z else PC ↦ᵣ inl match w' with inl _ => 0%Z | _ => 1%Z end ∗ src ↦ᵣ w') 
           ∗ pc_a ↦ₐ[pc_p'] w }}}.
   Proof.
     destruct (reg_eq_dec PC src).
     - subst src.
       intros Hinstr Hfl Hvpc.
       iIntros (ϕ) "(>HPC & >Hpc_a) Hϕ".
       iApply wp_lift_atomic_head_step_no_fork; auto.
       iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
       iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
       iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
       option_locate_mr m r.
       iApply fupd_frame_l.
       iSplit.
       + rewrite /reducible.
         iExists [], (Instr _), _, [].
         iPureIntro.
         constructor.
         eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                                (IsPtr PC PC)
                                (Failed,_)); eauto; simpl; try (unfold RegLocate; rewrite H2; auto); try congruence.
         rewrite HPC /update_reg /updatePC /= /RegLocate lookup_insert. auto.
       + iModIntro. iNext.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
         rewrite HPC. rewrite /updatePC /update_reg /RegLocate lookup_insert /=.
         iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
         iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame.
         iModIntro. done.
     - rename n into Hn.
       intros Hinstr Hfl Hvpc.
       iIntros (ϕ) "((>HPC & >Hsrc) & >Hpc_a) Hϕ".
       iApply wp_lift_atomic_head_step_no_fork; auto.
       iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
       iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
       iDestruct (@gen_heap_valid with "Hr HPC") as %?.
       iDestruct (@gen_heap_valid with "Hr Hsrc") as %?.
       option_locate_mr m r.
       iApply fupd_frame_l.
       iSplit.
       + rewrite /reducible.
         iExists [], (Instr _), _, [].
         iPureIntro.
         constructor.
         eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                                (IsPtr PC src)
                                (Failed, (<[PC:=inl match w' with inl _ => 0%Z | inr _ => 1%Z end]> r, m))); eauto; simpl; try congruence.
         rewrite Hsrc /update_reg /updatePC /= /RegLocate lookup_insert. destruct w'; auto.
         rewrite lookup_insert; auto.
       + iModIntro. iNext.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
         rewrite Hsrc. rewrite /updatePC /update_reg /RegLocate lookup_insert /=.
         iMod (@gen_heap_update with "Hr HPC") as "[Hr0 HPC]".
         iSpecialize ("Hϕ" with "[HPC Hsrc Hpc_a]"); iFrame.
         iModIntro. rewrite lookup_insert. destruct w'; simpl; iFrame; done.
   Qed.

   Lemma wp_IsPtr_fail E pc_p pc_g pc_b pc_e pc_a w dst r wr w' pc_p' :
     cap_lang.decode w = IsPtr dst r →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = None →
     dst ≠ PC →

       {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↦ₐ[pc_p'] w
             ∗ if reg_eq_dec r dst then ▷ r ↦ᵣ wr else
                 if reg_eq_dec r PC then ▷ dst ↦ᵣ w' else ▷ r ↦ᵣ wr ∗ ▷ dst ↦ᵣ w'
       }}}
         Instr Executable @ E
       {{{ RET FailedV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ if reg_eq_dec r dst then r ↦ᵣ inl (match wr with inr _ => 1%Z | inl _ => 0%Z end) else
               if reg_eq_dec r PC then dst ↦ᵣ inl 1%Z else r ↦ᵣ wr ∗ dst ↦ᵣ inl (match wr with inr _ => 1%Z | inl _ => 0%Z end) }}}.
   Proof.
     destruct (reg_eq_dec r dst). 
     { subst dst.
       iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr) Hϕ".
       iApply wp_lift_atomic_head_step_no_fork; auto.
       iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
       iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
       iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
       iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
       option_locate_mr m r0.
       assert (<[r:=inl (match wr with inr _ => 1%Z | inl _ => 0%Z end)]> r0 !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a))) as Hpc_new1.
       { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
       iApply fupd_frame_l.
       iSplit.
       - rewrite /reducible.
         iExists [], (Instr _), (<[r:=inl (match wr with inr _ => 1%Z | inl _ => 0%Z end)]> r0, m), [].
         iPureIntro.
         constructor.
         apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a
                                (IsPtr r r)
                                (Failed,_)); eauto; simpl; try congruence.
         destruct wr; by rewrite Hr /update_reg /updatePC /= Hpc_new1 Hpca' /update_reg /updatePC /=.
       - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
         iModIntro. iNext.
         iIntros (e1 σ2 efs Hstep).
         inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep Hpc_new1.
         destruct wr; rewrite Hr /updatePC /update_reg /= Hpc_new1 Hpca' /=.
         iMod (@gen_heap_update with "Hr0 Hr") as "[Hr0 Hdst]".
         iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a]"); iFrame.
         iModIntro. done.
         iMod (@gen_heap_update with "Hr0 Hr") as "[Hr0 Hdst]".
         iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a]"); iFrame.
         iModIntro. done. }
     { rename n into Hn. destruct (reg_eq_dec r PC).
       { subst r.
         iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hdst) Hϕ".
         iApply wp_lift_atomic_head_step_no_fork; auto.
         iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
         iDestruct "Hσ1" as "[Hr0 Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
         iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
         iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
         iDestruct (@gen_heap_valid with "Hr0 Hdst") as %?.
         option_locate_mr m r.
         assert (<[dst:=inl 1%Z]> r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a))) as Hpc_new1.
         { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
         iApply fupd_frame_l.
         iSplit.
         - rewrite /reducible.
           iExists [], (Instr _),(<[dst:=inl 1%Z]> r, m), [].
           iPureIntro.
           constructor.
           apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                                  (IsPtr dst PC)
                                  (Failed,_)); eauto; simpl; try congruence.
           by rewrite HPC /update_reg /updatePC /= Hpc_new1 Hpca' /update_reg /updatePC /=.
         - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
           iModIntro. iNext.
           iIntros (e1 σ2 efs Hstep).
           inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
           rewrite HPC /updatePC /update_reg /= Hpc_new1 Hpca' /=.
           iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
           iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a]"); iFrame.
           iModIntro. done. }
       { clear n.
         iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr & >Hdst) Hϕ".
         iApply wp_lift_atomic_head_step_no_fork; auto.
         iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
         iDestruct "Hσ1" as "[Hr0 Hm]". 
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
         iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
         iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
         iDestruct (@gen_heap_valid with "Hr0 Hr") as %?.
         iDestruct (@gen_heap_valid with "Hr0 Hdst") as %?.
         option_locate_mr m r0.
         assert (<[dst:=inl (match wr with inr _ => 1%Z | inl _ => 0%Z end)]> r0 !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a))) as Hpc_new1.
         { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
         iApply fupd_frame_l.
         iSplit.
         - rewrite /reducible.
           iExists [], (Instr _),(<[dst:=inl (match wr with inr _ => 1%Z | inl _ => 0%Z end)]> r0, m), [].
           iPureIntro.
           constructor.
           apply (step_exec_instr (r0,m) pc_p pc_g pc_b pc_e pc_a
                                  (IsPtr dst r)
                                  (Failed,_)); eauto; simpl; try congruence.
           destruct wr; by rewrite Hr /update_reg /updatePC /= Hpc_new1 Hpca' /update_reg /updatePC /=.
         - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
           iModIntro. iNext.
           iIntros (e1 σ2 efs Hstep).
           inv_head_step_advanced m r0 HPC Hpc_a Hinstr Hstep Hpc_new1.
           destruct wr; rewrite Hr /updatePC /update_reg /= Hpc_new1 Hpca' /=.
           iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
           iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a Hr]"); iFrame.
           iModIntro. done.
           iMod (@gen_heap_update with "Hr0 Hdst") as "[Hr0 Hdst]".
           iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a Hr]"); iFrame.
           iModIntro. done. } }
   Qed.

End cap_lang_rules.