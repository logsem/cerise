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

  Inductive Lea_failure (regs: Reg) (r1: RegName) (rv: Z + RegName) :=
  | Lea_fail_rv_nonconst :
     z_of_argument regs rv = None ->
     Lea_failure regs r1 rv
  | Lea_fail_p_E : forall p g b e a,
     regs !! r1 = Some (inr ((p, g), b, e, a)) ->
     p = E ->
     Lea_failure regs r1 rv
  | Lea_fail_r1_noncap : forall n,
     regs !! r1 = Some (inl n) ->
     Lea_failure regs r1 rv
  | Lea_fail_overflow : forall p g b e a z,
     regs !! r1 = Some (inr ((p, g), b, e, a)) ->
     z_of_argument regs rv = Some z ->
     (a + z)%a = None ->
     Lea_failure regs r1 rv
  | Lea_fail_overflow_PC : forall p g b e a z a',
     regs !! r1 = Some (inr ((p, g), b, e, a)) ->
     z_of_argument regs rv = Some z ->
     (a + z)%a = Some a' ->
     incrementPC (<[ r1 := inr ((p, g), b, e, a') ]> regs) = None ->
     Lea_failure regs r1 rv
   .

  Inductive Lea_spec
    (regs: Reg) (r1: RegName) (rv: Z + RegName)
    (regs': Reg) (retv: cap_lang.val) : Prop
  :=
  | Lea_spec_success : forall p g b e a z a',
    retv = NextIV ->
    regs !! r1 = Some (inr ((p, g), b, e, a)) ->
    p ≠ E ->
    z_of_argument regs rv = Some z ->
    (a + z)%a = Some a' ->
    incrementPC
      (<[ r1 := inr ((p, g), b, e, a') ]> regs) = Some regs' ->
    Lea_spec regs r1 rv regs' retv

  | Lea_spec_failure :
    retv = FailedV ->
    Lea_failure regs r1 rv ->
    Lea_spec regs r1 rv regs' retv.

   (* Used to close the failing cases.
      - Hcont is the (iris) name of the closing hypothesis (usually "Hφ")
      - lea_fail_case is one constructor of the Lea_failure inductive,
        indicating the appropriate error case
   *)
   Local Ltac iFail Hcont lea_fail_case :=
     by (
       cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
       eapply Lea_spec_failure; eauto;
       eapply lea_fail_case; eauto
     ).

   Lemma wp_lea Ep pc_p pc_g pc_b pc_e pc_a pc_p' r1 w arg regs :
     cap_lang.decode w = Lea r1 arg →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
     regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
     (∀ (ri: RegName), is_Some (regs !! ri)) →
     {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
         ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
       Instr Executable @ Ep
     {{{ regs' retv, RET retv;
         ⌜ Lea_spec regs r1 arg regs' retv ⌝ ∗
         pc_a ↦ₐ[pc_p'] w ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc HPC Hri φ) "(>Hpc_a & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     pose proof (regs_lookup_eq _ _ _ HPC) as HPC'.
     iAssert (⌜ r = regs ⌝)%I with "[Hr Hmap]" as %->.
     { iApply (gen_heap_valid_allSepM with "[Hr]"); eauto. }
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %Hpc_a; auto.
     (*option_locate_mr m r.*) iModIntro.
     iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

     destruct (Hri r1) as [r1v Hr1].
     pose proof (regs_lookup_eq _ _ _ Hr1) as Hr1'.
     cbn in Hstep. rewrite Hr1' in Hstep.
     destruct r1v as [| (([[p g] b] & e) & a) ] eqn:Hr1v.
     { (* Failure: r1 is not a capability *)
       assert (c = Failed ∧ σ2 = (regs, m)) as (-> & ->)
         by (destruct arg; inversion Hstep; auto).
       iFail "Hφ" Lea_fail_r1_noncap. }

     destruct (perm_eq_dec p E); [ subst p |].
     { (* Failure: r1.p is Enter *)
       assert (c = Failed ∧ σ2 = (regs, m)) as (-> & ->).
       { destruct arg; inversion Hstep; subst; eauto. }
       iFail "Hφ" Lea_fail_p_E. }

     destruct (z_of_argument regs arg) as [ argz |] eqn:Harg;
       pose proof Harg as Harg'; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Harg. destruct arg as [| r0]; [ congruence |].
       destruct (Hri r0) as [r0v Hr0]. rewrite /RegLocate Hr0 in Harg Hstep.
       destruct r0v; [ congruence |].
       assert (c = Failed ∧ σ2 = (regs, m)) as (-> & ->)
         by (destruct p; inversion Hstep; eauto).
       iFail "Hφ" Lea_fail_rv_nonconst. }

     destruct (a + argz)%a as [ a' |] eqn:Hoffset; cycle 1.
     { (* Failure: offset is too large *)
       unfold z_of_argument in Harg. destruct arg as [ z | r0].
       { inversion Harg; subst z. rewrite Hoffset in Hstep.
         assert (c = Failed ∧ σ2 = (regs, m)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
         iFail "Hφ" Lea_fail_overflow. }
       { destruct (Hri r0) as [r0v Hr0]. rewrite /RegLocate Hr0 in Harg Hstep.
         destruct r0v; [| congruence]. inversion Harg; subst z.
         rewrite Hoffset in Hstep.
         assert (c = Failed ∧ σ2 = (regs, m)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
         iFail "Hφ" Lea_fail_overflow. } }

     destruct (incrementPC (<[ r1 := inr ((p, g), b, e, a') ]> regs)) as [ regs' |] eqn:Hregs';
       pose proof Hregs' as Hregs'2; cycle 1.
     { (* Failure: incrementing PC overflows *)
       unfold z_of_argument in Harg.
       assert (exists regs',
         c = Failed ∧ σ2 = (regs', m) ∧
         (regs' = regs ∨ regs' = (<[ r1 := inr ((p, g), b, e, a') ]> regs)))
         as (regs' & -> & -> & Hregs'_cases).
       { destruct arg as [ z | r0 ].
         { inversion Harg; subst z. rewrite Hoffset in Hstep.
           rewrite incrementPC_fail_updatePC //= in Hstep.
           destruct p; inversion Hstep; subst; eauto. }
         { destruct (Hri r0) as [r0v Hr0]. rewrite /RegLocate Hr0 in Harg Hstep.
           destruct r0v; [| congruence]. inversion Harg; subst z. rewrite Hoffset in Hstep.
           rewrite incrementPC_fail_updatePC //= in Hstep.
           destruct p; inversion Hstep; subst; eauto. } }
       iAssert (|==> gen_heap_ctx regs' ∗ ([∗ map] k↦y ∈ regs', k ↦ᵣ y))%I
         with "[Hr Hmap]" as "HrHmap".
       { destruct Hregs'_cases; subst regs'; [ by iFrame |].
         iMod (@gen_heap_update_inSepM with "Hr Hmap") as "[Hr Hmap]"; eauto.
         by iFrame. }
       iMod "HrHmap". iModIntro. cbn. iDestruct "HrHmap" as "[? ?]".
       iFail "Hφ" Lea_fail_overflow_PC. }

     (* Success *)

     assert ((c, σ2) = updatePC (update_reg (regs, m) r1 (inr (p, g, b, e, a')))) as HH.
     { unfold z_of_argument in Harg. destruct arg as [ z | r0 ].
       { inversion Harg; subst z. rewrite Hoffset in Hstep. by destruct p. }
       { destruct (Hri r0) as [r0v Hr0]. rewrite /RegLocate Hr0 in Harg Hstep.
         destruct r0v; [| congruence]. inversion Harg; subst z.
         rewrite Hoffset in Hstep. by destruct p. } }

     clear Hstep. rewrite /update_reg /= in HH.
     eapply (incrementPC_success_updatePC _ m) in Hregs'
       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
     rewrite HuPC in HH; clear HuPC; inversion HH; clear HH; subst c σ2. cbn.
     iFrame.
     iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
     eapply Lea_spec_success; eauto.

     Unshelve. all: assumption.
   Qed.

   Lemma wp_lea_success_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv z a' pc_p' :
     cap_lang.decode w = Lea PC (inr rv) →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     r1 ≠ PC → pc_p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ rv ↦ᵣ inl z }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Ha' Hne1 Hnep ϕ) "(>HPC & >Hpc_a & >Hrv) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto.
     iDestruct (@gen_heap_valid with "Hr Hrv") as %?.
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_reg (r,m) PC (inr (pc_p, pc_g, pc_b, pc_e, a')))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Lea PC (inr rv))
                              (NextI,_)); eauto; simpl; try congruence.
       rewrite Hrv HPC.
       destruct pc_p; try contradiction;
         by rewrite Ha' /updatePC /update_reg /= /RegLocate lookup_insert Hpca'.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hrv /= Ha'.
       destruct pc_p; try contradiction;
         rewrite /updatePC /update_reg /RegLocate lookup_insert Hpca' /= insert_insert;
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hϕ" with "[HPC Hrv Hpc_a]"); iFrame; eauto.
   Qed.

   Lemma wp_lea_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv p g b e a z a' pc_p' :
     cap_lang.decode w = Lea r1 (inr rv) →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ PC → p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ rv ↦ᵣ inl z
              ∗ r1 ↦ᵣ inr ((p,g),b,e,a') }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Ha' Hne1 Hnep ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hϕ".
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

   Lemma wp_lea_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w z a' pc_p' :
     cap_lang.decode w = Lea PC (inl z) →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     pc_p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ[pc_p'] w }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a) Hϕ".
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
       iExists [], (Instr _),(updatePC (update_reg (r,m) PC (inr (pc_p, pc_g, pc_b, pc_e,a')))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Lea PC (inl z))
                              (NextI,_)); eauto; simpl; try congruence.
       rewrite HPC.
       destruct pc_p; try contradiction;
         by rewrite Ha' /updatePC /update_reg /= /RegLocate lookup_insert Hpca' /=.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC /= Ha'.
       destruct pc_p; try contradiction;
         rewrite /updatePC /update_reg /RegLocate lookup_insert Hpca' /= insert_insert;
         iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
         iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame; eauto.
   Qed.

   Lemma wp_lea_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 p g b e a z a' pc_p' :
     cap_lang.decode w = Lea r1 (inl z) →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ PC → p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r1 ↦ᵣ inr ((p,g),b,e,a') }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Ha' Hne1 Hnep ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;auto.
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

   Lemma wp_lea_failPC1 Ep pc_p pc_g pc_b pc_e pc_a w n pc_p' :
     cap_lang.decode w = Lea PC (inl n) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     (pc_p = E \/ (pc_a + n)%a = None) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc HpHa;
       (iIntros (φ) "(HPC & Hpc_a) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;[auto|];
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r,m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea PC (inl n))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite HPC. destruct (perm_eq_dec pc_p E).
       + subst pc_p; auto.
       + destruct HpHa as [Hp | Ha]; try congruence.
         rewrite Ha. destruct pc_p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC. assert (X:match pc_p with
                              | E => (Failed, (r, m))
                              | _ =>
                                match (pc_a + n)%a with
                                | Some a' =>
                                  updatePC (update_reg (r, m) PC (inr (pc_p, pc_g, pc_b, pc_e, a')))
                                | None => (Failed, (r, m))
                                end
                              end = (Failed, (r, m))).
       { destruct (perm_eq_dec pc_p E).
         - subst pc_p; auto.
         - destruct HpHa as [Hp | Ha]; try congruence.
           rewrite Ha. destruct pc_p; auto. }
       repeat rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_lea_failPCreg1 Ep pc_p pc_g pc_b pc_e pc_a w n r1 pc_p' :
     cap_lang.decode w = Lea PC (inr r1) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     (pc_p = E \/ (pc_a + n)%a = None) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r1 ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc HpHa;
     (iIntros (φ) "(HPC & Hpc_a & Hr1) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hr1") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea PC (inr r1))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite HPC. destruct (perm_eq_dec pc_p E).
       + subst pc_p; auto.
       + destruct HpHa as [Hp | Ha]; try congruence.
         rewrite Hr1 Ha. destruct pc_p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hr1. assert (X:match pc_p with
                              | E => (Failed, (r, m))
                              | _ =>
                                match (pc_a + n)%a with
                                | Some a' =>
                                  updatePC (update_reg (r, m) PC (inr (pc_p, pc_g, pc_b, pc_e, a')))
                                | None => (Failed, (r, m))
                                end
                              end = (Failed, (r, m))).
       { destruct (perm_eq_dec pc_p E).
         - subst pc_p; auto.
         - destruct HpHa as [Hp | Ha]; try congruence.
           rewrite Ha. destruct pc_p; auto. }
       repeat rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_lea_failPC1' Ep pc_p pc_g pc_b pc_e pc_a w n a' pc_p' :
     cap_lang.decode w = Lea PC (inl n) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     pc_p <> E ->
     (pc_a + n)%a = Some a' ->
     (a' + 1)%a = None ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hp Ha Ha';
     (iIntros (φ) "(HPC & Hpc_a) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit. (*
c     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea PC (inl n))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite HPC. destruct (perm_eq_dec pc_p E); try congruence.
       rewrite Ha /updatePC /= /RegLocate lookup_insert Ha'.
       assert (match pc_p with | E => (Failed, (r, m)) | _ => (Failed, update_reg (r, m) PC (inr (pc_p, pc_g, pc_b, pc_e, a'))) end = (Failed, match pc_p with | E => (r, m) | _ => update_reg (r, m) PC (inr (pc_p, pc_g, pc_b, pc_e, a')) end)) by (destruct pc_p; auto). rewrite H1. f_equal; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iMod (@gen_heap_update with "Hr HPC") as "[Hr HPC]".
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_a.
       rewrite HPC Ha /updatePC /= /RegLocate lookup_insert Ha'.
       assert (match pc_p with | E => (Failed, (r, m)) | _ => (Failed, update_reg (r, m) PC (inr (pc_p, pc_g, pc_b, pc_e, a'))) end = (Failed, match pc_p with | E => (r, m) | _ => update_reg (r, m) PC (inr (pc_p, pc_g, pc_b, pc_e, a')) end)) by (destruct pc_p; auto). repeat rewrite H2. simpl.
       iFrame. iNext. iModIntro.
       iSplitR; auto. destruct pc_p; simpl; iFrame; try iApply "Hφ"; auto.
       congruence. *)
   Admitted.

   Lemma wp_lea_failPCreg1' Ep pc_p pc_g pc_b pc_e pc_a w n a' r1 pc_p' :
     cap_lang.decode w = Lea PC (inr r1) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     pc_p <> E ->
     (pc_a + n)%a = Some a' ->
     (a' + 1)%a = None ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r1 ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hp Ha Ha';
     (iIntros (φ) "(HPC & Hpc_a & Hr1) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hr1") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea PC (inr r1))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite HPC Hr1.
       rewrite Ha /updatePC /= /RegLocate lookup_insert Ha'.
       destruct pc_p; eauto. congruence.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iMod (@gen_heap_update with "Hr HPC") as "[Hr HPC]".
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_a.
       rewrite HPC Hr1 Ha /updatePC /= /RegLocate lookup_insert Ha'.
       assert (match pc_p with | E => (Failed, (r, m)) | _ => (Failed, update_reg (r, m) PC (inr (pc_p, pc_g, pc_b, pc_e, a'))) end = (Failed, match pc_p with | E => (r, m) | _ => update_reg (r, m) PC (inr (pc_p, pc_g, pc_b, pc_e, a')) end)) by (destruct pc_p; auto). repeat rewrite H2. simpl.
       iFrame. iNext. iModIntro.
       iSplitR; auto. destruct pc_p; simpl; iFrame; try iApply "Hφ"; auto.
       congruence.
   Qed.

   Lemma wp_lea_fail1 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a n pc_p' :
     cap_lang.decode w = Lea dst (inl n) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     (p = E \/ (a + n)%a = None) ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc HpHa;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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

   Lemma wp_lea_fail1' Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a n a' pc_p' :
     cap_lang.decode w = Lea dst (inl n) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     p <> E ->
     (a + n)%a = Some a' ->
     (pc_a + 1)%a = None ->
     dst <> PC ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hp Ha Ha' Hnepc;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst (inl n))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. destruct (perm_eq_dec p E); try congruence.
       rewrite Ha /updatePC /= /RegLocate lookup_insert_ne; auto.
       rewrite /RegLocate in HPC. rewrite HPC Ha'.
       destruct p; eauto. congruence.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst Ha /updatePC /= /RegLocate lookup_insert_ne; auto.
       rewrite /RegLocate in HPC. rewrite HPC Ha'.
       iNext. iModIntro. iSplitR; auto.
       destruct p; simpl; iFrame; try congruence; by iApply "Hφ".
   Qed.

   Lemma wp_lea_fail2 E dst src pc_p pc_g pc_b pc_e pc_a w n pc_p' :
     cap_lang.decode w = Lea dst src →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

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
     assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?;
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; [auto|];
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

   Lemma wp_lea_fail3 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg pc_p' :
     cap_lang.decode w = Lea dst (inr rg) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     p = E →

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hp;
     (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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

   Lemma wp_lea_fail4 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg n pc_p' :
     cap_lang.decode w = Lea dst (inr rg) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     p <> E ->
     (a + n)%a = None ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ rg ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hp Ha;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
      { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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

   Lemma wp_lea_fail4' Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg n a' pc_p' :
     cap_lang.decode w = Lea dst (inr rg) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     p <> E ->
     (a + n)%a = Some a' ->
     (pc_a + 1)%a = None ->
     dst <> PC ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ rg ↦ᵣ inl n }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hp Ha Ha' Hne;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
      { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst (inr rg))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite Hdst. rewrite Hrg. rewrite Ha /updatePC /= /RegLocate lookup_insert_ne; auto.
       rewrite /RegLocate in HPC. rewrite HPC Ha'.
       destruct p; auto. congruence.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite Hdst. rewrite Hrg. rewrite Ha /updatePC /= /RegLocate lookup_insert_ne; auto.
       rewrite /RegLocate in HPC. rewrite HPC Ha'.
       iNext. iModIntro. iSplitR; auto.
       destruct p; simpl; iFrame; try congruence; by iApply "Hφ".
   Qed.

   Lemma wp_lea_failPC5 Ep pc_p pc_g pc_b pc_e pc_a w rg x pc_p' :
     cap_lang.decode w = Lea PC (inr rg) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

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
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea PC (inr rg))
                              (Failed,_));
         eauto; simpl; try congruence.
       rewrite HPC. rewrite Hrg.
       destruct pc_p; auto.
     - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
       iModIntro.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC. rewrite Hrg.
       assert (X: match pc_p with | O | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct pc_p; auto).
       rewrite X.
       iFrame. iNext. iModIntro.
       iSplitR; auto. by iApply "Hφ".
   Qed.

   Lemma wp_lea_fail5 Ep dst pc_p pc_g pc_b pc_e pc_a w p g b e a rg x pc_p' :
     cap_lang.decode w = Lea dst (inr rg) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
     p <> E ->

     {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ dst ↦ᵣ inr ((p,g),b,e,a)
            ∗ rg ↦ᵣ inr x }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     intros Hinstr Hfl Hvpc Hp;
     (iIntros (φ) "(HPC & Hpc_a & Hdst & Hrg) Hφ";
      iApply wp_lift_atomic_head_step_no_fork; auto;
      iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
      iDestruct "Hσ1" as "[Hr Hm]";
      iDestruct (@gen_heap_valid with "Hr HPC") as %?;
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?;
      iDestruct (@gen_heap_valid with "Hr Hrg") as %?;
      iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
      option_locate_mr m r).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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

   Lemma wp_lea_fail6 Ep dst pc_p pc_g pc_b pc_e pc_a w pc_p' :
     cap_lang.decode w = Lea dst (inr PC) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

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
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), (r, m), [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst (inr PC))
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

   Lemma wp_lea_fail7 Ep dst pc_p pc_g pc_b pc_e pc_a w x pc_p' :
     cap_lang.decode w = Lea dst (inr dst) →

     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

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
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; subst;
      destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [],(Instr Failed), _, [].
       iPureIntro.
       constructor.
       eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lea dst (inr dst))
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
