From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
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

  (* TODO: Move somewhere *)
  Ltac destruct_cap c :=
    let p := fresh "p" in
    let g := fresh "g" in
    let b := fresh "b" in
    let e := fresh "e" in
    let a := fresh "a" in
    destruct c as ((((p & g) & b) & e) & a).

  Ltac flatten_hyp H :=
    repeat
      match type of H with
      | context [ if ?b then ?X else ?Y ] => destruct b
      | context [ match ?t with
                  | _ => _
                  end ] => destruct t
      end.

  Definition addr_of_argument regs src :=
    match z_of_argument regs src with
    | None => None
    | Some n => z_to_addr n
    end.

  Inductive Subseg_spec (regs: Reg) (dst: RegName) (src1 src2: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Subseg_spec_failure:
      (match regs !! dst with
       | None => False
       | Some (inl _) => regs' = regs
       | Some (inr (p, g, b, e, a)) =>
         if perm_eq_dec p E then
           regs' = regs
         else match addr_of_argument regs src1 with
              | None => regs' = regs
              | Some a1 =>
                match addr_of_argument regs src2 with
                | None => regs' = regs
                | Some a2 => if isWithin a1 a2 b e then
                              match incrementPC (<[ dst := inr (p, g, a1, a2, a) ]> regs) with
                              | Some _ => False
                              | None => regs' = (<[ dst := inr (p, g, a1, a2, a) ]> regs)
                              end
                            else regs' = regs
                end
              end
       end) ->
      Subseg_spec regs dst src1 src2 regs' FailedV
  | Subseg_spec_success p g b e a a1 a2:
      regs !! dst = Some (inr (p, g, b, e, a)) ->
      p <> E ->
      addr_of_argument regs src1 = Some a1 ->
      addr_of_argument regs src2 = Some a2 ->
      isWithin a1 a2 b e = true ->
      incrementPC (<[ dst := inr (p, g, a1, a2, a) ]> regs) = Some regs' ->
      Subseg_spec regs dst src1 src2 regs' NextIV.
  
  Lemma wp_Subseg Ep pc_p pc_g pc_b pc_e pc_a pc_p' w dst src1 src2 regs :
    cap_lang.decode w = Subseg dst src1 src2 ->

    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    (∀ (ri: RegName), is_Some (regs !! ri)) →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
          ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗
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
    
    destruct (Hri dst) as [wdst Hdst].
    destruct wdst as [ndst | c0]; [| destruct_cap c0]; rewrite /= /RegLocate Hdst in Hstep.
    { assert (c = Failed /\ σ2 = (regs, m)) as (-> & ->) by (destruct src1; destruct src2; inv Hstep; auto).
      simpl; iFrame. iApply "Hφ"; iFrame.
      iPureIntro; econstructor 1; rewrite Hdst; auto. }
    destruct (perm_eq_dec p E).
    { subst p. assert (c = Failed /\ σ2 = (regs, m)) as (-> & ->) by (destruct src1; destruct src2; inv Hstep; auto).
      simpl; iFrame. iApply "Hφ"; iFrame.
      iPureIntro; econstructor 1; rewrite Hdst; destruct (perm_eq_dec E E); auto; congruence. }
    destruct (addr_of_argument regs src1) as [a1|] eqn:Ha1; cycle 1.
    { assert (c = Failed /\ σ2 = (regs, m)) as (-> & ->).
      { unfold addr_of_argument in Ha1.
        destruct (z_of_argument regs src1) as [n1|] eqn:Hn1.
        - destruct src1; simpl in *; inv Hn1.
          + rewrite Ha1 in Hstep.
            flatten_hyp Hstep; auto; inv Hstep; auto.
          + flatten_hyp H3; inv H3; rewrite Ha1 in Hstep; flatten_hyp Hstep; inv Hstep; auto.
        - unfold z_of_argument in Hn1.
          destruct src1; try congruence.
          destruct (Hri r) as [wr Hr]. rewrite Hr in Hn1, Hstep.
          destruct wr; try congruence; destruct src2; destruct p; inv Hstep; auto. }
      simpl; iFrame. iApply "Hφ"; iFrame.
      iPureIntro; econstructor 1; rewrite Hdst; destruct (perm_eq_dec p E); try contradiction; rewrite Ha1; auto. }
    destruct (addr_of_argument regs src2) as [a2|] eqn:Ha2; cycle 1.
    { assert (c = Failed /\ σ2 = (regs, m)) as (-> & ->).
      { unfold addr_of_argument in Ha2.
        destruct (z_of_argument regs src2) as [n2|] eqn:Hn2.
        - destruct src2; simpl in *; inv Hn2.
          + rewrite Ha2 in Hstep.
            flatten_hyp Hstep; auto; inv Hstep; auto.
          + flatten_hyp H3; inv H3; rewrite Ha2 in Hstep; flatten_hyp Hstep; inv Hstep; auto.
        - unfold z_of_argument in Hn2.
          destruct src2; try congruence.
          destruct (Hri r) as [wr Hr]. rewrite Hr in Hn2, Hstep.
          destruct wr; try congruence; flatten_hyp Hstep; inv Hstep; auto. }
      simpl; iFrame. iApply "Hφ"; iFrame.
      iPureIntro; econstructor 1; rewrite Hdst; destruct (perm_eq_dec p E); try contradiction; rewrite Ha1; rewrite Ha2; auto. }
    assert ((c, σ2) = if isWithin a1 a2 b e then updatePC (update_reg (regs, m) dst (inr (p, g, a1, a2, a))) else (Failed, (regs, m))) as Hexec.
    { rewrite -Hstep; clear Hstep.
      unfold addr_of_argument in Ha1, Ha2.
      unfold z_of_argument in Ha1, Ha2.
      destruct src1 as [n1|r1]; [rewrite Ha1| destruct (Hri r1) as [wr1 Hr1]; rewrite Hr1 in Ha1 |- *; destruct wr1; try congruence; rewrite Ha1]; (destruct src2 as [n2|r2]; [rewrite Ha2| destruct (Hri r2) as [wr2 Hr2]; rewrite Hr2 in Ha2 |- *; destruct wr2; try congruence; rewrite Ha2]; destruct p; auto; try congruence). }
    clear Hstep.
    destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1.
    { inv Hexec. simpl; iFrame. iApply "Hφ"; iFrame.
      iPureIntro; econstructor 1; rewrite Hdst; destruct (perm_eq_dec p E); try contradiction; rewrite Ha1; rewrite Ha2; rewrite Hiw; auto. }
    destruct (incrementPC (<[ dst := (inr (p, g, a1, a2, a)) ]> regs)) eqn:HX; cycle 1.
    { rewrite (incrementPC_fail_updatePC _ _ HX) in Hexec.
      iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      inv Hexec; simpl; iFrame. iApply "Hφ"; iFrame.
      iPureIntro; econstructor 1; rewrite Hdst; destruct (perm_eq_dec p E); try contradiction; rewrite Ha1; rewrite Ha2; rewrite Hiw; rewrite HX; auto. }
    eapply (incrementPC_success_updatePC _ m) in HX
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    rewrite HuPC in Hexec. inv Hexec.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    simpl; iFrame. iApply "Hφ". iFrame. iPureIntro.
    econstructor; eauto.
    by rewrite /incrementPC HPC'' Ha_pc'.
  Qed.

  Lemma wp_subseg_success E pc_p pc_g pc_b pc_e pc_a w dst r1 r2 p g b e a n1 n2 a1 a2 pc_p' :
    cap_lang.decode w = Subseg dst (inr r1) (inr r2) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ r1 ↦ᵣ inl n1
          ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inl n1
             ∗ r2 ↦ᵣ inl n2
             ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hdstne Hwb ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite Hdst. destruct p; (try congruence;
                                   rewrite Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite Hdst Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a;
      [iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hr1 Hr2 Hpc_a]"); iFrame;
       iModIntro; done|
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hr1 Hr2 Hpc_a]"); iFrame;
       iModIntro; done]).
  Qed.

  Lemma wp_subseg_success_same E pc_p pc_g pc_b pc_e pc_a w dst r1 p g b e a n1 a1 pc_p' :
    cap_lang.decode w = Subseg dst (inr r1) (inr r1) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a1 b e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ r1 ↦ᵣ inl n1 }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inl n1
             ∗ dst ↦ᵣ inr (p, g, a1, a1, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hn1 Hpne Hdstne Hwb ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    assert (<[dst:=inr (p, g, a1, a1, a)]>
            r !r! PC = (inr (pc_p, pc_g, pc_b, pc_e, pc_a)))
      as Hpc_new1.
    { rewrite (locate_ne_reg _ _ _ (inr (pc_p, pc_g, pc_b, pc_e, pc_a))); eauto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),
      (updatePC (update_reg (r,m) dst (inr ((p, g), a1, a1, a)))).2,[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst (inr r1) (inr r1))
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite Hdst. destruct p; (try congruence;
                                   rewrite Hr1 Hn1 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite Hdst Hr1 Hn1 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a;
      [iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hr1 Hpc_a]"); iFrame;
       iModIntro; done|
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hr1 Hpc_a]"); iFrame;
       iModIntro; done]).
  Qed.

  Lemma wp_subseg_success_l E pc_p pc_g pc_b pc_e pc_a w dst r2 p g b e a n1 n2 a1 a2 pc_p' :
    cap_lang.decode w = Subseg dst (inl n1) (inr r2) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ inl n2
             ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hdstne Hwb ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
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
                             (Subseg dst (inl n1) (inr r2))
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite Hdst. destruct p; (try congruence;
                                   rewrite Hr2 Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite Hdst Hr2 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a;
      [iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hr2 Hpc_a]"); iFrame;
       iModIntro; done|
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hr2 Hpc_a]"); iFrame;
       iModIntro; done]).
  Qed.

  Lemma wp_subseg_success_r E pc_p pc_g pc_b pc_e pc_a w dst r1 p g b e a n1 n2 a1 a2 pc_p' :
    cap_lang.decode w = Subseg dst (inr r1) (inl n2) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ r1 ↦ᵣ inl n1 }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inl n1
             ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hdstne Hwb ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
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
                             (Subseg dst (inr r1) (inl n2))
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite Hdst. destruct p; (try congruence;
                                   rewrite Hr1 Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite Hdst Hr1 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a;
      [iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hr1 Hpc_a]"); iFrame;
       auto |
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hr1 Hpc_a]"); iFrame;
       auto]).
  Qed.

  Lemma wp_subseg_success_lr E pc_p pc_g pc_b pc_e pc_a w dst p g b e a n1 n2 a1 a2 pc_p' :
    cap_lang.decode w = Subseg dst (inl n1) (inl n2) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hdstne Hwb ϕ) "(>HPC & >Hpc_a & >Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
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
                             (Subseg dst (inl n1) (inl n2))
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite Hdst. destruct p; (try congruence;
                                   rewrite Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite Hdst Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a;
      [iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
       iSpecialize ("Hϕ" with "[HPC Hdst  Hpc_a]"); iFrame;
       iModIntro; done|
       iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]";
       iSpecialize ("Hϕ" with "[HPC Hdst Hpc_a]"); iFrame;
       iModIntro; done]).
  Qed.

  Lemma wp_subseg_success_pc E pc_p pc_g pc_b pc_e pc_a w r1 r2 n1 n2 a1 a2 pc_p':
    cap_lang.decode w = Subseg PC (inr r1) (inr r2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ inl n1
          ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
          ∗ r2 ↦ᵣ inl n2
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hwb ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite HPC. destruct pc_p; (try congruence;
                                   rewrite Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct pc_p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite HPC Hr1 Hr2 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a; try (rewrite insert_insert);
      (iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
      iSpecialize ("Hϕ" with "[HPC Hr1 Hr2 Hpc_a]"); iFrame;
      iModIntro; done)).
  Qed.

  Lemma wp_subseg_success_pc_same E pc_p pc_g pc_b pc_e pc_a w r1 n1 a1 pc_p':
    cap_lang.decode w = Subseg PC (inr r1) (inr r1) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a1 pc_b pc_e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ inl n1 }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a1,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hn1 Hpne Hwb ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    option_locate_mr m r.
    assert (<[PC:=inr (pc_p, pc_g, a1, a1, pc_a)]>
            r !r! PC = inr (pc_p, pc_g, a1, a1, pc_a))
      as Hpc_new1; first by rewrite /RegLocate lookup_insert.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),
      (updatePC (update_reg (r,m) PC (inr ((pc_p, pc_g), a1, a1, pc_a)))).2,[].
      iPureIntro.
      constructor.
      apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg PC (inr r1) (inr r1))
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite HPC. destruct pc_p; (try congruence;
                                   rewrite Hr1 Hn1 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct pc_p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite HPC Hr1 Hn1 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a; try (rewrite insert_insert);
      (iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame;
      iModIntro; done)).
  Qed.

  Lemma wp_subseg_success_pc_l E pc_p pc_g pc_b pc_e pc_a w r2 n1 n2 a1 a2 pc_p':
    cap_lang.decode w = Subseg PC (inl n1) (inr r2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r2 ↦ᵣ inl n2
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hwb ϕ) "(>HPC & >Hpc_a & >Hr2) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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
                             (Subseg PC (inl n1) (inr r2))
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite HPC. destruct pc_p; (try congruence;
                                   rewrite Hr2 Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct pc_p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite HPC Hr2 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a; try (rewrite insert_insert);
      (iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
      iSpecialize ("Hϕ" with "[HPC Hr2 Hpc_a]"); iFrame;
      iModIntro; done)).
  Qed.

  Lemma wp_subseg_success_pc_r E pc_p pc_g pc_b pc_e pc_a w r1 n1 n2 a1 a2 pc_p':
    cap_lang.decode w = Subseg PC (inr r1) (inl n2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ inl n1 }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hwb ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
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
                             (Subseg PC (inr r1) (inl n2))
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite HPC. destruct pc_p; (try congruence;
                                   rewrite Hr1 Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct pc_p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite HPC Hr1 Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a; try (rewrite insert_insert);
      (iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
      iSpecialize ("Hϕ" with "[HPC Hr1 Hpc_a]"); iFrame;
      iModIntro; done)).
  Qed.

  Lemma wp_subseg_success_pc_lr E pc_p pc_g pc_b pc_e pc_a w n1 n2 a1 a2 pc_p':
    cap_lang.decode w = Subseg PC (inl n1) (inl n2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET (match (pc_a + 1)%a with Some pc_a' => NextIV | None => FailedV end);
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,(match (pc_a + 1)%a with Some pc_a' => pc_a' | None => pc_a end))
          ∗ pc_a ↦ₐ[pc_p'] w
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hwb ϕ) "(>HPC & >Hpc_a) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
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
                             (Subseg PC (inl n1) (inl n2))
                             (match (pc_a + 1)%a with Some _ => cap_lang.NextI | None => Failed end,_)); eauto; simpl; try congruence.
      rewrite HPC. destruct pc_p; (try congruence;
                                   rewrite Hn1 Hn2 Hwb /updatePC /update_reg /= Hpc_new1; destruct (pc_a + 1)%a; simpl; auto).
    - destruct pc_p; try congruence;
      (iModIntro; iNext;
      iIntros (e1 σ2 efs Hstep);
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1;
      rewrite HPC Hn1 Hn2 Hwb /updatePC /update_reg Hpc_new1 /=;
      destruct (pc_a + 1)%a; try (rewrite insert_insert);
      (iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]";
      iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame;
      iModIntro; done)).
  Qed.

  Lemma wp_subseg_fail_dst_E E pc_p pc_g pc_b pc_e pc_a w dst src1 src2 l b e a pc_p' :
    cap_lang.decode w = Subseg dst src1 src2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ dst ↦ᵣ inr (cap_lang.E, l, b, e, a) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & >Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }    
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst src1 src2)
                             (_,_)); eauto; simpl; try congruence.
      rewrite Hdst. flatten; auto.
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      assert (e1 = Instr Failed /\ σ2 = (r,m) /\ efs = []).
      { inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        rewrite Hdst. flatten; auto. }
      destruct H1 as [A [B C]]. subst; simpl.
      iFrame. iSplitR; auto. iApply "Hϕ"; auto.
  Qed.

  Lemma wp_subseg_fail_dst_z E pc_p pc_g pc_b pc_e pc_a w dst src1 src2 ndst pc_p' :
    cap_lang.decode w = Subseg dst src1 src2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ dst ↦ᵣ inl ndst }}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & >Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst src1 src2)
                             (_,_)); eauto; simpl; try congruence.
      rewrite Hdst. destruct src1, src2; auto.
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hdst. destruct src1, src2; simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
  Qed.
  
  Lemma wp_subseg_fail_pc1 E pc_p pc_g pc_b pc_e pc_a w dst src2 pc_p' :
    cap_lang.decode w = Subseg dst (inr PC) src2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Subseg dst (inr PC) src2)
                              (_,_)); eauto; simpl; try congruence.
      rewrite HPC. (instantiate (1 := (r,m))).
      destruct src2; auto; destruct (r !r! dst); auto; destruct c,p,p,p,p; auto.
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite HPC. destruct src2; destruct (r !r! dst); simpl; auto.
      + iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + destruct c,p,p,p,p; simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + destruct c,p,p,p,p; simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
  Qed.

  Lemma wp_subseg_fail_pc2 E pc_p pc_g pc_b pc_e pc_a w dst src1 pc_p' :
    cap_lang.decode w = Subseg dst src1 (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst src1 (inr PC))
                             (_,_)); eauto; simpl; try congruence.
      rewrite HPC. destruct src1; destruct (r !r! dst); auto.
      destruct c,p,p,p,p; auto.
      destruct c,p,p,p,p; destruct (r !r! r0); auto.
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite HPC. destruct src1; destruct (r !r! dst); simpl; auto.
      + iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + destruct c,p,p,p,p; simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + destruct c,p,p,p,p; destruct (r !r! r0); simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
  Qed.

  Lemma wp_subseg_fail_reg1_cap E pc_p pc_g pc_b pc_e pc_a w dst r1 src2 c pc_p' :
    cap_lang.decode w = Subseg dst (inr r1) src2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ inr c }}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & >Hr1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr1") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst (inr r1) src2)
                             (_,_)); eauto; simpl; try congruence.
      rewrite Hr1. (instantiate (1 := (r,m))).
      destruct src2; auto; destruct (r !r! dst); auto; destruct c0,p,p,p,p; auto.
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hr1. destruct src2; destruct (r !r! dst); simpl; auto.
      + iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + destruct c0,p,p,p,p; simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + destruct c0,p,p,p,p; simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
  Qed.

  Lemma wp_subseg_fail_reg2_cap E pc_p pc_g pc_b pc_e pc_a w dst src1 r2 c pc_p' :
    cap_lang.decode w = Subseg dst src1 (inr r2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r2 ↦ᵣ inr c }}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & >Hr2) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr Hr2") as %?.
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst src1 (inr r2))
                             (_,_)); eauto; simpl; try congruence.
      rewrite Hr2. destruct src1; destruct (r !r! dst); auto.
      destruct c0,p,p,p,p; auto.
      destruct c0,p,p,p,p; destruct (r !r! r0); auto.
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
      rewrite Hr2. destruct src1; destruct (r !r! dst); simpl; auto.
      + iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + destruct c0,p,p,p,p; simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + iFrame; iSplitR; auto; iApply "Hϕ"; auto.
      + destruct c0,p,p,p,p; destruct (r !r! r0); simpl; iFrame; iSplitR; auto; iApply "Hϕ"; auto.
  Qed.

  Lemma wp_subseg_fail_convert1 E pc_p pc_g pc_b pc_e pc_a w dst src1 src2 n1 pc_p' :
    cap_lang.decode w = Subseg dst src1 src2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = None ->
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ (match src1 with inr r1 => (r1 ↦ᵣ inl n1) | inl n => ⌜n = n1⌝ end) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hconv ϕ) "(>HPC & >Hpc_a & Hsrc1) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iAssert ((⌜match src1 with inl n0 => n0 = n1 | inr r1 => r !! r1 = Some (inl n1) end⌝)%I) as %?.
    { destruct src1; auto. iApply (@gen_heap_valid with "Hr Hsrc1"). }
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst src1 src2)
                             (Failed,(r,m))); eauto; simpl; try congruence.
      destruct src1.
      + subst z. rewrite Hconv.
        destruct src2, (r !r! dst); auto; destruct c,p,p,p,p; auto; destruct (r !r! r0); auto.
      + option_locate_mr m r. rewrite Hr0 Hconv.
        destruct src2, (r !r! dst); auto; destruct c,p,p,p,p; auto; destruct (r !r! r1); auto.
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      assert (e1 = Instr Failed /\ σ2 = (r,m) /\ efs = []).
      { inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        destruct src1.
        - subst z. rewrite Hconv.
          destruct src2, (r !r! dst); auto; destruct c,p,p,p,p; auto; destruct (r !r! r0); auto.
        - option_locate_mr m r. rewrite Hr0 Hconv.
          destruct src2, (r !r! dst); auto; destruct c,p,p,p,p; auto; destruct (r !r! r1); auto. }
      destruct H1 as [A [B C]]. subst e1; subst σ2; subst efs. simpl.
      iFrame; iSplitR; auto; iApply "Hϕ"; auto.
  Qed.

  Lemma wp_subseg_fail_convert2 E pc_p pc_g pc_b pc_e pc_a w dst src1 src2 n2 pc_p' :
    cap_lang.decode w = Subseg dst src1 src2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n2 = None ->
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ (match src2 with inr r2 => (r2 ↦ᵣ inl n2) | inl n => ⌜n = n2⌝ end) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hconv ϕ) "(>HPC & >Hpc_a & Hsrc2) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iAssert ((⌜match src2 with inl n0 => n0 = n2 | inr r2 => r !! r2 = Some (inl n2) end⌝)%I) as %?.
    { destruct src2; auto. iApply (@gen_heap_valid with "Hr Hsrc2"). }
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst src1 src2)
                             (Failed,(r,m))); eauto; simpl; try congruence.
      destruct src2.
      + subst z. rewrite Hconv. flatten; auto.
      + option_locate_mr m r. rewrite Hr0 Hconv.
        flatten; auto.
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      assert (e1 = Instr Failed /\ σ2 = (r,m) /\ efs = []).
      { inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        destruct src2.
        - subst z. rewrite Hconv. flatten; auto.
        - option_locate_mr m r. rewrite Hr0 Hconv. flatten; auto. }
      destruct H1 as [A [B C]]. subst e1; subst σ2; subst efs. simpl.
      iFrame; iSplitR; auto; iApply "Hϕ"; auto.
  Qed.

  Lemma wp_subseg_fail_notwithin E pc_p pc_g pc_b pc_e pc_a w dst src1 src2 n1 n2 a1 a2 p l b e a pc_p' :
    cap_lang.decode w = Subseg dst src1 src2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ->
    z_to_addr n2 = Some a2 ->
    isWithin a1 a2 b e = false ->
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ (match src1 with inr r1 => (r1 ↦ᵣ inl n1) | inl n => ⌜n = n1⌝ end)
          ∗ (match src2 with inr r2 => match src1 with inr r1 => if reg_eq_dec r1 r2 then ⌜n1 = n2⌝ else (r2 ↦ᵣ inl n2) | _ => (r2 ↦ᵣ inl n2) end | inl n => ⌜n = n2⌝ end)
          ∗ if (reg_eq_dec PC dst) then ⌜pc_b = b /\ pc_e = e⌝ else dst ↦ᵣ inr (p,l,b,e,a)}}}
      Instr Executable @ E
      {{{ RET FailedV;
          True
      }}}.
  Proof.
    Local Opaque reg_eq_dec.
    iIntros (Hinstr Hfl Hvpc Hconv1 Hconv2 Hnw ϕ) "(>HPC & >Hpc_a & Hsrc1 & Hsrc2 & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc; subst;
         destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iAssert (⌜if reg_eq_dec PC dst then pc_b = b ∧ pc_e = e else r !! dst = Some (inr (p, l, b, e, a))⌝)%I as %?.
    { destruct (reg_eq_dec PC dst); auto. iApply (@gen_heap_valid with "Hr Hdst"). }
    iAssert ((⌜match src1 with inl n0 => n0 = n1 | inr r1 => r !! r1 = Some (inl n1) end⌝)%I) as %?.
    { destruct src1; auto. iApply (@gen_heap_valid with "Hr Hsrc1"). }
    iAssert (⌜match src2 with | inl n0 => n0 = n2 | inr r2 => match src1 with | inl _ => r !! r2 = Some (inl n2) | inr r1 => if reg_eq_dec r1 r2 then n1 = n2 else r !! r2 = Some (inl n2) end end⌝)%I as %?.
    { destruct src2; auto. destruct src1; try (iApply (@gen_heap_valid with "Hr Hsrc2")).
      destruct (reg_eq_dec r1 r0); auto; iApply (@gen_heap_valid with "Hr Hsrc2"). }
    option_locate_mr m r.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [], (Instr _),_,[].
      iPureIntro.
      constructor.
      eapply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                             (Subseg dst src1 src2)
                             (Failed,(r,m))); eauto; simpl; try congruence.
      destruct src1.
      + subst z. rewrite Hconv1.
        destruct src2. 
        * subst z. rewrite Hconv2.
          destruct (reg_eq_dec PC dst).
          { subst dst. rewrite HPC. destruct H3; subst b; subst e.
            rewrite Hnw. flatten; auto. }
          { option_locate_mr m r. rewrite Hdst Hnw. flatten; auto. }
        * destruct (reg_eq_dec PC dst).
          { subst dst. rewrite HPC. destruct H3; subst b; subst e.
            option_locate_mr m r. rewrite Hr0 Hconv2 Hnw.
            flatten; auto. }
          { option_locate_mr m r. rewrite Hdst Hr0 Hconv2 Hnw.
            flatten; auto. }
      + option_locate_mr m r. rewrite Hr0 Hconv1.
        destruct src2; option_locate_mr m r; try (subst z); try (rewrite Hr1); try (rewrite Hconv2).
        * destruct (reg_eq_dec PC dst); option_locate_mr m r; try (rewrite Hdst Hnw; flatten; auto).
          destruct H3; subst; rewrite HPC Hnw; flatten; auto.
        * destruct (reg_eq_dec PC dst); option_locate_mr m r; try (rewrite Hdst).
          { destruct H3; subst. rewrite HPC.
            destruct (reg_eq_dec r0 r1); option_locate_mr m r; try (subst; rewrite Hr0 Hconv1); try (rewrite Hr1 Hconv2).
            - assert (a1 = a2) by congruence; subst a2; rewrite Hnw; flatten; auto.
            - rewrite Hnw; flatten; auto. }
          { destruct (reg_eq_dec r0 r1); option_locate_mr m r; subst; try (rewrite Hr0 Hconv1); try (rewrite Hr1 Hconv2).
            - assert (a1 = a2) by congruence; subst a2; rewrite Hnw; flatten; auto.
            - rewrite Hnw; flatten; auto. }
    - iModIntro; iNext.
      iIntros (e1 σ2 efs Hstep).
      assert (e1 = Instr Failed /\ σ2 = (r,m) /\ efs = []).
      { inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1.
        destruct src1.
        + subst z. rewrite Hconv1.
          destruct src2. 
          * subst z. rewrite Hconv2.
            destruct (reg_eq_dec PC dst).
            { subst dst. rewrite HPC. destruct H3; subst b; subst e.
              rewrite Hnw. flatten; auto. }
            { option_locate_mr m r. rewrite Hdst Hnw. flatten; auto. }
          * destruct (reg_eq_dec PC dst).
            { subst dst. rewrite HPC. destruct H3; subst b; subst e.
              option_locate_mr m r. rewrite Hr0 Hconv2 Hnw.
              flatten; auto. }
            { option_locate_mr m r. rewrite Hdst Hr0 Hconv2 Hnw.
              flatten; auto. }
        + option_locate_mr m r. rewrite Hr0 Hconv1.
          destruct src2; option_locate_mr m r; try (subst z); try (rewrite Hr1); try (rewrite Hconv2).
          * destruct (reg_eq_dec PC dst); option_locate_mr m r; try (rewrite Hdst Hnw; flatten; auto).
            destruct H3; subst; rewrite HPC Hnw; flatten; auto.
          * destruct (reg_eq_dec PC dst); option_locate_mr m r; try (rewrite Hdst).
            { destruct H3; subst. rewrite HPC.
              destruct (reg_eq_dec r0 r1); option_locate_mr m r; try (subst; rewrite Hr0 Hconv1); try (rewrite Hr1 Hconv2).
              - assert (a1 = a2) by congruence; subst a2; rewrite Hnw; flatten; auto.
              - rewrite Hnw; flatten; auto. }
            { destruct (reg_eq_dec r0 r1); option_locate_mr m r; subst; try (rewrite Hr0 Hconv1); try (rewrite Hr1 Hconv2).
              - assert (a1 = a2) by congruence; subst a2; rewrite Hnw; flatten; auto.
              - rewrite Hnw; flatten; auto. } }
      destruct H1 as [A [B C]]. subst e1; subst σ2; subst efs. simpl.
      iFrame; iSplitR; auto; iApply "Hϕ"; auto.
  Qed.

End cap_lang_rules.