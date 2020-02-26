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

  (* TODO: move to stdpp *)
  Tactic Notation "destruct_or" ident(H) :=
  match type of H with
  | _ ∨ _ => destruct H as [H|H]
  | Is_true (_ || _) => apply orb_True in H; destruct H as [H|H]
  end.
  Tactic Notation "destruct_or" "?" ident(H) := repeat (destruct_or H).
  Tactic Notation "destruct_or" "!" ident(H) := hnf in H; destruct_or H; destruct_or? H.

  Definition denote (i: instr) (n1 n2: Z): Z :=
    match i with
    | cap_lang.Add _ _ _ => (n1 + n2)%Z
    | Sub _ _ _ => (n1 - n2)%Z
    | Lt _ _ _ => (Z.b2z (n1 <? n2)%Z)
    | _ => 0%Z
    end.

  Definition is_AddSubLt (i: instr) (r: RegName) (arg1 arg2: Z + RegName) :=
    i = cap_lang.Add r arg1 arg2 ∨
    i = Sub r arg1 arg2 ∨
    i = Lt r arg1 arg2.

  Lemma regs_of_is_AddSubLt i r arg1 arg2 :
    is_AddSubLt i r arg1 arg2 →
    regs_of i = {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  (* TODO: move to rules_base *)
  Lemma z_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (z:Z) :
    z_of_argument regs arg = Some z →
    (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (inl z)).
  Proof.
    unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  Qed.

  (* TODO: move to rules_base. *)
  (* TODO: add in the second case of the conclusion the fact that [regs !! r = Some (inl z)]
     (there is an unecessary loss of generality at the moment) *)
  Lemma z_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (z:Z) :
    z_of_argument regs arg = Some z →
    regs ⊆ regs' →
    (arg = inl z ∨ ∃ r, arg = inr r ∧ regs' !! r = Some (inl z)).
  Proof.
    unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
    intros HH. unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
  Qed.

  Inductive AddSubLt_failure (i: instr) (regs: Reg) (dst: RegName) (rv1 rv2: Z + RegName) (regs': Reg) :=
  | AddSubLt_fail_nonconst1:
      z_of_argument regs rv1 = None ->
      AddSubLt_failure i regs dst rv1 rv2 regs'
  | AddSubLt_fail_nonconst2:
      z_of_argument regs rv2 = None ->
      AddSubLt_failure i regs dst rv1 rv2 regs'
  | AddSubLt_fail_incrPC n1 n2:
      z_of_argument regs rv1 = Some n1 ->
      z_of_argument regs rv2 = Some n2 ->
      incrementPC (<[ dst := inl (denote i n1 n2) ]> regs) = None ->
      regs' = (<[ dst := inl (denote i n1 n2) ]> regs) ->
      AddSubLt_failure i regs dst rv1 rv2 regs'.

  Inductive AddSubLt_spec (i: instr) (regs: Reg) (dst: RegName) (rv1 rv2: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | AddSubLt_spec_success n1 n2:
      z_of_argument regs rv1 = Some n1 ->
      z_of_argument regs rv2 = Some n2 ->
      incrementPC (<[ dst := inl (denote i n1 n2) ]> regs) = Some regs' ->
      AddSubLt_spec i regs dst rv1 rv2 regs' NextIV
  | AddSubLt_spec_failure:
      AddSubLt_failure i regs dst rv1 rv2 regs' ->
      AddSubLt_spec i regs dst rv1 rv2 regs' FailedV.

  Local Ltac iFail Hcont get_fail_case :=
    cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
    econstructor; eapply get_fail_case; eauto.

  (* TODO: move elsewhere *)
  Lemma pair_eq_inv {A B} {y u : A} {z t : B} {x} :
      x = (y, z) -> x = (u, t) ->
      y = u ∧ z = t.
  Proof. intros. subst x. inversion H2. auto. Qed.

  Tactic Notation "simplify_eq_pair" :=
    repeat
      lazymatch goal with
      | H1 : ?x = (?y, ?z), H2 : ?x = (?u, ?t) |- _ =>
        assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 H2)); clear H2
      | |- _ => progress simplify_eq
      end.

  Lemma wp_AddSubLt Ep i pc_p pc_g pc_b pc_e pc_a pc_p' w dst arg1 arg2 regs :
    cap_lang.decode w = i →
    is_AddSubLt i dst arg1 arg2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs_of i ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ AddSubLt_spec (cap_lang.decode w) regs dst arg1 arg2 regs' retv ⌝ ∗
          pc_a ↦ₐ[pc_p'] w ∗
          [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hfl Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst; destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have HPC' := regs_lookup_eq _ _ _ HPC.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    erewrite regs_of_is_AddSubLt in Hri, Dregs; eauto.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (z_of_argument regs arg1) as [n1|] eqn:Hn1;
      pose proof Hn1 as Hn1'; cycle 1.
    (* Failure: arg1 is not an integer *)
    { unfold z_of_argument in Hn1. destruct arg1 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hn1. destruct r0v as [| (([[? ?] ?] & ?) & ?) ]; [ congruence |].
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr /= in Hstep.
        all: rewrite /RegLocate Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFail "Hφ" AddSubLt_fail_nonconst1. }

    destruct (z_of_argument regs arg2) as [n2|] eqn:Hn2;
      pose proof Hn2 as Hn2'; cycle 1.
    (* Failure: arg2 is not an integer *)
    { unfold z_of_argument in Hn2. destruct arg2 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hn2. destruct r0v as [| (([[? ?] ?] & ?) & ?) ]; [ congruence |].
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr /= in Hstep.
        all: rewrite /RegLocate Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFail "Hφ" AddSubLt_fail_nonconst2. }

    eapply z_of_argument_Some_inv' in Hn1; eapply z_of_argument_Some_inv' in Hn2; eauto.

    destruct (incrementPC (<[ dst := inl (denote i n1 n2) ]> regs))
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    (* Failure: Cannot increment PC *)
    { apply incrementPC_fail_updatePC with (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.

      assert (c = Failed ∧ σ2 = (<[ dst := inl (denote i n1 n2) ]> r, m)) as (-> & ->).
      { destruct Hn1 as [ -> | (r1 & -> & Hr1) ]; destruct Hn2 as [ -> | (r2 & -> & Hr2) ].
        all: destruct_or! Hinstr; rewrite !Hinstr /= /update_reg /RegLocate in Hstep Hregs' |- *.
        all: rewrite ?Hr1 ?Hr2 /= in Hstep.
        all: by simplify_eq_pair. }
      cbn; iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      rewrite Hdecode. iFail "Hφ" AddSubLt_fail_incrPC. }

    (* Success *)

    assert ((c, σ2) = updatePC (update_reg (r, m) dst (inl (denote i n1 n2)))) as HH.
    { destruct Hn1 as [ -> | (r1 & -> & Hr1) ]; destruct Hn2 as [ -> | (r2 & -> & Hr2) ].
      all: destruct_or! Hinstr; rewrite Hinstr /= /RegLocate /update_reg /= in Hstep |- *; auto.
      all: rewrite ?Hr1 ?Hr2 /= in Hstep; auto. }

    rewrite /update_reg /= in HH.
    eapply (incrementPC_success_updatePC _ m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in HH. simplify_eq.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_add_sub_lt_success_same E dst pc_p pc_g pc_b pc_e pc_a w wdst x n1 pc_p' :
    cap_lang.decode w = cap_lang.Add dst x x \/ cap_lang.decode w = Sub dst x x \/ cap_lang.decode w = Lt dst x x →

    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    
    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ match x with
             | inl m => ⌜m = n1⌝
             | inr r1 => r1 ↦ᵣ inl n1
             end
           ∗ match x with
             | inr r1 => if reg_eq_dec r1 dst then emp else if reg_eq_dec dst PC then emp else dst ↦ᵣ wdst
             | _ => if reg_eq_dec dst PC then emp else dst ↦ᵣ wdst
             end
    }}}
      Instr Executable @ E
      {{{ RET (if reg_eq_dec dst PC then FailedV else match (pc_a + 1)%a with None => FailedV | Some _ => NextIV end);
          (if reg_eq_dec dst PC then emp else PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e, match (pc_a + 1)%a with None => pc_a | Some pc_a' => pc_a' end))
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ match x with
              | inl m => ⌜m = n1⌝
              | inr r1 => if reg_eq_dec r1 dst then emp else r1 ↦ᵣ inl n1
              end
            ∗ dst ↦ᵣ (match cap_lang.decode w with
                      | cap_lang.Add _ _ _ => inl (n1 + n1)%Z
                      | Sub _ _ _ => inl (n1 - n1)%Z
                      | Lt _ _ _ => (inl (Z.b2z (n1 <? n1)%Z))
                      | _ => inl 0%Z
                      end)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(HPC & Hpc_a & Hx & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iAssert (⌜match x with inl m => m = n1 | inr r1 => r !! r1 = Some (inl n1) end⌝)%I with "[Hr Hx]" as %?.
    { destruct x; auto.
      iDestruct (@gen_heap_valid with "Hr Hx") as %?. auto. }
    iAssert (⌜match x with inr r1 => if reg_eq_dec r1 dst then True else if reg_eq_dec dst PC then True else r !! dst = Some wdst | _ => if reg_eq_dec dst PC then True else r !! dst = Some wdst end⌝)%I with "[Hr Hdst]" as %?.
    { destruct x.
      - destruct (reg_eq_dec dst PC); auto.
        iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto.
      - destruct (reg_eq_dec r0 dst); auto.
        destruct (reg_eq_dec dst PC); auto.
        iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (cap_lang.decode w) (exec (cap_lang.decode w) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H5.
      + simpl in H8; unfold RegLocate in H8; rewrite H1 in H8; contradiction.
      + clear H10. unfold RegLocate in H9; rewrite H1 in H9. inv H9.
        unfold MemLocate. rewrite H2.
        destruct Hinstr as [Hinstr | [Hinstr | Hinstr]]; rewrite Hinstr; rewrite /exec /RegLocate.
        * destruct x; simpl.
          { destruct (reg_eq_dec dst PC).
            + subst dst.
              rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
              simpl. subst z.
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame. auto.
            + rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=. subst z.
              destruct (a+1)%a.
              * iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame. auto.
              * iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame. auto. }
          { destruct (reg_eq_dec dst PC).
            + subst dst; rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto.
              destruct (reg_eq_dec r0 PC); auto.
            + rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=.
              destruct (reg_eq_dec r0 dst).
              * subst r0. iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto.
              * iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto. }
        * destruct x; simpl.
          { destruct (reg_eq_dec dst PC).
            + subst dst.
              rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
              simpl. subst z.
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame. auto.
            + rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=. subst z.
              iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
              destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto. }
          { destruct (reg_eq_dec dst PC).
            + subst dst; rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto.
              destruct (reg_eq_dec r0 PC); auto.
            + rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=.
              destruct (reg_eq_dec r0 dst).
              * subst r0. iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto.
              * iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto. }
        * destruct x; simpl.
          { destruct (reg_eq_dec dst PC).
            + subst dst.
              rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
              simpl. subst z.
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame. auto.
            + rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=. subst z.
              iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
              destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto. }
          { destruct (reg_eq_dec dst PC).
            + subst dst; rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
              iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto.
              destruct (reg_eq_dec r0 PC); auto.
            + rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=.
              destruct (reg_eq_dec r0 dst).
              * subst r0. iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto.
              * iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx]"); iFrame; auto. }
  Qed.

  Lemma wp_add_sub_lt_success E dst pc_p pc_g pc_b pc_e pc_a w wdst x y n1 n2 pc_p' :
    cap_lang.decode w = cap_lang.Add dst x y \/ cap_lang.decode w = Sub dst x y \/ cap_lang.decode w = Lt dst x y →

    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    
    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ match x with
             | inl m => ⌜m = n1⌝
             | inr r1 => r1 ↦ᵣ inl n1
             end
           ∗ match y with
             | inl m => ⌜m = n2⌝
             | inr r2 => r2 ↦ᵣ inl n2
             end
           ∗ match x, y with
             | inr r1, inr r2 => if reg_eq_dec r1 dst then emp else if reg_eq_dec r2 dst then emp else if reg_eq_dec dst PC then emp else dst ↦ᵣ wdst
             | inl _, inr r2 => if reg_eq_dec r2 dst then emp else if reg_eq_dec dst PC then emp else dst ↦ᵣ wdst
             | inr r1, inl _ => if reg_eq_dec r1 dst then emp else if reg_eq_dec dst PC then emp else dst ↦ᵣ wdst
             | _, _ => if reg_eq_dec dst PC then emp else dst ↦ᵣ wdst
             end
    }}}
      Instr Executable @ E
      {{{ RET (if reg_eq_dec dst PC then FailedV else match (pc_a+1)%a with | None => FailedV | Some _ => NextIV end);
          (if reg_eq_dec dst PC then emp else PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,match (pc_a+1)%a with None => pc_a | Some pc_a' => pc_a' end))
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ match x with
              | inl m => ⌜m = n1⌝
              | inr r1 => if reg_eq_dec r1 dst then emp else r1 ↦ᵣ inl n1
              end
            ∗ match y with
              | inl m => ⌜m = n2⌝
              | inr r2 => if reg_eq_dec r2 dst then emp else r2 ↦ᵣ inl n2
              end
            ∗ dst ↦ᵣ (match cap_lang.decode w with
                      | cap_lang.Add _ _ _ => inl (n1 + n2)%Z
                      | Sub _ _ _ => inl (n1 - n2)%Z
                      | Lt _ _ _ => (inl (Z.b2z (n1 <? n2)%Z))
                      | _ => inl 0%Z
                      end)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(HPC & Hpc_a & Hx & Hy & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O) as Ho.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
    iAssert (⌜match x with inl m => m = n1 | inr r1 => r !! r1 = Some (inl n1) end⌝)%I with "[Hr Hx]" as %?.
    { destruct x; auto.
      iDestruct (@gen_heap_valid with "Hr Hx") as %?. auto. }
    iAssert (⌜match y with inl m => m = n2 | inr r2 => r !! r2 = Some (inl n2) end⌝)%I with "[Hr Hy]" as %?.
    { destruct y; auto.
      iDestruct (@gen_heap_valid with "Hr Hy") as %?. auto. }
    iAssert (⌜match x, y with inr r1, inr r2 => if reg_eq_dec r1 dst then True else if reg_eq_dec r2 dst then True else if reg_eq_dec dst PC then True else r !! dst = Some wdst | inl _, inr r2 => if reg_eq_dec r2 dst then True else if reg_eq_dec dst PC then True else r !! dst = Some wdst | inr r1, inl _ => if reg_eq_dec r1 dst then True else if reg_eq_dec dst PC then True else r !! dst = Some wdst | _, _ => if reg_eq_dec dst PC then True else r !! dst = Some wdst end⌝)%I with "[Hr Hdst]" as %?.
    { destruct x.
      - destruct y.
        + destruct (reg_eq_dec dst PC); auto.
          iDestruct (@gen_heap_valid with "Hr Hdst") as %?; auto.
        + destruct (reg_eq_dec r0 dst); auto.
          destruct (reg_eq_dec dst PC); auto.
          iDestruct (@gen_heap_valid with "Hr Hdst") as %?; auto.
      - destruct y.
        + destruct (reg_eq_dec r0 dst); auto.
          destruct (reg_eq_dec dst PC); auto.
          iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto.
        + destruct (reg_eq_dec r0 dst); auto.
          destruct (reg_eq_dec r1 dst); auto.
          destruct (reg_eq_dec dst PC); auto.
          iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (cap_lang.decode w) (exec (cap_lang.decode w) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H6.
      + simpl in H9; unfold RegLocate in H9; rewrite H1 in H9; contradiction.
      + clear H11. unfold RegLocate in H10; rewrite H1 in H10. inv H10.
        unfold MemLocate. rewrite H2.
        destruct Hinstr as [Hinstr | [Hinstr | Hinstr]]; rewrite Hinstr; rewrite /exec /RegLocate.
        * destruct x; simpl.
          { destruct y; simpl.
            - destruct (reg_eq_dec dst PC).
              + subst dst.
                rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
                simpl. subst z; subst z0.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame. auto.
              + rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z; subst z0.
                iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
            - destruct (reg_eq_dec dst PC).
              + subst dst.
                rewrite H4 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                subst z.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); auto.
              + rewrite H4 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z.
                destruct (reg_eq_dec r0 dst); [subst r0; iMod (@gen_heap_update with "Hr Hy") as "[Hr Hy]"|iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]"].
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto. }
          { destruct y; simpl.
            - destruct (reg_eq_dec dst PC).
              + subst dst; rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                subst z.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); auto.
              + rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z.
                destruct (reg_eq_dec r0 dst); [subst r0; iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]"|iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]"].
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
            - destruct (reg_eq_dec dst PC).
              { subst dst.
                rewrite H3 H4 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); destruct (reg_eq_dec r1 PC); auto; iFrame. }
              rewrite H3 H4 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=.
              destruct (reg_eq_dec r0 dst).
              + subst r0.
                iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy]"); iFrame; auto;
                    destruct (reg_eq_dec r1 dst); auto.
              + destruct (reg_eq_dec r1 dst).
                * subst r1.
                  iMod (@gen_heap_update with "Hr Hy") as "[Hr Hy]".
                  destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy]"); iFrame; auto.
                * iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                  destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy Hdst]"); iFrame; auto. }
        * destruct x; simpl.
          { destruct y; simpl.
            - destruct (reg_eq_dec dst PC).
              + subst dst.
                rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
                simpl. subst z; subst z0.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame. auto.
              + rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z; subst z0.
                iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
            - destruct (reg_eq_dec dst PC).
              + subst dst.
                rewrite H4 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                subst z.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); auto.
              + rewrite H4 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z.
                destruct (reg_eq_dec r0 dst); [subst r0; iMod (@gen_heap_update with "Hr Hy") as "[Hr Hy]"|iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]"].
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto. }
          { destruct y; simpl.
            - destruct (reg_eq_dec dst PC).
              + subst dst; rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                subst z.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); auto.
              + rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z.
                destruct (reg_eq_dec r0 dst); [subst r0; iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]"|iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]"].
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
            - destruct (reg_eq_dec dst PC).
              { subst dst.
                rewrite H3 H4 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); destruct (reg_eq_dec r1 PC); auto; iFrame. }
              rewrite H3 H4 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=.
              destruct (reg_eq_dec r0 dst).
              + subst r0.
                iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy]"); iFrame; auto;
                    destruct (reg_eq_dec r1 dst); auto.
              + destruct (reg_eq_dec r1 dst).
                * subst r1.
                  iMod (@gen_heap_update with "Hr Hy") as "[Hr Hy]".
                  destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy]"); iFrame; auto.
                * iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                  destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy Hdst]"); iFrame; auto. }
        * destruct x; simpl.
          { destruct y; simpl.
            - destruct (reg_eq_dec dst PC).
              + subst dst.
                rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
                simpl. subst z; subst z0.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame. auto.
              + rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z; subst z0.
                iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
            - destruct (reg_eq_dec dst PC).
              + subst dst.
                rewrite H4 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                subst z.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); auto.
              + rewrite H4 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z.
                destruct (reg_eq_dec r0 dst); [subst r0; iMod (@gen_heap_update with "Hr Hy") as "[Hr Hy]"|iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]"].
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto. }
          { destruct y; simpl.
            - destruct (reg_eq_dec dst PC).
              + subst dst; rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                subst z.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); auto.
              + rewrite H3 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
                rewrite H1 /=. subst z.
                destruct (reg_eq_dec r0 dst); [subst r0; iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]"|iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]"].
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                * destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
            - destruct (reg_eq_dec dst PC).
              { subst dst.
                rewrite H3 H4 /update_reg /updatePC /RegLocate /= lookup_insert /=; auto.
                iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
                iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst Hx Hy]"); iFrame; auto.
                destruct (reg_eq_dec r0 PC); destruct (reg_eq_dec r1 PC); auto; iFrame. }
              rewrite H3 H4 /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
              rewrite H1 /=.
              destruct (reg_eq_dec r0 dst).
              + subst r0.
                iMod (@gen_heap_update with "Hr Hx") as "[Hr Hx]".
                destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                  iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy]"); iFrame; auto;
                    destruct (reg_eq_dec r1 dst); auto.
              + destruct (reg_eq_dec r1 dst).
                * subst r1.
                  iMod (@gen_heap_update with "Hr Hy") as "[Hr Hy]".
                  destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy]"); iFrame; auto.
                * iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
                  destruct (a+1)%a; [iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]"|];
                    iSpecialize ("Hϕ" with "[HPC Hpc_a Hx Hy Hdst]"); iFrame; auto. }
  Qed.  

  Lemma wp_add_sub_lt_fail1 E dst r1 pc_p pc_g pc_b pc_e pc_a w x y pc_p' :
    cap_lang.decode w = cap_lang.Add dst (inr r1) y \/ cap_lang.decode w = Sub dst (inr r1) y \/ cap_lang.decode w = Lt dst (inr r1) y →

    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ r1 ↦ᵣ inr x }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inr x }}}.
  Proof.
    intros Hinstr Hfl Hvpc;
      (iIntros (φ) "(HPC & Hpc_a & Hr1) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid with "Hr Hr1") as %?;
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
       option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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
        iSplitR; auto.
        simpl. iApply "Hφ".
        iFrame.
      + rewrite Hr1. assert (X: match y with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct y; auto).
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
      + rewrite Hr1. assert (X: match y with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct y; auto).
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
  Qed.

  Lemma wp_add_sub_lt_fail2 E dst r2 pc_p pc_g pc_b pc_e pc_a w x y pc_p' :
    cap_lang.decode w = cap_lang.Add dst x (inr r2) \/ cap_lang.decode w = Sub dst x (inr r2) \/ cap_lang.decode w = Lt dst x (inr r2) →

    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ r2 ↦ᵣ inr y }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ inr y }}}.
  Proof.
    intros Hinstr Hfl Hvpc;
      (iIntros (φ) "(HPC & Hpc_a & Hr2) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid with "Hr Hr2") as %?;
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
       option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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
        iSplitR; auto. by (iApply "Hφ"; iFrame).
      + rewrite Hr2. assert (X: match x with
                                | inl _ => (Failed, (r, m))
                                | inr r1 => match r !r! r1 with
                                           | inl _ | _ => (Failed, (r, m))
                                           end
                                end = (Failed, (r, m))).
        { destruct x; auto. destruct (r !r! r0); auto. }
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
      + rewrite Hr2. assert (X: match x with
                                | inl _ => (Failed, (r, m))
                                | inr r1 => match r !r! r1 with
                                           | inl _ | _ => (Failed, (r, m))
                                           end
                                end = (Failed, (r, m))).
        { destruct x; auto. destruct (r !r! r0); auto. }
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
  Qed.

  Lemma wp_add_sub_lt_PC_fail1 E dst pc_p pc_g pc_b pc_e pc_a w y pc_p' :
    cap_lang.decode w = cap_lang.Add dst (inr PC) y \/ cap_lang.decode w = Sub dst (inr PC) y \/ cap_lang.decode w = Lt dst (inr PC) y →

    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    intros Hinstr Hfl Hvpc;
      (iIntros (φ) "(HPC & Hpc_a) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
       option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [],(Instr Failed), (r, m), [].
      iPureIntro.
      constructor.
      destruct Hinstr as [Hinstr | [Hinstr | Hinstr]].
      + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (cap_lang.Add dst (inr PC) y)
                               (Failed,_));
          eauto; simpl; try congruence.
        rewrite HPC. destruct y; auto.
      + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Sub dst (inr PC) y)
                               (Failed,_));
          eauto; simpl; try congruence.
        rewrite HPC. destruct y; auto.
      + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lt dst (inr PC) y)
                               (Failed,_));
          eauto; simpl; try congruence.
        rewrite HPC. destruct y; auto.
    - iModIntro.
      iIntros (e1 σ2 efs Hstep). destruct Hinstr as [Hinstr | [Hinstr | Hinstr]];
                                   inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      + rewrite HPC. assert (X: match y with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct y; auto).
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto.
        simpl. iApply "Hφ".
        iFrame.
      + rewrite HPC. assert (X: match y with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct y; auto).
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
      + rewrite HPC. assert (X: match y with | inl _ | _ => (Failed, (r, m)) end = (Failed, (r, m))) by (destruct y; auto).
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
  Qed.

  Lemma wp_add_sub_lt_PC_fail2 E dst pc_p pc_g pc_b pc_e pc_a w x pc_p' :
    cap_lang.decode w = cap_lang.Add dst x (inr PC) \/ cap_lang.decode w = Sub dst x (inr PC) \/ cap_lang.decode w = Lt dst x (inr PC) →

    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    intros Hinstr Hfl Hvpc;
      (iIntros (φ) "(HPC & Hpc_a) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n') "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
       option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      iExists [],(Instr Failed), (r, m), [].
      iPureIntro.
      constructor.
      destruct Hinstr as [Hinstr | [Hinstr | Hinstr]].
      + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (cap_lang.Add dst x (inr PC))
                               (Failed,_));
          eauto; simpl; try congruence.
        rewrite HPC. destruct x; auto. destruct (r !r! r0); auto.
      + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Sub dst x (inr PC))
                               (Failed,_));
          eauto; simpl; try congruence.
        rewrite HPC. destruct x; auto. destruct (r !r! r0); auto.
      + apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Lt dst x (inr PC))
                               (Failed,_));
          eauto; simpl; try congruence.
        rewrite HPC. destruct x; auto. destruct (r !r! r0); auto.
    - iModIntro.
      iIntros (e1 σ2 efs Hstep). destruct Hinstr as [Hinstr | [Hinstr | Hinstr]];
                                   inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
      + rewrite HPC. assert (X: match x with
                                | inl _ => (Failed, (r, m))
                                | inr r1 => match r !r! r1 with
                                           | inl _ | _ => (Failed, (r, m))
                                           end
                                end = (Failed, (r, m))).
        { destruct x; auto. destruct (r !r! r0); auto. }
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
      + rewrite HPC. assert (X: match x with
                                | inl _ => (Failed, (r, m))
                                | inr r1 => match r !r! r1 with
                                           | inl _ | _ => (Failed, (r, m))
                                           end
                                end = (Failed, (r, m))).
        { destruct x; auto. destruct (r !r! r0); auto. }
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
      + rewrite HPC. assert (X: match x with
                                | inl _ => (Failed, (r, m))
                                | inr r1 => match r !r! r1 with
                                           | inl _ | _ => (Failed, (r, m))
                                           end
                                end = (Failed, (r, m))).
        { destruct x; auto. destruct (r !r! r0); auto. }
        rewrite X.
        iFrame. iNext. iModIntro.
        iSplitR; auto. by (iApply "Hφ"; iFrame).
  Qed.

End cap_lang_rules.
