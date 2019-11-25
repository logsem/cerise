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