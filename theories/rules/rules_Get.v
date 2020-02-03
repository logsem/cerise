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

  Lemma wp_GetL_success E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_a' pc_p' :
    cap_lang.decode w = GetL dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET if reg_eq_dec PC src then NextIV else match wsrc with inr _ => NextIV | _ => FailedV end;
          PC ↦ᵣ (if reg_eq_dec PC src then inr ((pc_p,pc_g),pc_b,pc_e,pc_a') else match wsrc with inr _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (encodeLoc pc_g) else match wsrc with | inr ((_,g'),_,_,_) => inl (encodeLoc g') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork_determ; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iModIntro. iExists [], (Instr _), _, [].
    iSplit.
    - iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetL dst src) (exec (GetL dst src) (r, m))); eauto.
      + simpl in *. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iNext.
      rewrite /exec /RegLocate.
      destruct (reg_eq_dec PC src).
      * subst src. rewrite H1.
        destruct (reg_eq_dec PC dst); try contradiction.
        rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
        rewrite H1 Hpca' /=.
        iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
      * rewrite H3. destruct wsrc.
        { simpl. iFrame. destruct (reg_eq_dec src dst).
          - subst src. 
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
          - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
        { simpl. destruct c. destruct p,p,p.
          rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          destruct (reg_eq_dec src dst).
          - subst src.
            iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
          - iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetP_success E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_a' pc_p' :
    cap_lang.decode w = GetP dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET if reg_eq_dec PC src then NextIV else match wsrc with inr _ => NextIV | _ => FailedV end;
          PC ↦ᵣ (if reg_eq_dec PC src then inr ((pc_p,pc_g),pc_b,pc_e,pc_a') else match wsrc with inr _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (encodePerm pc_p) else match wsrc with | inr ((p',_),_,_,_) => inl (encodePerm p') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork_determ; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iModIntro. iExists [], (Instr _), _, [].
    iSplit.
    - iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetP dst src) (exec (GetP dst src) (r, m))); eauto.
      + simpl in *. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iNext.
      rewrite /exec /RegLocate.
      destruct (reg_eq_dec PC src).
      * subst src. rewrite H1.
        destruct (reg_eq_dec PC dst); try contradiction.
        rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
        rewrite H1 Hpca' /=.
        iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
      * rewrite H3. destruct wsrc.
        { simpl. iFrame. destruct (reg_eq_dec src dst).
          - subst src. 
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
          - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
        { simpl. destruct c. destruct p,p,p.
          rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          destruct (reg_eq_dec src dst).
          - subst src.
            iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
          - iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetB_success E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_a' pc_p' :
    cap_lang.decode w = GetB dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET if reg_eq_dec PC src then NextIV else match wsrc with inr _ => NextIV | _ => FailedV end;
          PC ↦ᵣ (if reg_eq_dec PC src then inr ((pc_p,pc_g),pc_b,pc_e,pc_a') else match wsrc with inr _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (z_of pc_b) else match wsrc with | inr ((_,_),A b' _,_,_) => inl b' | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork_determ; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iModIntro. iExists [], (Instr _), _, [].
    iSplit.
    - iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetB dst src) (exec (GetB dst src) (r, m))); eauto.
      + simpl in *. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iNext.
      rewrite /exec /RegLocate.
      destruct (reg_eq_dec PC src).
      * subst src. rewrite H1.
        destruct (reg_eq_dec PC dst); try contradiction.
        rewrite /update_reg /updatePC /RegLocate /=; auto.
        destruct pc_b; rewrite lookup_insert_ne; auto.
        rewrite H1 Hpca' /=.
        iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
      * rewrite H3. destruct wsrc.
        { simpl. iFrame. destruct (reg_eq_dec src dst).
          - subst src. 
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
          - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
        { simpl. destruct c. destruct p,p,p.
          rewrite /update_reg /updatePC /RegLocate /=; auto.
          destruct a1; rewrite lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          destruct (reg_eq_dec src dst).
          - subst src.
            iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
          - iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetE_success E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_a' pc_p' :
    cap_lang.decode w = GetE dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET if reg_eq_dec PC src then NextIV else match wsrc with inr _ => NextIV | _ => FailedV end;
          PC ↦ᵣ (if reg_eq_dec PC src then inr ((pc_p,pc_g),pc_b,pc_e,pc_a') else match wsrc with inr _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (z_of pc_e) else match wsrc with | inr ((_,_),_,e',_) => inl (z_of e') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork_determ; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iModIntro. iExists [], (Instr _), _, [].
    iSplit.
    - iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetE dst src) (exec (GetE dst src) (r, m))); eauto.
      + simpl in *. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iNext.
      rewrite /exec /RegLocate.
      destruct (reg_eq_dec PC src).
      * subst src. rewrite H1.
        destruct (reg_eq_dec PC dst); try contradiction.
        rewrite /update_reg /updatePC /RegLocate /=; auto.
        destruct pc_e; rewrite lookup_insert_ne; auto.
        rewrite H1 Hpca' /=.
        iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
      * rewrite H3. destruct wsrc.
        { simpl. iFrame. destruct (reg_eq_dec src dst).
          - subst src. 
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
          - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
        { simpl. destruct c. destruct p,p,p.
          rewrite /update_reg /updatePC /RegLocate /=; auto.
          destruct a0; rewrite lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          destruct (reg_eq_dec src dst).
          - subst src.
            iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
          - iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetA_success E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_a' pc_p' :
    cap_lang.decode w = GetA dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET if reg_eq_dec PC src then NextIV else match wsrc with inr _ => NextIV | _ => FailedV end;
          PC ↦ᵣ (if reg_eq_dec PC src then inr ((pc_p,pc_g),pc_b,pc_e,pc_a') else match wsrc with inr _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (z_of pc_a) else match wsrc with | inr ((_,_),_,_,a') => inl (z_of a') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork_determ; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iModIntro. iExists [], (Instr _), _, [].
    iSplit.
    - iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetA dst src) (exec (GetA dst src) (r, m))); eauto.
      + simpl in *. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iNext.
      rewrite /exec /RegLocate.
      destruct (reg_eq_dec PC src).
      * subst src. rewrite H1.
        destruct (reg_eq_dec PC dst); try contradiction.
        rewrite /update_reg /updatePC /RegLocate /=; auto.
        destruct pc_a; rewrite lookup_insert_ne; auto.
        rewrite H1 Hpca' /=.
        iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
      * rewrite H3. destruct wsrc.
        { simpl. iFrame. destruct (reg_eq_dec src dst).
          - subst src. 
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
          - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
        { simpl. destruct c. destruct p,p,p.
          rewrite /update_reg /updatePC /RegLocate /=; auto.
          destruct a; rewrite lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          destruct (reg_eq_dec src dst).
          - subst src.
            iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
          - iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetL_failPC E src pc_p pc_g pc_b pc_e pc_a w wsrc pc_p' :
    cap_lang.decode w = GetL PC src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ (if reg_eq_dec PC src then inl (encodeLoc pc_g) else match wsrc with inr ((_,g'),_,_,_) => inl (encodeLoc g') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(HPC & Hpc_a & Hsrc) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetL PC src) (exec (GetL PC src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate.
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
          iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame.
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc ]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto. }
  Qed.

  Lemma wp_GetL_fail E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_p' :
    cap_lang.decode w = GetL dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (encodeLoc pc_g) else match wsrc with | inr ((_,g'),_,_,_) => inl (encodeLoc g') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetL dst src) (exec (GetL dst src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate. 
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          destruct (reg_eq_dec PC dst); try contradiction.
          rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame. destruct (reg_eq_dec src dst).
            - subst src. 
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
            - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
            rewrite H1 Hpca' /=.
            destruct (reg_eq_dec src dst).
            - subst src.
              iMod (@gen_heap_update with "Hr Hsrc") as "[$ Hsrc]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
            - iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetP_failPC E src pc_p pc_g pc_b pc_e pc_a w wsrc pc_p' :
    cap_lang.decode w = GetP PC src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ (if reg_eq_dec PC src then inl (encodePerm pc_p) else match wsrc with inr ((p',_),_,_,_) => inl (encodePerm p') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(HPC & Hpc_a & Hsrc) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetP PC src) (exec (GetP PC src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate.
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
          iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame.
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc ]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto. }
  Qed.

  Lemma wp_GetP_fail E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_p' :
    cap_lang.decode w = GetP dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (encodePerm pc_p) else match wsrc with | inr ((p',_),_,_,_) => inl (encodePerm p') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetP dst src) (exec (GetP dst src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate. 
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          destruct (reg_eq_dec PC dst); try contradiction.
          rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame. destruct (reg_eq_dec src dst).
            - subst src. 
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
            - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
            rewrite H1 Hpca' /=.
            destruct (reg_eq_dec src dst).
            - subst src.
              iMod (@gen_heap_update with "Hr Hsrc") as "[$ Hsrc]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
            - iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetB_failPC E src pc_p pc_g pc_b pc_e pc_a w wsrc pc_p' :
    cap_lang.decode w = GetB PC src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ (if reg_eq_dec PC src then inl (z_of pc_b) else match wsrc with inr ((_,_),b',_,_) => inl (z_of b') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(HPC & Hpc_a & Hsrc) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetB PC src) (exec (GetB PC src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate.
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          rewrite /update_reg /updatePC /RegLocate /=.
          destruct b; rewrite lookup_insert; auto.
          iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame.
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc ]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /=.
            destruct a2; rewrite lookup_insert; auto.
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto. }
  Qed.

  Lemma wp_GetB_fail E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_p' :
    cap_lang.decode w = GetB dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (z_of pc_b) else match wsrc with | inr ((_,_),b',_,_) => inl (z_of b') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetB dst src) (exec (GetB dst src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate. 
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          destruct (reg_eq_dec PC dst); try contradiction.
          rewrite /update_reg /updatePC /RegLocate /=.
          destruct b; rewrite lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame. destruct (reg_eq_dec src dst).
            - subst src. 
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
            - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /=.
            destruct a2; rewrite lookup_insert_ne; auto.
            rewrite H1 Hpca' /=.
            destruct (reg_eq_dec src dst).
            - subst src.
              iMod (@gen_heap_update with "Hr Hsrc") as "[$ Hsrc]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
            - iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetE_failPC E src pc_p pc_g pc_b pc_e pc_a w wsrc pc_p' :
    cap_lang.decode w = GetE PC src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ (if reg_eq_dec PC src then inl (z_of pc_e) else match wsrc with inr ((_,_),_,e',_) => inl (z_of e') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(HPC & Hpc_a & Hsrc) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetE PC src) (exec (GetE PC src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate.
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          rewrite /update_reg /updatePC /RegLocate /=.
          destruct e; rewrite lookup_insert; auto.
          iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame.
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc ]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /=.
            destruct a1; rewrite lookup_insert; auto.
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto. }
  Qed.

  Lemma wp_GetE_fail E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_p' :
    cap_lang.decode w = GetE dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (z_of pc_e) else match wsrc with | inr ((_,_),_,e',_) => inl (z_of e') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetE dst src) (exec (GetE dst src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate. 
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          destruct (reg_eq_dec PC dst); try contradiction.
          rewrite /update_reg /updatePC /RegLocate /=.
          destruct e; rewrite lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame. destruct (reg_eq_dec src dst).
            - subst src. 
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
            - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /=.
            destruct a1; rewrite lookup_insert_ne; auto.
            rewrite H1 Hpca' /=.
            destruct (reg_eq_dec src dst).
            - subst src.
              iMod (@gen_heap_update with "Hr Hsrc") as "[$ Hsrc]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
            - iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  Lemma wp_GetA_failPC E src pc_p pc_g pc_b pc_e pc_a w wsrc pc_p' :
    cap_lang.decode w = GetA PC src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ (if reg_eq_dec PC src then inl (z_of pc_a) else match wsrc with inr ((_,_),b',_,a') => inl (z_of a') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(HPC & Hpc_a & Hsrc) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetA PC src) (exec (GetA PC src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate.
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          rewrite /update_reg /updatePC /RegLocate /=.
          destruct a; rewrite lookup_insert; auto.
          iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame.
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc ]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /=.
            destruct a0; rewrite lookup_insert; auto.
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto. }
  Qed.

  Lemma wp_GetA_fail E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_p' :
    cap_lang.decode w = GetA dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ dst ↦ᵣ if reg_eq_dec PC src then inl (z_of pc_a) else match wsrc with | inr ((_,_),b',_,a') => inl (z_of a') | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      unfold head_reducible. iExists [], (Instr _), _, [].
      iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (GetA dst src) (exec (GetA dst src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iModIntro. iNext. iIntros (e1 σ2 efs Hstep).
      inv Hstep. inv H4.
      + simpl in H7; unfold RegLocate in H7; rewrite H1 in H7; contradiction.
      + clear H9. rewrite /RegLocate H1 in H8. inv H8.
        rewrite /MemLocate H2 Hinstr /exec /RegLocate. 
        destruct (reg_eq_dec PC src).
        * subst src. rewrite H1.
          destruct (reg_eq_dec PC dst); try contradiction.
          rewrite /update_reg /updatePC /RegLocate /=.
          destruct a; rewrite lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
          iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame. auto.
        * rewrite H3. destruct wsrc.
          { simpl. iFrame. destruct (reg_eq_dec src dst).
            - subst src. 
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto.
            - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
          { simpl. destruct c, p0, p0, p0.
            rewrite /update_reg /updatePC /RegLocate /=.
            destruct a0; rewrite lookup_insert_ne; auto.
            rewrite H1 Hpca' /=.
            destruct (reg_eq_dec src dst).
            - subst src.
              iMod (@gen_heap_update with "Hr Hsrc") as "[$ Hsrc]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame. auto.
            - iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
              iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame. auto. }
  Qed.

  (* Generalized versions of the above lemma's, where a general Get instruction is assumed instead of a specific one. Additionally, the postconditions have been set to True in the failing cases, since no more information will be required in practical use *)

  Lemma wp_GetGeneral_success E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_a' pc_p' i:
    cap_lang.decode w = i dst src →
   (isGetInstr i) →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET if reg_eq_dec PC src then NextIV else match wsrc with inr _ => NextIV | _ => FailedV end;
          PC ↦ᵣ (if reg_eq_dec PC src then inr ((pc_p,pc_g),pc_b,pc_e,pc_a') else match wsrc with inr _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a') | inl _ => inr ((pc_p,pc_g),pc_b,pc_e,pc_a) end)
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ (if reg_eq_dec PC src then emp else if reg_eq_dec src dst then emp else src ↦ᵣ wsrc)
             ∗ ∃z, dst ↦ᵣ if reg_eq_dec PC src then inl z else match wsrc with | inr _ => inl z | _ => if reg_eq_dec src dst then wsrc else wdst end }}}.
  Proof.
    iIntros (Hinstr Hgetinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork_determ; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.
    iModIntro. iExists [], (Instr _), _, [].
    iSplit.
    - iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (i dst src) (exec (i dst src) (r, m))); eauto.
      + simpl in *. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iNext.
      destruct Hgetinstr. specialize H4 with (r,m) dst src. destruct H4 as [z0 H4].
      rewrite H4 /getterTemplate /RegLocate.
      destruct (reg_eq_dec PC src).
      * subst src. rewrite H1.
        destruct (reg_eq_dec PC dst); first by contradiction.
        rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
        rewrite H1 Hpca' /=.
        iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame; auto.
      * rewrite H3. destruct wsrc.
        { simpl. iFrame. destruct (reg_eq_dec src dst).
          - subst src.
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame; auto.
          - iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame; auto.
        }
        { simpl.
          rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          destruct (reg_eq_dec src dst).
          - subst src.
            iMod (@gen_heap_update with "Hr Hsrc") as "[Hr Hsrc]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame; auto.
          - iMod (@gen_heap_update with "Hr Hdst") as "[Hr Hdst]".
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc Hdst]"); iFrame; auto. }
  Qed.

  Lemma wp_GetGeneral_failPC E src pc_p pc_g pc_b pc_e pc_a w wsrc pc_p' i:
    cap_lang.decode w = i PC src →
    (isGetInstr i) →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc) }}}
      Instr Executable @ E
      {{{ RET FailedV; True}}}.
  Proof.
    iIntros (Hinstr Hgetinstr Hfl Hvpc ϕ) "(HPC & Hpc_a & Hsrc) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork_determ; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }

    iModIntro. iExists [], (Instr _), _, [].
    iSplit.
    - iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (i PC src) (exec (i PC src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iNext.
      destruct Hgetinstr. specialize H4 with (r,m) PC src. destruct H4 as [z0 H4].
      rewrite H4 /getterTemplate /RegLocate.
      destruct (reg_eq_dec PC src).
      * subst src. rewrite H1.
        rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
        iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame; auto.
      * rewrite H3. destruct wsrc.
          { simpl. iFrame.
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc ]"); iFrame; auto. }
          { simpl.
            rewrite /update_reg /updatePC /RegLocate /= lookup_insert; auto.
            iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
            iSpecialize ("Hϕ" with "[HPC Hpc_a Hsrc]"); iFrame; auto. }
Qed.

  Lemma wp_GetGeneral_fail E dst src pc_p pc_g pc_b pc_e pc_a w wdst wsrc pc_p' i:
    cap_lang.decode w = i dst src →
    (isGetInstr i) →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = None ->
    PC <> dst ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ (if reg_eq_dec PC src then emp else src ↦ᵣ wsrc)
           ∗ (if reg_eq_dec src dst then emp else dst ↦ᵣ wdst) }}}
      Instr Executable @ E
      {{{ RET FailedV; True}}}.
  Proof.
    iIntros (Hinstr Hgetinstr Hfl Hvpc Hpca' Hne ϕ) "(HPC & Hpc_a & Hsrc & Hdst) Hϕ".
    iApply wp_lift_atomic_head_step_no_fork_determ; auto.
    iIntros (σ1 l1 l2 n) "Hσ1". destruct σ1.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst;
        destruct H8 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
    iAssert (⌜if reg_eq_dec PC src then True else r !! src = Some wsrc⌝)%I with "[Hr Hsrc]" as %?.
    { destruct (reg_eq_dec PC src).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hsrc") as %?. auto. }
    iAssert (⌜if reg_eq_dec src dst then True else r !! dst = Some wdst⌝)%I with "[Hr Hdst]" as %?.
    { destruct (reg_eq_dec src dst).
      - auto.
      - iDestruct (@gen_heap_valid with "Hr Hdst") as %?. auto. } rename H4 into X4.

    iModIntro. iExists [], (Instr _), _, [].
    iSplit.
    - iPureIntro. constructor.
      eapply (step_exec_instr (r, m) pc_p pc_g pc_b pc_e pc_a (i dst src) (exec (i dst src) (r, m))); eauto.
      + simpl. unfold RegLocate. rewrite H1. auto.
      + unfold RegLocate. rewrite H1. auto.
      + simpl. unfold MemLocate; rewrite H2; auto.
    - iNext.
      destruct Hgetinstr. specialize H4 with (r,m) dst src. destruct H4 as [z0 H4].
      rewrite H4 /getterTemplate /RegLocate.
      destruct (reg_eq_dec PC src).
      * subst src. rewrite H1.
        destruct (reg_eq_dec PC dst); try contradiction.
        rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
        rewrite H1 Hpca' /=.
        iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]".
        iSpecialize ("Hϕ" with "[HPC Hpc_a Hdst]"); iFrame; auto.
      * rewrite H3. destruct wsrc.
        { simpl. iFrame. destruct (reg_eq_dec src dst); by iApply "Hϕ". }
        { simpl.
          rewrite /update_reg /updatePC /RegLocate /= lookup_insert_ne; auto.
          rewrite H1 Hpca' /=.
          destruct (reg_eq_dec src dst).
          - subst src.
            iMod (@gen_heap_update with "Hr Hsrc") as "[$ Hsrc]". iFrame; by iApply "Hϕ".
          - iMod (@gen_heap_update with "Hr Hdst") as "[$ Hdst]". iFrame; by iApply "Hϕ". }
  Qed.

End cap_lang_rules.
