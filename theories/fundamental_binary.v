From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr_binary Require Export Mov_binary Load_binary AddSubLt_binary Get_binary IsPtr_binary Jmp_binary.
From cap_machine Require Export logrel_binary.

Section bin_log_def.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MP: MachineParameters}.
  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iProp Σ).

  Definition bin_log_related (w w' : Word) :=
    ∀ r, spec_ctx ⊢ interp_expression r (w,w').
End bin_log_def.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MP: MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma extract_r_ex r (reg : RegName) :
    (∃ w, r !! reg = Some w) →
    ⊢ (([∗ map] r0↦w ∈ r, r0 ↣ᵣ w) → ∃ w, reg ↣ᵣ w)%I.
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w.
    iApply (big_sepM_lookup (λ reg' i, reg' ↣ᵣ i)%I r reg w); eauto.
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    ⊢ (([∗ map] r0↦w ∈ reg, r0 ↣ᵣ w) →
     (r ↣ᵣ w ∗ (∀ x', r ↣ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↣ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap".
    iDestruct (big_sepM_lookup_acc (λ (r : RegName) i, r ↣ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ (r : RegName) i, r ↣ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto.
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl eq_refl).

  Lemma interp_argeq p b e a p' b' e' a' :
    ⊢ (interp (inr (p,b,e,a),inr (p',b',e',a')) → ⌜p = p' ∧ b = b' ∧ e = e' ∧ a = a'⌝)%I.
  Proof.
    iIntros "Hinterp".
    rewrite fixpoint_interp1_eq /=.
    destruct p,p';try done;[|iDestruct "Hinterp" as "[Hinterp _]"..];
    iDestruct "Hinterp" as %(-> & -> & ->);auto.
  Qed.

  Theorem fundamental_binary r p b e a p' b' e' a' :
    ⊢ (spec_ctx → interp (inr (p,b,e,a),inr (p',b',e',a')) → interp_expression r (inr (p,b,e,a),inr (p',b',e',a')))%I.
  Proof.
    iIntros "#Hspec #Hval".
    iIntros "[[Hfull Hreg] [Hmreg [Hsreg [Hown Hs]]]]". simpl.
    iSplit; eauto; simpl.
    iDestruct (interp_argeq with "Hval") as %(<- & <- & <- & <-).
    iRevert "Hspec Hval".
    iLöb as "IH" forall (r p b e a).
    iIntros "#Hspec #Hinv".
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr (p,b,e,a)))).
    - assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; lia. }
      assert (p = RX ∨ p = RWX) as Hp.
      { inversion i. subst. auto. }
      iDestruct (read_allowed_inv_regs with "[] Hinv") as (P) "(#Hinva & #Hread)";[eauto|destruct Hp as [-> | ->];auto|iFrame "% #"|simpl].
      rewrite /interp_ref_inv /=.
      iInv (logN.@a) as (w w') "[>Ha [>Ha' HP] ]" "Hcls".
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
        first apply (lookup_insert _ _ (inr (p, b, e, a))).
      destruct (decodeInstrW w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *) iApply (jmp_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try iAssumption; eauto.
      + (* Jnz *) admit.
      + (* Mov *) iApply (mov_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Load *) iApply (load_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Store *) admit.
      + (* Lt *) iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try (eapply Hi); try iAssumption; eauto.
      + (* Add *) iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try (eapply Hi); try iAssumption; eauto.
      + (* Sub *) iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try (eapply Hi); try iAssumption; eauto.
      + (* Lea *) admit.
      + (* Restrict *) admit.
      + (* Subseg *) admit.
      + (* IsPtr *) iApply (isptr_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try iAssumption; eauto.
      + (* GetP *) iApply (get_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try (eapply Hi); try iAssumption; eauto.
      + (* GetB *) iApply (get_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try (eapply Hi); try iAssumption; eauto.
      + (* GetE *) iApply (get_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try (eapply Hi); try iAssumption; eauto.
      + (* GetA *) iApply (get_case with "[] [] [] [] [] [] [Hsreg] [Hown] [Hs] [Ha] [Ha'] [HP] [Hcls] [HPC] [Hmap]"); try (eapply Hi); try iAssumption; eauto.
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iMod ("Hcls" with "[HP Ha Ha']");[iExists w;iFrame|iModIntro].
        * iNext. iExists w'. iFrame.
        * iIntros (Hcontr); inversion Hcontr.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iMod ("Hcls" with "[HP Ha Ha']");[iExists w;iFrame|iModIntro].
        * iExists w'. iFrame.
        * iNext. iIntros (_).
          iExists (<[PC:=inr (p, b, e, a)]> r.1, <[PC:=inr (p, b, e, a)]> r.2). iFrame.
          iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (p, b, e, a)]> r.1 !! r0) ∧ is_Some (<[PC:=inr (p, b, e, a)]> r.2 !! r0)⌝)%I as "HA".
          { iPureIntro. intros. simpl. destruct (reg_eq_dec PC x).
            - subst x. rewrite !lookup_insert. split; eauto.
            - rewrite !lookup_insert_ne; auto. }
          rewrite /full_map /=. iFrame "HA".
          admit.
    - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (p, b, e, a))).
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
  Admitted.

  (* The fundamental theorem implies the binary exec_cond *)

  Definition exec_cond_binary b e p b' e' p' : iProp Σ :=
    (∀ a r, ⌜a ∈ₐ [[ b , e ]]⌝ → ▷ □ interp_expression r (inr (p,b, e,a), inr (p',b',e',a)))%I.

  Lemma interp_exec_cond p b e a p' b' e' :
    p ≠ E -> spec_ctx -∗ interp (inr (p,b,e,a),inr (p',b',e',a)) -∗ exec_cond_binary b e p b' e' p'.
  Proof.
    iIntros (Hnp) "#Hspec #Hw".
    iIntros (a0 r Hin). iNext. iModIntro.
    iApply (fundamental_binary with "Hspec").
    rewrite !logrel_binary.fixpoint_interp1_eq /=. destruct p,p'; try done.
    iDestruct "Hw" as %(->&->&?). done.
    all: iDestruct "Hw" as "[#Heq Hw]"; iDestruct "Heq" as %(->&->&?); iSplit;auto.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)

  Lemma exec_wp p b e a p' b' e' :
    isCorrectPC (inr (p, b, e, a)) ->
    exec_cond_binary b e p b' e' p' -∗
    ∀ r, ▷ □ (interp_expr interp r) (inr (p, b, e, a),inr (p', b', e', a)).
  Proof.
    iIntros (Hvpc) "#Hexec".
    rewrite /exec_cond_binary /enter_cond.
    iIntros (r).
    assert (a ∈ₐ[[b,e]])%I as Hin.
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    iSpecialize ("Hexec" $! a r Hin). iFrame "#".
  Qed.

  Lemma jmp_or_fail_spec w w' φ :
    ⊢ (spec_ctx -∗ interp (w,w')
    -∗ (if decide (isCorrectPC (updatePcPerm w)) then
          (∃ p b e a, ⌜w = inr (p,b,e,a)⌝
          ∗ ∀ r, ▷ □ (interp_expr interp r) (updatePcPerm w,updatePcPerm w'))
        else
          φ FailedV ∗ PC ↦ᵣ updatePcPerm w -∗ WP Seq (Instr Executable) {{ φ }} ))%I.
  Proof.
    iIntros "#Hspec #Hw".
    iDestruct (interp_eq with "Hw") as %<-.
    destruct (decide (isCorrectPC (updatePcPerm w))).
    - inversion i.
      destruct w;inversion H. destruct c,p0,p0; inversion H.
      destruct H1 as [-> | ->].
      + destruct p0; simpl in H; simplify_eq.
        * iExists _,_,_,_; iSplit;[eauto|].
          iDestruct (interp_exec_cond with "Hspec Hw") as "Hexec";[auto|].
          iApply exec_wp;auto.
        * iExists _,_,_,_; iSplit;[eauto|].
          rewrite /= fixpoint_interp1_eq /=.
          iDestruct "Hw" as "[_ Hw]".
          iExact "Hw".
      + destruct p0; simpl in H; simplify_eq.
        iExists _,_,_,_; iSplit;[eauto|].
        iDestruct (interp_exec_cond with "Hspec Hw") as "Hexec";[auto|].
        iApply exec_wp;auto.
    - iIntros "[Hfailed HPC]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC");eauto.
      iNext. iIntros "_".
      iApply wp_pure_step_later;auto;iNext.
      iApply wp_value. iFrame.
  Qed.

End fundamental.
