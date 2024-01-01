From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros call_ie.
From cap_machine.proofmode Require Import tactics_helpers.

Section callback.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* ---------------------------------------------------------------------------------- *)

  Fixpoint restore_locals_instrs r1 locals :=
    match locals with
    | [] => []
    | r :: locals => (lea_z r1 (-1))
                 :: (load_r r r1)
                 :: restore_locals_instrs r1 locals
    end.

  Definition restore_locals a r1 locals :=
    ([∗ list] a_i;i ∈ a;(restore_locals_instrs r1 locals), a_i ↦ₐ i)%I.

  Lemma length_restore_locals r1 locals :
    strings.length (restore_locals_instrs r1 locals) = 2 * length locals.
  Proof.
    induction locals;auto.
    simpl. lia.
  Qed.

  Lemma restore_locals_spec_middle
        (* cont *) φ
        (* list of locals *) r1 locals revlocals mlocals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l a_l :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    finz.dist b_l a_l = strings.length revlocals →
    strings.length revlocals > 0 →
    readAllowed p_l = true → (withinBounds b_l e_l a_l = true ∨ a_l = e_l) ->
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length revlocals = length wsr ->
    rev locals = revlocals ->

    (▷ restore_locals a r1 revlocals
   ∗ ▷ PC ↦ᵣ WCap p b e a_first
   ∗ ▷ r1 ↦ᵣ WCap p_l b_l e_l a_l
   ∗ ▷ ([∗ map] r↦_ ∈ mlocals, ∃ w, r ↦ᵣ w)
   ∗ ▷ ([[b_l,a_l]]↦ₐ[[ wsr ]])
   ∗ ▷ (PC ↦ᵣ WCap p b e a_last
           ∗ r1 ↦ᵣ WCap p_l b_l e_l b_l
           ∗ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
           ∗ [[b_l,a_l]]↦ₐ[[wsr]]
           ∗ restore_locals a r1 revlocals
           -∗ WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa Hwb Hperm Hlength Hreveq) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)".
    iInduction (revlocals) as [|r revlocals] "IH" forall (a_l mlocals locals wsr a a_first Hreveq Hvpc Hcont Hnz Hsize Hwb Hperm Hlength).
    { apply rev_nil_inv in Hreveq as ->. inversion Hnz. }
    destruct revlocals as [|r' revlocals].
    - apply rev_singleton_inv in Hreveq as ->. destruct wsr;[inversion Hlength|]. destruct wsr;[|inversion Hlength].
      apply Permutation_sym, Permutation_singleton_r in Hperm.
      assert (mlocals = {[r:=w]}) as Heq;[|subst mlocals].
      { apply map_to_list_inj. rewrite map_to_list_singleton. apply Permutation_singleton_r. auto. }
      rewrite big_sepM_singleton.
      rewrite /restore_locals /restore_locals_instrs.
      iDestruct (big_sepL2_length with "Hbl") as %Hlength_bl.
      rewrite finz_seq_between_length Hsize in Hlength_bl.
      assert (finz.seq_between b_l a_l = [b_l]) as Heq_locals;[ by rewrite /finz.seq_between Hsize /=|].
      rewrite /region_mapsto Heq_locals.
      iDestruct "Hbl" as "[Ha_l _]".
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      (* lea r_t1 -1 *)
      destruct_list a.
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
      assert (a_l + (-1) = Some b_l)%a as Hnext.
      { rewrite /finz.dist /= in Hsize. revert Hsize;clear;solve_addr. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last
        |iContiguous_next Hcont 0|apply Hnext|destruct p_l;auto;inversion Hwa|destruct p_l;auto;inversion Hwa|].
      iEpilogue "(HPC & Hprog_done & Hr_t1)".
      (* load r r_t1 *)
      pose proof (contiguous_between_last _ _ _ a Hcont eq_refl) as Hlast.
      iPrologue "Hprog".
      iDestruct "Hlocals" as (w0) "Hlocals".
      iAssert (⌜(b_l =? a)%a = false⌝)%I as %Hfalse.
      { destruct (decide (b_l = a)%Z); [subst|iPureIntro;apply Z.eqb_neq,finz_neq_to_z;auto].
        iDestruct (mapsto_valid_2 with "Hi Ha_l") as %[? _]. done. }
      iApply (wp_load_success with "[$HPC $Hi $Hlocals Ha_l $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|split;auto|apply Hlast|..].
      { revert Hwb. rewrite !andb_true_iff !Z.leb_le !Z.ltb_lt. clear -Hnext. intros [? | Hcontr];[solve_addr|].
        subst. assert (e_l ≠ b_l) as Hne;[solve_addr|]. solve_addr. }
      { rewrite Hfalse. iFrame. } rewrite Hfalse.
      iEpilogue "(HPC & Hi & Hr & Hr_t1 & Ha_l)".
      (* φ *)
      iApply "Hcont".
      iFrame. iSplit;[|done]. iApply big_sepM_singleton. iFrame.
    - assert (∃ w w0 wsr', wsr = wsr' ++ [w] ++ [w0]) as [w [w0 [wsr' Hwsr'] ] ].
      { destruct wsr;[inversion Hlength|]. destruct wsr;[inversion Hlength|].
        destruct wsr.
        - exists w,w0,[]. auto.
        - assert (is_Some((w :: w0 :: w1 :: wsr) !! length (w1::wsr))) as [? Hsome].
          { apply lookup_lt_is_Some_2. simpl. lia. }
          assert (is_Some((w :: w0 :: w1 :: wsr) !! length (w0::w1::wsr))) as [? Hsome'].
          { apply lookup_lt_is_Some_2. simpl. lia. }
          apply take_S_r in Hsome. simpl in Hsome. inversion Hsome.
          apply take_S_r in Hsome'. simpl in Hsome'. inversion Hsome'.
          exists x,x0,(take (S(strings.length (wsr))) (w::w0::w1::wsr)). simpl. f_equiv.
          assert ([x;x0] = [x] ++ [x0]) as ->;auto. rewrite app_assoc -H0. simpl. f_equiv.
          rewrite -H1. f_equiv. rewrite firstn_all. auto.
      }
      assert (mlocals !! r = Some w0) as Hrw.
      { apply elem_of_map_to_list. rewrite -Hperm.
        apply rev_cons_inv in Hreveq as Hl''. destruct Hl'' as [l'' Hl''].
        rewrite Hl'' rev_unit in Hreveq. inversion Hreveq.
        apply rev_cons_inv in H0 as [l3 Hl3]. rewrite Hl3 in Hl''.
        rewrite Hl'' Hwsr'. rewrite app_assoc.
        rewrite zip_app. apply elem_of_app. right. constructor.
        rewrite !app_length /=. simplify_eq.
        rewrite -Hreveq /= rev_unit /= !app_length /= rev_length in Hlength. clear -Hlength. lia.  }
      iDestruct (big_sepM_delete _ _ r with "Hlocals") as "[Hr Hlocals]";[eauto|].
      assert (is_Some (a_l + (-1))%a) as [a_l' Ha_l'].
      { rewrite /finz.dist /= in Hsize. destruct (a_l + -1)%a eqn:Hnone;eauto.
        simpl in Hsize. revert Hnone Hsize;clear;solve_addr. }
      assert (finz.seq_between b_l a_l = finz.seq_between b_l a_l' ++ [a_l']) as Heq.
      { rewrite (finz_seq_between_split _ a_l').
        assert (finz.seq_between a_l' a_l = [a_l']) as ->;auto.
        apply finz_seq_between_singleton. clear -Ha_l';solve_addr.
        rewrite /finz.dist in Hsize.
        clear -Ha_l' Hsize Hwb. solve_addr. }
      rewrite /region_mapsto Heq.
      iDestruct "Hr" as (w') "Hr".
      iDestruct (big_sepL2_length with "Hbl") as %Hlengthbl.
      rewrite Hwsr'.
      rewrite app_assoc.
      iDestruct (big_sepL2_app' _ _ _ _ (finz.seq_between b_l a_l') _ (wsr' ++ [w]) with "Hbl") as "[Hbl Ha_l]".
      { rewrite Hwsr' in Hlengthbl. rewrite app_length /= app_length /= in Hlengthbl.
        clear -Hlengthbl. rewrite app_length /=. lia. }
      iDestruct "Ha_l" as "[Ha_l _]".
      (* lea r_t1 -1 *)
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      simpl in Hlength_prog.
      destruct a;[inversion Hlength_prog|].
      destruct a;[inversion Hlength_prog|].
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|apply Ha_l'|destruct p_l;auto;inversion Hwa|destruct p_l;auto;inversion Hwa|].
      iEpilogue "(HPC & Hprog_done & Hr_t1)".
      (* load r r_t1 *) simpl in Hlength_prog.
      destruct a;[inversion Hlength_prog|].
      iPrologue "Hprog".
      iAssert (⌜(a_l' =? f0)%a = false⌝)%I as %Hfalse.
      { destruct (decide (a_l' = f0)%Z); [subst|iPureIntro;apply Z.eqb_neq,finz_neq_to_z;auto].
        iDestruct (mapsto_valid_2 with "Hi Ha_l") as %[? _]. done. }
      iApply (wp_load_success with "[$HPC $Hi Ha_l $Hr $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|split;auto|iContiguous_next Hcont 1|..].
      { revert Hwb Hsize. rewrite !andb_true_iff !Z.leb_le !Z.ltb_lt /finz.dist. clear -Ha_l'.
        intros [?|Hcontr];[solve_addr|]. subst. assert (e_l ≠ a_l') as Hne;[solve_addr|]. solve_addr. }
      { rewrite Hfalse. iFrame. } rewrite Hfalse.
      iEpilogue "(HPC & Hi & Hr & Hr_t1 & Ha_l)".
      apply rev_cons_inv in Hreveq as Hl''. destruct Hl'' as [l'' Hl''].
      iApply ("IH" $! a_l' (delete r mlocals) (l'') (wsr' ++ [w]) with "[] [] [] [] [] [] [] [] Hprog HPC Hr_t1 Hlocals [Hbl]").
      + iPureIntro. rewrite Hl'' in Hreveq. rewrite rev_unit in Hreveq. inversion Hreveq. auto.
      + iPureIntro. eapply isCorrectPC_range_restrict;[eauto|].
        assert (a_first + 1 = Some f0)%a;[iContiguous_next Hcont 0|].
        assert (f0 + 1 = Some f)%a;[iContiguous_next Hcont 1|].
        split;[revert H H0;clear|clear];solve_addr.
      + iPureIntro.
        assert (a_first + 1 = Some f0)%a;[iContiguous_next Hcont 0|].
        assert (f0 + 1 = Some f)%a;[iContiguous_next Hcont 1|].
        inversion Hcont;simplify_eq.
        inversion H6;simplify_eq. auto.
      + iPureIntro;simpl. lia.
      + iPureIntro. simpl in *.
        revert Hsize Ha_l'. rewrite /finz.dist. clear. solve_addr.
      + iPureIntro. simpl in *.
        revert Hsize Ha_l' Hwb. rewrite /finz.dist. clear. intros.
        destruct Hwb.
        ++ left.
           apply andb_true_intro.
           apply andb_prop in H. revert H. rewrite !Z.leb_le !Z.ltb_lt.
           intros.
           split; try solve_addr.
        ++ subst. left.
           apply andb_true_intro.
           rewrite !Z.leb_le !Z.ltb_lt.
           intros.
           split; try solve_addr.
      + iPureIntro. rewrite (stdpp_extra.map_to_list_delete _ _ w0);eauto.
        rewrite Hl'' rev_unit in Hreveq. inversion Hreveq.
        apply rev_cons_inv in H0 as [l3 Hl3]. rewrite Hl3. simplify_eq.
        rewrite -Hperm. rewrite - !app_assoc.
        assert (length l3 = length wsr') as Hlen.
        { clear -Hlength Hreveq. rewrite rev_unit in Hreveq. inversion Hreveq. simpl in *.
          rewrite -rev_length H0. rewrite app_length /= in Hlength. lia. }
        rewrite !zip_app;auto. rewrite app_assoc. assert (zip [r] [w0] = [(r,w0)]) as ->. auto.
        rewrite Permutation_cons_append. auto.
        rewrite fst_zip Permutation_cons_append. rewrite -Hl''.
        assert (locals = (zip locals wsr).*1) as ->;[rewrite fst_zip;auto|].
        { rewrite -rev_length Hreveq. rewrite Hlength. clear;lia. }
        rewrite Hperm. apply NoDup_map_to_list_fst. apply _.
        rewrite app_nil_l app_length /=. rewrite -Hreveq rev_length Hl'' Hwsr' !app_length /= in Hlength.
        clear -Hlength. lia.
      + rewrite Hl'' rev_unit in Hreveq. inversion Hreveq. rewrite rev_length.
        apply rev_cons_inv in H0 as [l3 Hl3]. rewrite Hl3. simplify_eq.
        rewrite rev_unit in Hreveq. inversion Hreveq. simplify_eq.
        rewrite !app_length /= rev_length in Hlength.
        rewrite !app_length /=. iPureIntro. clear -Hlength. lia.
      + auto.
      + iNext. iIntros "(HPC & Hr_t1 & Hlocals & Hbl & Hprog)".
        iApply "Hcont". iFrame. iSplit;[|done].
        iApply (big_sepM_delete);[|iFrame]. apply elem_of_map_to_list. rewrite -Hperm.
        rewrite Hl'' rev_unit in Hreveq. inversion Hreveq.
        apply rev_cons_inv in H0 as [l3 Hl3]. rewrite Hl3 in Hl''.
        rewrite Hl'' Hwsr'. rewrite app_assoc.
        rewrite zip_app. apply elem_of_app. right. constructor.
        rewrite !app_length /=. simplify_eq.
        rewrite -Hreveq /= rev_unit /= !app_length /= rev_length in Hlength. clear -Hlength. lia.
  Qed.


  Lemma restore_locals_spec
        (* cont *) φ
        (* list of locals *) r1 mlocals locals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    finz.dist b_l e_l = strings.length locals →
    strings.length locals > 0 → (* we assume the length of locals is non zero, or we would not be able to take a step before invoking continuation *)
    readAllowed p_l = true →
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length locals = length wsr ->

    (▷ restore_locals a r1 (rev locals)
   ∗ ▷ PC ↦ᵣ WCap p b e a_first
   ∗ ▷ r1 ↦ᵣ WCap p_l b_l e_l e_l
   ∗ ▷ ([∗ map] r↦_ ∈ mlocals, ∃ w, r ↦ᵣ w)
   ∗ ▷ ([[b_l,e_l]]↦ₐ[[wsr]])
   ∗ ▷ (PC ↦ᵣ WCap p b e a_last
           ∗ r1 ↦ᵣ WCap p_l b_l e_l b_l
           ∗ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
           ∗ [[b_l,e_l]]↦ₐ[[wsr]]
           ∗ restore_locals a r1 (rev locals)
           -∗ WP Seq (Instr Executable) {{ φ }})

   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa Hperm Hlen) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)".
    iApply (restore_locals_spec_middle with "[$HPC $Hprog $Hr_t1 $Hlocals $Hbl $Hcont]"); eauto; rewrite rev_length;auto.
  Qed.

  Lemma restore_locals_spec_middle_int
        (* list of locals *) r1 locals revlocals
        (* PC *) a p b e a_first a_last
        (* capability for locals *) z :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    strings.length revlocals > 0 →
    rev locals = revlocals ->

    (▷ restore_locals a r1 revlocals
       ∗ ▷ PC ↦ᵣ WCap p b e a_first
       ∗ ▷ r1 ↦ᵣ WInt z
   ⊢ WP Seq (Instr Executable) {{ λ v, ⌜v = FailedV⌝ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hnz Hreveq) "(>Hprog & >HPC & Hr1)".
    iInduction (revlocals) as [|r revlocals] "IH" forall (a a_first Hreveq Hvpc Hcont Hnz).
    { apply rev_nil_inv in Hreveq as ->. inversion Hnz. }
    destruct revlocals as [|r' revlocals].
    - apply rev_singleton_inv in Hreveq as ->.
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      (* lea r_t1 -1 *)
      destruct_list a.
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
      iPrologue "Hprog".
      iApply (wp_Lea_fail_int_inl with "[$HPC $Hi $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iEpilogue "_". by proofmode.wp_end.
    - iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      simpl in Hlength_prog.
      destruct a;[inversion Hlength_prog|].
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
      iPrologue "Hprog".
      iApply (wp_Lea_fail_int_inl with "[$HPC $Hi $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iEpilogue "_". by proofmode.wp_end.
  Qed.


  Lemma restore_locals_spec_int
        (* list of locals *) r1 mlocals locals (wsr : list Word)
        (* PC *) a p b e a_first a_last
        (* locals integer *) z :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    strings.length locals > 0 → (* we assume the length of locals is non zero, or we would not be able to take a step before invoking continuation *)
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length locals = length wsr ->

    (▷ restore_locals a r1 (rev locals)
       ∗ ▷ PC ↦ᵣ WCap p b e a_first
       ∗ ▷ r1 ↦ᵣ WInt z
   ⊢ WP Seq (Instr Executable) {{ λ v, ⌜v = FailedV⌝ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hlen) "(>Hprog & >HPC& >Hr_t1& Hcont)".
    iApply (restore_locals_spec_middle_int with "[$HPC $Hprog $Hr_t1 Hcont]"); eauto; rewrite rev_length;auto.
  Qed.

End callback.