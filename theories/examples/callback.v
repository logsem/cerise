From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers macros call.

Lemma rev_nil_inv {A} (l : list A) :
  rev l = [] -> l = [].
Proof.
  destruct l;auto.
  simpl. intros Hrev. exfalso.
  apply app_eq_nil in Hrev as [Hrev1 Hrev2].
  inversion Hrev2.
Qed.

Lemma rev_singleton_inv {A} (l : list A) (a : A) :
  rev l = [a] -> l = [a].
Proof.
  destruct l;auto.
  simpl. intros Hrev.
  destruct l. 
  - simpl in Hrev. inversion Hrev. auto. 
  - exfalso. simpl in Hrev. 
    apply app_singleton in Hrev. destruct Hrev as [ [Hrev1 Hrev2] | [Hrev1 Hrev2] ].
    + destruct (rev l);inversion Hrev1. 
    + inversion Hrev2.
Qed.

Lemma rev_lookup {A} (l : list A) (a : A) :
  rev l !! 0 = Some a <-> l !! (length l - 1) = Some a.
Proof.
  split; intros Hl.
  - rewrite -last_lookup.
    induction l.
    + inversion Hl.
    + simpl in Hl. simpl. destruct l.
      { simpl in Hl. inversion Hl. auto. }
      { apply IHl. rewrite lookup_app_l in Hl;[|simpl;rewrite app_length /=;lia]. auto. }
  - rewrite -last_lookup in Hl.
    induction l.
    + inversion Hl.
    + simpl. destruct l.
      { simpl. inversion Hl. auto. }
      { rewrite lookup_app_l;[|simpl;rewrite app_length /=;lia]. apply IHl. auto. }
Qed.

Lemma rev_cons_inv {A} (l l' : list A) (a : A) :
  rev l = a :: l' ->
  ∃ l'', l = l'' ++ [a].
Proof.
  intros Hrel.
  destruct l;inversion Hrel.
  assert ((a0 :: l) !! (length l) = Some a) as Hsome.
  { assert (length l = length (a0 :: l) - 1) as ->;[simpl;lia|]. apply rev_lookup. rewrite Hrel. constructor. }
  apply take_S_r in Hsome.
  exists (take (length l) (rev (rev l ++ [a0]))).
    simpl. rewrite rev_unit. rewrite rev_involutive. rewrite -Hsome /=. 
    f_equiv. rewrite firstn_all. auto.
Qed.     

Section callback.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
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
    region_size b_l a_l = strings.length revlocals →
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
    { apply rev_nil_inv in Hreveq as ->. apply Permutation.Permutation_nil in Hperm. inversion Hnz. }
    destruct revlocals as [|r' revlocals]. 
    - apply rev_singleton_inv in Hreveq as ->. destruct wsr;[inversion Hlength|]. destruct wsr;[|inversion Hlength]. 
      apply Permutation_sym, Permutation_singleton in Hperm. 
      assert (mlocals = {[r:=w]}) as Heq;[|subst mlocals]. 
      { apply map_to_list_inj. rewrite map_to_list_singleton. apply Permutation_singleton. auto. }
      rewrite big_sepM_singleton. 
      rewrite /restore_locals /restore_locals_instrs.
      iDestruct (big_sepL2_length with "Hbl") as %Hlength_bl.
      rewrite region_addrs_length Hsize in Hlength_bl.
      assert (region_addrs b_l a_l = [b_l]) as Heq_locals;[ by rewrite /region_addrs Hsize /=|]. 
      rewrite /region_mapsto Heq_locals.
      iDestruct "Hbl" as "[Ha_l _]".
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      (* lea r_t1 -1 *)
      destruct_list a.
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->. 
      assert (a_l + (-1) = Some b_l)%a as Hnext.
      { rewrite /region_size /= in Hsize. revert Hsize;clear;solve_addr. }
      iPrologue "Hprog". 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|apply Hnext|destruct p_l;auto;inversion Hwa|].
      iEpilogue "(HPC & Hprog_done & Hr_t1)". 
      (* load r r_t1 *)
      pose proof (contiguous_between_last _ _ _ a Hcont eq_refl) as Hlast.
      iPrologue "Hprog".
      iDestruct "Hlocals" as (w0) "Hlocals".
      iAssert (⌜(b_l =? a)%a = false⌝)%I as %Hfalse.
      { destruct (decide (b_l = a)%Z); [subst|iPureIntro;apply Z.eqb_neq,neq_z_of;auto].
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
      { rewrite /region_size /= in Hsize. destruct (a_l + -1)%a eqn:Hnone;eauto.
        simpl in Hsize. revert Hnone Hsize;clear;solve_addr. }
      assert (region_addrs b_l a_l = region_addrs b_l a_l' ++ [a_l']) as Heq.
      { rewrite (region_addrs_split _ a_l').
        assert (region_addrs a_l' a_l = [a_l']) as ->;auto.
        apply region_addrs_single. clear -Ha_l';solve_addr.
        rewrite /region_size in Hsize. 
        clear -Ha_l' Hsize Hwb. solve_addr. }
      rewrite /region_mapsto Heq.
      iDestruct "Hr" as (w') "Hr".
      iDestruct (big_sepL2_length with "Hbl") as %Hlengthbl.
      rewrite Hwsr'. 
      rewrite app_assoc. 
      iDestruct (big_sepL2_app' _ _ _ _ (region_addrs b_l a_l') _ (wsr' ++ [w]) with "Hbl") as "[Hbl Ha_l]".
      { rewrite Hwsr' in Hlengthbl. rewrite app_length /= app_length /= in Hlengthbl.
        clear -Hlengthbl. rewrite app_length /=. lia. }
      iDestruct "Ha_l" as "[Ha_l _]".
      (* lea r_t1 -1 *)
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      simpl in Hlength_prog. 
      destruct a;[inversion Hlength_prog|].
      destruct a0;[inversion Hlength_prog|]. 
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
      iPrologue "Hprog". 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|apply Ha_l'|destruct p_l;auto;inversion Hwa|].
      iEpilogue "(HPC & Hprog_done & Hr_t1)". 
      (* load r r_t1 *) simpl in Hlength_prog. 
      destruct a1;[inversion Hlength_prog|]. 
      iPrologue "Hprog". 
      iAssert (⌜(a_l' =? a0)%a = false⌝)%I as %Hfalse.
      { destruct (decide (a_l' = a0)%Z); [subst|iPureIntro;apply Z.eqb_neq,neq_z_of;auto].
        iDestruct (mapsto_valid_2 with "Hi Ha_l") as %[? _]. done. }
      iApply (wp_load_success with "[$HPC $Hi Ha_l $Hr $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|split;auto|iContiguous_next Hcont 1|..].
      { revert Hwb Hsize. rewrite !andb_true_iff !Z.leb_le !Z.ltb_lt /region_size. clear -Ha_l'.
        intros [?|Hcontr];[solve_addr|]. subst. assert (e_l ≠ a_l') as Hne;[solve_addr|]. solve_addr. }
      { rewrite Hfalse. iFrame. } rewrite Hfalse. 
      iEpilogue "(HPC & Hi & Hr & Hr_t1 & Ha_l)".     
      apply rev_cons_inv in Hreveq as Hl''. destruct Hl'' as [l'' Hl'']. 
      iApply ("IH" $! a_l' (delete r mlocals) (l'') (wsr' ++ [w]) with "[] [] [] [] [] [] [] [] Hprog HPC Hr_t1 Hlocals [Hbl]").
      + iPureIntro. rewrite Hl'' in Hreveq. rewrite rev_unit in Hreveq. inversion Hreveq. auto. 
      + iPureIntro. eapply isCorrectPC_range_restrict;[eauto|].
        assert (a_first + 1 = Some a0)%a;[iContiguous_next Hcont 0|].
        assert (a0 + 1 = Some a)%a;[iContiguous_next Hcont 1|].
        split;[revert H H0;clear|clear];solve_addr.
      + iPureIntro.
        assert (a_first + 1 = Some a0)%a;[iContiguous_next Hcont 0|].
        assert (a0 + 1 = Some a)%a;[iContiguous_next Hcont 1|].
        inversion Hcont;simplify_eq.
        inversion H6;simplify_eq. auto.
      + iPureIntro;simpl. lia.
      + iPureIntro. simpl in *.
        revert Hsize Ha_l'. rewrite /region_size. clear. solve_addr.
      + iPureIntro. simpl in *.
        revert Hsize Ha_l' Hwb. rewrite /region_size. clear. intros.
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
      + iPureIntro. rewrite (map_to_list_delete _ _ w0);eauto.
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
    region_size b_l e_l = strings.length locals →
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

  Lemma scall_epilogue_spec rt1w rt2w 
        (* reinstated PC *) pc_p pc_b pc_e a_last a_end
        (* activation frame *) b_c e_c
        (* locals *) b_l e_l
        (* current PC *) p φ :

    isCorrectPC_range p b_c e_c b_c e_c →
    (a_end + 1)%a = Some a_last ->

    (▷ PC ↦ᵣ WCap p b_c e_c b_c
       ∗ ▷ r_t1 ↦ᵣ rt1w
       ∗ ▷ r_t2 ↦ᵣ rt2w
       ∗ ▷ ([[b_c,e_c]]↦ₐ[[ [WInt hw_1;WInt hw_2;WInt hw_3;WInt hw_4;WInt hw_5;WCap RWX b_l e_l e_l;WCap pc_p pc_b pc_e a_end] ]]) (* activation frame *)
       ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e a_last
               ∗ (∃ rt1w, r_t1 ↦ᵣ rt1w)
               ∗ r_t2 ↦ᵣ WCap RWX b_l e_l e_l
               ∗ ([[b_c,e_c]]↦ₐ[[ [WInt hw_1;WInt hw_2;WInt hw_3;WInt hw_4;WInt hw_5;WCap RWX b_l e_l e_l;WCap pc_p pc_b pc_e a_end] ]]) (* activation frame *) -∗
               WP Seq (Instr Executable) {{ φ }})
       ⊢ WP Seq (Instr Executable) {{ φ }})%I. 
  Proof.
    iIntros (Hvpc Hcontinuation) "(>HPC & >Hr_t1 & >Hr_t2 & >Hprog & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlen.
    rewrite /= region_addrs_length in Hlen. 
    assert (b_c <= e_c)%a as Hle.
    { clear -Hlen. rewrite /region_size in Hlen; solve_addr. }
    specialize (contiguous_between_region_addrs b_c e_c Hle) as Hcont. 
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    rewrite /region_mapsto. 
    destruct (region_addrs b_c e_c);[inversion Hlength|]. 
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a. 
    (* move r_t1 PC *)
    simpl in Hlength. inversion Hlength. destruct_list l. 
    iPrologue "Hprog". 
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC b_c e_c|iContiguous_next Hcont 0|]. 
    iEpilogue "(HPC & Ha1 & Hr_t1)". 
    (* lea r_t1 5 *)
    assert (b_c + 5 = Some a3)%a as Hlea.
    { apply contiguous_between_incr_addr_middle with (i:=0) (j:=5) (ai:=b_c) (aj:=a3) in Hcont;auto. }
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC b_c e_c|iContiguous_next Hcont 1|apply Hlea|..].
    { eapply isCorrectPC_range_perm_non_E;eauto. rewrite /region_size in Hlen. solve_addr. }
    iEpilogue "(HPC & Ha2 & Hr_t1)". 
    (* load r_t2 r_t1 *)
    iDestruct "Hprog" as "(Ha3 & Ha4 & Ha5 & Ha6 & Ha7 & _)". 
    iApply (wp_bind (fill [SeqCtx])).
    iAssert (⌜(a3 =? a0)%a = false⌝)%I as %Hfalse.
    { destruct (decide (a3 = a0)%Z); [subst|iPureIntro;apply Z.eqb_neq,neq_z_of;auto].
      iDestruct (mapsto_valid_2 with "Ha3 Ha6") as %[? _]. done. }
    iApply (wp_load_success with "[$HPC $Ha3 $Hr_t2 $Hr_t1 Ha6]");
      [apply decode_encode_instrW_inv|iCorrectPC b_c e_c| |iContiguous_next Hcont 2|..].
    { apply andb_true_iff, Is_true_eq_true. apply isCorrectPC_ra_wb. iCorrectPC b_c e_c. }
    { rewrite Hfalse. iFrame. }
    rewrite Hfalse. iEpilogue "(HPC & Hr_t2 & Ha3 & Hr_t1 & Ha6)". 
    (* lea r_t1 1 *)
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z with "[$HPC $Ha4 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC b_c e_c|iContiguous_next Hcont 3|iContiguous_next Hcont 5|..].
    { eapply isCorrectPC_range_perm_non_E;eauto. rewrite /region_size in Hlen. solve_addr. }
    iEpilogue "(HPC & Ha4 & Hr_t1)". 
    (* load PC r_t1 *)
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_load_success_PC with "[$HPC $Ha5 $Hr_t1 $Ha7]");
      [apply decode_encode_instrW_inv|iCorrectPC b_c e_c| |apply Hcontinuation|..].
    { apply andb_true_iff, Is_true_eq_true. apply isCorrectPC_ra_wb. iCorrectPC b_c e_c. }
    iEpilogue "(HPC & Ha5 & Hr_t1 & Ha7)". 
    (* Hφ *)
    iApply "Hφ". 
    iFrame. iSplitL;eauto. 
  Qed. 

End callback.
