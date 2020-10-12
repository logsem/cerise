From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers macros fundamental call callback.

Lemma map_to_list_delete_fst {A B} `{Countable A} (m : gmap A B) (i : A) (x : B) :
  ∀ l, i :: l ≡ₚ(map_to_list m).*1 ->
       NoDup (i :: l) →
       (map_to_list (delete i m)).*1 ≡ₚl.
Proof.
  intros l Hl Hdup.
  assert (i ∈ (map_to_list m).*1) as Hin.
  { rewrite -Hl. constructor. }
  apply NoDup_cons_iff in Hdup as [Hnin Hdup]. 
  apply Permutation.NoDup_Permutation;auto. 
  apply NoDup_map_to_list_fst. done.
  set l' := zip l (repeat x (length l)).
  assert (l = l'.*1) as Heq;[rewrite fst_zip;auto;rewrite repeat_length;lia|]. 
  intros i0. split.
  - intros Hinx%elem_of_list_In%elem_of_list_fmap.
    destruct Hinx as [ [? ?] [? Hinx] ]. simpl in *. subst a.
    apply elem_of_map_to_list in Hinx.
    destruct (decide (i = i0));[subst i;rewrite lookup_delete in Hinx;inversion Hinx|].
    rewrite lookup_delete_ne in Hinx;auto.
    apply elem_of_map_to_list in Hinx.
    assert (i0 ∈ (map_to_list m).*1) as Hinx'.
    { apply elem_of_list_fmap. exists (i0,b). split;auto. }
    revert Hinx'. rewrite -Hl =>Hinx'. apply elem_of_cons in Hinx' as [Hcontr | Hinx'];[congruence|].
    apply elem_of_list_In;auto. 
  - intros Hinx%elem_of_list_In.
    apply elem_of_list_In. revert Hnin; rewrite -elem_of_list_In => Hnin. 
    assert (i ≠ i0) as Hne;[congruence|simplify_map_eq].
    assert (i0 ∈ i :: l) as Hin'.
    { constructor. auto. }
    revert Hin'. rewrite Hl =>Hin'.
    apply map_to_list_fst in Hin' as [x' Hx].
    apply elem_of_map_to_list in Hx.
    apply map_to_list_fst. exists x'. apply elem_of_map_to_list.
    rewrite lookup_delete_ne;auto. 
Qed.

Lemma big_sepM_to_create_gmap_default {Σ : gFunctors} {A B : Type} `{Countable A} (m m' : gmap A B) (φ : A -> B -> iProp Σ) (b : B) (l : list A) :
  l ≡ₚ(map_to_list m).*1 →
  m' = create_gmap_default l b →
  ([∗ map] a↦_ ∈ m, φ a b) -∗ ([∗ map] a↦b' ∈ m', φ a b').
Proof.
  iIntros (Hl Hm) "Hm".
  iInduction l as [|a l] "IH" forall (m m' Hl Hm). 
  - simpl in Hm. rewrite Hm. done. 
  - assert (NoDup (a :: l)) as Hdup.
    { rewrite Hl. apply NoDup_map_to_list_fst. done. }
    assert (a ∈ (map_to_list m).*1) as Hin'.
    { rewrite -Hl. constructor. }
    assert (is_Some(m !! a)) as [b' Hsome].
    { apply elem_of_gmap_dom. rewrite -list_to_set_map_to_list. apply elem_of_list_to_set. auto. }
    iDestruct (big_sepM_delete _ _ a with "Hm") as "[Ha Hm]";eauto.
    iApply big_sepM_delete;[|iFrame].
    { rewrite Hm.  apply lookup_insert. }
    rewrite Hm /= delete_insert_delete.
    iApply ("IH" $! (delete a m));[..|iFrame]. 
    + iPureIntro. rewrite map_to_list_delete_fst;eauto. 
    + iPureIntro. rewrite delete_notin;auto.
      destruct (create_gmap_default l b !! a) eqn:Hsome';auto. 
      exfalso. apply NoDup_cons_iff in Hdup as [Hnin Hdup].
      apply Hnin. apply elem_of_list_In.
      apply create_gmap_default_lookup_is_Some in Hsome' as [Hin Hsome']. subst.
      auto. 
Qed. 
    
    
Section roe.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Ltac iPrologue prog :=
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  (* ----------------------------------------------------------------------------- *)
  Definition ro := encodePerm RO.
  Definition roe_instrs f_m f_a r1 :=
    malloc_instrs f_m 1%nat ++
    [move_r r_env r_t1;
    move_r r_t7 r_t1;
    store_z r_env 1; 
    restrict_z r_t7 ro] ++
    call_instrs f_m (offset_to_cont_call [r_t7]) r1 [r_env] [r_t7] ++
    restore_locals_instrs r_t2 [r_env] ++
    [load_r r_t0 r_env] ++
    assert_r_z_instrs f_a r_t0 1 ++
    [halt].

  Definition roe a f_m f_a r1 :=
    ([∗ list] a_i;w ∈ a;(roe_instrs f_m f_a r1), a_i ↦ₐ w)%I.

  Definition roe_inv d : iProp Σ :=
    (∃ w, d ↦ₐ w ∗ ⌜w = inl 1%Z⌝)%I.

  Definition roeN : namespace := nroot .@ "roeN".
  Definition roeN_link : namespace := roeN .@ "link".
  Definition roeN_flag : namespace := roeN .@ "flag".
  Definition roeN_act : namespace := roeN .@ "act".
  Definition roeN_locals : namespace := roeN .@ "locals".
  Definition roeN_b : namespace := roeN .@ "locals".
  Definition roeN_prog : namespace := roeN .@ "prog".

  Definition r_adv := r_t31.
  
  Lemma roe_spec pc_p pc_b pc_e (* PC *)
        roe_addrs wadv (* program addresses *)
        b_m e_m f_m mallocN (* malloc *)
        b_link e_link a_link f_a a_entry a_entry' (* link *)
        fail_start fail_end a_env (* fail *)
        flag_p flag_b flag_e flag_a (* flag *)
        a_first a_last (* special adresses *)
        rmap (* registers *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between roe_addrs a_first a_last ->

    (* Assumptions about linking table *)
    withinBounds (RW, b_link, e_link, a_entry) = true →
    withinBounds (RW, b_link, e_link, a_entry') = true →
    (a_link + f_m)%a = Some a_entry →
    (a_link + f_a)%a = Some a_entry' →
    (fail_start + strings.length (assert_fail_instrs))%a = Some a_env →
    
    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_adv]} →
    
    {{{ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
      ∗ r_adv ↦ᵣ wadv
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ roe roe_addrs f_m f_a r_adv
      (* untrusted code *)
      ∗ interp wadv
      
      (** Resources for malloc and assert **)
      (* assume that a pointer to the linking table (where the malloc capa is) is at offset 0 of PC *)
      ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
      ∗ pc_b ↦ₐ (inr (RO, b_link, e_link, a_link))
      ∗ a_entry ↦ₐ (inr (E, b_m, e_m, b_m))
      ∗ a_entry' ↦ₐ (inr (E, fail_start, fail_end, fail_start))
      ∗ a_env ↦ₐ inr (flag_p, flag_b, flag_e, flag_a)
      (* invariant about the failure flag *)
      ∗ (inv roeN_flag (flag_a ↦ₐ inl 0%Z))
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; True }}}. (* in this spec, we do not care about the postcondition, 
                              only that the flag invariant holds throughout the program, 
                              and that the program does not get stuck *)
  Proof.
    iIntros (Hvpc Hcont Hwb1 Hwb2 Ha_entry Ha_entry' Ha_env Hdom φ) 
            "(HPC & Hr_adv & Hregs & Hown & Hprog & #Hwadv & #Hmalloc & Hpc_b & Ha_entry & Ha_entry' & Ha_env & #Hflag) Hφ". 
    (* extract r_t0 *)
    assert (is_Some (rmap !! r_t0)) as [w0 Hw0].
    { apply elem_of_gmap_dom. rewrite Hdom. clear;set_solver. }
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t0 Hregs]";[apply Hw0|]. 
    (* put back r_adv *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_adv]") as "Hregs". 
    { rewrite lookup_delete_ne;auto. apply elem_of_gmap_dom_none. rewrite Hdom. clear;set_solver. }

    (* prepare the program addresses for malloc *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_malloc ai_rest a_malloc_end) "(Hmalloc_prog & Hprog & #Hcont)"; [apply Hcont|].
    iDestruct "Hcont" as %(Hcont_malloc & Hcont_rest & Heqapp & Hlink).
    iDestruct (big_sepL2_length with "Hmalloc_prog") as %Hai_malloc_len.
    assert (isCorrectPC_range pc_p pc_b pc_e a_first a_malloc_end) as Hvpc1.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest). clear; solve_addr. }
    assert (isCorrectPC_range pc_p pc_b pc_e a_malloc_end a_last) as Hvpc2.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_malloc). clear; solve_addr. }
    rewrite -/(malloc _ _ _ _).
    (* apply the malloc spec *)
    iApply (malloc_spec_alt with "[- $Hφ $HPC $Hmalloc_prog $Hpc_b $Ha_entry $Hr_t0 $Hregs $Hmalloc $Hown]");
      [apply Hvpc1|eapply Hcont_malloc|eapply Hwb1|eapply Ha_entry| |auto|lia|..].
    { rewrite !dom_insert_L !dom_delete_L Hdom !difference_difference_L. clear. set_solver. }
    iSplitR;[iNext;auto|]. 
    iNext. iIntros "(HPC & Hmalloc_prog & Hpc_b & Ha_entry & Hbe & Hr_t0 & Hown & Hregs)".
    iDestruct "Hbe" as (b e Hincr) "(Hr_t1 & Hbe)". 
    iDestruct (region_mapsto_single with "Hbe") as (cellv) "(Hbe & _)". revert Hincr; clear; solve_addr.

    (* extract r_env and r_t7 *)
    assert (is_Some (rmap !! r_env)) as [wenv Hwenv].
    { apply elem_of_gmap_dom. rewrite Hdom. clear;set_solver. }
    iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]";[rewrite !lookup_insert_ne// lookup_delete_ne//
                                                                                    !lookup_insert_ne// lookup_delete_ne//|].
    assert (is_Some (rmap !! r_t7)) as [w7 Hw7].
    { apply elem_of_gmap_dom. rewrite Hdom. clear;set_solver. }
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]";[rewrite lookup_delete_ne// !lookup_insert_ne// lookup_delete_ne//
                                                                                    !lookup_insert_ne// lookup_delete_ne//|].
    (* continue *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    destruct ai_rest as [|? ai_rest];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq; subst a. 
    (* move r_env r_t1 *)
    destruct ai_rest as [|? ai_rest];[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_env $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_last|iContiguous_next Hcont_rest 0|]. 
    iEpilogue "(HPC & Hi & Hr_env & Hr_t1)". iCombine "Hi" "Hmalloc_prog" as "Hprog_done".
    (* move r_t7 r_t1 *)
    destruct ai_rest as [|? ai_rest];[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t7 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_last|iContiguous_next Hcont_rest 1|]. 
    iEpilogue "(HPC & Hi & Hr_t7 & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_env 1 *)
    destruct ai_rest as [|? ai_rest];[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_env $Hbe]");
      [apply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_last|iContiguous_next Hcont_rest 2|..].
    { split;auto. rewrite andb_true_iff Z.leb_le Z.ltb_lt. clear -Hincr. solve_addr. }
    iEpilogue "(HPC & Hi & Hr_env & Hbe)". iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* restrict r_t7 RO *)
    destruct ai_rest as [|? ai_rest];[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_restrict_success_z with "[$HPC $Hi $Hr_t7]");
      [apply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_last|iContiguous_next Hcont_rest 3|auto..].
    { rewrite decode_encode_perm_inv. auto. }
    iEpilogue "(HPC & Hi & Hr_t7)". iCombine "Hi" "Hprog_done" as "Hprog_done". 

    (* prepare the program addresses for call *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_call ai_rest' a_call_end) "(Hcall_prog & Hprog & #Hcont)".
    { repeat (apply contiguous_between_cons_inv in Hcont_rest as [_ [? [_ Hcont_rest] ] ];
        apply contiguous_between_cons_inv_first in Hcont_rest as Heq'; subst x). apply Hcont_rest. }
    iDestruct "Hcont" as %(Hcont_call & Hcont_rest' & Heqapp' & Hlink').
    iDestruct (big_sepL2_length with "Hcall_prog") as %Hai_call_len.
    assert (isCorrectPC_range pc_p pc_b pc_e a2 a_call_end) as Hvpc3.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest').
      generalize (contiguous_between_bounds _ _ _ Hcont_malloc).
      apply contiguous_between_middle_bounds' with (ai:=a2) in Hcont_rest;[|repeat constructor].
      clear -Hcont_rest; solve_addr. }
    assert (isCorrectPC_range pc_p pc_b pc_e a_call_end a_last) as Hvpc4.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_call).
      generalize (contiguous_between_bounds _ _ _ Hcont_malloc).
      apply contiguous_between_middle_bounds' with (ai:=a2) in Hcont_rest;[|repeat constructor]. 
      clear -Hcont_rest; solve_addr. }
    (* prepare the registers *)
    iDestruct (big_sepM_delete _ _ r_adv with "Hregs") as "[Hr_adv Hregs]";[rewrite !lookup_delete_ne// !lookup_insert_ne//
                                                                                    lookup_delete_ne//; apply lookup_insert|].
    rewrite (delete_insert_ne _ _ r_adv)// !(insert_commute _ _ r_adv)// (delete_insert_ne _ _ r_adv)// (delete_insert_ne _ _ r_adv)// delete_insert.
    2: { rewrite !lookup_delete_ne// !lookup_insert_ne// !lookup_delete_ne//. apply elem_of_gmap_dom_none. rewrite Hdom. clear; set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[rewrite !lookup_delete_ne// !lookup_insert_ne//; apply lookup_delete|].
    rewrite -!(delete_insert_ne _ r_t1)// 2!(delete_commute _ _ r_t1)// insert_delete. 
    (* apply the call spec *)
    iApply (wp_wand _ _ _ (λ v0 : language.val cap_lang, True ∨ ⌜v0 = FailedV⌝)%I with "[-]");[|auto].
    rewrite -/(call _ _ _ _). 
    iApply (call_spec r_adv {[r_env:=inr (RWX, b, e, b)]} {[r_t7:=inr (decodePerm ro, b, e, b)]} _
                      _ (delete r_t7 (delete r_t0 rmap))
              with "[- $HPC $Hown $Hmalloc $Hpc_b $Ha_entry $Hr_adv $Hregs]");
      [apply Hvpc3|apply Hcont_call|auto|apply Ha_entry|..|solve_ndisj|]. 
    { rewrite map_to_list_singleton. auto. }
    { rewrite !dom_singleton_L dom_insert_L !dom_delete_L !dom_insert_L !dom_delete_L Hdom. clear.
      rewrite !union_assoc_L !difference_difference_L !union_assoc_L union_comm_L (union_comm_L {[r_t2; r_t3; r_t4; r_t5]}).
      rewrite difference_union_distr_l_L. set_solver. }
    { rewrite dom_singleton_L !dom_delete_L Hdom. clear. set_solver. }
    { rewrite !dom_insert_L !dom_delete_L !dom_insert_L dom_delete_L !union_assoc_L Hdom !difference_difference_L. clear. 
      rewrite -!(union_assoc_L {[r_t1]}). apply union_mono_l. apply subseteq_difference_r;[set_solver|].
      apply union_mono_l. apply subseteq_difference_r;[set_solver|]. apply all_registers_subseteq. }
    rewrite !map_to_list_singleton. iSimpl. rewrite /call. iFrame "Hcall_prog". 
    iSplitL "Hr_t7". iNext. iApply big_sepM_singleton. iFrame.  
    iSplitL "Hr_t0". iNext. eauto.
    iSplitL "Hr_env". iNext. iApply big_sepM_singleton. iFrame.
    (* in anticipation of the result of the call macro, we create the callback now *)
    iDestruct (jmp_or_fail_spec with "Hwadv") as "Hcallback_now".
    destruct (decide (isCorrectPC (updatePcPerm wadv))).
    2: { iNext. iIntros "Hbc". iDestruct "Hbc" as (b_c e_c b_l e_l a_end Hnext) "(HPC & _)". iApply "Hcallback_now". iFrame. }
    iDestruct "Hcallback_now" as (p b' e' a' ->) "Hcallback_now". 
    (* continue the program, now pointing at the adversary *)
    iNext. iIntros "Hbc".
    iDestruct "Hbc" as (b_c e_c b_l e_l a_end Hnext) "(HPC & Hregs & Hr_t7 & Hpc_b & Ha_entry & Hr_adv & Hr_t0 & Hbec & Hbel & Hcall_prog & Hown)".
    (* cleanup *)
    iDestruct (big_sepM_singleton (λ k i, k ↦ᵣ i)%I with "Hr_t7") as "Hr_t7".
    iCombine "Hcall_prog" "Hprog_done" as "Hprog_done". 

    (* we are now ready to call the unknown adversary *)
    (* we first need to prepare the invariants needed *)
    iMod (na_inv_alloc logrel_nais _ roeN_act with "Hbec") as "#Hbec". 
    iMod (na_inv_alloc logrel_nais _ roeN_locals with "Hbel") as "#Hbel".
    iCombine "Ha_entry' Ha_env Hpc_b Ha_entry" as "Hlink". 
    iMod (na_inv_alloc logrel_nais _ roeN_link with "Hlink") as "#Hlink". 
    iMod (inv_alloc (logN.@b) _ (roe_inv b) with "[Hbe]") as "#Hb". 
    { iNext. iExists _; iFrame. auto. }
    iMod (na_inv_alloc logrel_nais _ roeN_prog with "Hprog") as "#Hprog".
    iClear "Hprog_done".
    
    (* Let's assert that the continuation holds *)
    iDestruct (big_sepM_to_create_gmap_default _ _ (λ k i, k ↦ᵣ i)%I (inl 0%Z) with "Hregs")  as "Hregs";[apply Permutation_refl|reflexivity|]. 
    iDestruct (big_sepM_insert with "[$Hregs $Hr_adv]") as "Hregs".
    { apply elem_of_gmap_dom_none. rewrite create_gmap_default_dom list_to_set_map_to_list !dom_delete_L Hdom. clear. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs".
    { apply elem_of_gmap_dom_none. rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list !dom_delete_L Hdom. clear. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs".
    { apply elem_of_gmap_dom_none. rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list !dom_delete_L Hdom. clear. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
    { apply elem_of_gmap_dom_none. rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list !dom_delete_L Hdom. clear. set_solver. }
    
    match goal with |- context [ ([∗ map] k↦y ∈ ?regs, k ↦ᵣ y)%I ] =>
          set rmap2 := regs
    end.
    iSpecialize ("Hcallback_now" $! rmap2). rewrite /interp_expr. 
    iDestruct ("Hcallback_now" with "[Hregs $Hown]") as "[_ Hconf]". 
    { rewrite /registers_mapsto /rmap2. rewrite insert_insert. iFrame. 
      iSplit.
      { iPureIntro. intros x. simpl.
        consider_next_reg x PC. consider_next_reg x r_t0. consider_next_reg x r_t7. consider_next_reg x r_adv.
        apply elem_of_gmap_dom. rewrite create_gmap_default_dom list_to_set_map_to_list !dom_delete_L Hdom. clear -n n0 n1 n2.
        repeat (apply elem_of_difference; split; [|set_solver]). apply all_registers_s_correct. }
      iIntros (r Hne). 
      rewrite /RegLocate. rewrite lookup_insert_ne;auto. 
      consider_next_reg r r_t0;[|consider_next_reg r r_t7;[|consider_next_reg r r_adv] ].
      - (* continuation *) iClear "Hcallback_now Hwadv".
        rewrite !fixpoint_interp1_eq.
        iIntros (r). iNext. iAlways.
        iIntros "([% #Hreg_val] & Hreg & Hown)". iSplit;auto.
        rewrite /interp_conf.
        (* get the registers we need *)
        iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; [rewrite lookup_insert;eauto|].
        rewrite delete_insert_delete.
        assert (is_Some (r !! r_t1)) as [wrt1 Hwrt1];[auto|].
        iDestruct (big_sepM_delete _ _ r_t1 with "Hreg") as "[Hr_t1 Hreg]"; [rewrite lookup_delete_ne//;eauto|].
        assert (is_Some (r !! r_t2)) as [wrt2 Hwrt2];[auto|].
        iDestruct (big_sepM_delete _ _ r_t2 with "Hreg") as "[Hr_t2 Hreg]"; [rewrite !lookup_delete_ne//;eauto|].
        assert (is_Some (r !! r_env)) as [wenv' Hwenv'];[auto|].
        iDestruct (big_sepM_delete _ _ r_env with "Hreg") as "[Hr_env Hreg]"; [rewrite !lookup_delete_ne//;eauto|].
        assert (is_Some (r !! r_t0)) as [wrt0 Hwrt0];[auto|].
        iDestruct (big_sepM_delete _ _ r_t0 with "Hreg") as "[Hr_t0 Hreg]"; [rewrite !lookup_delete_ne//;eauto|].
        assert (is_Some (r !! r_t3)) as [wrt3 Hwrt3];[auto|].
        iDestruct (big_sepM_delete _ _ r_t3 with "Hreg") as "[Hr_t3 Hreg]"; [rewrite !lookup_delete_ne//;eauto|].

        (* step through the activation record *)
        iMod (na_inv_open with "Hprog Hown") as "[>Hprog' [Hown Hcls] ]";[solve_ndisj|solve_ndisj|].
        iDestruct (big_sepL2_length with "Hprog'") as %Hlength_rest'. 
        iMod (na_inv_open with "Hbec Hown") as "[Hbec' [Hown Hcls'] ]";[solve_ndisj|solve_ndisj|].
        iApply (scall_epilogue_spec with "[- $HPC $Hbec' $Hr_t1 $Hr_t2]");[|apply Hnext|]. 
        { split;auto. }
        iNext. iIntros "(HPC & Hr_t1 & Hr_t2 & Hbec')".
        iMod ("Hcls'" with "[$Hbec' $Hown]") as "Hown". 
        iDestruct "Hr_t1" as (wrt1') "Hr_t1".

        (* Since there is just one local register, it is easier to just step through rather than using the macro spec *)
        rewrite /restore_locals_instrs.
        destruct ai_rest';[inversion Hlength_rest'|]. apply contiguous_between_cons_inv_first in Hcont_rest' as Heq;subst a3.
        destruct ai_rest';[inversion Hlength_rest'|].
        iRename "Hprog" into "Hprog_inv".
        (* lea r_t2 -1 *)
        iPrologue "Hprog'".
        iMod (na_inv_open with "Hbel Hown") as "[>Hbel' [Hown Hcls'] ]";[solve_ndisj|solve_ndisj|].
        iDestruct (big_sepL2_length with "Hbel'") as %Hbl_length. 
        assert ((b_l + 1) = Some e_l)%a as Hbl_next. 
        { rewrite region_addrs_length /= /region_size in Hbl_length. clear -Hbl_length. solve_addr. }
        assert ((e_l + -1)%a = Some b_l) as Hlea.
        { clear -Hbl_next. solve_addr. }
        iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
          [apply decode_encode_instrW_inv|iCorrectPC a_call_end a_last|iContiguous_next Hcont_rest' 0|apply Hlea|auto|..]. 
        iEpilogue "(HPC & Hprog_done & Hr_t2)". 
        (* load r_env r_t2 *)
        apply region_addrs_single in Hbl_next.
        rewrite /region_mapsto Hbl_next.
        iDestruct "Hbel'" as "[Hbel' _]".
        destruct ai_rest';[inversion Hlength_rest'|].
        iPrologue "Hprog".
        iAssert (⌜(b_l =? a3)%a = false⌝)%I as %Hfalse.
        { destruct (decide (b_l = a3)%Z); [subst|iPureIntro;apply Z.eqb_neq,neq_z_of;auto].
          iDestruct (mapsto_valid_2 with "Hi Hbel'") as %?. done. }
        iApply (wp_load_success with "[$HPC $Hi $Hr_env $Hr_t2 Hbel']");
          [apply decode_encode_instrW_inv|iCorrectPC a_call_end a_last| |iContiguous_next Hcont_rest' 1|..]. 
        { split;auto. rewrite andb_true_iff Z.leb_le Z.ltb_lt. clear -Hlea. solve_addr. }
        { rewrite Hfalse. iFrame. }
        rewrite Hfalse. iEpilogue "(HPC & Hr_env & Hi & Hr_t2 & Hb_l)". iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* load r_env r_t0 *)
        destruct ai_rest';[inversion Hlength_rest'|].
        iPrologue "Hprog".
        iInv (logN.@b) as (wd) ">[Hd %]" "Hcls''". subst wd. 
        iAssert (⌜(b =? a4)%a = false⌝)%I as %Hfalse'.
        { destruct (decide (b = a4)%Z); [subst|iPureIntro;apply Z.eqb_neq,neq_z_of;auto].
          iDestruct (mapsto_valid_2 with "Hi Hd") as %?. done. }
        iApply (wp_load_success with "[$HPC $Hi $Hr_t0 $Hr_env Hd]");
          [apply decode_encode_instrW_inv|iCorrectPC a_call_end a_last| |iContiguous_next Hcont_rest' 2|..]. 
        { split;auto. rewrite andb_true_iff Z.leb_le Z.ltb_lt. clear -Hincr. solve_addr. }
        { rewrite Hfalse'. iFrame. } rewrite Hfalse'.
        iNext. iIntros "(HPC & Hr_t0 & Hi & Hr_env & Hd)". iCombine "Hi" "Hprog_done" as "Hprog_done".
        iMod ("Hcls''" with "[Hd]") as "_".
        { iNext. iExists _. iFrame. auto. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.

        (* prepare memory for the assert macro *)
        iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_assert ai_rest'' a_assert_end) "(Hassert_prog & Hprog & #Hcont)".
        { repeat (apply contiguous_between_cons_inv in Hcont_rest' as [_ [? [_ Hcont_rest'] ] ];
                  apply contiguous_between_cons_inv_first in Hcont_rest' as Heq'; subst x). apply Hcont_rest'. }
        iDestruct "Hcont" as %(Hcont_assert & Hcont_rest'' & Heqapp'' & Hlink'').
        iDestruct (big_sepL2_length with "Hassert_prog") as %Hai_assert_len.
        assert (isCorrectPC_range pc_p pc_b pc_e a5 a_assert_end) as Hvpc5.
        { eapply isCorrectPC_range_restrict. apply Hvpc.
          generalize (contiguous_between_bounds _ _ _ Hcont_rest').
          generalize (contiguous_between_bounds _ _ _ Hcont_rest'').
          generalize (contiguous_between_bounds _ _ _ Hcont_malloc).
          generalize (contiguous_between_bounds _ _ _ Hcont_call).
          apply contiguous_between_middle_bounds' with (ai:=a5) in Hcont_rest';[|repeat constructor].
          apply contiguous_between_middle_bounds' with (ai:=a2) in Hcont_rest;[|repeat constructor].
          clear -Hcont_rest' Hcont_rest. solve_addr. }
        assert (isCorrectPC_range pc_p pc_b pc_e a_assert_end a_last) as Hvpc6.
        { eapply isCorrectPC_range_restrict. apply Hvpc.
          generalize (contiguous_between_bounds _ _ _ Hcont_rest').
          generalize (contiguous_between_bounds _ _ _ Hcont_rest'').
          generalize (contiguous_between_bounds _ _ _ Hcont_malloc).
          generalize (contiguous_between_bounds _ _ _ Hcont_call).
          apply contiguous_between_middle_bounds' with (ai:=a5) in Hcont_rest';[|repeat constructor].
          apply contiguous_between_middle_bounds' with (ai:=a2) in Hcont_rest;[|repeat constructor].
          clear -Hcont_rest' Hcont_rest Hlink''. solve_addr. }
        
        (* assert macro *)
        iMod (na_inv_open with "Hlink Hown") as "[ (a_entry' & a_env & >pc_b & >Ha_entry) [Hown Hcls''] ]";[solve_ndisj..|]. 
        iApply (assert_r_z_success with "[- $HPC $Hassert_prog $pc_b $a_entry' $Hr_t0]");
          [apply Hvpc5|apply Hcont_assert|auto..].
        iSplitL "Hr_t1";[eauto|]. 
        iSplitL "Hr_t2";[eauto|].
        iSplitL "Hr_t3";[eauto|]. 
        iNext. iIntros "(Hr_t1 & Hr_t2 & Hr_t3 & Hr_t0 & HPC & Hassert_prog & Hpc_b & Ha_entry')".
        iMod ("Hcls''" with "[$Hown $Ha_entry' $a_env $Hpc_b $Ha_entry]") as "Hown".
        iMod ("Hcls'" with "[$Hown $Hb_l]") as "Hown";[iNext;done|].  

        (* halt *)
        iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest''. 
        destruct ai_rest'';[inversion Hlength_rest''|]. destruct ai_rest'';[|inversion Hlength_rest'']. 
        apply contiguous_between_cons_inv_first in Hcont_rest'' as Heq; subst a6. 
        iPrologue "Hprog". 
        iApply (wp_halt with "[$HPC $Hi]");
          [apply decode_encode_instrW_inv|iCorrectPC a_assert_end a_last|..].
        iEpilogue "(HPC & Hi)".

        (* reassemble registers, close invariants and finish *)
        iMod ("Hcls" with "[$Hown Hprog_done Hi Hassert_prog]") as "Hown". 
        { iNext. iDestruct "Hprog_done" as "($&$&$)".
          rewrite Heqapp''. iApply (big_sepL2_app with "Hassert_prog [Hi]"). iFrame. done. }
        iDestruct (big_sepM_insert with "[$Hreg $Hr_t3]") as "Hreg";[apply lookup_delete|rewrite insert_delete -delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hreg $Hr_t0]") as "Hreg";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hreg $Hr_env]") as "Hreg";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hreg $Hr_t2]") as "Hreg";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hreg $Hr_t1]") as "Hreg";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hreg $HPC]") as "Hreg";[apply lookup_delete|rewrite insert_delete].
        
        iApply wp_value. iIntros (_).
        iExists _. iFrame. iPureIntro.
        intros r';simpl. consider_next_reg r' PC. consider_next_reg r' r_t1. consider_next_reg r' r_t2.
        consider_next_reg r' r_env. consider_next_reg r' r_t0. consider_next_reg r' r_t3. 
      - (* the shared RO capability *)
        rewrite decode_encode_perm_inv.
        rewrite !fixpoint_interp1_eq. iSimpl. apply region_addrs_single in Hincr. rewrite Hincr.
        iApply big_sepL_singleton. iExists (λne (w : leibnizO Word), ⌜w = inl 1%Z⌝)%I. rewrite /roe_inv. iFrame "Hb".
        iNext. iAlways. iIntros (w ->). rewrite !fixpoint_interp1_eq. done. 
      - (* the remaining 0'ed out capabilities *)
        destruct ((create_gmap_default (map_to_list (delete r_t7 (delete r_t0 rmap))).*1 (inl 0%Z : Word)) !! r) eqn:Hsome;rewrite Hsome.
        apply create_gmap_default_lookup_is_Some in Hsome as [Hsome ->]. rewrite !fixpoint_interp1_eq. done. rewrite !fixpoint_interp1_eq. done. 
    }

    (* conclude that the full program does not get stuck *)
    iApply (wp_wand with "Hconf");auto. 
  Qed. 
    
End roe. 
