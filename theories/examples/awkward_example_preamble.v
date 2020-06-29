From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static.
From cap_machine.examples Require Import region_macros stack_macros scall malloc awkward_example_helpers awkward_example.
From stdpp Require Import countable.

Lemma regmap_full_dom (r: gmap RegName Word):
  (∀ x, is_Some (r !! x)) →
  dom (gset RegName) r = all_registers_s.
Proof.
  intros Hfull. apply (anti_symm _); rewrite elem_of_subseteq.
  - intros rr _. apply all_registers_s_correct.
  - intros rr _. rewrite -elem_of_gmap_dom. apply Hfull.
Qed.

(* TODO: move *)
Lemma isCorrectPC_range_restrict p g b e a0 an a0' an' :
  isCorrectPC_range p g b e a0 an →
  (a0 <= a0')%a ∧ (an' <= an)%a →
  isCorrectPC_range p g b e a0' an'.
Proof.
  intros HR [? ?] a' [? ?]. apply HR. solve_addr.
Qed.

Section awkward_example_preamble.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Ltac iPrologue prog :=
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end.

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

  (**************)

  Lemma region_addrs_single b e:
    (b+1)%a = Some e →
    region_addrs b e = [b].
  Proof.
    intros. rewrite /region_addrs.
    rewrite (_: region_size b e = 1) //= /region_size.
    solve_addr.
  Qed.

  Lemma region_mapsto_single b e p l:
    (b+1)%a = Some e →
    [[b,e]] ↦ₐ[p] [[l]] -∗
    ∃ v, b ↦ₐ[p] v ∗ ⌜l = [v]⌝.
  Proof.
    iIntros (Hbe) "H". rewrite /region_mapsto region_addrs_single //.
    iDestruct (big_sepL2_length with "H") as %Hlen.
    cbn in Hlen. destruct l as [|x l']; [by inversion Hlen|].
    destruct l'; [| by inversion Hlen]. iExists x. cbn.
    iDestruct "H" as "(H & _)". eauto.
  Qed.

  (* [f_m] is the offset of the malloc capability *)
  (* [offset_to_awkward] is the offset between the [move_r r_t1 PC] instruction
  and the code of the awkward example *)
  Definition awkward_preamble_instrs (f_m offset_to_awkward: Z) :=
    malloc_instrs f_m 1%nat ++
    [store_z r_t1 0;
     move_r r_t2 r_t1;
     move_r r_t1 PC;
     lea_z r_t1 offset_to_awkward] ++
    crtcls_instrs f_m ++
    rclear_instrs (list_difference all_registers [PC; r_t0; r_t1]) ++
    [jmp r_t0].

  Definition awkward_preamble f_m offset_to_awkward ai p :=
    ([∗ list] a_i;w_i ∈ ai;(awkward_preamble_instrs f_m offset_to_awkward), a_i ↦ₐ[p] w_i)%I.

  (* Compute the offset from the start of the program to the move_r r_t1 PC
     instruction. Will be used later to compute [offset_to_awkward]. *)
  (* This is somewhat overengineered, but could be easily generalized to compute
     offsets for other programs if needed. *)
  Definition awkward_preamble_move_offset_ : Z.
  Proof.
    unshelve refine (let x := _ : Z in _). {
      set instrs := awkward_preamble_instrs 0 0.
      assert (sig (λ l1, ∃ l2, instrs = l1 ++ l2)) as [l1 _]; [do 2 eexists | exact (length l1)].

      assert (forall A (l1 l2 l3 l4: list A), l2 = l3 ++ l4 → l1 ++ l2 = (l1 ++ l3) ++ l4) as step_app.
      { intros * ->. by rewrite app_assoc. }
      assert (forall A (l1 l2 l3: list A) x, l1 = l2 ++ l3 → x :: l1 = (x :: l2) ++ l3) as step_cons.
      { intros * ->. reflexivity. }
      assert (forall A (l1 l2: list A) x, x :: l1 = l2 → x :: l1 = l2) as prepare_cons.
      { auto. }
      assert (forall A (l: list A), l = [] ++ l) as stop.
      { reflexivity. }

      unfold instrs, awkward_preamble_instrs.
      (* Program-specific part *)
      eapply step_app.
      repeat (eapply prepare_cons;
              lazymatch goal with
              | |- move_r r_t1 PC :: _ = _ => fail
              | _ => eapply step_cons end).
      eapply stop.
    }
    exact x.
  Defined.

  Definition awkward_preamble_move_offset : Z :=
    Eval cbv in awkward_preamble_move_offset_.

  Definition awkward_preamble_instrs_length : Z :=
    Eval cbv in (length (awkward_preamble_instrs 0 0)).

  Definition awkN : namespace := nroot .@ "awkN".
  Definition awk_invN : namespace := awkN .@ "inv".
  Definition awk_codeN : namespace := awkN .@ "code".
  Definition awk_clsN : namespace := awkN .@ "cls".
  Definition awk_env : namespace := awkN .@ "env". 

  Lemma awkward_preamble_spec (f_m f_a offset_to_awkward: Z) (r: Reg) W pc_p pc_b pc_e
        ai pc_p' a_first a_end b_link e_link a_link a_entry a_entry'
        mallocN b_m e_m fail_cap ai_awk awk_first awk_end a_move:

    isCorrectPC_range pc_p Global pc_b pc_e a_first a_end →
    PermFlows pc_p pc_p' →
    contiguous_between ai a_first a_end →
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    withinBounds (RW, Global, b_link, e_link, a_entry') = true →
    (a_link + f_m)%a = Some a_entry →
    (a_link + f_a)%a = Some a_entry' →
    (a_first + awkward_preamble_move_offset)%a = Some a_move →
    (a_move + offset_to_awkward)%a = Some awk_first →
    isCorrectPC_range pc_p Global pc_b pc_e awk_first awk_end →
    contiguous_between ai_awk awk_first awk_end →

    (* Code of the preamble *)
    awkward_preamble f_m offset_to_awkward ai pc_p'

    (* Code of the awkward example itself *)
    ∗ awkward_example ai_awk pc_p' f_a r_adv

    (*** Resources for malloc ***)
    (* assume that a pointer to the linking table (where the malloc capa is) is at offset 0 of PC *)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ pc_b ↦ₐ[pc_p'] (inr (RW, Global, b_link, e_link, a_link))
    ∗ a_entry ↦ₐ[RW] (inr (E, Global, b_m, e_m, b_m))
    ∗ a_entry' ↦ₐ[RW] fail_cap

    -∗
    interp_expr interp r W (inr (pc_p, Global, pc_b, pc_e, a_first)).
  Proof.
    rewrite /interp_expr /=.
    iIntros (Hvpc Hfl Hcont Hwb_malloc Hwb_assert Ha_entry Ha_entry' Ha_lea H_awk_offset Hvpc_awk Hcont_awk)
            "(Hprog & Hawk & #Hinv_malloc & Hpc_b & Ha_entry & Ha_entry')
             ([#Hr_full #Hr_valid] & Hregs & Hr & Hsts & HnaI)".
    iDestruct "Hr_full" as %Hr_full.
    rewrite /full_map.
    iSplitR; auto. rewrite /interp_conf.

    (* put the code for the awkward example in an invariant *)
    iDestruct (na_inv_alloc logrel_nais _ awk_codeN with "Hawk") as ">#Hawk".

    rewrite /registers_mapsto.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]".
      by rewrite lookup_insert //. rewrite delete_insert_delete //.
    destruct (Hr_full r_t0) as [r0 Hr0].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr0 Hregs]". by rewrite !lookup_delete_ne//.
    pose proof (regmap_full_dom _ Hr_full) as Hdom_r.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.

    assert (pc_p ≠ E).
    { eapply isCorrectPC_range_perm_non_E. eapply Hvpc.
      pose proof (contiguous_between_length _ _ _ Hcont) as HH. rewrite Hlength /= in HH.
      revert HH; clear; solve_addr. }

    (* malloc 1 *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_malloc ai_rest a_malloc_end) "(Hmalloc & Hprog & #Hcont)"; [apply Hcont|].
    iDestruct "Hcont" as %(Hcont_malloc & Hcont_rest & Heqapp & Hlink).
    iDestruct (big_sepL2_length with "Hmalloc") as %Hai_malloc_len.
    assert (isCorrectPC_range pc_p Global pc_b pc_e a_first a_malloc_end) as Hvpc1.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest). clear; solve_addr. }
    assert (isCorrectPC_range pc_p Global pc_b pc_e a_malloc_end a_end) as Hvpc2.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_malloc). clear; solve_addr. }
    rewrite -/(malloc _ _ _ _).
    iApply (wp_wand with "[-]").
    iApply (malloc_spec with "[- $HPC $Hmalloc $Hpc_b $Ha_entry $Hr0 $Hregs $Hr $Hsts $Hinv_malloc $HnaI]");
      [apply Hvpc1|apply Hfl|eapply Hcont_malloc|eapply Hwb_malloc|eapply Ha_entry| |auto|lia|..].
    { rewrite !dom_delete_L Hdom_r difference_difference_L //. }
    iNext. iIntros "(HPC & Hmalloc & Hpc_b & Ha_entry & HH & Hr0 & HnaI & Hregs & Hr & Hsts)".
    iDestruct "HH" as (b_cell e_cell Hbe_cell) "(Hr1 & Hcell)".
    (* TODO: change the postcondition of malloc to produce (b+size = Some e) instead of a subtraction? *)
    iDestruct (region_mapsto_single with "Hcell") as (cellv) "(Hcell & _)". revert Hbe_cell; clear; solve_addr.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    2: { iIntros (?) "[HH | ->]". iApply "HH". iIntros (Hv). inversion Hv. }

    destruct ai_rest as [| a l]; [by inversion Hlength|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest) as ->.
    (* store_z r_t1 0 *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hr1 $Hi $Hcell]");
      [eapply store_z_i|apply Hfl|constructor|iCorrectPC a_malloc_end a_end|
       iContiguous_next Hcont_rest 0|..].
    { split; auto. apply le_addr_withinBounds; revert Hbe_cell; clear; solve_addr. }
    iEpilogue "(HPC & Hprog_done & Hr1 & Hb_cell)". iCombine "Hprog_done" "Hmalloc" as "Hprog_done".
    (* move_r r_t2 r_t1 *)
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr2 Hregs]".
      by rewrite lookup_insert. rewrite delete_insert_delete.
    destruct l as [| a_move' l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg _ _ _ _ _ _ _ _ r_t2 _ r_t1 with "[$HPC $Hi $Hr1 $Hr2]");
      [eapply move_r_i|apply Hfl|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 1|done|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t1 PC *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [eapply move_r_i|apply Hfl|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 2|done|..].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t1 offset_to_awkward *)
    assert (a_move' = a_move) as ->.
    { assert ((a_first + (length ai_malloc + 2))%a = Some a_move') as HH.
      { rewrite Hai_malloc_len /= in Hlink |- *.
        generalize (contiguous_between_incr_addr_middle _ _ _ 0 2 _ _ Hcont_rest eq_refl eq_refl).
        revert Hlink; clear; solve_addr. }
      revert HH Ha_lea. rewrite Hai_malloc_len. cbn. clear.
      unfold awkward_preamble_move_offset. solve_addr. }
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ awk_first with "[$HPC $Hi $Hr1]");
      [eapply lea_z_i|apply Hfl|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 3
       |assumption|done|done|..].
    { destruct (isCorrectPC_range_perm _ _ _ _ _ _ Hvpc) as [-> | [-> | ->] ]; auto.
      generalize (contiguous_between_middle_bounds _ (length ai_malloc) a_malloc_end _ _ Hcont ltac:(subst ai; rewrite list_lookup_middle; auto)). clear. solve_addr. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* crtcls *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls ai_rest a_crtcls_end) "(Hcrtcls & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 4%nat _ _ _ Hcont_rest eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_]). 2: eapply Hcont_rest.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls & Hcont_rest' & Heqapp' & Hlink').
    assert (a_malloc_end <= a1)%a as Ha1_after_malloc.
    { eapply contiguous_between_middle_bounds'. apply Hcont_rest. repeat constructor. }
    iApply (wp_wand with "[-]").
    iApply (crtcls_spec with "[- $HPC $Hcrtcls $Hpc_b $Ha_entry $Hr0 $Hregs $Hr1 $Hr2 $Hr $Hsts $HnaI $Hinv_malloc]");
      [|apply Hfl|apply Hcont_crtcls|apply Hwb_malloc|apply Ha_entry| |done|done|auto|..].
    { eapply isCorrectPC_range_restrict. apply Hvpc2. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest'. }
    { rewrite dom_delete_L !dom_insert_L !dom_delete_L Hdom_r.
      rewrite !difference_difference_L singleton_union_difference_L all_registers_union_l.
      rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
      f_equal. set_solver-. }
    2: { iIntros (?) "[ H | -> ]". iApply "H". iIntros (HC). congruence. }
    iNext. iIntros "(HPC & Hcrtcls & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cls e_cls Hbe_cls) "(Hr1 & Hbe_cls & Hr0 & Hr2 & HnaI & Hregs & Hr & Hsts)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest'.
    iDestruct (na_inv_alloc logrel_nais _ awk_clsN with "Hbe_cls") as ">#Hcls_inv".
    (* rclear *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_rclear ai_rest' a_rclear_end) "(Hrclear & Hprog & #Hcont)"; eauto.
    iDestruct "Hcont" as %(Hcont_rclear & Hcont_rest'' & Heqapp'' & Hlink'').
    iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_len.
    destruct ai_rclear; [by inversion Hrclear_len|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rclear) as ->.
    assert (a_malloc_end <= a_crtcls_end)%a as Hcrtcls_end_after_malloc.
    { generalize (contiguous_between_bounds _ _ _ Hcont_rest'').
      revert Ha1_after_malloc Hlink'. clear; solve_addr. }
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr2]") as "Hregs".
      by rewrite !lookup_insert_ne // lookup_delete.
     (* /!\ This manual assert and the manual unfolding of rclear is needed.
        Otherwise Qed runs in a loop when checking that [rclear ...] and
        the type of "Hrclear" ([∗ list] ...) are convertible *)
    iAssert (rclear (a_crtcls_end :: ai_rclear) pc_p' (list_difference all_registers [PC; r_t0; r_t1]))
               with "[Hrclear]" as "Hrclear".
    { rewrite /rclear. iApply "Hrclear". }
    iApply (rclear_spec with "[- $HPC $Hrclear $Hregs]");
      [apply Hcont_rclear| | | |apply Hfl|..].
    { apply not_elem_of_list; repeat constructor. }
    { reflexivity. }
    { eapply isCorrectPC_range_restrict. apply Hvpc2. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest''. }
    { rewrite list_to_set_difference -/all_registers_s.
      repeat rewrite ?dom_insert_L ?dom_delete_L. rewrite Hdom_r.
      rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
      f_equal. clear. set_solver. }
    iNext. iIntros "(HPC & Hregs & Hrclear)". iCombine "Hrclear" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepL2_length with "Hprog") as %Hlen'.
    destruct ai_rest'; [by inversion Hlen'|].
    (* in preparation of jumping, we allocate the new awkward invariant and sts *)
    iDestruct (sts_alloc_loc _ false awk_rel_pub awk_rel_priv with "Hsts") as ">HH".
    iDestruct "HH" as (i) "(Hsts & % & % & Hst_i & #Hrel_i)".
    iDestruct (inv_alloc awkN _ (awk_inv i b_cell) with "[Hb_cell Hst_i]") as ">#Hawk_inv".
    { iNext. rewrite /awk_inv. iExists false. iFrame. }
    (* we also allocate a non atomic invariant for the environment table *)
    iMod (na_inv_alloc logrel_nais _ awk_env
                       (pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link) ∗ a_entry' ↦ₐ[RW] fail_cap)%I
            with "[$Ha_entry' $Hpc_b]") as "#Henv". 
    (* call the resulting world W2 *)
    match goal with |- context [ sts_full_world ?W ] => set W2 := W end.
    (* jmp *)
    iPrologue "Hprog".
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest'') as ->.
    assert (ai_rest' = []) as -> by (inversion Hlen'; eauto using nil_length_inv).
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply jmp_i|apply Hfl|..].
    { apply Hvpc2.
      generalize (contiguous_between_middle_bounds'
        _ a_rclear_end _ _ Hcont_rest'' ltac:(repeat constructor)).
      revert Hcrtcls_end_after_malloc Hlink''. clear; solve_addr. }

    (* the current state of registers is valid *)
    iAssert (interp W2 (inr (E, Global, b_cls, e_cls, b_cls)))%I as "#Hvalid_cls".
    { rewrite /interp fixpoint_interp1_eq. iModIntro. rewrite /enter_cond.
      iIntros (r' W3 HW3) "". iNext. rewrite /interp_expr /=.
      iIntros "([Hr'_full #Hr'_valid] & Hregs' & Hr & Hsts & HnaI)". iDestruct "Hr'_full" as %Hr'_full.
      pose proof (regmap_full_dom _ Hr'_full) as Hdom_r'.
      iSplitR; [auto|]. rewrite /interp_conf.

      iDestruct (na_inv_open with "Hcls_inv HnaI") as ">(>Hcls & Hna & Hcls_close)";
        [auto..|].

      rewrite /registers_mapsto.
      rewrite -insert_delete.
      iDestruct (big_sepM_insert with "Hregs'") as "[HPC Hregs']". by apply lookup_delete. 
      destruct (Hr'_full r_t1) as [r1v ?].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hregs'") as "[Hr1 Hregs']".
        by rewrite lookup_delete_ne //.
      destruct (Hr'_full r_env) as [renvv ?].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs'") as "[Hrenv Hregs']".
        by rewrite !lookup_delete_ne //.
      (* Run the closure activation code *)
      iApply (closure_activation_spec with "[- $HPC $Hr1 $Hrenv $Hcls]");
        [done|done| |done|..].
      { intros ? [? ?]. constructor; try split; auto. }
      rewrite updatePcPerm_cap_non_E //;[].
      iIntros "(HPC & Hr1 & Hrenv & Hcls)".
      (* close the invariant for the closure *)
      iDestruct ("Hcls_close" with "[Hcls $Hna]") as ">Hna".
      { repeat iDestruct "Hprog_done" as "(?&Hprog_done)". iNext. iFrame. }

      iDestruct (big_sepM_insert with "[$Hregs' $Hr1]") as "Hregs'".
        by rewrite lookup_delete_ne // lookup_delete //.
        rewrite -delete_insert_ne // insert_delete.
      destruct (Hr'_full r_t0) as [r0v Hr0v].
      iDestruct (big_sepM_delete _ _ r_t0 with "Hregs'") as "[Hr0 Hregs']".
        by rewrite lookup_delete_ne // lookup_insert_ne // lookup_delete_ne //.
      destruct (Hr'_full r_adv) as [radvv Hradvv].
      iDestruct (big_sepM_delete _ _ r_adv with "Hregs'") as "[Hradv Hregs']".
        by rewrite !lookup_delete_ne // lookup_insert_ne // lookup_delete_ne //.
      destruct (Hr'_full r_stk) as [rstkv Hrstkv].
      iDestruct (big_sepM_delete _ _ r_stk with "Hregs'") as "[Hrstk Hregs']".
        by rewrite !lookup_delete_ne // lookup_insert_ne // lookup_delete_ne //.

      iApply (f4_spec with "[$HPC $Hr0 $Hradv $Hrenv $Hrstk $Hregs' $Hrel_i $Hna $Hsts $Hr $Henv $Hawk]");
        [apply Hvpc_awk|auto|apply Hcont_awk|apply Hwb_assert|apply Ha_entry'|..].
      { revert Hbe_cell; clear; solve_addr. }
      { rewrite !dom_delete_L !dom_insert_L !dom_delete_L Hdom_r'.
        rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
        f_equal. clear. set_solver. }
      { solve_ndisj. }
      iSplitL. iExists awkN; iApply "Hawk_inv".
      iSplitL.
      { unshelve iSpecialize ("Hr'_valid" $! r_stk _); [done|].
        rewrite /(RegLocate r' r_stk) Hrstkv. iApply "Hr'_valid". }
      iSplitL.
      { unshelve iSpecialize ("Hr'_valid" $! r_adv _); [done|].
        rewrite /(RegLocate r' r_adv) Hradvv. iApply "Hr'_valid". }
      unshelve iSpecialize ("Hr'_valid" $! r_t0 _); [done|].
      rewrite /(RegLocate r' r_t0) Hr0v. iApply "Hr'_valid". 
      { iNext. iIntros (?) "HH". iIntros (->). iApply "HH". eauto. }
    }

    unshelve iSpecialize ("Hr_valid" $! r_t0 _). done.
    rewrite /(RegLocate _ r_t0) Hr0.

    iAssert (((fixpoint interp1) W2) r0) as "#Hr_valid2". 
    { iApply (interp_monotone with "[] Hr_valid"). iPureIntro. apply related_sts_pub_world_fresh_loc; auto. }
    set r' : gmap RegName Word :=
      <[r_t0  := r0]>
      (<[r_t1 := inr (E, Global, b_cls, e_cls, b_cls)]>
       (create_gmap_default (list_difference all_registers [r_t0;r_t1]) (inl 0%Z))).

    (* either we fail, or we use the continuation in rt0 *)
    iDestruct (jmp_or_fail_spec with "Hr_valid2") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm r0))). 
    2 : { iEpilogue "(HPC & Hi & Hr0)". iApply "Hcont". iFrame "HPC". iIntros (Hcontr);done. }
    iDestruct "Hcont" as (p g b e a3 Heq) "#Hcont". 
    simplify_eq. 

    iAssert (future_world g W2 W2) as "#Hfuture".
    { destruct g; iPureIntro. apply related_sts_priv_refl_world. apply related_sts_pub_refl_world. }
    iAssert (∀ r, ▷ ((interp_expr interp r) W2 (updatePcPerm (inr (p, g, b, e, a3)))))%I with "[Hcont]" as "Hcont'".
    { iIntros. iApply "Hcont". iApply "Hfuture". }

    (* prepare the continuation *)
    iEpilogue "(HPC & Hi & Hr0)". iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* Put the registers back in the map *)
    iAssert ([∗ map] r↦w ∈ (create_gmap_default (list_difference all_registers [PC; r_t0; r_t1]) (inl 0%Z)),
             r ↦ᵣ w)%I with "[Hregs]" as "Hregs".
    { iApply (big_sepM_mono (λ r w, r ↦ᵣ inl 0%Z)%I). intros k w.
      intros [? ->]%create_gmap_default_lookup_is_Some. auto.
      iDestruct (big_sepM_dom with "Hregs") as "Hregs". iApply big_sepM_dom.
      rewrite big_opS_proper'. iApply "Hregs". done.
      rewrite create_gmap_default_dom list_to_set_difference -/all_registers_s.
      repeat rewrite ?dom_insert_L ?dom_delete_L. rewrite Hdom_r.
      rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
      f_equal. clear. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs"; [done|].
    iDestruct (big_sepM_insert with "[$Hregs $Hr0]") as "Hregs"; [done|].
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs"; [done|].
    rewrite -(insert_insert _ PC _ (inl 0%Z)).
    match goal with |- context [ ([∗ map] k↦y ∈ <[PC:=_]> ?r, _)%I ] => set r'' := r end.
    iAssert (full_map r'') as %Hr''_full.
    { rewrite /full_map. iIntros (rr). iPureIntro. rewrite elem_of_gmap_dom /r''.
      rewrite 3!dom_insert_L create_gmap_default_dom list_to_set_difference -/all_registers_s.
      generalize (all_registers_s_correct rr). clear; set_solver. }
    iSpecialize ("Hcont'" $! r'' with "[Hsts Hr Hregs HnaI]").
    { iFrame.
      iDestruct (region_monotone with "[] [] Hr") as "$";
        [auto|iPureIntro; apply related_sts_pub_world_fresh_loc; auto|]. iFrame.
      rewrite /interp_reg. iSplit; [iPureIntro; apply Hr''_full|].
      iIntros (rr Hrr).
      assert (is_Some (r'' !! rr)) as [rrv Hrrv] by apply Hr''_full.
      rewrite /RegLocate Hrrv. rewrite /r'' in Hrrv.
      rewrite lookup_insert_Some in Hrrv |- *. move=> [ [? ?] | [_ Hrrv] ].
      { subst rr. by exfalso. }
      rewrite lookup_insert_Some in Hrrv |- *. move=> [ [? ?] | [? Hrrv] ].
      { subst rr rrv. iApply "Hr_valid2". }
      rewrite lookup_insert_Some in Hrrv |- *. move=> [ [? ?] | [? Hrrv] ].
      { subst rr rrv. iApply "Hvalid_cls". }
      apply create_gmap_default_lookup_is_Some in Hrrv as [_ ->].
      rewrite /interp /=. rewrite (fixpoint_interp1_eq W2 (inl 0%Z)). auto. }
    (* apply the continuation *)
    iDestruct "Hcont'" as "[_ Hcallback_now]".
    iApply wp_wand_l. iFrame "Hcallback_now".
    iIntros (v) "Hφ". iIntros (Hne).
    iDestruct ("Hφ" $! Hne) as (r0 W') "(Hfull & Hregs & #Hrelated & Hna & Hsts & Hr)".
    iExists r0,W'. iFrame.
    iDestruct "Hrelated" as %Hrelated. iPureIntro.
    eapply related_sts_pub_priv_trans_world;[|eauto].
    apply related_sts_pub_world_fresh_loc; auto.
  Qed.

End awkward_example_preamble.
