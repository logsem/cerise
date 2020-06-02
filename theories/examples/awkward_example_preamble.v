From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static.
From cap_machine.examples Require Import region_macros stack_macros scall malloc awkward_example.
From stdpp Require Import countable.

Lemma big_sepM_to_big_sepL2 {Σ : gFunctors} {A B : Type} `{EqDecision A} `{Countable A}
      (r : gmap A B) (lr : list A) (φ : A → B → iProp Σ) :
  NoDup lr →
  (∀ r0, r0 ∈ lr → is_Some (r !! r0)) →
  ([∗ map] k↦y ∈ r, φ k y) -∗ ∃ ys, ([∗ list] k;y ∈ lr;ys, φ k y).
Proof.
  iInduction (lr) as [ | r0 ] "IHl" forall (r); iIntros (Hdup Hlookup) "Hmap".
  - iExists []. done.
  - assert (is_Some (r !! r0)) as Hr0.
    { apply Hlookup. constructor. }
    destruct Hr0 as [v0 ?].
    iDestruct (big_sepM_delete _ _ r0 with "Hmap") as "(H & Hmap)"; eauto.
    iSpecialize ("IHl" with "[] [] Hmap").
    { iPureIntro. by eapply NoDup_cons_12. }
    { iPureIntro. intros rr Hrr. rewrite lookup_delete_ne.
      { apply Hlookup. by constructor. }
      intros ->. eapply NoDup_cons_11; eauto. }
    iDestruct "IHl" as (ys) "IHl". iExists (v0 :: ys). cbn. iFrame.
Qed.

(* TODO: move to lang.v *)
Lemma le_addr_withinBounds p l b e a:
  (b <= a)%a → (a < e)%a →
  withinBounds (p, l, b, e, a) = true .
Proof.
  intros. eapply andb_true_iff. unfold ltb_addr, leb_addr.
  unfold le_addr, lt_addr in *. rewrite Z.leb_le Z.ltb_lt. lia.
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
    malloc_instrs f_m 1 ++
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
  Definition awkward_preamble_move_offset : Z.
  Proof.
    unshelve notypeclasses refine (let x := _ : Z in _). {
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
    cbv in x. exact x.
  Defined.

  Lemma awkward_preamble_spec (f_m offset_to_awkward: Z) (r: Reg) W pc_p pc_g pc_b pc_e
        ai pc_p' a_first a_end b_link e_link a_link a_entry ai_awk awk_first awk_end p_awk
        r_adv a_move:

    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_end →
    PermFlows pc_p pc_p' →
    contiguous_between ai a_first a_end →
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    (a_first + awkward_preamble_move_offset)%a = Some a_move →
    (a_move + offset_to_awkward)%a = Some awk_first →
    contiguous_between ai_awk awk_first awk_end →

    (* Code of the preamble *)
    awkward_preamble f_m offset_to_awkward ai pc_p'

    (* Code of the awkward example itself *)
    ∗ awkward_example ai_awk p_awk r_adv 65

    (*** Resources for malloc ***)
    (* assume that a pointer to the linking table (where the malloc capa is) is at offset 0 of PC *)
    ∗ inv malloc_γ ([[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine]])
    ∗ pc_b ↦ₐ[pc_p'] (inr (RW, Global, b_link, e_link, a_link))
    ∗ a_entry ↦ₐ[RW] (inr (E, Global, b_m, e_m, a_m))

    -∗
    interp_expr interp r W (inr (pc_p, pc_g, pc_b, pc_e, a_first)).
  Proof.
    rewrite /interp_expr /=.
    iIntros (Hvpc Hfl Hcont Hwb_malloc Ha_entry Ha_lea H_awk_offset Hcont_awk)
            "(Hprog & Hawk & #Hinv_malloc & Hpc_b & Ha_entry)
             ([#Hr_full #Hr_valid] & Hregs & Hr & Hsts & HnaI)".
    iDestruct "Hr_full" as %Hr_full.
    rewrite /full_map.
    iSplitR; auto. rewrite /interp_conf.

    rewrite /registers_mapsto.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]".
      by rewrite lookup_insert //. rewrite delete_insert_delete //.
    destruct (Hr_full r_t0) as [r0 Hr0].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr0 Hregs]". by rewrite !lookup_delete_ne//.
    assert (dom (gset RegName) r = all_registers_s) as Hdom_r.
    { apply (anti_symm _); rewrite elem_of_subseteq.
      - intros rr _. apply all_registers_s_correct.
      - intros rr _. rewrite -elem_of_gmap_dom. apply Hr_full. }
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.

    (* malloc 1 *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_malloc ai_rest a_malloc_end) "(Hmalloc & Hprog & #Hcont)"; [apply Hcont|].
    iDestruct "Hcont" as %(Hcont_malloc & Hcont_rest & Heqapp & Hlink).
    iApply (malloc_spec with "[- $HPC $Hmalloc $Hpc_b $Ha_entry $Hr0 $Hregs $Hr $Hsts]");
      [|apply Hfl|eapply Hcont_malloc|eapply Hwb_malloc|eapply Ha_entry|..].
    { admit. }
    { rewrite !dom_delete_L Hdom_r difference_difference_L //. }
    iSplitR. iApply "Hinv_malloc". iNext.
    iIntros "(HPC & Hmalloc & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cell e_cell Hbe_cell)
                      "(Hr1 & Hcell & Hr0 & Hregs & #Hcell_fresh & Hr & Hsts)".
    iDestruct "Hcell_fresh" as %Hcell_fresh.
    (* TODO: change the postcondition of malloc to produce (b+size = Some e) instead of a subtraction? *)
    iDestruct (region_mapsto_single with "Hcell") as (cellv) "(Hcell & _)". revert Hbe_cell; clear; solve_addr.
    rewrite region_addrs_single in Hcell_fresh. 2: revert Hbe_cell; clear; solve_addr.
    rewrite ->Forall_singleton in Hcell_fresh.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.

    destruct ai_rest as [| a l]; [by inversion Hlength|].
    assert (a_malloc_end = a) as ->. admit.
    (* store_z r_t1 0 *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hr1 $Hi $Hcell]");
      [eapply store_z_i|apply Hfl|constructor| |iContiguous_next Hcont_rest 0|..].
    { admit. }
    { split; auto. apply le_addr_withinBounds; revert Hbe_cell; clear; solve_addr. }
    iEpilogue "(HPC & Hprog_done & Hr1 & Hb_cell)". iCombine "Hprog_done" "Hmalloc" as "Hprog_done".
    (* move_r r_t2 r_t1 *)
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr2 Hregs]".
      by rewrite lookup_insert. rewrite delete_insert_delete.
    destruct l as [| a_move' l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg _ _ _ _ _ _ _ _ r_t2 _ r_t1 with "[$HPC $Hi $Hr1 $Hr2]");
      [eapply move_r_i|apply Hfl| |iContiguous_next Hcont_rest 1|done|..].
    { admit. }
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t1 PC *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [eapply move_r_i|apply Hfl| |iContiguous_next Hcont_rest 2|done|..].
    { admit. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t1 offset_to_awkward *)
    assert (a_move' = a_move) as ->.
    { admit. }
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ awk_first with "[$HPC $Hi $Hr1]");
      [eapply lea_z_i|apply Hfl| |iContiguous_next Hcont_rest 3|assumption|done|..].
    { admit. }
    { admit. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* crtcls *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls ai_rest a_crtcls_end) "(Hcrtcls & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 4%nat _ _ _ Hcont_rest eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_]). 2: eapply Hcont_rest.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls & Hcont_rest' & Heqapp' & Hlink').
    iApply (crtcls_spec with "[- $HPC $Hcrtcls $Hpc_b $Ha_entry $Hr0 $Hregs $Hr1 $Hr2 $Hr $Hsts]");
      [|apply Hfl|apply Hcont_crtcls|apply Hwb_malloc|apply Ha_entry|..].
    { admit. }
    { rewrite dom_delete_L dom_insert_L !dom_delete_L Hdom_r.
      rewrite !difference_difference_L singleton_union_difference_L all_registers_union_l.
      clear. set_solver. }
    { admit. }
    { admit. }
    iSplitR. iApply "Hinv_malloc". iNext.
    iIntros "(HPC & Hcrtcls & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cls e_cls Hbe_cls) "(Hr1 & Hbe_cls & Hr0 & Hr2 & Hregs & #Hcls_fresh & Hr & Hsts)".
    iDestruct "Hcls_fresh" as %Hcls_fresh.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest'.
    (* rclear *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_rclear ai_rest' a_rclear_end) "(Hrclear & Hprog & #Hcont)"; eauto.
    iDestruct "Hcont" as %(Hcont_rclear & Hcont_rest'' & Heqapp'' & Hlink'').
    iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_len.
    destruct ai_rclear; [by inversion Hrclear_len|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rclear) as ->.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr2]") as "Hregs".
      by rewrite !lookup_insert_ne // lookup_delete.
    iApply (rclear_spec with "[- $HPC $Hrclear $Hregs]");
      [apply Hcont_rclear| | | |apply Hfl|..].
    { apply not_elem_of_list; repeat constructor. }
    { reflexivity. }
    { admit. }
    { rewrite list_to_set_difference -/all_registers_s.
      repeat rewrite ?dom_insert_L ?dom_delete_L. rewrite Hdom_r.
      rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
      f_equal. clear. set_solver. }
    iNext. iIntros "(HPC & Hregs & Hrclear)". iCombine "Hrclear" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepL2_length with "Hprog") as %Hlen'.
    destruct ai_rest'; [by inversion Hlen'|].
    (* jmp *)
    iPrologue "Hprog".
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest'') as ->.
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply jmp_i|apply Hfl|..].
    { admit. }
    iEpilogue "(HPC & Hi & Hr0)". iCombine "Hi" "Hprog_done" as "Hprog_done".

    unshelve iSpecialize ("Hr_valid" $! r_t0 _). done.
    rewrite /(RegLocate _ r_t0) Hr0.
    rewrite fixpoint_interp1_eq {1}/interp1.



  Admitted.

End awkward_example_preamble.
