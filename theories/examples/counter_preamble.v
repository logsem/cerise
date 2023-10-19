From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import rules logrel fundamental.
From cap_machine.examples Require Import macros macros_helpers malloc counter.
From stdpp Require Import countable.

Section counter_example_preamble.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Definition counter_instrs f_a :=
    incr_instrs ++ (read_instrs f_a) ++ reset_instrs.

  Definition counter f_a a :=
    ([∗ list] a_i;w ∈ a;(counter_instrs f_a), a_i ↦ₐ w )%I.

  Definition counter_instrs_length : Z :=
    Eval cbv in (length (incr_instrs ++ (read_instrs 0) ++ reset_instrs)).
  Definition incr_instrs_length : Z :=
    Eval cbv in (length (incr_instrs)).
  Definition read_instrs_length : Z :=
    Eval cbv in (length (read_instrs 0)).
  Definition reset_instrs_length : Z :=
    Eval cbv in (length (reset_instrs)).

  (* [f_m] is the offset of the malloc capability *)
  (* [offset_to_counter] is the offset between the [move_r r_t1 PC] instruction
  and the code of the counter, which will be the concatenation of: incr;read;reset *)
  Definition counter_preamble_instrs (f_m offset_to_counter: Z) :=
    malloc_instrs f_m 1%nat ++
    [store_z r_t1 0;
    move_r r_t2 r_t1;
    move_r r_t1 PC;
    move_r r_t8 r_t2; (* we keep a copy of the capability for the other closures *)
    move_r r_t9 r_t1; (* same for PC *)
    (* closure for incr *)
    lea_z r_t1 offset_to_counter] ++
    crtcls_instrs f_m ++
    [move_r r_t10 r_t1;
    move_r r_t2 r_t8;
    move_r r_t1 r_t9;
    (* closure for read *)
    lea_z r_t1 (offset_to_counter + (strings.length (incr_instrs)))] ++
    crtcls_instrs f_m ++
    [move_r r_t11 r_t1;
    move_r r_t2 r_t8;
    move_r r_t1 r_t9;
    (* closure for reset *)
    lea_z r_t1 (offset_to_counter + (strings.length (incr_instrs)) + (strings.length (read_instrs 0)))] ++
    crtcls_instrs f_m ++
    (* cleanup *)
    [move_r r_t2 r_t10;
    move_z r_t10 0;
    move_r r_t3 r_t11;
    move_z r_t11 0;
    move_z r_t8 0;
    move_z r_t9 0;
    jmp r_t0].

  Definition counter_preamble f_m offset_to_counter ai :=
    ([∗ list] a_i;w_i ∈ ai;(counter_preamble_instrs f_m offset_to_counter), a_i ↦ₐ w_i)%I.

  (* Compute the offset from the start of the program to the move_r r_t1 PC
     instruction. Will be used later to compute [offset_to_awkward]. *)
  (* This is somewhat overengineered, but could be easily generalized to compute
     offsets for other programs if needed. *)
  Definition counter_preamble_move_offset_ : Z.
  Proof.
    unshelve refine (let x := _ : Z in _). {
      set instrs := counter_preamble_instrs 0 0.
      assert (sig (λ l1, ∃ l2, instrs = l1 ++ l2)) as [l1 _]; [do 2 eexists | exact (length l1)].

      assert (forall A (l1 l2 l3 l4: list A), l2 = l3 ++ l4 → l1 ++ l2 = (l1 ++ l3) ++ l4) as step_app.
      { intros * ->. by rewrite app_assoc. }
      assert (forall A (l1 l2 l3: list A) x, l1 = l2 ++ l3 → x :: l1 = (x :: l2) ++ l3) as step_cons.
      { intros * ->. reflexivity. }
      assert (forall A (l1 l2: list A) x, x :: l1 = l2 → x :: l1 = l2) as prepare_cons.
      { auto. }
      assert (forall A (l: list A), l = [] ++ l) as stop.
      { reflexivity. }

      unfold instrs, counter_preamble_instrs.
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

  Definition counter_preamble_move_offset : Z :=
    Eval cbv in counter_preamble_move_offset_.

  Definition counter_preamble_instrs_length : Z :=
    Eval cbv in (length (counter_preamble_instrs 0 0)).

  Ltac iPrologue prog :=
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  (* The following three lemmas show that the created closures are valid *)
  Lemma incr_closure_valid incr_prog restc count_incrN countN count_clsN b_cls e_cls b_cls' e_cls' b_cls'' e_cls''
        pc_p pc_b pc_e counter_first counter_end linkc linkc' b_cell e_cell :
    pc_p ≠ E →
    contiguous_between incr_prog counter_first linkc →
    isCorrectPC_range pc_p pc_b pc_e counter_first counter_end →
    contiguous_between restc linkc counter_end →
    (b_cell + 1)%a = Some e_cell →

    ⊢ (inv countN (counter_inv b_cell) -∗
     na_inv logrel_nais count_incrN ([∗ list] a_i;w_i ∈ incr_prog;incr_instrs, a_i ↦ₐ w_i) -∗
     na_inv logrel_nais count_clsN
     ([[b_cls,e_cls]]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e counter_first; WCap RWX b_cell e_cell b_cell] ]]
  ∗ [[b_cls',e_cls']]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e linkc; WCap RWX b_cell e_cell b_cell] ]]
  ∗ [[b_cls'',e_cls'']]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e linkc'; WCap RWX b_cell e_cell b_cell] ]]) -∗
     na_own logrel_nais ⊤ -∗
    interp (WCap E b_cls e_cls b_cls))%I.
  Proof.
    iIntros (Hnp Hcont_incr Hvpc_counter Hcont_restc Hbe_cell) "#Hcounter_inv #Hincr #Hcls_inv HnaI".
    rewrite /interp fixpoint_interp1_eq. rewrite /enter_cond.
    iIntros (r') "". iNext. iModIntro. rewrite /interp_expr /=.
    iIntros "([Hr'_full #Hr'_valid] & Hregs' & HnaI)". iDestruct "Hr'_full" as %Hr'_full.
    pose proof (regmap_full_dom _ Hr'_full) as Hdom_r'.
    rewrite /interp_conf.

    iDestruct (na_inv_acc with "Hcls_inv HnaI") as ">(>(Hcls & Hcls' & Hcls'') & Hna & Hcls_close)";
      [auto..|].

    rewrite /registers_mapsto.
    rewrite -insert_delete_insert.
    iDestruct (big_sepM_insert with "Hregs'") as "[HPC Hregs']". by apply lookup_delete.
    destruct (Hr'_full r_t1) as [r1v ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs'") as "[Hr1 Hregs']".
      by rewrite lookup_delete_ne //.
    destruct (Hr'_full r_env) as [renvv ?].
    iDestruct (big_sepM_delete _ _ r_env with "Hregs'") as "[Hrenv Hregs']".
      by rewrite !lookup_delete_ne //.
    (* Run the closure activation code *)
    iApply (closure_activation_spec with "[- $HPC $Hr1 $Hrenv $Hcls]");
      [done| |done|..].
    { intros ? [? ?]. constructor; try split; auto. }
    rewrite updatePcPerm_cap_non_E //;[].
    iIntros "(HPC & Hr1 & Hrenv & Hcls)".
    (* close the invariant for the closure *)
    iDestruct ("Hcls_close" with "[Hcls Hcls' Hcls'' $Hna]") as ">Hna".
    { iNext. iFrame. }

    destruct (Hr'_full r_t0) as [r0v Hr0v].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs'") as "[Hr0 Hregs']".
      by rewrite !lookup_delete_ne // lookup_delete_ne //.

    iApply (incr_spec with "[$HPC $Hr0 $Hrenv $Hregs' $Hna $Hincr Hr1]");
      [|apply Hcont_incr|auto|..].
    { eapply isCorrectPC_range_restrict; [apply Hvpc_counter|]. split;[clear;solve_addr|].
      apply contiguous_between_bounds in Hcont_restc. apply Hcont_restc. }
    { rewrite !dom_delete_L Hdom_r'. clear. set_solver. }
    { iSplitL;[eauto|]. iSplit.
      - iExists _. iFrame "#".
      - iSplit; [unshelve iSpecialize ("Hr'_valid" $! r_t0 _ _ Hr0v); [done|]|].
        iFrame "Hr'_valid".
        iApply big_sepM_forall. iIntros (reg w Hlook).
        assert (reg ≠ r_t0);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ r_env);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ r_t1);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ PC);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        iSpecialize ("Hr'_valid" $! reg _ H4 Hlook).  iApply "Hr'_valid";auto.
    }
    { iNext. iIntros (?) "HH". iIntros (->). iApply "HH". eauto. }
  Qed.

  Lemma read_closure_valid read_prog reset_prog incr_prog count_readN countN count_clsN b_cls e_cls b_cls' e_cls' b_cls'' e_cls''
        pc_p pc_b pc_e counter_first counter_end linkc linkc' b_cell e_cell f_a
        b_link e_link a_link a_entry' b_a e_a a_flag assertN count_env :
    pc_p ≠ E →
    contiguous_between incr_prog counter_first linkc →
    contiguous_between read_prog linkc linkc' →
    isCorrectPC_range pc_p pc_b pc_e counter_first counter_end →
    contiguous_between reset_prog linkc' counter_end →
    (b_cell + 1)%a = Some e_cell →
    (a_link + f_a)%a = Some a_entry' →
    withinBounds b_link e_link a_entry' = true →
    (up_close (B:=coPset) count_env ## ↑count_readN) →
    up_close (B:=coPset) assertN ## ↑count_readN →
    up_close (B:=coPset) assertN ## ↑count_env →

    ⊢ (inv countN (counter_inv b_cell) -∗
     na_inv logrel_nais count_readN ([∗ list] a_i;w_i ∈ read_prog;read_instrs f_a, a_i ↦ₐ w_i) -∗
     na_inv logrel_nais count_clsN
     ([[b_cls,e_cls]]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e counter_first; WCap RWX b_cell e_cell b_cell] ]]
  ∗ [[b_cls',e_cls']]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e linkc; WCap RWX b_cell e_cell b_cell] ]]
  ∗ [[b_cls'',e_cls'']]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e linkc'; WCap RWX b_cell e_cell b_cell] ]]) -∗
     na_inv logrel_nais count_env (pc_b ↦ₐ WCap RO b_link e_link a_link ∗ a_entry' ↦ₐ WCap E b_a e_a b_a) -∗
     na_inv logrel_nais assertN (assert_inv b_a a_flag e_a) -∗
     na_own logrel_nais ⊤ -∗
    interp (WCap E b_cls' e_cls' b_cls'))%I.
  Proof.
    iIntros (Hnp Hcont_incr Hcont_read Hvpc_counter Hcont_restc Hbe_cell Hlink Hwb Hdisj ? ?)
            "#Hcounter_inv #Hincr #Hcls_inv #Hlink #Hassert HnaI".
    rewrite /interp fixpoint_interp1_eq. rewrite /enter_cond.
    iIntros (r') "". iNext. iModIntro. rewrite /interp_expr /=.
    iIntros "([Hr'_full #Hr'_valid] & Hregs' & HnaI)". iDestruct "Hr'_full" as %Hr'_full.
    pose proof (regmap_full_dom _ Hr'_full) as Hdom_r'.
    rewrite /interp_conf.

    iDestruct (na_inv_acc with "Hcls_inv HnaI") as ">(>(Hcls & Hcls' & Hcls'') & Hna & Hcls_close)";
      [auto..|].

    rewrite /registers_mapsto.
    rewrite -insert_delete_insert.
    iDestruct (big_sepM_insert with "Hregs'") as "[HPC Hregs']". by apply lookup_delete.
    destruct (Hr'_full r_t1) as [r1v ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs'") as "[Hr1 Hregs']".
      by rewrite lookup_delete_ne //.
    destruct (Hr'_full r_env) as [renvv ?].
    iDestruct (big_sepM_delete _ _ r_env with "Hregs'") as "[Hrenv Hregs']".
      by rewrite !lookup_delete_ne //.
    (* Run the closure activation code *)
    iApply (closure_activation_spec with "[- $HPC $Hr1 $Hrenv $Hcls']");
      [done| |done|..].
    { intros ? [? ?]. constructor; try split; auto. }
    rewrite updatePcPerm_cap_non_E //;[].
    iIntros "(HPC & Hr1 & Hrenv & Hcls')".
    (* close the invariant for the closure *)
    iDestruct ("Hcls_close" with "[Hcls Hcls' Hcls'' $Hna]") as ">Hna".
    { iNext. iFrame. }

    destruct (Hr'_full r_t0) as [r0v Hr0v].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs'") as "[Hr0 Hregs']".
      by rewrite !lookup_delete_ne // lookup_delete_ne //.

    iApply (read_spec with "[$HPC $Hr0 $Hrenv $Hregs' $Hna $Hincr Hr1 $Hlink $Hassert]");
      [|apply Hcont_read|auto..].
    { eapply isCorrectPC_range_restrict; [apply Hvpc_counter|].  apply contiguous_between_bounds in Hcont_incr.
      split;auto. apply contiguous_between_bounds in Hcont_restc. apply Hcont_restc. }
    { rewrite !dom_delete_L Hdom_r'. clear. set_solver. }
    { iSplitL;[eauto|]. iSplit.
      - iExists _. iFrame "#".
      - iSplit; [unshelve iSpecialize ("Hr'_valid" $! r_t0 _ _ Hr0v); [done|]|].
        iFrame "Hr'_valid".
        iApply big_sepM_forall. iIntros (reg w Hlook).
        assert (reg ≠ r_t0);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ r_env);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ r_t1);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ PC);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        unshelve iSpecialize ("Hr'_valid" $! reg _ _ Hlook). auto. iApply "Hr'_valid";auto.
    }
    { iNext. iIntros (?) "HH". iIntros (->). iApply "HH". eauto. }
  Qed.

  Lemma reset_closure_valid read_prog reset_prog incr_prog count_resetN countN count_clsN b_cls e_cls b_cls' e_cls' b_cls'' e_cls''
        pc_p pc_b pc_e counter_first counter_end linkc linkc' b_cell e_cell :
    pc_p ≠ E →
    contiguous_between incr_prog counter_first linkc →
    contiguous_between read_prog linkc linkc' →
    isCorrectPC_range pc_p pc_b pc_e counter_first counter_end →
    contiguous_between reset_prog linkc' counter_end →
    (b_cell + 1)%a = Some e_cell →

    ⊢ (inv countN (counter_inv b_cell) -∗
     na_inv logrel_nais count_resetN ([∗ list] a_i;w_i ∈ reset_prog;reset_instrs, a_i ↦ₐ w_i) -∗
     na_inv logrel_nais count_clsN
     ([[b_cls,e_cls]]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e counter_first; WCap RWX b_cell e_cell b_cell] ]]
  ∗ [[b_cls',e_cls']]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e linkc; WCap RWX b_cell e_cell b_cell] ]]
  ∗ [[b_cls'',e_cls'']]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; WCap pc_p pc_b pc_e linkc'; WCap RWX b_cell e_cell b_cell] ]]) -∗
     na_own logrel_nais ⊤ -∗
    interp (WCap E b_cls'' e_cls'' b_cls''))%I.
  Proof.
    iIntros (Hnp Hcont_incr Hcont_read Hvpc_counter Hcont_restc Hbe_cell) "#Hcounter_inv #Hincr #Hcls_inv HnaI".
    rewrite /interp fixpoint_interp1_eq. rewrite /enter_cond.
    iIntros (r') "". iNext. iModIntro. rewrite /interp_expr /=.
    iIntros "([Hr'_full #Hr'_valid] & Hregs' & HnaI)". iDestruct "Hr'_full" as %Hr'_full.
    pose proof (regmap_full_dom _ Hr'_full) as Hdom_r'.
    rewrite /interp_conf.

    iDestruct (na_inv_acc with "Hcls_inv HnaI") as ">(>(Hcls & Hcls' & Hcls'') & Hna & Hcls_close)";
      [auto..|].

    rewrite /registers_mapsto.
    rewrite -insert_delete_insert.
    iDestruct (big_sepM_insert with "Hregs'") as "[HPC Hregs']". by apply lookup_delete.
    destruct (Hr'_full r_t1) as [r1v ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs'") as "[Hr1 Hregs']".
      by rewrite lookup_delete_ne //.
    destruct (Hr'_full r_env) as [renvv ?].
    iDestruct (big_sepM_delete _ _ r_env with "Hregs'") as "[Hrenv Hregs']".
      by rewrite !lookup_delete_ne //.
    (* Run the closure activation code *)
    iApply (closure_activation_spec with "[- $HPC $Hr1 $Hrenv $Hcls'']");
      [done| |done|..].
    { intros ? [? ?]. constructor; try split; auto. }
    rewrite updatePcPerm_cap_non_E //;[].
    iIntros "(HPC & Hr1 & Hrenv & Hcls'')".
    (* close the invariant for the closure *)
    iDestruct ("Hcls_close" with "[Hcls Hcls' Hcls'' $Hna]") as ">Hna".
    { iNext. iFrame. }

    destruct (Hr'_full r_t0) as [r0v Hr0v].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs'") as "[Hr0 Hregs']".
      by rewrite !lookup_delete_ne // lookup_delete_ne //.

    iApply (reset_spec with "[$HPC $Hr0 $Hrenv $Hregs' $Hna $Hincr Hr1]");
      [|apply Hcont_restc|auto..].
    { eapply isCorrectPC_range_restrict; [apply Hvpc_counter|]. split;[|solve_addr].
      apply contiguous_between_bounds in Hcont_incr. apply contiguous_between_bounds in Hcont_read. solve_addr. }
    { rewrite !dom_delete_L Hdom_r'. clear. set_solver. }
    { iSplitL;[eauto|]. iSplit.
      - iExists _. iFrame "#".
      - iSplit; [unshelve iSpecialize ("Hr'_valid" $! r_t0 _ _ Hr0v); [done|]|].
        iFrame "Hr'_valid".
        iApply big_sepM_forall. iIntros (reg w Hlook).
        assert (reg ≠ r_t0);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ r_env);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ r_t1);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        assert (reg ≠ PC);[intro Hcontr;subst;rewrite lookup_delete in Hlook;inversion Hlook|rewrite lookup_delete_ne in Hlook;auto].
        iSpecialize ("Hr'_valid" $! reg _ H4 Hlook). iApply "Hr'_valid";auto.
    }
    { iNext. iIntros (?) "HH". iIntros (->). iApply "HH". eauto. }
  Qed.


  Definition countN : namespace := nroot .@ "awkN".
  Definition count_invN : namespace := countN .@ "inv".
  Definition count_incrN : namespace := countN .@ "incr".
  Definition count_readN : namespace := countN .@ "read".
  Definition count_resetN : namespace := countN .@ "reset".
  Definition count_clsN : namespace := countN .@ "cls".
  Definition count_env : namespace := countN .@ "env".

  Lemma counter_preamble_spec (f_m f_a offset_to_counter: Z) (r: Reg) pc_p pc_b pc_e
        ai a_first a_end b_link e_link a_link a_entry a_entry'
        mallocN b_m e_m assertN b_a a_flag e_a ai_counter counter_first counter_end a_move:

    isCorrectPC_range pc_p pc_b pc_e a_first a_end →
    contiguous_between ai a_first a_end →
    withinBounds b_link e_link a_entry = true →
    withinBounds b_link e_link a_entry' = true →
    (a_link + f_m)%a = Some a_entry →
    (a_link + f_a)%a = Some a_entry' →
    (a_first + counter_preamble_move_offset)%a = Some a_move →
    (a_move + offset_to_counter)%a = Some counter_first →
    isCorrectPC_range pc_p pc_b pc_e counter_first counter_end →
    contiguous_between ai_counter counter_first counter_end →
    up_close (B:=coPset) assertN ## ↑count_readN →
    up_close (B:=coPset) assertN ## ↑count_env →

    (* Code of the preamble *)
    counter_preamble f_m offset_to_counter ai

    (* Code of the counter example itself *)
    ∗ counter f_a ai_counter

    (** Resources for malloc and assert **)
    (* assume that a pointer to the linking table (where the malloc capa is) is at offset 0 of PC *)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_inv logrel_nais assertN (assert_inv b_a a_flag e_a)
    ∗ pc_b ↦ₐ (WCap RO b_link e_link a_link)
    ∗ a_entry ↦ₐ WCap E b_m e_m b_m
    ∗ a_entry' ↦ₐ WCap E b_a e_a b_a

    -∗
    interp_expr interp r (WCap pc_p pc_b pc_e a_first).
  Proof.
    rewrite /interp_expr /=.
    iIntros (Hvpc Hcont Hwb_malloc Hwb_assert Ha_entry Ha_entry' Ha_lea H_counter_offset Hvpc_counter Hcont_counter ? ?)
            "(Hprog & Hcounter & #Hinv_malloc & #Hinv_assert & Hpc_b & Ha_entry & Ha_entry')
             ([#Hr_full #Hr_valid] & Hregs & HnaI)".
    iDestruct "Hr_full" as %Hr_full.
    rewrite /full_map /interp_conf.

    (* put the code for the counter example in an invariant *)
    (* we separate the invariants into its tree functions *)
    iDestruct (contiguous_between_program_split with "Hcounter") as (incr_prog restc linkc)
                                                                   "(Hincr & Hcounter & #Hcont)";[apply Hcont_counter|].
    iDestruct "Hcont" as %(Hcont_incr & Hcont_restc & Heqappc & Hlinkrestc).
    iDestruct (contiguous_between_program_split with "Hcounter") as (read_prog reset_prog linkc')
                                                                   "(Hread & Hreset & #Hcont)";[apply Hcont_restc|].
    iDestruct "Hcont" as %(Hcont_read & Hcont_reset & Heqappc' & Hlinkrestc').
    iDestruct (big_sepL2_length with "Hincr") as %incr_length.
    iDestruct (big_sepL2_length with "Hread") as %read_length.
    iDestruct (big_sepL2_length with "Hreset") as %reset_length.

    iDestruct (na_inv_alloc logrel_nais _ count_incrN with "Hincr") as ">#Hincr".
    iDestruct (na_inv_alloc logrel_nais _ count_readN with "Hread") as ">#Hread".
    iDestruct (na_inv_alloc logrel_nais _ count_resetN with "Hreset") as ">#Hreset".

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
    assert (isCorrectPC_range pc_p pc_b pc_e a_first a_malloc_end) as Hvpc1.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest). clear; solve_addr. }
    assert (isCorrectPC_range pc_p pc_b pc_e a_malloc_end a_end) as Hvpc2.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_malloc). clear; solve_addr. }
    rewrite -/(malloc _ _ _).
    iApply (wp_wand with "[-]").
    iApply (malloc_spec with "[- $HPC $Hmalloc $Hpc_b $Ha_entry $Hr0 $Hregs $Hinv_malloc $HnaI]");
      [apply Hvpc1|eapply Hcont_malloc|eapply Hwb_malloc|eapply Ha_entry| |auto|lia|..].
    { rewrite !dom_delete_L Hdom_r difference_difference_l_L //. }
    iNext. iIntros "(HPC & Hmalloc & Hpc_b & Ha_entry & HH & Hr0 & HnaI & Hregs)".
    iDestruct "HH" as (b_cell e_cell Hbe_cell) "(Hr1 & Hcell)".
    iDestruct (region_mapsto_single with "Hcell") as (cellv) "(Hcell & _)". revert Hbe_cell; clear; solve_addr.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    2: { iIntros (?) "[HH | ->]". iApply "HH". iIntros (Hv). inversion Hv. }

    destruct ai_rest as [| a l]; [by inversion Hlength|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest) as ->.
    (* store_z r_t1 0 *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hr1 $Hi $Hcell]");
      [apply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|
       iContiguous_next Hcont_rest 0|..]; auto.
    { apply le_addr_withinBounds; revert Hbe_cell; clear; solve_addr. }
    iEpilogue "(HPC & Hprog_done & Hr1 & Hb_cell)". iCombine "Hprog_done" "Hmalloc" as "Hprog_done".
    (* move_r r_t2 r_t1 *)
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr2 Hregs]".
      by rewrite lookup_insert. rewrite delete_insert_delete.
    destruct l as [| a_move' l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg _ _ _ _ _ _ _ r_t2 _ r_t1 with "[$HPC $Hi $Hr1 $Hr2]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 1|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t1 PC *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 2|..].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t8 r_t2 *)
    assert (is_Some (r !! r_t8)) as [w8 Hrt8].
    { apply elem_of_dom. rewrite Hdom_r. apply all_registers_s_correct. }
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]".
    { rewrite lookup_delete_ne;[|by auto]. rewrite !lookup_insert_ne;auto; rewrite !lookup_delete_ne;auto. eauto. }
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t8 $Hr2]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 3|..].
    iEpilogue "(HPC & Hi & Hr_t8 & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert].
    (* move_r r_t9 r_t1 *)
    assert (is_Some (r !! r_t9)) as [w9 Hrt9].
    { apply elem_of_dom. rewrite Hdom_r. apply all_registers_s_correct. }
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t8 Hregs]".
    { rewrite lookup_insert_ne;[|by auto]. rewrite lookup_delete_ne;auto. rewrite !lookup_insert_ne;auto; rewrite !lookup_delete_ne;auto. eauto. }
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t8 $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 4|..].
    iEpilogue "(HPC & Hi & Hr_t8 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert].
    (* lea_z r_t1 offset_to_awkward *)
    assert (a_move' = a_move) as ->.
    { assert ((a_first + (length ai_malloc + 2))%a = Some a_move') as HH.
      { rewrite Hai_malloc_len /= in Hlink |- *.
        generalize (contiguous_between_incr_addr_middle _ _ _ 0 2 _ _ Hcont_rest eq_refl eq_refl).
        revert Hlink; clear; solve_addr. }
      revert HH Ha_lea. rewrite Hai_malloc_len. cbn. clear.
      unfold counter_preamble_move_offset. solve_addr. }
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ counter_first with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 5
       |assumption|done|..].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* crtcls *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls ai_rest a_crtcls_end) "(Hcrtcls & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 6%nat _ _ _ Hcont_rest eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_;_;_]). 2: eapply Hcont_rest.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls & Hcont_rest' & Heqapp' & Hlink').
    assert (a_malloc_end <= f3)%a as Ha1_after_malloc.
    { eapply contiguous_between_middle_bounds'. apply Hcont_rest. repeat constructor. }
    iApply (wp_wand with "[-]").
    iApply (crtcls_spec with "[- $HPC $Hcrtcls $Hpc_b $Ha_entry $Hr0 $Hregs $Hr1 $Hr2 $HnaI $Hinv_malloc]");
      [|apply Hcont_crtcls|apply Hwb_malloc|apply Ha_entry| |done|auto|..].
    { eapply isCorrectPC_range_restrict. apply Hvpc2. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest'. }
    { rewrite !dom_insert_L dom_delete_L !dom_insert_L !dom_delete_L Hdom_r.
      clear. set_solver-. }
    2: { iIntros (?) "[ H | -> ]". iApply "H". iIntros (HC). congruence. }
    iNext. iIntros "(HPC & Hcrtcls & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cls e_cls Hbe_cls) "(Hr1 & Hbe_cls & Hr0 & Hr2 & HnaI & Hregs)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest'.
    (* register map cleanup *)
    rewrite delete_insert_ne;auto. repeat (rewrite (insert_commute _ r_t3);[|by auto]). rewrite insert_insert.
    repeat (rewrite (insert_commute _ r_t5);[|by auto]). rewrite -delete_insert_ne;auto. rewrite (insert_commute _ r_t5);auto. rewrite insert_insert.
    repeat (rewrite -(insert_commute _ r_t9);auto).  repeat (rewrite -(insert_commute _ r_t8);auto).

    assert (isCorrectPC_range pc_p pc_b pc_e a_crtcls_end a_end) as Hvpc3.
    { eapply isCorrectPC_range_restrict. apply Hvpc2.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest').
      revert Ha1_after_malloc Hlink'. clear; solve_addr. }
    (* move r_t10 r_t1 *)
    assert (is_Some (r !! r_t10)) as [w10 Hrt10].
    { apply elem_of_dom. rewrite Hdom_r. apply all_registers_s_correct. }
    iDestruct (big_sepM_delete _ _ r_t10 with "Hregs") as "[Hr_t10 Hregs]".
    { rewrite !lookup_insert_ne;auto. rewrite lookup_delete_ne;[|by auto]. rewrite !lookup_insert_ne;auto; rewrite !lookup_delete_ne;auto. eauto. }
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest'|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest') as ->.
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest'|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t10 $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end a_end|iContiguous_next Hcont_rest' 0|..].
    iEpilogue "(HPC & Hi & Hr_t10 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t10 with "[$Hregs $Hr_t10]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert].
    (* move r_t2 r_t8 *)
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]".
    { rewrite lookup_insert_ne;auto. apply lookup_insert. }
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest'|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr2 $Hr_t8]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end a_end|iContiguous_next Hcont_rest' 1|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr_t8)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert insert_commute;auto;rewrite insert_insert].
    (* move r_t1 r_t9 *)
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t9 Hregs]".
    { rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne;auto. apply lookup_insert. }
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest'|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr1 $Hr_t9]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end a_end|iContiguous_next Hcont_rest' 2|..].
    iEpilogue "(HPC & Hi & Hr1 & Hr_t9)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t9]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert !(insert_commute _ _ r_t9);auto].
    rewrite insert_insert.
    (* lea r_t1 offset_to_counter + length incr_instrs *)
    assert ((a_move + (offset_to_counter + (length incr_instrs)))%a = Some linkc) as H_counter_offset'.
    { revert Hlinkrestc H_counter_offset incr_length. clear. intros. solve_addr. }
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ linkc with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end a_end|iContiguous_next Hcont_rest' 3|assumption|done|..].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* crtcls *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls' ai_rest' a_crtcls_end') "(Hcrtcls' & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 4%nat _ _ _ Hcont_rest' eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_]). 2: eapply Hcont_rest'.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls' & Hcont_rest'' & Heqapp'' & Hlink'').
    assert (a_crtcls_end <= f7)%a as Ha1_after_crtcls.
    { eapply contiguous_between_middle_bounds'. apply Hcont_rest'. repeat constructor. }
    iApply (wp_wand with "[-]").
    iApply (crtcls_spec with "[- $HPC $Hcrtcls' $Hpc_b $Ha_entry $Hr0 $Hregs $Hr1 $Hr2 $HnaI $Hinv_malloc]");
      [|apply Hcont_crtcls'|apply Hwb_malloc|apply Ha_entry| |done|auto|..].
    { eapply isCorrectPC_range_restrict. apply Hvpc3. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest''. }
    { rewrite !dom_insert_L dom_delete_L !dom_insert_L !dom_delete_L Hdom_r.
      clear. set_solver-. }
    2: { iIntros (?) "[ H | -> ]". iApply "H". iIntros (HC). congruence. }
    iNext. iIntros "(HPC & Hcrtcls' & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cls' e_cls' Hbe_cls') "(Hr1 & Hbe_cls' & Hr0 & Hr2 & HnaI & Hregs)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest''.
    (* register map cleanup *)
    repeat (rewrite (insert_commute _ _ r_t3);[|by auto]);rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t4);[|by auto]);rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t6);[|by auto]);rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t7);[|by auto]);rewrite insert_insert.
    do 2 (rewrite delete_insert_ne;auto). repeat (rewrite (insert_commute _ _ r_t5);[|by auto]);rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t4);[|by auto]);rewrite insert_insert.

    assert (isCorrectPC_range pc_p pc_b pc_e a_crtcls_end' a_end) as Hvpc4.
    { eapply isCorrectPC_range_restrict. apply Hvpc3.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest'').
      revert Ha1_after_malloc Ha1_after_crtcls Hlink'' Hlink'. clear; solve_addr. }
    (* move r_t11 r_t1 *)
    assert (is_Some (r !! r_t11)) as [w11 Hrt11].
    { apply elem_of_dom. rewrite Hdom_r. apply all_registers_s_correct. }
    iDestruct (big_sepM_delete _ _ r_t11 with "Hregs") as "[Hr_t11 Hregs]".
    { rewrite !lookup_insert_ne;auto.  rewrite !lookup_delete_ne;auto. eauto. }
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest''|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest'') as ->.
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest''|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t11 $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|iContiguous_next Hcont_rest'' 0|..].
    iEpilogue "(HPC & Hi & Hr_t11 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t11 with "[$Hregs $Hr_t11]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert].
    (* move r_t2 r_t8 *)
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]".
    { repeat (rewrite lookup_insert_ne;[|by auto]). apply lookup_insert. }
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest''|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr2 $Hr_t8]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|iContiguous_next Hcont_rest'' 1|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr_t8)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert !(insert_commute _ _ r_t8);auto;rewrite insert_insert].
    (* move r_t1 r_t9 *)
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t9 Hregs]".
    { repeat (rewrite lookup_insert_ne;[|by auto]). apply lookup_insert. }
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest''|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr1 $Hr_t9]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|iContiguous_next Hcont_rest'' 2|..].
    iEpilogue "(HPC & Hi & Hr1 & Hr_t9)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t9]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert !(insert_commute _ _ r_t9);auto;rewrite insert_insert].
    (* lea r_t1 offset_to_counter + length incr + length read *)
    assert ((a_move + (offset_to_counter + (length incr_instrs) + (length (read_instrs 0))))%a = Some linkc') as H_counter_offset''.
    { revert read_length H_counter_offset' Hlinkrestc' Hlinkrestc H_counter_offset incr_length. clear. intros. solve_addr. }
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest''|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ linkc' with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|iContiguous_next Hcont_rest'' 3|assumption|done|..].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* crtcls *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls'' ai_rest'' a_crtcls_end'') "(Hcrtcls'' & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 4%nat _ _ _ Hcont_rest'' eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_]). 2: eapply Hcont_rest''.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls'' & Hcont_rest''' & Heqapp''' & Hlink''').
    assert (a_crtcls_end' <= f11)%a as Ha1_after_crtcls'.
    { eapply contiguous_between_middle_bounds'. apply Hcont_rest''. repeat constructor. }
    iApply (wp_wand with "[-]").
    iApply (crtcls_spec with "[- $HPC $Hcrtcls'' $Hpc_b $Ha_entry $Hr0 $Hregs $Hr1 $Hr2 $HnaI $Hinv_malloc]");
      [|apply Hcont_crtcls''|apply Hwb_malloc|apply Ha_entry| |done|auto|..].
    { eapply isCorrectPC_range_restrict. apply Hvpc4. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest'''. }
    { rewrite !dom_insert_L !dom_delete_L Hdom_r.
      clear. set_solver-. }
    2: { iIntros (?) "[ H | -> ]". iApply "H". iIntros (HC). congruence. }
    iNext. iIntros "(HPC & Hcrtcls'' & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cls'' e_cls'' Hbe_cls'') "(Hr1 & Hbe_cls'' & Hr0 & Hr2 & HnaI & Hregs)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest'''.
    (* register map cleanup *)
    repeat (rewrite (insert_commute _ _ r_t3);[|by auto]);rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t4);[|by auto]);rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t6);[|by auto]);rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t7);[|by auto]);rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t5);[|by auto]);rewrite insert_insert.

    (* FINAL CLEANUP BEFORE RETURN *)
    assert (isCorrectPC_range pc_p pc_b pc_e a_crtcls_end'' a_end) as Hvpc5.
    { eapply isCorrectPC_range_restrict. apply Hvpc4.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest''').
      revert Ha1_after_malloc Ha1_after_crtcls Ha1_after_crtcls' Hlink''' Hlink'' Hlink'. clear; solve_addr. }
    destruct ai_rest'' as [| ? ai_rest'']; [by inversion Hlength_rest'''|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest''') as ->.
    (* move r_t2 r_t10 *)
    rewrite !(insert_commute _ _ r_t10);auto.
    iDestruct (big_sepM_delete _ _ r_t10 with "Hregs") as "[Hr_t10 Hregs]";[apply lookup_insert|].
    destruct ai_rest'' as [| ? ai_rest'']; [by inversion Hlength_rest'''|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr2 $Hr_t10]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end'' a_end|iContiguous_next Hcont_rest''' 0|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr_t10)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t10 0 *)
    destruct ai_rest'' as [| ? ai_rest'']; [by inversion Hlength_rest'''|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t10]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end'' a_end|iContiguous_next Hcont_rest''' 1|..].
    iEpilogue "(HPC & Hi & Hr_t10)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t10 with "[$Hregs $Hr_t10]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert insert_insert].
    (* move r_t3 r_t11 *)
    rewrite !(insert_commute _ _ r_t11);auto.
    iDestruct (big_sepM_delete _ _ r_t11 with "Hregs") as "[Hr_t11 Hregs]";[apply lookup_insert|].
    rewrite !(insert_commute _ _ r_t3);auto. rewrite delete_insert_ne;auto.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[apply lookup_insert|].
    destruct ai_rest'' as [| ? ai_rest'']; [by inversion Hlength_rest'''|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t3 $Hr_t11]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end'' a_end|iContiguous_next Hcont_rest''' 2|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t11)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t11 0 *)
    destruct ai_rest'' as [| ? ai_rest'']; [by inversion Hlength_rest'''|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t11]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end'' a_end|iContiguous_next Hcont_rest''' 3|..].
    iEpilogue "(HPC & Hi & Hr_t11)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert insert_insert].
    rewrite -delete_insert_ne;auto.
    iDestruct (big_sepM_insert _ _ r_t11 with "[$Hregs $Hr_t11]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert].
    rewrite insert_commute;auto. rewrite insert_insert.
    (* move r_t8 0 *)
    destruct ai_rest'' as [| ? ai_rest'']; [by inversion Hlength_rest'''|].
    iPrologue "Hprog".
    rewrite !(insert_commute _ _ r_t8);auto.
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]";[apply lookup_insert|].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t8]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end'' a_end|iContiguous_next Hcont_rest''' 4|..].
    iEpilogue "(HPC & Hi & Hr_t8)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert insert_insert].
    (* move r_t9 0 *)
    destruct ai_rest'' as [| ? ai_rest'']; [by inversion Hlength_rest'''|].
    iPrologue "Hprog".
    rewrite !(insert_commute _ _ r_t9);auto.
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t8 Hregs]";[apply lookup_insert|].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t8]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end'' a_end|iContiguous_next Hcont_rest''' 5|..].
    iEpilogue "(HPC & Hi & Hr_t9)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t9]") as "Hregs";[apply lookup_delete|rewrite insert_delete_insert insert_insert].


    (* WE WILL NOW PREPARE THΕ JUMP *)
    iCombine "Hbe_cls'" "Hbe_cls''" as "Hbe_cls'".
    iCombine "Hbe_cls" "Hbe_cls'" as "Hbe_cls".
    iDestruct (na_inv_alloc logrel_nais _ count_clsN with "Hbe_cls") as ">#Hcls_inv".

    (* in preparation of jumping, we allocate the counter invariant *)
    iDestruct (inv_alloc countN _ (counter_inv b_cell) with "[Hb_cell]") as ">#Hcounter_inv".
    { iNext. rewrite /counter_inv. iExists _. iFrame. auto. }
    (* we also allocate a non atomic invariant for the environment table *)
    iMod (na_inv_alloc logrel_nais _ count_env
                       (pc_b ↦ₐ WCap RO b_link e_link a_link ∗ a_entry' ↦ₐ WCap E b_a e_a b_a)%I
            with "[$Ha_entry' $Hpc_b]") as "#Henv".

    (* jmp *)
    destruct ai_rest'' as [| ? ai_rest'']; [|by inversion Hlength_rest'''].
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply decode_encode_instrW_inv|iCorrectPC a_crtcls_end'' a_end|..].

    (* the current state of registers is valid *)
    iAssert (interp (WCap E b_cls e_cls b_cls))%I as "#Hvalid_cls".
    { iApply (incr_closure_valid with "Hcounter_inv Hincr Hcls_inv");auto.
      apply Hvpc_counter. apply Hcont_restc. }

    iAssert (interp (WCap E b_cls' e_cls' b_cls'))%I as "#Hvalid_cls'".
    { iApply (read_closure_valid with "Hcounter_inv Hread Hcls_inv Henv Hinv_assert");auto.
      apply Hcont_incr. apply Hvpc_counter. apply Hcont_reset. solve_ndisj. }

    iAssert (interp (WCap E b_cls'' e_cls'' b_cls''))%I as "#Hvalid_cls''".
    { iApply (reset_closure_valid with "Hcounter_inv Hreset Hcls_inv");auto.
      apply Hcont_incr. apply Hcont_read. apply Hvpc_counter. apply Hcont_reset. }

    unshelve iPoseProof ("Hr_valid" $! r_t0 _ _ Hr0) as "#Hr0_valid". done.

    (* use the continuation in rt0 *)
    iDestruct (jmp_to_unknown with "Hr0_valid") as "Hcont".

    (* prepare the continuation *)
    iEpilogue "(HPC & Hi & Hr0)". iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* Put the registers back in the map *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete //. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr0]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne // lookup_delete //. }
    repeat (rewrite -(delete_insert_ne _ r_t2) //;[]). rewrite insert_delete_insert.
    repeat (rewrite -(delete_insert_ne _ r_t1) //;[]). rewrite insert_delete_insert.
    repeat (rewrite -(delete_insert_ne _ r_t0) //;[]). rewrite insert_delete_insert.
    match goal with |- context [ ([∗ map] k↦y ∈ ?r, _)%I ] => set r'' := r end.
    iApply "Hcont"; cycle 1.
    { iFrame. iApply big_sepM_sep. iFrame "Hregs".
      repeat (iApply big_sepM_insert_2; cbn beta;
              [first [done | by rewrite /= !fixpoint_interp1_eq // ]|]).
      iApply big_sepM_intro. iIntros "!>" (r' ? Hr').
      eapply lookup_delete_Some in Hr' as [? Hr'].
      unshelve iSpecialize ("Hr_valid" $! r' _ _ Hr'). by auto. done. }
    { iPureIntro. rewrite !dom_insert_L dom_delete_L Hdom_r. set_solver+. }
  Qed.

End counter_example_preamble.
