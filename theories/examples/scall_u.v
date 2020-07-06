From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel stack_macros_helpers stack_macros stack_macros_u.
From cap_machine.rules Require Import rules_StoreU_derived rules_LoadU_derived rules_PromoteU_derived.

Section scall.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* Macro for stack calling when the stack capability is uninitialized. Note that the prologue and epilogue does not include storing and loading private state on the stack. *)

  (* helper lemma for the length of the registers *)
  Ltac iRegNotEq Hne :=
    repeat (apply not_elem_of_cons in Hne;
            (let Hneq := fresh "Hneq" in destruct Hne as [Hneq Hne])); auto.

  Definition scallU_prologue_instrs epilogue_off r1 :=
    (* push activation code *)
    [pushU_z_instr r_stk w_1;
    pushU_z_instr r_stk w_2_U;
    pushU_z_instr r_stk w_3;
    pushU_z_instr r_stk w_4a;
    pushU_z_instr r_stk w_4b_U; (* Note that there is one fewer instruction here than in the non-initialized case, cause we store with an offset *)
    (* push old pc *)
    move_r r_t1 PC;
    lea_z r_t1 epilogue_off;
    pushU_r_instr r_stk r_t1;
    (* push stack pointer *)
    pushU_r_instr r_stk r_stk; (* Note that the stored r_stk will not be able to read itself, but that should not be a problem. *)
    (* set up protected return pointer *)
    (* since a URWLX capability cannot be made into an E, we have to promote r_t0 first *)
    move_r r_t0 r_stk;
    promoteU r_t0;
    lea_z r_t0 (-7)%Z;
    restrict_z r_t0 (local_e);
    (* restrict stack capability *)
    geta r_t1 r_stk;
    gete r_t2 r_stk;
    subseg_r_r r_stk r_t1 r_t2] ++
    (* don't clear the unused part of the stack - just clear the registers *)
    rclear_instrs (list_difference all_registers [PC;r_stk;r_t0;r1]).

  (* Tactic for destructing a list into elements *)
  Ltac destruct_list l :=
    match goal with
    | H : strings.length l = _ |- _ =>
      let a := fresh "a" in
      let l' := fresh "l" in
      destruct l as [|a l']; [inversion H|];
      repeat (let a' := fresh "a" in
              destruct l' as [|a' l'];[by inversion H|]);
      destruct l'; [|by inversion H]
    end.

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

  Ltac iPrologueCore l Hl prog :=
    destruct l; [by inversion Hl|];
    iDestruct prog as "[Hinstr Hprog]".

  Ltac iPrologue l Hl prog :=
    iPrologueCore l Hl prog ;
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogueCore intro_ptrn instr prog :=
    iNext; iIntros intro_ptrn; iSimpl;
    iCombine instr prog as prog.

  Ltac iEpilogue intro_ptrn instr prog :=
    iEpilogueCore intro_ptrn instr prog;
    iApply wp_pure_step_later;auto;iNext.

  Definition scallU_prologue (a : list Addr) p epilogue_off r1 :=
    ([∗ list] a_i;w_i ∈ a;(scallU_prologue_instrs epilogue_off r1), a_i ↦ₐ[p] w_i)%I.

  Ltac iContiguous_bounds i j :=
    eapply contiguous_between_middle_bounds' with (a0 := i) (an := j);
    [ eauto | cbn; solve [ repeat constructor ] ].

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_bounds_withinBounds a0 an :=
    apply isWithinBounds_bounds_alt' with a0 an; auto; [];
    iContiguous_bounds a0 an.

  Lemma single_instr_extract a i j instr prog p' :
    contiguous_between a i j →
    ([∗ list] a_i;w_i ∈ a; (instr :: prog), a_i ↦ₐ[p'] w_i) -∗
    ∃ a' a_rest,
      (( i ↦ₐ[p'] instr) ∗
       [∗ list] a_i;w_i ∈ a'; prog, a_i ↦ₐ[p'] w_i) ∗
       ⌜ a = i :: a'
         ∧ (i + 1 = Some a_rest)%a
         ∧ contiguous_between a' a_rest j ⌝.
  Proof.
    intros. iIntros "HH".
    iDestruct (big_sepL2_length with "HH") as %Hlength.
    destruct a; [ by inversion Hlength |].
    rewrite big_sepL2_cons.
    set (H' := H). apply contiguous_between_cons_inv_first in H'; subst i.
    apply contiguous_between_cons_inv in H as (_ & (a' & (Hpp & H))).
    iExists a0, a'; auto.
  Qed.

  Ltac iPush_z prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let Ha1 := fresh "Ha1" in
    let Ha := fresh "Ha" in
    iDestruct (single_instr_extract with prog) as (a_rest cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha);
    iApply (pushU_z_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha"; eauto;
    clear Ha1; last iRename "Hprog" into prog.

  Lemma scallU_prologue_spec
        (* adress arithmetic *) a_r_adv b_r_adv a_cont
        (* scall parameters *) a a_first p' epilogue_off r1
        (* program counter *) p g b e
        (* stack capability *) b_r e_r a_r
        (* continuation *) φ
        (* register contents *) rmap
        (* local stack *) ws_own :
    isCorrectPC_range p g b e a_first a_cont →
    withinBounds ((URWLX, Local), b_r, e_r, a_r) = true ->
    withinBounds ((URWLX, Local), b_r, e_r, b_r_adv) = true → (* TODO: Works with b_r_adv -1? - nothing written to this address *)
    (0%a <= e_r)%Z ∧ (0%a <= b_r)%Z → (* This assumption can be removed once we update addresses to be nats *)
    contiguous_between a a_first a_cont →
    PermFlows p p' →
    r1 ∉ [PC;r_stk;r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6] →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_stk; r1 ]} →

    (a_r + 6)%a = Some a_r_adv →
    (a_r + 7)%a = Some b_r_adv →
    (a_first + (5 + epilogue_off))%a = Some a_cont →
    (0 ≤ epilogue_off)%Z →

    (▷ scallU_prologue a p' epilogue_off r1
   ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a_first)
   ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Local),b_r,e_r,a_r)
   ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
   ∗ ▷ ([[a_r, b_r_adv]]↦ₐ[RWLX][[ws_own]]) (* local stack - note that the perm here is NOT unitialized, as the definition of interp1 has a promote_permission in there *)
   (* No ownership of adversarial stack here; no clearing required *)
   ∗ ▷ (PC ↦ᵣ inr (p,g,b,e,a_cont)
            ∗ r_stk ↦ᵣ inr ((URWLX,Local),b_r_adv,e_r,b_r_adv)
            ∗ r_t0 ↦ᵣ inr ((E,Local),b_r,b_r_adv,a_r) (* Note that this capbility does not grant permissions up to the end of the stack anymore *)
            ∗ ([∗ map] r_i↦_ ∈ delete r_t0 rmap, r_i ↦ᵣ inl 0%Z)
            ∗ [[ a_r, b_r_adv ]]↦ₐ[RWLX][[ [inl w_1;
                                             inl w_2_U;
                                             inl w_3;
                                             inl w_4a;
                                             inl w_4b_U;
                                             inr (p,g,b,e,a_cont);
                                             inr (URWLX,Local,b_r,e_r,a_r_adv)] ]] (* local stack *)
            ∗ scallU_prologue a p' epilogue_off r1 -∗
            WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc1 Hwb1 Hwb2 Hnonzero Ha Hfl Hne Hrmap Hadva Hadvb Hcont Heoff)
            "(>Hprog & >HPC & >Hr_stk & >Hregs & >Hgen_reg & Hφ)".
    assert (withinBounds ((RWLX, Local), b_r, e_r, a_r_adv) = true) as Hwb3.
    { apply andb_true_iff.
      apply andb_true_iff in Hwb2 as [Hba Hae]. apply andb_true_iff in Hwb1 as [Hbact Hacte].
      revert Hae Hba Hbact Hacte; repeat rewrite Z.leb_le Z.ltb_lt; intros Hae Hba Hbact Hacte.
      assert (a_r_adv ≤ b_r_adv)%Z as Hle;[apply incr_addr_le with a_r 6 7;auto;lia|].
      assert (a_r ≤ a_r_adv)%Z as Hle';[apply next_le_i with 6;auto;lia|]. lia.
    }
    assert (Hin_rmap: ∀ r, r ∈ [r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6] → is_Some (rmap !! r)).
    { intros r Hr. rewrite elem_of_gmap_dom Hrmap elem_of_difference.
      split; [apply all_registers_s_correct|]. rewrite !not_elem_of_union !not_elem_of_singleton.
      rewrite !elem_of_cons elem_of_nil in Hr |- * => Hr. split. naive_solver.
      intros <-. apply Hne. rewrite !elem_of_cons elem_of_nil. repeat destruct Hr as [|Hr]; tauto. }

    rewrite /scallU_prologue.
    (* prepare the local stack for storing the activation record, old PC and old SP *)
    assert (∃ a1 a2 a3 a4 a5 a6 a7, [a1;a2;a3;a4;a5;a6;a7] = region_addrs a_r b_r_adv)
      as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & Hstack_eq).
    {
      apply (incr_addr_region_size_iff a_r _ 6) in Hadva as [Hle Hsize].
      assert (length (region_addrs a_r b_r_adv) = 7) as Hlen.
      { rewrite region_addrs_length. rewrite /region_size in Hsize |- *. solve_addr. }
      rewrite /region_mapsto.
      destruct_list (region_addrs a_r b_r_adv).
      exists a0,a1,a2,a3,a4,a5,a6. done.
    }
    assert (contiguous_between (region_addrs a_r b_r_adv) a_r b_r_adv) as Hcontiguous.
    { apply contiguous_between_of_region_addrs; auto. solve_addr. }
    rewrite -Hstack_eq in Hcontiguous.
    rewrite /region_mapsto -Hstack_eq.
    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    iDestruct (big_sepL2_length with "Hgen_reg") as %Hlength'.
    assert ((region_addrs a_r b_r_adv) !! 0 = Some a_r) as Hfirst_stack.
    { apply region_addrs_first. revert Hadvb; clear. solve_addr. }
    rewrite -Hstack_eq /= in Hfirst_stack. inversion Hfirst_stack; subst. clear Hfirst_stack.
    assert(PermFlows URWLX RWLX) as Hfl'. by rewrite /PermFlows.
    (* PUSH ACTIVATION RECORD *)
    (* push w_1 *)
    destruct ws_own as [|w ws_own];[inversion Hlength'|]; iDestruct "Hgen_reg" as "[Ha Hstack_own]".
    iPush_z "Hprog"; [| iContiguous_next Hcontiguous 0|].
    { iCorrectPC a_first a_cont. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iRename "Hpush" into "Hi". iRename "Ha" into "Hw1".
    (* push w_2_U *)
    destruct ws_own as [|w1 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog"; [| |iContiguous_next Hcontiguous 1|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hw1" as "Hact_frame".
    (* push w_3 *)
    destruct ws_own as [|w2 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 2|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    (* push w_4a *)
    destruct ws_own as [|w3 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 3|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    (* push w_4b_U *)
    destruct ws_own as [|w4 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 4|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    clear Ha4 Ha3 Ha0.
    (* PUSH OLD PC *)
    (* some general purpose registers *)
    assert (is_Some (rmap !! r_t0)) as [rv0 ?] by (apply Hin_rmap; repeat constructor).
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hrt0 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t1)) as [rv1 ?] by (apply Hin_rmap; repeat constructor).
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hrt1 Hregs]".
      by rewrite lookup_delete_ne //.
    (* move r_t1 PC *)
    do 2 (destruct a_rest; [inversion Hlength|]).
    match goal with H: contiguous_between (?a' :: _) ?a _ |- _ =>
      generalize (contiguous_between_cons_inv_first _ a a' _ H); intro; subst a end.
    iDestruct "Hprog" as "[Hinstr Hprog]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_move_success_reg_fromPC with "[$Hinstr $Hrt1 $HPC]");
      [apply decode_encode_instrW_inv|apply Hfl| |iContiguous_next Ha 5|auto|].
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hi".
    (* lea r_t1 epilogue_off *)
    iPrologue a_rest Hlength "Hprog".
    (* we first need to make some assertions about the increase of the address a *)
    assert ((a + epilogue_off)%a = Some a_cont) as Hepilogue.
    { rewrite -Hcont (addr_add_assoc _ a);[auto|].
      eapply (contiguous_between_incr_addr _ 5); eauto. }
    iApply (wp_lea_success_z with "[$Hinstr $Hr_t1 $HPC]");
      [apply decode_encode_instrW_inv|apply Hfl| |iContiguous_next Ha 6|apply Hepilogue|auto|..].
    { iCorrectPC a_first a_cont. }
    { eapply isCorrectPC_range_npE; eauto. iContiguous_bounds a_first a_cont. }
    { apply contiguous_between_length in Ha.
      apply isCorrectPC_range_perm in Hvpc1; [|revert Ha; clear; solve_addr].
      destruct Hvpc1 as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hi".
    (* PUSH R_T1 *)
    (* pushU r_stk r_t1 *)
    destruct ws_own;[inversion Hlength'|].
    iDestruct "Hstack_own" as "[Ha6 Hstk_own]".
    iPrologueCore a_rest Hlength "Hprog".
    iApply (pushU_r_spec with "[-]"); last iFrame "Hinstr Ha6 HPC Hr_stk Hr_t1"; eauto.
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    { iContiguous_next Ha 7. }
    { iContiguous_next Hcontiguous 5. }
    iEpilogueCore "(HPC & Hinstr & Hr_stk & Hr_t1 & Ha6)" "Hinstr" "Hi".
    iCombine "Ha6" "Hact_frame" as "Hact_frame".
    (* STORE OLD SP *)
    (* pushU r_stk r_stk *)
    destruct ws_own;[inversion Hlength'|].
    iDestruct "Hstk_own" as "[Ha7 Hstk_own]".
    iPrologueCore a_rest Hlength "Hprog".
    iApply (pushU_r_spec_same with "[-]"); last iFrame "Hinstr Ha7 HPC Hr_stk"; eauto.
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    { iContiguous_next Ha 8. }
    { eapply contiguous_between_last. exact Hcontiguous. auto. }
    iEpilogueCore "(HPC & Hinstr & Hr_stk & Ha7)" "Hinstr" "Hi".
    iCombine "Ha7" "Hact_frame" as "Hact_frame".
    (* PREPARE RETURN CAP *)
    (* move r_t0 r_stk *)
    iPrologue a_rest Hlength "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hinstr $Hrt0 $Hr_stk]");
      [apply decode_encode_instrW_inv|apply Hfl| |iContiguous_next Ha 9|auto|].
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_t0 & Hr_stk)" "Hinstr" "Hi".
    (* promoteU r_t0 *)
    iPrologue a_rest Hlength "Hprog".
    iApply (wp_promoteU_success with "[$HPC $Hinstr $Hr_t0]");
      [apply decode_encode_instrW_inv|apply Hfl| |auto |iContiguous_next Ha 10|].
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_t0)" "Hinstr" "Hi".
    assert ((min b_r_adv e_r) = b_r_adv) as ->.
    { apply withinBounds_le_addr in Hwb2 as [_ Hlt].
      unfold min. destruct (Addr_le_dec b_r_adv e_r); auto. destruct n.
      apply Z.lt_le_incl; auto.
    }
    (* lea r_t0 -7 *)
    (* assert that the activation frame starts at a_r *)
    iPrologue a_rest Hlength "Hprog".
    generalize (contiguous_between_last _ _ _ _ Hcontiguous eq_refl).
    match goal with |- (?a + _)%a = _ -> _ =>
      intro HH; assert (a = a_r_adv); [ revert HH Hadva Hadvb; clear; solve_addr |];
      subst a end.
    iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t0]");
      [apply decode_encode_instrW_inv|apply Hfl| |iContiguous_next Ha 11| |auto..].
    { iCorrectPC a_first a_cont. }
    { eapply invert_incr_addr in Hadvb. done.  }
    { by cbn. }
    iEpilogue "(HPC & Hinstr & Hr_t0)" "Hinstr" "Hi".
    (* restrict r_t0 (Local,E) *)
    iPrologue a_rest Hlength "Hprog".
    iApply (wp_restrict_success_z with "[$HPC $Hinstr $Hr_t0]");
      [apply decode_encode_instrW_inv|apply Hfl| |iContiguous_next Ha 12| |auto|auto|].
    { iCorrectPC a_first a_cont. }
    { rewrite decode_encode_permPair_inv. auto. }
    iEpilogue "(HPC & Hinstr & Hr_t0)" "Hinstr" "Hi".
    (* RESTRICT STACK CAP *)
    (* geta r_t1 r_stk *)
    iPrologue a_rest Hlength "Hprog".
    iApply (wp_Get_success with "[$HPC $Hinstr Hr_t1 Hr_stk]");
      [apply decode_encode_instrW_inv|eauto|apply Hfl| |iContiguous_next Ha 13|auto| |iSimpl|]; eauto.
    { iCorrectPC a_first a_cont. } { iFrame. }
    iEpilogue "(HPC & Hinstr & Hr_stk & Hr_t1)" "Hinstr" "Hi".
    (* gete r_t2 r_stk *)
    assert (is_Some (rmap !! r_t2)) as [rv2 ?] by (apply Hin_rmap; repeat constructor).
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]".
      by rewrite !lookup_delete_ne //.
    iPrologue a_rest Hlength "Hprog".
    iApply (wp_Get_success with "[$HPC $Hinstr Hr_t2 Hr_stk]");
      [apply decode_encode_instrW_inv| eauto | apply Hfl| |iContiguous_next Ha 14|auto| |iSimpl|]; eauto.
    { iCorrectPC a_first a_cont. } { iFrame. }
    iEpilogue "(HPC & Hinstr & Hr_stk & Hr_t2)" "Hinstr" "Hi".
    (* subseg r_stk r_t1 r_t2 *)
    assert (z_to_addr b_r_adv = Some b_r_adv) as Hb_r_adv.
    { destruct b_r_adv; rewrite /z_to_addr /=. destruct (Z_le_dec z MemNum); [|elim n; eapply Z.leb_le; auto].
      destruct (Z_le_dec 0 z); [|elim n; eapply Z.leb_le; auto].
      f_equal; by apply z_of_eq. }
    assert (z_to_addr e_r = Some e_r) as He_r.
    { destruct e_r; rewrite /z_to_addr /=. destruct (Z_le_dec z MemNum); [|elim n; eapply Z.leb_le; auto].
      destruct (Z_le_dec 0 z); [|elim n; eapply Z.leb_le; auto].
      f_equal; by apply z_of_eq. }

    (* Annoying exception here: the Prologue does not resolve automatically, as the length definition does not get unfolded automatically, which is in turn caused by the fact that coq cannot derive that the map over the list of registers that need to be cleared at the end is not empty. -> inversion on Hlength does not work *)
    iDestruct (contiguous_between_program_split with "[Hprog]") as (subseg_addrs rclear_addrs rclear_first) "(Hmclear & Hrclear & #Hcont)".
    { eapply contiguous_between_app with (k := a14)(a2 := (a14 :: a_rest)) in Ha as [_ Ha]. exact Ha.
      * simpl. do 15 (instantiate (1:= cons _ _)). instantiate (1 := []). simpl; eauto.
      * cbn.  eapply (contiguous_between_incr_addr _ 15); eauto.
    }
    { instantiate(H2:= [_]). unfold app; auto. }
    iDestruct "Hcont" as %(Hcont21 & Hcont22 & Happeq' & Hlink').
    assert (a14 <= rclear_first)%a as Harcl. by eapply contiguous_between_bounds;eauto.
    destruct subseg_addrs.
    { inversion Hcont21. rewrite H4 in Hlink'. cbn in Hlink'. destruct rclear_first. unfold incr_addr in Hlink'. simpl in Hlink'.  destruct (Z_le_dec (z + 1%nat)%Z MemNum); last by inversion Hlink'. inversion Hlink'. done. }
    apply contiguous_between_cons_inv_first in Hcont21; subst a15.

    iDestruct (big_sepL2_length with "Hmclear") as %Hlen.
    destruct subseg_addrs. 2: {cbn in Hlen. discriminate. } clear Hlen.

    iDestruct "Hmclear" as "[Hinstr _]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_subseg_success with "[$HPC $Hinstr $Hr_stk $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|apply Hfl| |eauto|auto|auto|..].
    { iCorrectPC a_first a_cont. }
    { rewrite !andb_true_iff !Z.leb_le. repeat split; try lia.
      eapply withinBounds_le_addr; eauto. }
    { exact Hlink'. }
    iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_t2 & Hr_stk)" "Hinstr" "Hi".

    (* RCLEAR *)
    iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
    rewrite map_length helper1 in Hrclear_length;[|iRegNotEq Hne|apply all_registers_correct].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs".
      repeat (rewrite lookup_delete_ne //;[]); apply lookup_delete.
      repeat (rewrite -delete_insert_ne //;[]); rewrite insert_delete.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs".
      repeat (rewrite lookup_delete_ne //;[]); apply lookup_delete.
      repeat (rewrite -delete_insert_ne //;[]); rewrite insert_delete.
    iApply (rclear_spec with "[- $Hregs]"); last (iFrame "HPC Hrclear").
    { eauto. }
    { apply not_elem_of_list; apply elem_of_cons; by left. }
    { destruct rclear_addrs; inversion Hcont22; eauto. inversion Hrclear_length. }
    { intros a' [Ha'1 Ha'2]. eapply Hvpc1. split; [| by auto].
      have: (a_first <= a14)%a by iContiguous_bounds a_first a_cont.
      have: (a14 <= rclear_first)%a by auto.
      revert Ha'1; clear; solve_addr. }
    { apply Hfl. }
    { rewrite !dom_insert_L list_to_set_difference -/all_registers_s.
      rewrite !dom_delete_L Hrmap !difference_difference_L !singleton_union_difference_L
              !all_registers_union_l.
      f_equal. revert Hne. clear. set_solver. }
    iNext. iIntros "(HPC & Hregs & Hrclear)".
    iApply "Hφ". rewrite decode_encode_permPair_inv. iFrame "HPC Hr_stk Hr_t0".
    iSplitL "Hregs".
    { iDestruct (big_sepM_dom with "Hregs") as "Hregs". iApply big_sepM_dom.
      rewrite big_opS_proper'. iApply "Hregs". reflexivity.
      rewrite !dom_insert_L !dom_delete_L Hrmap.
      rewrite !difference_difference_L !singleton_union_difference_L !all_registers_union_l.
      f_equal. revert Hne. clear. set_solver. }
    iSplitL "Hact_frame".
    { iDestruct "Hact_frame" as "(?&?&?&?&?&?&?)". by iFrame. }
    { rewrite Happeq'. repeat (iDestruct "Hi" as "(?&Hi)"). by iFrame. }
  Qed.

  Lemma scallU_epilogue_spec stack_own_b stack_own_e s_last stack_new rt1w rstkw
        (* reinstated PC *) pc_p pc_g pc_b pc_e pc_cont pc_next
        (* reinstated stack *) p_r g_r b_r e_r p_r'
        (* current PC *) p g φ :

    isCorrectPC_range p g b_r stack_own_e stack_own_b stack_own_e →
    withinBounds ((p_r, g_r), b_r, e_r, s_last) = true -> (* Extra hypothesis to anchor the value of s_last vs e_r, when we load through the stack pointer - TODO: this could be avoided by loading through the PC instead, but I reused the legacy code for now *)
    isU p_r = true → (* Stack capability is uninitialized *)
    PermFlows p p_r' ->
    PermFlows p_r p_r' ->
    (pc_cont + 1)%a = Some pc_next ->
    (stack_new + 1)%a = Some s_last ->
    (s_last + 1)%a = Some stack_own_e ->

    (▷ PC ↦ᵣ inr (p, g, b_r, stack_own_e, stack_own_b) (* only permission up to adv frame, i.e. stack_own_e *)
       ∗ ▷ r_t1 ↦ᵣ rt1w
       ∗ ▷ r_stk ↦ᵣ rstkw
       ∗ ▷ ([[stack_own_b,stack_own_e]]↦ₐ[p_r'][[
                [inl w_1; inl w_2_U; inl w_3; inl w_4a; inl w_4b_U;
                 inr (pc_p, pc_g, pc_b, pc_e, pc_cont);
                 inr (p_r, g_r, b_r, e_r, s_last)]
            ]]) (* activation frame *)
       ∗ ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, pc_next)
               ∗ r_stk ↦ᵣ inr (p_r, g_r, b_r, e_r, s_last)
               ∗ (∃ rt1w, r_t1 ↦ᵣ rt1w)
               ∗ [[stack_own_b,stack_own_e]]↦ₐ[p_r'][[
                    [inl w_1; inl w_2_U; inl w_3; inl w_4a; inl w_4b_U;
                     inr (pc_p, pc_g, pc_b, pc_e, pc_cont);
                     inr (p_r, g_r, b_r, e_r, s_last)]
                 ]] (* activation frame *) -∗
               WP Seq (Instr Executable) {{ φ }})
       ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hwb HUstk Hfl Hfl' Hnext Hstack1 Hstack2) "(>HPC & >Hr_t1 & >Hr_stk & >Hframe & Hφ)".
    rewrite /region_mapsto.
    iDestruct (big_sepL2_length with "Hframe") as %Hframe_length.
    set (l := region_addrs stack_own_b stack_own_e) in *.
    simpl in Hframe_length.
    assert (contiguous_between l stack_own_b stack_own_e) as Hcont.
    { eapply contiguous_between_of_region_addrs; eauto.
      rewrite region_addrs_length /region_size // in Hframe_length. solve_addr. }
    assert (stack_own_b + 7 = Some stack_own_e)%a as Hstack_bounds.
    { generalize (contiguous_between_length _ _ _ Hcont). cbn. by rewrite Hframe_length. }

    destruct l; [ by inversion Hframe_length |].
    (* move r_t1 PC *)
    iPrologue l Hframe_length "Hframe".
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). subst a.
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hinstr $Hr_t1]");
      [apply decode_encode_instrW_inv|apply Hfl| |iContiguous_next Hcont 0|auto|].
    { iCorrectPC stack_own_b stack_own_e. }
    iAssert (emp)%I as "Hframe_past";[done|].
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hframe_past".
    (* lea r_t1 6 *)
    iPrologue l Hframe_length "Hprog".
    assert ((stack_own_b + 6)%a = Some s_last) as Hincr.
    { revert Hstack_bounds Hframe_length Hstack2; clear; solve_addr. }
    iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t1]");
      [apply decode_encode_instrW_inv|apply Hfl| |iContiguous_next Hcont 1|apply Hincr|auto|..].
    { iCorrectPC stack_own_b stack_own_e. }
    { eapply isCorrectPC_range_npE; eauto. iContiguous_bounds stack_own_b stack_own_e. }
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hframe_past".
    (* load r_stk r_t1 *)
    iPrologue l Hframe_length "Hprog".
    do 3 (let a := fresh "a" in destruct l as [|a l]; [inversion Hframe_length|]). destruct l;[|inversion Hframe_length].
    iDestruct "Hprog" as "(Hinstr1 & Hinstr2 & Hinstr3 & Hlast & _)".
    (* fixme: tedious *)
    assert (a4 = s_last) as ->.
    { generalize (contiguous_between_last _ _ _ _ Hcont eq_refl).
      revert Hstack2; clear; solve_addr. }
    assert (a3 = stack_new) as ->.
    { generalize (contiguous_between_incr_addr_middle _ _ _ 5 1 _ _ Hcont eq_refl eq_refl).
      revert Hstack1 Hstack2; clear; solve_addr. }

    assert ((s_last =? a)%a = false) as Hne.
    { assert ((a + 4)%a = Some s_last) as Hincr'.
      { pose proof (contiguous_between_last _ _ _ _ Hcont eq_refl) as HH5.
        eapply (contiguous_between_incr_addr_middle _ _ _ 2 4 _ _ Hcont); auto. }
      apply Z.eqb_neq. revert Hincr'; clear; solve_addr. }
    iApply (wp_load_success with "[$HPC $Hinstr $Hr_stk $Hr_t1 Hlast]").
    apply decode_encode_instrW_inv. apply Hfl.
    iCorrectPC stack_own_b stack_own_e.
    { split.
      - unshelve epose proof (isCorrectPC_range_perm _ _ _ _ _ _ Hvpc _)
          as [ ? | [?|?] ]; [| destruct p; cbn; congruence ..].
        iContiguous_bounds stack_own_b stack_own_e.
      - eapply isCorrectPC_withinBounds. apply Hvpc.
        iContiguous_bounds stack_own_b stack_own_e. }
    { iContiguous_next Hcont 2. }
    rewrite Hne; iFrame. iPureIntro; apply Hfl.
    iEpilogue "(HPC & Hr_stk & Hinstr & Hr_t1 & Hlast)" "Hinstr" "Hframe_past".
    (* sub r_t1 0 1 *)
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success_z_z with "[$HPC Hr_t1 $Hinstr1]");
      [apply decode_encode_instrW_inv| | | apply Hfl | | iFrame;eauto|..]; eauto.
    assert ((a1 + 1)%a = Some a2) as ->;[iContiguous_next Hcont 3|]. eauto.
    { iCorrectPC stack_own_b stack_own_e. }
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hframe_past".
    (* loadu PC r_stk r_t1 *)
    iApply (wp_bind (fill [SeqCtx])).
      rewrite Hne.
    iApply ( wp_loadU_success_reg_to_PC with "[$HPC $Hr_t1 $Hr_stk $Hinstr2 $Hinstr3]");
      [apply decode_encode_instrW_inv|apply Hfl| apply Hfl'| | apply HUstk | | apply Hnext | apply Hstack1 | ..];auto.
    { iCorrectPC stack_own_b stack_own_e. }
    { rewrite /withinBounds. rewrite /withinBounds in Hwb. rewrite andb_true_iff. apply andb_true_iff in Hwb as [Hle Hlt]. split.
      * assert ((stack_own_b + 5)%a = Some stack_new) as Hso. solve_addr. apply next_le_i in Hso; last done.
        assert (( b_r <=? stack_own_b)%a).
        { assert (isCorrectPC (inr (p, g, b_r, stack_own_e, stack_own_b))) as HPCownb. iCorrectPC stack_own_b stack_own_e.  eapply isCorrectPC_withinBounds in HPCownb. rewrite /withinBounds in HPCownb. apply andb_true_iff in HPCownb; destruct HPCownb as [Hr1 _]. auto. }
        unfold leb_addr in *. rewrite Z.leb_le. apply Is_true_eq_true in H. apply Z.leb_le in H. eapply Z.le_trans; eauto.
      * assert ((stack_new <= s_last)%a). solve_addr. unfold leb_addr, le_addr in *.
        apply Z.ltb_lt in Hlt.  rewrite Z.ltb_lt. eapply Z.le_lt_trans; eauto.
    }
    iEpilogue "(HPC & Hinstr & Hr_stk & Hr_t1 & Hsn)" "Hinstr" "Hframe_past".
    iDestruct "Hframe_past" as "(Ha2 & Ha1 & Ha0 & Ha & Hstack_own_b & _)".
    iApply "Hφ". iFrame. cbn. iSplitL; eauto.
    Unshelve. all: auto.
  Qed.

End scall.
