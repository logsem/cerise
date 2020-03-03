From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel stack_macros.

Section scall.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  (* Macro for stack calling. Note that the prologue and epilogue does
     not include storing and loading private state on the stack. *)

  (* helper lemma for the length of the registers *)
  Ltac iRegNotEq Hne :=
    repeat (apply not_elem_of_cons in Hne;
            (let Hneq := fresh "Hneq" in destruct Hne as [Hneq Hne])); auto.

  Ltac iNotElemOfList :=
    repeat (apply not_elem_of_cons; split;[auto|]); apply not_elem_of_nil.

  Lemma gen_pur_reg_length r1 :
    r1 ∉ [PC;r_stk] →
    strings.length (list_difference all_registers [PC; r_stk; r1]) = RegNum - 1.
  Proof.
    intros Hne.
    assert (r1 ∈ all_registers) as Hr1;[apply all_registers_correct|].
    assert ([PC; r_stk; r1] = [PC; r_stk] ++ [r1]) as Heq; first done.
    rewrite Heq.
    rewrite list_difference_app.
    assert (r1 ∈ (list_difference all_registers [PC; r_stk])).
    { simpl.
      rewrite /all_registers in Hr1.
      (* apply elem_of_cons in Hr1 as [Hcontr | Hr1]. *)
      assert
        ([r_t0;r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11;
          r_t12; r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22;
          r_t23; r_t24; r_t25; r_t26; r_t27; r_t28; r_t29; r_t30; r_t31; PC] =
         [r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11;
          r_t12; r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22;
          r_t23; r_t24; r_t25; r_t26; r_t27; r_t28; r_t29; r_t30] ++ [r_t31; PC]) as Hreq; auto.
      rewrite Hreq in Hr1. clear Hreq.
      iRegNotEq Hne.
      apply elem_of_app in Hr1 as [Hr1 | Hcontr]; auto.
      apply elem_of_cons in Hcontr as [? | Hcontr]; first contradiction.
      apply elem_of_list_singleton in Hcontr; contradiction.
    }
    rewrite list_difference_length; auto.
    simpl.
    repeat (apply NoDup_cons; first discharge_not_or).
    apply NoDup_nil.
  Qed.

   Lemma gen_pur_reg_extract {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
    a ∉ l2 → a ∉ l1 ->
    list_difference (a :: l1) l2 =
    a :: list_difference l1 (a :: l2).
   Proof.
     revert l2. induction l1.
     - intros l2 Hl2 _. simpl. destruct (decide_rel elem_of a l2); done.
     - intros l2 Hl2 Hl1.
       apply not_elem_of_cons in Hl1 as [Hen Hnin].
       simpl.
       destruct (decide_rel elem_of a l2);[done|].
       destruct (decide_rel elem_of a0 l2).
       + destruct (decide_rel elem_of a0 (a :: l2));[apply elem_of_cons in e0 as [Hcontr | Hcontr]; try done|].
         ++ rewrite list_difference_skip; auto.
         ++ apply not_elem_of_cons in n0 as [_ Hcontr]. done.
       + destruct (decide_rel elem_of a0 (a :: l2));[apply elem_of_cons in e as [Hcontr | Hcontr]; try done|].
         rewrite list_difference_skip; auto.
   Qed.

   Lemma gen_pur_app r1 :
    r1 ∉ [PC;r_stk;r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6] →
    list_difference all_registers [PC; r_stk; r1] =
    r_t0 :: r_t1 :: r_t2 :: r_t3 :: r_t4 :: r_t5 :: r_t6 :: (list_difference all_registers [r_t0; r_t1;r_t2;r_t3;r_t4;r_t5;r_t6;PC; r_stk; r1]).
   Proof.
    intros Hne.
    iRegNotEq Hne.
    assert (r1 ∈ all_registers) as Hr1;[apply all_registers_correct|].
    repeat (rewrite gen_pur_reg_extract;[|iNotElemOfList|iNotElemOfList];f_equiv).
    assert ([r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; PC; r_stk; r1] = [r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6] ++ [PC; r_stk; r1]) as Happ;[auto|].
    rewrite Happ.
    rewrite list_difference_app.
    assert ((list_difference all_registers [r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6]) =
            [r_t7; r_t8; r_t9; r_t10; r_t11; r_t12; r_t13; r_t14; r_t15; r_t16; r_t17;
             r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24; r_t25; r_t26; r_t27; r_t28;
             r_t29; r_t30; r_t31;PC]) as ->;[auto|].
    do 7 (rewrite list_difference_skip;[|iNotElemOfList]). done.
   Qed.

   Lemma gen_pur_app' r1 :
    r1 ∉ [PC;r_stk;r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6] →
    list_difference all_registers [PC; r_stk; r_t0; r1] =
    r_t1 :: r_t2 :: r_t3 :: r_t4 :: r_t5 :: r_t6 :: (list_difference all_registers [r_t1;r_t2;r_t3;r_t4;r_t5;r_t6;PC; r_stk; r_t0; r1]).
   Proof.
    intros Hne.
    iRegNotEq Hne.
    assert (r1 ∈ all_registers) as Hr1;[apply all_registers_correct|].

    assert ([PC; r_stk; r_t0; r1] = [PC; r_stk; r_t0] ++ [r1]) as ->;[auto|].
    rewrite list_difference_app.
    assert ([r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; PC; r_stk; r_t0; r1] = [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6] ++ [PC; r_stk; r_t0; r1]) as Happ;[auto|].
    assert (list_difference all_registers [PC; r_stk; r_t0] =
            [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12; r_t13; r_t14; r_t15; r_t16;
             r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24; r_t25; r_t26; r_t27; r_t28; r_t29; r_t30]) as ->;[auto|].
    repeat (rewrite gen_pur_reg_extract;[|iNotElemOfList|iNotElemOfList];f_equiv).
    assert (r_t1 :: r_t2 :: r_t3 :: r_t4 :: r_t5 :: r_t6 :: [PC; r_stk; r_t0] ++ [r1] =
            [r_t1;r_t2;r_t3;r_t4;r_t5;r_t6;PC; r_stk; r_t0] ++ [r1]) as ->;[auto|].
    rewrite (list_difference_app _ _ [r1]).
    assert (list_difference all_registers [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; PC; r_stk; r_t0] =
            [r_t7; r_t8; r_t9; r_t10; r_t11; r_t12; r_t13; r_t14; r_t15; r_t16;
             r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24; r_t25; r_t26; r_t27; r_t28; r_t29; r_t30]) as ->;[auto|].
    do 6 (rewrite list_difference_skip;[|iNotElemOfList]). done.
   Qed.

  (* the prologue pushes the activation code, the old pc and stack points,
     sets up the return capability and adv stack capability, then jumps to adversary code *)
  (* r1 is the register containg the adversary capability *)
  Definition scall_prologue_instrs epilogue_off r1 :=
    (* push activation code *)
    push_z_instrs r_stk w_1 ++
    push_z_instrs r_stk w_2 ++
    push_z_instrs r_stk w_3 ++
    push_z_instrs r_stk w_4a ++
    push_z_instrs r_stk w_4b ++
    push_z_instrs r_stk w_4c ++
    (* push old pc *)
    [move_r r_t1 PC;
    lea_z r_t1 epilogue_off;
    lea_z r_stk 1; store_r r_stk r_t1; (* push_r r_t1 *)
    (* push stack pointer *)
    lea_z r_stk 1;
    store_r r_stk r_stk;
    (* set up protected return pointer *)
    move_r r_t0 r_stk;
    lea_z r_t0 (-7)%Z;
    restrict_z r_t0 (local_e);
    (* restrict stack capability *)
    geta r_t1 r_stk;
    add_r_z r_t1 r_t1 1;
    gete r_t2 r_stk;
    subseg_r_r r_stk r_t1 r_t2] ++
    (* clear the unused part of the stack *)
    (* mclear r_stk: *)
    mclear_instrs r_stk 10 2 ++ (* 10 and 2 correspond to the offsets to iter in a contiguous mclear *)
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

  Ltac iGet_genpur_reg Hr_gen Hwsr wsr ptr :=
     let w := fresh "wr" in
     destruct wsr as [? | w wsr]; first (by inversion Hwsr);
     iDestruct Hr_gen as ptr.

  Ltac iPrologue l Hl prog :=
    destruct l; [by inversion Hl|];
    iDestruct prog as "[Hinstr Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue intro_ptrn instr prog :=
    iNext; iIntros intro_ptrn; iSimpl;
    iCombine instr prog as prog;
    iApply wp_pure_step_later;auto;iNext.

  Definition scall_prologue (a : list Addr) p epilogue_off r1 :=
    ([∗ list] a_i;w_i ∈ a;(scall_prologue_instrs epilogue_off r1), a_i ↦ₐ[p] w_i)%I.

  Ltac iContiguous_bounds i j :=
    eapply contiguous_between_middle_bounds' with (a0 := i) (an := j);
    [ eauto | cbn; solve [ repeat constructor ] ].

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_bounds_withinBounds a0 an :=
    apply isWithinBounds_bounds_alt' with a0 an; auto; [];
    iContiguous_bounds a0 an.

  Lemma isCorrectPC_range_npE p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p ≠ E.
  Proof.
    intros HH1 HH2. 
    destruct (isCorrectPC_range_perm _ _ _ _ _ _ HH1 HH2) as [?| [?|?] ]; 
      congruence.
  Qed.

  Lemma push_z_instrs_extract a i j z prog p' :
    contiguous_between a i j →
    ([∗ list] a_i;w_i ∈ a; (push_z_instrs r_stk z ++ prog), a_i ↦ₐ[p'] w_i) -∗
    ∃ a' push2 a_rest,
      (([∗ list] a_i;w_i ∈ [i; push2];push_z_instrs r_stk z, a_i ↦ₐ[p'] w_i) ∗
       [∗ list] a_i;w_i ∈ a'; prog, a_i ↦ₐ[p'] w_i) ∗
       ⌜ a = [i; push2] ++ a'
         ∧ (i + 1 = Some push2)%a
         ∧ (push2 + 1 = Some a_rest)%a
         ∧ contiguous_between a' a_rest j ⌝.
  Proof.
    intros. iIntros "HH".
    iDestruct (contiguous_between_program_split with "HH") as (a_push a' a_rest) "(Hpush & ? & #Hcont)"; eauto.
    iDestruct "Hcont" as %(Hcont1 & ? & -> & Hrest).
    iDestruct (big_sepL2_length with "Hpush") as %Hpushlength.
    destruct (contiguous_2 a_push) as (push1 & push2 & -> & Ha12); auto.
    { rewrite contiguous_iff_contiguous_between; eauto. }
    assert (push1 = i) as ->. { inversion Hcont1; auto. }
    iExists a', push2, a_rest. iFrame. iPureIntro. repeat split; eauto.
    cbn in Hrest. revert Ha12 Hrest; clear. solve_addr.
  Qed.

  Ltac iPush_z prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let push2 := fresh "push2" in
    let Ha1 := fresh "Ha1" in
    let Ha2 := fresh "Ha2" in
    let Ha := fresh "Ha" in
    iDestruct (push_z_instrs_extract with prog) as (a_rest push2 cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha2 & Ha);
    iApply (push_z_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha"; eauto;
    clear Ha1 Ha2; last iRename "Hprog" into prog.

  Lemma scall_prologue_spec
        (* adress arithmetic *) a_r_adv b_r_adv a_act a_cont
        (* scall parameters *) a a_first (*a_last*) p' epilogue_off r1
        (* program counter *) p g b e
        (* stack capability *) b_r e_r a_r
        (* continuation *) φ :
    isCorrectPC_range p g b e a_first a_cont →
    withinBounds ((RWLX, Local), b_r, e_r, a_act) = true -> withinBounds ((RWLX, Local), b_r, e_r, b_r_adv) = true →
    (0%a <= e_r)%Z ∧ (0%a <= b_r)%Z → (* This assumption can be removed once we update addresses to be nats *)
    contiguous_between a a_first a_cont →
    PermFlows p p' →
    r1 ∉ [PC;r_stk;r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6] →

    (a_r + 1)%a = Some a_act →
    (a_act + 7)%a = Some a_r_adv →
    (a_act + 8)%a = Some b_r_adv →
    (a_first + (12 + epilogue_off))%a = Some a_cont →
    (0 ≤ epilogue_off)%Z →

    (▷ scall_prologue a p' epilogue_off r1
   ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a_first)
   ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),b_r,e_r,a_r)
   ∗ ▷ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r1]; wsr, r_i ↦ᵣ w_i)
   ∗ ▷ (∃ ws_own, [[a_act, b_r_adv]]↦ₐ[RWLX][[ws_own]]) (* local stack *)
   ∗ ▷ (∃ ws_adv, [[b_r_adv, e_r]]↦ₐ[RWLX][[ws_adv]]) (* adv stack *)
   ∗ ▷ (PC ↦ᵣ inr (p,g,b,e,a_cont)
            ∗ r_stk ↦ᵣ inr ((RWLX,Local),b_r_adv,e_r,a_r_adv)
            ∗ r_t0 ↦ᵣ inr ((E,Local),b_r,e_r,a_act)
            ∗ ([∗ list] r_i ∈ list_difference all_registers [PC;r_stk;r_t0;r1], r_i ↦ᵣ inl 0%Z)
            ∗ [[ a_act, b_r_adv ]]↦ₐ[RWLX][[ [inl w_1;
                                             inl w_2;
                                             inl w_3;
                                             inl w_4a;
                                             inl w_4b;
                                             inl w_4c;
                                             inr (p,g,b,e,a_cont);
                                             inr (RWLX,Local,b_r,e_r,a_r_adv)] ]] (* local stack *)
            ∗ [[ b_r_adv, e_r ]] ↦ₐ[RWLX] [[ region_addrs_zeroes b_r_adv e_r ]] (* cleared adv stack *)
            ∗ scall_prologue a p' epilogue_off r1 -∗
            WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc1 Hwb1 Hwb2 Hnonzero Ha Hfl Hne Hact Hadva Hadvb Hcont Heoff)
            "(>Hprog & >HPC & >Hr_stk & >Hr1 & >Hgen_reg & >Hstack & Hφ)".
    assert (withinBounds ((RWLX, Local), b_r, e_r, a_r_adv) = true) as Hwb3.
    { apply andb_true_iff.
      apply andb_true_iff in Hwb2 as [Hba Hae]. apply andb_true_iff in Hwb1 as [Hbact Hacte].
      revert Hae Hba Hbact Hacte; repeat rewrite Z.leb_le Z.ltb_lt; intros Hae Hba Hbact Hacte.
      assert (a_r_adv ≤ b_r_adv)%Z as Hle;[apply incr_addr_le with a_act 7 8;auto;lia|].
      assert (a_act ≤ a_r_adv)%Z as Hle';[apply next_le_i with 7;auto;lia|]. lia.
    }
    iDestruct "Hgen_reg" as (ws_own) "Hgen_reg".
    rewrite /scall_prologue.
    (* prepare the local stack for storing the activation record, old PC and old SP *)
    assert (∃ a1 a2 a3 a4 a5 a6 a7 a8, [a1;a2;a3;a4;a5;a6;a7;a8] = region_addrs a_act b_r_adv)
      as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & Hstack_eq).
    {
      apply (incr_addr_region_size_iff a_act _ 7) in Hadva as [Hle Hsize].
      assert (length (region_addrs a_act b_r_adv) = 8) as Hlen.
      { rewrite region_addrs_length. rewrite /region_size in Hsize |- *. solve_addr. }
      rewrite /region_mapsto.
      destruct_list (region_addrs a_act b_r_adv).
      exists a0,a1,a2,a3,a4,a5,a6,a7. done.
    }
    assert (contiguous_between (region_addrs a_act b_r_adv) a_act b_r_adv) as Hcontiguous.
    { apply contiguous_between_of_region_addrs; auto. solve_addr. }
    rewrite -Hstack_eq in Hcontiguous.
    rewrite /region_mapsto -Hstack_eq.
    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    iDestruct (big_sepL2_length with "Hgen_reg") as %Hlength'.
    assert ((region_addrs a_act b_r_adv) !! 0 = Some a_act) as Hfirst_stack.
    { apply region_addrs_first. revert Hadvb; clear. solve_addr. }
    rewrite -Hstack_eq /= in Hfirst_stack. inversion Hfirst_stack; subst. clear Hfirst_stack.
    (* PUSH ACTIVATION RECORD *)
    (* push w_1 *)
    destruct ws_own as [|w ws_own];[inversion Hlength'|]; iDestruct "Hgen_reg" as "[Ha Hstack_own]".
    iPush_z "Hprog".
    { split; iCorrectPC a_first a_cont. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iRename "Hpush" into "Hi". iRename "Ha" into "Hw1".
    (* push w_2 *)
    destruct ws_own as [|w1 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog"; [| |iContiguous_next Hcontiguous 0|].
    { split; iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_act b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hw1" as "Hact_frame".
    (* push w_3 *)
    destruct ws_own as [|w2 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 1|].
    { split; iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_act b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    (* push w_4a *)
    destruct ws_own as [|w3 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 2|].
    { split; iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_act b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    (* push w_4b *)
    destruct ws_own as [|w4 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 3|].
    { split; iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_act b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    (* push w_4a *)
    destruct ws_own as [|w5 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 4|].
    { split; iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_act b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    clear Ha5 Ha4 Ha3 Ha0 Ha6.
    (* PUSH OLD PC *)
    (* some general purpose registers *)
    iDestruct "Hr1" as (wsr) "Hr_gen".
    iDestruct (big_sepL2_length with "Hr_gen") as %Hreglength.
    rewrite (gen_pur_reg_length r1) /= in Hreglength;[|iRegNotEq Hne;iNotElemOfList].
    rewrite gen_pur_app;[|auto].
    iGet_genpur_reg "Hr_gen" Hreglength wsr "[Hrt0 Hr_gen]".
    iGet_genpur_reg "Hr_gen" Hreglength wsr "[Hrt1 Hr_gen]".
    (* move r_t1 PC *)
    do 2 (destruct a_rest0; [inversion Hlength|]).
    match goal with H: contiguous_between (?a' :: _) ?a _ |- _ =>
      generalize (contiguous_between_cons_inv_first _ a a' _ H); intro; subst a end.
    iDestruct "Hprog" as "[Hinstr Hprog]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_move_success_reg_fromPC with "[$Hinstr $Hrt1 $HPC]");
      [apply move_r_i|apply Hfl| |iContiguous_next Ha 12|auto|].
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hi".
    (* lea r_t1 epilogue_off *)
    iPrologue a_rest0 Hlength "Hprog".
    (* we first need to make some assertions about the increase of the address a *)
    assert ((a + epilogue_off)%a = Some a_cont) as Hepilogue.
    { rewrite -Hcont (addr_add_assoc _ a);[auto|].
      eapply (contiguous_between_incr_addr _ 12); eauto. }
    iApply (wp_lea_success_z with "[$Hinstr $Hr_t1 $HPC]");
      [apply lea_z_i|apply Hfl| |iContiguous_next Ha 13|apply Hepilogue|auto|..].
    { iCorrectPC a_first a_cont. }
    { eapply isCorrectPC_range_npE; eauto. iContiguous_bounds a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hrt_1)" "Hinstr" "Hi".
    (* PUSH R_T1 *)
    (* lea r_stk 1 *)
    iPrologue a_rest0 Hlength "Hprog".
    iApply (wp_lea_success_z with "[$Hinstr $Hr_stk $HPC]");
      [apply lea_z_i|apply Hfl| |iContiguous_next Ha 14|iContiguous_next Hcontiguous 5|auto|auto|].
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_stk)" "Hinstr" "Hi".
    (* store r_stk r_t1 *)
    iPrologue a_rest0 Hlength "Hprog".
    destruct ws_own;[inversion Hlength'|].
    iDestruct "Hstack_own" as "[Ha7 Hstk_own]".
    iApply (wp_store_success_reg with "[$HPC $Hinstr $Hrt_1 $Hr_stk $Ha7]");
      [apply store_r_i|apply Hfl|apply PermFlows_refl| |iContiguous_next Ha 15|split;auto|by right;left|auto|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_act b_r_adv. }
    iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk & Ha7)" "Hinstr" "Hi".
    iCombine "Ha7" "Hact_frame" as "Hact_frame".
    (* STORE OLD SP *)
    (* lea r_stk 1 *)
    iPrologue a_rest0 Hlength "Hprog".
    iApply (wp_lea_success_z with "[$Hinstr $Hr_stk $HPC]");
      [apply lea_z_i|apply Hfl| |iContiguous_next Ha 16|iContiguous_next Hcontiguous 6|auto|auto|].
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_stk)" "Hinstr" "Hi".
    (* store r_stk r_stk *)
    iPrologue a_rest0 Hlength "Hprog".
    destruct ws_own;[inversion Hlength'|].
    iDestruct "Hstk_own" as "[Ha8 Hstk_own]".
    iApply (wp_store_success_reg_same with "[$HPC $Hinstr $Hr_stk $Ha8]");
      [apply store_r_i|apply Hfl|apply PermFlows_refl| |iContiguous_next Ha 17|split;auto|by right;left|auto|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_act b_r_adv. }
    iEpilogue "(HPC & Hinstr & Hr_stk & Ha_r_adv)" "Hinstr" "Hi".
    iCombine "Ha_r_adv" "Hact_frame" as "Hact_frame".
    (* PREPARE RETURN CAP *)
    (* move r_t0 r_stk *)
    iPrologue a_rest0 Hlength "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hinstr $Hrt0 $Hr_stk]");
      [apply move_r_i|apply Hfl| |iContiguous_next Ha 18|auto|].
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_t0 & Hr_stk)" "Hinstr" "Hi".
    (* lea r_t0 -7 *)
    (* assert that the activation frame starts at a_act *)
    iPrologue a_rest0 Hlength "Hprog".
    generalize (contiguous_between_last _ _ _ _ Hcontiguous eq_refl).
    match goal with |- (?a + _)%a = _ -> _ =>
      intro HH; assert (a = a_r_adv); [ revert HH Hadva Hadvb; clear; solve_addr |];
      subst a end.
    iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t0]");
      [apply lea_z_i|apply Hfl| |iContiguous_next Ha 19| |auto..].
    { iCorrectPC a_first a_cont. }
    { eapply contiguous_between_incr_addr_middle' with (i := 7); 
        [ eapply Hcontiguous | eauto; cbn; lia .. ]. }
    iEpilogue "(HPC & Hinstr & Hr_t0)" "Hinstr" "Hi".
    (* restrict r_t0 (Local,E) *)
    iPrologue a_rest0 Hlength "Hprog".
    iApply (wp_restrict_success_z with "[$HPC $Hinstr $Hr_t0]");
      [apply restrict_r_z|apply Hfl| |iContiguous_next Ha 20|rewrite epp_local_e;auto|auto|auto|].
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_t0)" "Hinstr" "Hi".
    (* RESTRICT STACK CAP *)
    (* geta r_t1 r_stk *)
    iPrologue a_rest0 Hlength "Hprog".
    iApply (wp_Get_success with "[$HPC $Hinstr Hr_t1 Hr_stk]");
      [apply geta_i|eauto|apply Hfl| |iContiguous_next Ha 21|auto| |iSimpl|]; eauto.
    { iCorrectPC a_first a_cont. } { iFrame. }
    iEpilogue "(HPC & Hinstr & Hr_stk & Hr_t1)" "Hinstr" "Hi".
    (* add r_t1 r_t1 1 *)
    iPrologue a_rest0 Hlength "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hinstr Hr_t1]");
      [apply add_r_z_i| | | apply Hfl| ..]; eauto.
    assert ((a15 + 1)%a = Some a16) as ->;[iContiguous_next Ha 22|]. eauto.
    { iCorrectPC a_first a_cont. }
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hi".
    (* gete r_t2 r_stk *)
    iGet_genpur_reg "Hr_gen" Hreglength wsr "[Hr_t2 Hr_gen]".
    iPrologue a_rest0 Hlength "Hprog".
    iApply (wp_Get_success with "[$HPC $Hinstr Hr_t2 Hr_stk]");
      [apply gete_i| eauto | apply Hfl| |iContiguous_next Ha 23|auto| |iSimpl|]; eauto.
    { iCorrectPC a_first a_cont. } { iFrame. }
    iEpilogue "(HPC & Hinstr & Hr_stk & Hr_t2)" "Hinstr" "Hi".
    (* subseg r_stk r_t1 r_t2 *)
    assert (z_to_addr (a_r_adv + 1) = Some b_r_adv) as Hb_r_adv.
    { assert ((a_r_adv + 1)%a = Some b_r_adv) as temp;[rewrite -(addr_add_assoc a_act _ 7);auto|auto]. }
    assert (z_to_addr e_r = Some e_r) as He_r.
    { rewrite /z_to_addr. destruct (Z_le_dec e_r MemNum);destruct e_r;[f_equiv;by apply z_of_eq|].
      exfalso. clear Hwb1 Hwb2 Hwb3 Hnonzero. simpl in n. revert fin. rewrite Z.leb_le. done. }
    iPrologue a_rest0 Hlength "Hprog".
    iApply (wp_subseg_success with "[$HPC $Hinstr $Hr_stk $Hr_t1 $Hr_t2]");
      [apply subseg_r_r_i|apply Hfl| |eauto|auto|auto|..].
    { iCorrectPC a_first a_cont. }
    { rewrite !andb_true_iff !Z.leb_le. repeat split; try lia.
      eapply withinBounds_le_addr; eauto. }
    assert ((a17 + 1)%a = Some a18) as ->;[iContiguous_next Ha 24|].
    iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_t2 & Hr_stk)" "Hinstr" "Hi".
    (* MCLEAR *)
    assert ([a_first; push2] ++ [cont; push0] ++ [cont0; push1] ++ [cont1; push3] ++ [cont2; push4] ++ [cont3; push5]
                             ++ a :: a0 :: a1 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a8 :: a15 :: a16 :: a17 :: a18 :: a_rest0 =
            [a_first; push2; cont; push0; cont0; push1; cont1; push3; cont2; push4; cont3; push5;
             a; a0; a1; a9; a10; a11; a12; a13; a14; a8; a15; a16; a17]
              ++ a18 :: a_rest0) as Happeq;[by auto|].
    eapply contiguous_between_app in Happeq as (Hcont1 & Hcont2); [| cbn; eauto..].
    2: by eapply contiguous_between_incr_addr; eauto.
    iDestruct (contiguous_between_program_split with "Hprog") as (mclear_addrs rclear_addrs rclear_first) "(Hmclear & Hrclear & #Hcont)"; [eauto|].
    iDestruct "Hcont" as %(Hcont21 & Hcont22 & Happeq' & Hlink').
    iDestruct (big_sepL2_length with "Hmclear") as %Hmclear_length.
    assert (7 < (length mclear_addrs)) as Hlt7;[rewrite Hmclear_length /=;lia|].
    assert (17 < (length mclear_addrs)) as Hlt17;[rewrite Hmclear_length /=;lia|].
    apply lookup_lt_is_Some_2 in Hlt7 as [ai Hai].
    apply lookup_lt_is_Some_2 in Hlt17 as [aj Haj].
    assert (ai + 10 = Some aj)%a.
    { rewrite (_: 10%Z = Z.of_nat (10 : nat)).
      eapply contiguous_between_incr_addr_middle; [eapply Hcont21|..]. all: eauto. }
    iApply (mclear_spec with "[-]"); last (rewrite /region_mapsto; iFrame "HPC Hr_stk Hstack");
      [ apply Hcont21 | ..]; eauto.
    { intros ak Hak. apply Hvpc1.
      have: (a_first <= a18)%a. iContiguous_bounds a_first a_cont.
      have: (rclear_first <= a_cont)%a. eapply contiguous_between_bounds; eauto.
      revert Hak; clear; solve_addr. }
    { apply PermFlows_refl. }
    { apply withinBounds_le_addr in Hwb2. revert Hwb2; clear; solve_addr. }
    rewrite /mclear.
    destruct (strings.length mclear_addrs =? strings.length (mclear_instrs r_stk 10 2))%nat eqn:Hcontr;
      [|rewrite Hmclear_length in Hcontr;inversion Hcontr].
    iFrame "Hmclear".
    iGet_genpur_reg "Hr_gen" Hreglength wsr "[Hr_t3 Hr_gen]".
    iGet_genpur_reg "Hr_gen" Hreglength wsr "[Hr_t4 Hr_gen]".
    iGet_genpur_reg "Hr_gen" Hreglength wsr "[Hr_t5 Hr_gen]".
    iGet_genpur_reg "Hr_gen" Hreglength wsr "[Hr_t6 Hr_gen]".
    iSplitL "Hr_t4". iNext; eauto.
    iSplitL "Hr_t1". iNext; eauto.
    iSplitL "Hr_t2". iNext; eauto.
    iSplitL "Hr_t3". iNext; eauto.
    iSplitL "Hr_t5". iNext; eauto.
    iSplitL "Hr_t6". iNext; eauto.
    iNext. iIntros "(HPC & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6 & Hr_stk & Hstack_adv & Hmclear)".
    (* RCLEAR *)
    iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
    rewrite map_length helper1 in Hrclear_length;[|iRegNotEq Hne|apply all_registers_correct].
    iApply (rclear_spec with "[-]"); last (iFrame "HPC Hrclear").
    { eauto. }
    { apply not_elem_of_list; apply elem_of_cons; by left. }
    { destruct rclear_addrs; inversion Hcont22; eauto. inversion Hrclear_length. }
    { intros a' [Ha'1 Ha'2]. eapply Hvpc1. split; [| by auto].
      have: (a_first <= a18)%a by iContiguous_bounds a_first a_cont.
      have: (a18 <= rclear_first)%a by eapply contiguous_between_bounds; eauto.
      revert Ha'1; clear; solve_addr. }
    { apply Hfl. }
    iSplitL "Hr_t1 Hr_t2 Hr_t3 Hr_t4 Hr_t5 Hr_t6 Hr_gen".
    { iNext. iApply region_addrs_exists.
      rewrite gen_pur_app';[|iRegNotEq Hne;iNotElemOfList].
      iSplitL "Hr_t1";[eauto|].
      iSplitL "Hr_t2";[eauto|].
      iSplitL "Hr_t3";[eauto|].
      iSplitL "Hr_t4";[eauto|].
      iSplitL "Hr_t5";[eauto|].
      iSplitL "Hr_t6";[eauto|].
      iApply region_addrs_exists.
      assert ([r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; PC; r_stk] ++ r_t0 :: [r1] =
              [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; PC; r_stk; r_t0; r1]) as Heq';[auto|].
      assert ([r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; PC; r_stk; r_t0; r1] ≡ₚ
              [r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; PC; r_stk; r1]) as Hperm.
      { rewrite -Heq'. rewrite -Permutation_middle. done. }
      apply list_difference_Permutation with all_registers _ _ in Hperm. rewrite Hperm.
      iExists wsr. iFrame.
    }
    iNext. iIntros "(HPC & Hgen_reg & Hrclear)".
    iApply "Hφ". rewrite epp_local_e. iFrame "HPC Hr_stk Hr_t0 Hgen_reg Hstack_adv".
    iSplitL "Hact_frame".
    - iDestruct "Hact_frame" as "(Ha_r_adv & Ha7 & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha_act)".
      iFrame. done.
    - rewrite Happeq'.
      iDestruct "Hi" as "(Ha17 & Ha16 & Ha15 & Ha14 & Ha13 & Ha12 & Ha11 & Ha10 & Ha9 &
                          Ha8 & Ha1 & Ha0 & Ha & Hpush6 & Hpush5 & Hpush4 & Hpush3 & Hpush0 & Hpush2)".
      iFrame. 
  Qed.

  Lemma scall_epilogue_spec stack_own_b stack_own_e s_last stack_new
        (* reinstated PC *) pc_p pc_g pc_b pc_e pc_cont pc_next
        (* reinstated stack *) p_r g_r b_r e_r 
        (* current PC *) p g φ :

    isCorrectPC_range p g b_r e_r stack_own_b stack_own_e →
    PermFlows p p_r ->
    (pc_cont + 1)%a = Some pc_next ->
    (stack_new + 1)%a = Some s_last ->
    (s_last + 1)%a = Some stack_own_e ->

    (▷ PC ↦ᵣ inr (p, g, b_r, e_r, stack_own_b)
       ∗ ▷ (∃ rt1w, r_t1 ↦ᵣ rt1w)
       ∗ ▷ (∃ rstkw, r_stk ↦ᵣ rstkw)
       ∗ ▷ ([[stack_own_b,stack_own_e]]↦ₐ[p_r][[
                [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c; 
                 inr (pc_p, pc_g, pc_b, pc_e, pc_cont);
                 inr (p_r, g_r, b_r, e_r, s_last)]
            ]]) (* activation frame *)
       ∗ ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, pc_next)
               ∗ r_stk ↦ᵣ inr (p_r, g_r, b_r, e_r, stack_new)
               ∗ (∃ rt1w, r_t1 ↦ᵣ rt1w)
               ∗ [[stack_own_b,stack_own_e]]↦ₐ[p_r][[
                    [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                     inr (pc_p, pc_g, pc_b, pc_e, pc_cont);
                     inr (p_r, g_r, b_r, e_r, s_last)]
                 ]] (* activation frame *) -∗ 
               WP Seq (Instr Executable) {{ φ }})
       ⊢ WP Seq (Instr Executable) {{ φ }})%I. 
  Proof.
    iIntros (Hvpc Hfl Hnext Hstack1 Hstack2) "(>HPC & >Hr_t1 & >Hr_stk & >Hframe & Hφ)". 
    iDestruct "Hr_t1" as (rt1w) "Hr_t1". 
    iDestruct "Hr_stk" as (rstkw) "Hr_stk". 
    rewrite /region_mapsto.
    iDestruct (big_sepL2_length with "Hframe") as %Hframe_length.
    set (l := region_addrs stack_own_b stack_own_e) in *.
    simpl in Hframe_length.
    assert (contiguous_between l stack_own_b stack_own_e) as Hcont.
    { eapply contiguous_between_of_region_addrs; eauto. 
      rewrite region_addrs_length /region_size // in Hframe_length. solve_addr. }
    assert (stack_own_b + 8 = Some stack_own_e)%a as Hstack_bounds.
    { generalize (contiguous_between_length _ _ _ Hcont). cbn. by rewrite Hframe_length. }

    destruct l; [ by inversion Hframe_length |].
    iPrologue l Hframe_length "Hframe". 
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). subst a.
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hinstr $Hr_t1]");
      [rewrite -i_1; apply decode_encode_inv|apply Hfl| |iContiguous_next Hcont 0|auto|].
    { iCorrectPC stack_own_b stack_own_e. }
    iAssert (emp)%I as "Hframe_past";[done|]. 
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hframe_past". 
    (* lea r_t1 7 *)
    iPrologue l Hframe_length "Hprog".
    assert ((stack_own_b + 7)%a = Some s_last) as Hincr.
    { revert Hstack_bounds Hframe_length Hstack2; clear; solve_addr. }
    iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t1]");
      [rewrite -i_2; apply decode_encode_inv|apply Hfl| |iContiguous_next Hcont 1|apply Hincr|auto|..].
    { iCorrectPC stack_own_b stack_own_e. }
    { eapply isCorrectPC_range_npE; eauto. iContiguous_bounds stack_own_b stack_own_e. }
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hframe_past". 
    (* load r_stk r_t1 *)
    iPrologue l Hframe_length "Hprog".
    do 4 (let a := fresh "a" in destruct l as [|a l]; [inversion Hframe_length|]). destruct l;[|inversion Hframe_length]. 
    iDestruct "Hprog" as "(Hinstr1 & Hinstr2 & Hinstr3 & Hinstr4 & Hlast & _)".
    (* fixme: tedious *)
    assert (a5 = s_last) as ->.
    { generalize (contiguous_between_last _ _ _ _ Hcont eq_refl).
      revert Hstack2; clear; solve_addr. }
    assert (a4 = stack_new) as ->.
    { generalize (contiguous_between_incr_addr_middle _ _ _ 6 1 _ _ Hcont eq_refl eq_refl).
      revert Hstack1 Hstack2; clear; solve_addr. }

    assert ((s_last =? a)%a = false) as Hne.
    { assert ((a + 5)%a = Some s_last) as Hincr'. 
      { pose proof (contiguous_between_last _ _ _ _ Hcont eq_refl) as HH5.
        eapply (contiguous_between_incr_addr_middle _ _ _ 2 5 _ _ Hcont); auto. }
      apply Z.eqb_neq. revert Hincr'; clear; solve_addr. }
    iApply (wp_load_success with "[$HPC $Hinstr $Hr_stk $Hr_t1 Hlast]");
      [rewrite -i_3; apply decode_encode_inv|apply Hfl|apply Hfl| | | |auto| 
       rewrite Hne; iFrame ..].
    { iCorrectPC stack_own_b stack_own_e. }
    { split.
      - unshelve epose proof (isCorrectPC_range_perm _ _ _ _ _ _ Hvpc _) 
          as [ ? | [?|?] ]; [| destruct p; cbn; congruence ..].
        iContiguous_bounds stack_own_b stack_own_e.
      - eapply isCorrectPC_withinBounds. apply Hvpc.
        iContiguous_bounds stack_own_b stack_own_e. }
    { iContiguous_next Hcont 2. }
    iEpilogue "(HPC & Hr_stk & Hinstr & Hr_t1 & Hlast)" "Hinstr" "Hframe_past".
    (* sub r_t1 0 1 *)
    iApply (wp_bind (fill [SeqCtx])). 
    iApply (wp_add_sub_lt_success_z_z with "[$HPC Hr_t1 $Hinstr1]");
      [rewrite -i_4a; apply decode_encode_inv| | | apply Hfl | | iFrame;eauto|..]; eauto.
    assert ((a1 + 1)%a = Some a2) as ->;[iContiguous_next Hcont 3|]. eauto.
    { iCorrectPC stack_own_b stack_own_e. }
    iEpilogue "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hframe_past".
    (* Lea r_stk r_t1 *)
    iApply (wp_bind (fill [SeqCtx])).
    assert ((s_last + (0 - 1))%a = Some stack_new) as Hdecr.
    { revert Hstack1; clear; solve_addr. }
    assert (isCorrectPC (inr (p, g, b_r, e_r, stack_own_b))) as Hvpc_b.
    { apply Hvpc. iContiguous_bounds stack_own_b stack_own_e. }
    iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr2]");
      [rewrite -i_4b; apply decode_encode_inv|apply Hfl| |iContiguous_next Hcont 4|apply Hdecr|auto|..].
    { iCorrectPC stack_own_b stack_own_e. }
    { destruct p_r; auto. destruct p; inversion Hfl; inversion Hvpc_b as [?????? [Hcontr | [Hcontr | Hcontr] ] ]; done. }
    iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)" "Hinstr" "Hframe_past".
    (* Load PC r_t1 *)
    iApply (wp_bind (fill [SeqCtx])). 
    iApply (wp_load_success_PC with "[$HPC $Hr_stk $Hinstr3 $Hinstr4]");
      [rewrite -i_4c; apply decode_encode_inv|apply Hfl|apply PermFlows_refl| | |apply Hnext|..].
    { iCorrectPC stack_own_b stack_own_e. }
    { split.
      - destruct p_r; auto; destruct p; inversion Hfl; inversion Hvpc_b as [?????? [Hcontr | [Hcontr | Hcontr] ] ]; done.
      - eapply isCorrectPC_withinBounds. apply Hvpc. iContiguous_bounds stack_own_b stack_own_e. }
    iEpilogue "(HPC & Hinstr & Hr_stk & Hinstr')" "Hinstr" "Hframe_past".
    iDestruct "Hframe_past" as "(Ha3 & Ha2 & Ha1 & Ha0 & Ha & Hstack_own_b & _)".
    iApply "Hφ". iFrame. cbn. iSplitL; eauto.
  Qed.

End scall.
