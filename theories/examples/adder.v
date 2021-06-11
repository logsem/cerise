From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers macros fundamental.

Section adder.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Context (N: namespace).

  (* For simplicity, we assume here that we know in advance where the code of f
     is going to be in memory.

     We do that because it simplifies a bit the code of g (for subseg). It would
     be easy to get rid of this requirement: f_start is already computed by g,
     and one could just read f_end from the end bound of the capability. *)
  Context (f_start f_end : Addr).

  Definition offset_to_f := Eval cbv in (length (scrtcls_instrs r_t2 r_t3) + 4).

  (* Closure initialization code *)
  Definition adder_g_instrs :=
    [move_r r_t2 PC;
     lea_z r_t2 offset_to_f;
     subseg_z_z r_t2 f_start f_end] ++
    scrtcls_instrs r_t2 r_t3 ++
    [jmp r_t0].

  Definition adder_g_instrs_length := Eval cbv in (length adder_g_instrs).

  (* Closure body *)
  Definition adder_f_instrs :=
    [
      move_r r_t1 PC;
      lea_z r_t1 7;
      lt_r_z r_t3 r_t2 0;
      jnz r_t1 r_t3;
      load_r r_t3 r_env;
      add_r_r r_t3 r_t3 r_t2;
      store_r r_env r_t3;
      move_z r_env 0;
      move_z r_t1 0;
      jmp r_t0
    ].

  Definition adder_f_instrs_length := Eval cbv in (length adder_f_instrs).

  Definition adder_g a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;adder_g_instrs, a_i ↦ₐ w_i)%I.

  Definition adder_f a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;adder_f_instrs, a_i ↦ₐ w_i)%I.

  Lemma adder_g_spec ag g_start w0 act_start act_end w2 x x' act0 φ :
    contiguous_between ag g_start f_start →
    (x + 1)%a = Some x' →
    (f_start <= f_end)%a →
    (act_start + 8)%a = Some act_end →

      ▷ adder_g ag
    ∗ ▷ PC ↦ᵣ WCap RX g_start f_end g_start
    ∗ ▷ r_t0 ↦ᵣ w0
    ∗ ▷ r_t1 ↦ᵣ WCap RWX act_start act_end act_start
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ WCap RW x x' x
    ∗ ▷ ([[ act_start, act_end ]] ↦ₐ [[ act0 ]])
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ updatePcPerm w0 ∗ adder_g ag
         ∗ r_t0 ↦ᵣ w0
         ∗ r_t1 ↦ᵣ WCap E act_start act_end act_start
         ∗ r_t2 ↦ᵣ WInt 0%Z
         ∗ r_t3 ↦ᵣ WInt 0%Z
         ∗ [[ act_start, act_end ]] ↦ₐ
           [[ activation_instrs (WCap RX f_start f_end f_start) (WCap RW x x' x) ]]
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hcont Hx Hf_start_end Hact_size) "(>Hprog & >HPC & >Hr0 & >Hr1 & >Hr2 & >Hr3 & >Hact & Hφ)".
    unfold adder_g.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    destruct ag as [| a0 ag]; [inversion Hlength|].
    destruct ag as [| ? ag]; [inversion Hlength|].
    feed pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). subst a0.
    assert (isCorrectPC_range RX g_start f_end g_start f_start).
    { intros mid [? ?]. constructor; auto. solve_addr. }
    (* move r_t2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC g_start f_start|iContiguous_next Hcont 0|..].
    iEpilogue "(HPC & Hi & Hr2)"; iRename "Hi" into "Hprog_done".
    (* lea r_t2 4 *)
    assert ((g_start + offset_to_f)%a = Some f_start) as Hlea.
    { pose proof (contiguous_between_length _ _ _ Hcont) as HH.
      rewrite Hlength in HH. apply HH. }
    destruct ag as [| ? ag];[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC g_start f_start|iContiguous_next Hcont 1|apply Hlea|eauto|].
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* subseg r_t2 f_start f_end *)
    destruct ag as [| ? ag];[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_subseg_success_lr with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC g_start f_start|..]; auto.
    { rewrite !z_to_addr_z_of //. }
    { rewrite !z_to_addr_z_of //. }
    { (* TODO: lemma *)
      rewrite /isWithin.
      rewrite /le_addr /lt_addr /leb_addr /ltb_addr.
      rewrite andb_true_iff !Z.leb_le. solve_addr. }
    { iContiguous_next Hcont 2. }
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* scrtcls *)
    assert (contiguous_between (a1::ag) a1 f_start) as Hcont'.
    { do 3 apply contiguous_between_cons_inv in Hcont as [? (? & ? & Hcont)].
      subst. pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). by subst. }
    iDestruct (contiguous_between_program_split with "Hprog") as (scrtcls_a a' link)
      "(Hcrtcls_prog & Hprog & #Hcont)"; eauto.
    iDestruct "Hcont" as %(Hcont_scrtcls & Hcont_jmp & Heqapp & Hlink).
    iApply (scrtcls_spec with "[- $HPC $Hcrtcls_prog $Hr1 $Hr2 $Hr3 $Hact]"); eauto.
    { intros mid Hmid. constructor; auto.
      apply contiguous_between_incr_addr with (i:=3) (ai:=a1) in Hcont;auto.
      apply contiguous_between_length in Hcont_jmp.
      revert Hmid Hcont_jmp Hcont Hf_start_end; clear. solve_addr. }
    iNext. iIntros "(HPC & Hscrtcls & Hr1 & Hact & Hr2 & Hr3)".
    (* jmp r_t0 *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_jmp.
    destruct a' as [| ? a']; [inversion Hlength_jmp|].
    destruct a'; [|inversion Hlength_jmp].
    apply contiguous_between_cons_inv in Hcont_jmp as [-> (? & ? & Hnil)].
    inversion Hnil. subst.
    iPrologue "Hprog". iClear "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply decode_encode_instrW_inv|..].
    { constructor; auto. split. 2: solve_addr.
      apply contiguous_between_incr_addr with (i:=3) (ai:=a1) in Hcont; auto.
      revert Hcont Hlink; clear. solve_addr. }
    iEpilogue "(HPC & Hi & Hr0)".
    (* continuation *)
    iApply "Hφ". iDestruct "Hprog_done" as "(? & ? & ?)". iFrame.
    rewrite Heqapp. iDestruct (big_sepL2_length with "Hscrtcls") as %?.
    rewrite -big_sepL2_app' //. by iFrame.
  Qed.

  Lemma adder_f_spec af w0 x x' w1 w2 w3 φ :
    contiguous_between af f_start f_end →
    (x + 1)%a = Some x' →
    (f_start <= f_end)%a →

    inv N (∃ (n:Z), x ↦ₐ WInt n ∗ ⌜(0 ≤ n)%Z⌝)
    ∗ ▷ adder_f af
    ∗ ▷ PC ↦ᵣ WCap RX f_start f_end f_start
    ∗ ▷ r_t0 ↦ᵣ w0
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_env ↦ᵣ WCap RW x x' x
    (* continuation *)
    ∗ ▷ ((∃ (k' n':Z),
          PC ↦ᵣ updatePcPerm w0 ∗ adder_f af
          ∗ r_t0 ↦ᵣ w0
          ∗ r_t1 ↦ᵣ WInt 0%Z
          ∗ r_t2 ↦ᵣ WInt k'
          ∗ r_t3 ↦ᵣ WInt n'
          ∗ r_env ↦ᵣ WInt 0%Z)
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hcont Hx Hf_start_end) "(#Hinv & >Hprog & >HPC & >Hr0 & >Hr1 & >Hr2 & >Hr3 & >Hrenv & Hφ)".
    unfold adder_f.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    remember af as af'.
    destruct af' as [| a0 af'];[inversion Hlength|].
    destruct af' as [| ? af'];[inversion Hlength|].
    feed pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). subst a0.
    assert (isCorrectPC_range RX f_start f_end f_start f_end).
    { intros ? [? ?]. constructor; auto. solve_addr. }
    (* move r_t1 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|iContiguous_next Hcont 0|..].
    iEpilogue "(HPC & Hi & Hr1)"; iRename "Hi" into "Hprog_done".
    (* lea r_t1 7 *)
    assert (∃ a_cleanup, (f_start + 7%nat)%a = Some a_cleanup) as [a_cleanup Ha_cleanup].
    { assert (is_Some (af !! 7)) as [ac Hac].
      { apply lookup_lt_is_Some_2. rewrite -Heqaf' Hlength /adder_f_instrs /=. lia. }
      exists ac. eapply contiguous_between_incr_addr; eauto.
      rewrite Heqaf' //. }
    destruct af' as [| ? af'];[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|iContiguous_next Hcont 1|..]; eauto.
    iEpilogue "(HPC & Hi & Hr1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lt r_t3 r_t2 0 *)
    destruct af' as [| ? af'];[inversion Hlength|].
    iPrologue "Hprog".
    destruct w2 as [z2|c2]; cycle 1.
    { (* Failure case: the argument is not an integer *)
      iDestruct (map_of_regs_3 with "HPC Hr3 Hr2") as "[Hmap %]".
      iApply (wp_AddSubLt with "[$Hi $Hmap]"); rewrite ?decode_encode_instrW_inv; eauto.
      { iCorrectPC f_start f_end. }
      { erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+. }
      iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [| * _]; [by exfalso; incrementPC_inv|].
      iApply wp_pure_step_later; auto; iNext. iApply wp_value. auto. }
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hi $Hr3 $Hr2]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 2|iCorrectPC f_start f_end|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    cbn [rules_AddSubLt.denote].
    (* Prove the internal continuation (a_cleanup) *)
    iAssert (∀ (w1 we: Word) (k' n' : Z),
      PC ↦ᵣ WCap RX f_start f_end a_cleanup
      ∗ adder_f af
      ∗ r_t0 ↦ᵣ w0
      ∗ r_t1 ↦ᵣ w1
      ∗ r_t2 ↦ᵣ WInt k'
      ∗ r_t3 ↦ᵣ WInt n'
      ∗ r_env ↦ᵣ we
      -∗ WP Seq (Instr Executable) {{ φ }})%I with "[Hφ]" as "Hcleanup".
    { iIntros (w2 we k' n') "(HPC & Hprog & Hr0 & Hr1 & Hr2 & Hr3 & Hrenv)".
      rewrite -Heqaf' /adder_f.
      do 3 (destruct af' as [| ? af'];[by inversion Hlength|]).
      destruct af' as [| ac af'];[inversion Hlength|].
      do 2 (destruct af' as [| ? af'];[inversion Hlength|]).
      destruct af';[|by inversion Hlength].
      assert (ac = a_cleanup) as ->.
      { eapply contiguous_between_incr_addr with (i:=7) in Hcont. 2: done.
        solve_addr. }
      iDestruct "Hprog" as "[Hprog_done Hprog]".
      do 6 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done").
      (* move r_env 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hrenv]");
        [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|iContiguous_next Hcont 7|..].
      iEpilogue "(HPC & Hi & Hrenv)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|iContiguous_next Hcont 8|..].
      iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t0 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
        [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|..].
      iEpilogue "(HPC & Hi & Hr0)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* continuation *)
      iApply "Hφ". iExists k', n'. do 9 iDestruct "Hprog_done" as "[? Hprog_done]".
      iFrame. }
    (* jnz r_t1 r_t3 *)
    destruct af' as [|? af'];[inversion Hlength|].
    iPrologue "Hprog".
    destruct (decide (z2 < 0)%Z) as [Hz2|Hz2].
    { (* jump to a_cleanup *)
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr1 $Hr3]");
        [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|..].
      { apply Zlt_is_lt_bool in Hz2. rewrite Hz2 //=. }
      iEpilogue "(HPC & Hi & Hr1 & Hr3)".
      iApply (wp_wand with "[-]").
      { iApply "Hcleanup". iFrame. rewrite /adder_f -Heqaf'.
        do 2 iDestruct "Hprog_done" as "[? Hprog_done]". iFrame. }
      eauto. }
    assert (0 <= z2)%Z as Hz2' by lia.
    apply Z.ltb_nlt in Hz2. rewrite Hz2 /=.
    iApply (wp_jnz_success_next with "[$HPC $Hi $Hr1 $Hr3]");
      [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|iContiguous_next Hcont 3|..].
    iEpilogue "(HPC & Hi & Hr1 & Hr3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_t3 r_env *)
    destruct af' as [|? af'];[inversion Hlength|].
    iPrologue "Hprog".
    (* Open the invariant to be able to read x *)
    iInv "Hinv" as (n) "[>Hx >#Hxpos]" "Hclose".
    iAssert (⌜(x =? a2)%a = false⌝)%I as %Hfalse.
    { destruct (x =? a2)%a eqn:HH; eauto. apply Z.eqb_eq,z_of_eq in HH as ->.
      iExFalso. iApply (addr_dupl_false with "Hi Hx"). }
    iApply (wp_load_success with "[$HPC $Hi $Hr3 $Hrenv Hx]");
      [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|..].
    { split; [eauto|]. rewrite withinBounds_true_iff; solve_addr. }
    { iContiguous_next Hcont 4. }
    { rewrite Hfalse //. }
    iNext. iIntros "(HPC & Hr3 & Hi & Hrenv & Hx)". rewrite Hfalse.
    iMod ("Hclose" with "[Hx]") as "_".
    { iNext. iExists n. iFrame; eauto. }
    iModIntro. iApply wp_pure_step_later; auto; iNext.
    iDestruct "Hxpos" as %Hnpos. clear Hfalse.
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* add r_t3 r_t3 r_t2 *)
    destruct af' as [|? af'];[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr2 $Hr3]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 5|iCorrectPC f_start f_end|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr3)". cbn [rules_AddSubLt.denote].
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_env r_t3 *)
    destruct af' as [|ac af'];[inversion Hlength|].
    iPrologue "Hprog".
    (* Open the invariant again, this time to write the new value *)
    iInv "Hinv" as (n') "[>Hx _]" "Hclose".
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr3 $Hx $Hrenv]");
      [apply decode_encode_instrW_inv|iCorrectPC f_start f_end|iContiguous_next Hcont 6|..]; auto.
    { rewrite withinBounds_true_iff; solve_addr. }
    iNext. iIntros "(HPC & Hi & Hr3 & Hrenv & Hx)".
    iMod ("Hclose" with "[Hx]") as "_".
    { iNext. iExists (n + z2)%Z. iFrame. iPureIntro. lia. }
    iModIntro. iApply wp_pure_step_later; auto; iNext.
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* invoque the spec for the cleanup code established earlier *)
    assert (ac = a_cleanup) as ->.
    { eapply contiguous_between_incr_addr with (i:=7) in Hcont. 2: done.
      solve_addr. }
    iApply (wp_wand with "[-]").
    { iApply "Hcleanup". iFrame. rewrite /adder_f -Heqaf'.
      do 6 (iDestruct "Hprog_done" as "[? Hprog_done]"). iFrame. }
    auto.
  Qed.


  (* "full system" specification, starting from the execution of [g] *)

  Definition closureN : namespace := nroot .@ "adder" .@ "closure".
  Definition actN : namespace := nroot .@ "adder" .@ "act".

  Lemma adder_full_spec af ag g_start x x' w0 w2 act0 rmap act_start act_end :
    contiguous_between ag g_start f_start →
    contiguous_between af f_start f_end →
    (x+1)%a = Some x' →
    (act_start + 8)%a = Some act_end →
    (f_start <= f_end)%a →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2; r_t3 ]} →

    inv N (∃ (n:Z), x ↦ₐ WInt n ∗ ⌜(0 ≤ n)%Z⌝)
    ∗ adder_g ag ∗ adder_f af
    ∗ PC ↦ᵣ WCap RX g_start f_end g_start
    ∗ r_t0 ↦ᵣ w0
    ∗ r_t1 ↦ᵣ WCap RWX act_start act_end act_start
    ∗ r_t2 ↦ᵣ w2
    ∗ r_t3 ↦ᵣ WCap RW x x' x
    ∗ [[act_start, act_end]] ↦ₐ [[ act0 ]]
    ∗ interp w0
    ∗ ([∗ map] r↦v ∈ rmap, r ↦ᵣ v ∗ interp v)
    ∗ na_own logrel_nais ⊤
    -∗ WP Seq (Instr Executable) {{ λ _, True }}.
  Proof.
    iIntros (Hcontg Hcontf Hx' Hact_start_end Hf_start_end Hrmap_dom)
            "(#Hinv & Hprog_g & Hprog_f & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hact & #Hw0 & Hregs & HnaI)".
    iApply (wp_wand with "[-]"). 2: iIntros (?) "_"; eauto.
    (* Step 1: Use the spec for g *)
    iApply (adder_g_spec with "[- $HPC $Hr0 $Hr1 $Hr2 $Hr3 $Hact $Hprog_g]"); auto.
    (* Step 2: Use the validity of w0 and the FTLR *)
    iPoseProof (jmp_to_unknown with "Hw0") as "Hcont_g".
    iNext. iIntros "(HPC & Hprog_g & Hr0 & Hr1 & Hr2 & Hr3 & Hact)".

    (* Step 3: Prove that the closure is valid, by using the spec of [f] *)
    (* Put the code of [f] and the activation record in invariants *)
    iDestruct (na_inv_alloc logrel_nais _ closureN with "Hprog_f") as ">#Iprog_f".
    iDestruct (na_inv_alloc logrel_nais _ actN with "Hact") as ">#Iact".

    iAssert (interp (WCap E act_start act_end act_start)) with "[Iprog_f Iact]"
      as "Hclosure".
    { iClear "Hw0". rewrite /interp /= fixpoint_interp1_eq /=.
      iIntros (rmap'). iNext. iModIntro. iIntros "([Hrmap' #HrV] & Hregs & HnaI)".
      iDestruct "Hrmap'" as %Hrmap'. rewrite /interp_conf.
      (* extract registers relevant for f from the map *)
      iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]".
      by rewrite lookup_insert.
      destruct (Hrmap' r_t0) as [rv0 Hrv0].
      iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr0 Hregs]".
      by rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (Hrmap' r_t1) as [rv1 Hrv1].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr1 Hregs]".
      by rewrite !lookup_delete_ne // lookup_insert_ne //.
      destruct (Hrmap' r_t2) as [rv2 Hrv2].
      iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr2 Hregs]".
      by rewrite !lookup_delete_ne // lookup_insert_ne //.
      destruct (Hrmap' r_t3) as [rv3 Hrv3].
      iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr3 Hregs]".
      by rewrite !lookup_delete_ne // lookup_insert_ne //.
      destruct (Hrmap' r_env) as [rvenv Hrvenv].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hrenv Hregs]".
      by rewrite !lookup_delete_ne // lookup_insert_ne //.
      (* Access the activation record code by opening the corresponding invariant;
         then use the spec for the activation record *)
      iDestruct (na_inv_acc with "Iact HnaI") as ">(>Hact & HnaI & Hact_close)";
        [auto..|].
      iApply (closure_activation_spec with "[- $HPC $Hr1 $Hrenv $Hact]"); auto.
      { intros ? ?. constructor; auto. }
      iIntros "(HPC & Hr1 & Hrenv & Hact)".
      iDestruct ("Hact_close" with "[$HnaI $Hact]") as ">HnaI". (* close the invariant *)
      (* Now, access the code of f and use its specification *)
      iDestruct (na_inv_acc with "Iprog_f HnaI") as ">(>Hprog_f & HnaI & Hprog_f_close)";
        [auto..|].
      iApply (wp_wand with "[-]").
      { iApply (adder_f_spec with "[- $HPC $Hr0 $Hr1 $Hr2 $Hr3 $Hrenv $Hprog_f]"); auto.
        iSplitL "Hinv"; eauto.
        (* Use the fact that the closure's continuation is valid to conclude *)
        (* This involves a lot of bureaucratic shuffling of the register resources *)
        unshelve iPoseProof ("HrV" $! r_t0 _) as "Hr0V";[done|].
        rewrite /RegLocate Hrv0.
        iPoseProof (jmp_to_unknown with "Hr0V") as "Hcont".
        iNext. iIntros "H".
        iDestruct "H" as (k' n') "(HPC & Hprog_f & Hr0 & Hr1 & Hr2 & Hr3 & Hrenv)".
        iDestruct ("Hprog_f_close" with "[$HnaI $Hprog_f]") as ">HnaI". (* close *)
        (* Put the registers back in the map *)
        iDestruct (big_sepM_insert with "[$Hregs $Hr0]") as "Hregs".
        by repeat (rewrite lookup_delete_ne //;[]); rewrite lookup_delete //.
        repeat (rewrite -delete_insert_ne //;[]). rewrite insert_delete.
        iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
        by repeat (rewrite lookup_delete_ne //;[]); rewrite lookup_delete //.
        repeat (rewrite -delete_insert_ne //;[]). rewrite insert_delete.
        iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "Hregs".
        by repeat (rewrite lookup_delete_ne //;[]); rewrite lookup_delete //.
        repeat (rewrite -delete_insert_ne //;[]). rewrite insert_delete.
        iDestruct (big_sepM_insert with "[$Hregs $Hr3]") as "Hregs".
        by repeat (rewrite lookup_delete_ne //;[]); rewrite lookup_delete //.
        repeat (rewrite -delete_insert_ne //;[]). rewrite insert_delete.
        iDestruct (big_sepM_insert with "[$Hregs $Hrenv]") as "Hregs".
        by repeat (rewrite lookup_delete_ne //;[]); rewrite lookup_delete //.
        repeat (rewrite -delete_insert_ne //;[]). rewrite insert_delete.
        match goal with |- context [ ([∗ map] _↦_ ∈ ?r, _)%I ] => set rmap'' := r end.
        iApply "Hcont"; cycle 1.
        { iFrame. iApply (big_sepM_sep with "[$Hregs HrV]"). cbn beta.
          repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
          rewrite delete_insert_delete.
          iApply big_sepM_intuitionistically_forall. iModIntro.
          iIntros (r' ? Hr'). eapply lookup_delete_Some in Hr' as [? Hr'].
          unshelve iSpecialize ("HrV" $! r' _). done. by rewrite Hr'. }
        { iPureIntro. rewrite !dom_insert_L dom_delete_L dom_insert_L.
          rewrite regmap_full_dom //. set_solver+. } }
      { cbn beta. iIntros (?) "H". iIntros (->). iDestruct "H" as "[H|%]". 2: congruence.
        iApply "H". done. } }

    (* Step 4: use the fact that the continuation is in the expression relation *)
    (* put the registers back in the map *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr3]") as "Hregs".
    { apply elem_of_gmap_dom_none. set_solver+ Hrmap_dom. }
    { rewrite /interp /= !fixpoint_interp1_eq //. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "Hregs".
    { rewrite lookup_insert_ne //. apply elem_of_gmap_dom_none. set_solver+ Hrmap_dom. }
    { rewrite /interp /= !fixpoint_interp1_eq //. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr1 Hclosure]") as "Hregs".
    { rewrite !lookup_insert_ne //. apply elem_of_gmap_dom_none. set_solver+ Hrmap_dom. }
    { eauto. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr0]") as "Hregs".
    { rewrite !lookup_insert_ne //. apply elem_of_gmap_dom_none. set_solver+ Hrmap_dom. }
    { eauto. }

    iApply "Hcont_g"; cycle 1. by iFrame.
    iPureIntro. rewrite !dom_insert_L Hrmap_dom.
    rewrite !singleton_union_difference_L !all_registers_union_l. set_solver+.
  Qed.

End adder.
