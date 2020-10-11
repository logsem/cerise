From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers macros fundamental.

Section adder.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

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
    ∗ ▷ PC ↦ᵣ inr (RX, g_start, f_end, g_start)
    ∗ ▷ r_t0 ↦ᵣ w0
    ∗ ▷ r_t1 ↦ᵣ inr (RWX, act_start, act_end, act_start)
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ inr (RW, x, x', x)
    ∗ ▷ ([[ act_start, act_end ]] ↦ₐ [[ act0 ]])
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ updatePcPerm w0
         ∗ r_t0 ↦ᵣ w0
         ∗ r_t1 ↦ᵣ inr (E, act_start, act_end, act_start)
         ∗ r_t2 ↦ᵣ inl 0%Z
         ∗ r_t3 ↦ᵣ inl 0%Z
         ∗ [[ act_start, act_end ]] ↦ₐ
           [[ activation_instrs (inr (RX, f_start, f_end, f_start)) (inr (RW, x, x', x)) ]]
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
    iApply "Hφ". iDestruct "Hprog_done" as "(? & ?)". iFrame.
  Qed.

End adder.
