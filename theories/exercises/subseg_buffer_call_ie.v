From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From cap_machine Require Import malloc macros.
From cap_machine Require Import fundamental logrel rules.
From cap_machine.proofmode Require Import tactics_helpers proofmode register_tactics.
From cap_machine.examples Require Import template_adequacy.
From cap_machine.exercises Require Import subseg_buffer.
From cap_machine.examples Require Import template_adequacy template_adequacy_ocpl.
From cap_machine Require Import call_ie callback_ie.
Open Scope Z_scope.

(** Variant of the exercise where we use the call macro
    to jump to the adversary *)

(** The full program does the following:
      - allocates a region
      - stores a secret data in the newly allocated region
      - derives 2 capabilities:
        + Cs: from the beginning of the buffer to the secret address
        + Cp: from the secret address (not included) to the end of the buffer
      - calls the adversary (with the call macro)
        + locally encapsulates Cs
        + gives Cp in parameter for the adversary
      - after the call, restores the locals and asserts the integrity of
        the secret data
      - halts *)

Section program_call.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg : sealStoreG Σ}
          `{MP: MachineParameters}.
  Context {nainv: logrel_na_invs Σ}.

  (** Definition useful tactics *)
  (* Address arithmetic solver with substitution *)
  Local Ltac solve_addr' :=
    repeat match goal with x := _ |- _ => subst x end
    ; solve_addr.

  (* Set an Iris proposition as a variable: allows to hide it in Emacs
     and clarify the goal buffer *)
  Local Ltac iHide0 irisH coqH :=
    let coqH := fresh coqH in
    match goal with
    | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
        set (coqH := prop)
    end.

  Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
    iHide0 irisH coqH.

  (** Definition of the program *)

  (** P1) First part: store the secret data, derive Cp and derive Cs *)
  (* - r_mem is the register that contains the capability pointing to
     the allocated buffer
     - secret_off is the offset of the secret in the buffer
     - secret is the value stored in the buffer *)
  Definition prog_secret_instrs
    (r_mem r_mem' : RegName) (secret_off secret : Z) : list Word :=
    encodeInstrsW [Mov r_mem' r_mem ]
    ++ prog_base_instrs r_mem secret_off secret (* store data + derive Cp*)
    ++ encodeInstrsW [ (* derive Cs*)
        GetB r_t2 r_mem' ;
        GetB r_t3 r_mem' ;
        Add r_t3 r_t3 (secret_off+1) ;
        Subseg r_mem' r_t2 r_t3].

  (** P) Full program, no assumptions on the registers *)
  Definition prog_call_instrs f_m f_a (size : nat) secret_off secret_val : list Word :=
    malloc_instrs f_m size ++
    encodeInstrsW [ Mov r_t7 r_t1 ; Mov r_t1 0 ] ++
    (prog_secret_instrs r_t7 r_t8 secret_off secret_val) ++
    call_instrs f_m (offset_to_cont_call [r_t7]) r_t30 [r_t8] [r_t7] ++
    restore_locals_instrs idc [r_t8] ++
    encodeInstrsW [ (* prepare the registers for the assert macro *)
      Lea r_t8 secret_off; (* r_t8 -> (RWX, b_mem, (b_mem ^+ (secret_off+1))%a, (b_mem ^+ secret_off)%a) *)
      Load r_t4 r_t8;      (* r_t4 -> secret_val *)
      Mov r_t5 secret_val (* Prepare the assert *)
    ] ++ assert_instrs f_a ++ encodeInstrsW [ Halt ].

  Definition prog_call_code a_prog f_m f_a (size : nat) secret_off secret_val :=
    ([∗ list] a_i;w ∈ a_prog;(prog_call_instrs f_m f_a size secret_off secret_val), a_i ↦ₐ w)%I.


  (** Definition of the invariants *)
  Definition call_versionN : namespace := nroot .@ "call_version".

  (* Program invariant *)
  Definition call_codeN := (call_versionN.@"code").
  Definition prog_call_inv a f_m f_a size secret_off secret_val :=
    na_inv logrel_nais call_codeN (prog_call_code a f_m f_a size secret_off secret_val ).

  Definition malloc_call_inv b_m e_m :=
    na_inv logrel_nais ocpl.mallocN (malloc_inv b_m e_m).

  (* Assert invariant *)
  Definition assert_call_inv b_a e_a a_flag :=
    na_inv logrel_nais ocpl.assertN (assert_inv b_a a_flag e_a).

  Definition flag_call_inv a_flag flagN :=
    inv flagN (a_flag ↦ₐ WInt 0%Z) .

  Definition call_actN : namespace := call_versionN .@ "act".
  Definition call_localsN : namespace := call_versionN .@ "locals".

  (** Specifications *)
  (* Specification P1 *)
  Lemma prog_secret_spec
        r_mem r_mem' secret_off secret (* instantiation prog_base *)
        p_pc b_pc e_pc s_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w2 w3
        φ :

    let e_prog := (s_prog ^+ length (prog_secret_instrs r_mem r_mem' secret_off secret))%a in
    let a_secret := (b_mem ^+ secret_off)%a in

    (* Validity pc *)
    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc s_prog e_prog ->

    (* Validity buffer *)
    ( b_mem <= a_secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    (* Specification *)
    ⊢ (( PC ↦ᵣ WCap p_pc b_pc e_pc s_prog
         ∗ r_mem ↦ᵣ WCap p_mem b_mem e_mem b_mem
         ∗ (∃ wm, r_mem' ↦ᵣ wm)
         ∗ r_t2 ↦ᵣ w2
         ∗ r_t3 ↦ᵣ w3
         (* I'd like to generelize more this hypothesis, such that it can be
            usefull even if I don't have a region of zeroes *)
         ∗ [[b_mem, e_mem]] ↦ₐ [[ region_addrs_zeroes b_mem e_mem ]]
         ∗ codefrag s_prog (prog_secret_instrs r_mem r_mem' secret_off secret)
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
               ∗ r_mem ↦ᵣ WCap p_mem (a_secret^+1)%a e_mem a_secret
               ∗ r_mem' ↦ᵣ WCap p_mem b_mem (a_secret^+1)%a b_mem
               ∗ r_t2 ↦ᵣ WInt b_mem
               ∗ r_t3 ↦ᵣ WInt (b_mem + (secret_off+1))
               ∗ [[b_mem, a_secret]] ↦ₐ [[ region_addrs_zeroes b_mem a_secret ]]
               ∗ a_secret ↦ₐ WInt secret
               ∗ [[(a_secret ^+1)%a, e_mem]] ↦ₐ [[ region_addrs_zeroes (a_secret^+1)%a e_mem ]]
               ∗ codefrag s_prog (prog_secret_instrs r_mem r_mem' secret_off secret)
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof with (try solve_addr').
    intros e_prog a_secret.
    iIntros (Hpc_perm Hpc_bounds Hsecret_bounds Hp_mem)
            "(HPC & Hr_mem & Hr_mem' & Hr2 & Hr3 & Hmem & Hprog & Post)"
    ; iDestruct "Hr_mem'" as (wmem) "Hr_mem'".

    (* For more clarity, we split the fragments of the programs *)
    rewrite /region_mapsto /prog_secret_instrs.
    match goal with
    | h:_ |- context [codefrag _ (?l1 ++ ?l2 ++ ?l3)] =>
        set (copy_instrs := l1)
        ; set (prog_base_instrs := l2)
        ; set (secret_instrs := l3)
    end.
    simpl in e_prog; subst e_prog.

    (* Fragment 1 - copy the buffer capability *)
    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hcopy" "Hcont".
    iGo "Hcopy".
    unfocus_block "Hcopy" "Hcont" as "Hprog".

    (* Fragment 2 - execute base program (cf. subseg_buffer)
                    restrict capability to public buffer *)
    focus_block 1%nat "Hprog" as amid Hamid "Hprog_base" "Hcont".
    iApply (prog_base_spec with "[- $HPC $Hr2 $Hr3 $Hmem $Hr_mem $Hprog_base]")
    ; auto.
    iNext
    ; iIntros "(HPC & Hr_mem & Hr2 & Hr3 & Hmem & Hsecret & Hmem' & Hprog_base)".
    unfocus_block "Hprog_base" "Hcont" as "Hprog".

    (* Fragment 3 - restrict capability to secret buffer *)
    focus_block 2%nat "Hprog" as apc_secret Hapc_secret "Hprog_secret" "Hcont".
    iGo "Hprog_secret".
    { transitivity (Some (b_mem ^+ (secret_off+1))%a) ; auto ; solve_addr'. }
    { intros -> ; simpl in Hp_mem ; discriminate. }
    { intros -> ; simpl in Hp_mem ; discriminate. }
    { intros -> ; simpl in Hp_mem ; discriminate. }
    { solve_addr'. }
    unfocus_block "Hprog_secret" "Hcont" as "Hprog".

    (* Post condition *)
    iApply "Post".
    replace (apc_secret ^+ 4)%a with (s_prog ^+ 11%nat)%a by solve_addr'.
    subst a_secret.
    replace ((b_mem ^+ secret_off) ^+ 1)%a with (b_mem ^+ (secret_off+1))%a by solve_addr'.
    iFrame.
  Qed.

  (* Specification for the preparation of the registers for the assert *)
  Lemma prepa_assert_spec
    (prepa_addrs : list Addr) (a_prepa : Addr)
    (pc_p : Perm) (pc_b pc_e : Addr)
    (secret_off secret_val : Z)
    (w4 w5 : Word)
    (b_mem : Addr) EN
    φ :

    let instrs_prepa :=
      [
       encodeInstrW (Lea r_t8 secret_off);
       encodeInstrW (Load r_t4 r_t8);
       encodeInstrW (Mov r_t5 secret_val)] in
    let e_prepa := (a_prepa ^+ (length instrs_prepa))%a in

    contiguous_between prepa_addrs a_prepa e_prepa ->
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_prepa e_prepa ->

    b_mem ≤ (b_mem ^+secret_off)%a < (b_mem ^+ (secret_off + 1))%a ->

    ⊢ ( PC ↦ᵣ WCap pc_p pc_b pc_e a_prepa
          ∗ r_t8 ↦ᵣ WCap RWX b_mem (b_mem ^+ (secret_off + 1))%a b_mem
          ∗ r_t4 ↦ᵣ w4
          ∗ r_t5 ↦ᵣ w5
          ∗ (b_mem ^+ secret_off)%a ↦ₐ WInt secret_val
          ∗ codefrag a_prepa instrs_prepa
          ∗ ▷ ( PC ↦ᵣ WCap pc_p pc_b pc_e e_prepa
                  ∗ r_t8 ↦ᵣ WCap RWX b_mem (b_mem ^+ (secret_off + 1))%a (b_mem ^+ secret_off)%a
                  ∗ r_t4 ↦ᵣ WInt secret_val
                  ∗ r_t5 ↦ᵣ WInt secret_val
                  ∗ (b_mem ^+ secret_off)%a ↦ₐ WInt secret_val
                  ∗ codefrag a_prepa instrs_prepa
                -∗ WP Seq (Instr Executable) @ EN {{ φ }})%I
        -∗ WP Seq (Instr Executable) @ EN {{ φ }})%I.
  Proof.
    intros instrs_prepa e_prepa
      Hcont_prepa Hperm Hpc_valid Hmem.
    iIntros "(HPC & Hr8 & Hr4 & Hr5 & Hsecret & Hprog & Hcont)".
    codefrag_facts "Hprog".
    iInstr "Hprog".
    { transitivity (Some (b_mem ^+ secret_off)%a) ; solve_addr. }
    iInstr "Hprog".
    split ; eauto ; solve_addr.
    iInstr "Hprog".
    iApply "Hcont". iFrame.
  Qed.

  (* Full spec *)
  Lemma prog_call_full_run_spec_aux
    (* call *) wadv
    (* remaining registers *) (rmap : gmap RegName Word)
    (* pc *) a pc_p pc_b pc_e a_first a_last
    (* malloc *) f_m b_m e_m
    (* assert *) f_a b_a e_a a_flag flagN
    (* linking *) b_link a_link e_link malloc_entry assert_entry
    (size : nat) secret_off secret_val :

    (* Validity PC *)
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last →
    (* Validity linking table *)
    withinBounds b_link e_link malloc_entry = true →
    withinBounds b_link e_link assert_entry = true →
    (a_link + f_m)%a = Some malloc_entry →
    (a_link + f_a)%a = Some assert_entry →
    (* Validity secret*)
    (0 <= secret_off < size %a) ->

    dom rmap = all_registers_s ∖ {[ PC; r_t30 ]} →

    ⊢ ( prog_call_code a f_m f_a size secret_off secret_val
        ∗ malloc_call_inv b_m e_m
        ∗ assert_call_inv b_a e_a a_flag
        ∗ flag_call_inv a_flag flagN
        ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
        ∗ r_t30 ↦ᵣ wadv
        ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)

        (* Linking table *)
        ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
        ∗ malloc_entry ↦ₐ WCap E b_m e_m b_m
        ∗ assert_entry ↦ₐ WCap E b_a e_a b_a

        ∗ na_own logrel_nais ⊤
        ∗  interp wadv

       -∗ WP Seq (Instr Executable) {{λ v,
               (⌜v = HaltedV⌝ → ∃ r : Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤)%I
               ∨ ⌜v = FailedV⌝ }})%I.

  Proof with (try solve_addr').
    iIntros
      (Hpc_perm Hpc_bounds Hcont Hwb_malloc Hwb_assert Hlink_malloc Hlink_assert Hsize Hdom)
      "(Hprog& #Hinv_malloc& #Hinv_assert& #Hinv_flag& HPC& Hr30& Hrmap&
Hlink& Hentry_malloc& Hentry_assert& Hna& #Hadv)".


    (* FTLR on wadv - we do it now because of the later modality *)
    iDestruct (jmp_to_unknown with "Hadv") as "Cont".
    iHide "Cont" as cont.

    (* The program is composed of multiple part. Most of them already have their
       own specification.
       The main method is the following:
       - split the code into the different parts of the program
       - when splitting, generate hypothesis about addresses, required by solve_addr
       - for each part, prepare the resources and use the specification *)

    (* Split the program between each parts *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    rewrite /prog_call_code /prog_call_instrs.
    (* malloc *)
    iDestruct (contiguous_between_program_split with "Hprog") as
      (malloc_addrs rest1 a_clear) "(Hmalloc_prog & Hprog & #Hcont1)"
    ;[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont_malloc & Hcont_rest1 & Heqapp1 & Ha_clear).
    iDestruct (big_sepL2_length with "Hmalloc_prog") as %Hlength_malloc.
    match goal with
    | h: _ |- context [ (big_sepL2 _ _ ?instrs) ] =>
        match instrs with
        | (?l0 ++ ?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5 ++ ?l6 ) =>
            set (instrs_clear := l0)
            ; set (instrs_prog := l1)
            ; set (instrs_call := l2)
            ; set (instrs_restore := l3)
            ; set (instrs_prepa := l4)
            ; set (instrs_assert := l5)
            ; set (instrs_end := l6)
        end
    end.
    (* clear end prepare registers *)
    iDestruct (contiguous_between_program_split with "Hprog")
      as (clear_addrs rest1_addrs a_prog) "(Hclear & Hrest2 & #Hcont2)"
    ;[apply Hcont_rest1|].
    iDestruct "Hcont2" as %(Hcont_clear & Hcont_rest2 & Heqapp2 & Ha_prog).
    iDestruct (big_sepL2_length with "Hclear") as %Hlength_clear.
    iDestruct (big_sepL2_length with "Hrest2") as %Hlength_rest2.
    (* prog_base  *)
    iDestruct (contiguous_between_program_split with "Hrest2")
      as (prog_addrs rest_addrs a_call) "(Hprogi & Hrest3 & #Hcont3)"
    ;[apply Hcont_rest2|].
    iDestruct "Hcont3" as %(Hcont_prog & Hcont_rest3 & Heqapp3 & Ha_call).
    iDestruct (big_sepL2_length with "Hprogi") as %Hlength_progi.
    iDestruct (big_sepL2_length with "Hrest3") as %Hlength_rest3.
    (* call *)
    iDestruct (contiguous_between_program_split with "Hrest3")
      as (call_addrs rest2_addrs a_restore) "(Hcall & Hrest4 & #Hcont4)"
    ;[apply Hcont_rest3|].
    iDestruct "Hcont4" as %(Hcont_call & Hcont_rest4 & Heqapp4 & Ha_restore).
    iDestruct (big_sepL2_length with "Hcall") as %Hlength_call.
    iDestruct (big_sepL2_length with "Hrest4") as %Hlength_rest4.
    (* restore *)
    iDestruct (contiguous_between_program_split with "Hrest4")
      as (restore_addrs rest3_addrs a_prepa) "(Hrestore & Hrest5 & #Hcont5)"
    ;[apply Hcont_rest4|].
    iDestruct "Hcont5" as %(Hcont_restore & Hcont_rest5 & Heqapp5 & Ha_prepa).
    iDestruct (big_sepL2_length with "Hrestore") as %Hlength_restore.
    iDestruct (big_sepL2_length with "Hrest5") as %Hlength_rest5.
    (* prepa *)
    iDestruct (contiguous_between_program_split with "Hrest5")
      as (prepa_addrs rest4_addrs a_assert) "(Hprepa & Hrest6 & #Hcont6)"
    ;[apply Hcont_rest5|].
    iDestruct "Hcont6" as %(Hcont_prepa & Hcont_rest6 & Heqapp6 & Ha_assert).
    iDestruct (big_sepL2_length with "Hprepa") as %Hlength_prepa.
    iDestruct (big_sepL2_length with "Hrest6") as %Hlength_rest6.
    (* assert and end *)
    iDestruct (contiguous_between_program_split with "Hrest6")
      as (assert_addrs end_addrs a_end) "(Hassert & Hend & #Hcont7)"
    ;[apply Hcont_rest6|].
    iDestruct "Hcont7" as %(Hcont_assert & Hcont_end & Heqapp7 & Ha_end).
    iDestruct (big_sepL2_length with "Hassert") as %Hlength_assert.
    iDestruct (big_sepL2_length with "Hend") as %Hlength_end.


    (* Part 1 - Malloc *)
    (* Prepare the resource for the malloc spec *)
    iInsert "Hrmap" r_t30.
    set (rmap' :=  <[r_t30:=wadv]> rmap).
    assert (Hdom' :
              dom rmap' = all_registers_s ∖ {[PC]}).
    { subst rmap'.
      rewrite dom_insert_L.
      rewrite Hdom.
      rewrite - difference_difference_l_L.
      rewrite -union_difference_L; auto.
      set_solver.
    }
    iExtract "Hrmap" r_t31 as "Hr31".

    (* malloc specification *)
    rewrite -/(malloc _ _ _).
    iApply (wp_wand_l _ _ _ (λ v, ((_ ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)))%I. iSplitR.
    { iIntros (v) "[H|H]";auto. }

    iApply (malloc_spec _ size with
             "[- $Hmalloc_prog $Hinv_malloc $Hna $Hlink $Hentry_malloc $HPC $Hr31 $Hrmap]")
    ; eauto ; try solve_ndisj ; try lia.
    { rewrite /contiguous.isCorrectPC_range; intros.
      apply isCorrectPC_ExecPCPerm_InBounds ; auto.
      apply contiguous_between_bounds in Hcont_rest1.
      solve_addr.
    }
    { subst rmap'.
      rewrite !dom_delete_L !dom_insert_L Hdom.
      clear.
      replace ( all_registers_s ∖ {[PC; r_t30]})
        with ( ( all_registers_s ∖ {[PC]} ∖ {[r_t30]} ) ) by set_solver+.
      replace ( {[r_t30]} ∪ all_registers_s ∖ {[PC]} ∖ {[r_t30]})
      with (all_registers_s ∖ {[PC]}) ; auto.
    }
    iNext.
    iIntros "(HPC & Hmalloc_prog & Hlink & Hentry_malloc & Hreg & Hr31 & Hna & Hrmap)"
    ; iDestruct "Hreg" as (b_mem e_mem Hmem_size) "(Hr1 & Hmem)".


    (* Part 2 - Clear register *)
    (* Unlike the other part of the code, we prove this one instructions by instructions *)
    iHide "Cont" as Cont.
    iExtract "Hrmap" r_t7 as "Hr7".

    do 2 (destruct clear_addrs;[inversion Hlength_clear|]).
    simpl in *.
    apply
      contiguous_between_cons_inv_first in Hcont_clear as Heq;subst f.
    iPrologue "Hclear" ; iRename "Hprog" into "Hclear".
    iApply (wp_move_success_reg with "[$HPC $Hr7 $Hr1 $Hi]")
           ; [apply decode_encode_instrW_inv|..]
    ; auto.
    { apply isCorrectPC_ExecPCPerm_InBounds ; auto.
      apply contiguous_between_bounds in Hcont_rest2.
      solve_addr.
    }
    { transitivity (Some f0) ; auto.
      replace (a_clear + 1)%a with (a_clear + 1%nat)%a by solve_addr.
      eapply contiguous_between_incr_addr.
      eassumption.
      by simplify_map_eq.
    }
    iEpilogue "(HPC & Ha_clear & Hr7 & Hr1)".

    iPrologue "Hclear" ; iRename "Hprog" into "Hclear".
    iApply (wp_move_success_z with "[$HPC $Hr1 $Hi]")
    ; [apply decode_encode_instrW_inv|..]
    ; auto.
    { apply isCorrectPC_ExecPCPerm_InBounds ; auto.
      assert (Hcont_clear' := Hcont_clear).
      eapply (contiguous_between_incr_addr _ 1%nat _ f0 _)
        in Hcont_clear'.
      repeat (
          match goal with
          | h: contiguous_between _ _ _ |- _ =>
              apply contiguous_between_bounds in h
          end).
      split ; auto...
      by simplify_map_eq.
    }
    { transitivity (Some a_prog) ; auto.
      rewrite Hlength_clear in Ha_prog.
      rewrite <- Ha_prog.
      replace (f0 + 1)%a with (f0 + 1%nat)%a by solve_addr.
      eapply (contiguous_between_incr_addr _ 1%nat _ f0 _)
        in Hcont_clear.
      solve_addr.
      by simplify_map_eq.
    }
    (* iNext ; iIntros "(HPC & Hi & Hr7 & Hr1)". *)
    iEpilogue "(HPC & Ha_f0 & Hr1)".
    iDestruct "Hend" as "[Hend _]".

    (* Part 3 - Prog_base *)
    (* Prepare the resources for the prog_base_spec *)
    iExtract "Hrmap" r_t8 as "Hr8".

    iAssert (codefrag a_prog (prog_secret_instrs r_t7 r_t8 secret_off secret_val))
      with "[Hprogi]" as "Hprogi".
    { rewrite /codefrag. simpl. rewrite /region_mapsto.
      simpl in *.
      replace prog_addrs with (finz.seq_between a_prog (a_prog ^+ 11%nat)%a).
      done.
      symmetry.
      apply region_addrs_of_contiguous_between.
      replace (a_prog ^+ 11%nat)%a with a_call. done.
      rewrite Hlength_progi in Ha_call... }
    do 4 (rewrite delete_insert_ne ; eauto).

    (* 2 - extract r2 and r3 *)
    iExtractList "Hrmap" [r_t2;r_t3] as ["Hr2";"Hr3"].

    (* Apply the base_prog_spec *)
    iApply (prog_secret_spec with "[- $HPC $Hr2 $Hr3 $Hprogi]")
    ; auto
    ; try (iFrame ; iFrame "#")
    ; eauto...
    { simpl in *.
      apply contiguous_between_length in Hcont_call, Hcont_end.
      solve_addr'.
    }
    iSplitL "Hr8" ; first (iExists _ ; iFrame).
    iNext
    ; iIntros "(HPC & Hr7 & Hr8 & Hr2 & Hr3 & Hmem & Hsecret & Hmem' & Hprogi)"
    ; iHide "Cont" as cont
    ; iClear "Hmem".
    replace ((b_mem ^+ secret_off) ^+ 1)%a with (b_mem ^+ (secret_off+1))%a by solve_addr.
    replace ((b_mem + secret_off) + 1) with (b_mem + (secret_off+1)) by lia.

    (* Part 4 - Call *)
    (* Prepare the ressource for the call_spec *)
    iAssert ( call _ f_m r_t30 [r_t8] [r_t7])
      with "Hcall"
      as "Hcall".
    (* Re-insert r2 and r3 in the [* map] *)
    iInsertList "Hrmap" [r_t3;r_t2;r_t1].
    (* Extract r30 - adv *)
    subst rmap'.
    iExtract "Hrmap" r_t30 as "Hr30".

    set (rmap_call' := delete r_t7 _).
    set (w7 := (WCap RWX _ e_mem _ )).
    set (w8 := (WCap RWX b_mem _ _ )).
    (* Call_spec *)
    iApply (call_spec
              r_t30 ({[r_t8 := w8]}) ({[r_t7 := w7]})
              wadv _ rmap_call'
              _ _ _ _ _ a_restore
             with "[- $HPC $Hna $Hr30 $Hrmap $Hlink $Hentry_malloc]") ; cycle -1
    ; simpl
    ; eauto.
    1: iFrame "#".
    shelve.
    { repeat
        ( match goal with
          | h: contiguous_between _ _ _ |- _ =>
              apply contiguous_between_bounds in h
          end).
      split ; auto...
    }
    { replace (a_prog ^+ 11%nat)%a with (a_call) by solve_addr.
      eassumption.
    }

 (*    set_solver +. *)
    all : subst rmap_call'.
    1,2: (solve_map_dom).
    match goal with | |- _ ⊆ dom ?m => get_map_dom m as Hid; rewrite Hid end.
    set_solver+.
    Unshelve.
    iSplitL "Hcall" ; first (iNext ; rewrite !map_to_list_singleton /= ; done).
    iSplitL "Hr7"; first (iApply big_sepM_singleton; iFrame).
    iSplitL "Hr31"; first (iNext ; iExists _ ; iFrame).
    iSplitL "Hr8" ; first (iApply big_sepM_singleton; iFrame).
    iNext.
    iIntros "H" ; iDestruct "H" as
      (b_act e_act b_local e_locals a_end_call)
        "( %Hnext & %Hb_act & HPC & Hrmap & Hr7 & Hpcb & Hentry_malloc & Hr30 & Hr31 & Hact & Hlocals & Hcall & Hna )".
    rewrite map_to_list_singleton /=.

    (* ------------------ Jump to the adversary code ----------------- *)
    (** In order to jump to the adversary code, we have to prove that the context is safe,
       i.e. all the registers are safe to share.
       We need to prove that all the registers contains safe-to-share words.
       In particular the register that contains the activation code is an
       indirect sentry capability, which relies on persistent proposition only.
       Thus, we encapsulate the needed memory resources for the remaining code
       into invariants. *)


    (* Allocate the invariants necessary for the continuation *)
    (* Activation record *)

    iDestruct (region_mapsto_cons with "Hact") as "[Hb_act Hact]".
    { transitivity (Some (b_act ^+ 1)%a); solve_addr. }
    { solve_addr. }
    iDestruct (region_mapsto_single with "Hact") as "Hb_act'".
    solve_addr.
    iDestruct "Hb_act'" as (?) "[Hb_act' %]" ; simplify_eq.

    iMod (inv_alloc (logN.@b_act) ⊤ _ with "Hb_act") as "#Hact1".
    iMod (inv_alloc (logN.@(b_act ^+ 1)%a) ⊤ _ with "Hb_act'") as "#Hact2".

    (* Locals*)
    iDestruct (big_sepL2_length with "Hlocals") as %Hlength_locals
    ; rewrite finz_seq_between_length /= in Hlength_locals.
    iMod (na_inv_alloc logrel_nais _ call_localsN with "Hlocals") as "#Hlocals".
    (* Code after the call *)
    iCombine "Hrestore" "Hprepa" as "Hcallback".
    iCombine "Hcallback" "Hassert" as "Hcallback".
    iCombine "Hcallback" "Hend" as "Hcallback".
    iMod (na_inv_alloc logrel_nais _  call_codeN with "Hcallback") as
      "#Hcallback".
    (* Secret address *)
    iMod (na_inv_alloc logrel_nais _ (call_versionN.@"secret") with "Hsecret")
      as "#Hsecret".
    (* Linking table *)
    iCombine "Hentry_malloc" "Hentry_assert" as "Hlink_entries".
    iCombine "Hpcb" "Hlink_entries" as "Hlink".
    iMod (na_inv_alloc logrel_nais _ (call_versionN.@"link_table") with "Hlink")
      as "#Hinv_link".

    (* Cleaning *)
    iClear "Hclear Hmalloc_prog Ha_clear Ha_f0 Hprogi".
    (* iHide "Hact" as Hact. *)
    iHide "Hadv" as Hinterp_adv.
    iHide "Hlocals" as Hlocals.
    iHide "Hinv_link" as Hinv_link.
    iHide "Hcallback" as Hcallback.
    subst rmap_call'.

    (* Re-insert the registers into the map *)
    (* r31 *)
    iDestruct (big_sepM_to_create_gmap_default _ _ (λ k i, k ↦ᵣ i)%I (WInt 0%Z) with "Hrmap")  as "Hrmap";[apply Permutation_refl|reflexivity|].
    iDestruct (big_sepM_insert with "[$Hrmap $Hr31]") as "Hrmap".
    { apply not_elem_of_dom.
      rewrite create_gmap_default_dom list_to_set_map_to_list.
      rewrite !dom_delete_L
      ; rewrite !dom_insert_L
      ; rewrite !dom_delete_L
      ; rewrite Hdom.
      clear. set_solver.
    }
    (* r30 *)
    iDestruct (big_sepM_insert with "[$Hrmap $Hr30]") as "Hrmap".
    { apply not_elem_of_dom.
      rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list.
      rewrite !dom_delete_L
      ; rewrite !dom_insert_L
      ; rewrite !dom_delete_L
      ; rewrite Hdom.
      clear. set_solver. }
    (* r7 *)
    iDestruct (big_sepM_singleton (fun k a => k ↦ᵣ a)%I r_t7 _ with "Hr7") as "Hr7".
    iDestruct (big_sepM_insert with "[$Hrmap $Hr7]") as "Hrmap".
    { apply not_elem_of_dom.
      rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list.
      rewrite !dom_delete_L
      ; rewrite !dom_insert_L
      ; rewrite !dom_delete_L
      ; rewrite Hdom.
      clear. set_solver. }
    set rmap2 := (<[r_t7:=w7]> _).

    (* We prove that the shared buffer is indeed safe to share
       (because it is given in param) *)
    rewrite /region_mapsto.
    iDestruct (region_integers_alloc' with "Hmem'") as ">#Hinterp_buffer".
    { by apply Forall_replicate. }

    (* Prepare common hypotheses *)
    assert (isCorrectPC (WCap pc_p pc_b pc_e a_end_call)).
    { apply isCorrectPC_ExecPCPerm_InBounds ; auto.
      assert (Hcont_clear' := Hcont_clear).
      eapply (contiguous_between_incr_addr _ 1%nat _ f0 _)
        in Hcont_clear'.
      repeat (
          match goal with
          | h: contiguous_between _ _ _ |- _ =>
              apply contiguous_between_bounds in h
          end).
      split ; auto...
      by simplify_map_eq.
    }

    (* Show that the content of all the registers are safe to share *)
    iAssert (interp (WCap RWX (b_mem ^+ (secret_off + 1))%a e_mem (b_mem ^+ secret_off)%a))%I as
      "#Hbuffer_valid"; first iFrame "#"; iClear "Hbuffer_valid".
    (* The return pointer is safe to share *)
    iAssert (interp (WCap IEpair b_act e_act b_act))%I as "Hact_valid".
    { cbn beta. rewrite !fixpoint_interp1_eq.
      iIntros (r).
      iExists (cap_eq pc_p pc_b pc_e a_restore), (cap_eq RWX b_local e_locals e_locals).
      iSplit ; first (by iApply cap_eq_persistent).
      iSplit ; first (by iApply cap_eq_persistent).
      iSplit; first (by iApply inv_cap_eq).
      iSplit; first (by iApply inv_cap_eq).

      iIntros (w1 w2 regs). iNext ; iModIntro.
      iIntros "[%Hw1 %Hw2]" ; simplify_eq.
      (* need to consider 2 cases: w2 is context, or it is integer *)

      iIntros "([% #Hrmap_safe] & Hrmap & Hna)".
      iHide "Hinterp_buffer" as Hinterp_buffer.
      iHide "Hrmap_safe" as Hrmap_safe.
      rewrite /interp_conf /registers_mapsto.
      apply regmap_full_dom in H1 as H'.

      (* get all the registers we need for the remaining code *)
      iExtractList "Hrmap" [PC;idc;r_t1;r_t2;r_t3;r_t4;r_t5;r_t8] as ["HPC";"Hidc";"Hr1";"Hr2";"Hr3";"Hr4";"Hr5";"Hr8"].

      (* Code after the return of the call *)
      iMod (na_inv_acc with "Hcallback Hna") as
        "[>[[[Hrestore Hprepa] Hassert] Hend] [Hna Hcls] ]"
      ;[solve_ndisj|solve_ndisj|].

      (* 2 - restore locals *)
      iMod (na_inv_acc with "Hlocals Hna") as "[>Hlocal [Hna Hcls'] ]"
      ;[solve_ndisj|solve_ndisj|].

      iAssert (restore_locals restore_addrs idc [r_t8]) with "Hrestore" as "Hrestore".
      (* the specification of restore_locals depends on whether w2 is an integer *)

      (* prepare the hypothesis for applying restore_local_spec *)
      assert (isCorrectPC_range pc_p pc_b pc_e a_restore a_prepa) as HcorrectPC_restore.
      { split ; try eauto.
        split ; try solve_addr.
        apply contiguous_between_bounds in Hcont_end.
        solve_addr.
      }
      assert (zip [r_t8] [w8] ≡ₚ map_to_list {[r_t8 := w8]}) as Hmap_locals.
      by (by rewrite map_to_list_singleton).

      destruct Hw2 as [ -> | Hw2]; cycle 1.
      { (* is_int w2 *)
        destruct_word w2 ; cbn in Hw2 ; try contradiction ; clear Hw2.
        iApply (wp_wand with "[-]").
        iApply (restore_locals_spec_int idc {[ r_t8 := w8]} [r_t8] [w8]
                  restore_addrs pc_p pc_b pc_e a_restore _ _
                 with "[- $HPC $Hidc $Hrestore]")
        ; try eauto.
        iIntros (v) "% %"; simplify_eq.
      }
      (* case (P2 w2) *)

      iApply (restore_locals_spec _ idc {[ r_t8 := w8]} [r_t8] [w8]
                restore_addrs pc_p pc_b pc_e a_restore _ RWX b_local e_locals
               with "[- $HPC $Hidc $Hlocal $Hrestore]")
      ; try eauto.
      clear HcorrectPC_restore Hmap_locals.
      iSplitL "Hr8"; iNext.
      iApply big_sepM_singleton ; iExists _ ; iAssumption.
      iIntros "(HPC & Hidc & Hr8 & Hlocal & Hrestore)".
      simpl.
      iAssert (r_t8 ↦ᵣ w8)%I with "[Hr8]" as "Hr8".
      { iApply (big_sepM_singleton (fun k a => k ↦ᵣ a)%I r_t8 w8).
        done. }

      (* 3 - Preparation of the assert *)
      iDestruct (big_sepL2_length with "Hlocal") as %Hlength_local.
      assert ( (b_local + 1)%a = Some e_locals ) as Hsize_locals.
      { rewrite finz_seq_between_length /= /finz.dist in Hlength_local.
        clear -Hlength_local. solve_addr. }
      iDestruct (region_mapsto_single with "Hlocal") as "Hlocal" ; auto.
      iDestruct "Hlocal" as (?) "[Hlocal %Hv]".
      inversion Hv as [Hv'] ; clear Hv Hv' v.
      subst w8.
      (* The specification requires the codefrag assertions *)
      iAssert (codefrag a_prepa instrs_prepa) with "[Hprepa]" as "Hprepa".
      { rewrite /codefrag /region_mapsto.
        rewrite <- (region_addrs_of_contiguous_between prepa_addrs).
        done.
        replace (a_prepa ^+ length instrs_prepa)%a with a_assert by solve_addr.
        done. }

      iMod (na_inv_acc with "Hsecret Hna") as "[>Ha_secret [Hna Hcls_secret] ]"
      ;[solve_ndisj|solve_ndisj|].

      iApply (prepa_assert_spec
               with "[- $HPC $Hr8 $Hr4 $Hr5 $Ha_secret $Hprepa]")
      ; auto.
      { Unshelve. 2: exact prepa_addrs. cbn.
        replace (a_prepa ^+ 3%nat)%a with a_assert by solve_addr;done.
      }
      cbn.
      split ; try solve_addr.
      split ; try solve_addr.
      repeat (
          match goal with
          | h:contiguous_between _ _ _ |- _ => apply contiguous_between_bounds in h
          end) ; solve_addr.
      solve_addr.
      iNext ; iIntros "(HPC & Hr8 & Hr4 & Hr5 & Ha_secret & Hprepa)".
      simpl.
      replace (a_prepa ^+ 3%nat)%a with a_assert by solve_addr.

      (* + Cleaning + *)
      iAssert ( ([∗ list] a_i;w_i ∈ prepa_addrs;instrs_prepa, a_i ↦ₐ w_i)%I )
        with "[Hprepa]" as "Hprepa".
      { rewrite /codefrag /region_mapsto. simpl.
        replace (a_prepa ^+ 3%nat)%a with a_assert by solve_addr.
        rewrite <- (region_addrs_of_contiguous_between prepa_addrs); done.
      }
      iMod ("Hcls_secret" with "[$Ha_secret $Hna]") as "Hna".
      iMod ("Hcls'" with "[Hlocal $Hna]") as "Hna".
      { iNext. rewrite /region_mapsto.
        rewrite finz_seq_between_singleton ; auto.
        by iFrame. }

      (* 4 - Assert *)
      iMod (na_inv_acc with "Hinv_link Hna") as "[>[Hlink [Hentry_malloc Hentry_assert]] [Hna Hcls'] ]"
      ;[solve_ndisj|solve_ndisj|].
      iApply (assert_success with
               "[- $HPC $Hna $Hinv_assert $Hidc $Hr1 $Hr2 $Hr3 $Hr4 $Hr5 $Hlink $Hentry_assert]") ; eauto.
      repeat (
          match goal with
          | h:contiguous_between _ _ _ |- _ => apply contiguous_between_bounds in h
          end).
      split ; auto ; solve_addr.
      solve_ndisj.
      iSplitL "Hassert" ; first (iNext ; auto).
      iNext
      ; iIntros
          "(Hidc & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & HPC & Hassert & Hna & Hlink & Hentry_assert)".
      iMod ("Hcls'" with "[$Hentry_assert $Hentry_malloc $Hlink $Hna]") as "Hna".

      (* 5 - End - halts *)
      assert (Hcont_end' := Hcont_end).
      apply contiguous_between_cons_inv_first in Hcont_end as ->.
      wp_instr.
      iApply (wp_halt with "[$HPC $Hend]")
      ; [apply decode_encode_instrW_inv|..].
      { apply isCorrectPC_ExecPCPerm_InBounds ; auto.
        subst.
        assert ( Hcont_end:= Hcont_end').
        apply region_addrs_of_contiguous_between in Hcont_end'.
        eapply (InBounds_sub _ _ _ _ _ a_end) in Hpc_bounds.
        split ; auto...
        split ; auto...
        assert ((a_end +1)%a = Some a_last).
        { inversion Hcont_end ; subst.
          match goal with | h: contiguous_between [] _ _ |- _ => (inversion h ; subst) end.
          solve_addr. }
        solve_addr.
      }
      iNext ; iIntros "[HPC Hi]".

      (* close invariants, reassemble registers, and finish *)
      iMod ("Hcls" with "[$Hna $Hrestore $Hi $Hprepa $Hassert]") as "Hna".
      iInsertList "Hrmap" [r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t8;PC].
      wp_pure; wp_end.
      iIntros "_".
      iExists _. iFrame.
      iPureIntro.
      intros r';simpl.
      consider_next_reg r' PC.
      consider_next_reg r' r_t8.
      consider_next_reg r' r_t5.
      consider_next_reg r' r_t4.
      consider_next_reg r' r_t3.
      consider_next_reg r' r_t2.
      consider_next_reg r' r_t1.
      consider_next_reg r' idc.
      apply lookup_delete_is_Some ; split ; auto.
    }

    iAssert ([∗ map] r↦w ∈ rmap2, r ↦ᵣ w ∗ interp w)%I
      with "[Hrmap]" as "Hrmap".
    {
      (* -- It remains to prove that all the registers are safe to share -- *)
      iApply big_sepM_sep. iFrame.
      iApply big_sepM_insert_2 ; first iFrame "#". (* interp r7 *)
      iApply big_sepM_insert_2 ; first iFrame "#". (* interp r30 *)
      iApply big_sepM_insert_2 ; first iFrame "#". (* interp r31 *)
      iApply big_sepM_intro. iIntros "!>" (r ?).
      set rmap' := delete r_t7 _ .
      iIntros "%Hrmap".
      destruct ((create_gmap_default (map_to_list rmap').*1 (WInt 0%Z : Word)) !! r) eqn:Hsome.
      apply create_gmap_default_lookup_is_Some in Hsome as [Hsome ->].
      all: simplify_eq; by rewrite !fixpoint_interp1_eq.
    }

    subst cont0 Cont.
    iApply ("Cont"$! rmap2); eauto ; iFrame.
    subst rmap2.
    iPureIntro.
    rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list.
    rewrite !dom_delete_L !dom_insert_L !dom_delete_L Hdom.
    rewrite !singleton_union_difference_L.
    set_solver.
  Qed.

  (* The post-condition actually does not matter *)
  Lemma prog_call_full_run_spec
    (* call *) wadv
    (* remaining registers *) (rmap : gmap RegName Word)
    (* pc *) a pc_p pc_b pc_e a_first a_last
    (* malloc *) f_m b_m e_m
    (* assert *) f_a b_a e_a a_flag flagN
    (* linking *) b_link a_link e_link malloc_entry assert_entry
    (size : nat) secret_off secret_val :

    (* Validity PC *)
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last →
    (* Validity linking table *)
    withinBounds b_link e_link malloc_entry = true →
    withinBounds b_link e_link assert_entry = true →
    (a_link + f_m)%a = Some malloc_entry →
    (a_link + f_a)%a = Some assert_entry →
    (* Validity secret*)
    (0 <= secret_off < size %a) ->

    dom rmap = all_registers_s ∖ {[ PC; r_t30 ]} →

    ⊢ ( prog_call_code a f_m f_a size secret_off secret_val
        ∗ malloc_call_inv b_m e_m
        ∗ assert_call_inv b_a e_a a_flag
        ∗ flag_call_inv a_flag flagN
        ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
        ∗ r_t30 ↦ᵣ wadv
        ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)

        (* Linking table *)
        ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
        ∗ malloc_entry ↦ₐ WCap E b_m e_m b_m
        ∗ assert_entry ↦ₐ WCap E b_a e_a b_a

        ∗ na_own logrel_nais ⊤
        ∗ interp wadv
       -∗ WP Seq (Instr Executable) {{λ v, True}})%I.
    Proof.
      intros.
      iIntros "(?&?&?&?&Hr30&?&?&?&assert_entry&?&?&Hadv)".
      iApply (wp_wand with "[-]").
      { iApply (prog_call_full_run_spec_aux
                  wadv _ _ _ _ _ _ _ f_m b_m e_m f_a)
        ; cycle -1
        ; [iFrame|..] ; eauto. }
      iIntros (?) "?" ; done.
    Qed.
End program_call.


(** Adequacy theorem *)
Section program_call_adequacy.

(** Defininition of the memory layout *)

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Import ocpl.

Context `{ secret_off : Z , secret_val : Z, size : nat }.
Context `{ HVsize : 0 <= secret_off < size }.


Class memory_layout `{MachineParameters} := {
  (* Code of f *)
  f_region_start : Addr;
  f_start : Addr;
  f_end : Addr;
  f_size: (f_start + (length (prog_call_instrs 0 1 size secret_off secret_val)) = Some f_end)%a;
  f_region_start_offset: (f_region_start + 1)%a = Some f_start;

  (* adversary code *)
  adv_region_start : Addr;
  adv_start : Addr;
  adv_end : Addr;
  adv_instrs : list Word;
  adv_size : (adv_start + (length adv_instrs) = Some adv_end)%a ;
  adv_region_start_offset: (adv_region_start + 1)%a = Some adv_start;

  (* malloc routine *)
  l_malloc_start : Addr;
  l_malloc_memptr : Addr;
  l_malloc_mem_start : Addr;
  l_malloc_end : Addr;

  l_malloc_code_size :
    (l_malloc_start + length malloc_subroutine_instrs)%a
    = Some l_malloc_memptr;

  l_malloc_memptr_size :
    (l_malloc_memptr + 1)%a = Some l_malloc_mem_start;

  l_malloc_mem_size :
    (l_malloc_mem_start <= l_malloc_end)%a;

  (* fail routine *)
  l_assert_start : Addr;
  l_assert_cap : Addr;
  l_assert_flag : Addr;
  l_assert_end : Addr;

  l_assert_code_size :
    (l_assert_start + length assert_subroutine_instrs)%a = Some l_assert_cap;
  l_assert_cap_size :
    (l_assert_cap + 1)%a = Some l_assert_flag;
  l_assert_flag_size :
    (l_assert_flag + 1)%a = Some l_assert_end;

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 2)%a = Some link_table_end;

  (* adversary link table *)
  adv_link_table_start : Addr;
  adv_link_table_end : Addr;
  adv_link_table_size :
    (adv_link_table_start + 1)%a = Some adv_link_table_end;

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
        finz.seq_between adv_region_start adv_end;
        finz.seq_between f_region_start f_end;
        finz.seq_between link_table_start link_table_end;
        finz.seq_between adv_link_table_start adv_link_table_end;
        finz.seq_between l_assert_start l_assert_end;
        finz.seq_between l_malloc_mem_start l_malloc_end;
        [l_malloc_memptr];
        finz.seq_between l_malloc_start l_malloc_memptr
       ]
}.

Definition call_prog `{memory_layout} : prog :=
  {| prog_start := f_start ;
     prog_end := f_end ;
     prog_instrs := (prog_call_instrs 0 1 size secret_off secret_val) ;
     prog_size := f_size |}.

Definition adv_prog `{memory_layout} : prog :=
  {| prog_start := adv_start ;
     prog_end := adv_end ;
     prog_instrs := adv_instrs ;
     prog_size := adv_size |}.

Program Definition layout `{memory_layout} : ocpl_library :=
  {| (* malloc library *)
     malloc_start := l_malloc_start;
     malloc_memptr := l_malloc_memptr;
     malloc_mem_start := l_malloc_mem_start;
     malloc_end := l_malloc_end;

     malloc_code_size := l_malloc_code_size;

     malloc_memptr_size := l_malloc_memptr_size;

     malloc_mem_size := l_malloc_mem_size;

     (* assertion fail library *)
     assert_start := l_assert_start;
     assert_cap := l_assert_cap;
     assert_flag := l_assert_flag;
     assert_end := l_assert_end;

     assert_code_size := l_assert_code_size;
     assert_cap_size := l_assert_cap_size;
     assert_flag_size := l_assert_flag_size;

     (* disjointness of the two libraries *)
     libs_disjoint := _
  |}.
Next Obligation.
  intros.
  pose proof (regions_disjoint) as Hdisjoint.
  rewrite !disjoint_list_cons in Hdisjoint |- *.
  set_solver.
Qed.
Definition OCPLLibrary `{memory_layout} := library layout.

Program Definition call_table `{memory_layout} : @tbl_priv call_prog OCPLLibrary :=
  {| prog_lower_bound := f_region_start ;
     tbl_start := link_table_start ;
     tbl_end := link_table_end ;
     tbl_size := link_table_size ;
     tbl_prog_link := f_region_start_offset ;
     tbl_disj := _
  |}.
Next Obligation.
  intros. simpl.
  pose proof (regions_disjoint) as Hdisjoint.
  rewrite !disjoint_list_cons in Hdisjoint |- *.
  disjoint_map_to_list. set_solver.
Qed.

Program Definition adv_table `{memory_layout} : @tbl_pub adv_prog OCPLLibrary :=
  {| prog_lower_bound := adv_region_start ;
     tbl_start := adv_link_table_start ;
     tbl_end := adv_link_table_end ;
     tbl_size := adv_link_table_size ;
     tbl_prog_link := adv_region_start_offset ;
     tbl_disj := _
  |}.
Next Obligation.
  intros. simpl.
  pose proof (regions_disjoint) as Hdisjoint.
  rewrite !disjoint_list_cons in Hdisjoint |- *.
  disjoint_map_to_list. set_solver.
Qed.

Section prog_call_correct.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg : sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{memlayout: memory_layout}.

  Lemma prog_call_correct :
    Forall (λ w, is_z w = true \/ in_region w adv_start adv_end) adv_instrs →
    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom (flag_inv layout)) m in
  (∀ rmap,
      dom rmap = all_registers_s ∖ {[ PC; r_t30 ]} →
      ⊢ inv invN (minv_sep (flag_inv layout))
        ∗ na_inv logrel_nais mallocN (mallocInv layout)
        ∗ na_inv logrel_nais assertN (assertInv layout)
        ∗ na_own logrel_nais ⊤
        ∗ PC ↦ᵣ WCap RWX (prog_lower_bound call_table) (prog_end call_prog) (prog_start call_prog)
        ∗ r_t30 ↦ᵣ WCap RWX (prog_lower_bound adv_table) (prog_end adv_prog) (prog_start adv_prog)
        ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_z w = true⌝)
        (* P program and table *)
        ∗ (prog_lower_bound call_table) ↦ₐ (WCap RO (tbl_start call_table) (tbl_end call_table) (tbl_start call_table))
        ∗ ([∗ map] a↦w ∈ (tbl_region call_table), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ (prog_region call_prog), a ↦ₐ w)
        (* Adv program and table *)
        ∗ (prog_lower_bound adv_table) ↦ₐ (WCap RO (tbl_start adv_table) (tbl_end adv_table) (tbl_start adv_table))
        ∗ ([∗ map] a↦w ∈ (tbl_region adv_table), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ (prog_region adv_prog), a ↦ₐ w)

        -∗ WP Seq (Instr Executable) {{ λ _, True }}).
    Proof.
    iIntros (Hints Hfilter rmap Hdom) "(#Hinv & #Hmalloc & #Hassert & Hown & HPC & Hr_adv & Hrmap & Hcall_link & Hcall_table & Hcall
                                 & Hadv_link & Hadv_table & Hadv)".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hrmapvalid]".
    simpl.

    (* setting up read only example program *)
    iAssert (prog_call_code (finz.seq_between f_start f_end) 0 1 size secret_off
               secret_val) with "[Hcall] "as "Hprog".
    { rewrite /prog_call_code /prog_region /= /mkregion.
      iApply big_sepM_to_big_sepL2. apply finz_seq_between_NoDup.
      pose proof f_size as Hsize.
      rewrite finz_seq_between_length /finz.dist. solve_addr +Hsize.
      iFrame. }

    (* cleaning up the environment tables *)
    rewrite /tbl_region /mkregion /=.
    pose proof link_table_size as Hsize.
    assert (is_Some (link_table_start + 1)%a) as [link_table_mid Hmid]. solve_addr+Hsize.
    rewrite finz_seq_between_cons;[|solve_addr +Hsize].
    rewrite (addr_incr_eq Hmid) /= finz_seq_between_singleton /=;[|solve_addr +Hmid Hsize].
    pose proof adv_link_table_size as Hsize_adv.
    rewrite finz_seq_between_singleton /=;[|solve_addr +Hsize_adv].
    iDestruct (big_sepM_insert with "Hcall_table") as "[Hlink_table_start Hcall_table]".
    { rewrite lookup_insert_ne//. solve_addr +Hmid. }
    iDestruct (big_sepM_insert with "Hcall_table") as "[Hlink_table_mid _]";auto.
    iDestruct (big_sepM_insert with "Hadv_table") as "[Hadv_link_table_start _]";auto.

    (* determine malloc validity *)
    iDestruct (simple_malloc_subroutine_valid with "[$Hmalloc]") as "#Hmalloc_val".

    (* allocate adversary table *)
    iMod (inv_alloc (logN .@ adv_link_table_start) ⊤ (interp_ref_inv adv_link_table_start interp)
            with "[Hadv_link_table_start]") as "#Hadv_table_valid".
    { iNext. iExists _. iFrame. auto. }

    (* allocate validity of adversary *)
    pose proof adv_size as Hadv_size'.
    pose proof adv_region_start_offset as Hadv_region_offset.
    iDestruct (big_sepM_to_big_sepL2 with "Hadv") as "Hadv /=". apply finz_seq_between_NoDup.
    rewrite finz_seq_between_length /finz.dist /=. solve_addr+Hadv_size'.

    iAssert (|={⊤}=> interp (WCap RWX adv_start adv_end adv_start))%I with "[Hadv]" as ">#Hadv".
    { iApply (region_valid_in_region _ _ _ _ adv_instrs);auto. apply Forall_forall. intros. set_solver+. }

    iAssert (|={⊤}=> interp (WCap RWX adv_region_start adv_end adv_start))%I with "[Hadv_link]" as ">#Hadv_valid".
    { iApply fixpoint_interp1_eq. iSimpl.
      rewrite (finz_seq_between_cons adv_region_start);
        [rewrite (addr_incr_eq Hadv_region_offset) /=|solve_addr +Hadv_region_offset Hadv_size'].
      iSplitL.
      - iExists interp. iSplitL;
          [|iModIntro;iSplit;[(iPureIntro ; intros ; cbn ; apply interp_persistent)|auto] ].
        iApply inv_alloc. iNext. iExists _. iFrame.
        iApply fixpoint_interp1_eq;simpl.
        rewrite finz_seq_between_singleton// /=.
        iSplit;auto. iExists interp. iFrame "#".
        iSplit ; first (iPureIntro ; intros ; cbn ; apply interp_persistent).
        iNext. iModIntro. auto.
      - rewrite !fixpoint_interp1_eq /=. iFrame "#". done.
    }

    iApply (prog_call_full_run_spec
             with "[- $HPC $Hown $Hr_adv $Hrmap $Hprog
             $Hlink_table_start $Hlink_table_mid $Hcall_link
             $Hadv_valid]");auto ; cycle -1.
    { rewrite /malloc_call_inv /mallocInv.
      rewrite /assert_call_inv /assertInv.
      rewrite /flag_call_inv.
      iFrame "#".
      iApply (inv_iff with "Hinv []"). iNext. iModIntro.
      iSplit.
      - rewrite /minv_sep /=. iIntros "HH". iDestruct "HH" as (m) "(Hm & %Heq & %HOK)".
        assert (is_Some (m !! l_assert_flag)) as [? Hlook].
        { apply elem_of_dom. rewrite Heq. apply elem_of_singleton. auto. }
        iDestruct (big_sepM_lookup _ _ l_assert_flag with "Hm") as "Hflag";eauto.
        apply HOK in Hlook as ->. iFrame.
      - iIntros "HH". iExists {[ l_assert_flag := WInt 0%Z ]}.
        rewrite big_sepM_singleton. iFrame.
        rewrite dom_singleton_L /minv_dom /=. iSplit;auto.
        rewrite /OK_invariant. iPureIntro. intros w Hw. simplify_map_eq. done.
    }
    {apply ExecPCPerm_RWX. }
    instantiate (1:=f_end).
    { pose proof (f_region_start_offset) as HH.
      pose proof (f_size) as HH'.
      solve_addr. }
    { apply contiguous_between_of_region_addrs;auto. pose proof (f_size) as HH. solve_addr+HH. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { solve_addr. }
  Qed.
End prog_call_correct.

Theorem prog_call_adequacy `{memory_layout}
    (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory call_prog adv_prog OCPLLibrary call_table adv_table m →
  is_initial_registers call_prog adv_prog OCPLLibrary call_table adv_table reg r_t30 →
  Forall (λ w, is_z w = true \/ in_region w adv_start adv_end) (prog_instrs adv_prog) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  (∀ w, m' !! l_assert_flag = Some w → w = WInt 0%Z).
Proof.
  intros ? ? Hints ?.
  set (Σ' := #[]).
  pose proof (ocpl_template_adequacy Σ' layout call_prog adv_prog call_table adv_table) as Hadequacy.
  eapply Hadequacy;eauto.

  intros Σ ? ? ? ? ?.
  cbn.
  apply prog_call_correct.
  apply Hints.
Qed.

End program_call_adequacy.
