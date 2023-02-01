From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules macros_helpers macros.
From cap_machine Require Import rules_binary logrel_binary fundamental_binary.

Section counter.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.

  (* ----------------------------------- a counter counting up --------------------------------------- *)
  Definition r_ret := r_t31.

  Definition incr_instrs :=
    [load_r r_t1 r_env;
    add_r_z r_t1 r_t1 1;
    store_r r_env r_t1;
    move_z r_env 0;
    move_z r_t1 0; (* we now need to erase internal details about the counter! *)
    jmp r_t0].

  Definition read_instrs :=
    [load_r r_ret r_env;
    move_z r_env 0;
    move_z r_t1 0; (* the closure activation will have a copy of the PC in r_t1, so we need to clear it *)
    jmp r_t0].

  Definition incr_left a :=
    ([∗ list] a_i;w ∈ a;incr_instrs, a_i ↦ₐ w)%I.
  Definition read_left a :=
    ([∗ list] a_i;w ∈ a;read_instrs, a_i ↦ₐ w)%I.

  (* ---------------------------------- a counter counting down -------------------------------------- *)

  Definition decr_instrs :=
    [load_r r_t1 r_env;
    sub_r_z r_t1 r_t1 1;
    store_r r_env r_t1;
    move_z r_env 0;
    move_z r_t1 0; (* we now need to erase internal details about the counter! *)
    jmp r_t0].

  (* The following read function returns the positive of r_env *)
  (* Assumption: r_env contains a negative integer *)
  Definition read_neg_instrs :=
    [load_r r_ret r_env;
    sub_z_r r_ret 0 r_ret;
    move_z r_env 0;
    move_z r_t1 0; (* the closure activation will have a copy of the PC in r_t1, so we need to clear it *)
    jmp r_t0].

  Definition decr_right a :=
    ([∗ list] a_i;w ∈ a;decr_instrs, a_i ↣ₐ w)%I.
  Definition read_right a :=
    ([∗ list] a_i;w ∈ a;read_neg_instrs, a_i ↣ₐ w)%I.


  (* ---------------------------------- the counter invariant -------------------------------------- *)

  Definition counter_inv d ds : iProp Σ :=
    (∃ z, d ↦ₐ WInt z ∗ ds ↣ₐ WInt (-z)%Z)%I.

  (* ----------------------------------- INCR -------------------------------------- *)

  Lemma incr_spec pc_p pc_b pc_e pcs_p pcs_b pcs_e (* PC *)
        wret wret' (* return cap *)
        incr_addrs decr_addrs (* program addresses *)
        d d' ds ds' (* dynamically allocated memory given by preamble *)
        a_first a_last s_first s_last (* special adresses *)
        rmap smap (* registers *)
        ι1 ι (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->
    isCorrectPC_range pcs_p pcs_b pcs_e s_first s_last ->

    (* Program adresses assumptions *)
    contiguous_between incr_addrs a_first a_last ->
    contiguous_between decr_addrs s_first s_last ->

    (* malloc'ed memory assumption for the counter *)
    (d + 1)%a = Some d' ->
    (ds + 1)%a = Some ds' ->

    (* footprint of the register map *)
    dom rmap = all_registers_s ∖ {[PC;r_t0;r_env;r_t1]} →
    dom smap = all_registers_s ∖ {[PC;r_t0;r_env;r_t1]} →

    nclose specN ## ↑ι →

    {{{ spec_ctx
      ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_first ∗ PC ↣ᵣ WCap pcs_p pcs_b pcs_e s_first
      ∗ r_t0 ↦ᵣ wret ∗ r_t0 ↣ᵣ wret'
      ∗ r_env ↦ᵣ WCap RWX d d' d ∗ r_env ↣ᵣ WCap RWX ds ds' ds
      ∗ (∃ w, r_t1 ↦ᵣ w) ∗ (∃ w, r_t1 ↣ᵣ w)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      ∗ ([∗ map] r_i↦w_i ∈ smap, r_i ↣ᵣ w_i)
      (* the specification side expression *)
      ∗ ⤇ Seq (Instr Executable)
      (* invariant for d *)
      ∗ inv ι (counter_inv d ds)
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp (wret,wret')
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (incr_left incr_addrs ∗ decr_right decr_addrs)
      (* the remaining registers are all valid: we will need this for the contunuation *)
      ∗ (∀ (r : RegName) v1 v2, (⌜r ≠ PC⌝  → ⌜rmap !! r = Some v1⌝ → ⌜smap !! r = Some v2⌝ → interp (v1, v2)))
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r, ⤇ of_val HaltedV ∗ full_map r ∧ registers_mapsto r.1 ∗ spec_registers_mapsto r.2
                         ∗ na_own logrel_nais ⊤ }}}.
  Proof.
    iIntros (Hvpc1 Hvpc2 Hcont1 Hcont2 Hd1 Hd2 Hdom1 Hdom2 Hnclose φ)
            "(#Hspec & HPC & HsPC & Hr_t0 & Hs_t0 & Hr_env & Hs_env
            & Hr_t1 & Hs_t1 & Hrmap & Hsmap & Hj & #Hcounter
            & Hown & #Hcont & #Hprogs & #Hregs_valid) Hφ".
    iMod (na_inv_acc with "Hprogs Hown") as "(>(Hprog & Hsprog) & Hown & Hcls)";auto.
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    iDestruct (big_sepL2_length with "Hsprog") as %Hsprog_length.
    destruct_list incr_addrs. destruct_list decr_addrs.
    apply contiguous_between_cons_inv_first in Hcont1 as Heq. subst a.
    apply contiguous_between_cons_inv_first in Hcont2 as Heq. subst a5.
    (* Get a general purpose register *)
    iDestruct "Hr_t1" as (w1) "Hr_t1".
    iDestruct "Hs_t1" as (w1') "Hs_t1".
    (* load r_t1 r_env *)
    iPrologue_both "Hprog" "Hsprog". rewrite /counter_inv.
    iInv ι as (z) "[>Hd >Hds]" "Hcls'".
    iApply (wp_load_success_notinstr with "[$HPC $Hi $Hr_t1 $Hr_env $Hd]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont1 0|..].
    { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hd1;solve_addr. }
    iNext. iIntros "(HPC & Hr_t1 & Hprog_done & Hr_env & Hd)".
    iMod (step_load_success_alt _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1 $Hs_env $Hds]")
      as "(Hj & HsPC & Hs_t1 & Hsprog_done & Hs_env & Hds)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last| |iContiguous_next Hcont2 0|solve_ndisj|..].
    { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hd2;solve_addr. }
    iMod ("Hcls'" with "[Hd Hds]") as "_".
    { iNext. iExists z. iFrame "∗ #". }
    iModIntro. iApply wp_pure_step_later;auto;iNext;iIntros "_".
    iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";[auto|].
    (* add r_t1 r_t1 1 || sub r_t1 r_t1 1 *)
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_add_sub_lt_success_dst_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1]")
      as "(Hj & HsPC & Hsi & Hs_t1)";
      [apply decode_encode_instrW_inv|eauto|iContiguous_next Hcont2 1|iCorrectPC s_first s_last|solve_ndisj|].
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next Hcont1 1|iCorrectPC a_first a_last|].
    iEpilogue_both "(HPC & Hi & Hr_t1) /=". iCombinePtrn.
    (* store r_env r_t1 *)
    iPrologue_both "Hprog" "Hsprog".
    iInv ι as (z') "[>Hd >Hds]" "Hcls'".
    iMod (step_store_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1 $Hs_env $Hds]")
      as "(Hj & HsPC & Hsi & Hs_t1 & Hs_env & Hds)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 2| |solve_ndisj|..].
    { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hd2;solve_addr. }
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t1 $Hr_env $Hd]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 2|..].
    { auto. }
    { simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hd1;solve_addr. }
    iNext. iIntros "(HPC & Hi & Hr_t1 & Hr_env & Hd)".
    iMod ("Hcls'" with "[Hd Hds]") as "_".
    { iNext. iExists ((z + 1)%Z). assert ((- z - 1)%Z = (- (z + 1))%Z) as ->;[clear;lia|]. iFrame. }
    iModIntro. iApply wp_pure_step_later;auto;iNext;iIntros "_".
    iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";[auto|]. iCombinePtrn.
    (* move r_env 0 *)
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_env]")
      as "(Hj & HsPC & Hsi & Hs_env)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 3|auto|].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_env]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 3|].
    iEpilogue_both "(HPC & Hi & Hr_env)". iCombinePtrn.
    (* move r_env 0 *)
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1]")
      as "(Hj & HsPC & Hsi & Hs_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 4|auto|].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 4|].
    iEpilogue_both "(HPC & Hi & Hr_t1)". iCombinePtrn.
    (* jmp r_t0 *)
    iPrologue_both "Hprog" "Hsprog".
    apply (contiguous_between_last _ _ _ a4) in Hcont1 as Hlast;auto.
    apply (contiguous_between_last _ _ _ a10) in Hcont2 as Hlast';auto.
    iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0]")
      as "(Hj & HsPC & Hsi & Hs_t0)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|auto|].
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
    iDestruct (jmp_or_fail_spec with "Hspec Hcont") as "Hcallback_now".

    (* reassemble registers *)
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr_t1]") as "Hrmap".
    { apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hsmap $Hs_t1]") as "Hsmap".
    { apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
    iDestruct (big_sepM_insert _ _ r_env with "[$Hrmap $Hr_env]") as "Hrmap".
    { rewrite !lookup_insert_ne;auto. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
    iDestruct (big_sepM_insert _ _ r_env with "[$Hsmap $Hs_env]") as "Hsmap".
    { rewrite !lookup_insert_ne;auto. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }

    (* now we are ready to apply the jump or fail pattern *)
    destruct (decide (isCorrectPC (updatePcPerm wret))).
    - iDestruct "Hcallback_now" as (p b e a Heq) "Hcallback'".
      simplify_eq.
      iEpilogue_both "(HPC & Hi & Hr_t0)".
      iMod ("Hcls" with "[Hprog_done Hsprog_done Hi Hsi $Hown]") as "Hown".
      { iNext. iFrame. iDestruct "Hprog_done" as "($&$&$&$&$)". iDestruct "Hsprog_done" as "($&$&$&$&$)". iSplit; done. }
      iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr_t0]") as "Hrmap".
      { rewrite !lookup_insert_ne;auto. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
      iDestruct (big_sepM_insert _ _ r_t0 with "[$Hsmap $Hs_t0]") as "Hsmap".
      { rewrite !lookup_insert_ne;auto. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
      iDestruct (interp_eq with "Hcont") as %<-.
      set (regs' := <[PC:=WInt 0%Z]> (<[r_t0:=WCap p b e a]> (<[r_env:=WInt 0%Z]> (<[r_t1:=WInt 0%Z]> rmap)))).
      set (segs' := <[PC:=WInt 0%Z]> (<[r_t0:=WCap p b e a]> (<[r_env:=WInt 0%Z]> (<[r_t1:=WInt 0%Z]> smap)))).
      iDestruct ("Hcallback'" $! (regs',segs') with "[Hrmap Hsmap $Hj $Hown HPC HsPC]") as "[_ Hexpr]".
      { rewrite /registers_mapsto /spec_registers_mapsto /regs' /segs'.
        iSplit.
        - iClear "Hcallback' Hrmap Hsmap HPC HsPC". rewrite /interp_reg /=. iSplit.
          + iPureIntro.
            intros r'. simpl. consider_next_reg_both r' PC.
            consider_next_reg_both r' r_t0. consider_next_reg_both r' r_env.
            consider_next_reg_both r' r_t1.
            split; apply elem_of_dom;[rewrite Hdom1|rewrite Hdom2];assert (r' ∈ all_registers_s) as Hin;
              [apply all_registers_s_correct| |apply all_registers_s_correct|];revert n n0 n1 n2 Hin;clear;set_solver.
          + iIntros (r v1 v2 Hne Hv1s Hv2s).
            consider_next_reg_both1 r PC Hv1s Hv2s. done.
            consider_next_reg_both1 r r_t0 Hv1s Hv2s. by simplify_eq. consider_next_reg_both1 r r_env Hv1s Hv2s. rewrite !fixpoint_interp1_eq. simplify_eq. done.
            consider_next_reg_both1 r r_t1 Hv1s Hv2s. rewrite !fixpoint_interp1_eq. simplify_eq. done.
            iApply "Hregs_valid"; auto.
        - rewrite !insert_insert.
          iSplitL "HPC Hrmap".
          + iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
            rewrite delete_insert. iFrame.
            repeat (rewrite lookup_insert_ne;auto).
            apply not_elem_of_dom. rewrite Hdom1. clear;set_solver.
          + iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
            rewrite delete_insert. iFrame.
            repeat (rewrite lookup_insert_ne;auto).
            apply not_elem_of_dom. rewrite Hdom2. clear;set_solver.
      }
      rewrite /interp_conf. iApply wp_wand_l. iFrame "Hexpr".
      iIntros (v). iApply "Hφ".
    - iEpilogue "(HPC & Hi & Hr_t0)".
      iApply "Hcallback_now". iFrame.
      iApply "Hφ". iIntros (Hcontr); inversion Hcontr.
  Qed.

  (* ----------------------------------- READ -------------------------------------- *)

  Lemma read_spec pc_p pc_b pc_e pcs_p pcs_b pcs_e (* PC *)
        wret wret' (* return cap *)
        read_addrs read_neg_addrs (* program addresses *)
        d d' ds ds' (* dynamically allocated memory given by preamble *)
        a_first a_last s_first s_last (* special adresses *)
        rmap smap (* registers *)
        ι1 ι (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->
    isCorrectPC_range pcs_p pcs_b pcs_e s_first s_last ->

    (* Program adresses assumptions *)
    contiguous_between read_addrs a_first a_last ->
    contiguous_between read_neg_addrs s_first s_last ->

    (* malloc'ed memory assumption for the counter *)
    (d + 1)%a = Some d' ->
    (ds + 1)%a = Some ds' ->

    (* footprint of the register map *)
    dom rmap = all_registers_s ∖ {[PC;r_t0;r_env;r_t1]} →
    dom smap = all_registers_s ∖ {[PC;r_t0;r_env;r_t1]} →

    nclose specN ## ↑ι →

    {{{ spec_ctx
      ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_first ∗ PC ↣ᵣ WCap pcs_p pcs_b pcs_e s_first
      ∗ r_t0 ↦ᵣ wret ∗ r_t0 ↣ᵣ wret'
      ∗ (∃ w, r_t1 ↦ᵣ w) ∗ (∃ w, r_t1 ↣ᵣ w)
      ∗ r_env ↦ᵣ WCap RWX d d' d ∗ r_env ↣ᵣ WCap RWX ds ds' ds
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      ∗ ([∗ map] r_i↦w_i ∈ smap, r_i ↣ᵣ w_i)
      (* the specification side expression *)
      ∗ ⤇ Seq (Instr Executable)
      (* invariant for d *)
      ∗ inv ι (counter_inv d ds)
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp (wret,wret')
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (read_left read_addrs ∗ read_right read_neg_addrs)
      (* the remaining registers are all valid *)
      ∗ (∀ (r : RegName) v1 v2, (⌜r ≠ PC⌝  → ⌜rmap !! r = Some v1⌝ → ⌜smap !! r = Some v2⌝ → interp (v1, v2)))
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r, ⤇ of_val HaltedV ∗ full_map r ∧ registers_mapsto r.1 ∗ spec_registers_mapsto r.2
                         ∗ na_own logrel_nais ⊤ }}}.
  Proof.
    iIntros (Hvpc1 Hvpc2 Hcont1 Hcont2 Hd Hds Hdom1 Hdom2 Hnclose φ)
            "(#Hspec & HPC & HsPC & Hr_t0 & Hs_t0 & Hr_t1 & Hs_t1 & Hr_env & Hs_env
            & Hregs & Hsegs & Hj & #Hinv & Hown
            & #Hcallback & #Hread & #Hregs_val) Hφ".
    iMod (na_inv_acc with "Hread Hown") as "((>Hprog & >Hsprog) & Hown & Hcls)";auto.
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    iDestruct (big_sepL2_length with "Hsprog") as %Hsprog_length.
    destruct_list read_addrs. destruct_list read_neg_addrs.
    apply contiguous_between_cons_inv_first in Hcont1 as Heq. subst a.
    apply contiguous_between_cons_inv_first in Hcont2 as Heq. subst a3.
    (* Get a general purpose register *)
    assert (is_Some (rmap !! r_ret) ∧ is_Some (smap !! r_ret)) as [ [w' Hrtret] [w'' Hstret] ].
    { split; apply elem_of_dom;[rewrite Hdom1|rewrite Hdom2];apply elem_of_difference;
      split;[apply all_registers_s_correct|clear;set_solver|apply all_registers_s_correct|clear;set_solver]. }
    iDestruct (big_sepM_delete _ _ r_ret with "Hregs") as "[Hr_ret Hregs]";[eauto|].
    iDestruct (big_sepM_delete _ _ r_ret with "Hsegs") as "[Hs_ret Hsegs]";[eauto|].
    (* load r_ret r_env *)
    iPrologue_both "Hprog" "Hsprog".
    iInv ι as (z) "[>Hd >Hds]" "Hcls'".
    iApply (wp_load_success_notinstr with "[$HPC $Hi $Hr_ret $Hr_env $Hd]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont1 0|..].
    { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd;clear;solve_addr. }
    iNext. iIntros "(HPC & Hr_ret & Hprog_done & Hr_env & Hd)".
    iMod (step_load_success_alt _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_ret $Hs_env $Hds]")
      as "(Hj & HsPC & Hs_ret & Hsprog_done & Hs_env & Hds)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last| |iContiguous_next Hcont2 0|solve_ndisj|..].
    { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hds;clear;solve_addr. }
    iMod ("Hcls'" with "[Hd Hds]") as "_".
    { iNext. iExists z. iFrame "∗ #". }
    iModIntro. iApply wp_pure_step_later;auto;iNext;iIntros "_".
    iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";[auto|].
    (* SPEC ONLY: sub r_ret 0 r_ret *)
    (* This is a crucial part of the RHS such that return value will match *)
    iDestruct "Hsprog" as "[Hsi Hsprog]".
    iMod (step_add_sub_lt_success_z_dst _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_ret]")
      as "(Hj & HsPC & Hsi & Hs_ret)";
      [apply decode_encode_instrW_inv|eauto|iContiguous_next Hcont2 1|iCorrectPC s_first s_last|solve_ndisj|..].
    iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";[auto|].
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    assert (0 - - z = z)%Z as ->;[clear;lia|].
    (* move r_env 0 *)
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_env]")
      as "(Hj & HsPC & Hsi & Hs_env)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 2|solve_ndisj|].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_env]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 1|].
    iEpilogue_both "(HPC & Hi & Hr_env)". iCombinePtrn.
    (* move r_t1 0 *)
    iDestruct "Hr_t1" as (?) "Hr_t1". iDestruct "Hs_t1" as (?) "Hs_t1".
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1]")
      as "(Hj & HsPC & Hsi & Hs_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 3|solve_ndisj|].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 2|].
    iEpilogue_both "(HPC & Hi & Hr_t1)". iCombinePtrn.
    (* jmp r_t0 *)
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0]")
      as "(Hj & HsPC & Hsi & Hs_t0)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|solve_ndisj|].
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].

    (* We now want to apply the jump or fail pattern *)
    iDestruct (jmp_or_fail_spec with "Hspec Hcallback") as "Hcallback_now".

    (* reassemble registers *)
    iDestruct (big_sepM_insert _ _ r_ret with "[$Hregs $Hr_ret]") as "Hregs";[apply lookup_delete|].
    iDestruct (big_sepM_insert _ _ r_ret with "[$Hsegs $Hs_ret]") as "Hsegs";[apply lookup_delete|].
    iDestruct (big_sepM_insert _ _ r_env with "[$Hregs $Hr_env]") as "Hregs".
    { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
    iDestruct (big_sepM_insert _ _ r_env with "[$Hsegs $Hs_env]") as "Hsegs".
    { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs".
    { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hsegs $Hs_t1]") as "Hsegs".
    { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
    rewrite !insert_delete_insert.

    (* now we are ready to apply the jump or fail pattern *)
    iDestruct (interp_eq with "Hcallback") as %<-.
    destruct (decide (isCorrectPC (updatePcPerm wret))).
    - iDestruct "Hcallback_now" as (p b e a' Heq) "Hcallback'".
      simplify_eq.
      iEpilogue_both "(HPC & Hi & Hr_t0)".
      iMod ("Hcls" with "[Hprog_done Hsprog_done Hi Hsi $Hown]") as "Hown".
      { iNext. iFrame. iDestruct "Hprog_done" as "($&$&$&$)". iDestruct "Hsprog_done" as "($&$&$&$)". iSplit;done. }
      iDestruct (big_sepM_insert _ _ r_t0 with "[$Hregs $Hr_t0]") as "Hregs".
      { rewrite !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
      iDestruct (big_sepM_insert _ _ r_t0 with "[$Hsegs $Hs_t0]") as "Hsegs".
      { rewrite !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
      set (regs' := <[PC:=WInt 0%Z]> (<[r_t0:=WCap p b e a']> (<[r_t1:=WInt 0%Z]> (<[r_env:=WInt 0%Z]> (<[r_ret:=WInt z]> rmap))))).
      set (segs' := <[PC:=WInt 0%Z]> (<[r_t0:=WCap p b e a']> (<[r_t1:=WInt 0%Z]> (<[r_env:=WInt 0%Z]> (<[r_ret:=WInt z]> smap))))).
      iDestruct ("Hcallback'" $! (regs',segs') with "[Hregs Hsegs $Hj $Hown HPC HsPC]") as "[_ Hexpr]".
      { rewrite /registers_mapsto /spec_registers_mapsto /regs' /segs'.
        iSplit.
        - iClear "Hcallback' Hregs Hsegs HsPC HPC". rewrite /interp_reg /=. iSplit.
          + iPureIntro.
            intros r'. simpl.
            consider_next_reg_both r' PC. consider_next_reg_both r' r_t0. consider_next_reg_both r' r_t1. consider_next_reg_both r' r_env.
            consider_next_reg_both r' r_ret.
            assert (r' ∈ all_registers_s) as Hin;[apply all_registers_s_correct|].
            split;apply elem_of_dom;[rewrite Hdom1|rewrite Hdom2];revert n n0 n1 n2 Hin;clear;set_solver.
          + iIntros (r v1 v2 Hne Hv1s Hv2s).
            consider_next_reg_both1 r PC Hv1s Hv2s. done.
            consider_next_reg_both1 r r_t0 Hv1s Hv2s. by simplify_eq. consider_next_reg_both1 r r_t1 Hv1s Hv2s. rewrite !fixpoint_interp1_eq. simplify_eq. done.
            consider_next_reg_both1 r r_env Hv1s Hv2s. rewrite !fixpoint_interp1_eq. simplify_eq. done. consider_next_reg_both1 r r_ret Hv1s Hv2s. simplify_eq. rewrite !fixpoint_interp1_eq. done.
            iApply "Hregs_val"; auto.
        - rewrite !insert_insert.
          iSplitL "Hregs HPC".
          + iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
            rewrite delete_insert. iFrame.
            repeat (rewrite lookup_insert_ne;auto).
            apply not_elem_of_dom. rewrite Hdom1. clear;set_solver.
          + iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
            rewrite delete_insert. iFrame.
            repeat (rewrite lookup_insert_ne;auto).
            apply not_elem_of_dom. rewrite Hdom2. clear;set_solver.
      }
      rewrite /interp_conf. iApply wp_wand_l. iFrame "Hexpr".
      iIntros (v). iApply "Hφ".
    - iEpilogue "(HPC & Hi & Hr_t0)".
      iApply "Hcallback_now". iFrame.
      iApply "Hφ". iIntros (Hcontr); inversion Hcontr.
  Qed.


  (* ----------------------------------- Counter with offset -------------------------------------- *)

  Section offset_counter.
    Variable offset : Z. (* The counter offset in an arbitrary 'secret' value *)

    (* No need to change the incr function *)
    Definition offset_incr_instrs := incr_instrs.

    Definition offset_read_instrs :=
      [load_r r_ret r_env;
      sub_r_z r_ret r_ret offset;
      move_z r_env 0;
      move_z r_t1 0;
      jmp r_t0].

    Definition offset_right a :=
      ([∗ list] a_i; w ∈ a; offset_incr_instrs, a_i ↣ₐ w)%I.
    Definition offset_read_right a :=
      ([∗ list] a_i; w ∈ a; offset_read_instrs, a_i ↣ₐ w)%I.

    (* -------------- invariant -------------------- *)
    Definition offset_counter_inv d ds : iProp Σ :=
      (∃ z, d ↦ₐ WInt z ∗ ds ↣ₐ WInt (z + offset)%Z)%I.

    Lemma offset_incr_spec pc_p pc_b pc_e pcs_p pcs_b pcs_e (* PC *)
      wret wret' (* return cap *)
      incr_addrs offset_addrs (* program addresses *)
      d d' ds ds' (* dynamically allocated memory given by preamble *)
      a_first a_last s_first s_last (* special addresses *)
      rmap smap (* registers *)
      ι1 ι (* invariant names *) :

      (* PC assumptions *)
      isCorrectPC_range pc_p pc_b pc_e a_first a_last ->
      isCorrectPC_range pcs_p pcs_b pcs_e s_first s_last ->

      (* Program adresses assumptions *)
      contiguous_between incr_addrs a_first a_last ->
      contiguous_between offset_addrs s_first s_last ->

      (* malloc'ed memory assumption for the counter *)
      (d + 1)%a = Some d' ->
      (ds + 1)%a = Some ds' ->
      (* footprint of the register map *)
      dom rmap = all_registers_s ∖ {[PC;r_t0;r_env;r_t1]} →
      dom smap = all_registers_s ∖ {[PC;r_t0;r_env;r_t1]} →

      nclose specN ## ↑ι →

      {{{ spec_ctx
        ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_first ∗ PC ↣ᵣ WCap pcs_p pcs_b pcs_e s_first
        ∗ r_t0 ↦ᵣ wret                      ∗ r_t0 ↣ᵣ wret'
        ∗ r_env ↦ᵣ WCap RWX d d' d          ∗ r_env ↣ᵣ WCap RWX ds ds' ds
        ∗ (∃ w, r_t1 ↦ᵣ w)                  ∗ (∃ w, r_t1 ↣ᵣ w)
        ∗ ([∗ map] r_i ↦ w_i ∈ rmap, r_i ↦ᵣ w_i)
        ∗ ([∗ map] r_i ↦ w_i ∈ smap, r_i ↣ᵣ w_i)
        (* the specification side expression *)
        ∗ ⤇ Seq (Instr Executable)
        (* invariant for d *)
        ∗ inv ι (offset_counter_inv d ds)
        (* token which states all non atomic invariants are closed *)
        ∗ na_own logrel_nais ⊤
        (* callback validity *)
        ∗ interp (wret,wret')
        (* trusted code *)
        ∗ na_inv logrel_nais ι1 (incr_left incr_addrs ∗ offset_right offset_addrs)
        (* the remaining registers are all valid: we will need this for the contunuation *)
        ∗ (∀ (r : RegName) v1 v2, (⌜r ≠ PC⌝  → ⌜rmap !! r = Some v1⌝ → ⌜smap !! r = Some v2⌝ → interp (v1, v2)))
      }}}
        Seq (Instr Executable)
        {{{ v, RET v; ⌜v = HaltedV⌝ →
                      ∃ r, ⤇ of_val HaltedV ∗ full_map r ∧ registers_mapsto r.1 ∗ spec_registers_mapsto r.2
                          ∗ na_own logrel_nais ⊤ }}}.
    Proof.
      iIntros (Hvpc1 Hvpc2 Hcont1 Hcont2 Hd1 Hd2 Hdom1 Hdom2 Hnclose φ)
              "(#Hspec & HPC & HsPC & Hr_t0 & Hs_t0 & Hr_env & Hs_env
              & Hr_t1 & Hs_t1 & Hrmap & Hsmap & Hj & #Hcounter
              & Hown & #Hcont & #Hprogs & #Hregs_valid) Hφ".
      iMod (na_inv_acc with "Hprogs Hown") as "(>(Hprog & Hsprog) & Hown & Hcls)";auto.
      iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
      iDestruct (big_sepL2_length with "Hsprog") as %Hsprog_length.
      destruct_list incr_addrs. destruct_list offset_addrs.
      apply contiguous_between_cons_inv_first in Hcont1 as Heq. subst a.
      apply contiguous_between_cons_inv_first in Hcont2 as Heq. subst a5.
      (* Get a general purpose register *)
      iDestruct "Hr_t1" as (w1) "Hr_t1".
      iDestruct "Hs_t1" as (w1') "Hs_t1".
      (* load r_t1 r_env *)
      iPrologue_both "Hprog" "Hsprog". rewrite /offset_counter_inv.
      iInv ι as (z) "[>Hd >Hds]" "Hcls'".
      iApply (wp_load_success_notinstr with "[$HPC $Hi $Hr_t1 $Hr_env $Hd]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont1 0|..].
      { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hd1;solve_addr. }
      iNext. iIntros "(HPC & Hr_t1 & Hprog_done & Hr_env & Hd)".
      iMod (step_load_success_alt _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1 $Hs_env $Hds]")
        as "(Hj & HsPC & Hs_t1 & Hsprog_done & Hs_env & Hds)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last| |iContiguous_next Hcont2 0|solve_ndisj|..].
      { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hd2;solve_addr. }
      iMod ("Hcls'" with "[Hd Hds]") as "_".
      { iNext. iExists z. iFrame "∗ #". }
      iModIntro. iApply wp_pure_step_later;auto;iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";[auto|]. iIntros "_".
      (* add r_t1 r_t1 1 || sub r_t1 r_t1 1 *)
      iPrologue_both "Hprog" "Hsprog".
      iMod (step_add_sub_lt_success_dst_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1]")
        as "(Hj & HsPC & Hsi & Hs_t1)";
        [apply decode_encode_instrW_inv|eauto|iContiguous_next Hcont2 1|iCorrectPC s_first s_last|solve_ndisj|].
      iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|eauto|iContiguous_next Hcont1 1|iCorrectPC a_first a_last|].
      iEpilogue_both "(HPC & Hi & Hr_t1) /=". iCombinePtrn.
      (* store r_env r_t1 *)
      iPrologue_both "Hprog" "Hsprog".
      iInv ι as (z') "[>Hd >Hds]" "Hcls'".
      iMod (step_store_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1 $Hs_env $Hds]")
        as "(Hj & HsPC & Hsi & Hs_t1 & Hs_env & Hds)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 2| |solve_ndisj|..].
      { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hd2;solve_addr. }
      iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t1 $Hr_env $Hd]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 2|..].
      { auto. }
      { simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hd1;solve_addr. }
      iNext. iIntros "(HPC & Hi & Hr_t1 & Hr_env & Hd)".
      iMod ("Hcls'" with "[Hd Hds]") as "_".
      { iNext. iExists ((z + 1)%Z). assert ((z + 1 + offset)%Z = (z + offset + 1)%Z) as ->;[clear;lia|]. iFrame. }
      iModIntro. iApply wp_pure_step_later;auto;iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";[auto|]. iCombinePtrn. iIntros "_".
      (* move r_env 0 *)
      iPrologue_both "Hprog" "Hsprog".
      iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_env]")
        as "(Hj & HsPC & Hsi & Hs_env)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 3|auto|].
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_env]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 3|].
      iEpilogue_both "(HPC & Hi & Hr_env)". iCombinePtrn.
      (* move r_env 0 *)
      iPrologue_both "Hprog" "Hsprog".
      iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1]")
        as "(Hj & HsPC & Hsi & Hs_t1)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 4|auto|].
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 4|].
      iEpilogue_both "(HPC & Hi & Hr_t1)". iCombinePtrn.
      (* jmp r_t0 *)
      iPrologue_both "Hprog" "Hsprog".
      apply (contiguous_between_last _ _ _ a4) in Hcont1 as Hlast;auto.
      apply (contiguous_between_last _ _ _ a10) in Hcont2 as Hlast';auto.
      iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0]")
        as "(Hj & HsPC & Hsi & Hs_t0)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|auto|].
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iDestruct (jmp_or_fail_spec with "Hspec Hcont") as "Hcallback_now".

      (* reassemble registers *)
      iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr_t1]") as "Hrmap".
      { apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
      iDestruct (big_sepM_insert _ _ r_t1 with "[$Hsmap $Hs_t1]") as "Hsmap".
      { apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
      iDestruct (big_sepM_insert _ _ r_env with "[$Hrmap $Hr_env]") as "Hrmap".
      { rewrite !lookup_insert_ne;auto. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
      iDestruct (big_sepM_insert _ _ r_env with "[$Hsmap $Hs_env]") as "Hsmap".
      { rewrite !lookup_insert_ne;auto. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }

      (* now we are ready to apply the jump or fail pattern *)
      destruct (decide (isCorrectPC (updatePcPerm wret))).
      - iDestruct "Hcallback_now" as (p b e a Heq) "Hcallback'".
        simplify_eq.
        iEpilogue_both "(HPC & Hi & Hr_t0)".
        iMod ("Hcls" with "[Hprog_done Hsprog_done Hi Hsi $Hown]") as "Hown".
        { iNext. iFrame. iDestruct "Hprog_done" as "($&$&$&$&$)". iDestruct "Hsprog_done" as "($&$&$&$&$)". iSplit; done. }
        iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr_t0]") as "Hrmap".
        { rewrite !lookup_insert_ne;auto. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
        iDestruct (big_sepM_insert _ _ r_t0 with "[$Hsmap $Hs_t0]") as "Hsmap".
        { rewrite !lookup_insert_ne;auto. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
        iDestruct (interp_eq with "Hcont") as %<-.
        set (regs' := <[PC:=WInt 0%Z]> (<[r_t0:=WCap p b e a]> (<[r_env:=WInt 0%Z]> (<[r_t1:=WInt 0%Z]> rmap)))).
        set (segs' := <[PC:=WInt 0%Z]> (<[r_t0:=WCap p b e a]> (<[r_env:=WInt 0%Z]> (<[r_t1:=WInt 0%Z]> smap)))).
        iDestruct ("Hcallback'" $! (regs',segs') with "[Hrmap Hsmap $Hj $Hown HPC HsPC]") as "[_ Hexpr]".
        { rewrite /registers_mapsto /spec_registers_mapsto /regs' /segs'.
          iSplit.
          - iClear "Hcallback' Hrmap Hsmap HPC HsPC". rewrite /interp_reg /=. iSplit.
            + iPureIntro.
              intros r'. simpl. consider_next_reg_both r' PC.
              consider_next_reg_both r' r_t0. consider_next_reg_both r' r_env.
              consider_next_reg_both r' r_t1.
              split; apply elem_of_dom;[rewrite Hdom1|rewrite Hdom2];assert (r' ∈ all_registers_s) as Hin;
                [apply all_registers_s_correct| |apply all_registers_s_correct|];revert n n0 n1 n2 Hin;clear;set_solver.
            + iIntros (r v1 v2 Hne Hv1s Hv2s).
              consider_next_reg_both1 r PC Hv1s Hv2s. done.
              consider_next_reg_both1 r r_t0 Hv1s Hv2s. by simplify_eq. consider_next_reg_both1 r r_env Hv1s Hv2s. rewrite !fixpoint_interp1_eq. simplify_eq. done.
              consider_next_reg_both1 r r_t1 Hv1s Hv2s. rewrite !fixpoint_interp1_eq. simplify_eq. done.
              iApply "Hregs_valid"; auto.
          - rewrite !insert_insert.
            iSplitL "HPC Hrmap".
            + iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
              rewrite delete_insert. iFrame.
              repeat (rewrite lookup_insert_ne;auto).
              apply not_elem_of_dom. rewrite Hdom1. clear;set_solver.
            + iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
              rewrite delete_insert. iFrame.
              repeat (rewrite lookup_insert_ne;auto).
              apply not_elem_of_dom. rewrite Hdom2. clear;set_solver.
        }
        rewrite /interp_conf. iApply wp_wand_l. iFrame "Hexpr".
        iIntros (v). iApply "Hφ".
      - iEpilogue "(HPC & Hi & Hr_t0)".
        iApply "Hcallback_now". iFrame.
        iApply "Hφ". iIntros (Hcontr); inversion Hcontr.
    Qed.

    (* ----------------------------------- READ -------------------------------------- *)

    Lemma offset_read_spec pc_p pc_b pc_e pcs_p pcs_b pcs_e (* PC *)
          wret wret' (* return cap *)
          read_addrs read_offset_addrs (* program addresses *)
          d d' ds ds' (* dynamically allocated memory given by preamble *)
          a_first a_last s_first s_last (* special adresses *)
          rmap smap (* registers *)
          ι1 ι (* invariant names *) :

      (* PC assumptions *)
      isCorrectPC_range pc_p pc_b pc_e a_first a_last ->
      isCorrectPC_range pcs_p pcs_b pcs_e s_first s_last ->

      (* Program adresses assumptions *)
      contiguous_between read_addrs a_first a_last ->
      contiguous_between read_offset_addrs s_first s_last ->

      (* malloc'ed memory assumption for the counter *)
      (d + 1)%a = Some d' ->
      (ds + 1)%a = Some ds' ->

      (* footprint of the register map *)
      dom rmap = all_registers_s ∖ {[PC;r_t0;r_env;r_t1]} →
      dom smap = all_registers_s ∖ {[PC;r_t0;r_env;r_t1]} →

      nclose specN ## ↑ι →

      {{{ spec_ctx
        ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_first ∗ PC ↣ᵣ WCap pcs_p pcs_b pcs_e s_first
        ∗ r_t0 ↦ᵣ wret ∗ r_t0 ↣ᵣ wret'
        ∗ (∃ w, r_t1 ↦ᵣ w) ∗ (∃ w, r_t1 ↣ᵣ w)
        ∗ r_env ↦ᵣ WCap RWX d d' d ∗ r_env ↣ᵣ WCap RWX ds ds' ds
        ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
        ∗ ([∗ map] r_i↦w_i ∈ smap, r_i ↣ᵣ w_i)
        (* the specification side expression *)
        ∗ ⤇ Seq (Instr Executable)
        (* invariant for d *)
        ∗ inv ι (offset_counter_inv d ds)
        (* token which states all non atomic invariants are closed *)
        ∗ na_own logrel_nais ⊤
        (* callback validity *)
        ∗ interp (wret,wret')
        (* trusted code *)
        ∗ na_inv logrel_nais ι1 (read_left read_addrs ∗ offset_read_right read_offset_addrs)
        (* the remaining registers are all valid *)
        ∗ (∀ (r : RegName) v1 v2, (⌜r ≠ PC⌝  → ⌜rmap !! r = Some v1⌝ → ⌜smap !! r = Some v2⌝ → interp (v1, v2)))
      }}}
        Seq (Instr Executable)
        {{{ v, RET v; ⌜v = HaltedV⌝ →
                      ∃ r, ⤇ of_val HaltedV ∗ full_map r ∧ registers_mapsto r.1 ∗ spec_registers_mapsto r.2
                          ∗ na_own logrel_nais ⊤ }}}.
    Proof.
      iIntros (Hvpc1 Hvpc2 Hcont1 Hcont2 Hd Hds Hdom1 Hdom2 Hnclose φ)
              "(#Hspec & HPC & HsPC & Hr_t0 & Hs_t0 & Hr_t1 & Hs_t1 & Hr_env & Hs_env
              & Hregs & Hsegs & Hj & #Hinv & Hown
              & #Hcallback & #Hread & #Hregs_val) Hφ".
      iMod (na_inv_acc with "Hread Hown") as "((>Hprog & >Hsprog) & Hown & Hcls)";auto.
      iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
      iDestruct (big_sepL2_length with "Hsprog") as %Hsprog_length.
      destruct_list read_addrs. destruct_list read_offset_addrs.
      apply contiguous_between_cons_inv_first in Hcont1 as Heq. subst a.
      apply contiguous_between_cons_inv_first in Hcont2 as Heq. subst a3.
      (* Get a general purpose register *)
      assert (is_Some (rmap !! r_ret) ∧ is_Some (smap !! r_ret)) as [ [w' Hrtret] [w'' Hstret] ].
      { split; apply elem_of_dom;[rewrite Hdom1|rewrite Hdom2];apply elem_of_difference;
        split;[apply all_registers_s_correct|clear;set_solver|apply all_registers_s_correct|clear;set_solver]. }
      iDestruct (big_sepM_delete _ _ r_ret with "Hregs") as "[Hr_ret Hregs]";[eauto|].
      iDestruct (big_sepM_delete _ _ r_ret with "Hsegs") as "[Hs_ret Hsegs]";[eauto|].
      (* load r_ret r_env *)
      iPrologue_both "Hprog" "Hsprog".
      iInv ι as (z) "[>Hd >Hds]" "Hcls'".
      iApply (wp_load_success_notinstr with "[$HPC $Hi $Hr_ret $Hr_env $Hd]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont1 0|..].
      { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd;clear;solve_addr. }
      iNext. iIntros "(HPC & Hr_ret & Hprog_done & Hr_env & Hd)".
      iMod (step_load_success_alt _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_ret $Hs_env $Hds]")
        as "(Hj & HsPC & Hs_ret & Hsprog_done & Hs_env & Hds)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last| |iContiguous_next Hcont2 0|solve_ndisj|..].
      { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hds;clear;solve_addr. }
      iMod ("Hcls'" with "[Hd Hds]") as "_".
      { iNext. iExists z. iFrame "∗ #". }
      iModIntro. iApply wp_pure_step_later;auto;iNext;iIntros "_".
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";[auto|].
      (* SPEC ONLY: sub r_ret r_ret offset *)
      (* This is a crucial part of the RHS such that return value will match *)
      iDestruct "Hsprog" as "[Hsi Hsprog]".
      iMod (step_add_sub_lt_success_dst_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_ret]")
        as "(Hj & HsPC & Hsi & Hs_ret)";
        [apply decode_encode_instrW_inv|eauto|iContiguous_next Hcont2 1|iCorrectPC s_first s_last|solve_ndisj|..].
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";[auto|].
      iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
      assert (z + offset - offset = z)%Z as ->;[clear;lia|].
      (* move r_env 0 *)
      iPrologue_both "Hprog" "Hsprog".
      iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_env]")
        as "(Hj & HsPC & Hsi & Hs_env)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 2|solve_ndisj|].
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_env]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 1|].
      iEpilogue_both "(HPC & Hi & Hr_env)". iCombinePtrn.
      (* move r_t1 0 *)
      iDestruct "Hr_t1" as (?) "Hr_t1". iDestruct "Hs_t1" as (?) "Hs_t1".
      iPrologue_both "Hprog" "Hsprog".
      iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1]")
        as "(Hj & HsPC & Hsi & Hs_t1)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 3|solve_ndisj|].
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 2|].
      iEpilogue_both "(HPC & Hi & Hr_t1)". iCombinePtrn.
      (* jmp r_t0 *)
      iPrologue_both "Hprog" "Hsprog".
      iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0]")
        as "(Hj & HsPC & Hsi & Hs_t0)";
        [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|solve_ndisj|].
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].

      (* We now want to apply the jump or fail pattern *)
      iDestruct (jmp_or_fail_spec with "Hspec Hcallback") as "Hcallback_now".

      (* reassemble registers *)
      iDestruct (big_sepM_insert _ _ r_ret with "[$Hregs $Hr_ret]") as "Hregs";[apply lookup_delete|].
      iDestruct (big_sepM_insert _ _ r_ret with "[$Hsegs $Hs_ret]") as "Hsegs";[apply lookup_delete|].
      iDestruct (big_sepM_insert _ _ r_env with "[$Hregs $Hr_env]") as "Hregs".
      { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
      iDestruct (big_sepM_insert _ _ r_env with "[$Hsegs $Hs_env]") as "Hsegs".
      { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
      iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs".
      { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
      iDestruct (big_sepM_insert _ _ r_t1 with "[$Hsegs $Hs_t1]") as "Hsegs".
      { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
      rewrite !insert_delete_insert.

      (* now we are ready to apply the jump or fail pattern *)
      iDestruct (interp_eq with "Hcallback") as %<-.
      destruct (decide (isCorrectPC (updatePcPerm wret))).
      - iDestruct "Hcallback_now" as (p b e a' Heq) "Hcallback'".
        simplify_eq.
        iEpilogue_both "(HPC & Hi & Hr_t0)".
        iMod ("Hcls" with "[Hprog_done Hsprog_done Hi Hsi $Hown]") as "Hown".
        { iNext. iFrame. iDestruct "Hprog_done" as "($&$&$&$)". iDestruct "Hsprog_done" as "($&$&$&$)". iSplit;done. }
        iDestruct (big_sepM_insert _ _ r_t0 with "[$Hregs $Hr_t0]") as "Hregs".
        { rewrite !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom1. clear; set_solver. }
        iDestruct (big_sepM_insert _ _ r_t0 with "[$Hsegs $Hs_t0]") as "Hsegs".
        { rewrite !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom2. clear; set_solver. }
        set (regs' := <[PC:=WInt 0%Z]> (<[r_t0:=WCap p b e a']> (<[r_t1:=WInt 0%Z]> (<[r_env:=WInt 0%Z]> (<[r_ret:=WInt z]> rmap))))).
        set (segs' := <[PC:=WInt 0%Z]> (<[r_t0:=WCap p b e a']> (<[r_t1:=WInt 0%Z]> (<[r_env:=WInt 0%Z]> (<[r_ret:=WInt z]> smap))))).
        iDestruct ("Hcallback'" $! (regs',segs') with "[Hregs Hsegs $Hj $Hown HPC HsPC]") as "[_ Hexpr]".
        { rewrite /registers_mapsto /spec_registers_mapsto /regs' /segs'.
          iSplit.
          - iClear "Hcallback' Hregs Hsegs HsPC HPC". rewrite /interp_reg /=. iSplit.
            + iPureIntro.
              intros r'. simpl.
              consider_next_reg_both r' PC. consider_next_reg_both r' r_t0. consider_next_reg_both r' r_t1. consider_next_reg_both r' r_env.
              consider_next_reg_both r' r_ret.
              assert (r' ∈ all_registers_s) as Hin;[apply all_registers_s_correct|].
              split;apply elem_of_dom;[rewrite Hdom1|rewrite Hdom2];revert n n0 n1 n2 Hin;clear;set_solver.
            + iIntros (r v1 v2 Hne Hv1s Hv2s).
              consider_next_reg_both1 r PC Hv1s Hv2s. done.
              consider_next_reg_both1 r r_t0 Hv1s Hv2s. by simplify_eq. consider_next_reg_both1 r r_t1 Hv1s Hv2s. rewrite !fixpoint_interp1_eq. simplify_eq. done.
              consider_next_reg_both1 r r_env Hv1s Hv2s. rewrite !fixpoint_interp1_eq. simplify_eq. done. consider_next_reg_both1 r r_ret Hv1s Hv2s. simplify_eq. rewrite !fixpoint_interp1_eq. done.
              iApply "Hregs_val"; auto.
          - rewrite !insert_insert.
            iSplitL "Hregs HPC".
            + iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
              rewrite delete_insert. iFrame.
              repeat (rewrite lookup_insert_ne;auto).
              apply not_elem_of_dom. rewrite Hdom1. clear;set_solver.
            + iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
              rewrite delete_insert. iFrame.
              repeat (rewrite lookup_insert_ne;auto).
              apply not_elem_of_dom. rewrite Hdom2. clear;set_solver.
        }
        rewrite /interp_conf. iApply wp_wand_l. iFrame "Hexpr".
        iIntros (v). iApply "Hφ".
      - iEpilogue "(HPC & Hi & Hr_t0)".
        iApply "Hcallback_now". iFrame.
        iApply "Hφ". iIntros (Hcontr); inversion Hcontr.
    Qed.

  End offset_counter.
End counter.
