From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From cap_machine Require Import rules rules_binary addr_reg_sample.
From cap_machine.examples Require Import contiguous malloc.
From cap_machine Require Import iris_extra logrel_binary fundamental_binary.
From cap_machine.rules Require Import rules_base.

Section SimpleMalloc.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.

  (* a binary variant of the malloc spec *)
  Definition malloc_inv_binary (b e : Addr) : iProp Σ :=
    (∃ b_m a_m,
       [[b, b_m]] ↦ₐ [[ malloc_subroutine_instrs ]]
     ∗ b_m ↦ₐ (WCap RWX b_m e a_m)
     ∗ [[b, b_m]] ↣ₐ [[ malloc_subroutine_instrs ]]
     ∗ b_m ↣ₐ (WCap RWX b_m e a_m)
     ∗ [[a_m, e]] ↦ₐ [[ region_addrs_zeroes a_m e ]]
     ∗ [[a_m, e]] ↣ₐ [[ region_addrs_zeroes a_m e ]]
     ∗ ⌜(b_m < a_m)%a ∧ (a_m <= e)%a⌝
    )%I.

  Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [| a' a]; inversion Hlen; simpl
    end.

  Ltac iPrologue_single prog :=
    (try iPrologue_pre);
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iPrologue prog prog' :=
    (try iPrologue_pre);
    iDestruct prog as "[Hi Hprog]";
    iDestruct prog' as "[Hsi Hsprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac iEpilogue_both prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext;
    iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj";auto;
    iSimpl in "Hj".

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

  Lemma simple_malloc_subroutine_spec (wsize: Word) (cont cont': Word) b e rmap smap N E φ :
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1 ]} →
    dom (gset RegName) smap = all_registers_s ∖ {[ PC; r_t0; r_t1 ]} →
    (* (size > 0)%Z → *)
    ↑N ⊆ E →
    (  na_inv logrel_nais N (malloc_inv_binary b e)
     ∗ na_own logrel_nais E
     ∗ spec_ctx
     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
     ∗ ([∗ map] r↦w ∈ smap, r ↣ᵣ w)
     ∗ r_t0 ↦ᵣ cont ∗ r_t0 ↣ᵣ cont'
     ∗ PC ↦ᵣ WCap RX b e b ∗ PC ↣ᵣ WCap RX b e b
     ∗ r_t1 ↦ᵣ wsize ∗ r_t1 ↣ᵣ wsize
     ∗ ⤇ Seq (Instr Executable)
     ∗ ▷ (na_own logrel_nais E
          ∗ ([∗ map] r↦w ∈ <[r_t2 := WInt 0%Z]>
                         (<[r_t3 := WInt 0%Z]>
                         (<[r_t4 := WInt 0%Z]>
                          rmap)), r ↦ᵣ w)
          ∗ r_t0 ↦ᵣ cont
          ∗ PC ↦ᵣ updatePcPerm cont
          ∗ ([∗ map] r↦w ∈ <[r_t2 := WInt 0%Z]>
                         (<[r_t3 := WInt 0%Z]>
                         (<[r_t4 := WInt 0%Z]>
                          smap)), r ↣ᵣ w)
          ∗ r_t0 ↣ᵣ cont'
          ∗ PC ↣ᵣ updatePcPerm cont'
          ∗ ⤇ Seq (Instr Executable)
          ∗ (∃ (ba ea : Addr) size,
            ⌜wsize = WInt size⌝
            ∗ ⌜(ba + size)%a = Some ea⌝
            ∗ r_t1 ↦ᵣ WCap RWX ba ea ba
            ∗ r_t1 ↣ᵣ WCap RWX ba ea ba
            ∗ [[ba, ea]] ↦ₐ [[region_addrs_zeroes ba ea]]
            ∗ [[ba, ea]] ↣ₐ [[region_addrs_zeroes ba ea]])
          -∗ WP Seq (Instr Executable) {{ φ }}))
    ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom Hsmap_dom (* Hsize *) HN) "(#Hinv & Hna & #Hspec & Hrmap & Hsmap & Hr0 & Hs0 & HPC & HsPC & Hr1 & Hs1 & Hj & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hmalloc & Hna & Hinv_close)"; auto.
    rewrite /malloc_inv_binary.
    iDestruct "Hmalloc" as (b_m a_m) "(Hprog & Hmemptr & Hsprog & Hsmemptr & Hmem & Hsmem & Hbounds)".
    iDestruct "Hbounds" as %[Hbm_am Ham_e].
    (* Get some registers *)
    assert (is_Some (rmap !! r_t2)) as [r2w Hr2w].
    { rewrite elem_of_gmap_dom Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! r_t3)) as [r3w Hr3w].
    { rewrite elem_of_gmap_dom Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! r_t4)) as [r4w Hr4w].
    { rewrite elem_of_gmap_dom Hrmap_dom. set_solver. }
    assert (is_Some (smap !! r_t2)) as [s2w Hs2w].
    { rewrite elem_of_gmap_dom Hsmap_dom. set_solver. }
    assert (is_Some (smap !! r_t3)) as [s3w Hs3w].
    { rewrite elem_of_gmap_dom Hsmap_dom. set_solver. }
    assert (is_Some (smap !! r_t4)) as [s4w Hs4w].
    { rewrite elem_of_gmap_dom Hsmap_dom. set_solver. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr2 Hrmap]".
    eassumption.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hsmap") as "[Hs2 Hsmap]".
    eassumption.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hrmap") as "[Hr3 Hrmap]".
      by rewrite lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hsmap") as "[Hs3 Hsmap]".
      by rewrite lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t4 with "Hrmap") as "[Hr4 Hrmap]".
      by rewrite !lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t4 with "Hsmap") as "[Hs4 Hsmap]".
      by rewrite !lookup_delete_ne //.

    rewrite /(region_mapsto b b_m) /(region_mapsto_spec b b_m).
    set ai := region_addrs b b_m.
    assert (Hai: region_addrs b b_m = ai) by reflexivity.
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_len.
    cbn in Hprog_len.
    assert ((b + malloc_subroutine_instrs_length)%a = Some b_m) as Hb_bm.
    { rewrite /malloc_subroutine_instrs_length.
      rewrite region_addrs_length /region_size in Hprog_len. solve_addr. }
    assert (contiguous_between ai b b_m) as Hcont.
    { apply contiguous_between_of_region_addrs; eauto.
      rewrite /malloc_subroutine_instrs_length in Hb_bm. solve_addr. }

    assert (HPC: ∀ a, a ∈ ai → isCorrectPC (WCap RX b e a)).
    { intros a Ha.
      pose proof (contiguous_between_middle_bounds' _ _ _ _ Hcont Ha) as [? ?].
      constructor; eauto. solve_addr. }

    (* lt r_t3 0 r_t1 *)
    destruct ai as [|a l];[inversion Hprog_len|].
    destruct l as [|? l];[inversion Hprog_len|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
    iPrologue "Hprog" "Hsprog".
    destruct (wsize) as [size|].
    2: { iApply (wp_add_sub_lt_fail_z_r with "[$HPC $Hi $Hr3 $Hr1]");
         [apply decode_encode_instrW_inv|right;right;eauto|..].
         { apply HPC; repeat constructor. }
         iEpilogue "_". iApply wp_value. by iRight.
    }
    iMod (step_add_sub_lt_success_z_r _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs3 $Hs1]")
      as "(Hj & HsPC & Hsprog_done & Hs1 & Hs3)";
      [apply decode_encode_instrW_inv|right;right;eauto|iContiguous_next Hcont 0| |auto|..].
    { apply HPC; repeat constructor. }
    iApply (wp_add_sub_lt_success_z_r with "[$HPC $Hi $Hr3 $Hr1]");
      [apply decode_encode_instrW_inv|right;right;eauto|iContiguous_next Hcont 0| |..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hprog_done & Hr1 & Hr3)".
    (* move r_t2 PC *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2]")
      as "(Hj & HsPC & Hsi & Hs2)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 1|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 1| |..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* lea r_t2 4 *)
    do 3 (destruct l as [|? l];[inversion Hprog_len|]).
    assert (a0 + 4 = Some a3)%a as Hlea1.
    { apply contiguous_between_incr_addr_middle with (i:=1) (j:=4) (ai:=a0) (aj:=a3) in Hcont;auto. }
    iPrologue "Hprog" "Hsprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2]")
      as "(Hj & HsPC & Hsi & Hs2)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 2|done|done|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 2|done|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".

    (* we need do destruct on the cases for the size *)
    destruct (decide (0 < size)%Z) as [Hsize | Hsize].
    2: {
      (* the program will not jump, and go to the fail instruction *)
      (* jnz  r_t2 r_t3 *)
      assert (denote (Lt r_t3 0 r_t1) 0%nat size = 0) as ->.
      { simpl. clear -Hsize. apply Z.ltb_nlt in Hsize. rewrite Hsize. auto. }
      iPrologue "Hprog" "Hsprog".
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr2 $Hr3]");
        [apply decode_encode_instrW_inv| |iContiguous_next Hcont 3|..].
      { apply HPC; repeat constructor. }
      iEpilogue "(HPC & Hi & Hr2 & Hr3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* fail *)
      iPrologue_single "Hprog".
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|..].
      { apply HPC; repeat constructor. }
      iEpilogue "_". iApply wp_value. by iRight.
    }

    (* otherwise we continue malloc *)
    iPrologue "Hprog" "Hsprog".
    assert (denote (Lt r_t3 0 r_t1) 0%nat size = 1) as ->.
    { simpl. clear -Hsize. apply Z.ltb_lt in Hsize. rewrite Hsize. auto. }
    iMod (step_jnz_success_jmp _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2 $Hs3]")
      as "(Hj & HsPC & Hsi & Hs2 & Hs3)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 3|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr2 $Hr3]");
        [apply decode_encode_instrW_inv| |iContiguous_next Hcont 3|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2 & Hr3)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* move r_t2 PC *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    iDestruct "Hprog" as "[Hi Hprog]". iDestruct "Hsprog" as "[Hsi Hsprog]".
    iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2]")
      as "(Hj & HsPC & Hsi & Hs2)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 5|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 5| |..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2)".
    (* lea r_t2 malloc_instrs_length *)
    destruct l as [|? l];[inversion Hprog_len|].
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    iPrologue "Hprog" "Hsprog".
    assert ((a3 + (malloc_subroutine_instrs_length - 5))%a = Some b_m) as Hlea.
    { assert (b + 5 = Some a3)%a. apply contiguous_between_incr_addr with (i:=5) (ai:=a3) in Hcont;auto.
      clear -H Hb_bm. solve_addr. }
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2]")
      as "(Hj & HsPC & Hsi & Hs2)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 6|apply Hlea|done|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 6|apply Hlea|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* load r_t2 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    assert (withinBounds b e b_m = true) as Hwb.
    { apply le_addr_withinBounds.
      - generalize (contiguous_between_length _ _ _ Hcont). cbn.
        clear; solve_addr.
      - revert Hbm_am Ham_e; solve_addr. }
    (* assert ((b_m =? a5)%a = false) as Hbm_a. *)
    (* { apply Z.eqb_neq. intro. *)
    (*   pose proof (contiguous_between_middle_bounds _ 7 a5 _ _ Hcont eq_refl) as [? ?]. *)
    (*   solve_addr. } *)
    iMod (step_load_success_same_alt _ [SeqCtx] with "[$Hspec $Hj $Hsi $HsPC $Hs2 $Hsmemptr]")
      as "(Hj & HsPC & Hs2 & Hsi & Hsmemptr)";
      [auto(*FIXME*)|apply decode_encode_instrW_inv| |split;try done
       |iContiguous_next Hcont 7|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_load_success_same_notinstr with "[$HPC $Hi $Hr2 $Hmemptr]");
      [auto(*FIXME*)|apply decode_encode_instrW_inv| |split;try done
       |iContiguous_next Hcont 7|auto..].
    { apply HPC; repeat constructor. }
    { iContiguous_next Hcont 7. }
    iEpilogue_both "(HPC & Hr2 & Hi & Hmemptr)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* geta r_t3 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs3 $Hs2]")
      as "(Hj & HsPC & Hsi & Hs2 & Hs3)";
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 8|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_Get_success with "[$HPC $Hi $Hr3 $Hr2]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 8|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2 & Hr3)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    cbn [rules_Get.denote].
    (* lea_r r_t2 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    destruct (a_m + size)%a as [a_m'|] eqn:Ha_m'; cycle 1.
    { iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "-#Hregs".
        by rewrite big_sepM_empty.
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
        by apply lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
        by rewrite lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      iApply (wp_lea with "[$Hregs $Hi]");
        [apply decode_encode_instrW_inv| |done|..].
      { apply HPC; repeat constructor. }
      { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec' & ? & ?)". iDestruct "Hspec'" as %Hspec.
      destruct Hspec as [| Hfail].
      { exfalso. simplify_map_eq. }
      { cbn. iApply wp_pure_step_later; auto. iNext.
        iApply wp_value. auto. } }
    iMod (step_lea_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2 $Hs1]")
      as "(Hj & HsPC & Hsi & Hs1 & Hs2)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 9|done|done|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr2 $Hr1]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 9|done|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr1 & Hr2)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* geta r_t1 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs1 $Hs2]")
      as "(Hj & HsPC & Hsi & Hs2 & Hs1)";
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 10|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_Get_success with "[$HPC $Hi $Hr1 $Hr2]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 10|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2 & Hr1)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    cbn [rules_Get.denote].
    (* move r_t4 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs4 $Hs2]")
      as "(Hj & HsPC & Hsi & Hs4 & Hs2)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 11|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr4 $Hr2]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 11|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr4 & Hr2)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* subseg r_t4 r_t3 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    destruct (isWithin a_m a_m' b_m e) eqn:Ha_m'_within; cycle 1.
    { iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "-#Hregs".
        by rewrite big_sepM_empty.
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
        by apply lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
        by rewrite lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr3]") as "Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr4]") as "Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      iApply (wp_Subseg with "[$Hregs $Hi]");
        [apply decode_encode_instrW_inv| |done|..].
      { apply HPC; repeat constructor. }
      { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec' & ? & ?)". iDestruct "Hspec'" as %Hspec.
      destruct Hspec as [| Hfail].
      { exfalso. unfold addr_of_argument in *. simplify_map_eq.
        repeat match goal with H:_ |- _ => apply z_to_addr_eq_inv in H end; subst.
        congruence. }
      { cbn. iApply wp_pure_step_later; auto. iNext. iApply wp_value. auto. } }
    iMod (step_subseg_success _ [SeqCtx] with "[$Hj $Hspec $HsPC $Hsi $Hs4 $Hs3 $Hs1]")
      as "(Hj & HsPC & Hsi & Hs3 & Hs1 & Hs4)";
      [apply decode_encode_instrW_inv| |split;apply z_to_addr_z_of|done|done|auto..].
    { apply HPC; repeat constructor. }
    { iContiguous_next Hcont 12. }
    iApply (wp_subseg_success with "[$HPC $Hi $Hr4 $Hr3 $Hr1]");
      [apply decode_encode_instrW_inv| |apply z_to_addr_z_of|apply z_to_addr_z_of|done|done|..].
    { apply HPC; repeat constructor. }
    { iContiguous_next Hcont 12. }
    iEpilogue_both "(HPC & Hi & Hr3 & Hr1 & Hr4)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* sub r_t3 r_t3 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_add_sub_lt_success_dst_r _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs1 $Hs3]")
      as "(Hj & HsPC & Hsi & Hs1 & Hs3)";
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 13|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr1 $Hr3]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 13|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr1 & Hr3)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    cbn [denote].
    (* lea r_t4 r_t3 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_lea_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs4 $Hs3]")
      as "(Hj & HsPC & Hsi & Hs3 & Hs4)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 14| |done|auto..].
    { apply HPC; repeat constructor. }
    { transitivity (Some a_m); auto. clear; solve_addr. }
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr4 $Hr3]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 14| |done|..].
    { apply HPC; repeat constructor. }
    { transitivity (Some a_m); auto. clear; solve_addr. }
    iEpilogue_both "(HPC & Hi & Hr3 & Hr4)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* move r_t3 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs3 $Hs2]")
      as "(Hj & HsPC & Hsi & Hs3 & Hs2)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 15|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr3 $Hr2]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 15|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr3 & Hr2)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* sub r_t1 0 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_add_sub_lt_success_z_dst _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs1]")
      as "(Hj & HsPC & Hsi & Hs1)";
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 16|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_add_sub_lt_success_z_dst with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 16|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr1)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    cbn [denote].
    (* lea r_t3 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_lea_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs3 $Hs1]")
      as "(Hj & HsPC & Hsi & Hs3 & Hs1)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 17| |done|auto..].
    { apply HPC; repeat constructor. }
    { transitivity (Some 0)%a; auto. clear; solve_addr. }
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr3 $Hr1]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 17| |done|..].
    { apply HPC; repeat constructor. }
    { transitivity (Some 0)%a; auto. clear; solve_addr. }
    iEpilogue_both "(HPC & Hi & Hr1 & Hr3)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* getb r_t1 r_t3 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs1 $Hs3]")
      as "(Hj & HsPC & Hsi & Hs3 & Hs1)";
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 18|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_Get_success with "[$HPC $Hi $Hr1 $Hr3]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 18|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr3 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    cbn [rules_Get.denote].
    (* lea r_t3 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_lea_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs3 $Hs1]")
      as "(Hj & HsPC & Hsi & Hs1 & Hs3)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 19| |done|auto..].
    { apply HPC; repeat constructor. }
    { transitivity (Some b_m)%a; auto. clear; solve_addr. }
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr3 $Hr1]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 19| |done|..].
    { apply HPC; repeat constructor. }
    { transitivity (Some b_m)%a; auto. clear; solve_addr. }
    iEpilogue_both "(HPC & Hi & Hr1 & Hr3)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* store r_t3 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    assert (withinBounds b_m e b_m = true) as Hwb'.
    { apply le_addr_withinBounds.
      - generalize (contiguous_between_length _ _ _ Hcont). cbn.
        clear; solve_addr.
      - revert Hbm_am Ham_e; solve_addr. }
    iPrologue "Hprog" "Hsprog".
    iMod (step_store_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2 $Hs3 $Hsmemptr]")
      as "(Hj & HsPC & Hsi & Hs2 & Hs3 & Hsmemptr)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 20|split;try done|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr2 $Hr3 $Hmemptr]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 20|split;try done|auto|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2 & Hr3 & Hmemptr)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* move r_t1 r_t4 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs1 $Hs4]")
      as "(Hj & HsPC & Hsi & Hs1 & Hs4)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 21|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr1 $Hr4]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 21|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr1 & Hr4)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* move r_t2 0 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2]")
      as "(Hj & HsPC & Hsi & Hs2)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 22|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_move_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 22|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* move r_t3 0 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs3]")
      as "(Hj & HsPC & Hsi & Hs3)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 23|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_move_success_z with "[$HPC $Hi $Hr3]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 23|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr3)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* move r_t4 0 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs4]")
      as "(Hj & HsPC & Hsi & Hs4)";
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 24|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_move_success_z with "[$HPC $Hi $Hr4]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 24|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr4)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* jmp r_t0 *)
    iPrologue "Hprog" "Hsprog".
    iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs0]")
      as "(Hj & HsPC & Hsi & Hs0)";
      [apply decode_encode_instrW_inv|auto..].
    { apply HPC; repeat constructor. }
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply decode_encode_instrW_inv|..].
    { apply HPC; repeat constructor. }
    iEpilogue_both "(HPC & Hi & Hr0)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hsi" "Hsprog_done" as "Hsprog_done".
    (* continuation *)
    destruct l;[|inversion Hprog_len].
    assert ((a_m <= a_m')%a ∧ (a_m' <= e)%a).
    { unfold isWithin in Ha_m'_within. (* FIXME? *)
      rewrite andb_true_iff !Z.leb_le in Ha_m'_within |- *.
      revert Ha_m' Hsize; clear. solve_addr. }
    rewrite (region_addrs_zeroes_split _ a_m') //;[].
    iDestruct (region_mapsto_split _ _ a_m' with "Hmem") as "[Hmem_fresh Hmem]"; auto.
    { rewrite replicate_length //. }
    iDestruct (region_mapsto_split_spec _ _ a_m' with "Hsmem") as "[Hsmem_fresh Hsmem]"; auto.
    { rewrite replicate_length //. }
    iDestruct ("Hinv_close" with "[Hprog_done Hsprog_done Hsmemptr Hmemptr Hsmem Hmem $Hna]") as ">Hna".
    { iNext. iExists b_m, a_m'. iFrame.
      rewrite /malloc_subroutine_instrs /malloc_subroutine_instrs'.
      unfold region_mapsto. unfold region_mapsto_spec. rewrite Hai. cbn.
      do 25 iDestruct "Hprog_done" as "[? Hprog_done]". iFrame.
      do 25 iDestruct "Hsprog_done" as "[? Hsprog_done]". iFrame.
      iPureIntro. unfold isWithin in Ha_m'_within. (* FIXME? *)
      rewrite andb_true_iff !Z.leb_le in Ha_m'_within |- *.
      revert Ha_m' Hsize; clear; solve_addr. }

    iApply (wp_wand with "[-]").
    { iApply "Hφ". iFrame.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr4]") as "Hrmap".
      by rewrite lookup_delete. rewrite !insert_delete.
      iDestruct (big_sepM_insert with "[$Hsmap $Hs4]") as "Hsmap".
      by rewrite lookup_delete. rewrite !insert_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr3]") as "Hrmap".
      by rewrite lookup_insert_ne // lookup_delete //.
      iDestruct (big_sepM_insert with "[$Hsmap $Hs3]") as "Hsmap".
      by rewrite lookup_insert_ne // lookup_delete //.
      rewrite !(insert_commute _ r_t3) // !insert_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr2]") as "Hrmap".
      by rewrite !lookup_insert_ne // lookup_delete //.
      iDestruct (big_sepM_insert with "[$Hsmap $Hs2]") as "Hsmap".
      by rewrite !lookup_insert_ne // lookup_delete //.
      rewrite !(insert_commute _ r_t2 r_t4) // !(insert_commute _ r_t2 r_t3) //.
      rewrite !insert_delete.
      rewrite !(insert_commute _ r_t3 r_t2) // !(insert_commute _ r_t4 r_t2) //.
      rewrite !(insert_commute _ r_t4 r_t3) //. iFrame.
      iExists a_m, a_m', size. iFrame. auto. }
    { auto. }
  Qed.

  Ltac consider_next_reg r1 r2 :=
    destruct (decide (r1 = r2));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].

  (* same tactic, but now operating on inline hypothesis. *)
  Ltac consider_next_reg1 r1 r2 H1 H2 :=
    destruct (decide (r1 = r2));
    [ subst; rewrite lookup_insert in H1, H2; eauto | rewrite lookup_insert_ne in H1, H2; auto ].

  Lemma allocate_region_inv E ba ea :
    [[ba,ea]]↦ₐ[[region_addrs_zeroes ba ea]] ∗ [[ba,ea]]↣ₐ[[region_addrs_zeroes ba ea]]
    ={E}=∗ [∗ list] a ∈ region_addrs ba ea, (inv (logN .@ a) (logrel_binary.interp_ref_inv a logrel_binary.interp)).
  Proof.
    iIntros "[Hbae Hsbae]".
    iApply big_sepL_fupd.
    rewrite /region_mapsto /region_mapsto_spec /region_addrs_zeroes -region_addrs_length.
    iDestruct (big_sepL2_to_big_sepL_replicate with "Hbae") as "Hbae".
    iDestruct (big_sepL2_to_big_sepL_replicate with "Hsbae") as "Hsbae".
    iDestruct (big_sepL_sep with "[$Hbae $Hsbae]") as "Hbae".
    iApply (big_sepL_mono with "Hbae").
    iIntros (k y Hky) "[Ha Ha']".
    iApply inv_alloc. iNext. iExists (WInt 0%Z),(WInt 0%Z). iFrame.
    rewrite logrel_binary.fixpoint_interp1_eq. auto.
  Qed.

  Lemma simple_malloc_subroutine_valid N b e :
    na_inv logrel_nais N (malloc_inv_binary b e) -∗ spec_ctx -∗
    logrel_binary.interp (WCap E b e b, WCap E b e b).
  Proof.
    iIntros "#Hmalloc #Hspec".
    rewrite logrel_binary.fixpoint_interp1_eq /=. iSplit;auto. iIntros (r). iNext. iModIntro.
    iIntros "(#Hregs_valid & Hregs & Hsregs & Hown & Hj)".
    iDestruct (interp_reg_dupl r.1 with "Hregs_valid") as "[_ Hregs_valid']".
    iDestruct "Hregs_valid" as "[% Hregs_valid]".
    iSplit;auto.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]";[rewrite lookup_insert;eauto|].
    iDestruct (big_sepM_delete _ _ PC with "Hsregs") as "[HsPC Hsregs]";[rewrite lookup_insert;eauto|].
    destruct H with r_t0 as [ [? ?] [? ?] ].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[r_t0 Hregs]";[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hsregs") as "[s_t0 Hsregs]";[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|].
    destruct H with r_t1 as [ [? ?] [? ?] ].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[r_t1 Hregs]";[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hsregs") as "[s_t1 Hsregs]";[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|].
    iDestruct (interp_reg_eq r.1 r.2 (WCap RX b e b) with "[Hregs_valid]") as %Heq;[iSplit;auto|].
    rewrite -Heq.
    iAssert (⌜x = x0⌝)%I as %->.
    { iApply interp_eq.
      unshelve iDestruct ("Hregs_valid" $! r_t0 _ _ _ H0 H1) as "Hr0_valid";auto.
    }
    iAssert (⌜x1 = x2⌝)%I as %->.
    { iApply interp_eq.
      unshelve iDestruct ("Hregs_valid" $! r_t1 _ _ _ H2 H3) as "H";auto.
    }
    iApply (wp_wand with "[-]").
    iApply (simple_malloc_subroutine_spec with "[- $Hspec $Hj $Hown $Hmalloc $Hregs $Hsregs $r_t0 $HPC $r_t1 $s_t0 $HsPC $s_t1]"); [| |solve_ndisj|].
    4: { iSimpl. iIntros (v) "[H | ->]". iExact "H". iIntros (Hcontr); done. }
    { rewrite !dom_delete_L dom_insert_L.
      assert (∀ x : RegName, is_Some (r.1 !! x)) as H'.
      { intros x. destruct H with x;eauto. }
      apply regmap_full_dom in H' as <-. set_solver. }
    { rewrite !dom_delete_L dom_insert_L.
      assert (∀ x : RegName, is_Some (r.1 !! x)) as H'.
      { intros x. destruct H with x;eauto. }
      apply regmap_full_dom in H' as <-. set_solver. }

    unshelve iDestruct ("Hregs_valid" $! r_t0 _ _ _ H0 H1) as "-#Hr0_valid";auto.
    iDestruct (jmp_or_fail_spec with "Hspec Hr0_valid") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm x0))).
    2: { iNext. iIntros "(_ & _ & _ & HPC & _)". iApply "Hcont". iFrame. iIntros (Hcontr). done. }
    iDestruct "Hcont" as (p b' e' a Heq') "Hcont". simplify_eq.
    iNext. iIntros "(Hown & Hregs & Hr_t0 & HPC & Hsregs & Hs_t0 & HsPC & Hj & Hres)".
    iDestruct "Hres" as (ba ea size Hsizeq Hsize) "(Hr_t1 & Hs_t1 & Hbe & Hsbe)".
    (* Next is the interesting part of the spec: we must allocate the invariants making the malloced region valid *)
    iMod (allocate_region_inv with "[$Hbe $Hsbe]") as "#Hbe".
    rewrite -!(delete_insert_ne _ r_t1)//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert with "[$Hsregs $Hs_t1]") as "Hsregs";[apply lookup_delete|rewrite insert_delete].
    rewrite -!(delete_insert_ne _ r_t0)//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs";[apply lookup_delete|rewrite insert_delete delete_insert_delete].
    iDestruct (big_sepM_insert with "[$Hsregs $Hs_t0]") as "Hsregs";[apply lookup_delete|rewrite insert_delete].
    rewrite -!(delete_insert_ne _ PC)//.
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert with "[$Hsregs $HsPC]") as "Hsregs";[apply lookup_delete|rewrite insert_delete].
    set regs := <[PC:=updatePcPerm (WCap p b' e' a)]>
                            (<[r_t0:=WCap p b' e' a]> (<[r_t1:=WCap RWX ba ea ba]> (<[r_t2:=WInt 0%Z]> (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]> r.1))))).
    iDestruct ("Hcont" $! (regs,regs) with "[$Hown Hregs Hsregs Hbe $Hj]") as "[_ $]".
    iSplitR "Hregs Hsregs".
    { rewrite /regs. iSplit.
      - iPureIntro. intros x. consider_next_reg x PC. consider_next_reg x r_t0. consider_next_reg x r_t1.
        consider_next_reg x r_t2. consider_next_reg x r_t3. consider_next_reg x r_t4. destruct H with x;auto.
      - iIntros (x v1 v2 Hne Hv1s Hv2s).
        consider_next_reg1 x PC Hv1s Hv2s ; [contradiction|].
        consider_next_reg1 x r_t0 Hv1s Hv2s.
        { cbn. iDestruct ("Hregs_valid'" $! r_t0 _ _ n H0 H0) as "-#Hr0_valid";auto.  iFrame. by simplify_eq. }
        consider_next_reg1 x r_t1 Hv1s Hv2s.
        { inversion Hv1s. inversion Hv2s. rewrite logrel_binary.fixpoint_interp1_eq /=. iSplit;auto. iApply (big_sepL_mono with "Hbe").
          iIntros (k y Hky) "Ha". iExists logrel_binary.interp. iFrame. rewrite /interp /fixpoint_interp1_eq /=. iSplit;auto. }
        consider_next_reg1 x r_t2 Hv1s Hv2s. inversion Hv1s. inversion Hv2s. by rewrite logrel_binary.fixpoint_interp1_eq.
        consider_next_reg1 x r_t3 Hv1s Hv2s. inversion Hv1s. inversion Hv2s. by rewrite logrel_binary.fixpoint_interp1_eq.
        consider_next_reg1 x r_t4 Hv1s Hv2s. inversion Hv1s. inversion Hv2s. by rewrite logrel_binary.fixpoint_interp1_eq.
        iApply "Hregs_valid'"; auto.
    }
    { rewrite /regs. rewrite insert_insert /=. iFrame. }
  Qed.


End SimpleMalloc.
