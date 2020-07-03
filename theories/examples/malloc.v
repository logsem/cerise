From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From cap_machine Require Import rules logrel addr_reg_sample.
From cap_machine.examples Require Import contiguous.

Section SimpleMalloc.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [| a' a]; inversion Hlen; simpl
    end.

  Ltac iPrologue prog :=
    (try iPrologue_pre);
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

  Definition malloc_subroutine_instrs' (offset: Z) :=
    [move_r r_t2 PC;
     lea_z r_t2 offset;
     load_r r_t2 r_t2;
     geta r_t3 r_t2;
     lea_r r_t2 r_t1;
     geta r_t1 r_t2;
     move_r r_t4 r_t2;
     subseg_r_r r_t4 r_t3 r_t1;
     sub_r_r r_t3 r_t3 r_t1;
     lea_r r_t4 r_t3;
     move_r r_t3 r_t2;
     sub_z_r r_t1 0%Z r_t1;
     lea_r r_t3 r_t1;
     getb r_t1 r_t3;
     lea_r r_t3 r_t1;
     store_r r_t3 r_t2;
     move_r r_t1 r_t4;
     move_z r_t2 0%Z;
     move_z r_t3 0%Z;
     move_z r_t4 0%Z;
     jmp r_t0].

  Definition malloc_subroutine_instrs_length : Z :=
    Eval cbv in (length (malloc_subroutine_instrs' 0%Z)).

  Definition malloc_subroutine_instrs :=
    malloc_subroutine_instrs' malloc_subroutine_instrs_length.

  Definition malloc_inv (b e : Addr) : iProp Σ :=
    (∃ b_m a_m,
       [[b, b_m]] ↦ₐ[RX] [[ malloc_subroutine_instrs ]]
     ∗ b_m ↦ₐ[RWX] (inr (RWX, Global, b_m, e, a_m))
     ∗ [[a_m, e]] ↦ₐ[RWX] [[ region_addrs_zeroes a_m e ]]
     ∗ ⌜(b_m < a_m)%a ∧ (a_m <= e)%a⌝
    )%I.

  Lemma z_to_addr_z_of (a:Addr) :
    z_to_addr a = Some a.
  Proof.
    generalize (addr_spec a); intros [? ?].
    set (z := (z_of a)) in *.
    unfold z_to_addr.
    destruct (Z_le_dec z MemNum) eqn:?;
    destruct (Z_le_dec 0 z) eqn:?.
    { f_equal. apply z_of_eq. cbn. lia. }
    all: lia.
  Qed.

  Lemma z_to_addr_eq_inv (a b:Addr) :
    z_to_addr a = Some b → a = b.
  Proof. rewrite z_to_addr_z_of. naive_solver. Qed.

  Lemma simple_malloc_subroutine_spec (size: Z) (cont: Word) b e rmap N E φ :
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1 ]} →
    (size > 0)%Z →
    ↑N ⊆ E →
    (  na_inv logrel_nais N (malloc_inv b e)
     ∗ na_own logrel_nais E
     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
     ∗ r_t0 ↦ᵣ cont
     ∗ PC ↦ᵣ inr (RX, Global, b, e, b)
     ∗ r_t1 ↦ᵣ inl size
     ∗ ▷ ((na_own logrel_nais E
          ∗ [∗ map] r↦w ∈ <[r_t2 := inl 0%Z]>
                         (<[r_t3 := inl 0%Z]>
                         (<[r_t4 := inl 0%Z]>
                          rmap)), r ↦ᵣ w)
          ∗ r_t0 ↦ᵣ cont
          ∗ PC ↦ᵣ updatePcPerm cont
          ∗ (∃ (ba ea : Addr),
            ⌜(ba + size)%a = Some ea⌝
            ∗ r_t1 ↦ᵣ inr (RWX, Global, ba, ea, ba)
            ∗ [[ba, ea]] ↦ₐ[RWX] [[region_addrs_zeroes ba ea]])
          -∗ WP Seq (Instr Executable) {{ φ }}))
    ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom Hsize HN) "(#Hinv & Hna & Hrmap & Hr0 & HPC & Hr1 & Hφ)".
    iMod (na_inv_open with "Hinv Hna") as "(>Hmalloc & Hna & Hinv_close)"; auto.
    rewrite /malloc_inv.
    iDestruct "Hmalloc" as (b_m a_m) "(Hprog & Hmemptr & Hmem & Hbounds)".
    iDestruct "Hbounds" as %[Hbm_am Ham_e].
    (* Get some registers *)
    assert (is_Some (rmap !! r_t2)) as [r2w Hr2w].
    { rewrite elem_of_gmap_dom Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! r_t3)) as [r3w Hr3w].
    { rewrite elem_of_gmap_dom Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! r_t4)) as [r4w Hr4w].
    { rewrite elem_of_gmap_dom Hrmap_dom. set_solver. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr2 Hrmap]".
      eassumption.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hrmap") as "[Hr3 Hrmap]".
      by rewrite lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t4 with "Hrmap") as "[Hr4 Hrmap]".
      by rewrite !lookup_delete_ne //.

    rewrite /(region_mapsto b b_m).
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

    assert (HPC: ∀ a, a ∈ ai → isCorrectPC (inr (RX, Global, b, e, a))).
    { intros a Ha.
      pose proof (contiguous_between_middle_bounds' _ _ _ _ Hcont Ha) as [? ?].
      constructor; eauto. solve_addr. }

    (* move r_t2 PC *)
    destruct ai as [|a l];[inversion Hprog_len|].
    destruct l as [|? l];[inversion Hprog_len|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 0|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hprog_done & Hr2)".
    (* lea r_t2 malloc_instrs_length *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 1|done|done|done|..].
    { apply HPC; repeat constructor. }
    { simpl; auto. }
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_t2 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    (* FIXME *)
    assert ((b_m =? a)%a = false) as Hbm_a.
    { apply Z.eqb_neq. intro.
      pose proof (contiguous_between_middle_bounds _ 2 a _ _ Hcont eq_refl) as [? ?].
      solve_addr. }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr2 Hmemptr]");
      [auto(*FIXME*)|apply decode_encode_instrW_inv|done| |split;try done
       |iContiguous_next Hcont 2|..].
    { apply HPC; repeat constructor. }
    { apply le_addr_withinBounds.
      - generalize (contiguous_between_length _ _ _ Hcont). cbn.
        clear; solve_addr.
      - revert Hbm_am Ham_e; solve_addr. }
    { rewrite Hbm_a; iFrame. done. }
    rewrite Hbm_a. iEpilogue "(HPC & Hr2 & Hi & Hmemptr)".
    iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* geta r_t3 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr3 $Hr2]");
      [apply decode_encode_instrW_inv|done|done| |iContiguous_next Hcont 3|done|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr2 & Hr3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    cbn [rules_Get.denote].
    (* lea_r r_t2 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    destruct (a_m + size)%a as [a_m'|] eqn:Ha_m'; cycle 1.
    { iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "Hregs".
        by rewrite big_sepM_empty.
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
        by apply lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
        by rewrite lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      iApply (wp_lea with "[$Hregs $Hi]");
        [apply decode_encode_instrW_inv|done| |done|..].
      { apply HPC; repeat constructor. }
      { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec & ? & ?)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [| Hfail].
      { exfalso. simplify_map_eq. }
      { cbn. iApply wp_pure_step_later; auto. iNext.
        iApply wp_value. auto. } }
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr2 $Hr1]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 4|done|done|done|..].
    { apply HPC; repeat constructor. }
    { simpl; auto. }
    iEpilogue "(HPC & Hi & Hr1 & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* geta r_t1 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr1 $Hr2]");
      [apply decode_encode_instrW_inv|done|done| |iContiguous_next Hcont 5|done|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    cbn [rules_Get.denote].
    (* move r_t4 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr4 $Hr2]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 6|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr4 & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* subseg r_t4 r_t3 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    destruct (isWithin a_m a_m' b_m e) eqn:Ha_m'_within; cycle 1.
    { iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "Hregs".
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
        [apply decode_encode_instrW_inv|done| |done|..].
      { apply HPC; repeat constructor. }
      { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec & ? & ?)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [| Hfail].
      { exfalso. unfold addr_of_argument in *. simplify_map_eq.
        repeat match goal with H:_ |- _ => apply z_to_addr_eq_inv in H end; subst.
        congruence. }
      { cbn. iApply wp_pure_step_later; auto. iNext. iApply wp_value. auto. } }
    iApply (wp_subseg_success with "[$HPC $Hi $Hr4 $Hr3 $Hr1]");
      [apply decode_encode_instrW_inv|done| |split;apply z_to_addr_z_of|done|done|done|..].
    { apply HPC; repeat constructor. }
    { iContiguous_next Hcont 7. }
    iEpilogue "(HPC & Hi & Hr3 & Hr1 & Hr4)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub r_t3 r_t3 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr1 $Hr3]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 8|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr1 & Hr3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    cbn [denote].
    (* lea r_t4 r_t3 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr4 $Hr3]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 9| |done|done|..].
    { apply HPC; repeat constructor. }
    { transitivity (Some a_m); auto. clear; solve_addr. }
    { simpl; auto. }
    iEpilogue "(HPC & Hi & Hr3 & Hr4)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t3 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr3 $Hr2]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 10|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr3 & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub r_t1 0 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_z_dst with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 11|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    cbn [denote].
    (* lea r_t3 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr3 $Hr1]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 12| |done|done|..].
    { apply HPC; repeat constructor. }
    { transitivity (Some 0)%a; auto. clear; solve_addr. }
    { simpl; auto. }
    iEpilogue "(HPC & Hi & Hr1 & Hr3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* getb r_t1 r_t3 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr1 $Hr3]");
      [apply decode_encode_instrW_inv|done|done| |iContiguous_next Hcont 13|done|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr3 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    cbn [rules_Get.denote].
    (* lea r_t3 r_t1 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr3 $Hr1]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 14| |done|done|..].
    { apply HPC; repeat constructor. }
    { transitivity (Some b_m)%a; auto. clear; solve_addr. }
    { simpl; auto. }
    iEpilogue "(HPC & Hi & Hr1 & Hr3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t3 r_t2 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr2 $Hr3 $Hmemptr]");
      [apply decode_encode_instrW_inv|done|done| |iContiguous_next Hcont 15|split;try done|auto|..].
    { apply HPC; repeat constructor. }
    { apply le_addr_withinBounds.
      - generalize (contiguous_between_length _ _ _ Hcont). cbn.
        clear; solve_addr.
      - revert Hbm_am Ham_e; solve_addr. }
    iEpilogue "(HPC & Hi & Hr2 & Hr3 & Hmemptr)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 r_t4 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr1 $Hr4]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 16|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr1 & Hr4)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 17|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t3 0 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr3]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 18|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t4 0 *)
    destruct l as [|? l];[inversion Hprog_len|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr4]");
      [apply decode_encode_instrW_inv|done| |iContiguous_next Hcont 19|done|..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr4)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jmp r_t0 *)
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply decode_encode_instrW_inv|done| |..].
    { apply HPC; repeat constructor. }
    iEpilogue "(HPC & Hi & Hr0)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    destruct l;[|inversion Hprog_len].
    assert ((a_m <= a_m')%a ∧ (a_m' <= e)%a).
    { unfold isWithin in Ha_m'_within. (* FIXME? *)
      rewrite andb_true_iff !Z.leb_le in Ha_m'_within |- *.
      revert Ha_m' Hsize; clear; solve_addr. }
    rewrite (region_addrs_zeroes_split _ a_m') //;[].
    (* TODO: move/rename *)
    iDestruct (region_macros.stack_split _ _ a_m' with "Hmem") as "[Hmem_fresh Hmem]"; auto.
    { rewrite replicate_length //. }
    iDestruct ("Hinv_close" with "[Hprog_done Hmemptr Hmem $Hna]") as ">Hna".
    { iNext. iExists b_m, a_m'. iFrame.
      rewrite /malloc_subroutine_instrs /malloc_subroutine_instrs'.
      unfold region_mapsto. rewrite Hai. cbn.
      repeat iDestruct "Hprog_done" as "[? Hprog_done]". iFrame.
      iPureIntro.
      unfold isWithin in Ha_m'_within. (* FIXME? *)
      rewrite andb_true_iff !Z.leb_le in Ha_m'_within |- *.
      revert Ha_m' Hsize; clear; solve_addr. }

    iApply (wp_wand with "[-]").
    { iApply "Hφ". iFrame.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr4]") as "Hrmap".
      by rewrite lookup_delete. rewrite insert_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr3]") as "Hrmap".
      by rewrite lookup_insert_ne // lookup_delete //.
      rewrite insert_commute // insert_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr2]") as "Hrmap".
      by rewrite !lookup_insert_ne // lookup_delete //.
      rewrite (insert_commute _ r_t2 r_t4) // (insert_commute _ r_t2 r_t3) //.
      rewrite insert_delete.
      rewrite (insert_commute _ r_t3 r_t2) // (insert_commute _ r_t4 r_t2) //.
      rewrite (insert_commute _ r_t4 r_t3) //. iFrame.
      iExists a_m, a_m'. iFrame. auto. }
    { auto. }
  Qed.

End SimpleMalloc.

