From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel addr_reg_sample fundamental rules proofmode.

(* A toy malloc implementation *)

(* The routine is initially provided a capability to a contiguous range of
   memory. It implements a bump-pointer allocator, where all memory before the
   pointer of the capability has been allocated, and all memory after is free.
   Allocating corresponds to increasing the pointer and returning the
   corresponding sub-slice.

   There is no free: when all the available memory has been allocated, the
   routine cannot allocate new memory and will fail instead.

   This is obviously not very realistic, but is good enough for our simple case
   studies. *)

Section SimpleMalloc.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Definition malloc_subroutine_instrs' (offset: Z) :=
    encodeInstrsW [
     Lt r_t3 0 r_t1;
     Mov r_t2 PC;
     Lea r_t2 4;
     Jnz r_t2 r_t3;
     Fail;
     Mov r_t2 PC;
     Lea r_t2 offset;
     Load r_t2 r_t2;
     GetA r_t3 r_t2;
     Lea r_t2 r_t1;
     GetA r_t1 r_t2;
     Mov r_t4 r_t2;
     Subseg r_t4 r_t3 r_t1;
     Sub r_t3 r_t3 r_t1;
     Lea r_t4 r_t3;
     Mov r_t3 r_t2;
     Sub r_t1 0%Z r_t1;
     Lea r_t3 r_t1;
     GetB r_t1 r_t3;
     Lea r_t3 r_t1;
     Store r_t3 r_t2;
     Mov r_t1 r_t4;
     Mov r_t2 0%Z;
     Mov r_t3 0%Z;
     Mov r_t4 0%Z;
     Jmp r_t31].

  Definition malloc_subroutine_instrs_length : Z :=
    Eval cbv in (length (malloc_subroutine_instrs' 0%Z)).

  Definition malloc_subroutine_instrs :=
    malloc_subroutine_instrs' (malloc_subroutine_instrs_length - 5).

  Definition malloc_inv (b e : Addr) : iProp Σ :=
    (∃ b_m a_m,
       codefrag b malloc_subroutine_instrs
     ∗ ⌜(b + malloc_subroutine_instrs_length)%a = Some b_m⌝
     ∗ b_m ↦ₐ (WCap RWX b_m e a_m)
     ∗ [[a_m, e]] ↦ₐ [[ region_addrs_zeroes a_m e ]]
     ∗ ⌜(b_m < a_m)%a ∧ (a_m <= e)%a⌝)%I.

  (* Specification of the subroutine, up-to the last jmp: it is managed separately,
     because of the possibility to jump to an IE-capability *)
  Lemma simple_malloc_subroutine_spec_main (wsize: Word) b e rmap N E φ :
    dom rmap = all_registers_s ∖ {[ PC; idc ; r_t1; r_t31 ]} →
    ↑N ⊆ E →
    (  na_inv logrel_nais N (malloc_inv b e)
         ∗ na_own logrel_nais E
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
         ∗ PC ↦ᵣ WCap RX b e b
         ∗ r_t1 ↦ᵣ wsize
         ∗ ▷ (na_own logrel_nais E
                ∗ ([∗ map] r↦w ∈
                   <[r_t2 := WInt 0%Z]>
                     (<[r_t3 := WInt 0%Z]>
                        (<[r_t4 := WInt 0%Z]> rmap)), r ↦ᵣ w)
                ∗ PC ↦ᵣ WCap RX b e (b ^+ (length malloc_subroutine_instrs - 1))%a
                ∗ (∃ (ba ea : Addr) size,
                    ⌜wsize = WInt size⌝
                    ∗ ⌜(ba + size)%a = Some ea⌝
                    ∗ r_t1 ↦ᵣ WCap RWX ba ea ba
                    ∗ [[ba, ea]] ↦ₐ [[region_addrs_zeroes ba ea]])
              -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}))
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom HN) "(#Hinv & Hna & Hrmap & HPC & Hr1 & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hmalloc & Hna & Hinv_close)"; auto.
    rewrite /malloc_inv.
    iDestruct "Hmalloc" as (b_m a_m) "(Hprog & %Hbm & Hmemptr & Hmem & %Hbounds)".
    destruct Hbounds as [Hbm_am Ham_e].
    (* Get some registers *)
    assert (is_Some (rmap !! r_t2)) as [r2w Hr2w].
    { rewrite -elem_of_dom Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! r_t3)) as [r3w Hr3w].
    { rewrite -elem_of_dom Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! r_t4)) as [r4w Hr4w].
    { rewrite -elem_of_dom Hrmap_dom. set_solver. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr2 Hrmap]".
      eassumption.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hrmap") as "[Hr3 Hrmap]".
      by rewrite lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t4 with "Hrmap") as "[Hr4 Hrmap]".
      by rewrite !lookup_delete_ne //.

    codefrag_facts "Hprog".
    rewrite {2}/malloc_subroutine_instrs /malloc_subroutine_instrs'.
    unfold malloc_subroutine_instrs_length in Hbm.
    assert (SubBounds b e b (b ^+ length malloc_subroutine_instrs)%a) by solve_addr.
    destruct wsize as [size | [ | ] | ].
    2,3,4: iInstr "Hprog"; wp_end; eauto.
    do 3 iInstr "Hprog".

    (* we need to destruct on the cases for the size *)
    destruct (decide (0 < size)%Z) as [Hsize | Hsize].
    2: { (* the program will not jump, and go to the fail instruction *)
      rewrite (_: Z.b2z (0%nat <? size)%Z = 0); cycle 1.
      { apply Z.ltb_nlt in Hsize. rewrite Hsize //. }
      iInstr "Hprog". iInstr "Hprog". wp_end. eauto. }

    (* otherwise we continue malloc *)
    iInstr "Hprog";auto. { apply Z.ltb_lt in Hsize. rewrite Hsize. auto. }
    iInstr "Hprog".
    iInstr "Hprog".
    rewrite (_: (b ^+ 26)%a = b_m); [| solve_addr].
    iInstr "Hprog". solve_pure_addr.
    iInstr "Hprog".
    (* Lea r_t1 r_t2 might fail. *)
    destruct (a_m + size)%a as [a_m'|] eqn:Ha_m'; cycle 1.
    { (* Failure case: no registered rule for that yet; do it the manual way *)
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "-#Hregs".
        by rewrite big_sepM_empty.
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "-#Hregs".
        by apply lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "-#Hregs".
        by rewrite lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "-#Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      wp_instr.
      iApply (wp_lea with "[$Hregs $Hi]"); [ | |done|..]; try solve_pure.
      { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec & ? & ?)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [| | Hfail].
      { exfalso. simplify_map_eq. }
      { exfalso. simplify_map_eq. }
      { cbn. iApply wp_pure_step_later; auto.
        iNext;iIntros "_".
        iApply wp_value. auto. } }

    do 3 iInstr "Hprog".
    (* Subseg r_t4 r_t3 r_t1 might fail. *)
    destruct (isWithin a_m a_m' b_m e) eqn:Ha_m'_within; cycle 1.
    { (* Failure case: manual mode. *)
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "-#Hregs".
        by rewrite big_sepM_empty.
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "-#Hregs".
        by apply lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "-#Hregs".
        by rewrite lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr3]") as "-#Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr4]") as "-#Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      wp_instr.
      iApply (wp_Subseg with "[$Hregs $Hi]"); [ | |done|..]; try solve_pure.
      { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec & ? & ?)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [ | | Hfail].
      { exfalso. unfold addr_of_argument in *. simplify_map_eq.
        repeat match goal with H:_ |- _ => apply finz_of_z_eq_inv in H end; subst.
        congruence. }
      { exfalso. simplify_map_eq. }
      { cbn. wp_pure. wp_end. auto. } }
    do 3 iInstr "Hprog". { transitivity (Some a_m); eauto. solve_addr. }
    do 3 iInstr "Hprog". { transitivity (Some 0%a); eauto. solve_addr. }
    do 2 iInstr "Hprog". { transitivity (Some b_m); eauto. solve_addr. }
    iInstr "Hprog". solve_pure_addr.
    do 4 iInstr "Hprog".

   (* Continuation *)
   rewrite (region_addrs_zeroes_split _ a_m') //; [| solve_addr].
   iDestruct (region_mapsto_split _ _ a_m' with "Hmem") as "[Hmem_fresh Hmem]".
   solve_addr. by rewrite replicate_length //.
   iDestruct ("Hinv_close" with "[Hprog Hmemptr Hmem $Hna]") as ">Hna".
   { iNext. iExists b_m, a_m'. iFrame. iSplitR. iPureIntro.
     by unfold malloc_subroutine_instrs_length. iPureIntro; solve_addr. }
   iApply "Hφ". iFrame.
   iDestruct (big_sepM_insert with "[$Hrmap $Hr4]") as "Hrmap".
   by rewrite lookup_delete. rewrite insert_delete_insert.
   iDestruct (big_sepM_insert with "[$Hrmap $Hr3]") as "Hrmap".
   by rewrite lookup_insert_ne // lookup_delete //.
   rewrite insert_commute // insert_delete_insert.
   iDestruct (big_sepM_insert with "[$Hrmap $Hr2]") as "Hrmap".
   by rewrite !lookup_insert_ne // lookup_delete //.
   rewrite (insert_commute _ r_t2 r_t4) // (insert_commute _ r_t2 r_t3) //.
   rewrite insert_delete_insert.
   rewrite (insert_commute _ r_t3 r_t2) // (insert_commute _ r_t4 r_t2) //.
   rewrite (insert_commute _ r_t4 r_t3) //. iFrame.
   iExists a_m, a_m', size. iFrame. auto.
  Qed.


  (* General specification of the routine. Up-to after performing the jmp.
     To use when dealing with a known continuation. *)
  Lemma simple_malloc_subroutine_spec (wsize: Word) (w' cont wpc widc: Word) b e rmap N E φ :
    dom rmap = all_registers_s ∖ {[ PC; idc ; r_t1; r_t31 ]} →
    ↑N ⊆ E →
    (  na_inv logrel_nais N (malloc_inv b e)
         ∗ na_own logrel_nais E
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
         ∗ PC ↦ᵣ WCap RX b e b
         ∗ idc ↦ᵣ w'
         ∗ r_t1 ↦ᵣ wsize
         ∗ r_t31 ↦ᵣ cont
         ∗ continuation_resources cont wpc widc
         ∗ ▷ (na_own logrel_nais E
                ∗ ([∗ map] r↦w ∈
                     <[r_t2 := WInt 0%Z]>
                        (<[r_t3 := WInt 0%Z]>
                           (<[r_t4 := WInt 0%Z]>
                              rmap)), r ↦ᵣ w)
                ∗ PC ↦ᵣ updatePcCont cont wpc
                ∗ idc ↦ᵣ updateIdcCont cont w' widc
                ∗ r_t31 ↦ᵣ cont
                ∗ continuation_resources cont wpc widc
                ∗ (∃ (ba ea : Addr) size,
                    ⌜wsize = WInt size⌝
                    ∗ ⌜(ba + size)%a = Some ea⌝
                    ∗ r_t1 ↦ᵣ WCap RWX ba ea ba
                    ∗ [[ba, ea]] ↦ₐ [[region_addrs_zeroes ba ea]])
              -∗ WP Seq (Instr Executable) {{ φ }}))
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom HN)
      "(#Hinv & Hna & Hrmap & HPC & Hidc & Hr1 & Hr31 & Hcont_res & Hφ)".
    iApply (simple_malloc_subroutine_spec_main with "[-]"); eauto ; iFrame "∗ #".
    iNext ; iIntros "(Hna & Hrmap & HPC & Hallocated)".

    iMod (na_inv_acc with "Hinv Hna") as "(>Hmalloc & Hna & Hinv_close)"; auto.
    iDestruct "Hmalloc" as (b_m a_m) "(Hprog & %Hbm & Hmemptr & Hmem & %Hbounds)".

    codefrag_facts "Hprog".
    rewrite {2}/malloc_subroutine_instrs /malloc_subroutine_instrs'.
    unfold malloc_subroutine_instrs_length in Hbm.
    assert (SubBounds b e b (b ^+ length malloc_subroutine_instrs)%a) by solve_addr.

    iInstr_lookup "Hprog" as "Hi" "Hprog_cont".
    iApply (@wp_jmp_general with "[- $HPC $Hi]"); try solve_pure; iFrame.
    iNext; iIntros "(HPC & Hidc & Hr31 & Hcont_res & Hi)".
    iDestruct ("Hprog_cont" with "Hi") as "Hprog".

    (* Continuation *)
    iDestruct ("Hinv_close" with "[Hprog Hmemptr Hmem $Hna]") as ">Hna".
    { iNext. iExists b_m, a_m. iFrame. iSplitR. iPureIntro.
      by unfold malloc_subroutine_instrs_length. iPureIntro; solve_addr. }
    iApply "Hφ". iFrame.
  Qed.

  (* Malloc subroutine is safe to share *)
  Lemma simple_malloc_subroutine_valid N b e :
    na_inv logrel_nais N (malloc_inv b e) -∗
    interp (WCap E b e b).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /=. iIntros (r). iNext. iModIntro.
    iIntros (w') "#Hvalid_w' (#[%Hsome Hregs_valid] & Hregs & Hown)".
    (* extract the registers PC, idc and r1 *)
    rewrite insert_commute //=.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]";[rewrite lookup_insert;eauto|].
    iDestruct (big_sepM_delete _ _ idc with "Hregs") as "[Hidc Hregs]"
    ; [rewrite lookup_delete_ne // lookup_insert_ne // lookup_insert; eauto |].
    destruct Hsome with r_t1 as [? ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[r_t1 Hregs]"
    ;[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|].
    destruct Hsome with r_t31 as [cont ?].
    iDestruct (big_sepM_delete _ _ r_t31 with "Hregs") as "[r_t31 Hregs]"
    ;[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|].
    iAssert (interp cont) as "Hvalid_cont".
    iApply "Hregs_valid"; by eauto.

    (* We need a special treatement for the jump, if we have an IE-cap, so we stop before
     the jmp *)
    iApply (wp_wand with "[-]").
    iApply (simple_malloc_subroutine_spec_main with
             "[- $Hown $Hinv $Hregs $HPC $r_t1]");[|solve_ndisj|].
    3: { iSimpl. iIntros (v) "[H | ->]". iExact "H". iIntros (Hcontr); done. }
    { rewrite !dom_delete_L dom_insert_L. apply regmap_full_dom in Hsome as <-. set_solver. }

    iNext ; iIntros "(Hna & Hrmap & HPC & Hallocated)".
    rewrite delete_insert_delete (delete_commute _ idc) delete_insert_delete.

    iMod (na_inv_acc with "Hinv Hna") as "(>Hmalloc & Hna & Hinv_close)"; auto.
    iDestruct "Hmalloc" as (b_m a_m) "(Hprog & %Hbm & Hmemptr & Hmem & %Hbounds)".
    codefrag_facts "Hprog".
    rewrite {2}/malloc_subroutine_instrs /malloc_subroutine_instrs'.
    unfold malloc_subroutine_instrs_length in Hbm.
    assert (SubBounds b e b (b ^+ length malloc_subroutine_instrs)%a) by solve_addr.

    (* TODO can't use =jmp_unknown_safe= here, because a na_invariant is open.
       We cannot close the invariant, because it contains the instruction.
       Maybe we can find a way to use =jmp_unknown_safe= (or a variant) with an
       invariant open ? It would allow us to factor out this part of the proof.
     *)

    destruct (decide (is_ie_cap cont = true)) as [Hcont | Hcont].
    - (* IE-cap *)
      destruct_word cont ; [ | destruct c | | ] ; cbn in Hcont ; try congruence ; clear Hcont.
      codefrag_facts "Hprog".

      rewrite (fixpoint_interp1_eq (WCap IE _ _ _)) //=.
      destruct (decide (withinBounds f f0 f1 ∧ withinBounds f f0 (f1 ^+ 1)%a)) as [Hwb | Hwb].
      { (* in bounds *)
        iDestruct ("Hvalid_cont" $! Hwb)
          as (P1 P2) "(%Hpers1 & %Hpers2 & Hinv_f1 & Hinv_f2 & Hcont)".
        destruct Hwb as [Hwb Hwb'].

        assert (Hf1: f1 <> (f1 ^+ 1)%a)
          by (apply Is_true_true_1, withinBounds_true_iff in Hwb; solve_addr).
        wp_instr.
        iInv (logN.@f1) as (w1) "[>Hf1 #HP1]" "Hcls1".
        iInv (logN.@(f1 ^+1)%a) as (w2) "[>Hf2 #HP2]" "Hcls2".
        iInstr "Hprog".
        iMod ("Hcls2" with "[Hf2 HP2]") as "_"; [iNext ; iExists _ ; iFrame "∗ #"| iModIntro].
        iMod ("Hcls1" with "[Hf1 HP1]") as "_"; [iNext ; iExists _ ; iFrame "∗ #"| iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".

        iDestruct ("Hinv_close" with "[Hprog Hmemptr Hmem $Hna]") as ">Hna".
        { iNext ; iFrame.
          iExists _,_. iFrame "∗ # %".
        }

        iDestruct "Hallocated" as (be ea sz) "(%Hsz & %Hea & Hr1 & Hmem)".
        iSpecialize ("Hcont" $! w1 w2).
        iApply (wp_wand with "[-]").
        iInsertList "Hrmap" [PC; idc;r_t1].
        iMod (region_integers_alloc _ _ _ _ _ RWX with "Hmem") as "#Hmem"; auto.
        by apply Forall_replicate.

        iInsert "Hrmap" r_t31.
        set (regs := <[_:= _]> _).
        iApply ("Hcont" $! regs); iFrame "∗ #".
        iSplit.
        { iSplit. rewrite /full_map.
          iIntros (r'). iPureIntro.
          subst regs.
          repeat (rewrite lookup_insert_is_Some'; right).
          apply Hsome.

          iIntros (r' w'') "%HrPC %HrIDC %Hsome'".
          subst regs.
          destruct (decide (r' = r_t1)); subst. { simplify_map_eq; iApply "Hmem". }
          destruct (decide (r' = r_t2)); subst. { simplify_map_eq ; rewrite !fixpoint_interp1_eq //. }
          destruct (decide (r' = r_t3)); subst. { simplify_map_eq ; rewrite !fixpoint_interp1_eq //. }
          destruct (decide (r' = r_t4)); subst. { simplify_map_eq ; rewrite !fixpoint_interp1_eq //. }
          destruct (decide (r' = r_t31)); subst. { simplify_map_eq ; rewrite !fixpoint_interp1_eq //. }
          iApply "Hregs_valid"; eauto.
          iPureIntro.
          by simplify_map_eq.
        }
        subst regs.
        rewrite
          (insert_commute _ PC r_t31) //=
          (insert_commute _ PC r_t1) //=
          (insert_commute _ PC idc) //=
          insert_insert
          (insert_commute _ idc r_t31) //=
          (insert_commute _ idc r_t1) //=
          insert_insert.
        iFrame.
        auto.
      }
      { (* not in bounds -- the jump fails *)
        iInstr "Hprog" with wp_jmp_fail_IE.
        wp_end; by iRight.
      }
    - (* not IE-cap *)
      apply not_true_is_false in Hcont.
      iDestruct (jmp_to_unknown with "Hvalid_cont") as "Hcont".

      iInstr "Hprog".

      iDestruct ("Hinv_close" with "[Hprog Hmemptr Hmem $Hna]") as ">Hna".
      { iNext. iExists b_m, a_m. iFrame. iSplitR. iPureIntro.
        by unfold malloc_subroutine_instrs_length. iPureIntro; solve_addr. }

      iApply (wp_wand with "[-]").
      iDestruct "Hallocated" as (be ea sz) "(%Hsz & %Hea & Hr1 & Hmem)".

      iMod (region_integers_alloc _ _ _ _ _ RWX with "Hmem") as "#Hmem"; auto.
      by apply Forall_replicate.

      iInsertList "Hrmap" [r_t1;idc;r_t31].
      set (regs := <[_:= _]> _).
      iApply ("Hcont" $! regs); iFrame "∗ #".
      { rewrite /full_map.
        subst regs.
        iPureIntro.
        apply regmap_full_dom in Hsome.
        rewrite <- Hsome.
        set_solver.
      }
      iApply big_sepM_sep. iFrame. iApply big_sepM_intro.
      iModIntro.
      iIntros (r' w'') "%Hsome'".
      subst regs.
      destruct (decide (r' = PC)). { simplify_map_eq. }
      destruct (decide (r' = idc)). { simplify_map_eq; iApply "Hvalid_w'". }
      destruct (decide (r' = r_t1)). { simplify_map_eq; iApply "Hmem". }
      destruct (decide (r' = r_t2)). { simplify_map_eq ; rewrite !fixpoint_interp1_eq //. }
      destruct (decide (r' = r_t3)). { simplify_map_eq ; rewrite !fixpoint_interp1_eq //. }
      destruct (decide (r' = r_t4)). { simplify_map_eq ; rewrite !fixpoint_interp1_eq //. }
      destruct (decide (r' = r_t31)). { simplify_map_eq; iApply "Hvalid_cont". }
      iApply "Hregs_valid"; eauto.
      iPureIntro; by simplify_map_eq.
      auto.
  Qed.

End SimpleMalloc.
