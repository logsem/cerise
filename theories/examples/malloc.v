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
     Jmp idc].

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

  Lemma simple_malloc_subroutine_spec_main (wsize: Word) (cont: Word) b e rmap N E φ :
    dom rmap = all_registers_s ∖ {[ PC; idc; r_t1 ]} →
    ↑N ⊆ E →
    (  na_inv logrel_nais N (malloc_inv b e)
         ∗ na_own logrel_nais E
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
         ∗ idc ↦ᵣ cont
         ∗ PC ↦ᵣ WCap RX b e b
         ∗ r_t1 ↦ᵣ wsize
         ∗ ▷ (na_own logrel_nais E
                ∗ ([∗ map] r↦w ∈
                   <[r_t2 := WInt 0%Z]>
                     (<[r_t3 := WInt 0%Z]>
                        (<[r_t4 := WInt 0%Z]> rmap)), r ↦ᵣ w)
                ∗ PC ↦ᵣ WCap RX b e (b ^+ (length malloc_subroutine_instrs - 1))%a
                ∗ idc ↦ᵣ cont
                ∗ (∃ (ba ea : Addr) size,
                    ⌜wsize = WInt size⌝
                    ∗ ⌜(ba + size)%a = Some ea⌝
                    ∗ r_t1 ↦ᵣ WCap RWX ba ea ba
                    ∗ [[ba, ea]] ↦ₐ [[region_addrs_zeroes ba ea]])
              -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}))
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom HN) "(#Hinv & Hna & Hrmap & Hr0 & HPC & Hr1 & Hφ)".
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
   (* iApply (wp_wand with "[-]"). *)
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


  Lemma simple_malloc_subroutine_spec (wsize: Word) (cont wpc widc: Word) b e rmap N E φ :
    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1 ]} →
    ↑N ⊆ E →
    (  na_inv logrel_nais N (malloc_inv b e)
         ∗ na_own logrel_nais E
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
         ∗ idc ↦ᵣ cont
         ∗ continuation_resources cont wpc widc
         ∗ PC ↦ᵣ WCap RX b e b
         ∗ r_t1 ↦ᵣ wsize
         ∗ ▷ (na_own logrel_nais E
                ∗ ([∗ map] r↦w ∈
                   <[r_t2 := WInt 0%Z]>
                     (<[r_t3 := WInt 0%Z]>
                        (<[r_t4 := WInt 0%Z]>
                           rmap)), r ↦ᵣ w)
                ∗ PC ↦ᵣ updatePcCont cont wpc
                ∗ idc ↦ᵣ updateIdcCont cont cont widc
                ∗ continuation_resources cont wpc widc
                ∗ (∃ (ba ea : Addr) size,
                    ⌜wsize = WInt size⌝
                    ∗ ⌜(ba + size)%a = Some ea⌝
                    ∗ r_t1 ↦ᵣ WCap RWX ba ea ba
                    ∗ [[ba, ea]] ↦ₐ [[region_addrs_zeroes ba ea]])
              -∗ WP Seq (Instr Executable) {{ φ }}))
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom HN) "(#Hinv & Hna & Hrmap & Hr0 & Hcont_res & HPC & Hr1 & Hφ)".
    iApply (simple_malloc_subroutine_spec_main with "[-]"); eauto; iFrame "∗ #".
    iNext ; iIntros "(Hna & Hrmap & HPC & Hidc & Hallocated)".

    iMod (na_inv_acc with "Hinv Hna") as "(>Hmalloc & Hna & Hinv_close)"; auto.
    iDestruct "Hmalloc" as (b_m a_m) "(Hprog & %Hbm & Hmemptr & Hmem & %Hbounds)".

    iInstr_lookup "Hprog" as "Hi" "Hprog_cont".
    cbn.
    iApply (@wp_jmp_general_idc _ _ _ _ RX b e (b ^+ 25)%a (encodeInstrW (Jmp idc)) cont wpc widc
             with "[-]"); try solve_pure.
    admit.
    iFrame.
    iNext; iIntros "(HPC & Hidc & Hcont_res & Hi)".
    iDestruct ("Hprog_cont" with "Hi") as "Hprog".

    (* Continuation *)
    iDestruct ("Hinv_close" with "[Hprog Hmemptr Hmem $Hna]") as ">Hna".
    { iNext. iExists b_m, a_m. iFrame. iSplitR. iPureIntro.
      by unfold malloc_subroutine_instrs_length. iPureIntro; solve_addr. }
    iApply "Hφ". iFrame.
  Admitted.

  Lemma wp_jmp_interp_idc pc_p pc_b pc_e pc_a w cont φ :
    decodeInstrW w = Jmp idc →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    (   interp cont
          ∗ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
              ∗ idc ↦ᵣ cont
              ∗ pc_a ↦ₐ w
              ∗ ▷ ( ∃ wpc widc,
                  PC ↦ᵣ updatePcCont cont wpc
                    ∗ idc ↦ᵣ updateIdcCont cont cont widc
                    ∗ pc_a ↦ₐ w
                  -∗ WP Seq (Instr Executable) {{ φ }}))
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hinstr Hvpc) "(#HcontV & HPC & Hidc & Hpc_a & Hφ)".
    destruct (decide (is_ie_cap cont = true)) as [Hcont|Hcont].
    { (* case is IE *)
      destruct_word cont ; cbn in Hcont ; try congruence.
      destruct c ; try congruence; clear Hcont; cbn.
      rewrite fixpoint_interp1_eq //=.

      destruct (decide (withinBounds f f0 f1 /\ withinBounds f f0 (f1^+1)%a))
        as [ Hwb | Hwb ].

      { (* case in bounds *)
        iDestruct ("HcontV" $! Hwb)
          as (P1 P2) "(%Hpers1 & %Hpers2 & Hinv_f1 & Hinv_f2 & Hcont)".
        destruct Hwb as [Hwb Hwb'].
        wp_instr.

        assert (Hf1: f1 <> (f1 ^+ 1)%a). admit.
        iInv (logN.@f1) as (w1) "[>Hf1 #HP1]" "Hcls1".
        iInv (logN.@(f1 ^+1)%a) as (w2) "[>Hf2 #HP2]" "Hcls2".

        iApply (wp_jmp_success_IE_same_idc with "[$HPC $Hidc $Hpc_a $Hf1 $Hf2]")
        ; try solve_pure.
        iNext; iIntros "(HPC& Hidc& Hpc_a& Hf1& Hf2) //=".
        iMod ("Hcls2" with "[Hf2 HP2]") as "_"; [iNext ; iExists _ ; iFrame "∗ #"| iModIntro].
        iMod ("Hcls1" with "[Hf1 HP1]") as "_"; [iNext ; iExists _ ; iFrame "∗ #"| iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".

        (* iApply (wp_wand with "[-]"). *)
        (* iApply "Hcont"; iFrame. *)


        admit.
        (* wp_instr. *)
        (* iApply (@wp_jmp_success_IE_same_idc with "[-Hφ]") *)
        (* ; [| | eapply Hwb | eapply Hwb' | | ]; eauto; iFrame. *)
        (* iNext; iIntros "(HPC & Hidc & Hpc_a & Hf1 & Hf2)"; wp_pure. *)
        (* iApply (wp_wand _ _ _ φ with "[-]"); last auto. *)
        (* iApply "Hφ"; iFrame. *)
      }
      { (* case not in bounds *)
        wp_instr.
        iDestruct "Hpre" as (wpc widc)
                              "(HPC & Hidc & Hpc_a & Hφ)".
        iApply (@wp_jmp_fail_IE_same_idc with "[-Hφ]"); eauto ; iFrame.
        iNext; iIntros "(HPC & Hidc & Hpc_a)"; wp_pure.
        wp_end. by iRight.
      }
    }
    { (* case is not IE *)
      assert (is_ie_cap cont = false) as Hcont'.
      { destruct_word cont ; [| destruct c | |] ; cbn in * ; congruence. }
      wp_instr.
      iApply (@wp_jmp_success with "[-Hφ]") ; eauto; iFrame.
      iNext; iIntros "(HPC & Hidc & Hpc_a)"; wp_pure.
      iApply (wp_wand _ _ _ φ with "[-]"); last auto.
      iApply "Hφ".
      destruct_word cont ; [| destruct c | |] ; cbn in Hcont ; try congruence; iFrame.
    }
  Admitted.




  Lemma simple_malloc_subroutine_spec_adv (wsize: Word) (cont: Word) b e rmap N E φ :
    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1 ]} →
    ↑N ⊆ E →
    interp cont ∗
    (  na_inv logrel_nais N (malloc_inv b e)
         ∗ na_own logrel_nais E
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
         ∗ idc ↦ᵣ cont
         ∗ PC ↦ᵣ WCap RX b e b
         ∗ r_t1 ↦ᵣ wsize
         ∗ ▷ ( ∃ wpc widc,
           na_own logrel_nais E
                ∗ ([∗ map] r↦w ∈
                   <[r_t2 := WInt 0%Z]>
                     (<[r_t3 := WInt 0%Z]>
                        (<[r_t4 := WInt 0%Z]>
                           rmap)), r ↦ᵣ w)
                ∗ PC ↦ᵣ updatePcCont cont wpc
                ∗ idc ↦ᵣ updateIdcCont cont cont widc
                ∗ (∃ (ba ea : Addr) size,
                    ⌜wsize = WInt size⌝
                    ∗ ⌜(ba + size)%a = Some ea⌝
                    ∗ r_t1 ↦ᵣ WCap RWX ba ea ba
                    ∗ [[ba, ea]] ↦ₐ [[region_addrs_zeroes ba ea]])
              -∗ WP Seq (Instr Executable) {{ φ }}))
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom HN)
      "(#HcontV & #Hinv & Hna & Hrmap & Hr0 & HPC & Hr1 & Hφ)".
    iDestruct "Hφ" as (wpc widc) "Hφ".

    iApply (simple_malloc_subroutine_spec_main with "[-]"); eauto; iFrame "∗ #".
    iNext ; iIntros "(Hna & Hrmap & HPC & Hidc & Hallocated)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hmalloc & Hna & Hinv_close)"; auto.

    iDestruct "Hmalloc" as (b_m a_m) "(Hprog & %Hbm & Hmemptr & Hmem & %Hbounds)".

    codefrag_facts "Hprog".
    iInstr_lookup "Hprog" as "Hi" "Hprog_cont".
    iApply (wp_jmp_interp_idc with "[-]"); try iFrame "∗ #" ; try solve_pure.
    cbn.
    admit.
    iExists _,_.
    iFrame.
    iNext; iIntros "(HPC & Hidc & Hi)".
    iDestruct ("Hprog_cont" with "Hi") as "Hprog".

    (* Continuation *)
    (* rewrite (region_addrs_zeroes_split _ a_m') //; [| solve_addr]. *)
    (* iDestruct (region_mapsto_split _ _ a_m' with "Hmem") as "[Hmem_fresh Hmem]". *)
    (* solve_addr. by rewrite replicate_length //. *)
    iDestruct ("Hinv_close" with "[Hprog Hmemptr Hmem $Hna]") as ">Hna".
    { iNext. iExists b_m, a_m. iFrame. iSplitR. iPureIntro.
      by unfold malloc_subroutine_instrs_length. iPureIntro; solve_addr. }
    iApply "Hφ". iFrame.
  Admitted.


  Lemma simple_malloc_subroutine_valid N b e :
    na_inv logrel_nais N (malloc_inv b e) -∗
    interp (WCap E b e b).
  Proof.
    iIntros "#Hmalloc".
    rewrite fixpoint_interp1_eq /=. iIntros (r). iNext. iModIntro.
    iIntros (cont) "#Hvalid_cont (#[% Hregs_valid] & Hregs & Hown)".
    rewrite insert_commute //=.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]";[rewrite lookup_insert;eauto|].
    iDestruct (big_sepM_delete _ _ idc with "Hregs") as "[idc Hregs]"
    ; [rewrite lookup_delete_ne // lookup_insert_ne // lookup_insert; eauto |].
    destruct H with r_t1 as [? ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[r_t1 Hregs]"
    ;[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|].

    iApply (wp_wand with "[-]").
    iApply (simple_malloc_subroutine_spec_adv with
             "[- $Hown $Hmalloc $Hregs $idc $HPC $r_t1 $Hvalid_cont]");[|solve_ndisj|].
    3: { iSimpl. iIntros (v) "[H | ->]". iExact "H". iIntros (Hcontr); done. }
    { rewrite !dom_delete_L dom_insert_L. apply regmap_full_dom in H as <-. set_solver. }

    iDestruct (jmp_to_unknown with "Hvalid_cont Hvalid_cont") as "Hcont".
    iNext.
    iDestruct "Hcont" as (wpc widc) "Hcont".

    rewrite delete_insert_delete (delete_commute _ idc) delete_insert_delete.
    iExists wpc, widc.
    iIntros "(Hna & Hregs & HPC & Hidc & Hres)".

    iDestruct "Hres" as (ba ea size) "(%Hsize & %Hea & Hr_t1 & Hbe)".
    iInsert "Hregs" r_t1.
    iMod (region_integers_alloc _ _ _ _ _ RWX with "Hbe") as "#Hbe"; auto.
    by apply Forall_replicate.
    set regs := <[_:=_]> _.

    iApply ("Hcont" $! regs).
    { iPureIntro. subst regs. rewrite !dom_insert_L dom_delete_L dom_delete_L.
      rewrite regmap_full_dom; eauto.
    }
    iFrame.
    iApply big_sepM_sep. iFrame. iApply big_sepM_intro.
    iIntros "!>" (r' w Hr'). subst regs.
    destruct (decide (r' = r_t1)). { subst r'. rewrite lookup_insert in Hr'. simplify_eq. iApply "Hbe". }
    destruct (decide (r' = r_t2)). { subst r'. repeat (rewrite lookup_insert_ne // in Hr'; []). rewrite lookup_insert in Hr'. simplify_eq. rewrite /interp !fixpoint_interp1_eq //. }
    destruct (decide (r' = r_t3)). { subst r'. repeat (rewrite lookup_insert_ne // in Hr'; []). rewrite lookup_insert in Hr'. simplify_eq. rewrite /interp !fixpoint_interp1_eq //. }
    destruct (decide (r' = r_t4)). { subst r'. repeat (rewrite lookup_insert_ne // in Hr'; []). rewrite lookup_insert in Hr'. simplify_eq. rewrite /interp !fixpoint_interp1_eq //. }
    repeat (rewrite lookup_insert_ne // in Hr'; []).
    apply lookup_delete_Some in Hr' as [? Hr'].
    apply lookup_delete_Some in Hr' as [? Hr'].
    simplify_map_eq.
    unshelve iSpecialize ("Hregs_valid" $! r' _ _ _ Hr'); done.
  Qed.

End SimpleMalloc.
