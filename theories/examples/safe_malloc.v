From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
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
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (* r0 contains the capability pointing to the lock address *)
  Definition spinlock_instrs' r0 r1 r2 r3 :=
    encodeInstrsW [
     Mov r1 1  ; (* value to acquire the lock *)
     Mov r2 PC ; (* Adresse loop to wait --> label loop*)
     Lea r2 2  ;
     (* loop: *)
     Mov r3 0  ; (* value to check lock state *)
     CAS r0 r3 r1;
     Jnz r2 r3
     (* if (r1 -> 0), then the lock was free, we can continue *)
     (* if (r1 -> 1), then the lock was locked, we can wait and loop *)
      ].

  (* Ltac  *)

  Ltac iInstr_inv Hinv :=
    wp_instr
    ; iInv Hinv as ">Hprog" "Hcls"
    ; codefrag_facts "Hprog"
    ; iInstr "Hprog"
    ; iMod ("Hcls" with "Hprog") as "_"
    ; iModIntro ; wp_pure.

  (* TODO : now, encapsulate the codefrag in an invariant *)
  Lemma spinlock_spec (i : CoreN)
    p_pc b_pc e_pc a_spinlock
    r0 r1 r2 r3
    w1 w2 w3
    p_lock b_lock e_lock a_lock
    ls
    N E φ :

    let e_spinlock := (a_spinlock ^+ length (spinlock_instrs' r0 r1 r2 r3))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_spinlock e_spinlock ->

    writeAllowed p_lock = true ->
    withinBounds b_lock e_lock a_lock = true ->

    ↑N ⊆ E ->
    ⊢ ( inv N (codefrag a_spinlock (spinlock_instrs' r0 r1 r2 r3))
        ∗ (i, PC) ↦ᵣ WCap p_pc b_pc e_pc a_spinlock
        ∗ (i, r0) ↦ᵣ (WCap p_lock b_lock e_lock a_lock)
        ∗ (i,r1) ↦ᵣ w1
        ∗ (i,r2) ↦ᵣ w2
        ∗ (i,r3) ↦ᵣ w3
        ∗ a_lock ↦ₐ ls
        ∗ ▷ ( (i,PC) ↦ᵣ WCap p_pc b_pc e_pc e_spinlock
              ∗ (i,r0) ↦ᵣ (WCap p_lock b_lock e_lock a_lock)
              ∗ (i,r1) ↦ᵣ WInt 1
              ∗ (∃ w2, (i,r2) ↦ᵣ w2)
              ∗ (i, r3) ↦ᵣ WInt 0
              ∗ a_lock ↦ₐ WInt 1
              -∗
                WP (i, Seq (Instr Executable)) @ E {{ φ }}
            )
        -∗ WP (i, Seq (Instr Executable)) @ E {{ φ }})%I.
  Proof.
    intro e_spinlock.
    iIntros (HPC_exec HPC_bounds Hwrite_lock Hwrite_bounds HN)
      "(#Hinv_prog & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hb_lock & Hφ)".

    do 3 (iInstr_inv "Hinv_prog").
    iLöb as "IH" forall (w3 ls).
    iInstr_inv "Hinv_prog".
    destruct (decide ( ls = WInt 0 )).
    - subst.
      do 2 (iInstr_inv "Hinv_prog").
      iApply "Hφ". iFrame.
      iExists _ ; iFrame.
    - do 2 (iInstr_inv "Hinv_prog").
      iAssert ( (i, PC) ↦ᵣ WCap p_pc b_pc e_pc (a_spinlock ^+ 3)%a )%I with "[HPC]"
        as "HPC".
      { inversion HPC_exec ; auto ; subst ; iFrame. }
      iApply ("IH" with "[$Hr0] [$Hr3] [$Hb_lock]
                         [$Hφ] [$Hr1] [$HPC] [$Hr2]").
Qed.



  Definition malloc_pre_spin (offset : Z) :=
    encodeInstrsW [
        (* bm: *)
     Lt r_t3 0 r_t1; (* ;; check that size > 0 *)
     Mov r_t2 PC;    (* ;; jmp after fail if   *)
     Lea r_t2 4;     (* ;; yes ; continue and  *)
     Jnz r_t2 r_t3;  (* ;; fail if not         *)
     Fail;
        (* xm: *)
     Mov r_t2 PC;
        (* Spinlock: wait until the malloc is available *)
        (* rt5, rt6, rt7, rt8 are used for the spinlock *)
     Mov r_t5 PC;
     Lea r_t5 (offset + 1)%Z].

  Definition malloc_post_spin (offset : Z) :=
    encodeInstrsW [
     Lea r_t2 offset;
     (* ;; r2 = (RWX, bm, em, bmid) *)
     Load r_t2 r_t2;  (* ;; r2 = (RWX, bmid, em, a)  *)
     GetA r_t3 r_t2;
     Lea r_t2 r_t1;
     (* ;; r2 = (RWX, bmid, em, a+size)  *)
     GetA r_t1 r_t2;
     Mov r_t4 r_t2;
     Subseg r_t4 r_t3 r_t1;
     Sub r_t3 r_t3 r_t1;
     Lea r_t4 r_t3;
     Mov r_t3 r_t2;
     Sub r_t1 0%Z r_t1;
     Lea r_t3 r_t1;
     GetB r_t1 r_t3;
     Lea r_t3 r_t1;   (* ;; r3 = (RWX, bmid, em, bmid)       *)
     Store r_t3 r_t2; (* ;; bmid <- (RWX, bmid, em, a+size)  *)
     Mov r_t1 r_t4;   (* ;; r3 = (RWX, a, a+size, a)         *)
     Store r_t8 0;    (* Release the lock - we don't need CAS *)
     Mov r_t2 0%Z;    (* Clear the registers *)
     Mov r_t3 0%Z;
     Mov r_t4 0%Z;
     Mov r_t5 0%Z;
     Mov r_t6 0%Z;
     Mov r_t7 0%Z;
     Mov r_t8 0%Z;
     Jmp r_t0
         (* bmid:     (RWX, bmid, em, a)          *)
         (* bmid+1:   lock_state                  *)
         (* ;; ... already allocated memory ... *)
         (* a:                                  *)
         (* ;;      ... free memory ...         *)
         (* em:                                  *)
      ].


  Definition malloc_subroutine_instrs' (offset: Z) :=
     malloc_pre_spin offset
       ++ spinlock_instrs' r_t5 r_t6 r_t7 r_t8
       ++ malloc_post_spin offset.

  Definition malloc_pre_spin_length : Z :=
    Eval cbv in (length (malloc_pre_spin 0%Z)).

  Definition malloc_pre_post_length : Z :=
    Eval cbv in (length (malloc_pre_spin 0%Z)).

  Definition spinlock_length : Z :=
    Eval cbv in (length (spinlock_instrs' PC PC PC PC)).

  Definition malloc_subroutine_instrs_length : Z :=
    Eval cbv in (length (malloc_subroutine_instrs' 0%Z)).

  Definition malloc_subroutine_instrs :=
    malloc_subroutine_instrs' (malloc_subroutine_instrs_length - 5).

  Definition malloc_inv (b e : Addr) : iProp Σ :=
    (codefrag b malloc_subroutine_instrs
     ∗ ∃ b_m a_m,
        ⌜(b + malloc_subroutine_instrs_length)%a = Some b_m⌝
     ∗ b_m ↦ₐ (WCap RWX b_m e a_m)
     ∗ ((b_m ^+1)%a ↦ₐ (WInt 0) ∨ (b_m ^+1)%a ↦ₐ (WInt 1))
     ∗ [[a_m, e]] ↦ₐ [[ region_addrs_zeroes a_m e ]]
     ∗ ⌜(b_m < a_m)%a ∧ (a_m <= e)%a⌝)%I.

  Lemma simple_malloc_subroutine_spec
    (i : CoreN)
    (wsize: Word)
    (cont: Word)
    (b e : Addr)
    (rmap : (gmap (CoreN * RegName) Word))
    N E
    (φ : language.val cap_lang → iProp Σ) :

    dom (gset (CoreN*RegName)) rmap =
      (set_map (fun r => (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0) ; (i, r_t1) ]} →

    (exists b_m, (b + malloc_subroutine_instrs_length)%a = Some b_m /\ (b_m < e)%a) ->
    ↑N ⊆ E →
    (  inv N (malloc_inv b e)
     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
     ∗ (i, r_t0) ↦ᵣ cont
     ∗ (i, PC) ↦ᵣ WCap RX b e b
     ∗ (i, r_t1) ↦ᵣ wsize
       ∗ ▷ (([∗ map] r↦w ∈ <[(i, r_t2) := WInt 0%Z]>
               (<[(i, r_t3) := WInt 0%Z]>
                  (<[(i, r_t4) := WInt 0%Z]> rmap)), r ↦ᵣ w)
            ∗ (i, r_t0) ↦ᵣ cont
            ∗ (i, PC) ↦ᵣ updatePcPerm cont
            ∗ (∃ (ba ea : Addr) size,
                  ⌜wsize = WInt size⌝
                  ∗ ⌜(ba + size)%a = Some ea⌝
                  ∗ (i, r_t1) ↦ᵣ WCap RWX ba ea ba
                  ∗ [[ba, ea]] ↦ₐ [[region_addrs_zeroes ba ea]])
            -∗ WP (i, Seq (Instr Executable)) @ E {{ φ }}%I))
    ⊢ WP (i, Seq (Instr Executable)) @ E {{ λ v, φ v ∨ ⌜v = (i, FailedV)⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom Hbm HN) "(#Hinv & Hrmap & Hr0 & HPC & Hr1 & Hφ)".
    destruct Hbm as ( bm & Hbm & Hbme ).
    unfold malloc_subroutine_instrs_length in Hbm.
    assert (Hbounds: SubBounds b e b (b ^+ length malloc_subroutine_instrs)%a) by solve_addr.
    rewrite /malloc_inv.

    (* Get some registers *)
    assert (is_Some (rmap !! (i, r_t2))) as [r2w Hr2w].
    { rewrite elem_of_gmap_dom Hrmap_dom.
      apply elem_of_difference. set_solver+. }
    assert (is_Some (rmap !! (i, r_t3))) as [r3w Hr3w].
    { rewrite elem_of_gmap_dom Hrmap_dom.
      apply elem_of_difference. set_solver+. }
    assert (is_Some (rmap !! (i, r_t4))) as [r4w Hr4w].
    { rewrite elem_of_gmap_dom Hrmap_dom.
      apply elem_of_difference. set_solver+. }
    assert (is_Some (rmap !! (i, r_t5))) as [r5w Hr5w].
    { rewrite elem_of_gmap_dom Hrmap_dom.
      apply elem_of_difference. set_solver+. }
    assert (is_Some (rmap !! (i, r_t6))) as [r6w Hr6w].
    { rewrite elem_of_gmap_dom Hrmap_dom.
      apply elem_of_difference. set_solver+. }
    assert (is_Some (rmap !! (i, r_t7))) as [r7w Hr7w].
    { rewrite elem_of_gmap_dom Hrmap_dom.
      apply elem_of_difference. set_solver+. }
    assert (is_Some (rmap !! (i, r_t8))) as [r8w Hr8w].
    { rewrite elem_of_gmap_dom Hrmap_dom.
      apply elem_of_difference. set_solver+. }


    iDestruct (big_sepM_delete _ _ (i, r_t2) with "Hrmap") as "[Hr2 Hrmap]".
      eassumption.
    iDestruct (big_sepM_delete _ _ (i, r_t3) with "Hrmap") as "[Hr3 Hrmap]".
      by rewrite lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ (i, r_t4) with "Hrmap") as "[Hr4 Hrmap]".
      by rewrite !lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ (i, r_t5) with "Hrmap") as "[Hr5 Hrmap]".
      by rewrite !lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ (i, r_t6) with "Hrmap") as "[Hr6 Hrmap]".
      by rewrite !lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ (i, r_t7) with "Hrmap") as "[Hr7 Hrmap]".
    by rewrite !lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ (i, r_t8) with "Hrmap") as "[Hr8 Hrmap]".
    by rewrite !lookup_delete_ne //.

  (* TODO move somewhere else *)
  Tactic Notation "solve_length_seq" "by" tactic3(solve_a) :=
    cbn ; try (rewrite finz_seq_between_length)
    ; repeat (rewrite finz_dist_S ; last solve_a)
    ; by rewrite finz_dist_0 ; last solve_a.


    (* Split the invariant into more fine-grained invariant *)
    iDestruct (inv_split_l with "Hinv") as "Hinv_code".
    rewrite {2}/codefrag.
    rewrite {2}/malloc_subroutine_instrs /malloc_subroutine_instrs'.
    rewrite (region_mapsto_split _ _ (b ^+ malloc_pre_spin_length)%a).
    2:{ cbn; rewrite /malloc_pre_spin_length; solve_addr. }
    2:{ cbn; rewrite /malloc_pre_spin_length. admit. }
    rewrite (region_mapsto_split (b ^+ malloc_pre_spin_length)%a _
               ((b ^+ malloc_pre_spin_length ^+ spinlock_length)%a)).
    2:{ rewrite /malloc_pre_spin_length /spinlock_length; solve_addr. }
    2:{ cbn. admit. }
    iDestruct (inv_split with "Hinv_code") as "[Hinv_code_pre H']".
    iDestruct (inv_split with "H'") as "[Hinv_code_spin Hinv_code_post]".
    iClear "Hinv_code"; iClear "H'".
    rewrite /length /=.

    iAssert ( inv N (codefrag b (malloc_pre_spin (malloc_subroutine_instrs_length - 5))))
              as "Hinv_pre"  ; first iFrame "#".
    iClear "Hinv_code_pre".

    iAssert ( inv N (codefrag (b ^+ malloc_pre_spin_length)%a
                       (spinlock_instrs' r_t5 r_t6 r_t7 r_t8)))
              as "Hinv_spin"  ; first iFrame "#".
    iClear "Hinv_code_spin".

    iAssert ( inv N (codefrag ((b ^+ malloc_pre_spin_length) ^+ spinlock_length)%a
                       (malloc_post_spin (malloc_subroutine_instrs_length - 5))))
              as "Hinv_post"
    ; first ( iFrame "#"
         ; rewrite /codefrag
         ; simpl ; rewrite /malloc_pre_spin_length /malloc_pre_post_length /spinlock_length
         ; replace ((((b ^+ 8) ^+ 6) ^+ 25%nat)%a) with (b ^+ 39%nat)%a by solve_addr
         ; iFrame "#").
    iClear "Hinv_code_post".

    (* Lt *)
    wp_instr.
    iInv "Hinv_pre" as ">Hprog" "Hcls".
    codefrag_facts "Hprog".

    destruct (wsize) as [size|].
    2: {
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      iApply ( wp_add_sub_lt_fail_z_r with "[ $HPC $Hr3 $Hr1 $Hi ]") ; eauto.
      { cbn; rewrite decode_encode_instr_inv; auto. }
      { apply isCorrectPC_intro ; [solve_addr| auto]. }
      iModIntro. iIntros "Hb".
      iDestruct ("Hcont" with "Hb") as "Hprog".
      cbn.
      iMod ("Hcls" with "Hprog") as "_".
      iModIntro. wp_pure; wp_end; cbn. eauto. }

    iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_add_sub_lt_success_z_r with "[ $HPC $Hr1 $Hr3 $Hi ]") ; eauto.
    { cbn; rewrite decode_encode_instr_inv; eauto. }
    { transitivity (Some (b ^+ 1)%a); solve_addr; done. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    iNext. iIntros "(HPC & Hi & Hr1 & Hr3)".
    rewrite decode_encode_instrW_inv.
    rewrite /denote.
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_pre" as ">Hprog" "Hcls"
    ; codefrag_facts "Hprog".
    (* Apply the invariant *)
    iInstr_lookup "Hprog" as "Hi" "Hcont"
    ; iApply ( wp_move_success_reg_fromPC with "[ $HPC Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some (b ^+ 2)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Lea *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_pre" as ">Hprog" "Hcls"
    ; codefrag_facts "Hprog".
    (* Apply the invariant *)
    iInstr_lookup "Hprog" as "Hi" "Hcont"
    ; iApply ( wp_lea_success_z with "[ $HPC $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some (b ^+ 3)%a); solve_addr; done. }
    { transitivity (Some (b ^+ 5)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* we need to destruct on the cases for the size *)
    destruct (decide (0 < size)%Z) as [Hsize | Hsize].
    2: { (* the program will not jump, and go to the fail instruction *)
      rewrite (_: Z.b2z (0%nat <? size)%Z = 0); cycle 1.
      { apply Z.ltb_nlt in Hsize. rewrite Hsize //. }
      wp_instr
      ; iInv "Hinv_pre" as ">Hprog" "Hcls"
      ; codefrag_facts "Hprog".
      (* Apply the invariant *)
      iInstr_lookup "Hprog" as "Hi" "Hcont"
      ; iApply ( wp_jnz_success_next with "[ $HPC $Hr2 Hr3 $Hi ]") ; eauto.
      { cbn ;rewrite decode_encode_instr_inv; eauto. }
      { apply isCorrectPC_intro ; [solve_addr| auto]. }
      { transitivity (Some (b ^+ 4)%a); solve_addr; done. }
      iNext; iIntros "(HPC & Hi & Hr2 & Hr3)".
      (* Close the invariant *)
      iDestruct ("Hcont" with "Hi") as "Hprog".
      iMod ("Hcls" with "Hprog") as "_".
      simpl ; iModIntro ; wp_pure.

      wp_instr
      ; iInv "Hinv_pre" as ">Hprog" "Hcls"
      ; codefrag_facts "Hprog".
      iInstr_lookup "Hprog" as "Hi" "Hcont"
      ; iApply ( wp_fail with "[ $HPC $Hi ]") ; eauto.
      { cbn ;rewrite decode_encode_instr_inv; eauto. }
      { apply isCorrectPC_intro ; [solve_addr| auto]. }
      iNext; iIntros "(HPC & Hi)".
      (* Close the invariant *)
      iDestruct ("Hcont" with "Hi") as "Hprog".
      iMod ("Hcls" with "Hprog") as "_".
      simpl ; iModIntro ; wp_pure.
      wp_end ; eauto.
      }


    rewrite (_: Z.b2z (0%nat <? size)%Z = 1); cycle 1.
    { rewrite (_: (0%nat <? size)%Z = true ); auto. by apply Z.ltb_lt. }

    (* Lea *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_pre" as ">Hprog" "Hcls"
    ; codefrag_facts "Hprog".
    (* Apply the invariant *)
    iInstr_lookup "Hprog" as "Hi" "Hcont"
    ; iApply ( wp_jnz_success_jmp with "[ $HPC $Hr2 $Hr3 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    iNext; iIntros "(HPC & Hi & Hr2 & Hr3)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_pre" as ">Hprog" "Hcls"
    ; codefrag_facts "Hprog".
    (* Apply the invariant *)
    iInstr_lookup "Hprog" as "Hi" "Hcont"
    ; iApply ( wp_move_success_reg_fromPC with "[ $HPC $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some (b ^+ 6)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_pre" as ">Hprog" "Hcls"
    ; codefrag_facts "Hprog".
    (* Apply the invariant *)
    iInstr_lookup "Hprog" as "Hi" "Hcont"
    ; iApply ( wp_move_success_reg_fromPC with "[ $HPC $Hr5 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some (b ^+ 7)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr5)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Lea *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_pre" as ">Hprog" "Hcls"
    ; codefrag_facts "Hprog".
    (* Apply the invariant *)
    iInstr_lookup "Hprog" as "Hi" "Hcont"
    ; iApply ( wp_lea_success_z with "[ $HPC $Hr5 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some (b ^+ 8)%a); solve_addr; done. }
    { rewrite /malloc_subroutine_instrs_length.
      transitivity (Some (b ^+ 41)%a).
      rewrite (_ : (39 - 5 + 1) = 35 )%Z ; last lia.
      admit. done. }
    iNext; iIntros "(HPC & Hi & Hr5)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* TODO: I need to extract the address of the lock, in order to give it to
             the spec, but it depends on the existantial b_m..... Find a solution *)
    (** ====== Spinlock ====== *)
    iApply (spinlock_spec i _ _ _ _ r_t5 r_t6 r_t7 r_t8 with "[$HPC $Hr5 $Hr6 $Hr7 $Hr8]").
    { apply ExecPCPerm_RX. }
    { solve_addr. }
    { admit. }
    { admit. }
    { eauto. }
    iFrame "#".
Abort.



  (*   (* otherwise we continue malloc *) *)
  (*   iInstr "Hprog". { apply Z.ltb_lt in Hsize. rewrite Hsize. auto. } *)
  (*   iInstr "Hprog". *)
  (*   iInstr "Hprog". *)
  (*   rewrite (_: (b ^+ 26)%a = b_m); [| solve_addr]. *)
  (*   iInstr "Hprog". solve_pure_addr. *)
  (*   iInstr "Hprog". *)
  (*   (* Lea r_t1 r_t2 might fail. *) *)
  (*   destruct (a_m + size)%a as [a_m'|] eqn:Ha_m'; cycle 1. *)
  (*   { (* Failure case: no registered rule for that yet; do it the manual way *) *)
  (*     iInstr_lookup "Hprog" as "Hi" "Hcont". *)
  (*     iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "-#Hregs". *)
  (*       by rewrite big_sepM_empty. *)
  (*     iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "-#Hregs". *)
  (*       by apply lookup_empty. *)
  (*     iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "-#Hregs". *)
  (*       by rewrite lookup_insert_ne // lookup_empty. *)
  (*     iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "-#Hregs". *)
  (*       by rewrite !lookup_insert_ne // lookup_empty. *)
  (*     wp_instr. *)
  (*     iApply (wp_lea with "[$Hregs $Hi]"); [ | |done|..]; try solve_pure. *)
  (*     { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. } *)
  (*     iNext. iIntros (regs' retv) "(Hspec & ? & ?)". iDestruct "Hspec" as %Hspec. *)
  (*     destruct Hspec as [| Hfail]. *)
  (*     { exfalso. simplify_map_eq. } *)
  (*     { cbn. iApply wp_pure_step_later; auto. iNext. *)
  (*       iApply wp_value. auto. } } *)

  (*   do 3 iInstr "Hprog". *)
  (*   (* Subseg r_t4 r_t3 r_t1 might fail. *) *)
  (*   destruct (isWithin a_m a_m' b_m e) eqn:Ha_m'_within; cycle 1. *)
  (*   { (* Failure case: manual mode. *) *)
  (*     iInstr_lookup "Hprog" as "Hi" "Hcont". *)
  (*     iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "-#Hregs". *)
  (*       by rewrite big_sepM_empty. *)
  (*     iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "-#Hregs". *)
  (*       by apply lookup_empty. *)
  (*     iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "-#Hregs". *)
  (*       by rewrite lookup_insert_ne // lookup_empty. *)
  (*     iDestruct (big_sepM_insert with "[$Hregs $Hr3]") as "-#Hregs". *)
  (*       by rewrite !lookup_insert_ne // lookup_empty. *)
  (*     iDestruct (big_sepM_insert with "[$Hregs $Hr4]") as "-#Hregs". *)
  (*       by rewrite !lookup_insert_ne // lookup_empty. *)
  (*     wp_instr. *)
  (*     iApply (wp_Subseg with "[$Hregs $Hi]"); [ | |done|..]; try solve_pure. *)
  (*     { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. } *)
  (*     iNext. iIntros (regs' retv) "(Hspec & ? & ?)". iDestruct "Hspec" as %Hspec. *)
  (*     destruct Hspec as [| Hfail]. *)
  (*     { exfalso. unfold addr_of_argument in *. simplify_map_eq. *)
  (*       repeat match goal with H:_ |- _ => apply finz_of_z_eq_inv in H end; subst. *)
  (*       congruence. } *)
  (*     { cbn. wp_pure. wp_end. auto. } } *)
  (*   do 3 iInstr "Hprog". { transitivity (Some a_m); eauto. solve_addr. } *)
  (*   do 3 iInstr "Hprog". { transitivity (Some 0%a); eauto. solve_addr. } *)
  (*   do 2 iInstr "Hprog". { transitivity (Some b_m); eauto. solve_addr. } *)
  (*   iInstr "Hprog". solve_pure_addr. *)
  (*   iGo "Hprog". *)
  (*   (* continuation *) *)
  (*   rewrite (region_addrs_zeroes_split _ a_m') //; [| solve_addr]. *)
  (*   iDestruct (region_mapsto_split _ _ a_m' with "Hmem") as "[Hmem_fresh Hmem]". *)
  (*   solve_addr. by rewrite replicate_length //. *)
  (*   iDestruct ("Hinv_close" with "[Hprog Hmemptr Hmem $Hna]") as ">Hna". *)
  (*   { iNext. iExists b_m, a_m'. iFrame. iSplitR. iPureIntro. *)
  (*     by unfold malloc_subroutine_instrs_length. iPureIntro; solve_addr. } *)
  (*   iApply (wp_wand with "[-]"). *)
  (*   { iApply "Hφ". iFrame. *)
  (*     iDestruct (big_sepM_insert with "[$Hrmap $Hr4]") as "Hrmap". *)
  (*     by rewrite lookup_delete. rewrite insert_delete. *)
  (*     iDestruct (big_sepM_insert with "[$Hrmap $Hr3]") as "Hrmap". *)
  (*     by rewrite lookup_insert_ne // lookup_delete //. *)
  (*     rewrite insert_commute // insert_delete. *)
  (*     iDestruct (big_sepM_insert with "[$Hrmap $Hr2]") as "Hrmap". *)
  (*     by rewrite !lookup_insert_ne // lookup_delete //. *)
  (*     rewrite (insert_commute _ r_t2 r_t4) // (insert_commute _ r_t2 r_t3) //. *)
  (*     rewrite insert_delete. *)
  (*     rewrite (insert_commute _ r_t3 r_t2) // (insert_commute _ r_t4 r_t2) //. *)
  (*     rewrite (insert_commute _ r_t4 r_t3) //. iFrame. *)
  (*     iExists a_m, a_m', size. iFrame. auto. } *)
  (*   { auto. } *)
  (* Qed. *)

  (* Lemma simple_malloc_subroutine_valid N b e : *)
  (*   na_inv logrel_nais N (malloc_inv b e) -∗ *)
  (*   interp (WCap E b e b). *)
  (* Proof. *)
  (*   iIntros "#Hmalloc". *)
  (*   rewrite fixpoint_interp1_eq /=. iIntros (r). iNext. iModIntro. *)
  (*   iIntros "(#[% Hregs_valid] & Hregs & Hown)". *)
  (*   iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]";[rewrite lookup_insert;eauto|]. *)
  (*   destruct H with r_t0 as [? ?]. *)
  (*   iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[r_t0 Hregs]";[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|]. *)
  (*   destruct H with r_t1 as [? ?]. *)
  (*   iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[r_t1 Hregs]";[rewrite !lookup_delete_ne// !lookup_insert_ne//;eauto|]. *)
  (*   iApply (wp_wand with "[-]"). *)
  (*   iApply (simple_malloc_subroutine_spec with "[- $Hown $Hmalloc $Hregs $r_t0 $HPC $r_t1]");[|solve_ndisj|].  *)
  (*   3: { iSimpl. iIntros (v) "[H | ->]". iExact "H". iIntros (Hcontr); done. } *)
  (*   { rewrite !dom_delete_L dom_insert_L. apply regmap_full_dom in H as <-. set_solver. } *)
  (*   unshelve iDestruct ("Hregs_valid" $! r_t0 _ _ H0) as "Hr0_valid";auto. *)
  (*   iDestruct (jmp_to_unknown with "Hr0_valid") as "Hcont". *)
  (*   iNext. iIntros "((Hown & Hregs) & Hr_t0 & HPC & Hres)". *)
  (*   iDestruct "Hres" as (ba ea size Hsizeq Hsize) "[Hr_t1 Hbe]". *)

  (*   iMod (region_integers_alloc _ _ _ _ _ RWX with "Hbe") as "#Hbe"; auto. *)
  (*   by apply Forall_replicate. *)
  (*   rewrite -!(delete_insert_ne _ r_t1)//. *)
  (*   iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[apply lookup_delete|rewrite insert_delete]. *)
  (*   rewrite -!(delete_insert_ne _ r_t0)//. *)
  (*   iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs";[apply lookup_delete|rewrite insert_delete delete_insert_delete]. *)
  (*   set regs := <[_:=_]> _. *)

  (*   iApply ("Hcont" $! regs). *)
  (*   { iPureIntro. subst regs. rewrite !dom_insert_L dom_delete_L. *)
  (*     rewrite regmap_full_dom; eauto. set_solver. } *)
  (*   iFrame. iApply big_sepM_sep. iFrame. iApply big_sepM_intuitionistically_forall. *)
  (*   iIntros "!>" (r' w Hr'). subst regs. *)
  (*   destruct (decide (r' = r_t0)). { subst r'. rewrite lookup_insert in Hr'. by simplify_eq. } *)
  (*   destruct (decide (r' = r_t1)). *)
  (*   { subst r'. rewrite lookup_insert_ne // lookup_insert in Hr'. simplify_eq. iApply "Hbe". } *)
  (*   destruct (decide (r' = r_t2)). *)
  (*   { subst r'. repeat (rewrite lookup_insert_ne // in Hr'; []). rewrite lookup_insert in Hr'. *)
  (*     simplify_eq. rewrite /interp !fixpoint_interp1_eq //. } *)
  (*   destruct (decide (r' = r_t3)). *)
  (*   { subst r'. repeat (rewrite lookup_insert_ne // in Hr'; []). rewrite lookup_insert in Hr'. *)
  (*     simplify_eq. rewrite /interp !fixpoint_interp1_eq //. } *)
  (*   destruct (decide (r' = r_t4)). *)
  (*   { subst r'. repeat (rewrite lookup_insert_ne // in Hr'; []). rewrite lookup_insert in Hr'. *)
  (*     simplify_eq. rewrite /interp !fixpoint_interp1_eq //. } *)
  (*   repeat (rewrite lookup_insert_ne // in Hr'; []). apply lookup_delete_Some in Hr' as [? Hr']. *)
  (*   unshelve iSpecialize ("Hregs_valid" $! r' _ _ Hr'). done. done. *)
  (* Qed. *)

End SimpleMalloc.
