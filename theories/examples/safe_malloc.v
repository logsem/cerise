From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From cap_machine Require Import logrel addr_reg_sample fundamental rules proofmode.
From cap_machine.examples Require Import static_spinlock.

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
          `{lockG Σ, MP: MachineParameters}.

  Ltac iInstr_inv Hinv :=
    wp_instr
    ; iInv Hinv as ">Hprog" "Hcls"
    ; codefrag_facts "Hprog" (* TODO fix this, because it duplicates the hypothesis *)
    ; iInstr "Hprog"
    ; try (match goal with
           | h: _ |- isCorrectPC _ => apply isCorrectPC_intro; [solve_addr| auto]
           end)
    ; try (match goal with
           | h: _ |- isCorrectPC _ => apply isCorrectPC_intro; [admit| auto]
           end)
    ; try (iMod ("Hcls" with "Hprog") as "_" ; iModIntro ; wp_pure).

  (* TODO we actually NEED to store the capability pointing to the lock,
          because we only have the RX permission, not RWX. *)
  (* offset_lock = last address of the free memory *)
  Definition malloc_pre_spin (offset_lock : Z) :=
    encodeInstrsW [
        (* bm: *)
     Lt r_t3 0 r_t1; (* ;; check that size > 0 *)
     Mov r_t2 PC;    (* ;; jmp after fail if   *)
     Lea r_t2 4;     (* ;; yes ; continue and  *)
     Jnz r_t2 r_t3;  (* ;; fail if not         *)
     Fail;
        (* xm: *)
     Mov r_t5 PC;
     Lea r_t5 (offset_lock - 5)%Z;
     Load r_t5 r_t5
      ].

  Definition malloc_post_spin (offset : Z) :=
    encodeInstrsW [
     Mov r_t2 PC;
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
     Store r_t5 0;    (* Release the lock - we don't need CAS *)
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


  Definition malloc_subroutine_instrs' (offset offset_lock: Z) :=
     malloc_pre_spin offset_lock
       ++ spinlock_instrs' r_t5 r_t6 r_t7 r_t8
       ++ malloc_post_spin offset.

  Definition malloc_pre_spin_length : Z :=
    Eval cbv in (length (malloc_pre_spin 0%Z)).

  Definition malloc_pre_post_length : Z :=
    Eval cbv in (length (malloc_pre_spin 0%Z)).

  Definition spinlock_length : Z :=
    Eval cbv in (length (spinlock_instrs' PC PC PC PC)).

  Definition malloc_subroutine_instrs_length : Z :=
    Eval cbv in (length (malloc_subroutine_instrs' 0%Z 0%Z)).

  Definition malloc_subroutine_instrs (offset_lock : Z) :=
    malloc_subroutine_instrs'
      (malloc_subroutine_instrs_length - (5+spinlock_length))
      offset_lock.

  Definition malloc_inv (b e : Addr) γ : iProp Σ :=
    (codefrag b (malloc_subroutine_instrs e)
     ∗ e ↦ₐ WCap RWX b (e^+2)%a (e^+1)%a
     ∗ is_lock γ (e ^+1)%a
         (  ∃ b_m a_m,
             ⌜(b + malloc_subroutine_instrs_length)%a = Some b_m⌝
             ∗ b_m ↦ₐ (WCap RWX b_m e a_m)
             ∗ [[a_m, e]] ↦ₐ [[ region_addrs_zeroes a_m e ]]
             ∗ ⌜(b_m < a_m)%a ∧ (a_m <= e)%a⌝)%I).


  Lemma malloc_prelock_spec
    (i : CoreN)
    (wsize: Word)
    (b e : Addr)
    w2 w3 w5
    N E
    (φ : language.val cap_lang → iProp Σ) :

    let e' := (e^+2)%a in
    SubBounds b e' b (b ^+ malloc_subroutine_instrs_length)%a ->
    ↑N ⊆ E →
    (    inv N (codefrag b (malloc_pre_spin e)
                ∗ e ↦ₐ WCap RWX b e' (e^+1)%a)
         ∗ (i, PC) ↦ᵣ WCap RX b e' b
         ∗ (i, r_t1) ↦ᵣ wsize
         ∗ (i, r_t2) ↦ᵣ w2
         ∗ (i, r_t3) ↦ᵣ w3
         ∗ (i, r_t5) ↦ᵣ w5
         ∗ ▷ (   (i, PC) ↦ᵣ WCap RX b e' (b ^+ malloc_pre_spin_length)%a
                 ∗ (i, r_t1) ↦ᵣ wsize
                 ∗ (i, r_t2) ↦ᵣ WCap RX b e' (b ^+ 5)%a
                 ∗ (i, r_t3) ↦ᵣ WInt 1%nat
                 ∗ (i, r_t5) ↦ᵣ WCap RWX b e' (e ^+1)%a
                 ∗ ⌜ exists size:Z, (0 < size)%Z /\ wsize = WInt size ⌝
                 -∗ WP (i, Seq (Instr Executable)) @ E {{ φ }}%I))
    ⊢ WP (i, Seq (Instr Executable)) @ E {{ λ v, φ v ∨ ⌜v = (i, FailedV)⌝ }}%I.
  Proof.
    intro e'.
    iIntros (Hbounds HN) "(#Hfinv & HPC & Hr1 & Hr2 & Hr3 & Hr5 & Hφ)".
    iDestruct (inv_split_l with "Hfinv") as "Hinv".
    destruct (wsize) as [size|].

    2: { iInstr_inv "Hinv". wp_end. eauto. }
    do 3 iInstr_inv "Hinv".

    (* we need to destruct on the cases for the size *)
    destruct (decide (0 < size)%Z) as [Hsize | Hsize].
    2: { (* the program will not jump, and go to the fail instruction *)
      rewrite (_: Z.b2z (0%nat <? size)%Z = 0); cycle 1.
      { apply Z.ltb_nlt in Hsize. rewrite Hsize //. }
      iInstr_inv "Hinv". iInstr_inv "Hinv". wp_end. eauto. }

    rewrite (_: Z.b2z (0%nat <? size)%Z = 1); cycle 1.
    { rewrite (_: (0%nat <? size)%Z = true ); auto. by apply Z.ltb_lt. }


    do 3 iInstr_inv "Hinv".
    { transitivity (Some e). admit. done. }

    wp_instr
    ; iInv "Hfinv" as ">[Hprog Hcaplock]" "Hcls"
    ; codefrag_facts "Hprog" (* TODO fix this, because it duplicates the hypothesis *).
    iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_load_success_same_notinstr with "[$HPC $Hi $Hr5 $Hcaplock]").
    { exact (WInt 0). } (* TODO : why do I have to provide a word ? *)
    { rewrite decode_encode_instrW_inv ; auto. }
    { apply isCorrectPC_intro; [admit| auto]. }
    { auto. }
    { admit. }
    { transitivity (Some (b ^+8)%a) ; solve_addr ; done. }
    iNext ; iIntros "(HPC & Hr5 & Hi & Hcaplock)".
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "[$Hprog $Hcaplock]") as "_".
    simpl ; iModIntro ; wp_pure.

    iApply (wp_wand with "[-]").
    { iApply "Hφ".
      rewrite /malloc_pre_spin_length.
      iFrame.
      iPureIntro. eexists. split ; eauto. }
    iIntros (?) "?" ; iFrame.
  Admitted.

  
  Lemma simple_malloc_subroutine_spec
    (i : CoreN)
    (wsize: Word)
    (cont: Word)
    (b e : Addr)
    (rmap : (gmap (CoreN * RegName) Word))
    N E γ
    (φ : language.val cap_lang → iProp Σ) :

    dom (gset (CoreN*RegName)) rmap =
      (set_map (fun r => (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0) ; (i, r_t1) ]} →

    (exists b_m, (b + malloc_subroutine_instrs_length)%a = Some b_m /\ (b_m < e)%a) ->
    ↑N ⊆ E →
    (  inv N (malloc_inv b e γ)
     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
     ∗ (i, r_t0) ↦ᵣ cont
     ∗ (i, PC) ↦ᵣ WCap RX b (e ^+2)%a b
     ∗ (i, r_t1) ↦ᵣ wsize
       ∗ ▷ (([∗ map] r↦w ∈ <[(i, r_t2) := WInt 0%Z]>
               (<[(i, r_t3) := WInt 0%Z]>
                  (<[(i, r_t4) := WInt 0%Z]>
                     (<[(i, r_t5) := WInt 0%Z]>
                        (<[(i, r_t6) := WInt 0%Z]>
                           (<[(i, r_t7) := WInt 0%Z]>
                              (<[(i, r_t8) := WInt 0%Z]> rmap)))))), r ↦ᵣ w)
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
    assert (Hbounds: SubBounds b (e ^+ 2)%a b (b ^+ (length (malloc_subroutine_instrs e)))%a) by solve_addr.
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
    iDestruct (inv_split with "Hinv") as "[Hinv_code Hinv_lock]".
    rewrite {2}/codefrag.
    rewrite {2}/malloc_subroutine_instrs /malloc_subroutine_instrs'.
    rewrite (region_mapsto_split _ _ (b ^+ malloc_pre_spin_length)%a).
    2:{ cbn; rewrite /malloc_pre_spin_length; solve_addr. }
    2:{ cbn; rewrite /malloc_pre_spin_length.
        assert (H0 : (b+8)%f = Some (b ^+8)%a) by solve_addr.
        apply (finz_incr_iff_dist b (b ^+8)%a 8%nat) in H0.
        destruct H0 as [_ ?].
        symmetry. apply H0. }
    rewrite (region_mapsto_split (b ^+ malloc_pre_spin_length)%a _
               ((b ^+ malloc_pre_spin_length ^+ spinlock_length)%a)).
    2:{ rewrite /malloc_pre_spin_length /spinlock_length; solve_addr. }
    2:{ cbn; rewrite /malloc_pre_spin_length /spinlock_length.
        set (b' := (b ^+ 8)%a).
        assert (H0 : ((b ^+ 8)%a+6)%f = Some ((b ^+ 8)%a ^+6)%a) by solve_addr.
        apply (finz_incr_iff_dist b' (b' ^+6)%a 6%nat) in H0.
        destruct H0 as [_ ?].
        symmetry. apply H0. }
    iDestruct (inv_split with "Hinv_code") as "[Hinv_code_pre H']".
    iDestruct (inv_split with "H'") as "[Hinv_code_spin Hinv_code_post]".
    iClear "Hinv_code"; iClear "H'".
    rewrite /length /=.

    iAssert ( inv N (codefrag b (malloc_pre_spin e)))
              as "Hinv_pre"  ; first iFrame "#".
    iClear "Hinv_code_pre".

    iAssert ( inv N (codefrag (b ^+ malloc_pre_spin_length)%a
                       (spinlock_instrs' r_t5 r_t6 r_t7 r_t8)))
              as "Hinv_spin"  ; first iFrame "#".
    iClear "Hinv_code_spin".

    iAssert ( inv N (codefrag ((b ^+ malloc_pre_spin_length) ^+ spinlock_length)%a
                       (malloc_post_spin (malloc_subroutine_instrs_length - (5 + spinlock_length)))))
              as "Hinv_post"
    ; first ( iFrame "#"
         ; rewrite /codefrag
         ; simpl ; rewrite /malloc_pre_spin_length /malloc_pre_post_length /spinlock_length
         ; replace ((((b ^+ 8) ^+ 6) ^+ 26%nat)%a) with (b ^+ 40%nat)%a by solve_addr
         ; iFrame "#").
    iClear "Hinv_code_post".

    (** ====== Pre lock ====== *)

    iApply (wp_wand_l _ _ _ (λ v, ((φ v ∨ ⌜v = (i, FailedV)⌝) ∨ ⌜v = (i, FailedV)⌝)))%I. iSplitR.
    { iIntros (v) "[H|H] /=";auto. }
    iApply (malloc_prelock_spec _ _ _ _ _ _ _ _ _ (fun v => (φ v ∨ ⌜v = (i, FailedV)⌝)%I)
             with "[-$HPC $Hr1 $Hr2 $Hr3 $Hr5 Hinv_pre]") ;eauto.
    iSplitR.
   { iClear "Hinv_lock"
      ; iClear "Hinv_pre"
      ; iClear "Hinv_spin"
      ; iClear "Hinv_post".

    (* iDestruct (inv_split with "Hinv") as "[Hinv_code Hinv_lock]". *)
    rewrite {1}/codefrag.
    rewrite {1}/malloc_subroutine_instrs /malloc_subroutine_instrs'.
    rewrite (region_mapsto_split _ _ (b ^+ malloc_pre_spin_length)%a).
    2:{ cbn; rewrite /malloc_pre_spin_length; solve_addr. }
    2:{ cbn; rewrite /malloc_pre_spin_length.
        assert (H' : (b+8)%f = Some (b ^+8)%a) by solve_addr.
        apply (finz_incr_iff_dist b (b ^+8)%a 8%nat) in H'.
        destruct H' as [_ H'].
        symmetry; apply H'. }
    rewrite (region_mapsto_split (b ^+ malloc_pre_spin_length)%a _
               ((b ^+ malloc_pre_spin_length ^+ spinlock_length)%a)).
    2:{ rewrite /malloc_pre_spin_length /spinlock_length; solve_addr. }
    2:{ cbn; rewrite /malloc_pre_spin_length /spinlock_length.
        set (b' := (b ^+ 8)%a).
        assert (H' : ((b ^+ 8)%a+6)%f = Some ((b ^+ 8)%a ^+6)%a) by solve_addr.
        apply (finz_incr_iff_dist b' (b' ^+6)%a 6%nat) in H'.
        destruct H' as [_ H'].
        symmetry; apply H'. }
    match goal with
    | h: _ |- context [ is_lock ?g ?b ?P] => set (L := is_lock g b P)
    end.
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P1 := region_mapsto b e l)
    end.
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P2 := region_mapsto b e l)
    end.
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P3 := region_mapsto b e l)
    end.
    match goal with
    | h: _ |- context [ mapsto ?e ?d ?v ] => set (IE := mapsto e d v)
    end.
    simpl.
    iAssert ( inv N ( (P1 ∗ IE) ∗ ( P2 ∗ P3 ) ∗ L ) ) as "Hinv1".
    iApply (inv_iff with "[$Hinv]")
     ; first (do 2 iModIntro ; iSplit ;
              [iIntros "((?&?&?) & ? & ?)" | iIntros "((? & ?) & (?&?) & ?)" ]
               ; iFrame).
    iDestruct (inv_split_l with "Hinv1") as "Hinv2".
    iClear "Hinv" ; iClear "Hinv1" ; clear -P1.
    assert (P1 =  codefrag b (malloc_pre_spin e)).
    { subst P1. rewrite /codefrag /malloc_pre_spin /malloc_pre_spin_length.
      by cbn. }
    auto.
    }
    iNext ; iIntros "(HPC & Hr1 & Hr2 & Hr3 & Hr5 & %Hsize)".
    destruct Hsize as (size & ? & ->).

    (** ====== Spinlock ====== *)
    iApply (spinlock_spec i _ _ _ _ r_t5 r_t6 r_t7 r_t8 with
             "[-$HPC $Hr5 $Hr6 $Hr7 $Hr8]")
    ;[ apply ExecPCPerm_RX
       |.. ].
    { rewrite /malloc_pre_spin_length ; solve_addr. }
    { auto. }
    { admit. }
    { eauto. }
    iSplitR.
    { iAssert ( inv N (codefrag (b ^+ 8)%a (spinlock_instrs' r_t5 r_t6 r_t7 r_t8)
                       ∗ is_lock γ (e ^+1)%a (∃ b_m a_m : Addr,
                               ⌜(b + malloc_subroutine_instrs_length)%a = Some b_m⌝
                                                                          ∗ b_m ↦ₐ WCap RWX b_m e a_m
                                                                          ∗
                                                                            [[a_m,e]]↦ₐ[[region_addrs_zeroes a_m e]] ∗ ⌜(b_m < a_m)%a ∧ (a_m <= e)%a⌝)))%I
                as "Hinv_spinlock" .
      admit.
      iFrame "Hinv_spinlock". }
    iNext ; iIntros "(HPC & Hr5 & Hr6 & Hr7 & Hr8 & Hbm & Hlocked)".

    (** ====== Post-Lock ======*)
    iDestruct "Hbm"
      as (b_m a_m) "(%Hbm_bounds & Hb_m & Hfree_reg & %Ham_bounds)".
    rewrite /length /=.
    replace ( ((b ^+ malloc_pre_spin_length) ^+ 6%nat)%a )
      with (b ^+ 14)%a
           by (rewrite /malloc_pre_spin_length ; solve_addr).
    replace ( ((b ^+ malloc_pre_spin_length) ^+ spinlock_length)%a )
      with (b ^+ 14)%a
           by (rewrite /malloc_pre_spin_length /spinlock_length ; solve_addr).


    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_reg_fromPC with "[ $HPC $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+1)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Lea *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_lea_success_z with "[ $HPC $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+2)%a); solve_addr; done. }
    { transitivity (Some (b ^+ 39)%a)
      ; rewrite /spinlock_length /malloc_subroutine_instrs_length.
      admit. done. } (* TODO correct the offset *)
      (* ; solve_addr; done. } *)
    iNext; iIntros "(HPC & Hi & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.


    (* Load *)
    (* Open the invariant *)
    replace (b ^+ 39)%a with b_m by admit.
    (* by (rewrite /malloc_subroutine_instrs_length *)
    (*                              in Hbm_bounds ; solve_addr). *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_load_success_same_notinstr with "[ $HPC $Hr2 $Hi $Hb_m]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { rewrite /malloc_subroutine_instrs_length in Hbm_bounds
      ; solve_addr. }
    { transitivity (Some ((b ^+ 14) ^+3)%a); solve_addr; done. }
    iNext ; iIntros "(HPC & Hr2 & Hi & Hbm)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* GetA *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_Get_success with "[ $HPC $Hr3 $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+4)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr2 & Hr3)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.
    rewrite decode_encode_instr_inv /rules_Get.denote.


    (* Lea might fail *)

    (* Lea *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".

    destruct (a_m + size)%a as [a_m'|] eqn:Ha_m'; cycle 1.
    { (* Failure case: no registered rule for that yet; do it the manual way *)
      (* TODO: cf malloc, do not use rmap, but an empty map *)
      iAssert ([∗ map] k↦x ∈ (∅:gmap (CoreN * RegName) Word), k ↦ᵣ x)%I as "-#Hregs".
        by rewrite big_sepM_empty.

      iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "Hregs".
      by rewrite lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
      rewrite !lookup_insert_ne
      ; first by rewrite lookup_empty.
      all: try (match goal with
                | h:_ |- _ ≠ _ => simplify_pair_eq
                end).
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
      rewrite !lookup_insert_ne
      ; first by rewrite lookup_empty.
      all: try (match goal with
                | h:_ |- _ ≠ _ => simplify_pair_eq
                end).


      iApply (wp_lea _ i RX b (e ^+2)%a ((b ^+ 14) ^+ 4)%a
               with "[$Hregs $Hi]").
      { rewrite decode_encode_instrW_inv; done. }
      { admit. }
      { apply lookup_insert. }
      { rewrite /regs_of_core !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec & Hi & ?)".
      iDestruct "Hspec" as %Hspec.

      iDestruct ("Hcont" with "Hi") as "Hprog".
      iMod ("Hcls" with "Hprog") as "_".

      destruct Hspec as [| Hfail].
      { exfalso.
        clear - H4 Ha_m' H3 H1.
        simplify_map_eq by simplify_pair_eq. }
      { cbn.
        iApply wp_pure_step_later; auto.
        do 2 iModIntro.
        iApply wp_value.
        auto. } }



    iApply ( wp_lea_success_reg with "[ $HPC $Hr2 $Hr1 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+5)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr1 & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* GetA *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_Get_success with "[ $HPC $Hr1 $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+6)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr2 & Hr1)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.
    rewrite decode_encode_instr_inv /rules_Get.denote.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_reg with "[ $HPC $Hr4 $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+7)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr4 & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.
    (* might fail *)
    (* subseg *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".

    destruct (isWithin a_m a_m' b_m e) eqn:Ha_m'_within; cycle 1.
    { (* Failure case: manual mode. *)
      iAssert ([∗ map] k↦x ∈ (∅:gmap (CoreN * RegName) Word), k ↦ᵣ x)%I as "-#Hregs".
        by rewrite big_sepM_empty.

      iDestruct (big_sepM_insert with "[$Hregs $Hr4]") as "Hregs".
      by rewrite lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr3]") as "Hregs".
      rewrite !lookup_insert_ne
      ; first by rewrite lookup_empty.
      all: try (match goal with
                | h:_ |- _ ≠ _ => simplify_pair_eq
                end).
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
      rewrite !lookup_insert_ne
      ; first by rewrite lookup_empty.
      all: try (match goal with
                | h:_ |- _ ≠ _ => simplify_pair_eq
                end).
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
      rewrite !lookup_insert_ne
      ; first by rewrite lookup_empty.
      all: try (match goal with
                | h:_ |- _ ≠ _ => simplify_pair_eq
                end).

      iApply (wp_Subseg with "[$Hregs $Hi]").
      { rewrite decode_encode_instrW_inv; done. }
      { admit. }
      { apply lookup_insert. }
      { rewrite /regs_of_core !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec & Hi & ?)".

      iDestruct ("Hcont" with "Hi") as "Hprog".
      iMod ("Hcls" with "Hprog") as "_".

      iDestruct "Hspec" as %Hspec.
      destruct Hspec as [| Hfail].
      { exfalso. unfold addr_of_argument in *.
        clear -H1 H3 H4 H5 Ha_m'_within.
        simplify_map_eq by simplify_pair_eq.
        repeat match goal with H:_ |- _ => apply finz_of_z_eq_inv in H end; subst.
        congruence. }
      { cbn. iModIntro. wp_pure. wp_end. auto. } }


    
    iApply ( wp_subseg_success with "[ $HPC $Hr4 $Hr3 $Hr1 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some a_m); solve_addr; done. }
    { transitivity (Some (a_m ^+ size)%a); solve_addr; done. }
    { transitivity (Some ((b ^+ 14) ^+8)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr3 & Hr1 & Hr4)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.


    (* sub *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_add_sub_lt_success_dst_r with "[ $HPC $Hr1 $Hr3 $Hi ]") ; eauto.
    { rewrite decode_encode_instrW_inv ;cbn ; auto. }
    { transitivity (Some ((b ^+ 14) ^+9)%a); solve_addr; done. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    iNext; iIntros "(HPC & Hi & Hr1 & Hr3)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.
    rewrite decode_encode_instr_inv /denote /=.
    (* replace (a_m - (a_m ^+ size)%a)%Z with (-size)%Z by admit. *)

    (* Lea *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_lea_success_reg with "[ $HPC $Hr4 $Hr3 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+10)%a); solve_addr; done. }
    { transitivity (Some a_m%a) ; solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr3 & Hr4)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_reg with "[ $HPC $Hr3 $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+11)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr3 & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* sub *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_add_sub_lt_success_z_dst with "[ $HPC $Hr1 $Hi ]") ; eauto.
    { rewrite decode_encode_instrW_inv ;cbn ; auto. }
    { transitivity (Some ((b ^+ 14) ^+12)%a); solve_addr; done. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    iNext; iIntros "(HPC & Hi & Hr1)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.
    rewrite decode_encode_instr_inv /denote /=.
    (* replace (a_m - (a_m ^+ size)%a)%Z with (-size)%Z by admit. *)


    (* Lea *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_lea_success_reg with "[ $HPC $Hr3 $Hr1 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+13)%a); solve_addr; done. }
    { transitivity (Some 0%a) ; solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr1 & Hr3)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* GetB *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_Get_success with "[ $HPC $Hr1 $Hr3 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+14)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr1 & Hr3)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.
    rewrite decode_encode_instr_inv /rules_Get.denote.


    (* Lea *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_lea_success_reg with "[ $HPC $Hr3 $Hr1 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+15)%a); solve_addr; done. }
    { transitivity (Some b_m%a) ; solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr1 & Hr3)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Store *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_store_success_reg with "[ $HPC $Hr2 $Hr3 $Hi $Hbm ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+16)%a); solve_addr; done. }
    { solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr2 & Hr3 & Hbm)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_reg with "[ $HPC $Hr1 $Hr4 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+17)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr1 & Hr4)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (** --- release the lock --- *)
    rewrite (region_addrs_zeroes_split _ (a_m ^+ size)%a)
    ; [| solve_addr].
    iDestruct (region_mapsto_split _ _ (a_m ^+ size)%a with "Hfree_reg")
      as "[Hmem_fresh Hmem]".
    solve_addr. by rewrite replicate_length //.

    iApply (release_spec i _ _ _ _ r_t5 _ _ _ _ _ (* define P ? *) N E γ _
             with "[-$HPC $Hlocked $Hr5]") ; auto.
    { apply ExecPCPerm_RX. }
    { solve_addr. }
    { admit. }
    Unshelve.
    2: { exact (∃ b_m0 a_m0 : Addr,
               ⌜(b + malloc_subroutine_instrs_length)%a = Some b_m0⌝
                                                          ∗ b_m0 ↦ₐ WCap RWX b_m0 e a_m0
                                                          ∗ [[a_m0,e]]↦ₐ[[region_addrs_zeroes a_m0 e]] ∗ ⌜(b_m0 < a_m0)%a ∧ (a_m0 <= e)%a⌝)%I.
    }
    iSplitR.
    { iClear "Hinv_lock"
      ; iClear "Hinv_pre"
      ; iClear "Hinv_spin"
      ; iClear "Hinv_post".

    (* iDestruct (inv_split with "Hinv") as "[Hinv_code Hinv_lock]". *)
    rewrite {1}/codefrag.
    rewrite {1}/malloc_subroutine_instrs /malloc_subroutine_instrs'.
    rewrite (region_mapsto_split _ _ (b ^+ malloc_pre_spin_length)%a).
    2:{ cbn; rewrite /malloc_pre_spin_length; solve_addr. }
    2:{ cbn; rewrite /malloc_pre_spin_length.
        assert (H' : (b+8)%f = Some (b ^+8)%a) by solve_addr.
        apply (finz_incr_iff_dist b (b ^+8)%a 8%nat) in H'.
        destruct H' as [_ H'].
        symmetry; apply H'. }
    rewrite (region_mapsto_split (b ^+ malloc_pre_spin_length)%a _
               ((b ^+ malloc_pre_spin_length ^+ spinlock_length)%a)).
    2:{ rewrite /malloc_pre_spin_length /spinlock_length; solve_addr. }
    2:{ cbn; rewrite /malloc_pre_spin_length /spinlock_length.
        set (b' := (b ^+ 8)%a).
        assert (H' : ((b ^+ 8)%a+6)%f = Some ((b ^+ 8)%a ^+6)%a) by solve_addr.
        apply (finz_incr_iff_dist b' (b' ^+6)%a 6%nat) in H'.
        destruct H' as [_ H'].
        symmetry; apply H'. }
    match goal with
    | h: _ |- context [ is_lock ?g ?b ?P] => set (L := is_lock g b P)
    end.
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P1 := region_mapsto b e l)
    end.
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P2 := region_mapsto b e l)
    end.
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P3 := region_mapsto b e l)
    end.
    match goal with
    | h: _ |- context [ mapsto ?e ?d ?v ] => set (IE := mapsto e d v)
    end.

    subst P3. simpl.
    replace (malloc_post_spin (malloc_subroutine_instrs_length - (5 + spinlock_length)))
      with
      (encodeInstrsW
      [Mov r_t2 PC; Lea r_t2 (malloc_subroutine_instrs_length - (5 + spinlock_length))%Z;
       Load r_t2 r_t2; GetA r_t3 r_t2; Lea r_t2 r_t1;
       GetA r_t1 r_t2; Mov r_t4 r_t2; Subseg r_t4 r_t3 r_t1; Sub r_t3 r_t3 r_t1;
       Lea r_t4 r_t3; Mov r_t3 r_t2; Sub r_t1 0%Z r_t1; Lea r_t3 r_t1; GetB r_t1 r_t3;
       Lea r_t3 r_t1; Store r_t3 r_t2; Mov r_t1 r_t4]
      ++ encodeInstrsW [Store r_t5 0]
      ++
      encodeInstrsW [Mov r_t2 0%Z;
                     Mov r_t3 0%Z; Mov r_t4 0%Z; Mov r_t5 0%Z; Mov r_t6 0%Z; Mov r_t7 0%Z; Mov r_t8 0%Z;
                     Jmp r_t0])
    by (rewrite /malloc_post_spin ; auto).
    rewrite (region_mapsto_split ((b ^+ malloc_pre_spin_length) ^+ spinlock_length)%a _
               ((b ^+ 14) ^+ 17)%a ).
    2:{ rewrite /malloc_pre_spin_length /spinlock_length; solve_addr. }
    2:{ cbn; rewrite /malloc_pre_spin_length /spinlock_length.
        replace ( ((b ^+ 8) ^+ 6)%a ) with ((b ^+ 14))%a by solve_addr.
        set (b' := (b ^+ 14)%a).
        assert (H' : ((b ^+ 14)%a+17)%f = Some ((b ^+ 14)%a ^+17)%a) by solve_addr.
        apply (finz_incr_iff_dist b' (b' ^+17)%a 17%nat) in H'.
        destruct H' as [_ H'].
        symmetry; apply H'. }

    rewrite (region_mapsto_split ((b ^+ 14) ^+ 17)%a _
               ((b ^+ 14) ^+ 18)%a ).
    2:{ solve_addr. }
    2:{ cbn.
        replace ((b ^+ 14) ^+ 17)%a with ((b ^+ 31))%a by solve_addr.
        replace ((b ^+ 14) ^+ 18)%a with ((b ^+ 31) ^+1)%a by solve_addr.
        rewrite finz_dist_S ; last solve_addr.
        rewrite finz_dist_0 ; last solve_addr.
        done. }
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P3 := region_mapsto b e l)
    end.
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P4 := region_mapsto b e l)
    end.
    match goal with
    | h: _ |- context [ region_mapsto ?b ?e ?l ] => set (P5 := region_mapsto b e l)
    end.
    iAssert ( inv N ( (P4 ∗ L) ∗ (P1 ∗ P2 ∗ P3 ∗ P5) ∗ IE ) ) as "Hinv1".
    iApply (inv_iff with "[$Hinv]")
     ; first (do 2 iModIntro ; iSplit ;
              [iIntros "((?&?&?&?&?) & ? & ?)" | iIntros "((? & ?) & (?&?&?&?) & ?)" ]
               ; iFrame).
    iDestruct (inv_split_l with "Hinv1") as "Hinv2".
    iClear "Hinv" ; iClear "Hinv1" ; clear -P4.
    assert (P4 =  codefrag ((b ^+ 14) ^+ 17)%a [encodeInstrW (Store r_t5 0)]).
    { subst P4. rewrite /codefrag /=.
      replace (((b ^+ 14) ^+ 17) ^+ 1%nat)%a with ((b ^+ 14) ^+ 18)%a by solve_addr.
      done. }
    rewrite H0.
    iFrame "Hinv2".
    }

    iSplitL "Hbm Hmem".
    iExists b_m , (a_m^+size)%a.
    replace a_m' with (a_m ^+size)%a by solve_addr.
    iFrame "∗%".
    iPureIntro. solve_addr.
    iNext; iIntros "(HPC & Hr5)".
    replace (((b ^+ 14) ^+ 17) ^+ 1)%a with (((b ^+ 14) ^+ 18)%a) by solve_addr.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_z with "[ $HPC $Hr2 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+19)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr2)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.



    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_z with "[ $HPC $Hr3 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+20)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr3)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_z with "[ $HPC $Hr4 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+21)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr4)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_z with "[ $HPC $Hr5 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+22)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr5)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_z with "[ $HPC $Hr6 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+23)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr6)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iDestruct "Hr7" as (w7) "Hr7".
    iApply ( wp_move_success_z with "[ $HPC $Hr7 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+24)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr7)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.

    (* Mov *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_move_success_z with "[ $HPC $Hr8 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    { transitivity (Some ((b ^+ 14) ^+25)%a); solve_addr; done. }
    iNext; iIntros "(HPC & Hi & Hr8)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.


    (* Jmp *)
    (* Open the invariant *)
    wp_instr
    ; iInv "Hinv_post" as ">Hprog" "Hcls"
    (* Apply the invariant *)
    ; iInstr_lookup "Hprog" as "Hi" "Hcont".
    iApply ( wp_jmp_success with "[ $HPC $Hr0 $Hi ]") ; eauto.
    { cbn ;rewrite decode_encode_instr_inv; eauto. }
    { apply isCorrectPC_intro ; [solve_addr| auto]. }
    iNext; iIntros "(HPC & Hi & Hr0)".
    (* Close the invariant *)
    iDestruct ("Hcont" with "Hi") as "Hprog".
    iMod ("Hcls" with "Hprog") as "_".
    simpl ; iModIntro ; wp_pure.


    iApply (wp_wand with "[-]").
    { iApply "Hφ". iFrame.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr8]") as "Hrmap".
      by rewrite lookup_delete. rewrite insert_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr7]") as "Hrmap".
      rewrite !lookup_insert_ne ;
        [by rewrite lookup_delete | simplify_pair_eq].
      iDestruct (big_sepM_insert with "[$Hrmap $Hr6]") as "Hrmap".
      rewrite !lookup_insert_ne ; [ | simplify_pair_eq | simplify_pair_eq].
      rewrite lookup_delete_ne  ; [ | simplify_pair_eq ].
      by rewrite lookup_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr5]") as "Hrmap".
      rewrite !lookup_insert_ne ; [ | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq].
      do 2 (rewrite lookup_delete_ne  ; [ |simplify_pair_eq]).
      by rewrite lookup_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr4]") as "Hrmap".
      rewrite !lookup_insert_ne ; [ | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq].
      do 3 (rewrite lookup_delete_ne  ; [ |simplify_pair_eq]).
      by rewrite lookup_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr3]") as "Hrmap".
      rewrite !lookup_insert_ne ; [ | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq].
      do 4 (rewrite lookup_delete_ne  ; [ |simplify_pair_eq]).
      by rewrite lookup_delete.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr2]") as "Hrmap".
      rewrite !lookup_insert_ne ; [ | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq
                                    | simplify_pair_eq].
      do 5 (rewrite lookup_delete_ne  ; [ |simplify_pair_eq]).
      by rewrite lookup_delete.
      iSplitL "Hrmap".
      { rewrite (insert_commute _ (i, r_t7) (i, r_t8)) ; last simplify_pair_eq.
        rewrite insert_delete.
        do 2 (rewrite (insert_commute _ (i, r_t6) _) ; last simplify_pair_eq).
        rewrite insert_delete.
        do 3 (rewrite (insert_commute _ (i, r_t5) _) ; last simplify_pair_eq).
        rewrite insert_delete.
        do 4 (rewrite (insert_commute _ (i, r_t4) _) ; last simplify_pair_eq).
        rewrite insert_delete.
        do 5 (rewrite (insert_commute _ (i, r_t3) _) ; last simplify_pair_eq).
        rewrite insert_delete.
        do 6 (rewrite (insert_commute _ (i, r_t2) _) ; last simplify_pair_eq).
        rewrite insert_delete.
        do 6 (rewrite (insert_commute _ (i, r_t8) _) ; last simplify_pair_eq).
        do 5 (rewrite (insert_commute _ (i, r_t7) _) ; last simplify_pair_eq).
        do 4 (rewrite (insert_commute _ (i, r_t6) _) ; last simplify_pair_eq).
        do 3 (rewrite (insert_commute _ (i, r_t5) _) ; last simplify_pair_eq).
        do 2 (rewrite (insert_commute _ (i, r_t4) _) ; last simplify_pair_eq).
        rewrite (insert_commute _ (i, r_t3) _) ; last simplify_pair_eq.
        iFrame. }
      iExists a_m, a_m', size.
      replace (a_m ^+ size)%a with a_m' by solve_addr.
      iFrame.
      iSplit ; eauto.
    }
      iIntros (v) "Hφ" ; iLeft ; done.
Admitted.





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
