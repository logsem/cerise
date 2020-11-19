From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine.examples Require Import stack_macros.
From cap_machine Require Import rules logrel fundamental. 

Section wbcf.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

   Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [_ | a' a]; inversion Hlen; simpl
    end.
  
  Ltac iPrologue prog :=
    (try iPrologue_pre);
    iDestruct prog as "[Hi Hprog]"; 
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _ 
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end. 

  Ltac iCorrectPC index :=
    match goal with
    | [ Hnext : ∀ (i : nat) (ai aj : Addr), ?a !! i = Some ai
                                          → ?a !! (i + 1) = Some aj
                                          → (ai + 1)%a = Some aj,
          Ha_first : ?a !! 0 = Some ?a_first,
          Ha_last : list.last ?a = Some ?a_last |- _ ]
      => apply isCorrectPC_bounds_alt with a_first a_last; eauto; split ;
         [ apply Z.lt_le_incl;auto |
           apply incr_list_le_middle with a index; auto ]
    end.

  Ltac addr_succ :=
    match goal with
    | H : _ |- (?a1 + ?z)%a = Some ?a2 =>
      rewrite /incr_addr /=; do 2 f_equal; apply eq_proofs_unicity; decide equality
    end.
       
  Ltac wp_push_z Hstack a_lo a_hi b e a_cur a_next φ push1 push2 push3 ws prog ptrn :=
    match goal with
    | H : strings.length _ = _ |- _ =>
      let wa := fresh "wa" in
      let Ha := fresh "w" in
      let Ha_next := fresh "H" in
      iDestruct prog as "[Hi Hf3]";
      destruct ws as [_ | wa ws]; first inversion H;
      iDestruct Hstack as "[Ha Hstack]"; 
      iApply (push_z_spec push1 push2 push3 _ _ _ _ _ _ _ b e a_cur a_next φ);
      eauto; try addr_succ; try apply PermFlows_refl; 
      [split; eauto; apply isCorrectPC_bounds with a_lo a_hi; eauto; split; done|];
      iFrame; iNext; iIntros ptrn
    end.

   Ltac wp_push_r Hstack a_lo a_hi b e a_cur a_next φ push1 push2 push3 ws prog ptrn :=
    match goal with
    | H : length _ = _ |- _ =>
      let wa := fresh "wa" in
      let Ha := fresh "w" in
      iDestruct prog as "[Hi Hf3]";
      destruct ws as [_ | wa ws]; first inversion H;
      iDestruct Hstack as "[Ha Hstack]"; 
      iApply (push_r_spec push1 push2 push3 _ _ _ _ _ _ _ _ b e a_cur a_next φ);
      eauto; try addr_succ; try apply PermFlows_refl;
      [split; eauto; apply isCorrectPC_bounds with a_lo a_hi; eauto; split; done|];
      iFrame; iNext; iIntros ptrn
    end.

   (* The following ltac gets out the next general purpuse register *)
   Ltac get_genpur_reg Hr_gen wsr ptr :=
     let w := fresh "wr" in 
       destruct wsr as [? | w wsr]; first (by iApply bi.False_elim);
       iDestruct Hr_gen as ptr.

   (* namespace definitions for the regions *)
   Definition regN : namespace := nroot .@ "regN".

   (* lemma for comparing namespaces *)
   Lemma list_names_disj_format {X : Type} `{EqDecision X} `{Countable X}
         l (x : X) : list_names l ## ↑regN.@x.
   Proof.
     induction l.
     - apply disjoint_empty_l.
     - apply disjoint_union_l. split.
       + solve_ndisj.  
       + apply IHl. 
   Qed.    

   (* TODO: move this earlier *)
   Lemma region_prepare W :
     region W ≡ open_region_many [] W. 
   Proof.
     rewrite open_region_many_eq /open_region_many_def /=. 
     rewrite region_eq /region_def. done.
   Qed.
     

   (* well bracketed control flow, using scall *)
   (* assume r1 contains an executable pointer to adversarial code 
     (no linking table yet) *)                 
   Definition f3 (r1 : RegName) (p : Perm) : iProp Σ :=
    (    (* push 1 *)
           push_z (a-0) (a-1) p r_stk 1
    (* scall r1([],[r1]) *)
         (* push private state *)
         ∗ push_r (a-2) (a-3) p r_stk r1
         (* push activation code *)
         ∗ push_z (a-4) (a-5) p r_stk w_1
         ∗ push_z (a-6) (a-7) p r_stk w_2
         ∗ push_z (a-8) (a-9) p r_stk w_3
         ∗ push_z (a-10) (a-11) p r_stk w_4a
         ∗ push_z (a-12) (a-13) p r_stk w_4b
         ∗ push_z (a-14) (a-15) p r_stk w_4c
         (* push old pc *)
         ∗ a-16 ↦ₐ[p] move_r r_t1 PC
         ∗ a-17 ↦ₐ[p] lea_z r_t1 64 (* offset to "after" *)
         ∗ push_r (a-18) (a-19) p r_stk r_t1
         (* push stack pointer *)
         ∗ a-20 ↦ₐ[p] lea_z r_stk 1
         ∗ a-21 ↦ₐ[p] store_r r_stk r_stk
         (* set up protected return pointer *)
         ∗ a-22 ↦ₐ[p] move_r r_t0 r_stk
         ∗ a-23 ↦ₐ[p] lea_z r_t0 (-7)%Z
         ∗ a-24 ↦ₐ[p] restrict_z r_t0 (local_e)
         (* restrict stack capability *)
         ∗ a-25 ↦ₐ[p] geta r_t1 r_stk
         ∗ a-26 ↦ₐ[p] add_r_z r_t1 r_t1 1
         ∗ a-27 ↦ₐ[p] gete r_t2 r_stk
         ∗ a-28 ↦ₐ[p] subseg_r_r r_stk r_t1 r_t2
         (* clear the unused part of the stack *)
         (* mclear r_stk: *)
         ∗ mclear (region_addrs_aux (a-29) 22) p r_stk 10 2 (* contiguous *)
         (* clear non-argument registers *)
         ∗ rclear (region_addrs_aux (a-51) 29) p
                  (list_difference all_registers [PC;r_stk;r_t0;r1])
         (* jump to unknown code *)
         ∗ a-80 ↦ₐ[p] jmp r1
    (* after: *)
         (* pop the restore code *)
         (* to shorten the program we will do it all at once *)
         ∗ a-81 ↦ₐ[p] sub_z_z r_t1 0 7
         ∗ a-82 ↦ₐ[p] lea_r r_stk r_t1
         (* pop the private state into appropriate registers *)
         ∗ pop (a-83) (a-84) (a-85) p r_stk r1
    (* END OF SCALL *)
         ∗ a-86 ↦ₐ[p] load_r r_t2 r_stk
         ∗ a-87 ↦ₐ[p] sub_z_z r_t1 0 1
         ∗ a-88 ↦ₐ[p] lea_r r_stk r_t1
         (* assert r1 points to 1. For "simplicity" I am not using the assert macro ! 
            but rather a hardcoded version for f3. TODO: change this to actual assert *)
         ∗ a-89 ↦ₐ[p] move_r r_t1 PC
         ∗ a-90 ↦ₐ[p] lea_z r_t1 83(* offset to fail at a173 *)
         ∗ a-91 ↦ₐ[p] sub_r_z r_t2 r_t2 1
         ∗ a-92 ↦ₐ[p] jnz r_t1 r_t2
        (* push 2 *)
         ∗ push_z (a-93) (a-94) p r_stk 2
    (* scall r1 ([],[]) *)
         (* push private state *)
         (* push activation code *)
         ∗ push_z (a-95) (a-96) p r_stk w_1
         ∗ push_z (a-97) (a-98) p r_stk w_2
         ∗ push_z (a-99) (a-100) p r_stk w_3
         ∗ push_z (a-101) (a-102) p r_stk w_4a
         ∗ push_z (a-103) (a-104) p r_stk w_4b
         ∗ push_z (a-105) (a-106) p r_stk w_4c
         (* push old pc *)
         ∗ a-107 ↦ₐ[p] move_r r_t1 PC
         ∗ a-108 ↦ₐ[p] lea_z r_t1 64 (* offset to "after" *)
         ∗ push_r (a-109) (a-110) p r_stk r_t1
         (* push stack pointer *)
         ∗ a-111 ↦ₐ[p] lea_z r_stk 1
         ∗ a-112 ↦ₐ[p] store_r r_stk r_stk
         (* set up protected return pointer *)
         ∗ a-113 ↦ₐ[p] move_r r_t0 r_stk
         ∗ a-114 ↦ₐ[p] lea_z r_t0 (-7)%Z
         ∗ a-115 ↦ₐ[p] restrict_z r_t0 (local_e)
         (* restrict stack capability *)
         ∗ a-116 ↦ₐ[p] geta r_t1 r_stk
         ∗ a-117 ↦ₐ[p] add_r_z r_t1 r_t1 1
         ∗ a-118 ↦ₐ[p] gete r_t2 r_stk
         ∗ a-119 ↦ₐ[p] subseg_r_r r_stk r_t1 r_t2
         (* clear the unused part of the stack *)
         (* mclear r_stk: *)
         ∗ mclear (region_addrs_aux (a-120) 22) p r_stk 10 2 (* contiguous *)
         (* clear non-argument registers *)
         ∗ rclear (region_addrs_aux (a-142) 29) p
                  (list_difference all_registers [PC;r_stk;r_t0;r1])
         (* jump to unknown code *)
         ∗ a-171 ↦ₐ[p] jmp r1
         (* after: *)
         (* pop the restore code *)
         (* to shorten the program we will do it all at once *)
         ∗ a-172 ↦ₐ[p] sub_z_z r_t1 0 7
         ∗ a-173 ↦ₐ[p] lea_r r_stk r_t1
         (* pop the private state into appropriate registers *)
         (* END OF SCALL *)
         ∗ a-174 ↦ₐ[p] halt
         (* The following code is jumped to in the case of failure of assert *)
         (* set the flag to 1 to indicate failure. flag is set to be the address a177 *)
         ∗ a-175 ↦ₐ[p] move_r r_t1 PC
         ∗ a-176 ↦ₐ[p] lea_z r_t1 4(* offset to flag *)
         ∗ a-177 ↦ₐ[p] store_z r_t1 1
         ∗ a-178 ↦ₐ[p] halt
    )%I.

   Lemma rtc_id_eq x y : 
     rtc (convert_rel (λ a b : bool, a = b)) x y → x = y.
   Proof.
     intros Hrtc.
     induction Hrtc; auto.
     inversion H3 as (b & Hb1 & Hb2 & Hb3 & Hb4). congruence.
   Qed.

   (* Lemma region_not_in W a p w : *)
   (*   p ≠ O → *)
   (*   a ↦ₐ[p] w ∗ region W -∗ ⌜(countable.encode a) ∉ dom (gset positive) (std_sta W)⌝. *)
   (* Proof. *)
   (*   iIntros (Hp) "[Ha Hr]". *)
   (*   iIntros (Hcontr). rewrite region_eq /region_def /region_map_def. *)
   (*   iDestruct "Hr" as (M) "(HM & Hdom & Hregion)". *)
   (*   iDestruct "Hdom" as %Hdom. apply elem_of_dom in Hcontr. *)
   (*   destruct Hdom with (countable.encode a) as [Hdom1 Hdom2]. *)
   (*   specialize (Hdom1 Hcontr) as [a' [Heq [x Hx] ] ]. *)
   (*   apply encode_inj in Heq; subst. *)
   (*   iDestruct (big_sepM_delete _ _ a with "Hregion") as "[Ha' Hr]"; eauto.  *)
   (*   iDestruct "Ha'" as (ρ) "[Hstate Ha']". *)
   (*   destruct ρ. *)
   (*   - iDestruct "Ha'" as (γpred v p0 φ Heq Ho) "[Ha' _]".  *)
   (*     iDestruct (cap_duplicate_false with "[$Ha $Ha']") as "Hcontr"; auto.  *)
   (*   - iDestruct "Ha'" as (γpred v p0 φ Heq Ho) "[Ha' _]".  *)
   (*     iDestruct (cap_duplicate_false with "[$Ha $Ha']") as "Hcontr"; auto. *)
   (*   - if the location is revoked, there is no contradiction. *)

       
  (* We want to show a spec that relies on well bracketed control flow. Thus we want
     to be able to show that if f3 halts in HaltedV configuration, then the flag was 
     not changed. We will therefore keep the flag state in an invarariant *)
  (* to make the proof simpler, we are assuming WLOG the r1 registers is r_t30 *)
  Lemma f3_spec W b e a pc_p pc_g pc_b pc_e :
    (* r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 → *)
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a-0)) ∧
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a-199)) →

    {{{ r_stk ↦ᵣ inr ((RWLX,Local),a-200,a-250,a-199)
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r_t30]; wsr,
           r_i ↦ᵣ w_i)
      ∗ (∃ ws, [[a-200, a-250]]↦ₐ[RWLX][[ws]]) 
      ∗ ⌜Forall (λ a, (countable.encode a) ∉ dom (gset positive) (std_sta W)
                      ∧ (countable.encode a) ∉ dom (gset positive) (std_rel W)) (region_addrs (a-200) (a-250))⌝
      (* TODO: the above stack should be represented by a read write condition.
         Difficulties with this approach: we will need to close the region when shifting control. 
         At that point we lose the ability to reason about local state: all the local state we 
         have must be put into the region!
         
         Alternatively, allocating the invariant in the proof will require us to 
         assume that the addresses are not in the domain of W (or in some ways prove this). This will then 
         enable us to allocate the adversarial stack. 
       *)
      (* flag *)
      ∗ a-179 ↦ₐ[RW] inl 0%Z
      (* token which states all invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv *)
      ∗ r_t30 ↦ᵣ inr ((E,Global),b,e,a)
      ∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                                        ∧ ⌜region_state_nwl W a Global⌝
                                        ∧ ⌜region_std W a⌝)
      (* trusted *)
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a-0)
      ∗ f3 r_t30 pc_p
      (* we start out with arbitrary sts *)
      ∗ sts_full_world sts_std W
      ∗ region W
    }}}
      Seq (Instr Executable)
    {{{ v, RET v; ⌜v = HaltedV⌝ → a-179 ↦ₐ[RW] inl 0%Z }}}.
  Proof. 
    iIntros ([Hvpc1 Hvpc2] φ)
    "(Hr_stk & Hr & Hstack & Hfresh & Hflag & Hna & Hr_t30 & #Hadv & HPC & Hprog & Hsts & Hex) Hφ".
    iDestruct "Hr" as (wsr) "Hr_gen".
    iDestruct "Hfresh" as %Hfresh. 
    (* rewrite /all_registers /r_stk. iSimpl in "Hr_gen".  *)
    (* get_genpur_reg "Hr_gen" wsr "[Hrt0 Hr_gen]". *)
    (* get_genpur_reg "Hr_gen" wsr "[Hrt1 Hr_gen]". *)
    (* get_genpur_reg "Hr_gen" wsr "[Hrt2 Hr_gen]".  *)
    (* (* prepare the stack by opening the region *) *)
    (* iDestruct (region_prepare with "Hex") as "Hex". *)
    (* iDestruct (region_addrs_open with "Hex Hsts Hstack") as "(Hstack & Hr & Hsts)"; *)
    (*   eauto;[by apply disjoint_nil_r|]. rewrite app_nil_r.  *)
    (* assert ((a-200 ≤ a-209)%Z ∧ (a-209 < a-250)%Z) as Hsplit; first (simpl; lia). *)
    (* assert (region_addrs (a-200) (a-250) = region_addrs (a-200) (a-209) ++ region_addrs (a-210) (a-250)) as Hstack_split. *)
    (* { rewrite (region_addrs_decomposition (a-200) (a-209) (a-250)). *)
    (*   - assert ((a-209 + 1)%a = Some (a-210)) as ->;[addr_succ|]. rewrite cons_middle app_assoc. *)
    (*     f_equiv. assert ((a-209 + -1)%a = Some (a-208)) as ->;[addr_succ|]. *)
    (*     rewrite /get_addr_from_option_addr. rewrite (region_addrs_decomposition (a-200) (a-209) (a-209)); auto. *)
    (*     split; rewrite /le_addr; lia.  *)
    (*   - destruct Hsplit as [Hle Hgt]. split;auto.  *)
    (* } *)
    (* rewrite Hstack_split. *)
    (* iDestruct (big_sepL_app with "Hstack") as "[Hstack_own Hstack_adv]". *)
    (* iDestruct (region_addrs_exists with "Hstack_own") as (ws_own) "Hstack_own".  *)
    (* iDestruct (big_sepL2_sep with "Hstack_own") as "[Hstack_own _]". *)
    (* iDestruct (big_sepL2_length with "Hstack_own") as %Hlength. *)
    (* apply eq_sym in Hlength. simpl in Hlength.  *)
    (* assert (region_addrs (a-200) (a-209) = *)
    (*         [a-200;a-201;a-202;a-203;a-204;a-205;a-206;a-207;a-208;a-209]) *)
    (*   as ->. *)
    (* { rewrite /region_addrs.  *)
    (*   simpl. repeat f_equal; (apply eq_proofs_unicity; decide equality). } *)
    rewrite /all_registers /r_stk /=.
    get_genpur_reg "Hr_gen" wsr "[Hrt0 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt1 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt2 Hr_gen]". 
    iDestruct "Hstack" as (ws) "Hstack". 
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 10)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { simpl in Hlength.
      do 10 (destruct ws as [|? ws]; inversion Hlength).
        by exists [w;w0;w1;w2;w3;w4;w5;w6;w7;w8],ws. }
    assert ((a-200 ≤ a-209)%Z ∧ (a-209 < a-250)%Z); first (simpl; lia).  
    rewrite Happ (stack_split (a-200) (a-250) (a-209) (a-210)); auto; try addr_succ.
    simpl in Hlength. 
    iDestruct "Hstack" as "[Hstack_own Hstack_adv]".
    rewrite /region_mapsto.
    assert (region_addrs (a-200) (a-209) =
            [a-200;a-201;a-202;a-203;a-204;a-205;a-206;a-207;a-208;a-209])
      as ->.
    { rewrite /region_addrs. 
      simpl. repeat f_equal; (apply eq_proofs_unicity; decide equality). }
    wp_push_z "Hstack_own" (a-0) (a-199) (a-200) (a-250) (a-199) (a-200) φ
              (a-0) (a-1) (a-2) ws_own "Hprog" "(HPC & _ & Hr_stk & Ha200)".
    wp_push_r "Hstack" (a-0) (a-199) (a-200) (a-250) (a-200) (a-201) φ
              (a-2) (a-3) (a-4) ws_own "Hf3" "(HPC & _ & Hr_stk & Hr_t30 & Ha201)".
    wp_push_z "Hstack" (a-0) (a-199) (a-200) (a-250) (a-201) (a-202) φ
              (a-4) (a-5) (a-6) ws_own "Hf3" "(HPC & _ & Hr_stk & Ha202)".
    wp_push_z "Hstack" (a-0) (a-199) (a-200) (a-250) (a-202) (a-203) φ
              (a-6) (a-7) (a-8) ws_own "Hf3" "(HPC & _ & Hr_stk & Ha203)".
    wp_push_z "Hstack" (a-0) (a-199) (a-200) (a-250) (a-203) (a-204) φ
              (a-8) (a-9) (a-10) ws_own "Hf3" "(HPC & _ & Hr_stk & Ha204)".
    wp_push_z "Hstack" (a-0) (a-199) (a-200) (a-250) (a-204) (a-205) φ
              (a-10) (a-11) (a-12) ws_own "Hf3" "(HPC & _ & Hr_stk & Ha205)".
    wp_push_z "Hstack" (a-0) (a-199) (a-200) (a-250) (a-205) (a-206) φ
              (a-12) (a-13) (a-14) ws_own "Hf3" "(HPC & _ & Hr_stk & Ha206)".
    wp_push_z "Hstack" (a-0) (a-199) (a-200) (a-250) (a-206) (a-207) φ
              (a-14) (a-15) (a-16) ws_own "Hf3" "(HPC & _ & Hr_stk & Ha207)".
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ (a-16) (a-17) _ r_t1
              with "[Hi Hrt1 HPC]"); eauto; try addr_succ;
      first apply move_r_i; first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hr_t1)". iSimpl.
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply wp_pure_step_later;auto;iNext. 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ (a-17) (a-18) _ r_t1 pc_p _ _ _ (a-16) 64 (a-80)
              with "[Hi Hr_t1 HPC]"); eauto; try addr_succ;
      first apply lea_z_i; first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    { inversion Hvpc1 as [ ?????? Hpc_p ];
        destruct Hpc_p as [Hpc_p | [Hpc_p | Hpc_p] ]; congruence. }
    iFrame. iNext. iIntros "(HPC & _ & Hrt_1)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext. 
    wp_push_r "Hstack" (a-0) (a-199) (a-200) (a-250) (a-207) (a-208) φ
              (a-18) (a-19) (a-20) ws_own "Hf3" "(HPC & _ & Hr_stk & Hr_t1 & Ha208)".
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ (a-20) (a-21) _ r_stk RWLX _ _ _ (a-208) 1 (a-209)
              with "[Hi Hr_stk HPC]"); eauto; try addr_succ;
      first apply lea_z_i; first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hr_stk)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    destruct ws_own as [_ | wa209 ws_own]; first inversion Hlength';
      iDestruct "Hstack" as "[Ha209 Hstack]".
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_reg_same _ _ _ _ _ (a-21) (a-22) _ r_stk _ RWLX
                                 Local (a-200) (a-250) (a-209)
              with "[HPC Hi Hr_stk Ha209]"); eauto; try addr_succ;
      first apply store_r_i; try apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hr_stk & Ha209)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext. 
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_move_success_reg _ _ _ _ _ (a-22) (a-23) _ r_t0 _ r_stk
              with "[HPC Hi Hrt0 Hr_stk]"); eauto; try addr_succ;
      first apply move_r_i; first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hrt0 & Hr_stk)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ (a-23) (a-24) _ r_t0 RWLX _ _ _ (a-209) (-7)%Z (a-202) 
              with "[Hi Hrt0 HPC]"); eauto; try addr_succ;
      first apply lea_z_i;first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hrt0)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_restrict_success_z _ _ _ _ _ (a-24) (a-25) _ r_t0 RWLX Local
                                  (a-200) (a-250) (a-202)
        local_e with "[Hi HPC Hrt0]"); eauto; try addr_succ;
      [apply restrict_r_z|apply PermFlows_refl| | | |];
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    { rewrite epp_local_e /=. auto. }
    iFrame. iNext. iIntros "(HPC & _ & Hrt0)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_GetA_success _ r_t1 _ _ _ _ _ (a-25) _ _ _ (a-26)
              with "[Hi HPC Hr_t1 Hr_stk]"); eauto;try addr_succ;
      first apply geta_i; first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    { iFrame. iFrame. }
    destruct (reg_eq_dec PC r_stk) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_stk r_t1) as [Hcontr | _]; [inversion Hcontr|].
    iNext. iIntros "(HPC & _ & Hr_stk & Hr_t1)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success _ r_t1 _ _ _ _ (a-26) _ (inl (z_of (a-210))) _ (inl 1%Z)
           with "[Hi HPC Hr_t1]"); try addr_succ; eauto; 
      first (left;apply add_r_z_i); first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    iFrame. iSplit;[eauto|done]. iNext.
    destruct (reg_eq_dec r_t1 PC) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t1 r_t1); last contradiction.
    rewrite add_r_z_i. assert (((a-26) + 1)%a = Some (a-27)) as ->;[addr_succ|]. 
    iIntros "(HPC & _ & _ & _ & Hr_t1)";iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_GetE_success _ r_t2 _ _ _ _ _ (a-27) _ _ _ (a-28)
              with "[Hi HPC Hrt2 Hr_stk]"); eauto;try addr_succ;
      first apply gete_i; first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    iFrame. iFrame. iNext.
    destruct (reg_eq_dec PC r_stk) as [Hcontr | _];[inversion Hcontr|].
    destruct (reg_eq_dec r_stk r_t2) as [Hcontr | _];[inversion Hcontr|].
    iIntros "(HPC & _ & Hr_stk & Hr_t2)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_subseg_success _ _ _ _ _ (a-28) _ r_stk r_t1 r_t2
                              RWLX Local (a-200) (a-250) (a-209) 210 250 (a-210) (a-250)
              with "[Hi HPC Hr_stk Hr_t1 Hr_t2]");eauto;try addr_succ;
      first apply subseg_r_r_i; first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
    { assert (110 ≤ MemNum)%Z; [done|].
      assert (100 ≤ MemNum)%Z; [done|].
      rewrite /z_to_addr.
      destruct ( Z_le_dec 109%Z MemNum),(Z_le_dec 100%Z MemNum); try contradiction.
      split;
        do 2 f_equal; apply eq_proofs_unicity; decide equality. 
    }
    iFrame.
    assert ((a-28 + 1)%a = Some (a-29)) as ->; [addr_succ|]. 
    (* assert ((a150 =? -42)%a = false) as Ha10042;[done|]; rewrite Ha10042.   *)
    iNext. iIntros "(HPC & _ & Hr_t1 & Hr_t2 & Hr_stk)"; iSimpl.
    iApply wp_pure_step_later; auto;iNext. 
    (* mclear r_stk *)
    assert (list.last (region_addrs_aux (a-29) 22) = Some (a-50)).
    { cbn. cbv. do 2 f_equal. apply eq_proofs_unicity. decide equality. }
    get_genpur_reg "Hr_gen" wsr "[Hrt3 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt4 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt5 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt6 Hr_gen]".
    iDestruct "Hf3" as "[Hi Hf3]".
    iApply (mclear_spec (region_addrs_aux (a-29) 22) r_stk (a-50) (a-29) (a-35) (a-45)
                pc_p _ pc_g pc_b pc_e RWLX _ Local (a-210) (a-250) (a-209) (a-251) (a-51) 
              with "[-Hstack]"); try apply PermFlows_refl;
      try addr_succ; try assumption;[|auto|auto| | | |].  
    { apply region_addrs_aux_contiguous. simpl. cbv. done. }
    { split; [cbn; f_equal; by apply addr_unique|].
      split; [addr_succ|cbn; f_equal; by apply addr_unique].  
    }
    { apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done. }
    { apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done. }
    iFrame.
    iSplitL "Hrt4"; [iNext;iExists _;iFrame|].
    iSplitL "Hr_t1"; [iNext;iExists _;iFrame|].
    iSplitL "Hr_t2"; [iNext;iExists _;iFrame|].
    iSplitL "Hrt3"; [iNext;iExists _;iFrame|].
    iSplitL "Hrt5"; [iNext;iExists _;iFrame|].
    iSplitL "Hrt6"; [iNext;iExists _;iFrame|].
    iSplitL "Hstack_adv"; [iNext;iExists _;iFrame|]. 
    iNext. iIntros "(HPC & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6
                   & Hr_stk & Hstack_adv & _)".
    iDestruct "Hf3" as "[Hi Hf3]".
    clear H3 Hlength'.
    assert (list.last (region_addrs_aux (a-51) 29) = Some (a-79)).
    { cbn. cbv. do 2 f_equal. apply eq_proofs_unicity. decide equality. }
    iApply (rclear_spec (region_addrs_aux (a-51) 29)
                        (list_difference all_registers [PC; r_stk; r_t0; r_t30])
                        _ _ _ _ _ (a-51) (a-79) (a-80) with "[-]");
      try addr_succ; try assumption; try apply PermFlows_refl; auto. 
    { apply region_addrs_aux_contiguous. simpl. cbv. done. }
    { apply not_elem_of_list, elem_of_list_here. }
    { split; (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done). }
    iSplitL "Hr_t1 Hr_t2 Hr_t3 Hr_t4 Hr_t5 Hr_t6 Hr_gen". 
    { iNext. iExists ((repeat (inl 0%Z) 6) ++ wsr); iSimpl. iFrame. }
    iSplitL "HPC";[iFrame|].
    iSplitL "Hi";[iExact "Hi"|].
    iNext. iIntros "(HPC & Hr_gen & _)".
    iPrologue "Hf3".
    iApply (wp_jmp_success _ _ _ _ _ (a-80) with "[Hi HPC Hr_t30]");
      first apply jmp_i;first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done). 
    iFrame. iEpilogue "(HPC & _ & Hr1)"; iSimpl in "HPC".
    (* We have now arrived at the interesting part of the proof: namely the unknown 
       adversary code. In order to reason about unknown code, we must apply the 
       fundamental theorem. To this purpose, we must first define the stsf that will 
       describe the behavior of the memory. This time since we are doing two calls, 
       we want to do slightly more fancy STS:  
            true --------> false       where --> is a private transition
     *)
    iMod (sts_alloc_loc W true (λ a b, a = b) (λ a b, a = true ∨ b = false) with "Hsts")
      as (i) "(Hsts & % & % & Hstate & #Hrel)".
    (* We can now allocate the invariant for the local state 
       (note the two possible states): *)
    iMod (na_inv_alloc logrel_nais ⊤ (regN.@(a-200, a-209))
                       (∃ x:bool, sts_state_loc i x
                       ∗ if x then 
                           (a-200 ↦ₐ[RWLX] inl 1%Z
                          ∗ a-201 ↦ₐ[RWLX] inr (cap_lang.E, Global, b, e, a)
                          ∗ a-202 ↦ₐ[RWLX] inl w_1
                          ∗ a-203 ↦ₐ[RWLX] inl w_2
                          ∗ a-204 ↦ₐ[RWLX] inl w_3
                          ∗ a-205 ↦ₐ[RWLX] inl w_4a
                          ∗ a-206 ↦ₐ[RWLX] inl w_4b
                          ∗ a-207 ↦ₐ[RWLX] inl w_4c
                          ∗ a-208 ↦ₐ[RWLX] inr (pc_p, pc_g, pc_b, pc_e, a-80)
                          ∗ a-209 ↦ₐ[RWLX] inr (RWLX, Local, a-200, a-250, a-209))
                         else
                           (a-200 ↦ₐ[RWLX] inl 2%Z
                          ∗ a-201 ↦ₐ[RWLX] inl w_1
                          ∗ a-202 ↦ₐ[RWLX] inl w_2
                          ∗ a-203 ↦ₐ[RWLX] inl w_3
                          ∗ a-204 ↦ₐ[RWLX] inl w_4a
                          ∗ a-205 ↦ₐ[RWLX] inl w_4b
                          ∗ a-206 ↦ₐ[RWLX] inl w_4c
                          ∗ a-207 ↦ₐ[RWLX] inr (pc_p, pc_g, pc_b, pc_e, (a-171))
                          ∗ a-208 ↦ₐ[RWLX] inr (RWLX, Local, a-200, a-250, a-208))
                       )%I
            with "[Hstate Ha200 Ha201 Ha202 Ha203 Ha204 Ha205 Ha206 Ha207 Ha208 Ha209]")
      as "#Hlocal".
    { iNext. iExists (true). iFrame. }
    (* We also allocate the rest of the program into an invariant *)
    iMod (na_inv_alloc logrel_nais ⊤ (regN.@(a-81,a-176)) with "Hprog") as "#Hprog".
    (* Next we update the monotone world monoid to the same future state *)
    assert (related_sts_pub_world W (W.1,(<[i:=countable.encode true]> W.2.1,
                                     <[i:=(convert_rel (λ a0 b0 : bool, a0 = b0),
                                            convert_rel (λ a0 b0 : bool, (a0 = true ∨ b0 = false)%type))]> W.2.2))) as Hrelated.
    { destruct W as [Wstd [Wloc_sta Wloc_rel] ]. split; [apply related_sts_pub_refl|simpl]. 
      split; [apply dom_insert_subseteq|split;[apply dom_insert_subseteq|] ].
      intros i0 r1 r2 r1' r2' Hr Hr'.
      destruct (decide (i = i0)).
      + subst. simpl in H6. apply not_elem_of_dom in H6.
        rewrite H6 in Hr. inversion Hr.
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr' in Hr; inversion Hr. repeat (split;auto). 
        intros x y Hx Hy. rewrite lookup_insert_ne in Hy; auto. 
        rewrite Hx in Hy. inversion Hy. left. 
    }
    iDestruct (region_monotone $! _ Hrelated
                 with "Hex") as "Hr". Unshelve. 2: { rewrite /std_sta /=. auto. }
    (* We allocate a revoked region for the stack that will be passed to adversary at call #2 *)
    assert (a-209 ∈ region_addrs (a-200) (a-250)) as Hin209.
    { apply elem_of_list_In. apply nth_error_In with 9.
      assert (a-209 = get_addr_from_option_addr ((a-200) + 9)%a) as ->; auto.
      simpl; f_equiv. apply eq_proofs_unicity; decide equality. }
    iMod (extend_region_revoked _ _ (a-209) RWLX (λ Wv, interp Wv.1 Wv.2) with "Hsts Hr") as "(Hsts & #Hrel209 & Hr)".
    (* TODO: make some lemma for the following two *)
    { revert Hfresh. rewrite list.Forall_forall =>Hfresh.
      destruct Hfresh with (a-209) as [Hfresh209 _]; auto. }
    { revert Hfresh. rewrite list.Forall_forall =>Hfresh.
      destruct Hfresh with (a-209) as [_ Hfresh209]; auto. }
    (* We create the necessary invariant for the adv stack *)
    iAssert (|={⊤}=> ([∗ list] a0 ∈ region_addrs (a-210) (a-250),
                     read_write_cond a0 RWLX (fixpoint interp1)) ∗ region _ ∗ sts_full_world sts_std _)%I
                                           with "[Hstack_adv Hr Hsts]" as ">(#Hstack_adv & Hr & Hsts)". 
    { iApply region_addrs_zeroes_alloc; auto; [|iFrame]. rewrite /std_sta /std_rel /=.
      rewrite (region_addrs_decomposition _ (a-210) _) in Hfresh.
      - apply Forall_app in Hfresh as [_ Hfresh].
        apply std_update_multiple_dom_insert; auto. 
        rewrite /lt_addr /=; lia. 
      - split; rewrite /le_addr /=; lia. 
    }
    (* We choose the r *)
    evar (r : gmap RegName Word).
    instantiate (r := <[PC    := inl 0%Z]>
                     (<[r_stk := inr (RWLX, Local, a-210, a-250, a-209)]>
                     (<[r_t0  := inr (E, Local, a-200, a-250, a-202)]>
                     (<[r_t30 := inr (E, Global, b, e, a)]>
                     (create_gmap_default
                        (list_difference all_registers [PC; r_stk; r_t0; r_t30]) (inl 0%Z)))))).
    (* Helper Lemma for later *)
    assert (∀ r1, r1 ≠ r_stk → r1 ≠ PC → r1 ≠ r_t0 → r1 ≠ r_t30 →
                  r !r! r1 = inl 0%Z) as Hr1.
    { intros r1 Hr_stk HPC Hr_t0 Hr_t30. rewrite /RegLocate.
      destruct (r !! r1) eqn:Hsome; rewrite Hsome; last done.
      do 4 (rewrite lookup_insert_ne in Hsome;auto).
      assert (Some w = Some (inl 0%Z)) as Heq.
      { rewrite -Hsome. apply create_gmap_default_lookup.
        apply elem_of_list_difference. split; first apply all_registers_correct.
        repeat (apply not_elem_of_cons;split;auto).
        apply not_elem_of_nil. 
      }
        by inversion Heq. 
    }
    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r))
                          with "[Hr_gen Hr_stk Hrt0 Hr1 HPC]" as "Hmaps".
    { rewrite /r /registers_mapsto (insert_insert _ PC).
      iApply (big_sepM_insert_2 with "[HPC]"); first iFrame.
      iApply (big_sepM_insert_2 with "[Hr_stk]"); first iFrame.
      iApply (big_sepM_insert_2 with "[Hrt0]"); first (rewrite epp_local_e;iFrame).
      iApply (big_sepM_insert_2 with "[Hr1]"); first iFrame.
      assert ((list_difference all_registers [PC; r_stk; r_t0; r_t30]) =
              [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12;
               r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24;
               r_t25; r_t26; r_t27; r_t28; r_t29]) as ->; first auto. 
      rewrite /create_gmap_default. iSimpl in "Hr_gen". 
      repeat (iDestruct "Hr_gen" as "[Hr Hr_gen]";
              iApply (big_sepM_insert_2 with "[Hr]"); first iFrame).
      done. 
    }
    (* r contrains all registers *)
    iAssert (full_map r) as "#full".
    { iIntros (r0).
      iPureIntro.
      assert (r0 ∈ all_registers); [apply all_registers_correct|].
      destruct (decide (r0 = PC)); [subst;rewrite lookup_insert; eauto|]. 
      rewrite lookup_insert_ne;auto.
      destruct (decide (r0 = r_stk)); [subst;rewrite lookup_insert; eauto|]. 
      rewrite lookup_insert_ne;auto.
      destruct (decide (r0 = r_t0)); [subst;rewrite lookup_insert; eauto|]. 
      rewrite lookup_insert_ne;auto.
      destruct (decide (r0 = r_t30)); [subst;rewrite lookup_insert; eauto|].
      rewrite lookup_insert_ne;auto.
      assert (¬ r0 ∈ [PC; r_stk; r_t0; r_t30]).
      { repeat (apply not_elem_of_cons; split; auto). apply not_elem_of_nil. }
      exists (inl 0%Z).
      apply create_gmap_default_lookup. apply elem_of_list_difference. auto.
    }
    (* W' is the notation for the current world, where the standard STS has been extended with adv stack, 
       and the local STS has been extended with i*)
    evar (W_loc : prod STS_states STS_rels). 
    instantiate (W_loc := (<[i:=countable.encode true]> W.2.1,
               <[i:=(convert_rel (λ a0 b0 : bool, a0 = b0), convert_rel (λ a0 b0 : bool, (a0 = true ∨ b0 = false)%type))]> W.2.2)).  
    evar (W' : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
    instantiate (W' :=
     (std_update_temp_multiple
              (std_update
                 (W.1,
                 (<[i:=countable.encode true]> W.2.1,
                 <[i:=(convert_rel (λ a0 b0 : bool, a0 = b0), convert_rel (λ a0 b0 : bool, (a0 = true ∨ b0 = false)%type))]> W.2.2))
                 (a-209) Revoked (Rpub, Rpriv).1 (Rpub, Rpriv).2) (region_addrs (a-210) (a-250)))).
    iAssert (region W') with "Hr" as "Hr". iAssert (sts_full_world sts_std W') with "Hsts" as "Hsts".
    (* We must show that W' is a public future world of W to conclude that the adv program remains valid *)
    assert (related_sts_pub_world (W.1,W_loc) W') as Hrelated'.
    { rewrite /W' /W_loc.
      eapply related_sts_pub_trans_world; 
      [|apply related_sts_pub_update_temp_multiple;[apply region_addrs_NoDup|] ].
      - apply related_sts_pub_world_fresh. 
        + rewrite /std_sta /=. revert Hfresh. rewrite list.Forall_forall =>Hfresh.
          destruct Hfresh with (a-209) as [Hfresh209 _]; auto.
        + rewrite /std_sta /=. revert Hfresh. rewrite list.Forall_forall =>Hfresh.
          destruct Hfresh with (a-209) as [_ Hfresh209]; auto.
      - rewrite (region_addrs_decomposition _ (a-210) _) in Hfresh.
        + apply Forall_app in Hfresh as [_ Hfresh].
          apply std_update_multiple_dom_insert; auto.
          rewrite /lt_addr /=; lia. 
        + split; rewrite /le_addr /=; lia. 
    }
    assert (related_sts_pub_world W W') as HrelatedWW'.
    { eapply related_sts_pub_trans_world;[|apply Hrelated'].
      split;[apply related_sts_pub_refl|apply Hrelated]. 
    }
    (* We instantiate the fundamental theorem on the adversary region *)
    iAssert (interp_expression r W' (inr (RX, Global, b, e, a)))
      as "Hvalid". 
    { iApply fundamental. iLeft; auto. iExists RX. assert (pwl RX = false) as ->;[auto|].
      iSplit; auto. iApply (big_sepL_mono with "Hadv"). iIntros (k y _) "(Hr & Hstd & Hsta)". iFrame.
      iDestruct "Hstd" as %Hstd. iDestruct "Hsta" as %Hsta.
      iPureIntro. split. 
      - apply related_sts_rel_std with W; auto. by apply related_sts_pub_priv_world.
      - apply region_state_nwl_monotone with W; auto. 
    }
    (* We are now ready to show that all registers point to a valid word *)
    (* instantiate (W' := (<[i:=countable.encode true]> W.1, *)
    (*        <[i:=(convert_rel (λ a0 b0 : bool, a0 = b0), convert_rel (λ a0 b0 : bool, (a0 = true ∨ b0 = false)%type))]> W.2)). *)
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W' (r !r! r1))%I
      with "[-Hsts Hr Hmaps Hvalid Hna Hφ Hflag]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_t30 ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_t30)).
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_t30)); [by left|right;auto].  
      }
      destruct H7 as [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      - iIntros "%". contradiction.
      - assert (r !! r_stk = Some (inr (RWLX, Local, a-210, a-250, a-209))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk fixpoint_interp1_eq. 
        iIntros (_). iExists RWLX. iSplitR; [auto|].
        iSplitL "Hstack_adv".
        { iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Helem) "Hr". iFrame.
          iPureIntro. by apply std_update_temp_multiple_lookup with k. }
        iAlways.
        rewrite /exec_cond.
        iIntros (a0 r' W'' Ha0 Hrelated0). iNext.
        iApply fundamental.
        + iRight. iRight. done.
        + iExists RWLX. iSplit; auto.
          iApply (big_sepL_mono with "Hstack_adv").
          iIntros (k y Hsome) "Hr".
          iFrame. iPureIntro.
          eapply std_update_temp_multiple_lookup (* with W _ _ _  *)in Hsome as [Hpwl Hstd]. 
          split.
          ++ apply related_sts_rel_std with W'; auto. apply related_sts_pub_priv_world; auto. apply Hstd. 
          ++ simpl. apply region_state_pwl_monotone with W'; auto. 
      - (* continuation *)
        iIntros (_). 
        assert (r !! r_t0 = Some (inr (E, Local, a-200, a-250, a-202))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 fixpoint_interp1_eq. iSimpl. 
        (* prove continuation *)
        iAlways.
        rewrite /enter_cond.
        iIntros (r' W'' Hrelated'').
        iNext. iSimpl. 
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hex & Hsts & Hna)". 
        iSplit; [auto|rewrite /interp_conf].
        (* we know that W'' is public
           future world of the sts previously defined *)
        (* This is the key to the proof! We will now be able to know that the state at 
           i must be true, from which we get the correct local state to be able to prove 
           the continuation. *)
         (* get the PC, currently pointing to the activation record *)
        iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']".
        { rewrite lookup_insert; eauto. }
        (* get some general purpose registers *)
        iAssert (⌜∃ wr_t1, r' !! r_t1 = Some wr_t1⌝)%I as %[rt1w Hrt1];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t1 with "Hmreg'") as "[Hr_t1 Hmreg']".
        { rewrite lookup_delete_ne; auto.
          rewrite lookup_insert_ne; eauto. }
        iAssert (⌜∃ wr_t1, r' !! r_t2 = Some wr_t1⌝)%I as %[rt2w Hrt2];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t2 with "Hmreg'") as "[Hr_t2 Hmreg']".
        { rewrite lookup_delete_ne; auto.
          rewrite lookup_delete_ne; auto. 
          rewrite lookup_insert_ne; eauto. }
        iAssert (⌜∃ wr_t0, r' !! r_t0 = Some wr_t0⌝)%I as %[rt0w Hrt0];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t0 with "Hmreg'") as "[Hr_t0 Hmreg']".
        { do 3 (rewrite lookup_delete_ne; auto). 
          rewrite lookup_insert_ne; eauto. }
        (* get r_stk *)
        iAssert (⌜∃ wr_stk, r' !! r_stk = Some wr_stk⌝)%I as %[rstkw Hrstk];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_stk with "Hmreg'") as "[Hr_stk Hmreg']".
        { do 4 (rewrite lookup_delete_ne; auto).
          rewrite lookup_insert_ne; eauto. }
        (* get r_t30 *)
        iAssert (⌜∃ wr30, r' !! r_t30 = Some wr30⌝)%I as %[wr30 Hr30];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t30 with "Hmreg'") as "[Hr_t30 Hmreg']".
        { do 5 (rewrite lookup_delete_ne; auto).
          rewrite lookup_insert_ne; eauto. }
        (* We start by opening the invariant for the program *)
        iMod (na_inv_acc logrel_nais ⊤ ⊤
                          (regN.@(a-81, a-176)) with "Hprog Hna")
          as "(>Hf3 & Hna & Hcls')"; auto. 
        (* open the na invariant for the local stack content *)
        iMod (na_inv_acc logrel_nais ⊤ (⊤ ∖ ↑regN.@(a-81, a-176))
                          (regN.@(a-200, a-209)) with "Hlocal Hna")
          as "(Hstack & Hna & Hcls)"; [auto|solve_ndisj|].
        (* assert that the state of i is true *)
        rewrite bi.later_exist. iDestruct "Hstack" as (x) "Hstack".
        destruct x.
        2: { (* by the future world relation, we will get a contradiction *)
          iDestruct "Hstack" as "(>Hstate & >Ha200 & >Ha201 & >Ha202 & >Ha203 & >Ha204
                              & >Ha205 & >Ha206 & >Ha207 & >Ha208)".
          iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hi.
          iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hir. 
          exfalso. destruct Hrelated'' as [_ [_ [_ Hrelated''] ] ].
          destruct (Hrelated'' i (convert_rel (λ a b : bool, a = b)) (convert_rel (λ a b : bool, a = true ∨ b = false))
                               (convert_rel (λ a b : bool, a = b)) (convert_rel (λ a b : bool, a = true ∨ b = false)))
            as [Heq1 [Heq2 Hrtc] ]; auto;[by rewrite /W' lookup_insert|].
          apply rtc_id_eq with (countable.encode true) (countable.encode false) in Hrtc;[done| |auto].
          by rewrite /W' lookup_insert. 
        }
        iDestruct "Hstack" as "(>Hstate & >Ha200 & >Ha201 & >Ha202 & >Ha203 & >Ha204
                              & >Ha205 & >Ha206 & >Ha207 & >Ha208 & >Ha209)".
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hi.
        assert (PermFlows RX RWLX) as Hrx;[by rewrite /PermFlows /=|]. 
        (* step through instructions in activation record *)
        (* move rt_1 PC *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_move_success_reg_fromPC _ RX Local (a-200) (a-250) (a-202) (a-203) (inl w_1)
               with "[HPC Ha202 Hr_t1]");
          [rewrite -i_1; apply decode_encode_inv|eauto
           |constructor; auto; split; done|
           addr_succ|
           auto|iFrame|]. 
        iEpilogue "(HPC & Ha202 & Hr_t1)".
        (* lea r_t1 7 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_z _ RX Local (a-200) (a-250) (a-203) (a-204) (inl w_2)
                                 _ RX _ _ _ (a-202) 7 (a-209) with "[HPC Ha203 Hr_t1]");
          try addr_succ;
          first (rewrite -i_2; apply decode_encode_inv);
          [eauto|(constructor; auto; split; done); auto|auto|auto|iFrame|].
        iEpilogue "(HPC & Ha203 & Hr_t1)".
        (* load r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_load_success _ _ _ RX Local (a-200) (a-250) (a-204) (inl w_3) _ _ RX Local (a-200) (a-250) (a-209) (a-205)
                  with "[HPC Ha209 Hr_t1 Hr_stk Ha204]");
         try addr_succ;
         first (rewrite -i_3; apply decode_encode_inv);
         [eauto|eauto|(constructor; auto; split; done)|auto|auto|iFrame|].
        iEpilogue "(HPC & Hr_stk & Ha204 & Hr_t1 & Ha209)".
        destruct (a- 209 =? a- 204)%a eqn:Hcontr; [inversion Hcontr|clear Hcontr]. 
        (* sub r_t1 0 1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_add_sub_lt_success _ r_t1 _ _ (a-200) (a-250) (a-205) (inl w_4a)
                  with "[HPC Hr_t1 Ha205]");
          try addr_succ;
          first (right; left; rewrite -i_4a; apply decode_encode_inv);
          [apply Hrx|constructor; auto; split; done| | ]. 
        iFrame. iSplit; auto.
        destruct (reg_eq_dec r_t1 PC) eqn:Hcontr;[inversion Hcontr|clear Hcontr].
        assert ((a-205 + 1)%a = Some (a-206)) as ->; [addr_succ|].
        rewrite -i_4a decode_encode_inv.
        iEpilogue "(HPC & Ha205 & _ & _ & Hr_t1)".
        (* Lea r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_reg _ RX Local (a-200) (a-250) (a-206) (a-207) (inl w_4b) _ _ RWLX Local (a-200) (a-250) (a-209) (-1) (a-208)
                  with "[HPC Hr_t1 Hr_stk Ha206]");
          try addr_succ;
          first (rewrite -i_4b; apply decode_encode_inv); first apply Hrx; 
          first (constructor; auto; split; done); auto.
        iFrame. iEpilogue "(HPC & Ha206 & Hr_t1 & Hr_stk)".
        (* Load PC r_t1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_load_success_PC _ r_stk RX Local (a-200) (a-250) (a-207) (inl w_4c) RWLX Local (a-200) (a-250) (a-208)
                                   _ _ _ _ (a-80) (a-81)
                  with "[HPC Hr_stk Ha207 Ha208]");
          try addr_succ;
          first (rewrite -i_4c; apply decode_encode_inv);
          first apply Hrx; first apply PermFlows_refl;
          first (constructor; auto; split; done); auto.
        iFrame. iEpilogue "(HPC & Ha126 & Hr_stk & Ha208)".
        (* We now continue execution of f3 *)
        (* sub r_t1 0 7 *)
        iDestruct "Hf3" as "[Ha81 Hf3]". 
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_add_sub_lt_success _ r_t1 _ _ _ _ (a-81)
                  with "[HPC Hr_t1 Ha81]");
          first (right; left; apply sub_z_z_i); first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); auto. 
        iFrame. iSplit; auto.
        destruct (reg_eq_dec r_t1 PC) eqn:Hcontr;[inversion Hcontr|clear Hcontr].
        assert ((a-81 + 1)%a = Some (a-82)) as ->; [addr_succ|].
        rewrite sub_z_z_i.
        iEpilogue "(HPC & Ha81 & _ & _ & Hr_t1)".
        (* lea r_stk r_t1 *)
        iDestruct "Hf3" as "[Ha82 Hf3]". 
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_lea_success_reg _ _ _ _ _ (a-82) (a-83) _ r_stk r_t1 RWLX _ _ _
                                   (a-208) (-7)%Z (a-201)
                  with "[HPC Hr_t1 Hr_stk Ha82]");
          try addr_succ;
          first apply lea_r_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); auto. 
        iFrame. iEpilogue "(HPC & Ha82 & Hr_t1 & Hr_stk)".
        (* pop r_stk r_t30 *)
        iDestruct "Hf3" as "[Ha83 Hf3]".
        iApply (pop_spec (a-83) (a-84) (a-85) (a-86) r_t30 _ _ _ _ _ _ _ _
                         (a-200) (a-250) (a-201) (a-200) with
                    "[-]");
          first (split;[|split]);
          try (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; auto. 
        iFrame.
        destruct (a- 201 =? a- 83)%a eqn:Hcontr;[inversion Hcontr|clear Hcontr].
        iNext. iIntros "(HPC & Ha83 & Hr_t30 & Ha201 & Hr_stk & Hr_t1)".
        (* load r_t30 r_stk *)
        iDestruct "Hf3" as "[Ha86 Hf3]". 
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_load_success _ r_t2 _ _ _ _ _ (a-86) _ _ _ RWLX Local
                                (a-200) (a-250) (a-200) (a-87)
                  with "[HPC Ha86 Ha200 Hr_t2 Hr_stk]");
          try addr_succ;
          first apply load_r_i; try apply PermFlows_refl; 
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); auto.
        iFrame.
        iEpilogue "(HPC & Hr_t2 & Ha86 & Hr_stk & Ha200)"; iSimpl.  
        (* we will now make the assertion that r_t30 points to 1 *)
        (* sub r_t1 0 1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iDestruct "Hf3" as "[Ha87 Hf3]". 
        iApply (wp_add_sub_lt_success _ r_t1 _ _ _ _ (a-87)
                  with "[HPC Hr_t1 Ha87]");
          first (right; left; apply sub_z_z_i); first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); auto. 
        iFrame. iSplit; eauto.
        destruct (reg_eq_dec r_t1 PC) eqn:Hcontr;[inversion Hcontr|clear Hcontr].
        assert ((a-87 + 1)%a = Some (a-88)) as ->; [addr_succ|].
        rewrite sub_z_z_i.
        iEpilogue "(HPC & Ha87 & _ & _ & Hr_t1)".
        (* lea r_stk r_t1 *)
        iDestruct "Hf3" as "[Ha88 Hf3]". 
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_lea_success_reg _ _ _ _ _ (a-88) (a-89) _ r_stk r_t1 RWLX _ _ _
                                   (a-200) (-1)%Z (a-199)
                  with "[HPC Hr_t1 Hr_stk Ha88]");
          try addr_succ;
          first apply lea_r_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); auto. 
        iFrame. iEpilogue "(HPC & Ha88 & Hr_t1 & Hr_stk)".
        (* move r_t1 PC *)
        iDestruct "Hf3" as "[Ha89 Hf3]". 
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_move_success_reg_fromPC _ _ _ _ _ (a-89) (a-90) _ r_t1
                  with "[HPC Hr_t1 Ha89]");
          try addr_succ;
          first apply move_r_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); auto. 
        iFrame. iEpilogue "(HPC & Ha89 & Hr_t1)".
        (* lea r_t1 5 *)
        iDestruct "Hf3" as "[Ha90 Hf3]".
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_lea_success_z _ _ _ _ _ (a-90) (a-91) _ r_t1 pc_p _ _ _
                                 (a-89) 83 (a-172)
               with "[HPC Ha90 Hr_t1]");
          try addr_succ;
          first apply lea_z_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); first auto. 
        { inversion Hvpc1 as [?????? Hpc_p];
            destruct Hpc_p as [Hpc_p | [Hpc_p | Hpc_p] ]; congruence. }
        iFrame. iEpilogue "(HPC & Ha85 & Hr_t1)".
        (* sub r_t2 r_t2 1 *)
        iDestruct "Hf3" as "[Ha91 Hf3]".
        destruct ((a- 200 =? a- 86)%a) eqn:Hcontr;[inversion Hcontr|clear Hcontr]. 
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_add_sub_lt_success _ r_t2 _ _ _ _ (a-91)
                  with "[HPC Ha91 Hr_t2]"); 
          first (right;left;apply sub_r_z_i); first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); auto. 
        iFrame. iSplit; auto. 
        destruct (reg_eq_dec r_t2 PC) eqn:Hcontr; [inversion Hcontr|clear Hcontr].
        assert ((a-91 + 1)%a = Some (a-92)) as ->;[addr_succ|].
        destruct (reg_eq_dec r_t2 r_t2) eqn:Hcontr;[clear Hcontr| inversion Hcontr].
        rewrite sub_r_z_i. 
        iEpilogue "(HPC & Ha91 & _ & _ & Hr_t2 )".
        (* jnz r_t1 r_t30 *)
        iDestruct "Hf3" as "[Ha92 Hf3]".
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_jnz_success_next _ r_t1 r_t2 _ _ _ _ (a-92) (a-93)
                  with "[HPC Ha92 Hr_t2]");
          try addr_succ;
          first apply jnz_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done).
        iFrame. iEpilogue "(HPC & Ha92 & Hr_t2)".
        (* we will now continue to the second call *)
        (* push 2 *)
        iDestruct "Hf3" as "[Ha93 Hf3]".
        iApply (push_z_spec (a-93) (a-94) (a-95) _ _ _ _ _ pc_b pc_e
                            (a-200) (a-250) (a-199) (a-200));
          first (split;apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; eauto.
        iFrame. iNext. iIntros "(HPC & Ha93 & Hr_stk & Ha200)".
        (* push activation record *)
        iDestruct "Hf3" as "[Ha95 Hf3]".
        iApply (push_z_spec (a-95) (a-96) (a-97) _ _ _ _ _ pc_b pc_e
                            (a-200) (a-250) (a-200) (a-201));
          first (split;apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; eauto.
        iFrame. iNext. iIntros "(HPC & Ha95 & Hr_stk & Ha201)".
        iDestruct "Hf3" as "[Ha97 Hf3]".
        iApply (push_z_spec (a-97) (a-98) (a-99) _ _ _ _ _ pc_b pc_e
                            (a-200) (a-250) (a-201) (a-202));
          first (split;apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; eauto.
        iFrame. iNext. iIntros "(HPC & Ha97 & Hr_stk & Ha202)".
        iDestruct "Hf3" as "[Ha99 Hf3]".
        iApply (push_z_spec (a-99) (a-100) (a-101) _ _ _ _ _ pc_b pc_e
                            (a-200) (a-250) (a-202) (a-203));
          first (split;apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; eauto.
        iFrame. iNext. iIntros "(HPC & Ha99 & Hr_stk & Ha203)".
        iDestruct "Hf3" as "[Ha101 Hf3]".
        iApply (push_z_spec (a-101) (a-102) (a-103) _ _ _ _ _ pc_b pc_e
                            (a-200) (a-250) (a-203) (a-204));
          first (split;apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; eauto.
        iFrame. iNext. iIntros "(HPC & Ha101 & Hr_stk & Ha204)".
        iDestruct "Hf3" as "[Ha103 Hf3]".
        iApply (push_z_spec (a-103) (a-104) (a-105) _ _ _ _ _ pc_b pc_e
                            (a-200) (a-250) (a-204) (a-205));
          first (split;apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; eauto.
        iFrame. iNext. iIntros "(HPC & Ha103 & Hr_stk & Ha205)".
        iDestruct "Hf3" as "[Ha105 Hf3]".
        iApply (push_z_spec (a-105) (a-106) (a-107) _ _ _ _ _ pc_b pc_e
                            (a-200) (a-250) (a-205) (a-206));
          first (split;apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; eauto.
        iFrame. iNext. iIntros "(HPC & Ha105 & Hr_stk & Ha206)".
        (* move r_t1 PC *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_move_success_reg_fromPC _ _ _ _ _ (a-107) (a-108) _ r_t1
                  with "[Hi Hr_t1 HPC]"); try addr_succ;
          first apply move_r_i; first apply PermFlows_refl;
            first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
            first auto. 
        iFrame. iNext. iIntros "(HPC & Ha107 & Hr_t1)". iSimpl.
        iApply wp_pure_step_later;auto;iNext.
        (* lea r_t1 64 *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_z _ _ _ _ _ (a-108) (a-109) _
                                 r_t1 pc_p _ _ _ (a-107) 64 (a-171)
                  with "[Hi Hr_t1 HPC]"); try addr_succ;
          first apply lea_z_i; first apply PermFlows_refl;
            first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
            [auto| | |]. 
        { inversion Hvpc1 as [ ?????? Hpc_p ];
            destruct Hpc_p as [Hpc_p | [Hpc_p | Hpc_p] ]; congruence. }
        iFrame. iNext. iIntros "(HPC & Ha108 & Hrt_1)"; iSimpl.
        iApply wp_pure_step_later;auto;iNext.
        (* push r_stk r_t1 *)
        iDestruct "Hf3" as "[Ha109 Hf3]".
        iApply (push_r_spec (a-109) (a-110) (a-111) _ _ _ _ _ _ pc_b pc_e
                            (a-200) (a-250) (a-206) (a-207));
          first (split;apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done);
          first apply PermFlows_refl;
          try addr_succ; eauto.
        iFrame. iNext. iIntros "(HPC & Ha109 & Hr_stk & Hr_t1 & Ha207)".
        (* lea r_stk 1 *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_z _ _ _ _ _ (a-111) (a-112) _
                                 r_stk RWLX _ _ _ (a-207) 1 (a-208)
              with "[Hi Hr_stk HPC]"); try addr_succ;
          first apply lea_z_i; first apply PermFlows_refl;
            first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done); [auto|auto|iFrame|].
        iEpilogue "(HPC & Ha111 & Hr_stk)". 
        (* store r_stk r_stk *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_store_success_reg_same _ _ _ _ _ (a-112) (a-113) _ r_stk _ RWLX
                                 Local (a-200) (a-250) (a-208)
                  with "[HPC Hi Hr_stk Ha208]"); try addr_succ;
          [apply store_r_i|apply PermFlows_refl|apply PermFlows_refl|
          (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)|
          auto|auto|auto|iFrame|].   
        iEpilogue "(HPC & Ha112 & Hr_stk & Ha208)".
        (* move r_t0 r_stk *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_move_success_reg _ _ _ _ _ (a-113) (a-114) _ r_t0 _ r_stk
                  with "[HPC Hi Hr_t0 Hr_stk]"); try addr_succ;
          [apply move_r_i|apply PermFlows_refl|
           (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)|
           auto|iFrame|].
        iEpilogue "(HPC & Ha113 & Hr_t0 & Hr_stk)". 
        (* lea r_t0 -7 *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_z _ _ _ _ _ (a-114) (a-115) _
                                 r_t0 RWLX _ _ _ (a-208) (-7)%Z (a-201) 
                  with "[Hi Hr_t0 HPC]"); try addr_succ;
          [apply lea_z_i|apply PermFlows_refl|
           (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)|
            auto|auto|iFrame|].
        iEpilogue "(HPC & Ha114 & Hr_t0)".
        (* restrict r_t0 (Local,E) *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_restrict_success_z _ _ _ _ _ (a-115) (a-116) _ r_t0 RWLX Local
                 (a-200) (a-250) (a-201) local_e with "[Hi HPC Hr_t0]");
          try addr_succ;
          [apply restrict_r_z|apply PermFlows_refl|
           (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)|
           rewrite epp_local_e /=;auto|auto|iFrame|].
        iEpilogue "(HPC & Ha115 & Hr_t0)".
        (* geta r_t1 r_stk *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_GetA_success _ r_t1 _ _ _ _ _ (a-116) _ _ _ (a-117)
                  with "[Hi HPC Hr_t1 Hr_stk]"); try addr_succ;
          [apply geta_i|apply PermFlows_refl|
           (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)|
           auto|iFrame;iFrame|]. 
        destruct (reg_eq_dec PC r_stk) as [Hcontr | _]; [inversion Hcontr|].
        destruct (reg_eq_dec r_stk r_t1) as [Hcontr | _]; [inversion Hcontr|].
        iEpilogue "(HPC & Ha116 & Hr_stk & Hr_t1)".
        (* add r_t1 r_t1 1 *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_add_sub_lt_success _ r_t1 _ _ _ _ (a-117) _
                                      (inl (z_of (a-208))) _ (inl 1%Z)
           with "[Hi HPC Hr_t1]"); try addr_succ;
          [(left;apply add_r_z_i)|apply PermFlows_refl|
           (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)|
           iFrame;iSplit;eauto|]. 
        destruct (reg_eq_dec r_t1 PC) as [Hcontr | _]; [inversion Hcontr|].
        destruct (reg_eq_dec r_t1 r_t1); last contradiction.
        rewrite add_r_z_i. assert (((a-117) + 1)%a = Some (a-118)) as ->;[addr_succ|]. 
        iEpilogue "(HPC & Ha117 & _ & _ & Hr_t1)".
        (* gete r_t2 r_stk *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_GetE_success _ r_t2 _ _ _ _ _ (a-118) _ _ _ (a-119)
              with "[Hi HPC Hr_t2 Hr_stk]"); try addr_succ;
          [apply gete_i|apply PermFlows_refl|
           (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)|
           auto|iFrame;iFrame|].
        destruct (reg_eq_dec PC r_stk) as [Hcontr | _];[inversion Hcontr|].
        destruct (reg_eq_dec r_stk r_t2) as [Hcontr | _];[inversion Hcontr|].
        iEpilogue "(HPC & Ha118 & Hr_stk & Hr_t2)".
        (* subseg r_stk r_t1 r_t2 *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_subseg_success _ _ _ _ _ (a-119) _ r_stk r_t1 r_t2
                              RWLX Local (a-200) (a-250) (a-208) 209 250 (a-209) (a-250)
              with "[Hi HPC Hr_stk Hr_t1 Hr_t2]");try addr_succ;
          [apply subseg_r_r_i|apply PermFlows_refl|
           (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)|
           |auto|auto|auto|iFrame|].
        { rewrite /z_to_addr.
          split;do 2 f_equal; apply eq_proofs_unicity; decide equality. 
        }
        assert ((a-119 + 1)%a = Some (a-120)) as ->;[addr_succ|]. 
        iEpilogue "(HPC & Ha119 & Hr_t1 & Hr_t2 & Hr_stk)".
        (* mclear *)
        assert (list.last (region_addrs_aux (a-120) 22) = Some (a-141)).
        { cbn. cbv. do 2 f_equal. apply eq_proofs_unicity. decide equality. }
        iAssert (⌜∃ wr_t3, r' !! r_t3 = Some wr_t3⌝)%I as %[rt3w Hrt3];
          [iApply "Hfull'"|].
        iDestruct (big_sepM_delete _ _ r_t3 with "Hmreg'") as "[Hr_t3 Hmreg']".
        { do 6 (rewrite lookup_delete_ne; auto). rewrite lookup_insert_ne; eauto. }
        iAssert (⌜∃ wr_t4, r' !! r_t4 = Some wr_t4⌝)%I as %[rt4w Hrt4];
          [iApply "Hfull'"|].
        iDestruct (big_sepM_delete _ _ r_t4 with "Hmreg'") as "[Hr_t4 Hmreg']".
        { do 7 (rewrite lookup_delete_ne; auto). rewrite lookup_insert_ne; eauto. }
        iAssert (⌜∃ wr_t5, r' !! r_t5 = Some wr_t5⌝)%I as %[rt5w Hrt5];
          [iApply "Hfull'"|].
        iDestruct (big_sepM_delete _ _ r_t5 with "Hmreg'") as "[Hr_t5 Hmreg']".
        { do 8 (rewrite lookup_delete_ne; auto). rewrite lookup_insert_ne; eauto. }
        iAssert (⌜∃ wr_t6, r' !! r_t6 = Some wr_t6⌝)%I as %[rt6w Hrt6];
          [iApply "Hfull'"|].
        iDestruct (big_sepM_delete _ _ r_t6 with "Hmreg'") as "[Hr_t6 Hmreg']".
        { do 9 (rewrite lookup_delete_ne; auto). rewrite lookup_insert_ne; eauto. }
        iDestruct "Hf3" as "[Hi Hf3]".
        (* open the adv stack invariants *)
        (* Stack clearing is interesting and tricky! Clearing the stack corresponds to revoking any local capabilities 
           previously given (for instance the old sp). Rather than opening the stack, we need to REVOKE the region. 
           revoking the region thus allows us to PRIVATELY update the world. 
         *)
        iDestruct (sts_full_world_std with "Hsts") as %Hstd.
        iMod (monotone_revoke_keep W'' (region_addrs (a-210) (a-250)) with "[$Hsts $Hex Hstack_adv]")
          as "(Hsts & Hex & Hstack_adv_r)".
        { apply NoDup_ListNoDup, region_addrs_NoDup. }
        { iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hr".
          rewrite /read_write_cond. iFrame. iPureIntro.
          assert (region_state_pwl W'' y) as Hlookup;[|auto].
          eapply std_update_temp_multiple_lookup in Hsome as [Hpwl Hstd']. 
          apply region_state_pwl_monotone with W'; eauto.
        }
        do 2 iDestruct (big_sepL_sep with "Hstack_adv_r") as "[Hstack_adv_r _]".
        iApply (mclear_spec (region_addrs_aux (a-120) 22) r_stk
                            (a-141) (a-120) (a-126) (a-136) pc_p _ pc_g pc_b pc_e RWLX _
                            Local (a-209) (a-250) (a-208) (a-251) (a-142) 
                  with "[-]"); try apply PermFlows_refl;
          try addr_succ; try assumption;[|auto|auto| | | |].  
        { intros j ai aj Hai Haj.
          apply (region_addrs_aux_contiguous (a-120) 22 j ai aj); auto.
          done. }
        { split; [cbn; f_equal; by apply addr_unique|].
          split; [addr_succ|cbn; f_equal; by apply addr_unique].  
        }
        { apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done. }
        { apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done. }
        iFrame "Hi HPC Hr_stk".
        iSplitL "Hr_t4"; [iNext;iExists _;iFrame|].
        iSplitL "Hr_t1"; [iNext;iExists _;iFrame|].
        iSplitL "Hr_t2"; [iNext;iExists _;iFrame|].
        iSplitL "Hr_t3"; [iNext;iExists _;iFrame|].
        iSplitL "Hr_t5"; [iNext;iExists _;iFrame|].
        iSplitL "Hr_t6"; [iNext;iExists _;iFrame|].        
        iSplitL "Ha209 Hstack_adv_r".
        { iNext. (* rewrite /temp_resources. *)
          iApply region_addrs_exists.
          rewrite /region_mapsto (region_addrs_decomposition (a-209) (a-209) (a-250));[|rewrite /le_addr /=; split; done].
          assert ((a- 209 + -1)%a = Some (a-208)) as ->; [addr_succ|].
          assert ((a- 209 + 1)%a = Some (a-210)) as ->; [addr_succ|]. 
          assert (region_addrs (a- 209) (get_addr_from_option_addr (Some (a-208))) = []) as ->.
          { rewrite /region_addrs.
              by destruct (Z_le_dec (a- 209) (a- 208)) eqn:Hle; inversion Hle. }
          rewrite app_nil_l. iApply big_sepL_cons.
          iSplitL "Ha209";[iExists _; iFrame|]. 
          iApply (big_sepL_mono with "Hstack_adv_r"). 
          iIntros (k y Hsome) "Hr /=". rewrite /temp_resources.
          iDestruct "Hr" as (v) "(_ & Hv & _)". iExists _; iFrame. 
        }
        iNext. iIntros "(HPC & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6 & Hr_stk 
                   & Hstack & Hmclear)".
        (* close the adv stack region (all now point to 0!). We choose the world after 
           the local state has taken a private update *)
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hir'. 
        assert (related_sts_priv_world W'' (W''.1, (<[i:=countable.encode false]> W''.2.1, W''.2.2)))
          as Hrelated'''.
        { split;[apply related_sts_priv_refl|]. rewrite /related_sts_priv. 
          split; [apply dom_insert_subseteq|split;[auto|] ].
          intros i0 r1 r2 r1' r2' Hr Hr'.
          subst. simpl in Hr'. rewrite Hr' in Hr. inversion Hr; subst. 
          do 2 (split;auto). 
          destruct (decide (i0 = i)).
          - subst. rewrite /= lookup_insert. 
            intros x y Hx Hy. inversion Hy; subst.
            right with (countable.encode false);[|left].
            rewrite Hi in Hx. inversion Hx.
            right. simpl in Hir'. rewrite Hir' in Hr'. inversion Hr'.
            cbv. exists true,false. auto.
          - rewrite lookup_insert_ne; auto.
            intros x y Hx Hy. rewrite Hx in Hy; inversion Hy; subst. 
            left.
        }
        iAssert (sts_full_world sts_std (revoke W'')
               ∗ region (revoke (W''.1, (<[i:=countable.encode false]> W''.2.1, W''.2.2))))%I with "[Hsts Hex]" as "[Hsts Hex]".
        { rewrite region_eq /region_def.
          iDestruct "Hex" as (M) "(HM & % & Hr)".
          iDestruct (monotone_revoke_list_region_def_mono $! Hrelated''' with "[] Hsts Hr") as "[Hsts Hr]".
          - iPureIntro. by apply dom_equal_revoke. 
          - iFrame. iExists M. iFrame. iPureIntro. auto. 
        }        
        rewrite /region_mapsto (region_addrs_decomposition (a-209) (a-209) (a-250));
          [|rewrite /le_addr /=; by split]. 
        rewrite /get_addr_from_option_addr. 
        assert ((a- 209 + -1)%a = Some (a-208)) as ->; [addr_succ|].
        assert ((a- 209 + 1)%a = Some (a-210)) as ->; [addr_succ|]. 
        assert (region_addrs (a- 209) (a- 208) = []) as ->.
        { rewrite /region_addrs.
            by destruct (Z_le_dec (a- 209) (a- 208)) eqn:Hle; inversion Hle. }
        rewrite app_nil_l.
        iDestruct "Hstack" as "[Ha209 Hstack]".         
        (* let's now close the invariant for the local stack. We will need to privately 
           update the state of sts to 2! *)
        (* first we update the sts *)
        iMod (sts_update_loc _ _ _ false with "Hsts Hstate") as "[Hsts Hstate]".
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hi'.
        iMod ("Hcls" with "[Hstate Ha200 Ha201 Ha202 Ha203 Ha204 
                             Ha205 Ha206 Ha207 Ha208 Hna]") as "Hna".
        { iFrame "Hna". iExists false.
          rewrite i_4a. iFrame. }
        
        (* We now need to consolidate the region with the updated local state collection. We do this by closing the revoked
           region at the new world *)
        iMod (monotone_revoked_close_sub _ (region_addrs (a-210) (a-250)) RWLX (λ Wv, interp Wv.1 Wv.2)
                with "[Hsts $Hex Hstack]") as "[Hsts Hex]".
        { rewrite /revoke. iFrame "Hsts". 
          iClear "Hprog Hlocal full Hfull'".
          iApply big_sepL_sep. iSplitL.
          - rewrite /temp_resources.
            iApply region_addrs_exists.
            iExists (region_addrs_zeroes (a- 210) (a- 250)). 
            iApply big_sepL2_sep. iSplitR.
            { iApply big_sepL2_to_big_sepL_r; auto. iApply big_sepL_forall. auto. }
            iApply big_sepL2_sep. iFrame.
            iApply big_sepL2_to_big_sepL_r; auto.
            iAssert ([∗ list] k↦y ∈ region_addrs_zeroes (a-210) (a-250), True)%I as "Htrivial".
            { iApply big_sepL_forall; auto. }
            iApply (big_sepL_mono with "Htrivial").
            iIntros (k y Hsome) "_ /=".
            assert (y = inl 0%Z) as ->;[by apply region_addrs_zeroes_lookup in Hsome|].
            iSplit.
            + iAlways. iIntros (W1 W2 HW12) "_ /=". rewrite fixpoint_interp1_eq /=. done.
            + rewrite fixpoint_interp1_eq /=. done.            
          - iApply big_sepL_sep. rewrite /read_write_cond. iFrame "Hstack_adv".
            iApply big_sepL_forall. iPureIntro. simpl. 
            intros x y Hsome. rewrite /std_sta /std_rel /=.
            apply revoke_lookup_Temp. eapply std_update_temp_multiple_lookup in Hsome as [Hpwl Hstd']. 
            apply region_state_pwl_monotone with W';eauto. 
        }
        (* rclear *)
        iDestruct "Hf3" as "[Hi Hf3]".
        assert (list.last (region_addrs_aux (a-142) 29) = Some (a-170)).
        { cbn. cbv. do 2 f_equal. apply eq_proofs_unicity. decide equality. }
        iApply (rclear_spec (region_addrs_aux (a-142) 29)
                            (list_difference all_registers [PC; r_stk; r_t0; r_t30])
                            _ _ _ _ _ (a-142) (a-170) (a-171) with "[-]");
          try addr_succ; try assumption; try apply PermFlows_refl; auto. 
        { intros j ai aj Hai Haj.
          apply (region_addrs_aux_contiguous (a-142) 29 j ai aj); eauto.
          done. }
        { apply not_elem_of_list, elem_of_list_here. }
        { split; (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done). }
        iSplitL "Hr_t1 Hr_t2 Hr_t3 Hr_t4 Hr_t5 Hr_t6 Hmreg'". 
        { (* TODO: make this into helper lemma *)
          iNext. iApply region_addrs_exists.
          iDestruct (big_sepM_delete _ (<[r_t6:=inl 0%Z]>_) r_t6 (inl 0%Z)
                       with "[Hr_t6 Hmreg']") as "Hmreg'". 
          by rewrite lookup_insert. rewrite delete_insert_delete;iFrame. 
          iDestruct (big_sepM_delete _ (<[r_t5:=inl 0%Z]>_) r_t5 (inl 0%Z)
                       with "[Hr_t5 Hmreg']") as "Hmreg'". 
          by rewrite lookup_insert. rewrite delete_insert_delete.
          rewrite delete_insert_delete. 
          repeat (rewrite -(delete_insert_ne _ _ r_t6);auto). iFrame. 
          iDestruct (big_sepM_delete _ (<[r_t4:=inl 0%Z]>_) r_t4 (inl 0%Z)
                       with "[Hr_t4 Hmreg']") as "Hmreg'". 
          by rewrite lookup_insert. rewrite delete_insert_delete.
          repeat (rewrite -(delete_insert_ne _ _ r_t5);auto). iFrame.
          iDestruct (big_sepM_delete _ (<[r_t3:=inl 0%Z]>_) r_t3 (inl 0%Z)
                       with "[Hr_t3 Hmreg']") as "Hmreg'". 
          by rewrite lookup_insert. rewrite delete_insert_delete.
          repeat (rewrite -(delete_insert_ne _ _ r_t4);auto). iFrame.
          iDestruct (big_sepM_delete _ (<[r_t2:=inl 0%Z]>_) r_t2 (inl 0%Z)
                       with "[Hr_t2 Hmreg']") as "Hmreg'". 
          by rewrite lookup_insert. rewrite delete_insert_delete.
          repeat (rewrite -(delete_insert_ne _ _ r_t3);auto).
          repeat (rewrite (delete_commute _ _ r_t2)). iFrame. 
          iDestruct (big_sepM_delete _ (<[r_t1:=inl 0%Z]>_) r_t1 (inl 0%Z)
                       with "[Hr_t1 Hmreg']") as "Hmreg'". 
          by rewrite lookup_insert. rewrite delete_insert_delete.
          repeat (rewrite -(delete_insert_ne _ _ r_t2);auto).
          repeat (rewrite (delete_commute _ _ r_t1)). iFrame.
          iAssert (full_map r') as %Hfull';[auto|]. 
          iApply (big_sepM_to_big_sepL with "Hmreg'").
          { apply NoDup_list_difference. apply all_registers_NoDup. }
          rewrite /all_registers. 
          assert (list_difference
                    [r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9;
                     r_t10; r_t11; r_t12; r_t13; r_t14; r_t15; r_t16; r_t17;
                     r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24; r_t25;
                     r_t26; r_t27; r_t28; r_t29; r_t30; r_t31; PC]
                    [PC; r_stk; r_t0; r_t30] =
                  [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9;
                   r_t10; r_t11; r_t12; r_t13; r_t14; r_t15; r_t16; r_t17;
                   r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24; r_t25;
                   r_t26; r_t27; r_t28; r_t29]
                 ) as ->; auto.
          intros r0 Hr0.
          assert (r0 ≠ PC ∧ r0 ≠ r_t0 ∧ r0 ≠ r_t30 ∧ r0 ≠ r_stk)
            as (Hne1 & Hne2 & Hne3 & Hne4).
          { repeat (split;try split);
              (rewrite /not; intros Hne; rewrite Hne in Hr0;
               repeat (apply elem_of_cons in Hr0 as [Hcontr | Hr0]; [inversion Hcontr|]);
               inversion Hr0).
          }
          destruct (decide (r0 = r_t1)); first (subst;rewrite lookup_insert;eauto). 
          repeat (rewrite (delete_insert_ne _ _ r_t2);auto).
          destruct (decide (r0 = r_t2));
            first (subst;rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto).
          repeat (rewrite (delete_insert_ne _ _ r_t3);auto).
          destruct (decide (r0 = r_t3));
            first (subst;do 2 (rewrite lookup_insert_ne;auto)
                   ;rewrite lookup_insert;eauto).
          repeat (rewrite (delete_insert_ne _ _ r_t4);auto).
          destruct (decide (r0 = r_t4));
            first (subst;do 3 (rewrite lookup_insert_ne;auto)
                   ;rewrite lookup_insert;eauto).
          repeat (rewrite (delete_insert_ne _ _ r_t5);auto).
          destruct (decide (r0 = r_t5));
            first (subst;do 4 (rewrite lookup_insert_ne;auto)
                   ;rewrite lookup_insert;eauto).
          repeat (rewrite (delete_insert_ne _ _ r_t6);auto).
          destruct (decide (r0 = r_t6));
            first (subst;do 5 (rewrite lookup_insert_ne;auto)
                   ;rewrite lookup_insert;eauto).
          repeat (rewrite lookup_insert_ne;auto). 
          repeat (rewrite lookup_delete_ne;auto).
          apply Hfull'. 
        }
        iSplitL "HPC";[iFrame|].
        iSplitL "Hi";[iExact "Hi"|].
        iNext. iIntros "(HPC & Hmreg' & Hrclear)".
        (* jmp r_t30 *)
        iDestruct "Hf3" as "[Hi Hf3]".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_jmp_success _ _ _ _ _ (a-171) with "[Hi HPC Hr_t30]");
          first apply jmp_i;first apply PermFlows_refl;
            first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done). 
        iFrame. iEpilogue "(HPC & Ha171 & Hr1)"; iSimpl in "HPC".
        (* we will now close the invariant for the program *)
        iMod ("Hcls'" with "[-Hr_stk Hex Hmreg' HPC Hr1 Hsts Hr_t0 Ha209]") as "Hna".
        { iSplitR "Hna";[|iFrame]. iNext.
          iCombine "Ha81 Ha82 Ha83 Ha86 Ha87 Ha88 Ha89 Ha85 Ha91 Ha92 Ha93 Ha95 Ha97 
          Ha99 Ha101 Ha103 Ha105 Ha107 Ha108 Ha109 Ha111 Ha112 Ha113 Ha114 Ha115 
          Ha116 Ha117 Ha118 Ha119 Hmclear Hrclear Ha171 Hf3" as "Hprog'". 
          iExact "Hprog'". 
        }
        (* The stack pointer passed to the adversary now contains a209. we must therefore
           update the state of 209 from revoked to temporary *)
        (* First we must assert that its state is still revoked (this must be the case since we have a non duplicable 
           resource that cannot be in the map). We can prove this in a more direct way by using the fact that a-209 was 
           not in the list that we closed, and must therefore either be revoked *)
        assert (std_sta W' !! countable.encode (a-209) = Some (countable.encode Revoked)) as Ha.
        { rewrite /W' std_sta_update_multiple_insert /std_update /std_sta. rewrite lookup_insert; auto.
          rewrite /lt_addr /=. lia. }
        apply region_state_Revoked_monotone with _ W'' _ in Ha; [| |auto].
        2: { rewrite /rel_is_std_i /W' std_rel_update_multiple_insert /std_update /std_rel.
             rewrite lookup_insert;auto. rewrite /lt_addr /=. lia. }
        assert (std_sta (close_list (countable.encode <$> region_addrs (a-210) (a-250))
                                     (revoke (W''.1, (<[i:=countable.encode false]> W''.2.1, W''.2.2))))
                        !! countable.encode (a-209) = Some (countable.encode Revoked)) as Ha'.
        { assert (a-209 ∉ region_addrs_aux (a-210) (region_size (a-210) (a-250))) as Hnin. 
          { apply region_addrs_not_elem_of. rewrite /lt_addr /=; lia. }
          destruct Ha as [Hrevoked | Htemporary].
          - rewrite -close_list_std_sta_same.
            + apply revoke_lookup_Revoked. auto.
            + intros Hcontr. apply elem_of_list_fmap in Hcontr as [y  [Hy Hcontr] ].
              apply encode_inj in Hy; subst. contradiction.
          - rewrite -close_list_std_sta_same.
            + apply revoke_lookup_Temp. auto.
            + intros Hcontr. apply elem_of_list_fmap in Hcontr as [y  [Hy Hcontr] ].
              apply encode_inj in Hy; subst. contradiction.
        }
        iDestruct (full_sts_world_is_Some_rel_std _ (a-209) with "Hsts") as %Hstd209; [eauto|].         
        iMod (update_region_revoked_temp_pwl with "[] Hsts Hex Ha209 [] Hrel209") as "[Hex Hsts]"; auto. 
        { iAlways. iIntros (W1 W2 Hpub) "Hv". do 2 (rewrite fixpoint_interp1_eq). done. }
        { iAssert (∀ W, interp W (inl 0%Z))%I as "Htrivial".
          { iIntros (W0). rewrite fixpoint_interp1_eq. auto. }
          iApply "Htrivial". 
        } 
        (* We choose the r *)
        evar (r'' : gmap RegName Word).
        instantiate (r'' := <[r_stk := inr (RWLX, Local, a-209, a-250, a-208)]>
                          (<[r_t0  := inr (E, Local, a-200, a-250, a-201)]>
                           (<[r_t30 := inr (E, Global, b, e, a)]> r))).
        (* We have all the resources of r'' *)
        iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r''))
                                                   with "[Hmreg' Hr_stk Hr1 Hr_t0 HPC]"
          as "Hmaps''".
        { rewrite /r'' /r.
          do 3 (rewrite (insert_commute _ _ PC);auto). rewrite insert_insert.
          do 5 (rewrite (insert_commute _ _ r_stk);auto). rewrite insert_insert.
          do 1 (rewrite (insert_commute _ r_t0 r_t30);auto). rewrite insert_insert. 
          do 1 (rewrite (insert_commute _ r_t30 r_t0);auto). rewrite insert_insert.
          iApply (big_sepM_insert_2 with "[Hr_stk]"); first iFrame.
          iApply (big_sepM_insert_2 with "[HPC]"); first iFrame.
          iApply (big_sepM_insert_2 with "[Hr_t0]"); first (rewrite epp_local_e;iFrame).
          iApply (big_sepM_insert_2 with "[Hr1]"); first iFrame.
          assert ((list_difference all_registers [PC; r_stk; r_t0; r_t30]) =
              [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12;
               r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24;
               r_t25; r_t26; r_t27; r_t28; r_t29]) as ->; first auto. 
          rewrite /create_gmap_default. iSimpl in "Hmreg'". 
          repeat (iDestruct "Hmreg'" as "[Hr Hmreg']";
                  iApply (big_sepM_insert_2 with "[Hr]"); first iFrame).
          done. 
        }
        (* r contrains all registers *)
        iAssert (full_map r'') as "#full''".
        { rewrite /full_map /r''.
          iAssert (full_map r) as %Hfull;[auto|]. 
          iPureIntro.
          intros x; cbn.
          destruct (decide (r_stk = x)); first (subst;rewrite lookup_insert;eauto).
          rewrite lookup_insert_ne;auto.
          destruct (decide (r_t0 = x)); first (subst;rewrite lookup_insert;eauto).
          rewrite lookup_insert_ne;auto.
          destruct (decide (r_t30 = x)); first (subst;rewrite lookup_insert;eauto).
          rewrite lookup_insert_ne;auto.
        }
        (* We instantiate the fundamental theorem on the adversary region *)
        (* We start by instantiating a variable for the final version of the sts collection *)
        evar (W''' : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
        instantiate (W''' := (std_update
                                (close_list (countable.encode <$> region_addrs (a-210) (a-250))
                                            (revoke (W''.1, (<[i:=countable.encode false]> W''.2.1, W''.2.2)))) (a-209) Temporary 
                                (Rpub, Rpriv).1 (Rpub, Rpriv).2)). 
        assert (related_sts_priv_world W'' W''')
          as Hrelated4.
        { apply related_sts_priv_trans_world with (W''.1, (<[i:=countable.encode false]> W''.2.1, W''.2.2)); auto. 
          apply related_sts_priv_trans_world with (revoke (W''.1, (<[i:=countable.encode false]> W''.2.1, W''.2.2))). 
          - apply revoke_related_sts_priv; auto.
          - eapply related_sts_priv_trans_world. 
            + apply related_sts_pub_priv_world. 
              apply (close_list_related_sts_pub _ (countable.encode <$> region_addrs (a-210) (a-250))); auto.
            + apply related_sts_pub_priv_world. 
              apply related_sts_pub_world_revoked_temp; auto.
        }
        iAssert (interp_expression r'' W''' (inr (RX, Global, b, e, a)))
          as "Hvalid".
        { iApply fundamental. iLeft; auto. iExists RX. iSplit;[auto|]. 
          iApply (big_sepL_mono with "Hadv"). iIntros (k y Hsome) "(Hadv & Hperm & Hstd)". iFrame.
          iDestruct "Hstd" as %Hstd'. iDestruct "Hperm" as %Hsta.
          iPureIntro. split. 
          - apply related_sts_rel_std with W; auto.
            apply related_sts_pub_priv_trans_world with W'; auto.
            apply related_sts_pub_priv_trans_world with W''; auto. 
          - apply region_state_nwl_monotone_nl with W; auto.
            apply related_sts_pub_priv_trans_world with W'; auto.
            apply related_sts_pub_priv_trans_world with W''; auto.
        } 
        (* We are now ready to show that all registers point to a valid word *)
        iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W''' (r'' !r! r1))%I
                        with "[-Hsts Hex Hmaps'' Hvalid Hna]" as "Hreg''".
        { iIntros (r1).
          assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_t30 ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_t30)).
          { destruct (decide (r1 = PC)); [by left|right].
            destruct (decide (r1 = r_stk)); [by left|right].
            destruct (decide (r1 = r_t0)); [by left|right].
            destruct (decide (r1 = r_t30)); [by left|right;auto].  
          }
          destruct H9 as [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
          - iIntros "%". contradiction.
          - assert (r'' !! r_stk = Some (inr (RWLX, Local, a-209, a-250, a-208))) as Hr_stk.
            { rewrite /r''. by rewrite lookup_insert. }
            rewrite /RegLocate Hr_stk fixpoint_interp1_eq. 
            iIntros (_). iExists RWLX. iSplitR; [auto|].
            rewrite (region_addrs_decomposition (a-209) (a-209) (a-250));
                last (split; rewrite /le_addr; done).
            rewrite /region_addrs.
            assert ((a- 209 + -1)%a = Some (a-208)) as ->;[addr_succ|].
            rewrite /get_addr_from_option_addr.
            destruct (Z_le_dec (a- 209) (a- 208)) eqn:Hcontr;
              [inversion Hcontr|clear Hcontr]. rewrite app_nil_l.
            assert ((a- 209 + 1)%a = Some (a-210)) as ->;[addr_succ|].
            destruct (Z_le_dec (a- 210) (a- 250)) eqn:Hcontr;
              [clear Hcontr;iFrame "#"|inversion Hcontr].
            iAssert ([∗ list] y ∈ region_addrs (a-210) (a-250), read_write_cond y RWLX (fixpoint interp1)
                                                                ∧ ⌜region_state_pwl W''' y⌝
                                                                ∧ ⌜region_std W''' y⌝)%I as "#Hstack_adv+". 
            { iApply (big_sepL_mono with "Hstack_adv").
              iIntros (k y Hsome) "Hr".
              iFrame. iPureIntro.
              rewrite /region_state_pwl /region_std /rel_is_std_i /W'''.
              destruct (decide (y = (a-209))); subst; [do 2 rewrite lookup_insert;auto|].
              rewrite lookup_insert_ne;[|intros Hcontr; apply encode_inj in Hcontr; subst; contradiction].
              assert (countable.encode y ∈ countable.encode <$> region_addrs (a-210) (a-250)) as Hin.
              { apply elem_of_list_fmap. exists y. split; auto. apply elem_of_list_lookup_2 with k. auto. }
              eapply std_update_temp_multiple_lookup in Hsome as [Hpwl Hstd'].
              split. 
              - apply close_list_std_sta_revoked; auto.
                apply revoke_lookup_Temp.
                apply region_state_pwl_monotone with (W'.1, (<[i:=countable.encode false]> W''.2.1, W''.2.2));
                  [apply Hstd'| |apply Hpwl].
                split;[|apply related_sts_pub_refl].
                destruct Hrelated'' as [Hrelated'' _]; apply Hrelated''.                      
              - apply related_sts_rel_std with W''; auto.
                apply related_sts_rel_std with W'; auto.
                apply related_sts_pub_priv_world; auto.
            }
            iFrame "Hstack_adv+". iSplit. 
            { iPureIntro. rewrite /region_state_pwl /region_std /rel_is_std_i /W'''.
              do 2 rewrite lookup_insert. auto. }
            iAlways. 
            rewrite /exec_cond.
            iIntros (a0 r0 W4 Ha0 Hrelated5). iNext.
            iApply fundamental.
            + iRight. iRight. done.
            + iExists RWLX. iSplit; auto.
              rewrite (region_addrs_decomposition (a-209) (a-209) (a-250));
                last (split; rewrite /le_addr; done).
              rewrite /region_addrs.
              assert ((a- 209 + -1)%a = Some (a-208)) as ->;[addr_succ|].
              rewrite /get_addr_from_option_addr.
              destruct (Z_le_dec (a- 209) (a- 208)) eqn:Hcontr;
                [inversion Hcontr|clear Hcontr]. rewrite app_nil_l.
              assert ((a- 209 + 1)%a = Some (a-210)) as ->;[addr_succ|].
              destruct (Z_le_dec (a- 210) (a- 250)) eqn:Hcontr;
                [clear Hcontr;iFrame "#"|inversion Hcontr].
              iSplit.
              ++ iSimpl. iPureIntro. split.
                 +++ apply rel_is_std_i_monotone with W'''; auto.
                     by rewrite /W''' /std_update /rel_is_std_i lookup_insert. 
                 +++ apply region_state_pwl_monotone with W'''; auto;
                       [by rewrite /W''' /std_update /rel_is_std_i lookup_insert|
                        by rewrite /W''' /std_update /region_state_pwl lookup_insert]. 
              ++ iApply (big_sepL_mono with "Hstack_adv+").
                 iIntros (k y Hsome) "(Hr & Hpwl & Hstd)".
                 iDestruct "Hpwl" as %Hpwl; iDestruct "Hstd" as %Hstd'. 
                 iFrame. iSimpl. iPureIntro. split. 
                 +++ apply rel_is_std_i_monotone with W'''; auto. 
                 +++ apply region_state_pwl_monotone with W'''; auto. 
          - (* continuation *)
            (* clear some previously used lemmas *)
            clear rt1w Hrt1 rt2w Hrt2 rt0w Hrt0 rstkw Hrstk wr30 Hr30.
            clear rt3w Hrt3 rt4w Hrt4 rt5w Hrt5 rt6w Hrt6 Hr_t0. 
            iIntros (_). 
            assert (r'' !! r_t0 = Some (inr (E, Local, a-200, a-250, a-201)))
              as Hr_t0; auto. 
            rewrite /RegLocate Hr_t0 fixpoint_interp1_eq. iSimpl. 
            (* prove continuation *)
            iAlways.
            rewrite /enter_cond.
            iIntros (r3 W4 Hrelated5).
            iNext. iSimpl. 
            iIntros "(#[Hfull3 Hreg3] & Hmreg & Hex & Hsts & Hna)".
            iSplit; [auto|rewrite /interp_conf].
            (* get the PC, currently pointing to the activation record *)
            iDestruct (big_sepM_delete _ _ PC with "Hmreg") as "[HPC Hmreg]".
            { rewrite lookup_insert; eauto. }
            (* get some general purpose registers *)
             iAssert (⌜∃ wr_t1, r3 !! r_t1 = Some wr_t1⌝)%I as %[rt1w Hrt1];
              first iApply "Hfull3".
            iDestruct (big_sepM_delete _ _ r_t1 with "Hmreg") as "[Hr_t1 Hmreg]".
            { rewrite lookup_delete_ne; auto.
              rewrite lookup_insert_ne; eauto. }
            iAssert (⌜∃ wr_t1, r3 !! r_t2 = Some wr_t1⌝)%I as %[rt2w Hrt2];
              first iApply "Hfull3".
            iDestruct (big_sepM_delete _ _ r_t2 with "Hmreg") as "[Hr_t2 Hmreg]".
            { do 2 (rewrite lookup_delete_ne; auto).
              rewrite lookup_insert_ne; eauto. }
            iAssert (⌜∃ wr_t0, r3 !! r_t0 = Some wr_t0⌝)%I as %[rt0w Hrt0];
              first iApply "Hfull3".
            iDestruct (big_sepM_delete _ _ r_t0 with "Hmreg") as "[Hr_t0 Hmreg]".
            { do 3 (rewrite lookup_delete_ne; auto). 
              rewrite lookup_insert_ne; eauto. }
            (* get r_stk *)
            iAssert (⌜∃ wr_stk, r3 !! r_stk = Some wr_stk⌝)%I as %[rstkw Hrstk];
              first iApply "Hfull3".
            iDestruct (big_sepM_delete _ _ r_stk with "Hmreg") as "[Hr_stk Hmreg]".
            { do 4 (rewrite lookup_delete_ne; auto).
              rewrite lookup_insert_ne; eauto. }
            (* get r_t30 *)
            iAssert (⌜∃ wr30, r3 !! r_t30 = Some wr30⌝)%I as %[wr30 Hr30];
              first iApply "Hfull3".
            iDestruct (big_sepM_delete _ _ r_t30 with "Hmreg") as "[Hr_t30 Hmreg]".
            { do 5 (rewrite lookup_delete_ne; auto).
              rewrite lookup_insert_ne; eauto. }
            (* We start by opening the invariant for the program *)
            iMod (na_inv_acc logrel_nais ⊤ ⊤
                              (regN.@(a-81, a-176)) with "Hprog Hna")
              as "(>Hf3 & Hna & Hcls')"; auto. 
            (* open the na invariant for the local stack content *)
            iMod (na_inv_acc logrel_nais ⊤ (⊤ ∖ ↑regN.@(a-81, a-176))
                              (regN.@(a-200, a-209)) with "Hlocal Hna")
              as "(Hstack & Hna & Hcls)"; [auto|solve_ndisj|].
            (* By public future world, we can assert that the state of i is true *)
            rewrite bi.later_exist. iDestruct "Hstack" as (x) "Hstack".
            destruct x.
            { (* by the future world relation, we will get a contradiction *)
              iDestruct "Hstack" as "(>Hstate & _)".
              iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hi'''.
              iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hir''. 
              exfalso.
              destruct Hrelated5 as (_ & _ & _ & Hrelated5).
              destruct Hrelated5 with i (convert_rel (λ a b : bool, a = b))
                                       (convert_rel (λ a b : bool, a = true ∨ b = false))
                                       (convert_rel (λ a b : bool, a = b))
                                       (convert_rel (λ a b : bool, a = true ∨ b = false))
                as (_ & _ & Hcontr); auto.
              eapply rtc_id_eq  with (countable.encode false) (countable.encode true) in Hcontr; auto; done. 
            }
            iDestruct "Hstack" as "(>Hstate & >Ha200 & >Ha201 & >Ha202 & >Ha203 & >Ha204
                                        & >Ha205 & >Ha206 & >Ha207 & >Ha208)".
            (* step through instructions in activation record *)
            (* move rt_1 PC *)
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_move_success_reg_fromPC _ RX Local (a-200) (a-250) (a-201) (a-202) (inl w_1)
                      with "[HPC Ha201 Hr_t1]");
              [rewrite -i_1; apply decode_encode_inv|eauto
               |constructor; auto; split; done|
               addr_succ|
               auto|iFrame|]. 
            iEpilogue "(HPC & Ha201 & Hr_t1)".
            (* lea r_t1 7 *)
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_lea_success_z _ RX Local (a-200) (a-250) (a-202) (a-203) (inl w_2)
                                     _ RX _ _ _ (a-201) 7 (a-208) with "[HPC Ha202 Hr_t1]");
              try addr_succ;
              first (rewrite -i_2; apply decode_encode_inv);
              [eauto|(constructor; auto; split; done); auto|auto|auto|iFrame|].
            iEpilogue "(HPC & Ha202 & Hr_t1)".
            (* load r_stk r_t1 *)
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_load_success _ _ _ RX Local (a-200) (a-250) (a-203) (inl w_3) _ _ RX Local (a-200) (a-250) (a-208) (a-204)
                      with "[HPC Ha208 Hr_t1 Hr_stk Ha203]");
              try addr_succ;
              first (rewrite -i_3; apply decode_encode_inv);
              [eauto|eauto|(constructor; auto; split; done)|auto|auto|iFrame|].
            iEpilogue "(HPC & Hr_stk & Ha203 & Hr_t1 & Ha208)".
            destruct (a- 208 =? a- 203)%a eqn:Hcontr; [inversion Hcontr|clear Hcontr]. 
            (* sub r_t1 0 1 *)
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_add_sub_lt_success _ r_t1 _ _ (a-200) (a-250) (a-204) (inl w_4a)
                      with "[HPC Hr_t1 Ha204]");
              try addr_succ;
              first (right; left; rewrite -i_4a; apply decode_encode_inv);
              [apply Hrx|constructor; auto; split; done| | ]. 
            rewrite -i_4a. iFrame. iSplit; auto.
            destruct (reg_eq_dec r_t1 PC) eqn:Hcontr;[inversion Hcontr|clear Hcontr].
            assert ((a-204 + 1)%a = Some (a-205)) as ->; [addr_succ|].
            rewrite -i_4a decode_encode_inv.
            iEpilogue "(HPC & Ha204 & _ & _ & Hr_t1)".
            (* Lea r_stk r_t1 *)
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_lea_success_reg _ RX Local (a-200) (a-250) (a-205) (a-206) (inl w_4b) _ _ RWLX Local (a-200) (a-250) (a-208) (-1) (a-207)
                      with "[HPC Hr_t1 Hr_stk Ha205]");
              try addr_succ;
              first (rewrite -i_4b; apply decode_encode_inv); first apply Hrx; 
                first (constructor; auto; split; done); auto.
            iFrame. iEpilogue "(HPC & Ha205 & Hr_t1 & Hr_stk)".
            (* Load PC r_t1 *)
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_load_success_PC _ r_stk RX Local (a-200) (a-250) (a-206) (inl w_4c) RWLX Local (a-200) (a-250) (a-207)
                                       _ _ _ _ (a-171) (a-172)
                      with "[HPC Hr_stk Ha206 Ha207]");
              try addr_succ;
              first (rewrite -i_4c; apply decode_encode_inv);
              first apply Hrx; first apply PermFlows_refl;
                first (constructor; auto; split; done); auto.
            iFrame. iEpilogue "(HPC & Ha206 & Hr_stk & Ha207)".
            (* We now continue execution of f3 *)
            (* We need to extract a172 from f3 *)
            iDestruct "Hf3" as "[Hf3_done Hf3]".
            do 31 (iDestruct "Hf3" as "[Ha Hf3]";
                   iCombine "Hf3_done Ha" as "Hf3_done").
            (* sub r_t1 0 7 *)
            iDestruct "Hf3" as "[Ha172 Hf3]". 
            iApply (wp_bind (fill [SeqCtx])). 
            iApply (wp_add_sub_lt_success _ r_t1 _ _ _ _ (a-172)
                      with "[HPC Hr_t1 Ha172]");
              first (right; left; apply sub_z_z_i); first apply PermFlows_refl;
              first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)
                ; auto. 
            iFrame. iSplit; auto.
            destruct (reg_eq_dec r_t1 PC) eqn:Hcontr;[inversion Hcontr|clear Hcontr].
            assert ((a-172 + 1)%a = Some (a-173)) as ->; [addr_succ|].
            rewrite sub_z_z_i.
            iEpilogue "(HPC & Ha172 & _ & _ & Hr_t1)".
            (* lea r_stk r_t1 *)
            iDestruct "Hf3" as "[Ha173 Hf3]". 
            iApply (wp_bind (fill [SeqCtx])). 
            iApply (wp_lea_success_reg _ _ _ _ _ (a-173) (a-174) _ r_stk r_t1 RWLX _ _ _
                                   (a-207) (-7)%Z (a-200)
                  with "[HPC Hr_t1 Hr_stk Ha173]");
              try addr_succ;
              first apply lea_r_i; first apply PermFlows_refl;
              first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)
                ; auto. 
            iFrame. iEpilogue "(HPC & Ha173 & Hr_t1 & Hr_stk)".
            (* halt *)
            iDestruct "Hf3" as "[Ha174 Hf3]". 
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_halt _ _ _ _ _ (a-174) with "[HPC Ha174]");
              try addr_succ;
              first apply halt_i; first apply PermFlows_refl;
              first (apply isCorrectPC_bounds with (a-0) (a-199); eauto; split; done)
                ; auto. 
            iFrame. iEpilogue "(HPC & Ha174)".
            (* before we halt the execution, we must close our invariants *)
            iMod ("Hcls" with "[Hstate Ha200 Ha201 Ha202 Ha203 Ha204
                               Ha205 Ha206 Ha207 Ha208 Hna]") as "Hna".
            { iFrame. iExists false. iNext. iFrame. }
            iMod ("Hcls'" with "[Hf3 Hf3_done Ha172 Ha173 Ha174 Hna]") as "Hna".
            { iSplitR "Hna";[|iFrame].
              iNext.
              iDestruct "Hf3" as "(Ha175 & Ha176 & Ha177 & Ha178)".
              iCombine "Ha172 Ha173 Ha174 Ha175 Ha176 Ha177 Ha178" as "Hf3_end".
              repeat (iDestruct "Hf3_done" as "[Hf3_done Ha]";
                      iCombine "Ha Hf3_end" as "Hf3_end"). 
              iCombine "Hf3_done Hf3_end" as "$". 
            }
            (* we are now ready to show the postcondition *)
            iApply wp_value; auto.
            iIntros "_".
            iExists _,_.
            (* reconstruct the full map f3 *)
            iDestruct (big_sepM_delete _ _ r_t30 with "[$Hmreg $Hr_t30]") as "Hmreg".
            { repeat (rewrite lookup_delete_ne;auto).
              rewrite lookup_insert_ne;auto. }
            rewrite (delete_commute _ r_stk). 
            iDestruct (big_sepM_delete _ _ r_t0 with "[$Hmreg $Hr_t0]") as "Hmreg".
            { repeat (rewrite lookup_delete_ne;auto).
              rewrite lookup_insert_ne;auto. }
            rewrite (delete_commute _ _ r_t2).
            iDestruct (big_sepM_delete _ _ r_t2 with "[$Hmreg $Hr_t2]") as "Hmreg".
            { repeat (rewrite lookup_delete_ne;auto).
              rewrite lookup_insert_ne;auto. }
            rewrite delete_insert_delete.
            rewrite -(delete_insert_delete r3 PC (inr (pc_p, pc_g, pc_b, pc_e, a- 174))).
            do 2 rewrite (delete_commute _ _ PC). 
            iDestruct (big_sepM_delete _ _ PC with "[$Hmreg $HPC]") as "Hmreg".
            { do 2 (rewrite lookup_delete_ne;auto).
              rewrite lookup_insert;auto. }
            rewrite -(delete_insert_delete _ r_t1 (inl (-7)%Z)).
            rewrite -(delete_commute _ r_t1).
            iDestruct (big_sepM_delete _ _ r_t1 with "[$Hmreg $Hr_t1]") as "Hmreg".
            { rewrite lookup_delete_ne;auto.
              rewrite lookup_insert;auto. }
            rewrite -(delete_insert_delete _ r_stk
                                           (inr (RWLX, Local, a- 200, a- 250, a- 200))).
            iDestruct (big_sepM_delete _ _ r_stk with "[$Hmreg $Hr_stk]") as "Hmreg".
            { rewrite lookup_insert;auto. }
            (* frame *)
            iFrame.
            iSplitL;[|iPureIntro;split;apply related_sts_priv_refl].
            rewrite /full_map.
            iIntros (r0).
            destruct (decide (r0 = r_stk)); first subst;
              [iPureIntro; rewrite lookup_insert;eauto|].
            rewrite lookup_insert_ne;[|auto].
            destruct (decide (r0 = r_t1)); first subst;
              [iPureIntro; rewrite lookup_insert;eauto|].
            rewrite lookup_insert_ne;[|auto].
            destruct (decide (r0 = PC)); first subst;
              [iPureIntro; rewrite lookup_insert;eauto|].
            rewrite lookup_insert_ne;[|auto].
            iApply "Hfull3". 
          - rewrite Hr_t30.
            assert (r'' !! r_t30 = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto.
            rewrite /RegLocate Hr_t30_some fixpoint_interp1_eq. iSimpl. 
            iIntros (_). 
            iAlways. rewrite /enter_cond.
            iIntros (r0 W6 Hrelated6). 
            iNext. iApply fundamental.
            iLeft. done.
            iExists RX. iSplit; auto.
            iApply (big_sepL_mono with "Hadv"). 
            iIntros (k y Hsome) "(Hcond & Hperm & Hstd)".
            iFrame. iDestruct "Hperm" as %Hperm; iDestruct "Hstd" as %Hstd'.
            iPureIntro. simpl.
            assert (related_sts_priv_world W W6) as Hrelated_final.
            { apply related_sts_priv_trans_world with W'''; auto.
              apply related_sts_priv_trans_world with W''; auto.
              apply related_sts_priv_trans_world with W';
                apply related_sts_pub_priv_world; auto.
            }
            split.
            + apply related_sts_rel_std with W; auto.
            + apply region_state_nwl_monotone_nl with W; auto.
          - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
            rewrite /RegLocate in Hr1. 
            rewrite /r'' /RegLocate. 
            do 3 (rewrite lookup_insert_ne;[|auto]).
            destruct (r !! r1) eqn:Hrr1;rewrite Hrr1;
              [|rewrite fixpoint_interp1_eq;iPureIntro;eauto].
            specialize Hr1 with r1. rewrite Hrr1 in Hr1.
            rewrite Hr1; auto.
            rewrite fixpoint_interp1_eq. iPureIntro. eauto.      
        }
        iDestruct ("Hvalid" with "[$Hreg'' Hsts $Hex $Hna $Hmaps'']")
          as "[_ Ho]". 
        { iFrame "∗ #". }
        iApply wp_wand_r. iFrame.
        iIntros (v) "Hhalted".
        iIntros (->).
        iSpecialize ("Hhalted" with "[]");[auto|]. 
        iDestruct "Hhalted" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
        iExists _,_. iFrame. 
        iPureIntro.
        apply related_sts_priv_trans_world with W'''; auto. 
      - rewrite Hr_t30. 
        assert (r !! r_t30 = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some fixpoint_interp1_eq. iSimpl. 
        iIntros (_). 
        iAlways. rewrite /enter_cond.
        iIntros (r0 W6 Hrelated6). 
        iNext. iApply fundamental.
        iLeft. done.
        iExists RX. iSplit; auto.
        iApply (big_sepL_mono with "Hadv").
        iIntros (k y Hsome) "(Hcond & Hperm & Hstd)". iFrame.
        iDestruct "Hperm" as %Hperm; iDestruct "Hstd" as %Hstd. iPureIntro.
        assert (related_sts_priv_world W W6) as Hrelated_final.
        { apply related_sts_priv_trans_world with W'; auto.
          apply related_sts_pub_priv_world; auto. }
        split.
        + apply related_sts_rel_std with W; auto.
        + apply region_state_nwl_monotone_nl with W; auto.
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        rewrite Hr1; auto.
        rewrite fixpoint_interp1_eq. iPureIntro. eauto.         
    }
    iAssert (((interp_reg interp) W' r))%I as "#HvalR";[iSimpl;auto|]. 
    iSpecialize ("Hvalid" with "[$HvalR $Hmaps Hsts $Hna $Hr]"); iFrame. 
    iDestruct "Hvalid" as "[_ Ho]". 
    rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros "_"; iFrame. Unshelve. done. 
  Qed. 
