From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental. 
From cap_machine.examples Require Import stack_macros scall. 

Section lse.
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

  Ltac isWithinBounds := rewrite /withinBounds; apply andb_true_iff; split; apply Z.leb_le; simpl; auto.

  Ltac iNotElemOfList :=
    repeat (apply not_elem_of_cons; split;[auto|]); apply not_elem_of_nil.  

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
      iDestruct prog as "[Hi Hf2]";
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
      iDestruct prog as "[Hi Hf2]";
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

   Ltac iDestructList Hlength l :=
     (repeat (let a := fresh "a" in destruct l as [|a l];[by inversion Hlength|]));
     destruct l;[|by inversion l].
   
   Ltac iContiguous_bounds lo mid hi index Ha :=
     split; [apply incr_list_ge_middle with _ index lo mid in Ha; auto|
             apply incr_list_le_middle with _ index mid hi in Ha; auto]. 

   Ltac iContiguous_next Ha index :=
     rewrite /contiguous in Ha; apply Ha with index;auto.
    
        
  (* encapsulation of local state using local capabilities and scall *)
  (* assume r1 contains an executable pointer to adversarial code 
     (no linking table yet) *)
   Definition f2_instrs (r1 : RegName) epilogue_off flag_off :=
     push_z_instrs r_stk 1 ++
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1;
     load_r r1 r_stk;
     sub_z_z r_t1 0 1;
     lea_r r_stk r_t1;
     move_r r_t1 PC;
     lea_z r_t1 5; (* offset to assertion failure *)
     sub_r_z r1 r1 1;
     jnz r_t1 r1;
     halt;
     (* failure *)
     move_r r_t1 PC;
     lea_z r_t1 flag_off;
     store_z r_t1 1;
     halt].

  Definition f2 (a : list Addr) (p : Perm) (r1 : RegName) epilogue_off flag_off : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(f2_instrs r1 epilogue_off flag_off), a_i ↦ₐ[p] w_i)%I.

  Compute (length (f2_instrs (r_t30) 0 0)).
  Compute (region_size (a-0) (a-93)).

  (* We want to show encapsulation of local state, by showing that an arbitrary adv 
     cannot change what lies on top of the stack after return, i.e. we want to show
     that the last pop indeed loads the value 1 into register r1 *)
  (* to make the proof simpler, we are assuming WLOG the r1 registers is r_t30 *)
  Lemma f2_spec W b e a pc_p pc_g pc_b pc_e (* PC *)
        f2_addrs flag_off (* f2 *)
        a_first a_last a_flag (* special adresses *) 
        (b_r e_r b_r' : Addr) (* stack *) :
    
    (* PC assumptions *)
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a_first)) ∧
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a_last)) →

    (* Program adresses assumptions *)
    contiguous f2_addrs ->
    f2_addrs !! 0 = Some a_first ∧ list.last f2_addrs = Some a_last ->
    
    (* Stack assumptions *)
    (0%a ≤ e_r)%Z ∧ (0%a ≤ b_r)%Z -> (* this assumption will not be necessary once addresses are finite *)
    (b_r ≤ e_r)%Z ->
    region_size b_r e_r > 10 -> (* we must assume the stack is large enough for needed local state *)
    (b_r' + 1)%a = Some b_r ->
    
    {{{ r_stk ↦ᵣ inr ((RWLX,Local),b_r,e_r,b_r')
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r_t30]; wsr,
           r_i ↦ᵣ w_i)
      ∗ (∃ ws, [[b_r, e_r]]↦ₐ[RWLX][[ws]])
      (* flag *)
      ∗ a_flag ↦ₐ[RW] inl 0%Z
      (* token which states all invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv *)
      ∗ r_t30 ↦ᵣ inr ((E,Global),b,e,a)
      ∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp)
      (* trusted *)
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ f2 f2_addrs pc_p r_t30 65 flag_off
      (* we start out with arbitrary sts *)
      ∗ sts_full_world sts_std W
      ∗ region W
    }}}
      Seq (Instr Executable)
    {{{ v, RET v; ⌜v = HaltedV⌝ → a_flag ↦ₐ[RW] inl 0%Z }}}.
  Proof.
    iIntros ([Hvpc0 Hvpc93] Hf2 [Ha_first Ha_last] Hbounds Hle Hsize Hb_r' φ)
            "(Hr_stk & Hr_gen & Hstack & Hflag & Hna & Hr1 & #Hadv & HPC & Hf2 & Hs & Hr) Hφ /=".
    (* Getting some general purpose regiters *)
    iDestruct "Hr_gen" as (wsr) "Hr_gen". 
    (* get_genpur_reg "Hr_gen" wsr "[Hrt0 Hr_gen]". *)
    (* get_genpur_reg "Hr_gen" wsr "[Hrt1 Hr_gen]". *)
    (* get_genpur_reg "Hr_gen" wsr "[Hrt2 Hr_gen]". *)
    (* assert that the stack bounds are within bounds *)
    assert (withinBounds (RWLX,Local,b_r,e_r,b_r) = true ∧ withinBounds (RWLX,Local,b_r,e_r,e_r) = true) as [Hwb1 Hwb2].
    { split; isWithinBounds; lia. }
    (* Splitting the stack into own and adv parts *)
    iDestruct "Hstack" as (ws) "Hstack". 
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 9)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { rewrite region_addrs_length in Hlength; auto. rewrite Hlength in Hsize. 
      do 9 (destruct ws as [|? ws]; [simpl in Hsize; lia|]).
           by exists [w;w0;w1;w2;w3;w4;w5;w6;w7],ws. }
    rewrite Happ.
    iDestruct (contiguous_program_split with "Hstack") as (stack_own stack_adv s_last s_first)
                                                            "(Hstack_own & Hstack_adv & #Hcont)";
      [apply region_addrs_contiguous|lia|..].
    { rewrite Happ region_addrs_length in Hlength;[|auto]. rewrite app_length in Hlength. lia. }
    iDestruct "Hcont" as %(Hstack_own & Hstack_adv & Hstackeq & Hs_last & Hs_first & Hlink).
    assert (contiguous (region_addrs b_r e_r)) as Hstackcont;[apply region_addrs_contiguous|rewrite Hstackeq in Hstackcont]. 
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_own. rewrite Hlength' in Hlength_own.
    (* Getting the top adress on the stack *)
    destruct stack_own as [|a0 stack_own]; [inversion Hlength_own|]; destruct ws_own as [|w ws_own];[inversion Hlength'|].
    iDestruct "Hstack_own" as "[Ha0 Hstack_own]".
    (* Prepare the push macro *)
    rewrite /f2 /f2_instrs. 
    iDestruct (contiguous_program_split with "Hf2") as (push_z rest push_z_last rest_first)
                                                         "(Hpush & Hf2 & #Hcont)"; [auto|simpl;lia|simpl;lia|..]. 
    iDestruct "Hcont" as %(Hpush & Hrest & Hprogeq & Hp_last & Hp_first & Hlink').
    iDestruct (big_sepL2_length with "Hpush") as %Hpush_length.
    iDestructList Hpush_length push_z.
    assert (a1 = a_first) as ->;[subst; by inversion Ha_first|simplify_eq].
    assert (a0 = b_r) as ->;[|simplify_eq].
    { assert ((region_addrs b_r e_r) !! 0 = Some b_r) as Hfirst;[apply region_addrs_first;auto|].
      rewrite Hstackeq in Hfirst. by inversion Hfirst. }
    assert (a2 = push_z_last) as <-;[|simplify_eq];[simpl in Hp_last; by inversion Hp_last|].
    (* push 1 *)
    iApply (push_z_spec with "[-]"); last iFrame "Hpush HPC Ha0 Hr_stk";
      [|apply PermFlows_refl|isWithinBounds;lia|iContiguous_next Hf2 0|apply Hlink'|apply Hb_r'|..].
    { split; auto. apply isCorrectPC_bounds_alt with a_first a_last; auto. iContiguous_bounds a_first a2 a_last 1 Hf2. }
    iNext. iIntros "(HPC & _ & Hr_stk & Hb_r)".
    (* Prepare the scall prologue macro *)
    destruct stack_own as [|stack_own_b stack_own];[inversion Hlength_own|]. 
    assert ((stack_own_b :: stack_own) = region_addrs stack_own_b s_last) as ->.
    { apply contiguous_region_addrs; auto. by apply contiguous_weak in Hstack_own. }
    assert (stack_adv = region_addrs s_first e_r) as ->.
    { apply contiguous_region_addrs; auto. rewrite -(region_addrs_last b_r);[|auto].
      rewrite Hstackeq. rewrite -last_app_eq; [auto|]. destruct stack_adv; [inversion Hs_first|simpl;lia]. }
    iDestruct (contiguous_program_split with "Hf2") as (scall_prologue rest0 scall_last rest0_first)
                                                         "(Hscall & Hf2 & #Hcont)"; [auto|simpl;lia|simpl;lia|..].
    clear Hlink' Hp_last.
    iDestruct "Hcont" as %(Hcont_scall & Hcont_rest0 & Hrest_app & Hscall_last & Hrest0_first & Hlink'). subst.
    iDestruct (big_sepL2_length with "Hscall") as %Hscall_length. simpl in Hscall_length.
    assert ((stack_own_b + 7)%a = Some s_last) as Hstack_own_bound.
    { apply (contiguous_incr_addr_middle _ 1 7 stack_own_b _ Hstack_own); auto. simpl.
      assert (length stack_own - 1 = 6) as Heq;[simpl in Hlength_own;lia|]. rewrite -Heq. 
      rewrite -last_lookup. simpl in Hs_last. destruct stack_own; [inversion Heq|done]. }
    (* scall *)
    iApply (scall_prologue_spec with "[-]");
      last ((iFrame "HPC Hr_stk Hscall"); iSplitL "Hr_gen";[iNext;simpl;iExists wsr;iFrame|
                                          iSplitL "Hstack_own";[iNext;iExists ws_own;iFrame|
                                                                iSplitL "Hstack_adv";[iNext;iExists ws_adv;iFrame|] ] ]);
      [| | | |apply Hbounds|apply Hcont_scall|rewrite -(lookup_app_l _ rest0);[auto|rewrite Hscall_length;simpl;lia] |apply Hscall_last|
       apply PermFlows_refl|iNotElemOfList|iContiguous_next Hstack_own 0|apply Hstack_own_bound| | |apply Hlink'|..].
    { apply isCorrectPC_bounds_alt with a_first a_last; auto. iContiguous_bounds a_first rest_first a_last 2 Hf2. }
    { apply isCorrectPC_bounds_alt with a_first a_last; auto. iContiguous_bounds a_first scall_last a_last 78 Hf2;
      (rewrite lookup_app_r;[|simpl;lia]; rewrite lookup_app_l;[simpl|rewrite Hscall_length;simpl;lia];
      assert (length scall_prologue - 1 = 76) as <-;[subst;lia|]; by rewrite -last_lookup). }
    { apply isWithinBounds_bounds_alt with b_r e_r; auto. iContiguous_bounds b_r stack_own_b e_r 1 Hstackcont.
      apply last_app_region_addrs. destruct (region_addrs s_first e_r); [inversion Hs_first|simpl;lia]. }
    { apply isWithinBounds_bounds_alt with b_r e_r; auto. iContiguous_bounds b_r s_first e_r (2 + length stack_own) Hstackcont;
      [rewrite lookup_app_r /=; auto; by rewrite PeanoNat.Nat.sub_diag..|].
      apply last_app_region_addrs. destruct (region_addrs s_first e_r); [inversion Hs_first|simpl;lia]. }
    { assert (8 = 7 + 1)%Z as ->;[lia|]. rewrite (addr_add_assoc _ s_last); auto. }
    { apply (contiguous_incr_addr _ 77 rest_first _ Hrest); auto.
      rewrite lookup_app_r;[|lia]. by rewrite -Hscall_length PeanoNat.Nat.sub_diag. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hstack_adv & _)". 
    (* jmp r_t30 *)
    iPrologue "Hf2".
    iApply (wp_jmp_success _ _ _ _ _ (a-78) with "[Hi HPC Hr1]");
      first apply jmp_i;first apply PermFlows_refl;
      first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done). 
    iFrame. iEpilogue "(HPC & _ & Hr1)"; iSimpl in "HPC".
    (* We have now arrived at the interesting part of the proof: namely the unknown 
       adversary code. In order to reason about unknown code, we must apply the 
       fundamental theorem. To this purpose, we must first define the stsf that will 
       describe the behavior of the memory. *)
    evar (r : gmap RegName Word).
    instantiate (r := <[PC    := inl 0%Z]>
                     (<[r_stk := inr (RWLX, Local, (a-129), (a-150), (a-128))]>
                     (<[r_t0  := inr (E, Local, (a-120), (a-150), (a-121))]>
                     (<[r_t30 := inr (E, Global, b, e, a)]>
                     (create_gmap_default
                (list_difference all_registers [PC; r_stk; r_t0; r_t30]) (inl 0%Z)))))).
    iAssert (interp_expression r W (inr (RX, Global, b, e, a))) as "Hvalid". 
    { iApply fundamental. iLeft; auto. iExists RX. iFrame "#". admit. }
    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r))
                          with "[Hr_gen Hr_stk Hr_t0 Hr1 HPC]" as "Hmaps".
    { rewrite /r /registers_mapsto (insert_insert _ PC).
      iApply (big_sepM_insert_2 with "[HPC]"); first iFrame.
      iApply (big_sepM_insert_2 with "[Hr_stk]"); first iFrame.
      iApply (big_sepM_insert_2 with "[Hr_t0]"); first iFrame.
      iApply (big_sepM_insert_2 with "[Hr1]"); first iFrame.
      assert ((list_difference all_registers [PC; r_stk; r_t0; r_t30]) =
              [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12;
               r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24;
               r_t25; r_t26; r_t27; r_t28; r_t29]) as ->; first auto. 
      rewrite /create_gmap_default. iSimpl in "Hr_gen". 
      repeat (iDestruct "Hr_gen" as "[Hr Hr_gen]"; iApply (big_sepM_insert_2 with "[Hr]"); first iFrame).
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
    (* Need to prove the validity of the continuation, the stack, as well as put
       local memory into invariant. *)
    iMod (inv_alloc
            (nroot.@"Hprog")
            _
            (a- 79 ↦ₐ[pc_p] sub_z_z r_t1 0 7
           ∗ a- 80 ↦ₐ[pc_p] lea_r r_stk r_t1
           ∗ a- 81 ↦ₐ[pc_p] load_r r_t30 r_stk
           ∗ a- 82 ↦ₐ[pc_p] sub_z_z r_t1 0 1
           ∗ a- 83 ↦ₐ[pc_p] lea_r r_stk r_t1
           ∗ a- 84 ↦ₐ[pc_p] move_r r_t1 PC
           ∗ a- 85 ↦ₐ[pc_p] lea_z r_t1 5
           ∗ a- 86 ↦ₐ[pc_p] sub_r_z r_t30 r_t30 1
           ∗ a- 87 ↦ₐ[pc_p] jnz r_t1 r_t30
           ∗ a- 88 ↦ₐ[pc_p] halt
           ∗ a- 89 ↦ₐ[pc_p] move_r r_t1 PC
           ∗ a- 90 ↦ₐ[pc_p] lea_z r_t1 4
           ∗ a- 91 ↦ₐ[pc_p] store_z r_t1 1
           ∗ a- 92 ↦ₐ[pc_p] halt)
            with "[Hprog]")%I as "#Hprog".
    { iNext; iFrame. }
    iMod (na_inv_alloc logrel_nais ⊤ (logN.@(a- 120, a- 150))
                        (a- 120 ↦ₐ[RWLX] inl 1%Z
                       ∗ a- 121 ↦ₐ[RWLX] inl w_1
                       ∗ a- 122 ↦ₐ[RWLX] inl w_2
                       ∗ a- 123 ↦ₐ[RWLX] inl w_3
                       ∗ a- 124 ↦ₐ[RWLX] inl w_4a
                       ∗ a- 125 ↦ₐ[RWLX] inl w_4b
                       ∗ a- 126 ↦ₐ[RWLX] inl w_4c
                       ∗ a- 127 ↦ₐ[RWLX] inr (pc_p, pc_g, pc_b, pc_e, a- 78)
                                ∗ a- 128 ↦ₐ[RWLX] inr (RWLX, Local, a- 120, a- 150, a- 128))%I
            with "[-Hφ Hs Hstack_adv Hvalid Hmaps Hna Hflag Hr]")
      as "#Hlocal".
    { iNext. iFrame. rewrite /region_mapsto. 
      assert (region_addrs (a-121) (a-128) = [a-121; a-122; a-123; a-124; a-125; a-126; a-127; a-128]) as ->.
      { rewrite /region_addrs. simpl. repeat f_equal; (apply eq_proofs_unicity; decide equality). }
      repeat (iDestruct "Hstack_own" as "(Ha & Hstack_own)"; iFrame "Ha"). 
    }
    iAssert (|={⊤}=> ([∗ list] a0 ∈ region_addrs (a-129) (a-150),
                     read_write_cond a0 RWLX (fixpoint interp1)) ∗ region _ ∗ sts_full_world sts_std _)%I
                                           with "[Hstack_adv Hr Hs]" as ">(#Hstack_adv & Hr & Hs)". 
    { iApply region_addrs_zeroes_alloc; auto; [|iFrame]. rewrite /std_sta /std_rel /=.
      admit. }
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W (r !r! r1))%I
      with "[-Hs Hmaps Hvalid Hna Hφ Hflag Hr]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_t30 ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_t30)).
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_t30)); [by left|right;auto].  
      }
      destruct H4 as [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      - iIntros "%". contradiction.
      - (* invariant for the stack of the adversary *)
        assert (r !! r_stk = Some (inr (RWLX, Local, a-129, a-150, a-128))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk fixpoint_interp1_eq. (* iSimpl.  *)
        iIntros (_). (* iAlways. iExists _,_,_,_. (iSplitR; [eauto|]). *)
        iExists RWLX. iSplitR; [auto|].
        iSplitL.
        { admit. }
        iAlways.
        rewrite /exec_cond.
        iIntros (a0 r' W' Ha0 HWW'). iNext.
        iApply fundamental.
        + iRight. iRight. done.
        + iExists RWLX. iSplit; auto. admit.
      - (* continuation *)
        iIntros (_). 
        assert (r !! r_t0 = Some (inr (E, Local, a-120, a-150, a-121))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 fixpoint_interp1_eq. iSimpl. 
        (* prove continuation *)
        (* iExists _,_,_,_. iSplit;[eauto|]. *)
        iAlways.
        rewrite /enter_cond. 
        iIntros (r' W' HWW').
        destruct W as [fs' fr' ].
        iNext. iSimpl. 
        (* iExists _,_.  do 2 (iSplit; [eauto|]).*)
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hr & Hs & Hna)". 
        iSplit; [eauto|rewrite /interp_conf].
        (* get the PC, currently pointing to the activation record *)
        iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']".
        { rewrite lookup_insert; eauto. }
        (* get a general purpose register *)
        iAssert (⌜∃ wr_t1, r' !! r_t1 = Some wr_t1⌝)%I as %[rt1w Hrt1];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t1 with "Hmreg'") as "[Hr_t1 Hmreg']".
        { rewrite lookup_delete_ne; auto.
          rewrite lookup_insert_ne; eauto. }
        (* get r_stk *)
        iAssert (⌜∃ wr_stk, r' !! r_stk = Some wr_stk⌝)%I as %[rstkw Hrstk];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_stk with "Hmreg'") as "[Hr_stk Hmreg']".
        { do 2 (rewrite lookup_delete_ne; auto).
          rewrite lookup_insert_ne; eauto. }
        (* get r_t30 *)
        iAssert (⌜∃ wr30, r' !! r_t30 = Some wr30⌝)%I as %[wr30 Hr30];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t30 with "Hmreg'") as "[Hr_t30 Hmreg']".
        { do 3 (rewrite lookup_delete_ne; auto).
          rewrite lookup_insert_ne; eauto. }
        (* open the na invariant for the local stack content *)
        iMod (na_inv_open logrel_nais ⊤ ⊤ (logN.@(a-120,a-150)) with "Hlocal Hna")
          as "(>(Ha120 & Ha121 & Ha122 & Ha123 & Ha124 & Ha125 & Ha126 & Ha127 & Ha128) 
          & Hna & Hcls)"; auto.
        assert (PermFlows RX RWLX) as Hrx;[by rewrite /PermFlows /=|]. 
        (* step through instructions in activation record *)
        (* move rt_1 PC *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_move_success_reg_fromPC _ RX Local (a-120) (a-150) (a-121) (a-122) (inl w_1)
               with "[HPC Ha121 Hr_t1]");
          [rewrite -i_1; apply decode_encode_inv|eauto
           |constructor; auto; split; done|
           addr_succ|
           auto|iFrame|]. 
        iEpilogue "(HPC & Ha121 & Hr_t1)".
        (* lea r_t1 7 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_z _ RX Local (a-120) (a-150) (a-122) (a-123) (inl w_2)
                                 _ RX _ _ _ (a-121) 7 (a-128) with "[HPC Ha122 Hr_t1]");
          try addr_succ;
          first (rewrite -i_2; apply decode_encode_inv);
          [eauto|(constructor; auto; split; done); auto|auto|auto|iFrame|].
        iEpilogue "(HPC & Ha122 & Hr_t1)".
        (* load r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_load_success _ _ _ RX Local (a-120) (a-150) (a-123) (inl w_3) _ _ RX Local (a-120) (a-150) (a-128) (a-124)
                  with "[HPC Ha128 Hr_t1 Hr_stk Ha123]");
         try addr_succ;
         first (rewrite -i_3; apply decode_encode_inv);
         [eauto|eauto|(constructor; auto; split; done)|auto|auto|iFrame|].
        iEpilogue "(HPC & Hr_stk & Ha123 & Hr_t1 & Ha128)".
        (* sub r_t1 0 1 *)
        destruct ((a-128) =? (a-123))%a eqn:Hcontr;[inversion Hcontr|clear Hcontr].
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_add_sub_lt_success _ r_t1 _ _ (a-120) (a-150) (a-124) (inl w_4a)
                  with "[HPC Hr_t1 Ha124]");
          try addr_succ;
          first (right; left; rewrite -i_4a; apply decode_encode_inv);
          [apply Hrx|constructor; auto; split; done| | ]. 
        iFrame. iSplit; auto.
        destruct (reg_eq_dec r_t1 PC) eqn:Hcontr;[inversion Hcontr|clear Hcontr].
        assert ((a-124 + 1)%a = Some (a-125)) as ->; [addr_succ|].
        rewrite -i_4a decode_encode_inv.
        iEpilogue "(HPC & Ha124 & _ & _ & Hr_t1)".
        (* Lea r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_reg _ RX Local (a-120) (a-150) (a-125) (a-126) (inl w_4b) _ _
                                   RWLX Local (a-120) (a-150) (a-128) (-1) (a-127)
                  with "[HPC Hr_t1 Hr_stk Ha125]");
          try addr_succ;
          first (rewrite -i_4b; apply decode_encode_inv); first apply Hrx; 
          first (constructor; auto; split; done); auto.
        iFrame. iEpilogue "(HPC & Ha125 & Hr_t1 & Hr_stk)".
        (* Load PC r_t1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_load_success_PC _ r_stk RX Local (a-120) (a-150) (a-126) (inl w_4c)
                                   RWLX Local (a-120) (a-150) (a-127) _ _ _ _ (a-78) (a-79)
                  with "[HPC Hr_stk Ha126 Ha127]");
          try addr_succ;
          first (rewrite -i_4c; apply decode_encode_inv);
          first apply Hrx; first apply PermFlows_refl;
          first (constructor; auto; split; done); auto.
        iFrame. iEpilogue "(HPC & Ha126 & Hr_stk & Ha127)".
        (* we don't want to close the stack invariant yet, as we will now need to pop it *)
        (* iMod ("Hcls" with "[$Ha120 $Ha121 $Ha122 $Ha123 $Ha124 $Ha125 $Ha126 $Ha127 $Ha128 $Hna]") as "Hna". *)
        (* go through rest of the program. We will now need to open the invariant one instruction at a time *)
        (* sub r_t1 0 7 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "[>Ha79 Hprog_rest]" "Hcls'".
        iApply (wp_add_sub_lt_success _ r_t1 _ _ _ _ (a-79)
                  with "[HPC Hr_t1 Ha79]");
          first (right; left; apply sub_z_z_i); first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done); auto. 
        iFrame. iSplit; auto. iNext.
        destruct (reg_eq_dec r_t1 PC) eqn:Hcontr;[inversion Hcontr|clear Hcontr].
        assert ((a-79 + 1)%a = Some (a-80)) as ->; [addr_succ|].
        rewrite sub_z_z_i.
        iIntros "(HPC & Ha79 & _ & _ & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *) 
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & >Ha80 & Hprog_rest)" "Hcls'".
        iApply (wp_lea_success_reg _ _ _ _ _ (a-80) (a-81) _ r_stk r_t1 RWLX _ _ _ (a-127) (-7)%Z (a-120)
                  with "[HPC Hr_t1 Hr_stk Ha80]");
          try addr_succ;
          first apply lea_r_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Ha80 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* load r_t30 r_stk *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & >Ha81 & Hprog_rest)" "Hcls'".
        iApply (wp_load_success _ r_t30 _ _ _ _ _ (a-81) _ _ _ RWLX Local (a-120) (a-150) (a-120) (a-82)
                  with "[HPC Ha81 Ha120 Hr_t30 Hr_stk]");
          try addr_succ;
          first apply load_r_i; try apply PermFlows_refl; 
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done); auto.
        iFrame. iNext. iIntros "(HPC & Hr_t30 & Ha81 & Hr_stk & Ha120)"; iSimpl.  
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* we will not use the local stack anymore, so we may close the na_inv *)
        iMod ("Hcls" with "[$Ha120 $Ha121 $Ha122 $Ha123 $Ha124 $Ha125 $Ha126 $Ha127 $Ha128 $Hna]") as "Hna".
        (* we will now make the assertion that r_t30 points to 1 *)
        (* sub r_t1 0 1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & >Ha82 & Hprog_rest)" "Hcls'".
        iApply (wp_add_sub_lt_success _ r_t1 _ _ _ _ (a-82)
                  with "[HPC Hr_t1 Ha82]");
          first (right; left; apply sub_z_z_i); first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done); auto. 
        iFrame. iSplit; eauto. iNext.
        destruct (reg_eq_dec r_t1 PC) eqn:Hcontr;[inversion Hcontr|clear Hcontr].
        assert ((a-82 + 1)%a = Some (a-83)) as ->; [addr_succ|].
        rewrite sub_z_z_i.
        iIntros "(HPC & Ha82 & _ & _ & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & >Ha83 & Hprog_rest)" "Hcls'".
        iApply (wp_lea_success_reg _ _ _ _ _ (a-83) (a-84) _ r_stk r_t1 RWLX _ _ _ (a-120) (-1)%Z (a-119)
                  with "[HPC Hr_t1 Hr_stk Ha83]");
          try addr_succ;
          first apply lea_r_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Ha83 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* move r_t1 PC *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & >Ha84 & Hprog_rest)" "Hcls'".
        iApply (wp_move_success_reg_fromPC _ _ _ _ _ (a-84) (a-85) _ r_t1
                  with "[HPC Hr_t1 Ha84]");
          try addr_succ;
          first apply move_r_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Ha84 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_t1 5 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & >Ha85 & Hprog_rest)" "Hcls'".
        iApply (wp_lea_success_z _ _ _ _ _ (a-85) (a-86) _ r_t1 pc_p _ _ _ (a-84) 5 (a-89)
               with "[HPC Ha85 Hr_t1]");
          try addr_succ;
          first apply lea_z_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done); first auto. 
        { inversion Hvpc0 as [?????? Hpc_p];
            destruct Hpc_p as [Hpc_p | [Hpc_p | Hpc_p] ]; congruence. }
        iFrame. iNext. iIntros "(HPC & Ha85 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* sub r_t30 r_t30 1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & >Ha86 & Hprog_rest)" "Hcls'".
        iApply (wp_add_sub_lt_success _ r_t30 _ _ _ _ (a-86)
                  with "[HPC Ha86 Hr_t30]"); 
          first (right;left;apply sub_r_z_i); first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done); auto. 
        iFrame. iSplit; auto. iNext.
        destruct (reg_eq_dec r_t30 PC) eqn:Hcontr; [inversion Hcontr|clear Hcontr].
        assert ((a-86 + 1)%a = Some (a-87)) as ->;[addr_succ|].
        destruct (reg_eq_dec r_t30 r_t30) eqn:Hcontr;[clear Hcontr| inversion Hcontr].
        rewrite sub_r_z_i. 
        iIntros "(HPC & Ha86 & _ & _ & Hr_t30 )".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $ Ha86 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* jnz r_t1 r_t30 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & Ha86 & >Ha87 
        & Hprog_rest)" "Hcls'".
        iApply (wp_jnz_success_next _ r_t1 r_t30 _ _ _ _ (a-87) (a-88)
                  with "[HPC Ha87 Hr_t30]");
          try addr_succ;
          first apply jnz_i; first apply PermFlows_refl;
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done).
        iFrame. iNext. iIntros "(HPC & Ha87 & Hr_t30)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Ha86 $Ha87 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* halt *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & Ha86 & Ha87 & >Ha88
        & Hprog_rest)" "Hcls'".
        iApply (wp_halt _ _ _ _ _ (a-88) with "[HPC Ha88]");
          first apply halt_i; first apply PermFlows_refl; 
          first (apply isCorrectPC_bounds with (a-0) (a-110); eauto; split; done).
        iFrame. iNext. iIntros "(HPC & Ha88)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Ha86 $Ha87 $Ha88 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* halted: need to show post condition *)
        iApply wp_value. iIntros "_".
        evar (r'' : gmap RegName Word).
        instantiate (r'' := <[PC    := inr (pc_p, pc_g, pc_b, pc_e, (a-88))]>
                           (<[r_t1  := inr (pc_p, pc_g, pc_b, pc_e, (a-89))]>
                           (<[r_t30 := inl 0%Z]>
                           (<[r_stk := inr (RWLX, Local, (a-120), (a-150), (a-119))]> r')))). 
        destruct W' as [fs'' fr'']. 
        iExists r'',fs'',fr''.        
        iFrame. iSplit;[|iSplit].
        + iDestruct "Hfull'" as %Hfull'.
          iPureIntro.
          intros r0. rewrite /r''.
          destruct (decide (PC = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_t1 = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_t30 = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_stk = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto.
        + rewrite /r''.
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I r'' PC
                       with "[-]") as "Hmreg'"; auto.
          { by rewrite lookup_insert. }
          iFrame. do 2 rewrite delete_insert_delete.
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I
                        (delete PC (<[r_t1:=inr (pc_p, pc_g, pc_b, pc_e, a-89)]>
                         (<[r_t30:=inl 0%Z]>
                          (<[r_stk:=inr (RWLX, Local, a-120, a-150, a-119)]> r')))) r_t1
                       with "[-]") as "Hmreg'"; auto.
          { rewrite lookup_delete_ne; auto. by rewrite lookup_insert. }
          iFrame. do 2 rewrite (delete_commute _ r_t1 PC).
          rewrite delete_insert_delete.
          do 2 rewrite (delete_commute _ PC r_t1).
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I
                        (delete r_t1 (delete PC
                            (<[r_t30:=inl 0%Z]>
                             (<[r_stk:=inr (RWLX, Local, a-120, a-150, a-119)]> r')))) r_stk
                       with "[-]") as "Hmreg'"; auto.
          { repeat (rewrite lookup_delete_ne; auto).
            rewrite lookup_insert_ne; auto. by rewrite lookup_insert. }
          iFrame. repeat rewrite (delete_commute _ r_stk _).
          rewrite insert_commute; auto. 
          rewrite delete_insert_delete; auto. 
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I
                  (delete r_t1 (delete PC (delete r_stk (<[r_t30:=inl 0%Z]> r')))) r_t30
                       with "[-]") as "Hmreg'"; auto.
          { repeat (rewrite lookup_delete_ne; auto). by rewrite lookup_insert. }
          iFrame. repeat rewrite (delete_commute _ r_t30 _).  
          rewrite delete_insert_delete. iFrame. 
        + iPureIntro. apply related_sts_priv_refl. 
      - rewrite Hr_t30. 
        assert (r !! r_t30 = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some fixpoint_interp1_eq. iSimpl. 
        iIntros (_). 
        iExists _,_,_,_. iSplit; [eauto|].
        iIntros (r' W' Hrelated).
        iAlways. rewrite /enter_cond.
        iNext. iApply fundamental.
        iLeft. done.
        iExists RX. iSplit; auto. 
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        assert (r !r! r1 = inl 0%Z) as Hr1.
        { rewrite /RegLocate.
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
        rewrite Hr1 fixpoint_interp1_eq. iPureIntro. eauto.         
    }
    iAssert (((interp_reg interp) _ r))%I as "#HvalR";[iSimpl;auto|].
    iSpecialize ("Hvalid" with "[HvalR Hmaps Hs Hna Hr]").
    { iFrame "∗ #". } 
    iDestruct "Hvalid" as (p' g b0 e1 a0 Heq) "Ho". 
    inversion Heq; subst. rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros "_"; iFrame. Unshelve. eauto. 
  Qed. 


End lse.
