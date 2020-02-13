From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental. 
From cap_machine.examples Require Import stack_macros scall. 

Section lse.
   Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.


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

   Ltac iPrologue_pre l Hl :=
     destruct l; [inversion Hl|]; iApply (wp_bind (fill [SeqCtx])).
   
   Ltac iPrologue l Hl prog := 
     iPrologue_pre l Hl;
     iDestruct prog as "[Hinstr Hprog]".     

  Ltac iEpilogue intro_ptrn :=
    iNext; iIntros intro_ptrn; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac iLookupR Hl :=
    rewrite /= lookup_app_r;rewrite Hl /=;auto. 
    
        
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
    (* Finally, we must assume that the stack is currently not in the world *)
    Forall (λ a, (countable.encode a) ∉ dom (gset positive) (std_sta W)
                      ∧ (countable.encode a) ∉ dom (gset positive) (std_rel W)) (region_addrs b_r e_r) ->
    
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
      ∗ ([∗ list] a ∈ (region_addrs b e), (read_write_cond a RX interp)
                                             ∧ ⌜region_state_nwl W a Global⌝
                                             ∧ ⌜region_std W a⌝)
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
    iIntros ([Hvpc0 Hvpc93] Hf2 [Ha_first Ha_last] Hbounds Hle Hsize Hb_r' Hdom φ)
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
    iDestruct (big_sepL2_length with "Hf2") as %Hf2_length. simpl in Hf2_length. 
    (* jmp r_t30 *)
    iPrologue rest0 Hf2_length "Hf2". simpl in Hrest0_first; inversion Hrest0_first; subst.
    iApply (wp_jmp_success with "[$Hinstr $Hr1 $HPC]");
      [apply jmp_i|apply PermFlows_refl|..].
    { apply isCorrectPC_bounds_alt with a_first a_last; auto. iContiguous_bounds a_first rest0_first a_last 79 Hf2;
      do 2 (rewrite lookup_app_r;[simpl|simpl;lia]); by rewrite Hscall_length. }
    iEpilogue "(HPC & _ & Hr1)"; iSimpl in "HPC".
    (* We have now arrived at the interesting part of the proof: namely the unknown 
       adversary code. In order to reason about unknown code, we must apply the 
       fundamental theorem. To this purpose, we must first define the stsf that will 
       describe the behavior of the memory. *)
    evar (r : gmap RegName Word).
    instantiate (r := <[PC    := inl 0%Z]>
                     (<[r_stk := inr (RWLX, Local, s_first, e_r, s_last)]>
                     (<[r_t0  := inr (E, Local, b_r, e_r, stack_own_b)]>
                     (<[r_t30 := inr (E, Global, b, e, a)]>
                     (create_gmap_default
                        (list_difference all_registers [PC; r_stk; r_t0; r_t30]) (inl 0%Z)))))).
    evar (W_stk : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
    instantiate (W_stk := (std_update_temp_multiple W (region_addrs s_first e_r))).
    assert (related_sts_pub_world W W_stk) as Hrelated_alloc.
    { rewrite /W_stk. apply related_sts_pub_update_temp_multiple;[apply region_addrs_NoDup|].
      rewrite Hstackeq in Hdom. apply Forall_app in Hdom as [_ Hdom]. done. }
    iAssert (interp_expression r W_stk (inr (RX, Global, b, e, a))) as "Hvalid". 
    { iApply fundamental. iLeft; auto. iExists RX. iSplit;[auto|]. 
      iApply (big_sepL_mono with "Hadv"). iIntros (k y Hsome) "(Hadv & Hperm & Hstd)". iFrame.
      iDestruct "Hstd" as %Hstd'. iDestruct "Hperm" as %Hsta.
      iPureIntro. simpl. split.
      + apply region_state_nwl_monotone_nl with W; auto. by apply related_sts_pub_priv_world.
      + apply related_sts_rel_std with W; auto. by apply related_sts_pub_priv_world.
    } 
    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r))
                          with "[Hr_gen Hr_stk Hr_t0 Hr1 HPC]" as "Hmaps".
    { rewrite /r /registers_mapsto (insert_insert _ PC).
      iApply (big_sepM_insert_2 with "[HPC]"); [iFrame|]. 
      iApply (big_sepM_insert_2 with "[Hr_stk]"); [iFrame|].
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
    iMod (inv_alloc (nroot.@"Hprog") with "Hprog")%I as "#Hprog".
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"Hframe") _ with "Hstack_own") as "#Hlocal".
    (* We will put the local state 1 into a separate invariant *)
    iMod (inv_alloc (nroot.@"local") with "Hb_r")%I as "#Hlocal_one".
    iAssert (|={⊤}=> ([∗ list] a0 ∈ region_addrs s_first e_r,
                     read_write_cond a0 RWLX (fixpoint interp1)) ∗ region _ ∗ sts_full_world sts_std _)%I
                                           with "[Hstack_adv Hr Hs]" as ">(#Hstack_adv & Hr & Hs)". 
    { iApply region_addrs_zeroes_alloc; auto; [|iFrame]. rewrite /std_sta /std_rel /=.
      rewrite Hstackeq in Hdom. by apply Forall_app in Hdom as [_ Hdom]. }
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W_stk (r !r! r1))%I
      with "[-Hs Hmaps Hvalid Hna Hφ Hflag Hr]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_t30 ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_t30)) as Hne.
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_t30)); [by left|right;auto].  
      }
      destruct Hne as [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      - iIntros "%". contradiction.
      - (* invariant for the stack of the adversary *)
        assert (r !! r_stk = Some (inr (RWLX, Local, s_first, e_r, s_last))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk fixpoint_interp1_eq. (* iSimpl.  *)
        iIntros (_). (* iAlways. iExists _,_,_,_. (iSplitR; [eauto|]). *)
        iExists RWLX. iSplitR; [auto|].
        iSplitR.
        { iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Helem) "Hr". iFrame.
          iPureIntro. by apply std_update_temp_multiple_lookup with k. }
        iAlways.
        rewrite /exec_cond.
        iIntros (a0 r' W' Ha0 HWW'). iNext.
        iApply fundamental.
        + iRight. iRight. done.
        + iExists RWLX. iSplit; simpl;auto.
          iApply (big_sepL_mono with "Hstack_adv").
          iIntros (k y Hsome) "Hr".
          iFrame. iPureIntro.
          eapply std_update_temp_multiple_lookup (* with W _ _ _  *)in Hsome as [Hpwl Hstd]. 
          split;[by apply (region_state_pwl_monotone _ _ _ Hstd HWW')|].
          eapply related_sts_rel_std;[|eauto]. apply related_sts_pub_priv_world; auto. 
      - (* continuation *)
        iIntros (_). 
        assert (r !! r_t0 = Some (inr (E, Local, b_r, e_r, stack_own_b))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 fixpoint_interp1_eq. iSimpl. 
        (* prove continuation *)
        (* iExists _,_,_,_. iSplit;[eauto|]. *)
        iAlways.
        rewrite /enter_cond. 
        iIntros (r' W' HWW').
        iNext. iSimpl. 
        (* iExists _,_.  do 2 (iSplit; [eauto|]).*)
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hr & Hs & Hna)". 
        iSplit; [auto|rewrite /interp_conf].
        (* get the PC, currently pointing to the activation record *)
        iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
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
        iMod (na_inv_open logrel_nais ⊤ ⊤ with "Hlocal Hna") as "(>Hframe & Hna & Hcls)";auto. 
        assert (PermFlows RX RWLX) as Hrx;[by rewrite /PermFlows /=|].
        (* prepare the continuation *)
        let a := fresh "a" in destruct rest0 as [|a rest0];[inversion Hf2_length|].
        (* prepare the new stack value *)
        assert (is_Some (s_last + (0 - 1))%a) as [stack_new Hstack_new].
        { do 7 (let a := fresh "a" in destruct stack_own as [|a stack_own];[inversion Hlength_own|]).
          destruct stack_own;[|inversion Hlength_own]. exists a7. simpl in Hs_last; inversion Hs_last; subst.
          rewrite -(addr_add_assoc a7 _ 1);[|iContiguous_next Hstackcont 7]. apply addr_add_0. }
        (* step through instructions in activation record *)
        iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
          [| |auto|iContiguous_next Hcont_rest0 0|apply Hstack_new|..]. 
        { split;[|auto]. split;[apply (incr_list_ge_middle _ 1 _ _ Hstack_own);auto|].
          apply (incr_list_lt_middle_alt _ 1 _ _ Hstackcont); [auto| |rewrite app_length Hlength_own /=;lia].
          rewrite -last_app_eq;[|destruct (region_addrs s_first e_r);[inversion Hs_first|simpl;lia] ].
          apply region_addrs_last. rewrite /region_addrs in Hs_first. destruct (Z_le_dec s_first e_r);[auto|inversion Hs_first]. }
        { split;[|auto]. split;[apply (incr_list_ge_middle _ 8 _ _ Hstack_own);auto|].
          - assert (8 = length (b_r :: stack_own_b :: stack_own) - 1) as ->;[by rewrite Hlength_own|]. by rewrite -last_lookup.
          - assert (s_first <= e_r)%Z as Hle';[rewrite /region_addrs in Hs_first;destruct (Z_le_dec s_first e_r);[auto|inversion Hs_first]|].
            apply next_lt in Hlink. lia. }
        iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
        iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
        iDestruct "Hr_t1" as (wrt1) "Hr_t1". 
        (* we don't want to close the stack invariant yet, as we will now need to pop it *)
        (* go through rest of the program. We will now need to open the invariant one instruction at a time *)
        (* sub r_t1 0 7 *)
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "[>Hinstr Hprog_rest]" "Hcls'".
        iApply (wp_add_sub_lt_success with "[$HPC Hr_t1 $Hinstr]");
          [right; left; apply sub_z_z_i|apply PermFlows_refl| |iSimpl;iFrame;eauto|iSimpl;rewrite sub_z_z_i].
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a0 a_last 80 Hf2; iLookupR Hscall_length. }
        assert ((a0 + 1)%a = Some a1) as ->;[iContiguous_next Hcont_rest0 1|]. 
        iNext. iIntros "(HPC & Hinstr & _ & _ & Hr_t1)".
        iMod ("Hcls'" with "[$Hinstr $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *) 
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "(Ha79 & >Ha80 & Hprog_rest)" "Hcls'".
        assert ((stack_new + (0 - 7))%a = Some b_r) as Hpop.
        { rewrite -(addr_add_assoc b_r _ 7);[apply addr_add_0|].
          rewrite -Hstack_new. assert (7 = 1 + 6)%Z as ->;[lia|]. 
          rewrite (addr_add_assoc b_r stack_own_b 1);[|iContiguous_next Hstack_own 0].
          assert (6 = 7 + (0 - 1))%Z as ->;[lia|]. rewrite (addr_add_assoc stack_own_b s_last 7); auto. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Ha80]");
          [apply lea_r_i|apply PermFlows_refl| |iContiguous_next Hcont_rest0 2|apply Hpop|auto..].
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a1 a_last 81 Hf2; iLookupR Hscall_length. }
        iNext. iIntros "(HPC & Ha80 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* load r_t30 r_stk *)
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & >Ha81 & Hprog_rest)" "Hcls'".
        iInv (nroot.@"local") as ">Hb_r" "Hcls''".
        iAssert (⌜(b_r =? a3)%a = false⌝)%I as %Hne.
        { destruct (b_r =? a3)%a eqn:Heq;auto. apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
          iDestruct (cap_duplicate_false with "[$Ha81 $Hb_r]") as "Hfalse";[|done]. destruct pc_p;auto.
          inversion Hvpc0 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
        iApply (wp_load_success with "[$HPC $Ha81 Hb_r $Hr_t30 $Hr_stk]");
          [apply load_r_i|apply PermFlows_refl|apply PermFlows_refl| |auto|iContiguous_next Hcont_rest0 3|auto|rewrite Hne;iFrame|rewrite Hne].
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a3 a_last 82 Hf2; iLookupR Hscall_length. }
        iNext. iIntros "(HPC & Hr_t30 & Ha81 & Hr_stk & Ha120)"; iSimpl.  
        iMod ("Hcls''" with "[$Ha120]") as "_". iModIntro. 
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* we will not use the local stack anymore, so we may close the na_inv *)
        iMod ("Hcls" with "[$Hframe $Hna]") as "Hna".
        (* we will now make the assertion that r_t30 points to 1 *)
        (* sub r_t1 0 1 *)
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & >Ha82 & Hprog_rest)" "Hcls'".
        iApply (wp_add_sub_lt_success with "[$HPC Hr_t1 $Ha82]");
          [right; left; apply sub_z_z_i|apply PermFlows_refl| |iSimpl;iFrame;eauto|iSimpl;rewrite sub_z_z_i].
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a4 a_last 83 Hf2; iLookupR Hscall_length. }
        assert ((a4 + 1)%a = Some a5) as ->;[iContiguous_next Hcont_rest0 4|]. 
        iNext. iIntros "(HPC & Ha82 & _ & _ & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *)
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & >Ha83 & Hprog_rest)" "Hcls'".
        assert ((b_r + (0 - 1))%a = Some b_r') as Hb_r'_decr.
        { rewrite -(addr_add_assoc b_r' _ 1);[apply addr_add_0|auto]. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Ha83]");
          [apply lea_r_i|apply PermFlows_refl| |iContiguous_next Hcont_rest0 5|apply Hb_r'_decr|auto..].
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a5 a_last 84 Hf2; iLookupR Hscall_length; lia. }
        iNext. iIntros "(HPC & Ha83 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* move r_t1 PC *)
        iPrologue_pre rest0 Hf2_length.
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & >Ha84 & Hprog_rest)" "Hcls'".
        iApply (wp_move_success_reg_fromPC with "[$HPC $Hr_t1 $Ha84]");
          [apply move_r_i|apply PermFlows_refl| |iContiguous_next Hcont_rest0 6|auto|..].
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a6 a_last 85 Hf2; iLookupR Hscall_length; lia. }
        iNext. iIntros "(HPC & Ha84 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_t1 5 *)
        iPrologue_pre rest0 Hf2_length.
        do 3 (destruct rest0;[inversion Hf2_length|]).
        assert ((a6 + 5)%a = Some a11) as Hincr;[apply (contiguous_incr_addr_middle _ 6 5 _ _ Hcont_rest0); auto|].
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & >Ha85 & Hprog_rest)" "Hcls'".
        iApply (wp_lea_success_z with "[$HPC $Ha85 $Hr_t1]");
          [apply lea_z_i|apply PermFlows_refl| |iContiguous_next Hcont_rest0 7|apply Hincr|auto|..].
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a7 a_last 86 Hf2; iLookupR Hscall_length; lia. }
        { inversion Hvpc0 as [?????? Hpc_p]; destruct Hpc_p as [Hpc_p | [Hpc_p | Hpc_p] ]; congruence. }
        iNext. iIntros "(HPC & Ha85 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* sub r_t30 r_t30 1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & >Ha86 & Hprog_rest)" "Hcls'".
        iApply (wp_add_sub_lt_success with "[$HPC $Ha86 Hr_t30]");
          [right;left;apply sub_r_z_i|apply PermFlows_refl| |iSimpl;iFrame;eauto|iSimpl;rewrite sub_r_z_i]. 
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a8 a_last 87 Hf2; iLookupR Hscall_length; lia. }
        assert ((a8 + 1)%a = Some a9) as ->;[iContiguous_next Hcont_rest0 8|]. 
        iNext. iIntros "(HPC & Ha86 & _ & _ & Hr_t30 )".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $ Ha86 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* jnz r_t1 r_t30 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & Ha86 & >Ha87 
        & Hprog_rest)" "Hcls'".
        iApply (wp_jnz_success_next with "[$HPC $Ha87 $Hr_t30]");
          [apply jnz_i|apply PermFlows_refl| |iContiguous_next Hcont_rest0 9|..].
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a9 a_last 88 Hf2; iLookupR Hscall_length; lia. }
        iNext. iIntros "(HPC & Ha87 & Hr_t30)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Ha86 $Ha87 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* halt *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & Ha86 & Ha87 & >Ha88
        & Hprog_rest)" "Hcls'".
        iApply (wp_halt with "[$HPC $Ha88]");
          [apply halt_i|apply PermFlows_refl|..]. 
        { apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a10 a_last 89 Hf2; iLookupR Hscall_length; lia. }
        iNext. iIntros "(HPC & Ha88)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Ha86 $Ha87 $Ha88 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* halted: need to show post condition *)
        iApply wp_value. iIntros "_".
        evar (r'' : gmap RegName Word).
        instantiate (r'' := <[PC    := inr (pc_p, pc_g, pc_b, pc_e, a10)]>
                           (<[r_t1  := inr (pc_p, pc_g, pc_b, pc_e, a11)]>
                           (<[r_t30 := inl 0%Z]>
                           (<[r_stk := inr (RWLX, Local, b_r, e_r, b_r')]> r')))). 
        iFrame. iExists r'',_. iFrame. iSplit;[|iSplit].
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
                        (delete PC (<[r_t1:=inr (pc_p, pc_g, pc_b, pc_e, a11)]>
                         (<[r_t30:=inl 0%Z]>
                          (<[r_stk:=inr (RWLX, Local, b_r, e_r, b_r')]> r')))) r_t1
                       with "[-]") as "Hmreg'"; auto.
          { rewrite lookup_delete_ne; auto. by rewrite lookup_insert. }
          iFrame. do 2 rewrite (delete_commute _ r_t1 PC).
          rewrite delete_insert_delete.
          do 2 rewrite (delete_commute _ PC r_t1).
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I
                        (delete r_t1 (delete PC
                            (<[r_t30:=inl 0%Z]>
                             (<[r_stk:=inr (RWLX, Local, b_r, e_r, b_r')]> r')))) r_stk
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
        + iPureIntro. split; apply related_sts_priv_refl. 
      - rewrite Hr_t30. 
        assert (r !! r_t30 = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some fixpoint_interp1_eq. iSimpl. 
        iIntros (_). 
        iAlways. iIntros (r' W' Hrelated). 
        iNext. iApply fundamental.
        iLeft. done.
        iExists RX. iSplit; simpl; auto.
        iApply (big_sepL_mono with "Hadv").
        iIntros (k y Hsome) "(Ha & Hy & Hstd)". iDestruct "Hy" as %Hy. iDestruct "Hstd" as %Hstd.
        iFrame. iPureIntro.
        assert (related_sts_priv_world W W') as Hrelated_final.
        { eapply related_sts_priv_trans_world;[|apply Hrelated].
          apply related_sts_pub_priv_world. auto. 
        }
        split.
        + apply region_state_nwl_monotone_nl with W; auto.
        + apply related_sts_rel_std with W; auto.
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        assert (r !r! r1 = inl 0%Z) as Hr1.
        { rewrite /RegLocate.
          destruct (r !! r1) eqn:Hsome; rewrite Hsome; last done. rewrite /r in Hsome. 
          do 4 (rewrite lookup_insert_ne in Hsome;auto). 
          assert (Some w0 = Some (inl 0%Z)) as Heq.
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
    iSpecialize ("Hvalid" with "[$HvalR $Hmaps $Hs $Hna $Hr]"); iFrame. 
    iDestruct "Hvalid" as "[_ Ho]". 
    rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros "_"; iFrame. Unshelve. done. 
  Qed. 


End lse.
