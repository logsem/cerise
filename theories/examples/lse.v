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

  Ltac iContiguous_bounds i j :=
    eapply contiguous_between_middle_bounds' with (a0 := i) (an := j);
    [ eauto | cbn; solve [ repeat constructor ] ].

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_bounds_withinBounds a0 an :=
    apply isWithinBounds_bounds_alt' with a0 an; auto; [];
    iContiguous_bounds a0 an.

  Lemma isCorrectPC_range_npE p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p ≠ E.
  Proof.
    intros HH1 HH2. 
    destruct (isCorrectPC_range_perm _ _ _ _ _ _ HH1 HH2) as [?| [?|?] ]; 
      congruence.
  Qed.

  Ltac isWithinBounds := rewrite /withinBounds; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; simpl; auto.

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

   Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

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

  Lemma push_z_instrs_extract a i j z prog p' :
    contiguous_between a i j →
    ([∗ list] a_i;w_i ∈ a; (push_z_instrs r_stk z ++ prog), a_i ↦ₐ[p'] w_i) -∗
    ∃ a' push2 a_rest,
      (([∗ list] a_i;w_i ∈ [i; push2];push_z_instrs r_stk z, a_i ↦ₐ[p'] w_i) ∗
       [∗ list] a_i;w_i ∈ a'; prog, a_i ↦ₐ[p'] w_i) ∗
       ⌜ a = [i; push2] ++ a'
         ∧ (i + 1 = Some push2)%a
         ∧ (push2 + 1 = Some a_rest)%a
         ∧ contiguous_between a' a_rest j ⌝.
  Proof.
    intros. iIntros "HH".
    iDestruct (contiguous_between_program_split with "HH") as (a_push a' a_rest) "(Hpush & ? & #Hcont)"; eauto.
    iDestruct "Hcont" as %(Hcont1 & ? & -> & Hrest).
    iDestruct (big_sepL2_length with "Hpush") as %Hpushlength.
    destruct (contiguous_2 a_push) as (push1 & push2 & -> & Ha12); auto.
    { rewrite contiguous_iff_contiguous_between; eauto. }
    assert (push1 = i) as ->. { inversion Hcont1; auto. }
    iExists a', push2, a_rest. iFrame. iPureIntro. repeat split; eauto.
    cbn in Hrest. revert Ha12 Hrest; clear. solve_addr.
  Qed.

  Ltac iPush_z prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let push2 := fresh "push2" in
    let Ha1 := fresh "Ha1" in
    let Ha2 := fresh "Ha2" in
    let Ha := fresh "Ha" in
    iDestruct (push_z_instrs_extract with prog) as (a_rest push2 cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha2 & Ha);
    iApply (push_z_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha"; eauto;
    clear Ha1 Ha2; last iRename "Hprog" into prog.
    
        
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
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between f2_addrs a_first a_last ->
    
    (* Stack assumptions *)
    (0%a ≤ e_r)%Z ∧ (0%a ≤ b_r)%Z -> (* this assumption will not be necessary once addresses are finite *)
    region_size b_r e_r > 11 -> (* we must assume the stack is large enough for needed local state *)
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
    iIntros (Hvpc Hf2 Hbounds Hsize Hb_r' Hdom φ)
            "(Hr_stk & Hr_gen & Hstack & Hflag & Hna & Hr1 & #Hadv & HPC & Hf2 & Hs & Hr) Hφ /=".
    (* Getting some general purpose regiters *)
    iDestruct "Hr_gen" as (wsr) "Hr_gen". 
    (* Splitting the stack into own and adv parts *)
    assert (contiguous (region_addrs b_r e_r)) as Hcont_stack;[apply region_addrs_contiguous|].
    assert (contiguous_between (region_addrs b_r e_r) b_r e_r) as Hcontiguous.
    { apply contiguous_between_of_region_addrs; auto. rewrite /region_size in Hsize. solve_addr. }
    iDestruct "Hstack" as (ws) "Hstack". 
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 9)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { rewrite region_addrs_length in Hlength; auto. rewrite Hlength in Hsize. 
      do 9 (destruct ws as [|? ws]; [simpl in Hsize; lia|]).
           by exists [w;w0;w1;w2;w3;w4;w5;w6;w7],ws. }
    rewrite Happ.
    iDestruct (contiguous_between_program_split with "Hstack") as (stack_own stack_adv stack_own_last) "(Hstack_own & Hstack_adv & #Hcont)"; [eauto|].
    iDestruct "Hcont" as %(Hcont1 & Hcont2 & Hstack_eq & Hlink).
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_own. rewrite Hlength' in Hlength_own.
    rewrite Hstack_eq in Hcontiguous.
    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hf2") as %Hlength_f2.
    iDestruct (big_sepL2_length with "Hstack_adv") as %Hlength_adv.
    (* Getting the top adress on the stack *)
    destruct stack_own as [|a0 stack_own]; [inversion Hlength_own|]; destruct ws_own as [|w ws_own];[inversion Hlength'|].
    assert ((region_addrs b_r e_r) !! 0 = Some b_r) as Hfirst_stack.
    { apply region_addrs_first. revert Hsize; clear. rewrite /region_size. solve_addr. }
    rewrite Hstack_eq /= in Hfirst_stack. inversion Hfirst_stack as [Heq]. subst b_r. 
    iDestruct "Hstack_own" as "[Ha Hstack_own]".
    (* push 1 *)
    iPush_z "Hf2";[|apply PermFlows_refl|..].
    { split; iCorrectPC a_first a_last. }
    { isWithinBounds;[lia|]. subst. revert Hsize;clear. rewrite /region_size; solve_addr. }
    iNext. iIntros "(HPC & Hi & Hr_stk & Hb_r)".
    (* Prepare the scall prologue macro *)
    destruct stack_own as [|stack_own_b stack_own];[inversion Hlength_own|].
    assert ((stack_own_b :: stack_own) = region_addrs stack_own_b stack_own_last) as ->.
    { apply region_addrs_of_contiguous_between; auto. inversion Hcont1 as [|????? Hcont1']; subst; auto.
      apply contiguous_between_cons_inv_first in Hcont1' as Heq. subst; auto. }
    assert (stack_adv = region_addrs stack_own_last e_r) as ->.
    { apply region_addrs_of_contiguous_between; auto. }
    iDestruct (contiguous_between_program_split with "Hf2") as (scall_prologue rest0 s_last)
                                                         "(Hscall & Hf2 & #Hcont)"; [eauto|..].
    clear Hfirst_stack.
    iDestruct "Hcont" as %(Hcont_scall & Hcont_rest0 & Hrest_app & Hlink'). subst a_rest.
    iDestruct (big_sepL2_length with "Hscall") as %Hscall_length. simpl in Hscall_length.
    assert ((stack_own_b + 8)%a = Some stack_own_last) as Hstack_own_bound.
    { rewrite -(addr_add_assoc a0 _ 1);[|iContiguous_next Hcont1 0]. assert ((1 + 8) = 9)%Z as ->;[done|].
      rewrite Hlength_own in Hlink. revert Hlink; clear; solve_addr. }
    assert (∃ a, (stack_own_b + 7)%a = Some a) as [stack_own_end Hstack_own_bound'].
    { revert Hstack_own_bound. clear. intros H. destruct (stack_own_b + 7)%a eqn:Hnone; eauto. solve_addr. }
    assert (cont < s_last)%a as Hcontlt.
    { revert Hscall_length Hlink'. clear. solve_addr. }
    assert (a_first <= cont)%a as Hcontge.
    { apply region_addrs_of_contiguous_between in Hcont_scall. simplify_eq. revert Hscall_length Hf2 Hcontlt. clear =>Hscall_length Hf2 Hcontlt.
      apply contiguous_between_middle_bounds with (i := 2) (ai := cont) in Hf2;[solve_addr|simpl].
      rewrite lookup_app_l;[|rewrite Hscall_length;lia]. by apply region_addrs_first. 
    }
    (* assert that the stack bounds are within bounds *)
    assert (withinBounds (RWLX,Local,a0,e_r,a0) = true ∧ withinBounds (RWLX,Local,a0,e_r,stack_own_last) = true) as [Hwb1 Hwb2].
    { split; isWithinBounds; first lia.
      - revert Hlength. rewrite Happ app_length Hlength' region_addrs_length /region_size. clear. solve_addr.
      - by eapply contiguous_between_bounds.
      - apply contiguous_between_bounds in Hcont2.
        revert Happ Hlength' Hsize Hlength_adv Hlength_own Hcont2. rewrite -region_addrs_length Hstack_eq app_length. clear.
        rewrite region_addrs_length /region_size. solve_addr.
    }        
    iApply (scall_prologue_spec with "[-]");
      last ((iFrame "HPC Hr_stk Hscall"); iSplitL "Hr_gen";[iNext;simpl;iExists wsr;iFrame|
                                          iSplitL "Hstack_own";[iNext;iExists ws_own;iFrame|
                                                                iSplitL "Hstack_adv";[iNext;iExists ws_adv;iFrame|] ] ]);
      [| |apply Hwb2|apply Hbounds|apply Hcont_scall|apply PermFlows_refl|iNotElemOfList|iContiguous_next Hcont1 0|apply Hstack_own_bound'|apply Hstack_own_bound| |done|..].
    { assert (s_last <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest0|].
      intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      revert Hle Hcontlt Hcontge Hmid. clear; intros. split; solve_addr. }
    { simplify_eq. iContiguous_bounds_withinBounds a0 stack_own_last. }
    { assert (12 + 65 = 77)%Z as ->;[done|]. rewrite Hscall_length in Hlink'. done. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hstack_adv & _)".
    iDestruct (big_sepL2_length with "Hf2") as %Hf2_length. simpl in Hf2_length.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last a_last) as Hvpc1.
    { intros mid Hmid. assert (a_first <= s_last)%a as Hle;[apply contiguous_between_bounds in Hcont_scall; revert Hcont_scall Hcontge;clear; solve_addr|].
      apply isCorrectPC_inrange with a_first a_last; auto.
      revert Hmid Hle. clear. solve_addr. }
    (* jmp r_t30 *)
    iPrologue rest0 Hf2_length "Hf2".
    assert (a1 = s_last) as Heq;[by apply contiguous_between_cons_inv_first in Hcont_rest0|].
    subst s_last. 
    iApply (wp_jmp_success with "[$Hinstr $Hr1 $HPC]");
      [apply jmp_i|apply PermFlows_refl|iCorrectPC a1 a_last|..].
    iEpilogue "(HPC & _ & Hr1)"; iSimpl in "HPC".
    (* We have now arrived at the interesting part of the proof: namely the unknown 
       adversary code. In order to reason about unknown code, we must apply the 
       fundamental theorem. To this purpose, we must first define the stsf that will 
       describe the behavior of the memory. *)
    evar (r : gmap RegName Word).
    instantiate (r := <[PC    := inl 0%Z]>
                     (<[r_stk := inr (RWLX, Local, stack_own_last, e_r, stack_own_end)]>
                     (<[r_t0  := inr (E, Local, a0, e_r, stack_own_b)]>
                     (<[r_t30 := inr (E, Global, b, e, a)]>
                     (create_gmap_default
                        (list_difference all_registers [PC; r_stk; r_t0; r_t30]) (inl 0%Z)))))).
    evar (W_stk : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
    instantiate (W_stk := (std_update_temp_multiple W (region_addrs stack_own_last e_r))).
    assert (related_sts_pub_world W W_stk) as Hrelated_alloc.
    { rewrite /W_stk. apply related_sts_pub_update_multiple;[apply region_addrs_NoDup|].
      rewrite Hstack_eq in Hdom. apply Forall_app in Hdom as [_ Hdom]. done. }
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
    iAssert (|={⊤}=> ([∗ list] a0 ∈ region_addrs stack_own_last e_r,
                     read_write_cond a0 RWLX (fixpoint interp1)) ∗ region _ ∗ sts_full_world sts_std _)%I
                                           with "[Hstack_adv Hr Hs]" as ">(#Hstack_adv & Hr & Hs)". 
    { iApply region_addrs_zeroes_alloc; auto; [|iFrame]. rewrite /std_sta /std_rel /=.
      rewrite Hstack_eq in Hdom. by apply Forall_app in Hdom as [_ Hdom]. }
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
        assert (r !! r_stk = Some (inr (RWLX, Local, stack_own_last, e_r, stack_own_end))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk fixpoint_interp1_eq. (* iSimpl.  *)
        iIntros (_). (* iAlways. iExists _,_,_,_. (iSplitR; [eauto|]). *)
        iExists RWLX. iSplitR; [auto|].
        iSplitR.
        { iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Helem) "Hr". iFrame.
          iPureIntro. by apply std_update_temp_multiple_lookup with k. }
        iAlways.
        rewrite /exec_cond.
        iIntros (a2 r' W' Ha0 HWW'). iNext.
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
        assert (r !! r_t0 = Some (inr (E, Local, a0, e_r, stack_own_b))) as Hr_t0; auto. 
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
        assert (exists stack_new, (stack_new + 1)%a = Some stack_own_end) as [stack_new Hstack_new].
        { revert Hstack_own_bound'. clear. intros H. destruct (stack_own_b + 6)%a eqn:Hsome;[|solve_addr].
          exists a. solve_addr. }
        (* step through instructions in activation record *)
        iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
          [|auto|iContiguous_next Hcont_rest0 0|apply Hstack_new|revert Hstack_own_bound Hstack_own_bound'; clear; solve_addr|..].
        { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb2.
          apply (contiguous_between_middle_bounds _ 1 stack_own_b) in Hcont1;[|auto]. revert Hwb2 Hcont1 Hmid. clear. solve_addr.
        }
        iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
        iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
        iDestruct "Hr_t1" as (wrt1) "Hr_t1". 
        (* we don't want to close the stack invariant yet, as we will now need to pop it *)
        (* go through rest of the program. We will now need to open the invariant one instruction at a time *)
        (* sub r_t1 0 7 *)
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "[>Hinstr Hprog_rest]" "Hcls'".
        iApply (wp_add_sub_lt_success_z_z with "[$HPC $Hr_t1 $Hinstr]");
          [apply sub_z_z_i|right;left;eauto|iContiguous_next Hcont_rest0 1|apply PermFlows_refl|iCorrectPC a1 a_last|..]. 
        iNext. iIntros "(HPC & Hinstr & Hr_t1)".
        iMod ("Hcls'" with "[$Hinstr $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *) 
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "(Ha79 & >Ha80 & Hprog_rest)" "Hcls'".
        assert ((stack_new + (0 - 7))%a = Some a0) as Hpop.
        { assert ((a0 + 1)%a = Some stack_own_b) as Ha0;[iContiguous_next Hcontiguous 0|]. 
          revert Ha0 Hstack_own_bound' Hstack_new. clear. solve_addr. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Ha80]");
          [apply lea_r_i|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest0 2|apply Hpop|auto..].
        iNext. iIntros "(HPC & Ha80 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* load r_t30 r_stk *)
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & >Ha81 & Hprog_rest)" "Hcls'".
        iInv (nroot.@"local") as ">Hb_r" "Hcls''".
        iAssert (⌜(a0 =? a4)%a = false⌝)%I as %Hne.
        { destruct (a0 =? a4)%a eqn:Heq;auto. apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
          iDestruct (cap_duplicate_false with "[$Ha81 $Hb_r]") as "Hfalse";[|done].
          apply isCorrectPC_range_perm in Hvpc1.
          destruct pc_p;auto. destruct Hvpc1 as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr.
          apply (contiguous_between_middle_bounds _ 0 a1) in Hcont_rest0 as [_ Hlt]; auto. 
        }
        iApply (wp_load_success with "[$HPC $Ha81 Hb_r $Hr_t30 $Hr_stk]");
          [apply load_r_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC a1 a_last|auto|iContiguous_next Hcont_rest0 3|auto|rewrite Hne;iFrame|rewrite Hne].
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
        iApply (wp_add_sub_lt_success_z_z with "[$HPC Hr_t1 $Ha82]");
          [apply sub_z_z_i|right;left;eauto|iContiguous_next Hcont_rest0 4|apply PermFlows_refl|iCorrectPC a1 a_last|iSimpl;iFrame;eauto|].
        iNext. iIntros "(HPC & Ha82 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *)
        iPrologue_pre rest0 Hf2_length. 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & >Ha83 & Hprog_rest)" "Hcls'".
        assert ((a0 + (0 - 1))%a = Some b_r') as Hb_r'_decr.
        { revert Hb_r'. clear. solve_addr. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Ha83]");
          [apply lea_r_i|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest0 5|apply Hb_r'_decr|auto..].
        iNext. iIntros "(HPC & Ha83 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* move r_t1 PC *)
        iPrologue_pre rest0 Hf2_length.
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & >Ha84 & Hprog_rest)" "Hcls'".
        iApply (wp_move_success_reg_fromPC with "[$HPC $Hr_t1 $Ha84]");
          [apply move_r_i|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest0 6|auto|..].
        iNext. iIntros "(HPC & Ha84 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_t1 5 *)
        iPrologue_pre rest0 Hf2_length.
        do 3 (destruct rest0;[inversion Hf2_length|]).
        assert ((a7 + 5)%a = Some a12) as Hincr;[apply (contiguous_between_incr_addr_middle _ _ _ 6 5 _ _ Hcont_rest0); auto|].
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & >Ha85 & Hprog_rest)" "Hcls'".
        iApply (wp_lea_success_z with "[$HPC $Ha85 $Hr_t1]");
          [apply lea_z_i|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest0 7|apply Hincr|auto|..].
        { apply isCorrectPC_range_npE in Hvpc1; auto. apply (contiguous_between_middle_bounds _ 0 a1) in Hcont_rest0 as [_ Hlt]; auto. }
        iNext. iIntros "(HPC & Ha85 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* sub r_t30 r_t30 1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & >Ha86 & Hprog_rest)" "Hcls'".
        iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Ha86 $Hr_t30]");
          [apply sub_r_z_i|right;left;eauto|iContiguous_next Hcont_rest0 8|apply PermFlows_refl|iCorrectPC a1 a_last|..]. 
        iNext. iIntros "(HPC & Ha86 & Hr_t30 )".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $ Ha86 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* jnz r_t1 r_t30 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & Ha86 & >Ha87 
        & Hprog_rest)" "Hcls'".
        iApply (wp_jnz_success_next with "[$HPC $Ha87 $Hr_t30]");
          [apply jnz_i|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest0 9|..].
        iNext. iIntros "(HPC & Ha87 & Hr_t30)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Ha86 $Ha87 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* halt *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & Ha86 & Ha87 & >Ha88
        & Hprog_rest)" "Hcls'".
        iApply (wp_halt with "[$HPC $Ha88]");
          [apply halt_i|apply PermFlows_refl|iCorrectPC a1 a_last|]. 
        iNext. iIntros "(HPC & Ha88)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Ha86 $Ha87 $Ha88 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* halted: need to show post condition *)
        iApply wp_value. iIntros "_".
        evar (r'' : gmap RegName Word).
        instantiate (r'' := <[PC    := inr (pc_p, pc_g, pc_b, pc_e, a11)]>
                           (<[r_t1  := inr (pc_p, pc_g, pc_b, pc_e, a12)]>
                           (<[r_t30 := inl 0%Z]>
                           (<[r_stk := inr (RWLX, Local, a0, e_r, b_r')]> r')))). 
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
                        (delete PC (<[r_t1:=inr (pc_p, pc_g, pc_b, pc_e, a12)]>
                         (<[r_t30:=inl 0%Z]>
                          (<[r_stk:=inr (RWLX, Local, a0, e_r, b_r')]> r')))) r_t1
                       with "[-]") as "Hmreg'"; auto.
          { rewrite lookup_delete_ne; auto. by rewrite lookup_insert. }
          iFrame. do 2 rewrite (delete_commute _ r_t1 PC).
          rewrite delete_insert_delete.
          do 2 rewrite (delete_commute _ PC r_t1).
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I
                        (delete r_t1 (delete PC
                            (<[r_t30:=inl 0%Z]>
                             (<[r_stk:=inr (RWLX, Local, a0, e_r, b_r')]> r')))) r_stk
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
    iIntros "_"; iFrame. 
  Qed. 


End lse.
