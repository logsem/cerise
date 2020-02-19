From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental. 
From cap_machine.examples Require Import region_macros stack_macros scall malloc. 


Section awkward_example.
   Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

   Notation STS := (leibnizO (STS_states * STS_rels)).
   Notation WORLD := (leibnizO (STS * STS)). 
   Implicit Types W : WORLD.
   
   (* choose a special register for the environment and adv pointer *)
   (* note that we are here simplifying the environment to simply point to one location *)      
   Definition r_env : RegName := r_t30.
   Definition r_adv : RegName := r_t28.
   Definition r_self : RegName := r_t29.

   (* Helper lemma to extract registers from a big_sepL2 *)
   Lemma big_sepL2_extract_l {A B : Type} (i : nat) (ai : A) (a : list A) (b : list B) (φ : A -> B -> iProp Σ) :
     a !! i = Some ai ->
     (([∗ list] a_i;b_i ∈ a;b, φ a_i b_i) -∗
     (∃ b', [∗ list] a_i;b_i ∈ (delete i a);b', φ a_i b_i) ∗ ∃ b, φ ai b)%I.
   Proof. 
     iIntros (Hsome) "Hl".
     iDestruct (big_sepL2_length with "Hl") as %Hlength.      
     assert (take i a ++ drop i a = a) as Heqa;[apply take_drop|]. 
     assert (take i b ++ drop i b = b) as Heqb;[apply take_drop|]. 
     rewrite -Heqa -Heqb.
     iDestruct (big_sepL2_app_inv with "Hl") as "[Htake Hdrop]". 
     { apply lookup_lt_Some in Hsome.
       do 2 (rewrite take_length_le;[|lia]). done. 
     }
     apply take_drop_middle in Hsome as Hcons.
     assert (ai :: drop (S i) a = drop i a) as Hh.
     { apply app_inv_head with (take i a). congruence. }
     rewrite -Hh.
     iDestruct (big_sepL2_length with "Hdrop") as %Hlength'.      
     destruct (drop i b);[inversion Hlength'|].
     iDestruct "Hdrop" as "[Hφ Hdrop]".
     iSplitR "Hφ";[|eauto].
     iExists (take i b ++ l). rewrite Hcons. 
     iDestruct (big_sepL2_app with "Htake Hdrop") as "Hl". 
     rewrite delete_take_drop. iFrame.
   Qed.

   (* helper lemma to state that a fresh allocation creates a public future world *)
   Lemma related_sts_pub_fresh (W : STS) a ρ i:
    i ∉ dom (gset positive) W.1 →
    i ∉ dom (gset positive) W.2 →
    related_sts_pub W.1 (<[i:=a]> W.1) W.2 (<[i:=ρ]> W.2).
  Proof.
    intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub. split;[|split;[auto|] ].
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq.
    - apply not_elem_of_dom in Hdom_sta.
      apply not_elem_of_dom in Hdom_rel.
      intros j r1 r2 r1' r2' Hr Hr'.
      destruct (decide (j = i)).
      + subst. rewrite Hr in Hdom_rel. done.
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy.
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.
     
  Ltac isWithinBounds := rewrite /withinBounds; apply andb_true_iff; split; apply Z.leb_le; simpl; auto.

  Ltac isWithinBounds_stack Hcont_stack index :=
    isWithinBounds;[apply (incr_list_ge_middle _ index _ _ Hcont_stack);auto|apply (incr_list_le_middle _ index _ _ Hcont_stack);auto]. 
   
   Ltac iNotElemOfList :=
     repeat (apply not_elem_of_cons; split;[auto|]); apply not_elem_of_nil.  
   
   
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

   Ltac iGet_genpur_reg Hr_gen Hwsr wsr ptr :=
     let w := fresh "wr" in 
     destruct wsr as [? | w wsr]; first (by inversion Hwsr);
     iDestruct Hr_gen as ptr.

   Ltac iCorrectPC a_first a a_last index Hcont :=
     apply isCorrectPC_bounds_alt with a_first a_last;auto;iContiguous_bounds a_first a a_last index Hcont.
    
   (* Recall that the malloc subroutine lies in b_m e_m *)

   (* assume that r1 contains an executable pointer to the malloc subroutine *)
   Definition awkward_preamble_instrs r1 offset_to_awkward :=
     [move_r r_t0 PC;
     lea_z r_t0 3;
     jmp r1;
     move_r r_self PC;
     lea_z r_self offset_to_awkward;
     jmp r_self].
   
   (* assume r1 contains an executable pointer to adversarial code *)
   (* assume r0 contains an executable pointer to the awkward example *)
   Definition awkward_instrs (r0 r1 : RegName) epilogue_off flag_off :=
     [store_z r_env 0] ++
     push_r_instrs r_stk r_env ++
     push_r_instrs r_stk r0 ++
     push_r_instrs r_stk r1 ++
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r1 ++
     pop_instrs r_stk r0 ++
     pop_instrs r_stk r_env ++
     [store_z r_env 1] ++
     push_r_instrs r_stk r_env ++
     push_r_instrs r_stk r0 ++
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r0 ++
     pop_instrs r_stk r_env ++
     (* assert that the cap in r_env points to 1 *)
     [load_r r1 r_env;
     move_r r_t1 PC;
     lea_z r_t1 5; (* offset to assertion failure *)
     sub_r_z r1 r1 1;
     jnz r_t1 r1;
     jmp r0;
     (* failure *)
     move_r r_t1 PC;
     lea_z r_t1 flag_off;
     store_z r_t1 1;
     halt].

   
  
   Definition awkward_preamble a p r1 offset_to_awkward :=
     ([∗ list] a_i;w_i ∈ a;(awkward_preamble_instrs r1 offset_to_awkward), a_i ↦ₐ[p] w_i)%I.
   
   Definition awkward_example (a : list Addr) (p : Perm) (r0 r1 : RegName) epilogue_off flag_off : iProp Σ :=
     ([∗ list] a_i;w_i ∈ a;(awkward_instrs r0 r1 epilogue_off flag_off), a_i ↦ₐ[p] w_i)%I.

   
   Definition awk_inv i a :=
     (∃ x:bool, sts_state_loc i x
           ∗ if x
             then a ↦ₐ[RWX] inl 1%Z
             else a ↦ₐ[RWX] inl 0%Z)%I.

   Definition awk_rel_pub := λ a b, a = false ∨ b = true.
   Definition awk_rel_priv := λ (a b : bool), True.

   Inductive local_state :=
   | First
   | Second
   | Released. 
   Definition local_rel_pub := λ (a b : local_state), a = b.
   Definition local_rel_priv := λ (a b : local_state), (a = First ∧ b = Second) ∨ (a = Second ∧ b = Released). 

   Definition awk_W W i : WORLD := (W.1,(<[i:=countable.encode false]>W.2.1,<[i:=(convert_rel awk_rel_pub,convert_rel awk_rel_priv)]>W.2.2)).

   (* namespace definitions for the regions *)
   Definition regN : namespace := nroot .@ "regN".

   (* the following spec is for the preamble to the awkward example. It allocates the invariant on the malloc'ed region *)
   Lemma g1_spec φ W pc_p pc_g pc_b pc_e (* PC *)
         g1_addrs offset_to_awkward (* g1 *)
         a_first a_last a_cont (* special adresses *) :

     (* PC assumptions *)
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a_first)) ∧
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a_last)) →
     
     (* Program adresses assumptions *)
     contiguous g1_addrs ->
     g1_addrs !! 0 = Some a_first ∧ list.last g1_addrs = Some a_last ->

     (* Address assumptions *)
     (a_first + (3 + offset_to_awkward))%a = Some a_cont ->

     ((* PC *)
       PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      (* assume r_t1 points to a the malloc subroutine *)
      ∗ r_t1 ↦ᵣ inr (E,Global,b_m,e_m,a_m)
      ∗ [[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine r_env 1]]
      (* general purpose registers *)
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [r_t1;PC]; wsr, r_i ↦ᵣ w_i)
      (* program *)
      ∗ awkward_preamble g1_addrs pc_p r_t1 offset_to_awkward
      (* region invariants *)
      ∗ region W
      ∗ sts_full_world sts_std W
      (* continuation *)
      ∗ ▷ ((PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_cont)
          ∗ r_self ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_cont)
          ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_self;r_env]; wsr, r_i ↦ᵣ w_i)    
          ∗ ∃ d, r_env ↦ᵣ inr (RWX,Global,d,d,d)
          ∗ (∃ (i : positive), region (awk_W W i) ∗ sts_full_world sts_std (awk_W W i) ∗ sts_rel_loc i awk_rel_pub awk_rel_priv ∗ (∃ ι, inv ι (awk_inv i d))))
          -∗ WP Seq (Instr Executable) {{ φ }})
      ⊢ WP Seq (Instr Executable) {{ φ }})%I.
   Proof. 
     iIntros ([Hvpc1 Hvpc2] Hcont [Hfirst Hlast] Ha_cont) "(HPC & Hr_t1 & Hmalloc & Hr_gen & Hprog & Hr & Hsts & Hφ)".
     iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
     destruct g1_addrs; [inversion Hprog_length|].
     simpl in Hfirst; inversion Hfirst; subst.
     iDestruct "Hr_gen" as (wsr) "Hr_gen".
     iDestruct (big_sepL2_length with "Hr_gen") as %Hwsr.
     rewrite /all_registers /=. 
     iGet_genpur_reg "Hr_gen" Hwsr wsr "[Hr_t0 Hr_gen]". 
     (* move r_t1 PC *)
     iPrologue g1_addrs Hprog_length "Hprog".
     iApply (wp_move_success_reg_fromPC with "[$HPC $Hinstr $Hr_t0]");
       [apply move_r_i|apply PermFlows_refl|auto|iContiguous_next Hcont 0|auto|].
     iEpilogue "(HPC & Hprog_done & Hr_t0)".
     (* lea r_t0 2 *)
     iPrologue g1_addrs Hprog_length "Hprog".
     destruct g1_addrs;[inversion Hprog_length|].
     assert (a_first + 3 = Some a1)%a as Ha1;[apply (contiguous_incr_addr _ 3 a_first _ Hcont); auto|].
     iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t0]");
       [apply lea_z_i|apply PermFlows_refl|iCorrectPC a_first a a_last 1 Hcont|iContiguous_next Hcont 1|apply Ha1|auto..]. 
     { destruct pc_p; auto. inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
     iEpilogue "(HPC & Ha & Hr_t0)". iCombine "Ha" "Hprog_done" as "Hprog_done". 
     (* jmp r_t1 *)
     iPrologue g1_addrs Hprog_length "Hprog". 
     iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_t1]");
       [apply jmp_i|apply PermFlows_refl|iCorrectPC a_first a0 a_last 2 Hcont|]. 
     iEpilogue "(HPC & Ha0 & Hr_t1)"; iCombine "Ha0" "Hprog_done" as "Hprog_done".
     iSimpl in "HPC". 
     (* malloc subroutine *)
     iApply (malloc_spec W); last iFrame "Hmalloc Hr_t0 HPC".
     iSplitL "Hr_gen Hr_t1".
     { iExists (_ :: wsr). rewrite /all_registers /=. iFrame. }
     iNext. iIntros "(_ & Hgen_reg & HPC & Hbe)".
     (* Since we are dynamically allocating local state, we do not need the freshness requirement *)
     iDestruct "Hbe" as (b e Hsize) "(Hr_env & Hbe & _)".
     (* Allocate a new invariant *)
     rewrite Z.sub_diag in Hsize. rewrite /region_mapsto /region_addrs_zeroes /region_addrs. 
     destruct (Z_le_dec b e);[|omega]. 
     assert (region_size b e = 1) as ->;[by rewrite /region_size Hsize /=|]. 
     iDestruct "Hbe" as "[Hb _]".
     iDestruct "Hgen_reg" as (wsr') "Hgen_reg". clear Hwsr. 
     iMod (sts_alloc_loc W false awk_rel_pub awk_rel_priv with "Hsts")
       as (i) "(Hsts & % & % & Hstate & #Hrel)".
     iMod (inv_alloc (regN.@b) _ (awk_inv i b) with "[Hstate Hb]")%I as "#Hb".
     { iNext. iExists false. iFrame. }
     (* Prepare to jump to f4 *)
     (* move_r r_self PC *)
     iDestruct "Hprog" as "[Hinstr Hprog]".
     iApply (wp_bind (fill [SeqCtx])).
     iDestruct (big_sepL2_extract_l 29 r_self with "Hgen_reg") as "[Hr_gen Hr_self]";[auto|rewrite /all_registers /=].
     iDestruct "Hr_self" as (w) "Hr_self". 
     iApply (wp_move_success_reg_fromPC with "[$HPC $Hinstr $Hr_self]");
       [apply move_r_i|apply PermFlows_refl|iCorrectPC a_first a1 a_last 3 Hcont|iContiguous_next Hcont 3|auto|]. 
     iEpilogue "(HPC & Hinstr & Hr_self)"; iCombine "Hinstr" "Hprog_done" as "Hprog_done".
     (* lea r_self offset_to_awkward *)
     iPrologue g1_addrs Hprog_length "Hprog".
     assert ((a1 + offset_to_awkward)%a = Some a_cont) as Hcont';[rewrite (addr_add_assoc _ a1) in Ha_cont;auto|].
     iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_self]");
       [apply lea_z_i|apply PermFlows_refl|iCorrectPC a_first a2 a_last 4 Hcont|iContiguous_next Hcont 4|apply Hcont'|auto..].
     { destruct pc_p; auto. inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
     iEpilogue "(HPC & Hinstr & Hr_self)"; iCombine "Hinstr" "Hprog_done" as "Hprog_done".
     (* jmp r_self *)
     iDestruct "Hprog" as "[Hinstr _]".
     iApply (wp_bind (fill [SeqCtx])).
     iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_self]");
       [apply jmp_i|apply PermFlows_refl|iCorrectPC a_first a3 a_last 5 Hcont|].
     iEpilogue "(HPC & Hinstr & Hr_self)"; iCombine "Hinstr" "Hprog_done" as "_".
     (* continuation *)
     iApply "Hφ". iFrame "Hr_gen Hr_self".
     iSplitL "HPC".
     { destruct pc_p; iFrame. inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
     assert (b = e)%a as ->;[apply z_of_eq;lia|].
     iExists e. iFrame.
     iExists i. iFrame "∗ #". iSplitL;[|eauto]. 
     iApply (region_monotone with "[] [] Hr"); [auto|].
     iPureIntro. split;[apply related_sts_pub_refl|simpl]. 
     apply related_sts_pub_fresh; auto.
   Qed.

   Import uPred.

   (* TODO: move this to separate region lemma file *)
   Lemma monotone_revoked_close_sub' W l p φ :
    ([∗ list] a ∈ l, temp_resources W φ a p ∗ rel a p φ ∗ ⌜revoked W a⌝)
    ∗ sts_full_world sts_std W ∗ region W ==∗
    sts_full_world sts_std (close_list (countable.encode <$> l) W)
    ∗ region (close_list (countable.encode <$> l) W).
  Admitted. 
   


   (* The proof of the awkward example goes through a number of worlds.
      Below are some helper lemmas and definitions about how these worlds 
      are related *)
   Lemma related_priv_local_1 W i :
     W.2.1 !! i = Some (countable.encode true) ->
     W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     related_sts_priv_world W (W.1, (<[i:=countable.encode false]> W.2.1, W.2.2)).
   Proof.
     intros Hlookup Hrel. 
     split;[apply related_sts_priv_refl|simpl].
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros j r1 r2 r1' r2' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x y Hx Hy.
     destruct (decide (i = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. rewrite Hlookup in Hx. inversion Hr; inversion Hx; subst.
       right with (countable.encode false);[|left].
       right. exists true,false. repeat (split;auto).
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst. left.
   Qed. 
   
     
   (* the following spec is for the f4 subroutine of the awkward example, jumped to after dynamically allocating into r_env *)
   Lemma f4_spec W pc_p pc_g pc_b pc_e (* PC *)
         b e a (* adv *)
         f4_addrs flag_off (* f2 *)
         d i (* dynamically allocated memory given by preamble, connected to invariant i *)
         a_first a_last a_flag (* special adresses *) 
         (b_r e_r b_r' : Addr) (* stack *) :
    
     (* PC assumptions *)
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a_first)) ∧
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a_last)) →
     
     (* Program adresses assumptions *)
     contiguous f4_addrs ->
     f4_addrs !! 0 = Some a_first ∧ list.last f4_addrs = Some a_last ->
    
     (* Stack assumptions *)
     (0%a ≤ e_r)%Z ∧ (0%a ≤ b_r)%Z -> (* this assumption will not be necessary once addresses are finite *)
     (b_r ≤ e_r)%Z ->
     region_size b_r e_r > 12 -> (* we must assume the stack is large enough for needed local state *)
     (b_r' + 1)%a = Some b_r ->

     (* Finally, we must assume that the stack is currently in a revoked state *)
     Forall (λ a, revoked W a ∧ rel_is_std_i W (countable.encode a)) (region_addrs b_r e_r) ->

     {{{ r_stk ↦ᵣ inr ((RWLX,Local),b_r,e_r,b_r')
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_self ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_adv ↦ᵣ inr ((E,Global),b,e,a)
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d,d)
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r_adv;r_self;r_env]; wsr, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (awk_inv i d))
      ∗ sts_rel_loc i awk_rel_pub awk_rel_priv
      (* stack *)
      ∗ (∃ ws, [[b_r, e_r]]↦ₐ[RWLX][[ws]])
      ∗ ([∗ list] a ∈ (region_addrs b_r e_r), rel a RWLX (λ Wv : prodO STS STS * Word, (interp Wv.1) Wv.2))
      (* flag *)
      ∗ a_flag ↦ₐ[RW] inl 0%Z
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv code *)
      ∗ ([∗ list] a ∈ (region_addrs b e), (read_write_cond a RX interp) ∧ ⌜region_state_nwl W a Global⌝ ∧ ⌜region_std W a⌝)
      (* trusted code *)
      ∗ awkward_example f4_addrs pc_p r_self r_adv 65 flag_off
      (* we start out with arbitrary sts *)
      ∗ sts_full_world sts_std W
      ∗ region W
    }}}
      Seq (Instr Executable)
    {{{ v, RET v; ⌜v = HaltedV⌝ → a_flag ↦ₐ[RW] inl 0%Z }}}.
  Proof.
    iIntros ([Hvpc1 Hvpc2] Hcont [Hfirst Hlast] Hpos Hle Hl_bound Hb_r Hrevoked φ)
            "(Hr_stk & HPC & Hr_self & Hr_adv & Hr_env & Hgen_reg & #Hι & #Hrel & Hstack & #Hstack_val & Hflag & Hna & Hadv_val & Hprog & Hsts & Hr) Hφ".
    (* We put the code in a non atomic invariant for each iteration of the program *)
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"prog") with "Hprog") as "#Hf4". 
    (* Since the program will jump to itself, we need to do a Lob induction *)
    (* We generalize the induction over all W *)
    iRevert (Hrevoked). iLöb as "IH" forall (W).
    iIntros (Hrevoked).
    (* Now we step through the iteration *)
    iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls)";[auto..|]. 
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct (f4_addrs);[inversion Hprog_length|].
    iDestruct "Hι" as (ι) "Hinv". 
    (* We will now need to open the invariant for d. 
       We do not know which state d is in, and may need to 
       do a private transition from 1 to 0! For that reason 
       we will first revoke region, so that we can do private 
       updates to it. We do not care about the stack resources, 
       as it currently in the revoked state. 
     *)
    iMod (monotone_revoke with "[$Hsts $Hr]") as "[Hsts Hr]". 
    (* Now we may do any private transitions to our local invariants.
       since we don't know which case we are in, we can generalize and 
       say that there exists some private future world such that   
       the store succeeded, after which the state at i is false
     *)
    iPrologue l Hprog_length "Hprog".
    simpl in Hfirst. inversion Hfirst; subst. 
    iAssert (▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a1)
              ∗ r_env ↦ᵣ inr (RWX, Global, d, d, d)
              ∗ a_first ↦ₐ[pc_p] store_z r_env 0
              ∗ (∃ W', ⌜related_sts_priv_world (revoke W) W'⌝ ∧
                       ⌜W'.2.1 !! i = Some (countable.encode false)⌝ ∧
                       region W' ∗ sts_full_world sts_std W' ∗
                       ⌜Forall (λ a : Addr, revoked W' a ∧ rel_is_std_i W' (countable.encode a)) (region_addrs b_r e_r)⌝)
              -∗ WP Seq (Instr Executable) {{ v, φ v }})
        -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
      with "[HPC Hinstr Hr_env Hr Hsts]" as "Hstore_step".
    { iIntros "Hcont". 
      (* store r_env 0 *)
      iInv ι as (x) "[>Hstate Hb]" "Hcls".
      destruct x; iDestruct "Hb" as ">Hb".
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|auto|iContiguous_next Hcont 0| |auto|..].
        { split;auto. isWithinBounds; lia. }
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* we assert that updating the local state d to 0 is a private transition *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.
        assert (related_sts_priv_world W (W.1, (<[i:=countable.encode false]> W.2.1, W.2.2)))
          as Hrelated;[apply related_priv_local_1; auto|].
        (* first we can update region privately since it is revoked *)
        iAssert (sts_full_world sts_std (revoke W)
               ∗ region ((revoke W).1, (<[i:=countable.encode false]> (revoke W).2.1, (revoke W).2.2)))%I with "[Hsts Hr]" as "[Hsts Hr]".
        { rewrite region_eq /region_def.
          iDestruct "Hr" as (M) "(HM & % & Hr)".
          iDestruct (monotone_revoke_list_region_def_mono $! Hrelated with "[] Hsts Hr") as "[Hsts Hr]".
          - iPureIntro. by apply dom_equal_revoke.
          - iFrame. iExists M. iFrame. iPureIntro. auto.
        }
        (* we must update the local state of d to false *)
        iMod (sts_update_loc _ _ _ false with "Hsts Hstate") as "[Hsts Hstate]". 
        iMod ("Hcls" with "[Hstate Hd]") as "_". 
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        iExists _.
        iDestruct (sts_full_world_std with "[] Hsts") as %Hstd; [iPureIntro;split;apply related_sts_priv_refl|].
        iFrame "Hsts Hr". iSimpl.
        iPureIntro. split;[apply revoke_monotone in Hrelated; auto|split;[apply lookup_insert|] ].
        eapply Forall_impl;[|apply Hrevoked].
        intros a0 [Ha0_rev Ha0_std]. split;auto. 
        rewrite /revoked /std_sta /=. rewrite /revoked /= in Ha0_rev.
        destruct (W.1.1 !! countable.encode a0) eqn:Hsome;[subst|done].
        apply revoke_lookup_Revoked in Hsome. rewrite Hsome. done. 
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|auto|iContiguous_next Hcont 0| |auto|..].
        { split;auto. isWithinBounds; lia. }
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* use sts_state to assert that the current state of i is false *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup. 
        (* No need to update the world, since we did not change state *)
        iMod ("Hcls" with "[Hstate Hd]") as "_". 
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        iExists _. iFrame. iPureIntro. split;[split;apply related_sts_priv_refl|split;auto].
        eapply Forall_impl;[|apply Hrevoked].
        intros a0 [Ha0_rev Ha0_std]. split;auto. 
        rewrite /revoked /std_sta /=. rewrite /revoked /= in Ha0_rev.
        destruct (W.1.1 !! countable.encode a0) eqn:Hsome;[subst|done].
        apply revoke_lookup_Revoked in Hsome. rewrite Hsome. done. 
    }
    iApply "Hstore_step". 
    iNext. iIntros "(HPC & Hr_env & Hprog_done & HW')".
    iDestruct "HW'" as (W' Hrelated Hfalse) "(Hr & Hsts & #Hforall)".
    clear Hrevoked. iDestruct "Hforall" as %Hrevoked. 
    (* we prepare the stack for storing local state *)
    iDestruct "Hstack" as (ws) "Hstack".
    iDestruct (big_sepL2_length with "Hstack") as %Hstack_length.
    assert (∃ ws_local ws_rest, ws = ws_local ++ ws_rest ∧ length ws_local = 3)
      as [ws_local [ws_rest [Happ Hlocal_length] ] ].
    { rewrite region_addrs_length in Hstack_length; auto. rewrite Hstack_length in Hl_bound. 
      do 3 (destruct ws as [|? ws]; [simpl in Hl_bound; lia|]). by exists [w;w0;w1],ws. }
    rewrite Happ.
    iDestruct (contiguous_program_split with "Hstack") as (stack_local stack_rest s_last s_first)
                                                            "(Hstack_local & Hstack_rest & #Hcont)";
      [apply region_addrs_contiguous|lia|..].
    { rewrite Happ region_addrs_length in Hstack_length;[|auto]. rewrite app_length in Hstack_length. lia. }
    iDestruct "Hcont" as %(Hstack_local & Hstack_rest & Hstackeq & Hs_last & Hs_first & Hlink).
    iDestruct (big_sepL2_length with "Hstack_local") as %Hlength_local. rewrite Hlocal_length in Hlength_local. 
    do 3 (destruct stack_local;[inversion Hlength_local|]). destruct stack_local;[|inversion Hlength_local]. 
    do 3 (destruct ws_local;[inversion Hlocal_length|]). destruct ws_local;[|inversion Hlocal_length]. 
    assert (a0 = b_r) as Heq;[|simplify_eq]. 
    { assert (region_addrs b_r e_r !! 0 = Some b_r) as Hfirst';[apply region_addrs_first;auto|].
      rewrite Hstackeq /= in Hfirst'. inversion Hfirst'; done. 
    }
    iDestruct "Hstack_local" as "(Hb_r & Ha2 & Ha3 & _)".
    assert (contiguous (region_addrs b_r e_r)) as Hcont_stack;[apply region_addrs_contiguous|].
    assert (list.last ([b_r; a2; a3] ++ stack_rest) = Some e_r) as Hlast_stack.
    { rewrite -Hstackeq. apply region_addrs_last;auto. }
    rewrite Hstackeq in Hcont_stack.
    (* push r_stk r_env *)
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a1;a0] (a4::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Hb_r"];
      [|apply PermFlows_refl|by isWithinBounds|iContiguous_next Hcont 1|iContiguous_next Hcont 2|apply Hb_r|..].
    { split;[iCorrectPC a_first a1 a_last 1 Hcont|iCorrectPC a_first a0 a_last 2 Hcont]. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_self *)
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a4;a5] (a6::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_self Ha2"];
      [|apply PermFlows_refl|isWithinBounds_stack Hcont_stack 1|iContiguous_next Hcont 3|
       iContiguous_next Hcont 4|iContiguous_next Hstack_local 0|..].
    { split;[iCorrectPC a_first a4 a_last 3 Hcont|iCorrectPC a_first a5 a_last 4 Hcont]. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha2)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_adv *)
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a6;a7] (a8::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_adv Ha3"];
      [|apply PermFlows_refl|isWithinBounds_stack Hcont_stack 2|iContiguous_next Hcont 5|
       iContiguous_next Hcont 6|iContiguous_next Hstack_local 1|..].
    { split;[iCorrectPC a_first a6 a_last 5 Hcont|iCorrectPC a_first a7 a_last 6 Hcont]. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_adv & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    
    (* need to split the stack in additionally two parts: own and adv *)
    iDestruct (big_sepL2_length with "Hstack_rest") as %Hlength_stack_rest.
     assert (∃ ws_own ws_adv, ws_rest = ws_own ++ ws_adv ∧ length ws_own = 8)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { rewrite region_addrs_length in Hstack_length; auto. rewrite Hstack_length in Hl_bound. 
      do 8 (destruct ws_rest as [|? ws_rest]; [simpl in Hl_bound; lia|]).
           by exists [w2;w3;w4;w5;w6;w7;w8;w9],ws_rest. }
    rewrite Happ.
    iDestruct (contiguous_program_split with "Hstack_rest") as (stack_own stack_adv s_last' s_first')
                                                            "(Hstack_own & Hstack_adv & #Hcont)";
      [repeat (apply contiguous_weak in Hcont_stack;try done)|lia|..].
    { rewrite Happ region_addrs_length in Hstack_length;[|auto]. do 2 (rewrite app_length in Hstack_length). lia. }
    iDestruct "Hcont" as %(Hstack_own & Hstack_adv & Hstackeq' & Hs_last' & Hs_first' & Hlink'').
    assert (contiguous (region_addrs b_r e_r)) as Hstackcont;[apply region_addrs_contiguous|rewrite Hstackeq in Hstackcont]. 
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_own. rewrite Hlength' in Hlength_own.
    (* prepare for scall *)
    (* split the program into the scall_prologue and the rest *)
    iDestruct (contiguous_program_split with "Hprog") as (scall_prologue rest0 scall_last rest0_first)
                                                         "(Hscall & Hf2 & #Hcont)"; [auto|simpl;lia|simpl;lia|..].
    { repeat (apply contiguous_weak in Hcont; try done). }
    iDestruct "Hcont" as %(Hcont_scall & Hcont_rest0 & Hrest_app & Hscall_last & Hrest0_first & Hlink'). subst.
    iDestruct (big_sepL2_length with "Hscall") as %Hscall_length. simpl in Hscall_length.
    destruct scall_prologue as [|scall_prologue_first scall_prologue];[inversion Hscall_length|].
    assert (scall_prologue_first = a8) as <-;[inversion Hrest_app;auto|].
    (* get important elements of the stack *)
    destruct stack_own as [|stack_own_b stack_own];[inversion Hlength_own|].
    assert ((stack_own_b :: stack_own) = region_addrs stack_own_b s_last') as ->.
    { apply contiguous_region_addrs; auto. }
    assert (stack_adv = region_addrs s_first' e_r) as ->.
    { apply contiguous_region_addrs; auto. rewrite -(region_addrs_last b_r);[|auto].
      rewrite Hstackeq. rewrite -last_app_eq; [auto|simpl;lia]. rewrite -last_app_eq;[auto|]. destruct stack_adv; [inversion Hs_first'|simpl;lia]. }
    assert ((stack_own_b + 7)%a = Some s_last') as Hstack_own_bound.
    { apply (contiguous_incr_addr_middle _ 0 7 stack_own_b _ Hstack_own); auto. simpl.
      assert (length stack_own - 1 = 6) as Heq;[simpl in Hlength_own;lia|]. rewrite -Heq. 
      rewrite -last_lookup. simpl in Hs_last. destruct stack_own; [inversion Heq|done]. }
    (* Scall *)
    iApply scall_prologue_spec; last (iFrame "Hscall HPC Hr_stk"; iSplitL "Hgen_reg Hr_env Hr_self";
                                      [|iSplitL "Hstack_own";[iNext;eauto|iSplitL "Hstack_adv";[iNext;eauto|] ] ]);
      [iCorrectPC a_first scall_prologue_first a_last 7 Hcont| |isWithinBounds_stack Hcont_stack 3| |apply Hpos|apply Hcont_scall|auto|apply Hscall_last|
       apply PermFlows_refl|iNotElemOfList|iContiguous_next Hstackcont 2|apply Hstack_own_bound|..|apply Hlink'| |].
    { assert (length scall_prologue - 1 = 75) as Heq;[simpl in Hscall_length; lia|]. 
      iCorrectPC a_first scall_last a_last 83 Hcont;
      (rewrite Hrest_app /= lookup_app_l;[rewrite -Heq -last_lookup; destruct scall_prologue;[inversion Hscall_length|auto]|simpl in Hscall_length;lia]). }
    { isWithinBounds_stack Hstackcont 11; inversion Hlength_own as [Heq]; rewrite /= Heq lookup_app_r;rewrite Heq; auto. }
    { assert (8 = 7 + 1)%Z as ->;[auto|]. rewrite (addr_add_assoc _ s_last'); auto. }
    { apply (contiguous_incr_addr_middle _ 7 77 scall_prologue_first _ Hcont); auto.
      rewrite -Hscall_length Hrest_app /= lookup_app_r;[|lia]. rewrite PeanoNat.Nat.sub_diag; auto. }
    { iNext. iDestruct "Hgen_reg" as (wsr) "Hgen_reg". iExists (wsr ++ [_;_]). rewrite /all_registers /=.
      iApply (big_sepL2_app _ _ [r_t29; r_t30] wsr with "Hgen_reg [Hr_env Hr_self]").
      by iFrame. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hgen_reg & Hstack_own & Hstack_adv & Hscall)".
    iCombine "Hscall" "Hprog_done" as "Hprog_done".
    assert (isCorrectPC (inr (pc_p, pc_g, pc_b, pc_e, rest0_first))) as Hvpc1'.
    { iCorrectPC a_first rest0_first a_last 84 Hcont;
      (rewrite Hrest_app /=;inversion Hscall_length; rewrite lookup_app_r;[rewrite PeanoNat.Nat.sub_diag; auto|auto]). }
    (* jmp r_adv *)
    iDestruct (big_sepL2_length with "Hf2") as %Hrest_length; simpl in Hrest_length. 
    destruct rest0;[inversion Hrest_length|]. 
    iPrologue rest0 Hrest_length "Hf2". inversion Hrest0_first; subst.
    iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
      [apply jmp_i|apply PermFlows_refl|auto|..].
    iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".
    (* We now want to reason about unknows code. For this we invoke the fundamental theorem *)
    (* Before we can show the validity of the continuation, we need to set up the invariants 
       for local state, as well as the invariant for the stack *)
    (* We start out by closing the invariant for the program *)
    iMod ("Hcls" with "[Hprog_done Hinstr Hprog $Hna]") as "Hna". 
    { iNext. iDestruct "Hprog_done" as "(Hscall & Hpush3 & Hpush2 & Hpush1 & Ha_first)".
      iFrame "Ha_first". rewrite Hrest_app. 
      iApply (big_sepL2_app with "Hpush1 [-]"). 
      iApply (big_sepL2_app with "Hpush2 [-]").
      iApply (big_sepL2_app with "Hpush3 [-]").
      iApply (big_sepL2_app with "Hscall [-]").
      iFrame. 
    }
    (* Next we close the adversary stack region so that it is Temporary *)
    iMod (monotone_revoked_close_sub' _ (region_addrs s_first' e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
            with "[$Hsts $Hr Hstack_adv]") as "[Hsts Hex]".
    { rewrite Hstackeq app_assoc. iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_val']".
      iApply big_sepL_sep. iSplitL.
      - iDestruct (region_addrs_zeroes_trans with "Hstack_adv") as "Hstack_adv".
        iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hy".
        iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
        + iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
        + by repeat (rewrite fixpoint_interp1_eq /=).
      - iApply big_sepL_sep; iFrame "#". iApply big_sepL_forall. iPureIntro.
        rewrite Hstackeq app_assoc in Hrevoked. apply Forall_app in Hrevoked as [_ Hrevoked]. 
        intros k x Hsome. apply (Forall_lookup_1 _ _ k _ Hrevoked Hsome). 
    }
    (* We put the local stack in a non atomic invariant. Since the local stack will change, 
       we allocate an STS to model that change *)
    iMod (sts_alloc_loc _ (First : local_state) local_rel_pub local_rel_pub with "Hsts")
      as (j) "(Hsts & % & % & Hstate & #Hrelj)".
    iMod (na_inv_alloc logrel_nais ⊤ (regN.@"stack") (∃ x:local_state, sts_state_loc j First
                       ∗ match x with
                         | First => b_r ↦ₐ[RWLX] inr (RWX, Global, d, d, d)
                                  ∗ a2 ↦ₐ[RWLX] inr (pc_p, pc_g, pc_b, pc_e, a_first)
                                  ∗ a3 ↦ₐ[RWLX] inr (E, Global, b, e, a)
                                  ∗ [[stack_own_b,s_last']]↦ₐ[RWLX][[ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c; inr (pc_p, pc_g, pc_b, pc_e, rest0_first);
                                                                       inr (RWLX, Local, b_r, e_r, s_last')] ]]
                         | Second => True
                         | Released => emp
                         end 
                       )%I
            with "[Hstack_own Hstate Hb_r Ha2 Ha3]")
      as "#Hlocal".
    { iNext. iExists (First : local_state). iFrame "Hstate". 
      iExact "Hstate". iFrame "Hstate".  }
    
End awkward_example. 
