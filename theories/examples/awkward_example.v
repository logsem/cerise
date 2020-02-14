From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental. 
From cap_machine.examples Require Import region_macros stack_macros scall malloc. 


Section awkward_example.
   Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

   (* choose a special register for the environment and adv pointer *)
   (* note that we are here simplifying the environment to simply point to one location *)      
   Definition r_env : RegName := r_t30.
   Definition r_adv : RegName := r_t31.
   Definition r_self : RegName := r_t29.
   
   Ltac isWithinBounds := rewrite /withinBounds; apply andb_true_iff; split; apply Z.leb_le; simpl; auto.
   
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
    
   (* Recall that the malloc subroutine lies in b_m e_m *)

   (* assume that r1 contains an executable pointer to the malloc subroutine *)
   Definition awkward_preamble_instrs r1 offset_to_awkward :=
     [move_r r_t0 PC;
     lea_z r_self 1;
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
             then a ↦ₐ[RW] inl 1%Z
             else a ↦ₐ[RW] inl 0%Z)%I.

   Definition awk_rel_pub := λ a b, a = false ∨ b = true.
   Definition awk_rel_priv := λ (a b : bool), True.

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

     (PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_t1 ↦ᵣ inr (E,Global,b_m,e_m,a_m)
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_t1]; wsr, r_i ↦ᵣ w_i)
      ∗ awkward_preamble g1_addrs pc_p r_t1 offset_to_awkward
      ∗ region W
      ∗ sts_full_world sts_std W
      ∗ ▷ (PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_cont)
          ∗ r_self ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_cont)
          ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_self]; wsr, r_i ↦ᵣ w_i)
          -∗ WP Seq (Instr Executable) {{ φ }})
      ⊢ WP Seq (Instr Executable) {{ φ }})%I.
     
   
   (* the following spec is for the f4 subroutine of the awkward example, jumped to after dynamically allocating into r_env *)
   Lemma f4_spec W pc_p pc_g pc_b pc_e (* PC *)
         b e a (* adv *)
         f4_addrs flag_off (* f2 *)
         d d' i (* dynamically allocated memory given by preamble, connected to invariant i *)
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

     (* Preamble assumptions *)
     (d + 1)%a = Some d' ->

     (* Finally, we must assume that the stack is currently in a revoked state *)
     Forall (λ a, revoked W a ∧ rel_is_std_i W (countable.encode a)) (region_addrs b_r e_r) ->

     {{{ r_stk ↦ᵣ inr ((RWLX,Local),b_r,e_r,b_r')
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_self ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_adv ↦ᵣ inr ((E,Global),b,e,a)
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r_adv;r_self;r_env]; wsr, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ awk_inv i d
      ∗ sts_rel_loc i awk_rel_pub awk_rel_priv
      (* stack *)
      ∗ (∃ ws, [[b_r, e_r]]↦ₐ[RWLX][[ws]])
      (* flag *)
      ∗ a_flag ↦ₐ[RW] inl 0%Z
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv code *)
      ∗ interp W (inr ((E,Global),b,e,a))
      (* trusted code *)
      ∗ awkward_example f4_addrs pc_p r_self r_adv 65 flag_off
      (* we start out with arbitrary sts *)
      ∗ sts_full_world sts_std W
      ∗ region W
    }}}
      Seq (Instr Executable)
    {{{ v, RET v; ⌜v = HaltedV⌝ → a_flag ↦ₐ[RW] inl 0%Z }}}.
  Proof.
                

   

End awkward_example. 
