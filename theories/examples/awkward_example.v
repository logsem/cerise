From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental. 
From cap_machine.examples Require Import region_macros stack_macros scall malloc. 


Section awkward_example.
   Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

   (* choose a special register for the environment *)
   (* note that we are here simplifying the environment to simply point to one location *)      
   Definition r_env : RegName := r_t30.
   
   
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

   Definition awkward_preamble_instrs offset_to_awkward :=
     malloc_subroutine r_env 1 ++
     [move_r r_t3 PC;
     lea_z r_t3 offset_to_awkward;
     jmp r_t3].
   
   (* assume r1 contains an executable pointer to adversarial code *)
   Definition awkward_instrs (r1 : RegName) epilogue_off flag_off :=
     [store_z r_env 0] ++
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1;
     store_z r_env 1] ++
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1;
     (* assert that the cap in r_env points to 1 *)
     load_r r1 r_env;
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
  
   Definition awkward_preamble a p offset_to_awkward :=
     ([∗ list] a_i;w_i ∈ a;(awkward_preamble_instrs offset_to_awkward), a_i ↦ₐ[p] w_i)%I.
   
   Definition awkward_example (a : list Addr) (p : Perm) (r1 : RegName) epilogue_off flag_off : iProp Σ :=
     ([∗ list] a_i;w_i ∈ a;(awkward_instrs r1 epilogue_off flag_off), a_i ↦ₐ[p] w_i)%I.
   

End awkward_example. 
