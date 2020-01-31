From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel stack_macros. 

Section scall.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  (* Macro for stack calling. Note that the prologue and epilogue does 
     not include storing and loading private state on the stack. *)
  
  (* the prologue pushes the activation code, the old pc and stack points, 
     sets up the return capability and adv stack capability, then jumps to adversary code *)
  (* r1 is the register containg the adversary capability *)
  Definition scall_prologue_instrs epilogue_off r1 :=
    (* push activation code *)
    push_z_instrs r_stk w_1 ++
    push_z_instrs r_stk w_2 ++
    push_z_instrs r_stk w_3 ++
    push_z_instrs r_stk w_4a ++             
    push_z_instrs r_stk w_4b ++
    push_z_instrs r_stk w_4c ++
    (* push old pc *)
    [move_r r_t1 PC;
    lea_z r_t1 epilogue_off;
    lea_z r_stk 1; store_r r_stk r_t1; (* push_r r_t1 *)
    (* push stack pointer *)
    lea_z r_stk 1;
    store_r r_stk r_stk;
    (* set up protected return pointer *)
    move_r r_t0 r_stk;
    lea_z r_t0 (-7)%Z;
    restrict_z r_t0 (local_e);
    (* restrict stack capability *)
    geta r_t1 r_stk;
    add_r_z r_t1 r_t1 1;
    gete r_t2 r_stk;
    subseg_r_r r_stk r_t1 r_t2] ++
    (* clear the unused part of the stack *)
    (* mclear r_stk: *)
    mclear_instrs r_stk 10 2 ++ (* 10 and 2 correspond to the offsets to iter in a contiguous mclear *)
    rclear_instrs (list_difference all_registers [PC;r_stk;r_t0;r1]).

  Definition scall_prologue (a : list Addr) p epilogue_off r1 :=
    ([∗ list] a_i;w_i ∈ a;(scall_prologue_instrs epilogue_off r1), a_i ↦ₐ[p] w_i)%I.

  Lemma scall_prologue_spec
        (* adress arithmetic *) a_r_adv b_r_adv a_act a_cont a_next
        (* scall parameters *) a a_first a_last p' epilogue_off r1
        (* program counter *) p g b e
        (* stack capability *) b_r e_r a_r
        (* continuation *) φ :
    isCorrectPC (inr ((p,g),b,e,a_first)) → isCorrectPC (inr ((p,g),b,e,a_last)) →
    contiguous a →
    a !! 0 = Some a_first -> list.last a = Some a_last ->
    PermFlows p p' →

    (a_r + 1)%a = Some a_act →
    (a_r + 8)%a = Some a_r_adv →
    (a_r + 9)%a = Some b_r_adv →
    (a_first + (13 + epilogue_off))%a = Some a_cont →
    (a_last + 1)%a = Some a_next →

    (▷ scall_prologue a p' epilogue_off r1
   ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a_first)
   ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),b_r,e_r,a_r)
   ∗ ▷ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r1]; wsr, r_i ↦ᵣ w_i)
   ∗ ▷ (∃ ws_own, [[a_act, a_r_adv]]↦ₐ[RWLX][[ws_own]]) (* local stack *)
   ∗ ▷ (∃ ws_adv, [[b_r_adv, e_r]]↦ₐ[RWLX][[ws_adv]]) (* adv stack *)
   ∗ ▷ (PC ↦ᵣ inr (p,g,b,e,a_next)
            ∗ r_stk ↦ᵣ inr ((RWLX,Local),b_r_adv,e_r,a_r_adv)
            ∗ r_t0 ↦ᵣ inr ((E,Local),b_r,e_r,a_act)
            ∗ ([∗ list] r_i ∈ list_difference all_registers [PC;r_stk;r_t0;r1], r_i ↦ᵣ inl 0%Z)
            ∗ [[ a_act, a_r_adv ]]↦ₐ[RWLX][[ [inl w_1;
                                             inl w_2;
                                             inl w_3;
                                             inl w_4a;
                                             inl w_4b;
                                             inl w_4c;
                                             inr (p,g,b,e,a_cont);
                                             inr (RWLX,Local,b_r,e_r,b_r_adv)] ]] (* local stack *)
            ∗ [[ b_r_adv, e_r ]] ↦ₐ[RWLX] [[ region_addrs_zeroes b_r_adv e_r ]] (* cleared adv stack *)
            ∗ scall_prologue a p' epilogue_off r1 -∗ 
            WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I. 
  Proof.
    iIntros (Hvpc1 Hvpc2 Ha Hfirst Hlast Hfl Hact Hadva Hadvb Hcont Hnext)
            "(>Hscall & >HPC & >Hr_stk & >Hr1 & >Hgen_reg & >Hstack & Hφ)".
    rewrite /scall_prologue.
    iDestruct (big_sepL2_length with "Hscall") as %Hlength.
    iDestruct (contiguous_program_split with "Hscall") as (a1 a2 a1_last a2_first) "(Hpush & Hprog & #Hcont)"; [auto|cbv;auto|..].
    { rewrite app_length. apply PeanoNat.Nat.lt_lt_add_r. cbv. auto. } (* Make tactic for lengths *)
    iDestruct "Hcont" as %(Ha1 & Ha2 & Happ & Ha1_last & Ha2_first). 
    
    
    
  Admitted.



  Definition scall_epilogue_instrs :=
    (* pop the restore code *)
    (* to shorten the program we will do it all at once *)
    [sub_z_z r_t1 0 7; lea_r r_stk r_t1]. 


End scall. 
