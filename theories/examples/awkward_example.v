From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants. 
Require Import Eqdep_dec. 
From cap_machine Require Import rules logrel fundamental region_invariants region_invariants_revocation. 
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

   Lemma test W :
     sts_full_world sts_std W ∗ region W ==∗ sts_full_world sts_std (revoke W) ∗ region (revoke W).
   Proof.
     iIntros "[HW Hr]". iMod (monotone_revoke W with "[HW Hr]"). iFrame. done. 
   Qed. 

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

   Ltac iGet_genpur_reg_map r' reg Hgen_reg Hfull Hgen_ptrn :=
     let w := fresh "w" in
     let Hw := fresh "Hw" in 
     iAssert (⌜∃ w, r' !! reg = Some w⌝)%I as %[w Hw];
     first iApply Hfull;
     iDestruct (big_sepM_delete _ _ reg with Hgen_reg) as Hgen_ptrn;
     [repeat (rewrite lookup_delete_ne; auto; (try by (rewrite lookup_insert_ne; eauto)))|].

   Ltac iClose_genpur_reg_map reg Hgen_ptrn Hgen :=
     repeat (rewrite -(delete_insert_ne _ reg); [|auto]);
     iDestruct (big_sepM_insert _ _ reg with Hgen_ptrn) as Hgen;[apply lookup_delete|iFrame|rewrite insert_delete].

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
     push_r_instrs r_stk r1 ++ 
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r1 ++
     pop_instrs r_stk r0 ++
     pop_instrs r_stk r_env ++
     (* assert that the cap in r_env points to 1 *)
     [load_r r_t2 r_env;
     move_r r_t1 PC;
     lea_z r_t1 5; (* offset to assertion failure *)
     sub_r_z r_t2 r_t2 1;
     jnz r_t1 r_t2;
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

   (* useful lemma about awk rels *)
   Lemma rtc_rel_pub y x :
     y = (countable.encode true) ->
     rtc (convert_rel awk_rel_pub) y x ->
     x = (countable.encode true).
   Proof.
     intros Heq Hrtc.
     induction Hrtc; auto. 
     rewrite Heq in H3. 
     inversion H3 as [y' [b [Heq1 [Heq2 Hy] ] ] ].
     inversion Hy; subst; auto.
     apply encode_inj in Heq1. inversion Heq1.
   Qed.
   Lemma rtc_rel_pub' x :
     rtc (convert_rel awk_rel_pub) (countable.encode true) (countable.encode x) ->
     x = true.
   Proof.
     intros Hrtc. 
     apply encode_inj.
     apply rtc_rel_pub with (countable.encode true); auto. 
   Qed. 
     
   Inductive local_state :=
   | Live
   | Released.
   Instance local_state_EqDecision : EqDecision local_state.
   Proof.
     intros ρ1 ρ2.
     destruct ρ1,ρ2;
       [by left|by right|by right| by left]. 
   Qed.
   Instance local_state_finite : finite.Finite local_state.
   Proof.
     refine {| finite.enum := [Live;Released] ;
               finite.NoDup_enum := _ ;
               finite.elem_of_enum := _ |}.
     - repeat (apply NoDup_cons; split; [repeat (apply not_elem_of_cons;split;auto); apply not_elem_of_nil|]).
         by apply NoDup_nil.
     - intros ρ.
       destruct ρ;apply elem_of_cons;[by left|right];
           apply elem_of_cons; by left.
   Qed.
   Global Instance local_state_countable : Countable local_state.
   Proof. apply finite.finite_countable. Qed.
   Instance local_state_inhabited: Inhabited local_state := populate (Live).
   
   Definition local_rel_pub := λ (a b : local_state), a = b.
   Definition local_rel_priv := λ (a b : local_state), (a = Live ∨ b = Released).

   (* useful lemmas about local state *)
   Lemma rtc_id_eq x y : 
     rtc (convert_rel (λ a b : local_state, a = b)) x y → x = y.
   Proof.
     intros Hrtc.
     induction Hrtc; auto.
     inversion H3 as (b & Hb1 & Hb2 & Hb3 & Hb4). congruence.
   Qed.
   Lemma local_state_related_sts_pub W W' j x :
     related_sts_pub_world W W' ->
     W.2.1 !! j = Some (countable.encode Live) ->
     W.2.2 !! j = Some (convert_rel local_rel_pub, convert_rel local_rel_priv) ->
     W'.2.1 !! j = Some (countable.encode x) ->
     W'.2.2 !! j = Some (convert_rel local_rel_pub, convert_rel local_rel_priv) ->
     x = Live.
   Proof.
     intros Hrelated Hjx Hj Hjx' Hj'. 
     destruct Hrelated as (_ & Hsub1 & Hsub2 & Hrelated).
     specialize (Hrelated j _ _ _ _ Hj Hj') as (_ & _ & Htrans).
     specialize (Htrans _ _ Hjx Hjx').
     destruct x; auto.
     apply rtc_id_eq in Htrans. apply countable.encode_inj in Htrans.
     inversion Htrans. 
   Qed. 
     
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

   Lemma related_priv_local_2 W i j :
     i ≠ j ->
     W.2.1 !! j = Some (countable.encode Live) ->
     W.2.2 !! j = Some (convert_rel local_rel_pub, convert_rel local_rel_priv) ->
     related_sts_priv_world (W.1, (<[i:=countable.encode true]> W.2.1, W.2.2))
                            (W.1.1, std_rel (W.1, (<[i:=countable.encode true]> W.2.1, W.2.2)),
                             (<[j:=countable.encode Released]> (<[i:=countable.encode true]> W.2.1), W.2.2)). 
   Proof.
     intros Hne Hlookup Hrel.
     split;[apply related_sts_priv_refl|simpl].
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros k r1 r2 r1' r2' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x y Hx Hy.
     destruct (decide (k = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. rewrite lookup_insert_ne in Hx;auto.
       rewrite Hlookup in Hx. inversion Hr; inversion Hx; subst.
       right with (countable.encode Released);[|left].
       right. exists Live,Released. repeat (split;auto). by left. 
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst. left.
   Qed.

   Lemma related_priv_local_3 W j :
     W.2.1 !! j = Some (countable.encode Live) ->
     W.2.2 !! j = Some (convert_rel local_rel_pub, convert_rel local_rel_priv) ->
     related_sts_priv_world W (W.1, (<[j:=countable.encode Released]> W.2.1, W.2.2)). 
   Proof.
     intros Hlookup Hrel.
     split;[apply related_sts_priv_refl|simpl].
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros k r1 r2 r1' r2' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x y Hx Hy.
     destruct (decide (k = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. 
       rewrite Hlookup in Hx. inversion Hr; inversion Hx; subst.
       right with (countable.encode Released);[|left].
       right. exists Live,Released. repeat (split;auto). by left. 
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst. left.
   Qed. 
     
   Lemma related_pub_local_1 W i (x : bool) :
     W.2.1 !! i = Some (countable.encode x) ->
     W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     related_sts_pub_world W (W.1, (<[i:=countable.encode true]> W.2.1, W.2.2)).
   Proof.
     intros Hx Hrel.
     split;[apply related_sts_pub_refl|simpl].
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros j r1 r2 r1' r2' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x' y Hx' Hy.
     destruct (decide (i = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. rewrite Hx in Hx'. inversion Hr; inversion Hx; subst.
       right with (countable.encode true);[|left].
       exists x,true. inversion Hx'. subst. repeat (split;auto).
       destruct x; rewrite /awk_rel_pub; auto. 
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx' in Hy; inversion Hy; subst. left.
   Qed.

   Lemma related_pub_lookup_local W W' i x :
     related_sts_pub_world W W' ->
     W.2.1 !! i = Some (countable.encode true) ->
     W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     W'.2.1 !! i = Some (countable.encode x) -> x = true.
   Proof.
     intros Hrelated Hi Hr Hi'.
     destruct Hrelated as [_ [Hdom1 [Hdom2 Htrans] ] ].
     assert (is_Some (W'.2.2 !! i)) as [r' Hr'].
     { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom2. apply Hdom2.
       apply elem_of_gmap_dom. eauto. }
     destruct r' as [r1' r2']. 
     specialize (Htrans i _ _ _ _ Hr Hr') as [Heq1 [Heq2 Htrans] ].
     subst. specialize (Htrans _ _ Hi Hi').
     apply rtc_rel_pub'; auto. 
   Qed.
   
   (* The proof will also go through a number of register states, the following lemmas
      are useful for each of those states *)
   
  Lemma registers_mapsto_resources pc_w stk_w rt0_w adv_w pc_w' :
    ([∗ list] r_i ∈ list_difference all_registers [PC; r_stk; r_t0; r_adv], r_i ↦ᵣ inl 0%Z)
      -∗ r_stk ↦ᵣ stk_w
      -∗ r_t0 ↦ᵣ rt0_w
      -∗ r_adv ↦ᵣ adv_w
      -∗ PC ↦ᵣ pc_w' -∗
     registers_mapsto (<[PC:=pc_w']> (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z))))))). 
  Proof.
    iIntros "Hgen_reg Hr_stk Hr_t0 Hr_adv HPC".
    rewrite /registers_mapsto (insert_insert _ PC).
    iApply (big_sepM_insert_2 with "[HPC]"); first iFrame.
    iApply (big_sepM_insert_2 with "[Hr_stk]"); first iFrame.
    iApply (big_sepM_insert_2 with "[Hr_t0]"); first iFrame.
    iApply (big_sepM_insert_2 with "[Hr_adv]"); first iFrame.
    assert ((list_difference all_registers [PC; r_stk; r_t0; r_adv]) =
            [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12;
             r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24;
             r_t25; r_t26; r_t27; r_t29; r_t30]) as ->; first auto. 
    rewrite /create_gmap_default. iSimpl in "Hgen_reg". 
    repeat (iDestruct "Hgen_reg" as "[Hr Hgen_reg]";
            iApply (big_sepM_insert_2 with "[Hr]"); first iFrame).
    done.
  Qed.

  Lemma r_full (pc_w stk_w rt0_w adv_w : Word) :
    full_map (Σ:=Σ) (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
  Proof.
    iIntros (r0).
    iPureIntro.
    assert (r0 ∈ all_registers); [apply all_registers_correct|].
    destruct (decide (r0 = PC)); [subst;rewrite lookup_insert; eauto|]. 
    rewrite lookup_insert_ne;auto.
    destruct (decide (r0 = r_stk)); [subst;rewrite lookup_insert; eauto|]. 
    rewrite lookup_insert_ne;auto.
    destruct (decide (r0 = r_t0)); [subst;rewrite lookup_insert; eauto|]. 
    rewrite lookup_insert_ne;auto.
    destruct (decide (r0 = r_adv)); [subst;rewrite lookup_insert; eauto|].
    rewrite lookup_insert_ne;auto.
    assert (¬ r0 ∈ [PC; r_stk; r_t0; r_adv]).
    { repeat (apply not_elem_of_cons; split; auto). apply not_elem_of_nil. }
    exists (inl 0%Z).
    apply create_gmap_default_lookup. apply elem_of_list_difference. auto.
  Qed.

  Lemma r_zero (pc_w stk_w rt0_w adv_w : Word) r1 :
    r1 ≠ r_stk → r1 ≠ PC → r1 ≠ r_t0 → r1 ≠ r_adv →
    (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))) !r! r1 = inl 0%Z.
  Proof.
    intros Hr_stk HPC Hr_t0 Hr_t30. rewrite /RegLocate.
    destruct (<[PC:=pc_w]>
              (<[r_stk:=stk_w]>
               (<[r_t0:=rt0_w]>
                (<[r_adv:=adv_w]> (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv])
                                                       (inl 0%Z)))))
                !! r1) eqn:Hsome; rewrite Hsome; last done.
    do 4 (rewrite lookup_insert_ne in Hsome;auto).
    assert (Some s = Some (inl 0%Z)) as Heq.
    { rewrite -Hsome. apply create_gmap_default_lookup.
      apply elem_of_list_difference. split; first apply all_registers_correct.
      repeat (apply not_elem_of_cons;split;auto).
      apply not_elem_of_nil. 
    } by inversion Heq. 
  Qed.     

  (* The validity of adversary region is monotone wrt private future worlds *)
  Lemma adv_monotone W W' b e :
    related_sts_priv_world W W' →
    rel_is_std W ->
    (([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std_sta W !! countable.encode a = Some (countable.encode Permanent)⌝ ∧ ⌜region_std W a⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std_sta W' !! countable.encode a = Some (countable.encode Permanent)⌝ ∧ ⌜region_std W' a⌝))%I.
  Proof.
    iIntros (Hrelated Hstd) "Hr".
    iApply (big_sepL_mono with "Hr").
    iIntros (k y Hsome) "(Hy & Hperm & Hstd)". 
    iFrame.
    iDestruct "Hperm" as %Hperm.
    iDestruct "Hstd" as %region_std. 
    iPureIntro; split. 
    - apply (region_state_nwl_monotone_nl _ W') in Hperm; auto.
    - apply (related_sts_preserve_std W); auto. eauto.
  Qed.

  Lemma adv_stack_monotone W W' b e :
    related_sts_pub_world W W' ->
    rel_is_std W ->
    (([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                     ∧ ⌜region_state_pwl W a⌝ ∧ ⌜region_std W a⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                       ∧ ⌜region_state_pwl W' a⌝ ∧ ⌜region_std W' a⌝))%I.
  Proof.
    iIntros (Hrelated Hstd) "Hstack_adv". 
    iApply (big_sepL_mono with "Hstack_adv").
    iIntros (k y Hsome) "(Hr & Htemp & Hstd)".
    iDestruct "Htemp" as %Htemp. iDestruct "Hstd" as %Hstd'. 
    iFrame. iPureIntro; split.
    - apply (region_state_pwl_monotone _ W') in Htemp; auto.
    - apply (related_sts_preserve_std W); auto; [|eauto].
      apply related_sts_pub_priv_world. auto. 
  Qed. 

  (* Helper lemma about private future worlds *)
  (* TODO: move this in sts? *)
  Lemma related_sts_priv_world_std_sta_is_Some W W' i :
    related_sts_priv_world W W' -> is_Some ((std_sta W) !! i) -> is_Some ((std_sta W') !! i).
  Proof.
    intros [ [Hdom1 [_ _] ] _] Hsome.
    apply elem_of_gmap_dom in Hsome.
    apply elem_of_gmap_dom.
    apply elem_of_subseteq in Hdom1. auto.
  Qed.

  Lemma related_sts_priv_world_std_rel_is_Some W W' i :
    related_sts_priv_world W W' -> is_Some ((std_rel W) !! i) -> is_Some ((std_rel W') !! i).
  Proof.
    intros [ [_ [Hdom1 _] ] _] Hsome.
    apply elem_of_gmap_dom in Hsome.
    apply elem_of_gmap_dom.
    apply elem_of_subseteq in Hdom1. auto.
  Qed.

  Lemma related_sts_priv_world_std_sta_region_type W W' (i : positive) (ρ : region_type) :
    related_sts_priv_world W W' ->
    (std_sta W) !! i = Some (countable.encode ρ) ->
    rel_is_std_i W i ->
    ∃ (ρ' : region_type), (std_sta W') !! i = Some (countable.encode ρ').
  Proof.
    intros Hrelated Hρ Hrel.
    assert (is_Some ((std_sta W') !! i)) as [x Hx].
    { apply related_sts_priv_world_std_sta_is_Some with W; eauto. }
    assert (is_Some ((std_rel W') !! i)) as [r Hr].
    { apply related_sts_priv_world_std_rel_is_Some with W; eauto. }
    destruct Hrelated as [ [Hdom1 [Hdom2 Hrevoked] ] _].
    destruct r as [r1 r2]. 
    specialize (Hrevoked i _ _ _ _ Hrel Hr) as [Heq1 [Heq2 Hrelated] ].
    specialize (Hrelated _ _ Hρ Hx). simplify_eq. 
    apply std_rel_exist in Hrelated as [ρ' Hρ'];[|eauto]. simplify_eq.
    eauto. 
  Qed.
      
   (* Shorthand definition for an adress being currently revoked *)
  Definition region_type_revoked W (a : Addr) :=
     (std_sta W) !! (countable.encode a) = Some (countable.encode Revoked).
   
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
     Forall (λ a, region_type_revoked W a ∧ rel_is_std_i W (countable.encode a)) (region_addrs b_r e_r) ->

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
      (* flag inv *)
      ∗ (∃ ι, inv ι (a_flag ↦ₐ[RW] inl 0%Z))
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
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r W', full_map r ∧ registers_mapsto r
                         ∗ ⌜related_sts_priv_world W W'⌝
                         ∗ na_own logrel_nais ⊤                           
                         ∗ sts_full_world sts_std W'
                         ∗ region W' }}}.
  Proof.
    iIntros ([Hvpc1 Hvpc2] Hcont [Hfirst Hlast] Hpos Hle Hl_bound Hb_r Hrevoked φ)
            "(Hr_stk & HPC & Hr_self & Hr_adv & Hr_env & Hgen_reg & #Hι & #Hrel & Hstack & #Hstack_val & #Hflag & Hna & Hadv_val & Hprog & Hsts & Hr) Hφ".
    (* We put the code in a non atomic invariant for each iteration of the program *)
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"prog") with "Hprog") as "#Hf4". 
    (* Since the program will jump to itself, we need to do a Lob induction *)
    (* We generalize the induction over all W *)
    iRevert (Hrevoked). iLöb as "IH" forall (W φ).
    iIntros (Hrevoked). iDestruct "Hadv_val" as "#Hadv_val". 
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
    iDestruct (sts_full_world_std with "[] Hsts") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|]. 
    iMod (monotone_revoke W with "[$Hsts $Hr]") as "[Hsts Hr]".
    (* Now we may do any private transitions to our local invariants.
       since we don't know which case we are in, we can generalize and 
       say that there exists some private future world such that   
       the store succeeded, after which the state at i is false
     *)
    iPrologue l Hprog_length "Hprog".
    simpl in Hfirst. inversion Hfirst; subst.
    iDestruct (sts_full_world_std with "[] Hsts") as %Hstd';[iPureIntro;split;apply related_sts_priv_refl|]. 
    iAssert (▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a1)
              ∗ r_env ↦ᵣ inr (RWX, Global, d, d, d)
              ∗ a_first ↦ₐ[pc_p] store_z r_env 0
              ∗ (∃ W', ⌜related_sts_priv_world (revoke W) W'⌝ ∧
                       ⌜W'.2.1 !! i = Some (countable.encode false)⌝ ∧
                       region W' ∗ sts_full_world sts_std W' ∗
                       ⌜Forall (λ a : Addr, region_type_revoked W' a ∧ rel_is_std_i W' (countable.encode a)) (region_addrs b_r e_r)⌝)
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
        iFrame "Hsts Hr". iSimpl.
        iPureIntro. split;[apply revoke_monotone in Hrelated; auto|split;[apply lookup_insert|] ].
        eapply Forall_impl;[apply Hrevoked|].
        intros a0 [Ha0_rev Ha0_std]. split; auto. 
        rewrite /region_type_revoked /std_sta /=. rewrite /region_type_revoked /std_sta /= in Ha0_rev.
        apply revoke_lookup_Revoked in Ha0_rev. rewrite Ha0_rev. done. 
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
        eapply Forall_impl;[apply Hrevoked|]. 
        intros a0 [Ha0_rev Ha0_std]. split; auto.  
        rewrite /region_type_revoked /std_sta /=. rewrite /region_type_revoked /std_sta /= in Ha0_rev.
        apply revoke_lookup_Revoked in Ha0_rev. rewrite Ha0_rev. done. 
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
    (* We now want to reason about unknown code. For this we invoke the fundamental theorem *)
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
    iDestruct (sts_full_world_std with "[] Hsts") as %Hstd'';[iPureIntro;split;apply related_sts_priv_refl|]. 
    iMod (monotone_close _ (region_addrs s_first' e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
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
    (* The resulting closed world is a public future world of W' *)
    assert (related_sts_pub_world W' (close_list (countable.encode <$> region_addrs s_first' e_r) W')) as Hrelated'. 
    { apply close_list_related_sts_pub. auto. } clear Hstd''. 
    (* We put the local stack in a non atomic invariant. Since the local stack will change, 
       we allocate an STS that will release the resources *)
    iMod (sts_alloc_loc _ Live local_rel_pub local_rel_priv with "Hsts")
      as (j) "(Hsts & % & % & Hstate & #Hrelj)".
    iMod (na_inv_alloc logrel_nais ⊤ (regN.@"stack") (∃ x:local_state, sts_state_loc j x
                       ∗ match x with
                         | Live => b_r ↦ₐ[RWLX] inr (RWX, Global, d, d, d)
                                  ∗ a2 ↦ₐ[RWLX] inr (pc_p, pc_g, pc_b, pc_e, a_first)
                                  ∗ a3 ↦ₐ[RWLX] inr (E, Global, b, e, a)
                                  ∗ [[stack_own_b,s_last']]↦ₐ[RWLX][[ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                                                                       inr (pc_p, pc_g, pc_b, pc_e, rest0_first);
                                                                       inr (RWLX, Local, b_r, e_r, s_last')] ]]
                         | Released => emp
                         end 
                       )%I
            with "[Hstack_own Hstate Hb_r Ha2 Ha3]")
      as "#Hlocal".
    { iNext. iExists Live. iFrame. }
    (* The resulting world is a public future world of W' *)
    evar (W'' : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
    instantiate (W'' :=
       ((close_list (countable.encode <$> region_addrs s_first' e_r) W').1,
        (<[j:=countable.encode Live]> (close_list (countable.encode <$> region_addrs s_first' e_r) W').2.1,
         <[j:=(convert_rel local_rel_pub, convert_rel local_rel_priv)]> (close_list (countable.encode <$> region_addrs s_first' e_r) W').2.2))).
    assert (related_sts_priv_world W' W'') as HW'W''.
    { apply related_sts_pub_priv_world. 
      eapply related_sts_pub_trans_world;[apply Hrelated'|].
      split;[apply related_sts_pub_refl|apply related_sts_pub_fresh]; auto.
    }
    assert (related_sts_priv_world W W'') as HWW''.
    { eapply related_sts_priv_trans_world;[apply revoke_related_sts_priv;auto|].
      eapply related_sts_priv_trans_world;[apply Hrelated|].
      auto. 
    }
    (* for future use, we will need to know that i is not equal to j *)
    assert (i ≠ j) as Hneij.
    { assert (i ∈ dom (gset positive) (loc W').1) as Hcontr;[apply elem_of_dom; eauto|]. intros Heq; subst. contradiction. }
    (* Next we update the region to the same future state *)
    iDestruct (region_monotone _ W'' with "[] [] Hex") as "Hr";[rewrite /std_sta /=;auto|..].
    { iPureIntro. split;[apply related_sts_pub_refl|apply related_sts_pub_fresh]; auto. }
    iAssert (sts_full_world sts_std W'') with "Hsts" as "Hsts".
    (* We choose the r *)
    evar (r : gmap RegName Word).
    instantiate (r := <[PC    := inl 0%Z]>
                     (<[r_stk := inr (RWLX, Local, s_first', e_r, s_last')]>
                     (<[r_t0  := inr (E, Local, b_r, e_r, stack_own_b)]>
                     (<[r_adv := inr (E, Global, b, e, a)]>
                     (create_gmap_default
                        (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r))
      with "[Hgen_reg Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
    { iApply (registers_mapsto_resources with "Hgen_reg Hr_stk Hr_t0 Hr_adv HPC"). } 
    (* r contrains all registers *)
    iAssert (full_map r) as "#full";[iApply r_full|].
    iSimpl in "Hadv_val".
    iAssert (interp_expression r W'' (inr (RX, Global, b, e, a)))
      as "Hvalid". 
    { iApply fundamental. iLeft; auto. iExists RX. iSplit;[iPureIntro;apply PermFlows_refl|]. 
      iApply (adv_monotone with "Hadv_val"); auto. }
    (* We are now ready to show that all registers point to a valid word *)
    iDestruct (sts_full_world_std with "[] Hsts") as %Hstd'';[iPureIntro;split;apply related_sts_priv_refl|].     
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W'' (r !r! r1))%I
      with "[-Hsts Hr Hmaps Hvalid Hna Hφ Hflag]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
          [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_adv)); [by left|right;auto].  
      }
      - iIntros "%". contradiction.
      - assert (r !! r_stk = Some (inr (RWLX, Local, s_first', e_r, s_last'))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk fixpoint_interp1_eq. 
        iIntros (_). iExists RWLX. iSplitR; [auto|].
        iAssert ([∗ list] a ∈ region_addrs s_first' e_r, read_write_cond a RWLX (fixpoint interp1)
                             ∧ ⌜region_state_pwl W'' a⌝ ∧ ⌜region_std W'' a⌝)%I as "#Hstack_adv_val". 
        { rewrite Hstackeq app_assoc.
          iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_val']".
          iApply (big_sepL_mono with "Hstack_val'").
          iIntros (k y Hsome) "Hy".
          rewrite Hstackeq app_assoc in Hrevoked.
          apply Forall_app in Hrevoked as [_ Hrevoked].
          iFrame. iPureIntro;split.
          - apply close_list_std_sta_revoked.
            + apply elem_of_list_fmap. eexists _; split;[eauto|]. apply elem_of_list_lookup; eauto.
            + revert Hrevoked. rewrite Forall_forall =>Hrevoked. apply Hrevoked.
              apply elem_of_list_lookup; eauto.
          - revert Hrevoked. rewrite Forall_forall =>Hrevoked.
            rewrite /region_std. apply Hrevoked. apply elem_of_list_lookup; eauto. 
        }
        iFrame "Hstack_adv_val". 
        iAlways.
        rewrite /exec_cond.
        iIntros (y r' W3 Hay Hrelated3). iNext.
        iApply fundamental.
        + iRight. iRight. done.
        + iExists RWLX. iSplit; auto. simpl.
          iApply (adv_stack_monotone with "Hstack_adv_val"); auto. 
      - (* continuation *)
        iIntros (_).
        assert (r !! r_t0 = Some (inr (E, Local, b_r, e_r, stack_own_b))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 fixpoint_interp1_eq. iSimpl. 
        (* prove continuation *)
        iAlways.
        iIntros (r' W3 Hrelated3).
        iNext. iSimpl. 
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hr & Hsts & Hna)". 
        iSplit; [auto|rewrite /interp_conf].
        (* get the PC, currently pointing to the activation record *)
        iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
        (* get some registers *)
        iGet_genpur_reg_map r' r_t1 "Hmreg'" "Hfull'" "[Hr_t1 Hmreg']".
        iGet_genpur_reg_map r' r_stk "Hmreg'" "Hfull'" "[Hr_stk Hmreg']".
        iGet_genpur_reg_map r' r_adv "Hmreg'" "Hfull'" "[Hr_adv Hmreg']".
        iGet_genpur_reg_map r' r_self "Hmreg'" "Hfull'" "[Hr_self Hmreg']".
        iGet_genpur_reg_map r' r_env "Hmreg'" "Hfull'" "[Hr_env Hmreg']".
        (* we open the local stack *)
        iMod (na_inv_open logrel_nais ⊤ ⊤ with "Hlocal Hna") as "(Hframe & Hna & Hcls)";auto.
        (* we need to assert that the local state is Live *)
        iDestruct (bi.later_exist with "Hframe") as (x) "[>Hstate Hframe]". 
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hj.
        iDestruct (sts_full_rel_loc with "Hsts Hrelj") as %Hrel. 
        assert (x = Live) as ->.
        { apply (local_state_related_sts_pub W'' W3 j);auto; rewrite /W'' /= lookup_insert; auto. }
        iDestruct "Hframe" as ">(Hb_r & Ha2 & Ha3 & Hframe)". 
        (* prepare the new stack value *)
        assert (is_Some (s_last' + (0 - 1))%a) as [stack_new Hstack_new].
        { do 7 (let a := fresh "a" in destruct stack_own as [|a stack_own];[inversion Hlength_own|]).
          destruct stack_own;[|inversion Hlength_own]. exists a14. simpl in Hs_last; inversion Hs_last; subst.
          rewrite -(addr_add_assoc a14 _ 1);[|iContiguous_next Hstackcont 9]. apply addr_add_0. }
        (* step through instructions in activation record *)
        iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
          [| |by rewrite /PermFlows /=|iContiguous_next Hcont_rest0 0|apply Hstack_new|..]. 
        { apply isCorrectPC_intro;[|by left]. split; [apply (incr_list_ge_middle _ 3 _ _ Hstackcont); auto|]. 
          apply (incr_list_lt_middle_alt _ 3 _ _ Hstackcont); auto. repeat rewrite app_length. rewrite Hlength_own /=. lia. }
        { apply isCorrectPC_intro;[|by left].
          assert (([b_r; a2; a3] ++ (stack_own_b :: stack_own) ++ region_addrs s_first' e_r) !! 10 = Some s_last') as Hlast'.
          { rewrite lookup_app_r;[|lia]. rewrite lookup_app_l;[|lia].
            assert (10 - length [b_r; a2; a3] = length (stack_own_b :: stack_own) - 1) as ->;[simpl;inversion Hlength_own as [Heq]; rewrite Heq;auto|].
            rewrite -last_lookup; auto. }
          split;[apply (incr_list_ge_middle _ 10 _ _ Hstackcont)|apply (incr_list_lt_middle_alt _ 10 _ _ Hstackcont)];auto.
          repeat rewrite app_length. rewrite Hlength_own /=. destruct (region_addrs s_first' e_r); inversion Hs_first'; simpl; lia. }
        iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
        iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
        iDestruct "Hr_t1" as (wrt1) "Hr_t1".
        (* we can now step through the rest of the program *)
        (* to do that wee need to open the non atomic invariant of the program *)
        iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|]. 
        rewrite Hrest_app /=. repeat rewrite app_comm_cons. 
        iDestruct (mapsto_decomposition _ _ _ (take 84 (awkward_instrs r_self r_adv 65 flag_off)) with "Hprog")
          as "[Hprog_done [Ha Hprog] ]". 
        { simpl. inversion Hscall_length as [Heq]. rewrite Heq. omega. }
        (* let's prove some practical lemmas before continuing *)
        assert (last (rest0_first :: a9 :: rest0) = Some a_last) as Hlast0.
        { rewrite Hrest_app in Hlast. repeat rewrite app_comm_cons in Hlast.
          by rewrite -last_app_eq in Hlast; [|simpl;lia]. }
        iCombine "Ha" "Hprog_done" as "Hprog_done".
        (* sub r_t1 0 7 *)
        iPrologue rest0 Hrest_length "Hprog".
        iApply (wp_add_sub_lt_success with "[$HPC Hr_t1 $Hinstr]");
          [right; left; apply sub_z_z_i|apply PermFlows_refl|iCorrectPC rest0_first a9 a_last 1 Hcont_rest0|
           iSimpl;iFrame;eauto|iSimpl;rewrite sub_z_z_i].
        assert (a9 + 1 = Some a8)%a as ->;[iContiguous_next Hcont_rest0 1|]. 
        iEpilogue "(HPC & Hinstr & _ & _ & Hr_t1)".
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* lea r_stk r_t1 *)
        iPrologue rest0 Hrest_length "Hprog". 
        assert ((stack_new + (0 - 7))%a = Some a3) as Hpop.
        { rewrite -(addr_add_assoc a3 _ 7);[apply addr_add_0|].
          rewrite -Hstack_new. assert (7 = 1 + 6)%Z as ->;[lia|].
          rewrite (addr_add_assoc a3 stack_own_b 1);[|iContiguous_next Hstackcont 2].
          assert (6 = 7 + (0 - 1))%Z as ->;[lia|]. rewrite (addr_add_assoc stack_own_b s_last' 7); auto. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
          [apply lea_r_i|apply PermFlows_refl|iCorrectPC rest0_first a8 a_last 2 Hcont_rest0|
           iContiguous_next Hcont_rest0 2|apply Hpop|auto..].
        iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
        (* pop r_stk r_adv *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a10;a11;a12] (a13::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a3 + (0 - 1))%a = Some a2) as Hpop.
        { rewrite -(addr_add_assoc a2 _ 1);[apply addr_add_0|iContiguous_next Hstack_local 1]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_adv Ha3"];
          [split;[iCorrectPC rest0_first a10 a_last 3 Hcont_rest0|split;
                 [iCorrectPC rest0_first a11 a_last 4 Hcont_rest0|iCorrectPC rest0_first a12 a_last 5 Hcont_rest0] ]|
           apply PermFlows_refl|isWithinBounds_stack Hcont_stack 2|auto|
           iContiguous_next Hcont_rest0 3|iContiguous_next Hcont_rest0 4|iContiguous_next Hcont_rest0 5|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_adv & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_self *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a13;a14;a15] (a16::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a2 + (0 - 1))%a = Some b_r) as Hpop.
        { rewrite -(addr_add_assoc b_r _ 1);[apply addr_add_0|iContiguous_next Hstack_local 0]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_self Ha2"];
          [split;[iCorrectPC rest0_first a13 a_last 6 Hcont_rest0|split;
                 [iCorrectPC rest0_first a14 a_last 7 Hcont_rest0|iCorrectPC rest0_first a15 a_last 8 Hcont_rest0] ]|
           apply PermFlows_refl|isWithinBounds_stack Hcont_stack 1|auto|
           iContiguous_next Hcont_rest0 6|iContiguous_next Hcont_rest0 7|iContiguous_next Hcont_rest0 8|apply Hpop|..].
        iNext. iIntros "(HPC & Hpop & Hr_self & Ha2 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_env *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a16;a17;a18] (a19::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((b_r + (0 - 1))%a = Some b_r') as Hpop.
        { rewrite -(addr_add_assoc b_r' _ 1);[apply addr_add_0|auto]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Hb_r"];
          [split;[iCorrectPC rest0_first a16 a_last 9 Hcont_rest0|split;
                 [iCorrectPC rest0_first a17 a_last 10 Hcont_rest0|iCorrectPC rest0_first a18 a_last 11 Hcont_rest0] ]|
           apply PermFlows_refl|isWithinBounds;omega|auto|
           iContiguous_next Hcont_rest0 9|iContiguous_next Hcont_rest0 10|iContiguous_next Hcont_rest0 11|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_env & Hb_r & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* store r_env 1 *)
        iPrologue rest0 Hrest_length "Hprog".
        (* Storing 1 will always constitute a public future world of W3 *)
        iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a20)
                       ∗ r_env ↦ᵣ inr (RWX, Global, d, d, d)
                       ∗ a19 ↦ₐ[pc_p] store_z r_env 1
                       ∗ region (W3.1,(<[i:=countable.encode true]> W3.2.1,W3.2.2))
                       ∗ sts_full_world sts_std (W3.1,(<[i:=countable.encode true]> W3.2.1,W3.2.2))
                       ∗ ⌜(∃ y, W3.2.1 !! i = Some (countable.encode y)) ∧ W3.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝
                       -∗ WP Seq (Instr Executable) {{ v, φ v }})
                   -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
          with "[HPC Hinstr Hr_env Hr Hsts]" as "Hstore_step".
        { iIntros (φ') "Hφ".
          iInv ι as (y) "[>Hstate Hb]" "Hcls".
          iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
          iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrellookup. 
          destruct y; iDestruct "Hb" as ">Hb".
          - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
              [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC rest0_first a19 a_last 12 Hcont_rest0|
               iContiguous_next Hcont_rest0 12|split;[auto|isWithinBounds;done]|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ". iFrame.
            rewrite (insert_id _ i);[|auto].
            destruct W3 as [W3_std [W3_loc_pub W3_lo_priv] ]. iFrame. eauto. 
          - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
              [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC rest0_first a19 a_last 12 Hcont_rest0|
               iContiguous_next Hcont_rest0 12|split;[auto|isWithinBounds;done]|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod (sts_update_loc _ _ _ true with "Hsts Hstate") as "[Hsts Hstate] /=".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ".
            iFrame. iSplitL;[|eauto]. iApply (region_monotone with "[] [] Hr");[auto|..].
            iPureIntro. apply related_pub_local_1 with false; auto. 
        }
        iApply "Hstore_step". iNext. iIntros "(HPC & Hr_env & Hinstr & Hr & Hsts & #HW3lookup)".
        iDestruct "HW3lookup" as %[HW3lookup Hw3rel]. 
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* push r_stk r_env *)
        do 2 (destruct rest0;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a20;a21] (a22::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Hb_r"];
          [|apply PermFlows_refl|by isWithinBounds|iContiguous_next Hcont_rest0 13|iContiguous_next Hcont_rest0 14|apply Hb_r|..].
        { split;[iCorrectPC rest0_first a20 a_last 13 Hcont_rest0|iCorrectPC rest0_first a21 a_last 14 Hcont_rest0]. }
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
        (* push r_stk r_self *)
        do 2 (destruct rest0;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a22;a23] (a24::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_self Ha2"];
          [|apply PermFlows_refl|isWithinBounds_stack Hcont_stack 1|iContiguous_next Hcont_rest0 15|
           iContiguous_next Hcont_rest0 16|iContiguous_next Hstack_local 0|..].
        { split;[iCorrectPC rest0_first a22 a_last 15 Hcont_rest0|iCorrectPC rest0_first a23 a_last 16 Hcont_rest0]. }
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha2)". iCombine "Hpush" "Hprog_done" as "Hprog_done". 
        (* push r_stk r_adv *)
        do 2 (destruct rest0;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a24;a25] (a26::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_adv Ha3"];
          [|apply PermFlows_refl|isWithinBounds_stack Hcont_stack 2|iContiguous_next Hcont_rest0 17|
           iContiguous_next Hcont_rest0 18|iContiguous_next Hstack_local 1|..].
        { split;[iCorrectPC rest0_first a24 a_last 17 Hcont_rest0|iCorrectPC rest0_first a25 a_last 18 Hcont_rest0]. }
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_adv & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done". 
        (* SECOND SCALL *)
        (* before invoking the scall spec, we need to revoke the adversary stack region *)
        iMod (monotone_revoke_keep _ (region_addrs s_first' e_r) with "[$Hsts $Hr]") as "(Hsts & Hr & Hstack_adv)";[apply NoDup_ListNoDup, region_addrs_NoDup|..]. 
        { rewrite Hstackeq app_assoc.
          iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_adv]".
          iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hr".
          rewrite /read_write_cond. iFrame. iPureIntro.
          assert (region_state_pwl W3 y) as Hlookup;[|auto].
          revert Hrevoked; rewrite Forall_forall =>Hrevoked.
          apply region_state_pwl_monotone with W''; eauto.
          - apply Hrevoked. rewrite Hstackeq.
            do 2 (apply elem_of_app;right).
            apply elem_of_list_lookup. eauto. 
          - rewrite /W'' /region_state_pwl /std_sta /=.
            apply close_list_std_sta_revoked; [apply elem_of_list_fmap_1, elem_of_list_lookup; eauto|]. 
            apply Hrevoked. rewrite Hstackeq.
            do 2 (apply elem_of_app;right).
            apply elem_of_list_lookup. eauto.
        }
        (* we now want to extract the final element of the local stack, which will now be handed off to the adversary *)
        do 2 (iDestruct (big_sepL_sep with "Hstack_adv") as "[Hstack_adv _]").
        iAssert (▷ (∃ ws_adv : list Word, [[s_first',e_r]]↦ₐ[RWLX][[ws_adv]]))%I with "[Hstack_adv]" as ">Hstack_adv".
        { iNext.
          iDestruct (region_addrs_exists with "Hstack_adv") as (ws_adv') "Hstack_adv".
          iDestruct (big_sepL2_sep with "Hstack_adv") as "[_ Hstack_adv]". iDestruct (big_sepL2_sep with "Hstack_adv") as "[Hstack_adv _]".
          iExists (ws_adv'). iFrame.
        }
        (* prepare for scall *)
        (* split the program into the scall_prologue and the rest *)
        iDestruct (contiguous_program_split with "Hprog") as (scall_prologue1 rest1 scall_last1 rest1_first)
                                                               "(Hscall & Hf2 & #Hcont)"; [auto|simpl;lia|simpl;lia|..].
        { repeat (apply contiguous_weak in Hcont_rest0; try done). }
        iDestruct "Hcont" as %(Hcont_scall1 & Hcont_rest1 & Hrest_app1 & Hscall_last1 & Hrest1_first & Hlink1). subst.
        iDestruct (big_sepL2_length with "Hscall") as %Hscall_length1. simpl in Hscall_length1.
        destruct scall_prologue1 as [|scall_prologue_first1 scall_prologue1];[inversion Hscall_length1|].
        assert (scall_prologue_first1 = a26) as <-;[inversion Hrest_app1;auto|].
        (* we can now invoke the stack call prologue *)
        iApply scall_prologue_spec; last (iFrame "Hscall HPC Hr_stk"; iSplitL "Hmreg' Hr_env Hr_self Hr_t1";
                                          [|iSplitL "Hframe";[iNext;eauto|iSplitL "Hstack_adv";[iNext;eauto|] ] ]);
        [iCorrectPC rest0_first scall_prologue_first1 a_last 19 Hcont_rest0| |isWithinBounds_stack Hcont_stack 3|
         |apply Hpos|apply Hcont_scall1|auto|apply Hscall_last1|
         apply PermFlows_refl|iNotElemOfList|iContiguous_next Hstackcont 2|apply Hstack_own_bound|..|apply Hlink1| |].
        { assert (length scall_prologue1 - 1 = 75) as Heq;[simpl in Hscall_length1; lia|]. 
          iCorrectPC rest0_first scall_last1 a_last 95 Hcont_rest0;
            (rewrite Hrest_app1 /= lookup_app_l;[rewrite -Heq -last_lookup; destruct scall_prologue1;[inversion Hscall_length1|auto]|simpl in Hscall_length1;lia]). }
        { isWithinBounds_stack Hstackcont 11; inversion Hlength_own as [Heq]; rewrite /= Heq lookup_app_r;rewrite Heq; auto. }
        { assert (8 = 7 + 1)%Z as ->;[auto|]. rewrite (addr_add_assoc _ s_last'); auto. }
        { apply (contiguous_incr_addr_middle _ 19 77 scall_prologue_first1 _ Hcont_rest0); auto.
          rewrite -Hscall_length1 Hrest_app1 /= lookup_app_r;[|lia]. rewrite PeanoNat.Nat.sub_diag; auto. }
        { iNext. iApply region_addrs_exists.
          iClose_genpur_reg_map r_env "[Hr_env $Hmreg']" "Hmreg'".
          iClose_genpur_reg_map r_self "[Hr_self $Hmreg']" "Hmreg'".
          repeat (rewrite -(delete_commute _ r_t1)). 
          iClose_genpur_reg_map r_t1 "[Hr_t1 $Hmreg']" "Hmreg'".
          iDestruct ("Hfull'") as %Hfull. 
          iDestruct (big_sepM_to_big_sepL _ (list_difference all_registers [PC; r_stk; r_adv]) with "Hmreg'") as "$Hmlist". 
          - apply NoDup_list_difference. apply all_registers_NoDup.
          - intros r0 Hin. apply elem_of_list_difference in Hin as [Hin Hnin].
            revert Hnin. repeat rewrite not_elem_of_cons. intros (Hne1 & Hne2 & Hne3 & _).
            destruct (decide (r0 = r_t1));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            destruct (decide (r0 = r_self));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            destruct (decide (r0 = r_env));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            rewrite delete_insert_delete. repeat (rewrite lookup_delete_ne;auto). apply Hfull. 
        }
        iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hgen_reg & Hstack_own & Hstack_adv & Hscall)".
        iCombine "Hscall" "Hprog_done" as "Hprog_done".
        assert (isCorrectPC (inr (pc_p, pc_g, pc_b, pc_e, rest1_first))) as Hvpc1''.
        { iCorrectPC rest0_first rest1_first a_last 96 Hcont_rest0;
            (rewrite Hrest_app1 /=;inversion Hscall_length1; rewrite lookup_app_r;[rewrite PeanoNat.Nat.sub_diag; auto|auto]). }
        (* jmp r_adv *)
        iDestruct (big_sepL2_length with "Hf2") as %Hrest_length1; simpl in Hrest_length1. 
        destruct rest1;[inversion Hrest_length1|]. 
        iPrologue rest1 Hrest_length1 "Hf2". inversion Hrest1_first; subst.
        iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
          [apply jmp_i|apply PermFlows_refl|auto|..].
        iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".
        (* again we are jumping to unknown code. We will now need to close all our invariants so we can reestablish the FTLR 
           on the new state *)
        (* we close the invariant for our program *)
        iMod ("Hcls'" with "[Hprog_done Hprog Hinstr $Hna]") as "Hna".
        { iNext. iDestruct "Hprog_done" as "(Hscall & Hpush3 & Hpush2 & push1 & Ha19 & Hpop1 & Hpop2 & 
                                             Hpop3 & Ha8 & Ha9 & Hrest0_first & Hprog_done)".
          iApply (big_sepL2_app with "Hprog_done [-]").
          iFrame "Hrest0_first Ha9 Ha8". 
          iApply (big_sepL2_app with "Hpop3 [-]").
          iApply (big_sepL2_app with "Hpop2 [-]").
          iApply (big_sepL2_app with "Hpop1 [-]").
          iFrame "Ha19".
          iApply (big_sepL2_app with "push1 [-]").
          iApply (big_sepL2_app with "Hpush2 [-]").
          iApply (big_sepL2_app with "Hpush3 [-]").
          rewrite Hrest_app1. 
          iApply (big_sepL2_app with "Hscall [-]"). iFrame.
        }
        (* lets define the world before we close the adv stack invariant *)
        evar (W4 : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
        instantiate (W4 := (W3.1.1, std_rel (W3.1, (<[i:=countable.encode true]> W3.2.1, W3.2.2)),
                            (<[j:=countable.encode Released]> (<[i:=countable.encode true]> W3.2.1), W3.2.2))).
        assert (related_sts_priv_world (W3.1, (<[i:=countable.encode true]> W3.2.1, W3.2.2)) W4) as Hrelated4.
        { apply related_priv_local_2;auto. }
        (* Since the current region is revoked, we can privately update it *)
        iAssert (sts_full_world sts_std (revoke (W3.1, (<[i:=countable.encode true]> W3.2.1, W3.2.2))) ∗ region (revoke W4))%I with "[Hsts Hr]" as "[Hsts Hr]".
        { rewrite region_eq /region_def.
          iDestruct "Hr" as (M) "(HM & % & Hr)".
          iApply bi.sep_exist_l. iExists (M). 
          iAssert (⌜dom_equal (std_sta (revoke W4)) M⌝)%I as "#Hdom";[|iFrame "Hdom HM"].
          { iPureIntro. rewrite /W4 /std_sta /=. auto. }
          iApply (monotone_revoke_list_region_def_mono $! Hrelated4 with "[] Hsts Hr").
          by rewrite -dom_equal_revoke. 
        } 
        (* before we close our stack invariants, we want to privately update our local stack invariant *)
        iMod (sts_update_loc _ j Live Released with "Hsts Hstate") as "[Hsts Hstate]".
        iMod ("Hcls" with "[Hstate $Hna]") as "Hna".
        { iNext. iExists Released. iFrame. }
        iAssert (sts_full_world sts_std (revoke W4)) with "Hsts" as "Hsts". 
        (* now that we have privately updated our resources, we can close the region invariant for the adv stack *)
        iDestruct (sts_full_world_std with "[] Hsts") as %Hstd3;[iPureIntro;split;apply related_sts_priv_refl|].
        (* finally we can now close the region: a_last' will be in state revoked in revoke(W3) *)
        assert (∀ k x, (region_addrs s_first' e_r) !! k = Some x ->
                       revoke_std_sta W3.1.1 !! countable.encode x = Some (countable.encode Revoked)) as Hlookup_revoked.
        { intros k x Hsome.
          rewrite Hstackeq app_assoc in Hrevoked. apply Forall_app in Hrevoked as [Hrevoked_last Hrevoked].
          apply revoke_lookup_Temp. inversion Hsome. 
          apply (Forall_lookup_1 _ _ k x) in Hrevoked as [Hstd_x Hrevoked_x]; auto. 
          apply region_state_pwl_monotone with W''; auto.
          rewrite /W'' /region_state_pwl /std_sta /=.
          apply close_list_std_sta_revoked; auto. 
          apply elem_of_list_fmap. exists x. split; auto. apply elem_of_list_lookup_2 with k. auto.
        } 
        iMod (monotone_close _ (region_addrs s_first' e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
                with "[$Hsts $Hr Hstack_adv ]") as "[Hsts Hex]".
        { iClear "Hreg' Hfull' full Hlocal Hrelj IH Hf4 Hrel Hinv Hadv_val".
          rewrite Hstackeq app_assoc. 
          iDestruct (region_addrs_zeroes_trans with "Hstack_adv") as "Hstack_adv".
          iDestruct (big_sepL_app with "Hstack_val") as "[Hstack_last Hstack_val']".
          iApply big_sepL_sep. iSplitL.
          - iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hy".
            iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
            + iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
            + by repeat (rewrite fixpoint_interp1_eq /=).
          - iApply big_sepL_sep; iFrame "#". iApply big_sepL_forall. iPureIntro.
            auto. 
        }
        (* finally we allocate a new local region for the local stack *)
        iMod (sts_alloc_loc _ Live local_rel_pub local_rel_priv with "Hsts")
          as (k) "(Hsts & % & % & Hstate & #Hrelk)".
        iMod (na_inv_alloc logrel_nais ⊤ (regN.@"stack_1") (∃ x:local_state, sts_state_loc k x
                                 ∗ match x with
                                   | Live => b_r ↦ₐ[RWLX] inr (RWX, Global, d, d, d)
                                                ∗ a2 ↦ₐ[RWLX] inr (pc_p, pc_g, pc_b, pc_e, a_first)
                                                ∗ a3 ↦ₐ[RWLX] inr (E, Global, b, e, a)
                                                ∗ [[stack_own_b,s_last']]↦ₐ[RWLX][[ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                                                                                     inr (pc_p, pc_g, pc_b, pc_e, rest1_first);
                                                                                     inr (RWLX, Local, b_r, e_r, s_last')] ]]
                                   | Released => emp
                                   end)%I
                with "[Hstack_own Hstate Hb_r Ha2 Ha3]")
          as "#Hlocal_1".
        { iNext. iExists Live. iFrame. }
        (* for future use, we will need to know that i is not equal to j *)
        assert (i ≠ k) as Hneik.
        { assert (i ∈ dom (gset positive) (close_list (countable.encode <$> region_addrs s_last' e_r) (revoke W4)).2.1) as Hcontr.
          - apply elem_of_dom. rewrite lookup_insert_ne;[rewrite lookup_insert|auto]. eauto.
          - intros Heq; subst. contradiction.
        }
        (* The resulting world is a private future world of W3 *)
        iSimpl in "Hsts". 
        evar (W5 : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
        instantiate (W5 :=
                       (close_list_std_sta (countable.encode <$> region_addrs s_first' e_r) (std_sta (revoke W4)), std_rel (revoke W4),
                        (<[k:=countable.encode Live]> (<[j:=countable.encode Released]> (<[i:=countable.encode true]> W3.2.1)),
                         <[k:=(convert_rel local_rel_pub, convert_rel local_rel_priv)]> W3.2.2))).
        assert (related_sts_pub_world (close_list (countable.encode <$> region_addrs s_first' e_r) (revoke W4)) W5) as Hrelated5'.
        { split;[apply related_sts_pub_refl|].
          apply related_sts_pub_fresh with _ (countable.encode Live) (convert_rel local_rel_pub, convert_rel local_rel_priv) _ in H5;auto. 
        }
        assert (related_sts_priv_world W3 W5) as Hrelated5.
        { eapply related_sts_priv_pub_trans_world;[|apply Hrelated5'].
          eapply related_sts_priv_pub_trans_world;[|apply close_list_related_sts_pub;auto].
          eapply related_sts_priv_trans_world;[apply revoke_related_sts_priv|];auto.
          apply revoke_monotone; auto. eapply related_sts_priv_trans_world;[|apply Hrelated4].
          apply related_sts_pub_priv_world. destruct HW3lookup as [y Hy]. apply related_pub_local_1 with y; auto.
        }
        (* we can now finally monotonically update the region to match the new sts collection *)
        iDestruct (region_monotone _ W5 with "[] [] Hex") as "Hr";[rewrite /std_sta /=;auto|auto|..].
        iAssert (sts_full_world sts_std W5) with "Hsts" as "Hsts".
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hreli. 
        (* We choose the r *)
        evar (r2 : gmap RegName Word).
        instantiate (r2 := <[PC    := inl 0%Z]>
                          (<[r_stk := inr (RWLX, Local, s_first', e_r, s_last')]>
                           (<[r_t0  := inr (E, Local, b_r, e_r, stack_own_b)]>
                            (<[r_adv := inr (E, Global, b, e, a)]>
                             (create_gmap_default
                                (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
        (* We have all the resources of r *)
        iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r2))
          with "[Hgen_reg Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
        { iApply (registers_mapsto_resources with "Hgen_reg Hr_stk Hr_t0 Hr_adv HPC"). } 
        (* r contrains all registers *)
        iAssert (full_map r2) as "#Hfull2";[iApply r_full|].
        iSimpl in "Hadv_val".
        iAssert (interp_expression r2 W5 (inr (RX, Global, b, e, a)))
          as "Hvalid". 
        { iApply fundamental. iLeft; auto. iExists RX. iSplit;[iPureIntro;apply PermFlows_refl|]. 
          iApply (adv_monotone with "Hadv_val");[|auto].
          eapply related_sts_priv_trans_world;[|apply Hrelated5].
            by eapply related_sts_priv_pub_trans_world;[|apply Hrelated3]. }
        (* the adversary stack is valid in the W5 *)
        iAssert ([∗ list] a ∈ region_addrs s_first' e_r, read_write_cond a RWLX (fixpoint interp1)
                                                             ∗ ⌜region_state_pwl W5 a⌝ ∧ ⌜region_std W5 a⌝)%I as "#Hstack_adv_val". 
        { rewrite Hstackeq app_assoc.
          iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_val']".
          iApply big_sepL_sep. iSplit.
          - iApply (big_sepL_mono with "Hstack_val'").
            iIntros (g y Hsome) "Hy". iFrame.
          - iApply big_sepL_forall. iPureIntro.
            intros g y Hsome. split. 
            + apply close_list_std_sta_revoked; auto.
              apply elem_of_list_fmap. exists y. split; auto. apply elem_of_list_lookup_2 with g. auto.
              rewrite /W4 /revoke /std_sta /=. by apply Hlookup_revoked with g. 
            + apply related_sts_rel_std with W'; auto.
              { apply related_sts_priv_trans_world with W3;auto.
                apply related_sts_priv_pub_trans_world with W'';auto. }
              rewrite Hstackeq app_assoc in Hrevoked.
              apply Forall_app in Hrevoked as [Hrevoked_last Hrevoked].
              revert Hrevoked. rewrite Forall_forall =>Hrevoked.
              apply Hrevoked. apply elem_of_list_lookup; eauto.  
        }   
        (* We are now ready to show that all registers point to a valid word *)
        iDestruct (sts_full_world_std with "[] Hsts") as %Hstd5;[iPureIntro;split;apply related_sts_priv_refl|].     
        iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W5 (r2 !r! r1))%I
          with "[-Hsts Hr Hmaps Hvalid Hna Hflag]" as "Hreg".
        { iIntros (r1).
          assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
              [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
          { destruct (decide (r1 = PC)); [by left|right].
            destruct (decide (r1 = r_stk)); [by left|right].
            destruct (decide (r1 = r_t0)); [by left|right].
            destruct (decide (r1 = r_adv)); [by left|right;auto].  
          }
          - iIntros "%". contradiction.
          - assert (r2 !! r_stk = Some (inr (RWLX, Local, s_first', e_r, s_last'))) as Hr_stk; auto. 
            rewrite /RegLocate Hr_stk fixpoint_interp1_eq. 
            iIntros (_). iExists RWLX. iSplitR; [auto|].
            iAssert ([∗ list] a ∈ region_addrs s_first' e_r, read_write_cond a RWLX (fixpoint interp1)
                                                             ∧ ⌜region_state_pwl W5 a⌝ ∧ ⌜region_std W5 a⌝)%I as "#Hstack_adv_val'". 
            { iApply (big_sepL_mono with "Hstack_adv_val"). iIntros (g y Hsome) "(Hr & Hrev & Hstd)". iFrame. }
            iFrame "Hstack_adv_val'". 
            iAlways.
            rewrite /exec_cond.
            iIntros (y r3 W6 Hay Hrelated6). iNext.
            iApply fundamental.
            + iRight. iRight. done.
            + iExists RWLX. iSplit; auto. simpl.
              iApply (adv_stack_monotone with "Hstack_adv_val'"); auto. 
          - (* continuation *)
            iIntros (_). clear Hr_t0. 
            assert (r2 !! r_t0 = Some (inr (E, Local, b_r, e_r, stack_own_b))) as Hr_t0; auto. 
            rewrite /RegLocate Hr_t0 fixpoint_interp1_eq. iSimpl. 
            (* prove continuation *)
            iAlways.
            iIntros (r3 W6 Hrelated6).
            iNext. iSimpl. 
            iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)". 
            iSplit; [auto|rewrite /interp_conf].
            (* get the PC, currently pointing to the activation record *)
            iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
            (* get some registers *)
            iGet_genpur_reg_map r3 r_t1 "Hmreg'" "Hfull3" "[Hr_t1 Hmreg']".
            iGet_genpur_reg_map r3 r_stk "Hmreg'" "Hfull3" "[Hr_stk Hmreg']".
            iGet_genpur_reg_map r3 r_adv "Hmreg'" "Hfull3" "[Hr_adv Hmreg']".
            iGet_genpur_reg_map r3 r_self "Hmreg'" "Hfull3" "[Hr_self Hmreg']".
            iGet_genpur_reg_map r3 r_env "Hmreg'" "Hfull3" "[Hr_env Hmreg']".
            (* we open the local stack *)
            iMod (na_inv_open logrel_nais ⊤ ⊤ with "Hlocal_1 Hna") as "(Hframe & Hna & Hcls)";auto.
            (* we need to assert that the local state is Live *)
            iDestruct (bi.later_exist with "Hframe") as (x) "[>Hstate Hframe]". 
            iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hj'.
            iDestruct (sts_full_rel_loc with "Hsts Hrelk") as %Hrel'. 
            assert (x = Live) as ->.
            { apply (local_state_related_sts_pub W5 W6 k); auto; rewrite /W5 /= lookup_insert; auto. }
            iDestruct "Hframe" as ">(Hb_r & Ha2 & Ha3 & Hframe)". 
            (* prepare the new stack value *)
            (* assert (is_Some (stack_new + (0 - 1))%a) as [stack_new_1 Hstack_new_1]. *)
            (* { do 7 (let a := fresh "a" in destruct stack_own as [|a stack_own];[inversion Hlength_own|]). *)
            (*      rewrite -(addr_add_assoc a3 stack_new 7);[|auto]. exists a29. *)
            (*      apply (contiguous_incr_addr_middle _ 2 6 _ _ Hcont_stack); auto. } *)
            (* step through instructions in activation record *)
            iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
              [| |by rewrite /PermFlows /=|iContiguous_next Hcont_rest1 0|apply Hstack_new|..]. 
            { apply isCorrectPC_intro;[|by left]. split; [apply (incr_list_ge_middle _ 3 _ _ Hstackcont); auto|]. 
              apply (incr_list_lt_middle_alt _ 3 _ _ Hstackcont); auto. repeat rewrite app_length. rewrite Hlength_own /=. lia. }
            { apply isCorrectPC_intro;[|by left].
              assert (([b_r; a2; a3] ++ (stack_own_b :: stack_own) ++ region_addrs s_first' e_r) !! 10 = Some s_last') as Hs_last_lookup.
              { rewrite lookup_app_r;[|lia]. rewrite lookup_app_l;[|lia].
                assert (10 - length [b_r; a2; a3] = length (stack_own_b :: stack_own) - 1) as ->;[simpl;inversion Hlength_own as [Heq]; rewrite Heq;auto|].
                rewrite -last_lookup; auto. }
               split;[apply (incr_list_ge_middle _ 10 _ _ Hstackcont)|apply (incr_list_lt_middle_alt _ 10 _ _ Hstackcont)];auto.
              repeat rewrite app_length. rewrite Hlength_own /=. destruct (region_addrs s_first' e_r); inversion Hs_first'; simpl; lia. }
            iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
            iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
            iDestruct "Hr_t1" as (wrt1') "Hr_t1".
            (* we don't want to close the stack invariant yet, as we will now need to pop it *)
            (* go through rest of the program. We will now need to open the invariant and destruct it into its done and prog part *)
            (* sub r_t1 0 7 *)
            iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|]. 
            rewrite Hrest_app1 /=. repeat rewrite app_comm_cons. rewrite app_assoc.
            iDestruct (mapsto_decomposition _ _ _ ([store_z r_env 0] ++
                                                   push_r_instrs r_stk r_env ++
                                                   push_r_instrs r_stk r_self ++
                                                   push_r_instrs r_stk r_adv ++
                                                   scall_prologue_instrs 65 r_adv ++
                                                   [jmp r_adv;
                                                    sub_z_z r_t1 0 7;
                                                    lea_r r_stk r_t1] ++
                                                   pop_instrs r_stk r_adv ++
                                                   pop_instrs r_stk r_self ++
                                                   pop_instrs r_stk r_env ++
                                                   [store_z r_env 1] ++
                                                   push_r_instrs r_stk r_env ++
                                                   push_r_instrs r_stk r_self ++
                                                   push_r_instrs r_stk r_adv ++
                                                   scall_prologue_instrs 65 r_adv) with "Hprog")
              as "[Hprog_done [Ha Hprog] ]". 
            { simpl. inversion Hscall_length as [Heq]. inversion Hscall_length1 as [Heq']. rewrite app_length Heq /=. rewrite Heq'. done. }
            (* let's prove some practical lemmas before continuing *)
            assert (last (rest1_first :: a27 :: rest1) = Some a_last) as Hlast1.
            { rewrite Hrest_app in Hlast. repeat rewrite app_comm_cons in Hlast.
              rewrite -last_app_eq in Hlast;[|simpl;apply gt_Sn_O].
              rewrite Hrest_app1 in Hlast. repeat rewrite app_comm_cons in Hlast.
              by rewrite -last_app_eq in Hlast;[|simpl;apply gt_Sn_O]. }
            iCombine "Ha" "Hprog_done" as "Hprog_done".
            (* sub r_t1 0 7 *)
            iPrologue rest1 Hrest_length1 "Hprog".
            iApply (wp_add_sub_lt_success with "[$HPC Hr_t1 $Hinstr]");
              [right; left; apply sub_z_z_i|apply PermFlows_refl|iCorrectPC rest1_first a27 a_last 1 Hcont_rest1|
               iSimpl;iFrame;eauto|iSimpl;rewrite sub_z_z_i].
            assert (a27 + 1 = Some a26)%a as ->;[iContiguous_next Hcont_rest1 1|]. 
            iEpilogue "(HPC & Hinstr & _ & _ & Hr_t1)".
            iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* lea r_stk r_t1 *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            assert ((stack_new + (0 - 7))%a = Some a3) as Hpop1.
            { rewrite -(addr_add_assoc a3 _ 7);[apply addr_add_0|].
              rewrite -Hstack_new. assert (7 = 1 + 6)%Z as ->;[lia|].
              rewrite (addr_add_assoc a3 stack_own_b 1);[|iContiguous_next Hstackcont 2].
              assert (6 = 7 + (0 - 1))%Z as ->;[lia|]. rewrite (addr_add_assoc stack_own_b s_last' 7); auto. }
            iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
              [apply lea_r_i|apply PermFlows_refl|iCorrectPC rest1_first a26 a_last 2 Hcont_rest1|
               iContiguous_next Hcont_rest1 2|apply Hpop1|auto..].
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* pop r_stk r_adv *)
            do 3 (destruct rest1; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a28;a29;a30] (a31::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a3 + (0 - 1))%a = Some a2) as Hpop1.
            { rewrite -(addr_add_assoc a2 _ 1);[apply addr_add_0|iContiguous_next Hstack_local 1]. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_adv Ha3"];
              [split;[iCorrectPC rest1_first a28 a_last 3 Hcont_rest1|split;
                     [iCorrectPC rest1_first a29 a_last 4 Hcont_rest1|iCorrectPC rest1_first a30 a_last 5 Hcont_rest1] ]|
               apply PermFlows_refl|isWithinBounds_stack Hcont_stack 2|auto|
               iContiguous_next Hcont_rest1 3|iContiguous_next Hcont_rest1 4|iContiguous_next Hcont_rest1 5|apply Hpop1|..].
            iNext. iIntros "(HPC & Hpop & Hr_adv & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* pop r_stk r_self *)
            do 3 (destruct rest1; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a31;a32;a33] (a34::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a2 + (0 - 1))%a = Some b_r) as Hpop1.
            { rewrite -(addr_add_assoc b_r _ 1);[apply addr_add_0|iContiguous_next Hstack_local 0]. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_self Ha2"];
              [split;[iCorrectPC rest1_first a31 a_last 6 Hcont_rest1|split;
                     [iCorrectPC rest1_first a32 a_last 7 Hcont_rest1|iCorrectPC rest1_first a33 a_last 8 Hcont_rest1] ]|
               apply PermFlows_refl|isWithinBounds_stack Hcont_stack 1|auto|
               iContiguous_next Hcont_rest1 6|iContiguous_next Hcont_rest1 7|iContiguous_next Hcont_rest1 8|apply Hpop1|..].
            iNext. iIntros "(HPC & Hpop & Hr_self & Ha2 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* pop r_stk r_env *)
            do 3 (destruct rest1; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a34;a35;a36] (a37::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((b_r + (0 - 1))%a = Some b_r') as Hpop1.
            { rewrite -(addr_add_assoc b_r' _ 1);[apply addr_add_0|auto]. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Hb_r"];
              [split;[iCorrectPC rest1_first a34 a_last 9 Hcont_rest1|split;
                     [iCorrectPC rest1_first a35 a_last 10 Hcont_rest1|iCorrectPC rest1_first a36 a_last 11 Hcont_rest1] ]|
               apply PermFlows_refl|isWithinBounds;done|auto|
               iContiguous_next Hcont_rest1 9|iContiguous_next Hcont_rest1 10|iContiguous_next Hcont_rest1 11|apply Hpop1|..].
            iNext. iIntros "(HPC & Hpop & Hr_env & Hb_r & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* we have now arrived at the final load of the environment. we must here assert that the loaded
               value is indeed 1. We are able to show this since W6 is a public future world of W5, in which 
               invariant i is in state true *)
            (* load r_adv r_env *)
            iPrologue rest1 Hrest_length1 "Hprog".
            iGet_genpur_reg_map r3 r_t2 "Hmreg'" "Hfull3" "[Hr_t2 Hmreg']".
            iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a38)
                                ∗ r_env ↦ᵣ inr (RWX, Global, d, d, d)
                                ∗ a37 ↦ₐ[pc_p] load_r r_t2 r_env
                                ∗ sts_full_world sts_std W6
                                ∗ r_t2 ↦ᵣ inl 1%Z
                                -∗ WP Seq (Instr Executable) {{ v, φ v }})
                            -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
              with "[HPC Hinstr Hr_env Hr_t2 Hsts]" as "Hload_step".
            { iIntros (φ') "Hφ'".
              iInv ι as (x) "[>Hstate Hb]" "Hcls".
              iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hi.
              assert (x = true) as ->.
              { apply related_pub_lookup_local with W5 W6 i;auto.
                do 2 (rewrite lookup_insert_ne; auto). apply lookup_insert. }
              iDestruct "Hb" as ">Hb".
              iAssert (⌜(d =? a37)%a = false⌝)%I as %Hne.
              { destruct (d =? a37)%a eqn:Heq;auto. apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
                iDestruct (cap_duplicate_false with "[$Hinstr $Hb]") as "Hfalse";[|done]. destruct pc_p;auto.
                inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
              iApply (wp_load_success with "[$HPC $Hinstr $Hr_t2 $Hr_env Hb]");
                [apply load_r_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC rest1_first a37 a_last 12 Hcont_rest1
                 |auto|iContiguous_next Hcont_rest1 12|auto|rewrite Hne;iFrame|rewrite Hne].
              { split;auto. isWithinBounds; apply Z.le_refl. }
              iNext. iIntros "(HPC & Hr_adv & Ha37 & Hr_env & Hd)".
              iMod ("Hcls" with "[Hstate Hd]") as "_".
              { iNext. iExists true. iFrame. }
              iModIntro. iApply wp_pure_step_later;auto;iNext.
              iApply "Hφ'". iFrame. 
            }
            iApply "Hload_step".
            iNext. iIntros "(HPC & Hr_env & Ha37 & Hsts & Hr_t2)".
            (* We can now assert that r_adv indeed points to 1 *)
            (* move r_t1 PC *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            iApply (wp_move_success_reg_fromPC with "[$HPC $Hr_t1 $Hinstr]");
              [apply move_r_i|apply PermFlows_refl|iCorrectPC rest1_first a38 a_last 13 Hcont_rest1|
               iContiguous_next Hcont_rest1 13|auto|..].
            iEpilogue "(HPC & Hinstr & Hr_t1)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* lea r_t1 5 *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            do 3 (destruct rest1;[inversion Hrest_length1|]).
            assert ((a38 + 5)%a = Some a43) as Hincr;[apply (contiguous_incr_addr_middle _ 13 5 _ _ Hcont_rest1); auto|].
            iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t1]");
              [apply lea_z_i|apply PermFlows_refl|iCorrectPC rest1_first a39 a_last 14 Hcont_rest1|
               iContiguous_next Hcont_rest1 14|apply Hincr|auto|..].
            { inversion Hvpc1 as [?????? Hpc_p]; destruct Hpc_p as [Hpc_p | [Hpc_p | Hpc_p] ]; congruence. }
            iEpilogue "(HPC & Hinstr & Hr_t1)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* sub r_t2 r_t2 1 *)
            iDestruct "Hprog" as "[Hinstr Hprog]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_add_sub_lt_success with "[$HPC $Hinstr Hr_t2]");
              [right;left;apply sub_r_z_i|apply PermFlows_refl|iCorrectPC rest1_first a40 a_last 15 Hcont_rest1|
               iSimpl;iFrame;eauto|iSimpl;rewrite sub_r_z_i]. 
            assert ((a40 + 1)%a = Some a41) as ->;[iContiguous_next Hcont_rest1 15|]. 
            iEpilogue "(HPC & Hinstr & _ & _ & Hr_t2)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".  
            (* jnz r_self *)
            iDestruct "Hprog" as "[Hinstr Hprog]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_jnz_success_next with "[$HPC $Hinstr $Hr_t2]");
              [apply jnz_i|apply PermFlows_refl|iCorrectPC rest1_first a41 a_last 16 Hcont_rest1|iContiguous_next Hcont_rest1 16|..].
            iEpilogue "(HPC & Hinstr & Hr_t2)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".  
            (* Since the assertion succeeded, we are now ready to jump back to r_self, i.e. the start of the program *)
            (* jmp r_self *)
            iDestruct "Hprog" as "[Hinstr Hprog]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_self]");
              [apply jmp_i|apply PermFlows_refl|iCorrectPC rest1_first a42 a_last 17 Hcont_rest1|]. 
            iEpilogue "(HPC & Hinstr & Hr_self)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".  
            (* We must now apply the IH! in order to do that we start out by closing our program invariant *)
            iMod ("Hcls'" with "[$Hna Hprog_done Hprog Ha37]") as "Hna". 
            { iNext. iDestruct "Hprog_done" as "(Ha42 & Ha41 & Ha40 & Ha39 & Ha38 & 
                                                 Hpop3 & Hpop2 & Hpop1 & Ha24 & Ha25 & Hrest1_first & Hprog_done)".
              iApply (big_sepL2_app with "Hprog_done [-]").
              iFrame "Hrest1_first Ha25 Ha24". 
              iApply (big_sepL2_app with "Hpop1 [-]").
              iApply (big_sepL2_app with "Hpop2 [-]").
              iApply (big_sepL2_app with "Hpop3 [-]").
              iFrame "Ha37 Ha38 Ha39 Ha40 Ha41 Ha42". iFrame.
            }
            iDestruct (sts_full_world_std with "[] Hsts") as %Hstd6;[iPureIntro;split;apply related_sts_priv_refl|].     
            (* next we want to close the invariant for the local stack. However we need to release the contents 
               so we can apply the IH. Going from Live to Release is a private update, and we therefore need 
               to revoke region. This also fits the fact that we need to revoke the stack resources for applying the IH *)
            iMod (monotone_revoke_keep _ (region_addrs s_first' e_r) with "[$Hsts $Hr]") as "(Hsts & Hr & Hstack_adv)";[apply NoDup_ListNoDup, region_addrs_NoDup|..]. 
            { iClear "Hreg' Hfull' full Hlocal Hrelj IH Hf4 Hrel Hinv Hadv_val Hfull2 Hfull3 Hlocal_1 Hrelk Hreg3".
              iAssert ( [∗ list] a39 ∈ region_addrs s_first' e_r, ⌜std_sta W6 !! countable.encode a39 = Some (countable.encode Temporary)⌝
                                        ∗ rel a39 RWLX (λ Wv : prodO STS STS * Word, ((fixpoint interp1) Wv.1) Wv.2))%I as "Hstack_val'". 
              { iApply big_sepL_sep. iDestruct (big_sepL_sep with "Hstack_adv_val") as "#[Hstack_adv_val' Hstack_adv_r]".
                iFrame "Hstack_adv_val'".
                iApply (big_sepL_mono with "Hstack_adv_r").
                iIntros (k0 y Hsome) "#[Hr Hx]".
                iDestruct "Hr" as %Hr; iDestruct "Hx" as %Hx. 
                iPureIntro. apply region_state_pwl_monotone with W5; auto.
              }
              iApply (big_sepL_mono with "Hstack_val'").
              iIntros (k0 y Hsome) "[Hr Hx]"; iFrame "Hr Hx".
            }
            iDestruct (big_sepL_sep with "Hstack_adv") as "[Hstack_adv_val' #Hrevoked]".
            iDestruct (big_sepL_sep with "Hstack_adv_val'") as "[Hstack_adv Hstack_adv_val']".
            iAssert (▷ (∃ ws : list Word, [[b_r,e_r]]↦ₐ[RWLX][[ws]]))%I with "[Hstack_adv Hframe Hb_r Ha2 Ha3]" as ">Hstack".
            { iNext.
              iDestruct (region_addrs_exists with "Hstack_adv") as (ws_adv') "Hstack_adv".
              iDestruct (big_sepL2_sep with "Hstack_adv") as "[_ Hstack_adv]". iDestruct (big_sepL2_sep with "Hstack_adv") as "[Hstack_adv _]".
              iExists (_ :: _ :: _ :: _ ++ ws_adv').
              rewrite /region_mapsto Hstackeq app_assoc. repeat rewrite app_comm_cons.
              assert (stack_own_b :: stack_own = region_addrs stack_own_b s_last') as <-.
              { apply contiguous_region_addrs; auto. }
              iApply mapsto_decomposition;[|iSimpl;iFrame "Hstack_adv Hb_r Ha2 Ha3 Hframe"]. 
              by rewrite app_length Hlength_own.
            }
            (* Since the current region is revoked, we can privately update it *)
            iDestruct (sts_full_rel_loc with "Hsts Hrelk") as %Hlookupk.
            iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hstate. 
            iAssert ((sts_full_world sts_std (revoke W6))
                       ∗ region (revoke (W6.1, (<[k:=countable.encode Released]> W6.2.1, W6.2.2))))%I with "[Hsts Hr]" as "[Hsts Hr]".
            { rewrite region_eq /region_def.
              iDestruct "Hr" as (M) "(HM & % & Hr)".
              iApply bi.sep_exist_l. iExists (M).
              iAssert (⌜dom_equal (std_sta (revoke (W6.1, (<[k:=countable.encode Released]> W6.2.1, W6.2.2)))) M⌝)%I
                as "#Hdom";[|iFrame "Hdom HM"].
              { iPureIntro. rewrite /std_sta /=. auto. }
              iApply (monotone_revoke_list_region_def_mono with "[] [] Hsts Hr");[|by rewrite -dom_equal_revoke].
              iPureIntro. rewrite /revoke /loc /= in Hlookupk,Hstate. apply related_priv_local_3; auto. 
            }
            (* before we close our stack invariants, we want to privately update our local stack invariant *)
            iMod (sts_update_loc _ k Live Released with "Hsts Hstate") as "[Hsts Hstate]".
            iMod ("Hcls" with "[Hstate $Hna]") as "Hna".
            { iNext. iExists Released. iFrame. }
            evar (W7 : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
            instantiate (W7 := (revoke (W6.1, (<[k:=countable.encode Released]> W6.2.1, W6.2.2)))).
            assert (related_sts_priv_world W6 W7) as Hrelated7.
            { apply related_sts_priv_trans_world with (revoke W6);[apply revoke_related_sts_priv;auto|].
              apply revoke_monotone;auto. apply related_priv_local_3; auto. 
            }
            assert (related_sts_priv_world W' W7) as Hrelated8.
            { apply related_sts_priv_trans_world with W6; [|auto].
              apply related_sts_priv_pub_trans_world with W5; [|auto].
              apply related_sts_priv_trans_world with W3; [|auto].
              apply related_sts_priv_pub_trans_world with W''; auto. }
            iAssert (sts_full_world sts_std W7) with "Hsts" as "Hsts". 
            iAssert (region W7) with "Hr" as "Hr".
            iAssert (⌜Forall (λ a : Addr, region_type_revoked W7 a) (region_addrs b_r e_r)⌝)%I as %Hrevoked7.
            { iRevert (Hrevoked). repeat rewrite Forall_forall. iIntros (Hrevoked). iIntros (x Hx).
              specialize (Hrevoked _ Hx). 
              apply elem_of_list_lookup in Hx as [x0 Hx0]. 
              iDestruct (big_sepL_lookup _ _ x0 x Hx0 with "Hstack_val") as "#Hrel_x".
              assert (∃ (ρ : region_type), (std_sta W7) !! (countable.encode x) = Some (countable.encode ρ)) as [ρ Hρ].
              { destruct Hrevoked as [Hrevoked_x Hstd_x].
                apply related_sts_priv_world_std_sta_region_type with W' Revoked;[apply Hrelated8|eauto|eauto].
              }
              destruct ρ;[| |auto]. 
              - iDestruct (region_open_temp_pwl _ _ _ _ Hρ with "[$Hrel_x $Hr $Hsts]") as (v) "(_ & _ & _ & Hcontr & _)";[auto|..].
                iDestruct "Hstack" as (ws) "Hstack". rewrite /region_mapsto.
                iDestruct (big_sepL2_extract_l _ _ _ _ _ Hx0 with "Hstack") as "[_ Hcontr']".
                iDestruct "Hcontr'" as (b0) "Hcontr'".
                iDestruct (cap_duplicate_false with "[$Hcontr $Hcontr']") as "Hfalse"; [auto..|by iApply bi.False_elim].
              - iDestruct (region_open_perm _ _ _ _ Hρ with "[$Hrel_x $Hr $Hsts]") as (v) "(_ & _ & _ & Hcontr & _)";[auto|..].
                iDestruct "Hstack" as (ws) "Hstack". rewrite /region_mapsto.
                iDestruct (big_sepL2_extract_l _ _ _ _ _ Hx0 with "Hstack") as "[_ Hcontr']".
                iDestruct "Hcontr'" as (b0) "Hcontr'".
                iDestruct (cap_duplicate_false with "[$Hcontr $Hcontr']") as "Hfalse"; [auto..|by iApply bi.False_elim].
            }
            (* insert general purpose registers back into map *)
            repeat (rewrite -(delete_commute _ r_t1)). 
            iClose_genpur_reg_map r_t1 "[Hr_t1 $Hmreg']" "Hmreg'".
            iClose_genpur_reg_map r_t2 "[Hr_t2 $Hmreg']" "Hmreg'".
            rewrite delete_insert_delete. 
            repeat (rewrite -(delete_insert_ne _ _ r_t1); [|auto]).
            repeat (rewrite -(delete_insert_ne _ _ r_t2); [|auto]).
            iApply ("IH" $! W7 with "Hr_stk [HPC] Hr_self Hr_adv Hr_env [Hmreg'] Hstack Hna [] Hsts Hr").
            { destruct pc_p; iFrame. inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
            { assert ([r_t0; r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10;
                       r_t11; r_t12; r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20;
                       r_t21; r_t22; r_t23;r_t24; r_t25; r_t26; r_t27] =
                      list_difference all_registers [r_env;r_self;r_adv;r_stk;PC]) as ->;[auto|]. 
              iApply region_addrs_exists.
              iDestruct "Hfull3" as %Hfull3. 
              iApply (big_sepM_to_big_sepL with "Hmreg'"); 
                [apply NoDup_list_difference; apply all_registers_NoDup|].
              intros r0 Hin. apply elem_of_list_difference in Hin as [Hin Hnin].
              revert Hnin. repeat rewrite not_elem_of_cons. intros (Hne1 & Hne2 & Hne3 & Hne4 & Hne5 & _).
              repeat rewrite lookup_delete_ne; auto.
              destruct (decide (r_t2 = r0)) as [-> | Hne6];[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto]. 
              destruct (decide (r_t1 = r0)) as [-> | Hne7];[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              apply Hfull3. 
            }
            { iApply (adv_monotone with "Hadv_val"); auto.
              apply related_sts_priv_trans_world with W'; auto.
              apply related_sts_priv_trans_world with (revoke W); auto.
              apply revoke_related_sts_priv; auto. 
            }
            { iNext. iIntros (v) "Hv". iFrame.
              iIntros (->). 
              iSpecialize ("Hv" with "[]");[auto|]. 
              iDestruct "Hv" as (r0 W8) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
              iExists _,_. iFrame. iPureIntro.
              apply related_sts_priv_trans_world with W7; auto.
            }
            { iPureIntro.
              apply Forall_and. split; auto. 
              apply Forall_forall. intros x Hx.
              apply (related_sts_rel_std _ _ _ Hrelated8).
              revert Hrevoked; rewrite Forall_forall =>Hrevoked. by apply Hrevoked.
            } 
      - rewrite Hr_t30. 
        assert (r !! r_adv = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some fixpoint_interp1_eq. iSimpl. 
        iIntros (_). 
        iAlways. rewrite /enter_cond.
        iIntros (r0 W2 Hrelated2). 
        iNext. iApply fundamental.
        iLeft. done.
        iExists RX. iSplit; auto.
        iApply (adv_monotone with "Hadv_val"); auto.
        apply related_sts_priv_trans_world with W''; auto.
        eapply related_sts_priv_trans_world;[apply related_sts_pub_priv_world;apply Hrelated3|].
        apply related_sts_priv_trans_world with W5; auto.
      - rewrite r_zero; auto.
        rewrite fixpoint_interp1_eq. iPureIntro. auto.
        }
        iDestruct ("Hvalid" with "[$Hsts $Hr $Hna $Hfull2 $Hmaps $Hreg]")
          as "[_ Ho]". 
        iApply wp_wand_r. iFrame.
        iIntros (v) "Hhalted".
        iIntros (->).
        iSpecialize ("Hhalted" with "[]");[auto|]. 
        iDestruct "Hhalted" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
        iExists _,_. iFrame. 
        iPureIntro. eapply related_sts_priv_trans_world;[apply Hrelated5|auto]. 
      - rewrite Hr_t30. 
        assert (r !! r_adv = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some fixpoint_interp1_eq. iSimpl. 
        iIntros (_). 
        iAlways. iIntros (r' W3 Hrelated3). 
        iNext. iApply fundamental.
        iLeft. done.
        iExists RX. iSplit; simpl; auto.
        iApply (adv_monotone with "Hadv_val");auto.
        eapply related_sts_priv_trans_world;[apply HWW''|auto].          
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        iIntros (Hne). 
        assert (r !r! r1 = inl 0%Z) as Hr1.
        { rewrite /RegLocate.
          destruct (r !! r1) eqn:Hsome; rewrite Hsome; last done. rewrite /r in Hsome. 
          do 4 (rewrite lookup_insert_ne in Hsome;auto). 
          assert (Some w2 = Some (inl 0%Z)) as Heq.
          { rewrite -Hsome. apply create_gmap_default_lookup.
            apply elem_of_list_difference. split; first apply all_registers_correct.
            repeat (apply not_elem_of_cons;split;auto).
            apply not_elem_of_nil. 
          }
            by inversion Heq. 
        }
        rewrite Hr1 fixpoint_interp1_eq. iPureIntro. eauto.         
    }
    iAssert (((interp_reg interp) W'' r))%I as "#HvalR";[iSimpl;auto|]. 
    iSpecialize ("Hvalid" with "[$HvalR $Hmaps Hsts $Hna $Hr]"); iFrame. 
    iDestruct "Hvalid" as "[_ Ho]". 
    rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros (->). 
    iSpecialize ("Htest" with "[]");[auto|]. 
    iDestruct "Htest" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
    iExists _,_. iFrame.
    iPureIntro. eapply related_sts_priv_trans_world;[apply HWW''|auto]. 
    Unshelve. done.
  Qed. 

End awkward_example. 
