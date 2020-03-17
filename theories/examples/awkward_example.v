From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants. 
Require Import Eqdep_dec. 
From cap_machine Require Import rules logrel fundamental region_invariants region_invariants_revocation. 
From cap_machine.examples Require Import region_macros stack_macros scall malloc.

Lemma big_sepM_to_big_sepL {Σ : gFunctors} {A B : Type} `{EqDecision A} `{Countable A}
      (r : gmap A B) (lr : list A) (φ : A → B → iProp Σ) :
  NoDup lr →
  (∀ r0, r0 ∈ lr → ∃ b, r !! r0 = Some b) →
  ([∗ map] k↦y ∈ r, φ k y) -∗ ([∗ list] y ∈ lr, ∃ b, φ y b).
Proof.
  iInduction (lr) as [ | r0 ] "IHl" forall (r); iIntros (Hdup Hlookup) "Hmap".
  - done.
  - assert (∃ b, r !! r0 = Some b) as [b Hr0].
    { apply Hlookup. apply elem_of_cons. by left. } 
    iDestruct (big_sepM_delete _ _ r0 with "Hmap") as "[Hr0 Hmap]"; eauto.
    iSplitL "Hr0".
    + iExists b. iFrame. 
    + iApply ("IHl" with "[] [] [$Hmap]").
      { iPureIntro. apply NoDup_cons_12 in Hdup. auto. }
      iPureIntro.
      intros r1 Hr1.
      destruct (decide (r0 = r1)).
      * subst. apply NoDup_cons in Hdup as [Hnelem Hdup]. contradiction. 
      * rewrite lookup_delete_ne;auto. apply Hlookup.
        apply elem_of_cons. by right.
Qed.

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

  Lemma push_r_instrs_extract a i j r prog p' :
    contiguous_between a i j →
    ([∗ list] a_i;w_i ∈ a; (push_r_instrs r_stk r ++ prog), a_i ↦ₐ[p'] w_i) -∗
    ∃ a' push2 a_rest,
      (([∗ list] a_i;w_i ∈ [i; push2];push_r_instrs r_stk r, a_i ↦ₐ[p'] w_i) ∗
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

  Ltac iPush_r prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let push2 := fresh "push2" in
    let Ha1 := fresh "Ha1" in
    let Ha2 := fresh "Ha2" in
    let Ha := fresh "Ha" in
    iDestruct (push_r_instrs_extract with prog) as (a_rest push2 cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha2 & Ha);
    iApply (push_r_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha Hreg";
    last iRename "Hprog" into prog.
  
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
  
   (* Recall that the malloc subroutine lies in b_m e_m *)

   (* assume that r1 contains an executable pointer to the malloc subroutine *)
   (* Definition awkward_preamble_instrs r1 offset_to_awkward := *)
   (*   [move_r r_t0 PC; *)
   (*   lea_z r_t0 3; *)
   (*   jmp r1; *)
   (*   move_r r_self PC; *)
   (*   lea_z r_self offset_to_awkward; *)
   (*   jmp r_self]. *)
   
   (* assume r1 contains an executable pointer to adversarial code *)
  (* assume r0 contains an executable pointer to the awkward example *)
   Definition awkward_instrs (r1 : RegName) epilogue_off :=
     [store_z r_env 0] ++
     push_r_instrs r_stk r_env ++
     push_r_instrs r_stk r_t0 ++
     push_r_instrs r_stk r1 ++
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r1 ++
     pop_instrs r_stk r_t0 ++
     pop_instrs r_stk r_env ++
     [store_z r_env 1] ++
     push_r_instrs r_stk r_env ++
     push_r_instrs r_stk r_t0 ++ 
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r_t0 ++
     pop_instrs r_stk r_env ++
     (* assert that the cap in r_env points to 1 *)
     [load_r r1 r_env;
     move_r r_t1 PC;
     lea_z r_t1 59; (* offset to assertion failure *)
     sub_r_z r1 r1 1;
     jnz r_t1 r1] ++
     (* in this version, we will clear before retuning *)
     mclear_instrs r_stk 10 2 ++
     rclear_instrs (list_difference all_registers [PC;r_t0]) ++
     [jmp r_t0].

   (* TODO: possibly add fail to awkward example? *)
  
   (* Definition awkward_preamble a p r1 offset_to_awkward := *)
   (*   ([∗ list] a_i;w_i ∈ a;(awkward_preamble_instrs r1 offset_to_awkward), a_i ↦ₐ[p] w_i)%I. *)
   
   Definition awkward_example (a : list Addr) (p : Perm) (r1 : RegName) epilogue_off : iProp Σ :=
     ([∗ list] a_i;w_i ∈ a;(awkward_instrs r1 epilogue_off), a_i ↦ₐ[p] w_i)%I.

   
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
   (* Lemma g1_spec φ W pc_p pc_g pc_b pc_e (* PC *) *)
   (*       g1_addrs offset_to_awkward (* g1 *) *)
   (*       a_first a_last a_cont (* special adresses *) : *)

   (*   (* PC assumptions *) *)
   (*   isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a_first)) ∧ *)
   (*   isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a_last)) → *)
     
   (*   (* Program adresses assumptions *) *)
   (*   contiguous g1_addrs -> *)
   (*   g1_addrs !! 0 = Some a_first ∧ list.last g1_addrs = Some a_last -> *)

   (*   (* Address assumptions *) *)
   (*   (a_first + (3 + offset_to_awkward))%a = Some a_cont -> *)

   (*   ((* PC *) *)
   (*     PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first) *)
   (*    (* assume r_t1 points to a the malloc subroutine *) *)
   (*    ∗ r_t1 ↦ᵣ inr (E,Global,b_m,e_m,a_m) *)
   (*    ∗ [[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine r_env 1]] *)
   (*    (* general purpose registers *) *)
   (*    ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [r_t1;PC]; wsr, r_i ↦ᵣ w_i) *)
   (*    (* program *) *)
   (*    ∗ awkward_preamble g1_addrs pc_p r_t1 offset_to_awkward *)
   (*    (* region invariants *) *)
   (*    ∗ region W *)
   (*    ∗ sts_full_world sts_std W *)
   (*    (* continuation *) *)
   (*    ∗ ▷ ((PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_cont) *)
   (*        ∗ r_self ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_cont) *)
   (*        ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_self;r_env]; wsr, r_i ↦ᵣ w_i)     *)
   (*        ∗ ∃ d, r_env ↦ᵣ inr (RWX,Global,d,d,d) *)
   (*        ∗ (∃ (i : positive), region (awk_W W i) ∗ sts_full_world sts_std (awk_W W i) ∗ sts_rel_loc i awk_rel_pub awk_rel_priv ∗ (∃ ι, inv ι (awk_inv i d)))) *)
   (*        -∗ WP Seq (Instr Executable) {{ φ }}) *)
   (*    ⊢ WP Seq (Instr Executable) {{ φ }})%I. *)
   (* Proof.  *)
   (*   iIntros ([Hvpc1 Hvpc2] Hcont [Hfirst Hlast] Ha_cont) "(HPC & Hr_t1 & Hmalloc & Hr_gen & Hprog & Hr & Hsts & Hφ)". *)
   (*   iDestruct (big_sepL2_length with "Hprog") as %Hprog_length. *)
   (*   destruct g1_addrs; [inversion Hprog_length|]. *)
   (*   simpl in Hfirst; inversion Hfirst; subst. *)
   (*   iDestruct "Hr_gen" as (wsr) "Hr_gen". *)
   (*   iDestruct (big_sepL2_length with "Hr_gen") as %Hwsr. *)
   (*   rewrite /all_registers /=.  *)
   (*   iGet_genpur_reg "Hr_gen" Hwsr wsr "[Hr_t0 Hr_gen]".  *)
   (*   (* move r_t1 PC *) *)
   (*   iPrologue g1_addrs Hprog_length "Hprog". *)
   (*   iApply (wp_move_success_reg_fromPC with "[$HPC $Hinstr $Hr_t0]"); *)
   (*     [apply move_r_i|apply PermFlows_refl|auto|iContiguous_next Hcont 0|auto|]. *)
   (*   iEpilogue "(HPC & Hprog_done & Hr_t0)". *)
   (*   (* lea r_t0 2 *) *)
   (*   iPrologue g1_addrs Hprog_length "Hprog". *)
   (*   destruct g1_addrs;[inversion Hprog_length|]. *)
   (*   assert (a_first + 3 = Some a1)%a as Ha1;[apply (contiguous_incr_addr _ 3 a_first _ Hcont); auto|]. *)
   (*   iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t0]"); *)
   (*     [apply lea_z_i|apply PermFlows_refl|iCorrectPC a_first a a_last 1 Hcont|iContiguous_next Hcont 1|apply Ha1|auto..].  *)
   (*   { destruct pc_p; auto. inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. } *)
   (*   iEpilogue "(HPC & Ha & Hr_t0)". iCombine "Ha" "Hprog_done" as "Hprog_done".  *)
   (*   (* jmp r_t1 *) *)
   (*   iPrologue g1_addrs Hprog_length "Hprog".  *)
   (*   iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_t1]"); *)
   (*     [apply jmp_i|apply PermFlows_refl|iCorrectPC a_first a0 a_last 2 Hcont|].  *)
   (*   iEpilogue "(HPC & Ha0 & Hr_t1)"; iCombine "Ha0" "Hprog_done" as "Hprog_done". *)
   (*   iSimpl in "HPC".  *)
   (*   (* malloc subroutine *) *)
   (*   iApply (malloc_spec W); last iFrame "Hmalloc Hr_t0 HPC". *)
   (*   iSplitL "Hr_gen Hr_t1". *)
   (*   { iExists (_ :: wsr). rewrite /all_registers /=. iFrame. } *)
   (*   iNext. iIntros "(_ & Hgen_reg & HPC & Hbe)". *)
   (*   (* Since we are dynamically allocating local state, we do not need the freshness requirement *) *)
   (*   iDestruct "Hbe" as (b e Hsize) "(Hr_env & Hbe & _)". *)
   (*   (* Allocate a new invariant *) *)
   (*   rewrite Z.sub_diag in Hsize. rewrite /region_mapsto /region_addrs_zeroes /region_addrs.  *)
   (*   destruct (Z_le_dec b e);[|omega].  *)
   (*   assert (region_size b e = 1) as ->;[by rewrite /region_size Hsize /=|].  *)
   (*   iDestruct "Hbe" as "[Hb _]". *)
   (*   iDestruct "Hgen_reg" as (wsr') "Hgen_reg". clear Hwsr.  *)
   (*   iMod (sts_alloc_loc W false awk_rel_pub awk_rel_priv with "Hsts") *)
   (*     as (i) "(Hsts & % & % & Hstate & #Hrel)". *)
   (*   iMod (inv_alloc (regN.@b) _ (awk_inv i b) with "[Hstate Hb]")%I as "#Hb". *)
   (*   { iNext. iExists false. iFrame. } *)
   (*   (* Prepare to jump to f4 *) *)
   (*   (* move_r r_self PC *) *)
   (*   iDestruct "Hprog" as "[Hinstr Hprog]". *)
   (*   iApply (wp_bind (fill [SeqCtx])). *)
   (*   iDestruct (big_sepL2_extract_l 29 r_self with "Hgen_reg") as "[Hr_gen Hr_self]";[auto|rewrite /all_registers /=]. *)
   (*   iDestruct "Hr_self" as (w) "Hr_self".  *)
   (*   iApply (wp_move_success_reg_fromPC with "[$HPC $Hinstr $Hr_self]"); *)
   (*     [apply move_r_i|apply PermFlows_refl|iCorrectPC a_first a1 a_last 3 Hcont|iContiguous_next Hcont 3|auto|].  *)
   (*   iEpilogue "(HPC & Hinstr & Hr_self)"; iCombine "Hinstr" "Hprog_done" as "Hprog_done". *)
   (*   (* lea r_self offset_to_awkward *) *)
   (*   iPrologue g1_addrs Hprog_length "Hprog". *)
   (*   assert ((a1 + offset_to_awkward)%a = Some a_cont) as Hcont';[rewrite (addr_add_assoc _ a1) in Ha_cont;auto|]. *)
   (*   iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_self]"); *)
   (*     [apply lea_z_i|apply PermFlows_refl|iCorrectPC a_first a2 a_last 4 Hcont|iContiguous_next Hcont 4|apply Hcont'|auto..]. *)
   (*   { destruct pc_p; auto. inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. } *)
   (*   iEpilogue "(HPC & Hinstr & Hr_self)"; iCombine "Hinstr" "Hprog_done" as "Hprog_done". *)
   (*   (* jmp r_self *) *)
   (*   iDestruct "Hprog" as "[Hinstr _]". *)
   (*   iApply (wp_bind (fill [SeqCtx])). *)
   (*   iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_self]"); *)
   (*     [apply jmp_i|apply PermFlows_refl|iCorrectPC a_first a3 a_last 5 Hcont|]. *)
   (*   iEpilogue "(HPC & Hinstr & Hr_self)"; iCombine "Hinstr" "Hprog_done" as "_". *)
   (*   (* continuation *) *)
   (*   iApply "Hφ". iFrame "Hr_gen Hr_self". *)
   (*   iSplitL "HPC". *)
   (*   { destruct pc_p; iFrame. inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. } *)
   (*   assert (b = e)%a as ->;[apply z_of_eq;lia|]. *)
   (*   iExists e. iFrame. *)
   (*   iExists i. iFrame "∗ #". iSplitL;[|eauto].  *)
   (*   iApply (region_monotone with "[] [] Hr"); [auto|]. *)
   (*   iPureIntro. split;[apply related_sts_pub_refl|simpl].  *)
   (*   apply related_sts_pub_fresh; auto. *)
   (* Qed. *)

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

   (* The following lemma asserts that the world upon return is indeed a public future world of W *)
   (* As the first step we want to show that if we assert that the closed region corresponds to ALL the 
      temporary region, then closing a revoked W equals W *)
   
   Lemma related_pub_local_2 W W' W3 W6 b e l i k j c c' :
     W' = ((revoke_std_sta W.1.1,W.1.2),(<[i:=countable.encode false]> W.2.1,W.2.2))
     -> (∃ M, dom_equal W6.1.1 M)
     -> (forall (a : Addr), W.1.1 !! (countable.encode a) = Some (countable.encode Temporary) <-> a ∈ l)
     -> (b <= c < e)%a ∧ (b <= c' < e)%a -> (∃ l', l = l' ++ (region_addrs b e))
     -> j ∉ dom (gset positive) W'.2.1 → j ∉ dom (gset positive) W'.2.2
     → k ∉ dom (gset positive) (<[j:=countable.encode Released]> (<[i:=countable.encode true]> W3.2.1)) → k ∉ dom (gset positive) W3.2.2
     → W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)
     -> (∃ (b : bool), W.2.1 !! i = Some (countable.encode b))
     -> rel_is_std W6             
     → related_sts_pub_world
         (close_list_std_sta (countable.encode <$> region_addrs c e) W'.1.1, W'.1.2,
          (<[j:=countable.encode Live]> W'.2.1,
           <[j:=(convert_rel local_rel_pub, convert_rel local_rel_priv)]> W'.2.2)) W3
     → related_sts_pub_world
         (close_list_std_sta (countable.encode <$> region_addrs c' e)
                             (revoke_std_sta W3.1.1), W3.1.2,
          (<[k:=countable.encode Live]>
           (<[j:=countable.encode Released]> (<[i:=countable.encode true]> W3.2.1)),
           <[k:=(convert_rel local_rel_pub, convert_rel local_rel_priv)]> W3.2.2)) W6
     → related_sts_pub_world W (close_list_std_sta (countable.encode <$> l) (revoke_std_sta W6.1.1),
                                W6.1.2, (<[k:=countable.encode Released]> W6.2.1, W6.2.2)).
   Proof.
     intros Heq Hdom Hiff1 Hbounds Happ Hj1 Hj2 Hk1 Hk2 Hawk [x Hawki] HstdW6 Hrelated1 Hrelated2. 
     subst W'. 
     destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
     destruct W3 as [ [Wstd_sta3 Wstd_rel3] [Wloc_sta3 Wloc_rel3] ]. 
     destruct W6 as [ [Wstd_sta6 Wstd_rel6] [Wloc_sta6 Wloc_rel6] ].
     simpl in *.
     split; simpl. 
     - destruct Hrelated1 as [Hstd_related1 _]. 
       destruct Hrelated2 as [Hstd_related2 _]. simpl in *. 
       destruct Hstd_related2 as [Hstd_sta_dom2 [Hstd_rel_dom2 Hstd_related2] ].
       destruct Hstd_related1 as [Hstd_sta_dom1 [Hstd_rel_dom1 Hstd_related1] ].
       assert (dom (gset positive) Wstd_sta ⊆ dom (gset positive) Wstd_sta6) as Hsub.
       { rewrite -close_list_dom_eq -revoke_dom_eq in Hstd_sta_dom2.
         rewrite -close_list_dom_eq -revoke_dom_eq in Hstd_sta_dom1. etrans;eauto. }
       split;[|split].
       + rewrite -close_list_dom_eq -revoke_dom_eq. auto. 
       + etrans;eauto. 
       + intros i0 r1 r2 r1' r2' Hr Hr'.
         assert (i0 ∈ dom (gset positive) Wstd_rel3) as Hin.
         { apply elem_of_subseteq in Hstd_rel_dom1. apply Hstd_rel_dom1. apply elem_of_dom. eauto. }
         apply elem_of_dom in Hin as [ [r3 r3'] Hr3].
         specialize (Hstd_related2 i0 r3 r3' r1' r2' Hr3 Hr') as [Heq1 [Heq2 Hstd_related2] ]. subst. 
         specialize (Hstd_related1 i0 r1 r2 r1' r2' Hr Hr3) as [Heq1 [Heq2 Hstd_related1] ]. subst.
         repeat (split;auto).
         assert (rel_is_std_i (Wstd_sta6, Wstd_rel6, (Wloc_sta6, Wloc_rel6)) i0) as Hstd6.
         { apply HstdW6. eauto. }
         rewrite Hstd6 in Hr'. inversion Hr'. subst. intros x' y Hx' Hy.
         assert (∃ (a : Addr), countable.encode a = i0) as [a Ha].
         { revert Hdom Hsub Hx'. clear. intros [M HM] Hsub Hx'.
           apply elem_of_subseteq in Hsub.
           assert (i0 ∈ dom (gset positive) Wstd_sta).
           { apply elem_of_dom. eauto. }
           specialize (Hsub _ H). apply elem_of_dom in Hsub.
           rewrite /dom_equal in HM. apply HM in Hsub as [a [Ha _] ]. eauto. 
         } subst. 
         destruct (decide (a ∈ l)).
         ++ apply Hiff1 in e0 as Htemp1.
            rewrite Htemp1 in Hx'. inversion Hx'; subst.
            destruct (decide (a ∈ (region_addrs c e))),(decide (a ∈ (region_addrs c' e))). 
            +++ apply revoke_lookup_Temp in Htemp1.
                apply close_list_std_sta_revoked with (l:=countable.encode <$> region_addrs c e) in Htemp1;
                  [|apply elem_of_list_fmap;eauto]. 
                assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta3) as Hin3. 
                { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_dom. eauto. }
                apply elem_of_dom in Hin3 as [y3 Hy3].
                specialize (Hstd_related1 _ _ Htemp1 Hy3). 
                apply std_rel_pub_rtc_Temporary in Hstd_related1;auto. subst. 
                apply revoke_lookup_Temp in Hy3.
                apply close_list_std_sta_revoked with (l:=countable.encode <$> region_addrs c' e) in Hy3;
                  [|apply elem_of_list_fmap;eauto]. 
                assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta6) as Hin6. 
                { apply elem_of_subseteq in Hstd_sta_dom2. apply Hstd_sta_dom2. apply elem_of_dom. eauto. }
                apply elem_of_dom in Hin6 as [y6 Hy6].
                specialize (Hstd_related2 _ _ Hy3 Hy6).
                apply std_rel_pub_rtc_Temporary in Hstd_related2;auto. subst.
                apply revoke_lookup_Temp in Hy6.
                apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                  [|apply elem_of_list_fmap;eauto].
                rewrite Hy in Hy6. inversion Hy6. subst. left.
            +++ apply revoke_lookup_Temp in Htemp1.
                apply close_list_std_sta_revoked with (l:=countable.encode <$> region_addrs c e) in Htemp1;
                  [|apply elem_of_list_fmap;eauto]. 
                assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta3) as Hin3. 
                { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_dom. eauto. }
                apply elem_of_dom in Hin3 as [y3 Hy3].
                specialize (Hstd_related1 _ _ Htemp1 Hy3). 
                apply std_rel_pub_rtc_Temporary in Hstd_related1;auto. subst. 
                apply revoke_lookup_Temp in Hy3.
                rewrite (close_list_std_sta_same _ (countable.encode <$> region_addrs c' e)) in Hy3.
                assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta6) as Hin6. 
                { apply elem_of_subseteq in Hstd_sta_dom2. apply Hstd_sta_dom2. apply elem_of_dom. eauto. }
                apply elem_of_dom in Hin6 as [y6 Hy6].
                specialize (Hstd_related2 _ _ Hy3 Hy6). 
                apply std_rel_pub_rtc_Revoked in Hstd_related2 as [Htemporary | Hrevoked];auto. 
                ++++ subst. apply revoke_lookup_Temp in Hy6.
                     apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                       [|apply elem_of_list_fmap;eauto].
                     rewrite Hy in Hy6. inversion Hy6. subst. left.
                ++++ subst. apply revoke_lookup_Revoked in Hy6.
                     apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                       [|apply elem_of_list_fmap;eauto].
                     rewrite Hy in Hy6. inversion Hy6. subst. left.
                ++++ intros Hcontr. apply elem_of_list_fmap in Hcontr.
                     destruct Hcontr as [y' [Heq Hcontr] ]. 
                     apply encode_inj in Heq. subst. contradiction.
            +++ apply revoke_lookup_Temp in Htemp1.
                rewrite (close_list_std_sta_same _ (countable.encode <$> region_addrs c e)) in Htemp1.
                2: { intros Hcontr. apply elem_of_list_fmap in Hcontr.
                     destruct Hcontr as [y' [Heq Hcontr] ]. apply encode_inj in Heq. subst. contradiction. }
                assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta3) as Hin3. 
                { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_dom. eauto. }
                apply elem_of_dom in Hin3 as [y3 Hy3].
                specialize (Hstd_related1 _ _ Htemp1 Hy3). 
                apply std_rel_pub_rtc_Revoked in Hstd_related1 as [Htemp | Hrev];auto; subst. 
                ++++ apply revoke_lookup_Temp in Hy3.
                     apply (close_list_std_sta_revoked _ (countable.encode <$> region_addrs c' e)) in Hy3.
                     2: { apply elem_of_list_fmap. eauto. }
                     assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta6) as Hin6. 
                     { apply elem_of_subseteq in Hstd_sta_dom2. apply Hstd_sta_dom2. apply elem_of_dom. eauto. }
                     apply elem_of_dom in Hin6 as [y6 Hy6].
                     specialize (Hstd_related2 _ _ Hy3 Hy6). 
                     apply std_rel_pub_rtc_Temporary in Hstd_related2 as Heq;auto. subst.
                      apply revoke_lookup_Temp in Hy6.
                      apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                        [|apply elem_of_list_fmap;eauto].
                      rewrite Hy in Hy6. inversion Hy6. subst. left.
                ++++ apply revoke_lookup_Revoked in Hy3.
                     apply (close_list_std_sta_revoked _ (countable.encode <$> region_addrs c' e)) in Hy3.
                     2: { apply elem_of_list_fmap. eauto. }
                     assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta6) as Hin6. 
                     { apply elem_of_subseteq in Hstd_sta_dom2. apply Hstd_sta_dom2. apply elem_of_dom. eauto. }
                     apply elem_of_dom in Hin6 as [y6 Hy6].
                     specialize (Hstd_related2 _ _ Hy3 Hy6). 
                     apply std_rel_pub_rtc_Temporary in Hstd_related2 as Heq;auto. subst.
                      apply revoke_lookup_Temp in Hy6.
                      apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                        [|apply elem_of_list_fmap;eauto].
                      rewrite Hy in Hy6. inversion Hy6. subst. left.
            +++ apply revoke_lookup_Temp in Htemp1.
                rewrite (close_list_std_sta_same _ (countable.encode <$> region_addrs c e)) in Htemp1.
                2: { intros Hcontr. apply elem_of_list_fmap in Hcontr.
                     destruct Hcontr as [y' [Heq Hcontr] ]. apply encode_inj in Heq. subst. contradiction. }
                assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta3) as Hin3. 
                { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_dom. eauto. }
                apply elem_of_dom in Hin3 as [y3 Hy3].
                specialize (Hstd_related1 _ _ Htemp1 Hy3). 
                apply std_rel_pub_rtc_Revoked in Hstd_related1 as [Htemp | Hrev];auto; subst. 
                ++++ apply revoke_lookup_Temp in Hy3.
                     rewrite (close_list_std_sta_same _ (countable.encode <$> region_addrs c' e)) in Hy3.
                     2: { intros Hcontr. apply elem_of_list_fmap in Hcontr.
                          destruct Hcontr as [y' [Heq Hcontr] ]. apply encode_inj in Heq. subst. contradiction. }
                     assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta6) as Hin6. 
                     { apply elem_of_subseteq in Hstd_sta_dom2. apply Hstd_sta_dom2. apply elem_of_dom. eauto. }
                     apply elem_of_dom in Hin6 as [y6 Hy6].
                     specialize (Hstd_related2 _ _ Hy3 Hy6). 
                     apply std_rel_pub_rtc_Revoked in Hstd_related2 as [Htemp | Hrev];auto; subst. 
                     { apply revoke_lookup_Temp in Hy6.
                       apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                         [|apply elem_of_list_fmap;eauto].
                       rewrite Hy in Hy6. inversion Hy6. subst. left. }
                     { apply revoke_lookup_Revoked in Hy6.
                       apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                         [|apply elem_of_list_fmap;eauto].
                       rewrite Hy in Hy6. inversion Hy6. subst. left. }
                ++++ apply revoke_lookup_Revoked in Hy3.
                     rewrite (close_list_std_sta_same _ (countable.encode <$> region_addrs c' e)) in Hy3.
                     2: { intros Hcontr. apply elem_of_list_fmap in Hcontr.
                          destruct Hcontr as [y' [Heq Hcontr] ]. apply encode_inj in Heq. subst. contradiction. }
                     assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta6) as Hin6. 
                     { apply elem_of_subseteq in Hstd_sta_dom2. apply Hstd_sta_dom2. apply elem_of_dom. eauto. }
                     apply elem_of_dom in Hin6 as [y6 Hy6].
                     specialize (Hstd_related2 _ _ Hy3 Hy6). 
                     apply std_rel_pub_rtc_Revoked in Hstd_related2 as [Htemp | Hrev];auto; subst. 
                     { apply revoke_lookup_Temp in Hy6.
                       apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                         [|apply elem_of_list_fmap;eauto].
                       rewrite Hy in Hy6. inversion Hy6. subst. left. }
                     { apply revoke_lookup_Revoked in Hy6.
                       apply close_list_std_sta_revoked with (l:=countable.encode <$> l) in Hy6;
                         [|apply elem_of_list_fmap;eauto].
                       rewrite Hy in Hy6. inversion Hy6. subst. left. }
         ++ assert (a ∉ region_addrs c e) as Hnin.
            { intros Hcontr. destruct Happ as [l' Happ]; subst.
              apply not_elem_of_app in n as [Hl' Hbe]. 
              rewrite (region_addrs_split _ c _) in Hbe;[|solve_addr].
              apply not_elem_of_app in Hbe as [_ Hn]. contradiction. }
            assert (a ∉ region_addrs c' e) as Hnin'. 
            { intros Hcontr. destruct Happ as [l' Happ]; subst.
              apply not_elem_of_app in n as [Hl' Hbe]. 
              rewrite (region_addrs_split _ c' _) in Hbe;[|solve_addr].
              apply not_elem_of_app in Hbe as [_ Hn]. contradiction. }
            assert (Wstd_sta !! countable.encode a ≠ Some (countable.encode Temporary)) as Hne.
            { intros Hcontr. apply Hiff1 in Hcontr. contradiction. }
            assert (x' ≠ countable.encode Temporary) as Hne'.
            { intros Hcontr; subst. contradiction. }
            rewrite -revoke_monotone_lookup_same in Hx'; auto. 
            rewrite (close_list_std_sta_same _ (countable.encode <$> region_addrs c e)) in Hx'. 
            2: { intro Hcontr. apply elem_of_list_fmap in Hcontr as [a' [Ha' Hcontr] ]. 
                 apply encode_inj in Ha'. inversion Ha'. subst. contradiction. }
            assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta3) as Hin3. 
            { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_dom. eauto. }
            apply elem_of_dom in Hin3 as [y3 Hy3].
            specialize (Hstd_related1 _ _ Hx' Hy3).
            assert (countable.encode a ∉ countable.encode <$> l) as Hninl.
            { intro Hcontr. apply elem_of_list_fmap in Hcontr as [a' [Ha' Hcontr] ].
              destruct Happ as [l' Happ]; subst. apply not_elem_of_app in n as [Hl' Hbe]. 
              apply encode_inj in Ha'. inversion Ha'. subst.
              apply elem_of_app in Hcontr as [Hcontr | Hcontr]; contradiction. }
            apply std_rel_pub_rtc_not_temp_cases in Hstd_related1 as [ [Heq1 Heq2] | Heq]. 
            +++ subst. apply revoke_lookup_Temp in Hy3.
                rewrite (close_list_std_sta_same _ (countable.encode <$> region_addrs c' e)) in Hy3; auto. 
                 2: { intro Hcontr. apply elem_of_list_fmap in Hcontr as [a' [Ha' Hcontr] ]. 
                      apply encode_inj in Ha'. inversion Ha'. subst. contradiction. }
                 assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta6) as Hin6. 
                 { apply elem_of_subseteq in Hstd_sta_dom2. apply Hstd_sta_dom2. apply elem_of_dom. eauto. }
                 apply elem_of_dom in Hin6 as [y6 Hy6].
                 specialize (Hstd_related2 _ _ Hy3 Hy6).
                 apply std_rel_pub_rtc_Revoked in Hstd_related2 as [Htemp | Hrev];auto. 
                 ++++ subst. apply revoke_lookup_Temp in Hy6.
                      rewrite (close_list_std_sta_same _ (countable.encode <$> l)) in Hy6; auto. 
                      rewrite Hy6 in Hy. inversion Hy. left. 
                 ++++ subst. apply revoke_lookup_Revoked in Hy6.
                      rewrite (close_list_std_sta_same _ (countable.encode <$> l)) in Hy6;auto. 
                      rewrite Hy6 in Hy. inversion Hy. left.
            +++ subst. clear Hne. 
                assert (Wstd_sta3 !! countable.encode a ≠ Some (countable.encode Temporary)) as Hne.
                { intros Hcontr. rewrite Hy3 in Hcontr. inversion Hcontr. contradiction. }
                rewrite -revoke_monotone_lookup_same in Hy3; auto.
                rewrite (close_list_std_sta_same _ (countable.encode <$> region_addrs c' e)) in Hy3. 
                2: { intro Hcontr. apply elem_of_list_fmap in Hcontr as [a' [Ha' Hcontr] ]. 
                     apply encode_inj in Ha'. inversion Ha'. subst. contradiction. }
                assert ((countable.encode a) ∈ dom (gset positive) Wstd_sta6) as Hin6. 
                { apply elem_of_subseteq in Hstd_sta_dom2. apply Hstd_sta_dom2. apply elem_of_dom. eauto. }
                apply elem_of_dom in Hin6 as [y6 Hy6].
                specialize (Hstd_related2 _ _ Hy3 Hy6).
                apply std_rel_pub_rtc_not_temp_cases in Hstd_related2 as [ [Heq1 Heq2] | Heq]. 
                ++++ subst. apply revoke_lookup_Temp in Hy6.
                     rewrite (close_list_std_sta_same _ (countable.encode <$> l)) in Hy6;auto. 
                     rewrite Hy6 in Hy. inversion Hy. left. 
                ++++ subst. clear Hne. 
                     assert (Wstd_sta6 !! countable.encode a ≠ Some (countable.encode Temporary)) as Hne.
                     { intros Hcontr. rewrite Hy6 in Hcontr. inversion Hcontr. contradiction. }
                     rewrite -revoke_monotone_lookup_same in Hy6; auto.
                     rewrite (close_list_std_sta_same _ (countable.encode <$> l)) in Hy6; auto. 
                     rewrite Hy6 in Hy. inversion Hy. left. 
     - destruct Hrelated1 as [_ Hloc_related1]. 
       destruct Hrelated2 as [_ Hloc_related2]. simpl in *. 
       destruct Hloc_related2 as [Hloc_sta_dom2 [Hloc_rel_dom2 Hloc_related2] ].
       destruct Hloc_related1 as [Hloc_sta_dom1 [Hloc_rel_dom1 Hloc_related1] ].
       split;[|split]. 
       + apply insert_id in Hawki. rewrite -Hawki.
         assert (dom (gset positive) (<[i:=countable.encode x]> Wloc_sta) ⊆
                     dom (gset positive) (<[j:=countable.encode Live]> (<[i:=countable.encode false]> Wloc_sta))) as Hsub. 
         { trans (dom (gset positive) (<[i:=countable.encode false]> Wloc_sta));[repeat rewrite dom_insert;done|]. 
           repeat rewrite dom_insert. apply union_subseteq_r. }
         etrans;[apply Hsub|]. 
         etrans;[apply Hloc_sta_dom1|]. 
         assert (k ∈ dom (gset positive) Wloc_sta6) as Hin. 
         { apply elem_of_subseteq in Hloc_sta_dom2. apply Hloc_sta_dom2. apply elem_of_dom.
           rewrite lookup_insert; eauto. }
         rewrite dom_insert.
         trans (dom (gset positive) Wloc_sta6);[|apply union_subseteq_r].
         etrans;[|apply Hloc_sta_dom2].
         repeat rewrite dom_insert. repeat rewrite union_assoc. apply union_subseteq_r.
       + etrans;[|apply Hloc_rel_dom2].
         trans (dom (gset positive) (<[j:=(convert_rel local_rel_pub, convert_rel local_rel_priv)]> Wloc_rel));
           [rewrite dom_insert;apply union_subseteq_r|].
         etrans;[apply Hloc_rel_dom1|]. rewrite dom_insert. apply union_subseteq_r.
       + intros i0 r1 r2 r1' r2' Hr Hr'. 
         destruct (decide (i0 = j)). 
         { subst. assert (j ∈ dom (gset positive) Wloc_rel) as Hcontr.
           apply elem_of_dom. eauto. contradiction. }
         destruct (decide (i0 = k)). 
         { subst. assert (k ∈ dom (gset positive) Wloc_rel3) as Hcontr;[|contradiction].
           assert (k ∈ dom (gset positive) Wloc_rel) as Hk4;[apply elem_of_dom;eauto|]. 
           apply elem_of_subseteq in Hloc_rel_dom1. apply Hloc_rel_dom1.
           apply elem_of_dom. rewrite lookup_insert_ne; auto. eauto. 
         }
         destruct (decide (i0 = i)). 
         { subst. assert (i ∈ dom (gset positive) Wloc_rel3) as Hin3.
           { apply elem_of_subseteq in Hloc_rel_dom1. apply Hloc_rel_dom1. apply elem_of_dom.
             rewrite lookup_insert_ne;auto. eauto. }
           apply elem_of_dom in Hin3 as [ [r3 r3'] Hr3]. 
           specialize (Hloc_related1 i r1 r2 r3 r3'). 
           rewrite lookup_insert_ne in Hloc_related1; auto.
           destruct Hloc_related1 as [Heq1 [Heq2 Hloc_related1] ]; auto. subst.
           specialize (Hloc_related2 i r3 r3' r1' r2').
           rewrite lookup_insert_ne in Hloc_related2; auto.
           destruct Hloc_related2 as [Heq1 [Heq2 Hloc_related2] ]; auto. subst.
           rewrite Hawk in Hr. inversion Hr. subst.
           repeat (split;auto).
           intros x0 y Hx0 Hy.
           rewrite lookup_insert_ne in Hy; auto.
           specialize (Hloc_related2 (countable.encode true) y).
           assert (rtc (convert_rel awk_rel_pub) (countable.encode true) y) as Htrue.
           { apply Hloc_related2; auto. do 2 (rewrite lookup_insert_ne; auto). apply lookup_insert. }
           apply rtc_rel_pub in Htrue;auto. subst. rewrite Hawki in Hx0. inversion Hx0. subst.
           destruct x;[left|right with (countable.encode true);[|left] ].
           exists false, true. repeat (split;auto). by left. 
         }
         subst. assert (i0 ∈ dom (gset positive) Wloc_rel3) as Hin3.
         { apply elem_of_subseteq in Hloc_rel_dom1. apply Hloc_rel_dom1. apply elem_of_dom.
           rewrite lookup_insert_ne;auto. eauto. }
         apply elem_of_dom in Hin3 as [ [r3 r3'] Hr3]. 
         specialize (Hloc_related1 i0 r1 r2 r3 r3'). 
         rewrite lookup_insert_ne in Hloc_related1; auto.
         specialize (Hloc_related1 Hr Hr3) as [Heq1 [Heq2 Hloc_related1] ]. subst. 
         specialize (Hloc_related2 i0 r3 r3' r1' r2'). 
         rewrite lookup_insert_ne in Hloc_related2;auto.
         specialize (Hloc_related2 Hr3 Hr') as [Heq1 [Heq2 Hloc_related2] ]. subst. 
         repeat (split;auto).
         intros x0 y Hx0 Hy.
         assert (i0 ∈ dom (gset positive) Wloc_sta3) as Hin3'. 
         { apply elem_of_subseteq in Hloc_sta_dom1. apply Hloc_sta_dom1. apply elem_of_dom.
           repeat rewrite lookup_insert_ne;auto. eauto. }
         apply elem_of_dom in Hin3' as [x0' Hx0']. 
         specialize (Hloc_related1 x0 x0'). 
         assert (rtc r1' x0 x0') as Hrtc1.
         { apply Hloc_related1; auto. repeat (rewrite lookup_insert_ne;auto). }
         specialize (Hloc_related2 x0' y). 
         assert (rtc r1' x0' y) as Hrtc2.
         { apply Hloc_related2; auto. repeat (rewrite lookup_insert_ne;auto). rewrite lookup_insert_ne in Hy; auto. }
         etrans; eauto. 
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
  
  (* Shorthand definition for an adress being currently temporary/revoked *)
  Definition region_type_revoked W (a : Addr) :=
    (std_sta W) !! (countable.encode a) = Some (countable.encode Revoked).
  Definition region_type_temporary W (a : Addr) :=
    (std_sta W) !! (countable.encode a) = Some (countable.encode Temporary).
   
   (* the following spec is for the f4 subroutine of the awkward example, jumped to after dynamically allocating into r_env *)
  Lemma f4_spec W pc_p pc_g pc_b pc_e (* PC *)
        b e a (* adv *)
        g_ret b_ret e_ret a_ret (* return cap *)
        f4_addrs (* f2 *)
        d d' i (* dynamically allocated memory given by preamble, connected to invariant i *)
        a_first a_last (* special adresses *) 
        (b_r e_r b_r' : Addr) (* stack *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between f4_addrs a_first a_last ->
    
    (* Stack assumptions *)
    (0%a ≤ e_r)%Z ∧ (0%a ≤ b_r)%Z -> (* this assumption will not be necessary once addresses are finite *)
    region_size b_r e_r > 11 -> (* we must assume the stack is large enough for needed local state *)
    (b_r' + 1)%a = Some b_r ->

    (* malloc'ed memory assumption *)
    (d + 1)%a = Some d' ->
    
    (* Finally, we must assume that the stack is currently in a temporary state *)
    (* (forall (a : Addr), W.1.1 !! (countable.encode a) = Some (countable.encode Temporary) <-> a ∈ (region_addrs b_r e_r)) -> *)
    Forall (λ a, region_type_temporary W a ∧ rel_is_std_i W (countable.encode a)) (region_addrs b_r e_r) ->

    {{{ r_stk ↦ᵣ inr ((RWLX,Local),b_r,e_r,b_r')
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ inr ((E,g_ret),b_ret,e_ret,a_ret) (* for now we say it's an enter cap. We will need to generalize to all words *)
      ∗ r_adv ↦ᵣ inr ((E,Global),b,e,a)
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r_adv;r_t0;r_env]; wsr, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (awk_inv i d))
      ∗ sts_rel_loc i awk_rel_pub awk_rel_priv
      (* stack *)
      ∗ ([∗ list] a ∈ (region_addrs b_r e_r), rel a RWLX (λ Wv : prodO STS STS * Word, (interp Wv.1) Wv.2))
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv code *)
      ∗ ([∗ list] a ∈ (region_addrs b e), (read_write_cond a RX interp) ∧ ⌜region_state_nwl W a Global⌝ ∧ ⌜region_std W a⌝)
      (* callback validity *)
      ∗ interp W (inr ((E,g_ret),b_ret,e_ret,a_ret))
      (* trusted code *)
      ∗ awkward_example f4_addrs pc_p r_adv 65
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
    iIntros (Hvpc Hf2 Hbounds Hsize Hb_r' Hd Htemp φ)
            "(Hr_stk & HPC & Hr_t0 & Hr_adv & Hr_env & Hgen_reg & #Hι & #Hrel & #Hstack_val & Hna & #Hadv_val & #Hcallback & Hprog & Hsts & Hr) Hφ".
    (* We put the code in a non atomic invariant for each iteration of the program *)
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"prog") with "Hprog") as "#Hf4".
    (* Now we step through the program *)
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
    iAssert (⌜exists M, dom_equal (std_sta W) M⌝)%I as %Hdom.
    { rewrite region_eq /region_def. iDestruct "Hr" as (M) "(_ & % & _)". eauto. }
    apply extract_temps_split with (l:=region_addrs b_r e_r) in Hdom as [l' [Hdup Hiff] ];
      [|apply NoDup_ListNoDup,region_addrs_NoDup|apply Forall_and in Htemp as [Htemp _];apply Htemp]. 
    iMod (monotone_revoke_keep_some W _ (region_addrs b_r e_r) with "[$Hsts $Hr]") as "[Hsts [Hr [Hrest Hstack] ] ]";[apply Hdup|..].
    { iSplit.
      - iApply big_sepL_forall. iPureIntro. intros n. simpl. intros x Hsome. apply Hiff. apply elem_of_app; left.
        apply elem_of_list_lookup. eauto. 
      - iApply (big_sepL_mono with "Hstack_val"). iIntros (k y Hk) "Hrel". iFrame. iPureIntro.
        revert Htemp; rewrite Forall_forall =>Htemp. apply Htemp. apply elem_of_list_lookup. eauto. }
    iAssert ((▷ ∃ ws, [[b_r, e_r]]↦ₐ[RWLX][[ws]])
               ∗ ⌜Forall (λ a : Addr, region_type_revoked (revoke W) a ∧ rel_is_std_i (revoke W) (countable.encode a)) (region_addrs b_r e_r)⌝)%I
      with "[Hstack]" as "[>Hstack #Hrevoked]".
    { iDestruct (big_sepL_sep with "Hstack") as "[Hstack #Hrevoked]".
      iDestruct (big_sepL_forall with "Hrevoked") as %Hrevoked. iSplit;[|iPureIntro].
      - iDestruct (big_sepL_sep with "Hstack") as "[Hstack _]". iNext. 
        iDestruct (region_addrs_exists with "Hstack") as (ws) "Hstack".
        iDestruct (big_sepL2_sep with "Hstack") as "[_ Hstack]".
        iDestruct (big_sepL2_sep with "Hstack") as "[Hstack _]". iExists ws. iFrame.
      - revert Htemp; repeat (rewrite Forall_forall). rewrite /revoke /std_sta /rel_is_std_i /std_rel /=.
        intros Htemp x Hx. split; [|by apply Htemp]. apply revoke_lookup_Temp. by apply Htemp. 
    }
    iDestruct "Hrevoked" as %Hrevoked.
    (* For later use it will be useful to know that W contains i *)
    (* Now we may do any private transitions to our local invariants.
       since we don't know which case we are in, we can generalize and 
       say that there exists some private future world such that   
       the store succeeded, after which the state at i is false
     *)
    iPrologue l Hprog_length "Hprog".
    apply contiguous_between_cons_inv_first in Hf2 as Heq. subst a_first. 
    iDestruct (sts_full_world_std with "[] Hsts") as %Hstd';[iPureIntro;split;apply related_sts_priv_refl|].
    assert (withinBounds (RWX, Global, d, d', d) = true) as Hwb.
    { isWithinBounds;[lia|]. revert Hd; clear. solve_addr. }
    iAssert (▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a1)
              ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
              ∗ a0 ↦ₐ[pc_p] store_z r_env 0
              ∗ (∃ W',⌜(∃ b : bool, W.2.1 !! i = Some (countable.encode b))
                        ∧ W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝ ∧ 
                    ⌜W' = ((revoke_std_sta W.1.1,W.1.2),(<[i:=countable.encode false]> W.2.1,W.2.2))⌝ ∧
                    ⌜related_sts_priv_world (revoke W) W'⌝ ∧
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
          [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC a0 a_last|iContiguous_next Hf2 0|auto|auto|..].
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
        iPureIntro.
        split;[eauto|].
        split; [auto|]. split;[apply revoke_monotone in Hrelated; auto|split;[apply lookup_insert|] ].
        eapply Forall_impl;[apply Hrevoked|].
        intros a2 [Ha0_rev Ha0_std]. split; auto. 
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC a0 a_last|iContiguous_next Hf2 0|auto|auto|..].
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* use sts_state to assert that the current state of i is false *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.   
        (* No need to update the world, since we did not change state *)
        iMod ("Hcls" with "[Hstate Hd]") as "_". 
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        iExists _. iFrame. iPureIntro. rewrite /revoke /loc /= in Hlookup.
        apply insert_id in Hlookup as Heq. rewrite Heq. split;[eauto|]. split. 
        { destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ]. rewrite /revoke /loc /std_sta /std_rel /=. done. }
        split;[split;apply related_sts_priv_refl|split;auto].
    }
    iApply "Hstore_step". 
    iNext. iIntros "(HPC & Hr_env & Hprog_done & HW')".
    iDestruct "HW'" as (W' [Hawki Hawk] HeqW' Hrelated Hfalse) "(Hr & Hsts & #Hforall)".
    clear Hrevoked. iDestruct "Hforall" as %Hrevoked. 
    (* we prepare the stack for storing local state *)
    (* Splitting the stack into own and adv parts *)
    assert (contiguous (region_addrs b_r e_r)) as Hcont_stack;[apply region_addrs_contiguous|].
    assert (contiguous_between (region_addrs b_r e_r) b_r e_r) as Hcontiguous.
    { apply contiguous_between_of_region_addrs; auto. revert Hsize. rewrite /region_size. clear. solve_addr. }
    iDestruct "Hstack" as (ws) "Hstack". 
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 11)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { rewrite region_addrs_length in Hlength; auto. rewrite Hlength in Hsize. 
      do 11 (destruct ws as [|? ws]; [simpl in Hsize; lia|]).
           by exists [w;w0;w1;w2;w3;w4;w5;w6;w7;w8;w9],ws. }
    rewrite Happ.
    iDestruct (contiguous_between_program_split with "Hstack") as (stack_own stack_adv stack_own_last) "(Hstack_own & Hstack_adv & #Hcont)"; [eauto|].
    iDestruct "Hcont" as %(Hcont1 & Hcont2 & Hstack_eq & Hlink).
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_own. rewrite Hlength' in Hlength_own.
    rewrite Hstack_eq in Hcontiguous.
    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_f2.
    iDestruct (big_sepL2_length with "Hstack_adv") as %Hlength_adv.
    (* Getting the three top adress on the stack *)
    do 3 (destruct stack_own; [inversion Hlength_own|]; destruct ws_own;[inversion Hlength'|]).
    assert ((region_addrs b_r e_r) !! 0 = Some b_r) as Hfirst_stack.
    { apply region_addrs_first. revert Hsize; clear. rewrite /region_size. solve_addr. }
    rewrite Hstack_eq /= in Hfirst_stack. inversion Hfirst_stack as [Heq]. subst b_r.
    (* assert that the stack bounds are within bounds *)
    assert (withinBounds (RWLX,Local,a2,e_r,a2) = true ∧ withinBounds (RWLX,Local,a2,e_r,stack_own_last) = true) as [Hwb1 Hwb2].
    { split; isWithinBounds; first lia.
      - revert Hlength. rewrite Happ app_length Hlength' region_addrs_length /region_size. clear. solve_addr.
      - by eapply contiguous_between_bounds.
      - apply contiguous_between_bounds in Hcont2. simplify_eq.
        revert Hlength' Hlength Hlink Hsize Hlength_adv Hlength_own Hcont2. rewrite -region_addrs_length app_length. clear.
        rewrite region_addrs_length /region_size. solve_addr.
    }   
    (* push r_stk r_env *)
    iDestruct "Hstack_own" as "[Ha Hstack_own]".
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a1;a5] (a6::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Ha"];
      [|apply PermFlows_refl|auto|iContiguous_next Hf2 1|iContiguous_next Hf2 2|auto|..].
    { split;iCorrectPC a0 a_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_self *)
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a6;a7] (a8::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iDestruct "Hstack_own" as "[Ha2 Hstack_own]".
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_t0 Ha2"];
      [|apply PermFlows_refl| |iContiguous_next Hf2 3|
       iContiguous_next Hf2 4|iContiguous_next Hcont1 0|..].
    { split;iCorrectPC a0 a_last. }
    { iContiguous_bounds_withinBounds a2 stack_own_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha2)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_adv *)
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a8;a9] (a10::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|].
    iDestruct "Hstack_own" as "[Ha3 Hstack_own]".
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_adv Ha3"];
      [|apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|iContiguous_next Hf2 5|
       iContiguous_next Hf2 6|iContiguous_next Hcont1 1|..].
    { split;iCorrectPC a0 a_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_adv & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* prepare for scall *)
    (* Prepare the scall prologue macro *)
    destruct stack_own as [|stack_own_b stack_own];[inversion Hlength_own|].
    assert ((stack_own_b :: stack_own) = region_addrs stack_own_b stack_own_last) as ->.
    { apply region_addrs_of_contiguous_between; auto.
      repeat (inversion Hcont1 as [|????? Hcont1']; subst; auto; clear Hcont1; rename Hcont1' into Hcont1). }      
    assert (stack_adv = region_addrs stack_own_last e_r) as ->.
    { apply region_addrs_of_contiguous_between; auto. }
    assert (contiguous_between (a10 :: l) a10 a_last) as Hcont_weak.
    { repeat (inversion Hf2 as [|????? Hf2']; subst; auto; clear Hf2; rename Hf2' into Hf2). }
    iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue rest0 s_last)
                                                                   "(Hscall & Hf2 & #Hcont)"; [eauto|..].
    clear Hfirst_stack Hcont_weak.
    iDestruct "Hcont" as %(Hcont_scall & Hcont_rest0 & Hrest_app & Hlink').
    iDestruct (big_sepL2_length with "Hscall") as %Hscall_length. simpl in Hscall_length, Hlength_f2.
    assert ((stack_own_b + 8)%a = Some stack_own_last) as Hstack_own_bound.
    { rewrite -(addr_add_assoc a2 _ 3). assert ((3 + 8) = 11)%Z as ->;[done|].
      rewrite Hlength_own in Hlink. revert Hlink; clear; solve_addr.
      apply contiguous_between_incr_addr with (i:=3) (ai:=stack_own_b) in Hcont1; auto. }
    assert (∃ a, (stack_own_b + 7)%a = Some a) as [stack_own_end Hstack_own_bound'].
    { revert Hstack_own_bound. clear. intros H. destruct (stack_own_b + 7)%a eqn:Hnone; eauto. solve_addr. }
    assert (a10 < s_last)%a as Hcontlt.
    { revert Hscall_length Hlink'. clear. solve_addr. }
    assert (a0 <= a10)%a as Hcontge.
    { apply region_addrs_of_contiguous_between in Hcont_scall. simplify_eq. revert Hscall_length Hf2 Hcontlt. clear =>Hscall_length Hf2 Hcontlt.
      apply contiguous_between_middle_bounds with (i := 7) (ai := a10) in Hf2;[solve_addr|auto]. 
    }
    (* scall *)
    iApply (scall_prologue_spec with "[-]");
      last ((iFrame "HPC Hr_stk Hscall"); iSplitL "Hgen_reg Hr_env Hr_self";[|
                                          iSplitL "Hstack_own";[iNext;iExists ws_own;iFrame|
                                                                iSplitL "Hstack_adv";[iNext;iExists ws_adv;iFrame|] ] ]);
      [| |apply Hwb2|apply Hbounds|apply Hcont_scall|apply PermFlows_refl|iNotElemOfList|iContiguous_next Hcont1 2|apply Hstack_own_bound'|apply Hstack_own_bound| |done|..].
    { assert (s_last <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest0|].
      intros mid Hmid. apply isCorrectPC_inrange with a0 a_last; auto.
      revert Hle Hcontlt Hcontge Hmid. clear; intros. split; solve_addr. }
    { simplify_eq. iContiguous_bounds_withinBounds a2 stack_own_last. }
    { assert (12 + 65 = 77)%Z as ->;[done|]. rewrite Hscall_length in Hlink'. done. }
    { iNext. iDestruct "Hgen_reg" as (wsr) "Hgen_reg".
      iExists (_ :: wsr ++ [_]).
      rewrite /all_registers /=; iFrame "Hr_self". 
      iApply (big_sepL2_app _ _ [r_t30] wsr with "Hgen_reg [Hr_env]").
      by iFrame. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hstack_adv & Hscall)".
    iDestruct (big_sepL2_length with "Hf2") as %Hf2_length. simpl in Hf2_length.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last a_last) as Hvpc1.
    { intros mid Hmid. assert (a0 <= s_last)%a as Hle;[apply contiguous_between_bounds in Hcont_scall; revert Hcont_scall Hcontge;clear; solve_addr|].
      apply isCorrectPC_inrange with a0 a_last; auto.
      revert Hmid Hle. clear. solve_addr. }
    (* jmp r_adv *)
    iDestruct (big_sepL2_length with "Hf2") as %Hrest_length; simpl in Hrest_length. 
    destruct rest0;[inversion Hrest_length|]. 
    iPrologue rest0 Hrest_length "Hf2".
    apply contiguous_between_cons_inv_first in Hcont_rest0 as Heq. subst a11. 
    iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
      [apply jmp_i|apply PermFlows_refl|iCorrectPC s_last a_last|..].
    iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".
    (* We now want to reason about unknown code. For this we invoke the fundamental theorem *)
    (* Before we can show the validity of the continuation, we need to set up the invariants 
       for local state, as well as the invariant for the stack *)
    (* We start out by closing the invariant for the program *)
    iMod ("Hcls" with "[Hprog_done Hinstr Hprog $Hna Hscall]") as "Hna". 
    { iNext. iDestruct "Hprog_done" as "(Hpush3 & Hpush2 & Hpush1 & Ha_first)".
      iFrame "Ha_first". rewrite Hrest_app. 
      iApply (big_sepL2_app with "Hpush1 [-]"). 
      iApply (big_sepL2_app with "Hpush2 [-]").
      iApply (big_sepL2_app with "Hpush3 [-]").
      iApply (big_sepL2_app with "Hscall [-]").
      iFrame. 
    }
    (* Next we close the adversary stack region so that it is Temporary *)
    iDestruct (sts_full_world_std with "[] Hsts") as %Hstd'';[iPureIntro;split;apply related_sts_priv_refl|]. 
    iMod (monotone_close _ (region_addrs stack_own_last e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
            with "[$Hsts $Hr Hstack_adv]") as "[Hsts Hex]".
    { rewrite Hstack_eq. iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_val']".
      iApply big_sepL_sep. iSplitL.
      - iDestruct (region_addrs_zeroes_trans with "Hstack_adv") as "Hstack_adv".
        iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hy".
        iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
        + iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
        + by repeat (rewrite fixpoint_interp1_eq /=).
      - iApply big_sepL_sep; iFrame "#". iApply big_sepL_forall. iPureIntro.
        rewrite Hstack_eq in Hrevoked. apply Forall_app in Hrevoked as [_ Hrevoked]. 
        intros k x Hsome. apply (Forall_lookup_1 _ _ k _ Hrevoked Hsome).
    }
    (* The resulting closed world is a public future world of W' *)
    assert (related_sts_pub_world W' (close_list (countable.encode <$> region_addrs stack_own_last e_r) W')) as Hrelated'. 
    { apply close_list_related_sts_pub. auto. } clear Hstd''. 
    (* We put the local stack in a non atomic invariant. Since the local stack will change, 
       we allocate an STS that will release the resources *)
    iMod (sts_alloc_loc _ Live local_rel_pub local_rel_priv with "Hsts")
      as (j) "(Hsts & % & % & Hstate & #Hrelj)".
    iMod (na_inv_alloc logrel_nais ⊤ (regN.@"stack") (∃ x:local_state, sts_state_loc j x
                       ∗ match x with
                         | Live => a2 ↦ₐ[RWLX] inr (RWX, Global, d, d', d)
                                  ∗ a3 ↦ₐ[RWLX] inr (E, g_ret, b_ret, e_ret, a_ret)
                                  ∗ a4 ↦ₐ[RWLX] inr (E, Global, b, e, a)
                                  ∗ [[stack_own_b,stack_own_last]]↦ₐ[RWLX][[ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                                                                       inr (pc_p, pc_g, pc_b, pc_e, s_last);
                                                                       inr (RWLX, Local, a2, e_r, stack_own_end)] ]]
                                  ∗ ([∗ list] x ∈ l', (∃ (x0 : Perm) (x1 : prodO STS STS * Word → iProp Σ),
                                                          temp_resources W x1 x x0 ∗ rel x x0 x1)
                                                        ∗ ⌜std_sta (revoke W) !! countable.encode x = Some (countable.encode Revoked)⌝)
                         | Released => emp
                         end 
                       )%I
            with "[Hstack_own Hstate Hb_r Ha2 Ha3 Hrest]")
      as "#Hlocal".
    { iNext. iExists Live. iFrame. }
    (* The resulting world is a public future world of W' *)
    evar (W'' : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
    instantiate (W'' :=
       ((close_list (countable.encode <$> region_addrs stack_own_last e_r) W').1,
             (<[j:=countable.encode Live]> (close_list (countable.encode <$> region_addrs stack_own_last e_r) W').2.1,
             <[j:=(convert_rel local_rel_pub, convert_rel local_rel_priv)]> (close_list (countable.encode <$> region_addrs stack_own_last e_r) W').2.2))).
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
                     (<[r_stk := inr (RWLX, Local, stack_own_last, e_r, stack_own_end)]>
                     (<[r_t0  := inr (E, Local, a2, e_r, stack_own_b)]>
                     (<[r_adv := inr (E, Global, b, e, a)]>
                     (create_gmap_default
                        (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r))
      with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
    { iApply (registers_mapsto_resources with "Hr_gen Hr_stk Hr_t0 Hr_adv HPC"). } 
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
      with "[-Hsts Hr Hmaps Hvalid Hna Hφ]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
          [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_adv)); [by left|right;auto].  
      }
      - iIntros "%". contradiction.
      - assert (r !! r_stk = Some (inr (RWLX, Local, stack_own_last, e_r, stack_own_end))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk fixpoint_interp1_eq. 
        iIntros (_). iExists RWLX. iSplitR; [auto|].
        iAssert ([∗ list] a ∈ region_addrs stack_own_last e_r, read_write_cond a RWLX (fixpoint interp1)
                             ∧ ⌜region_state_pwl W'' a⌝ ∧ ⌜region_std W'' a⌝)%I as "#Hstack_adv_val". 
        { rewrite Hstack_eq. 
          iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_val']".
          iApply (big_sepL_mono with "Hstack_val'").
          iIntros (k y Hsome) "Hy".
          rewrite Hstack_eq in Hrevoked.
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
        assert (r !! r_t0 = Some (inr (E, Local, a2, e_r, stack_own_b))) as Hr_t0; auto. 
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
        iGet_genpur_reg_map r' r_t0 "Hmreg'" "Hfull'" "[Hr_t0 Hmreg']".
        iGet_genpur_reg_map r' r_env "Hmreg'" "Hfull'" "[Hr_env Hmreg']".
        (* we open the local stack *)
        iMod (na_inv_open logrel_nais ⊤ ⊤ with "Hlocal Hna") as "(Hframe & Hna & Hcls)";auto.
        (* we need to assert that the local state is Live *)
        iDestruct (bi.later_exist with "Hframe") as (x) "[>Hstate Hframe]". 
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hj.
        iDestruct (sts_full_rel_loc with "Hsts Hrelj") as %Hrel. 
        assert (x = Live) as ->.
        { apply (local_state_related_sts_pub W'' W3 j);auto; rewrite /W'' /= lookup_insert; auto. }
        iDestruct "Hframe" as "(>Hb_r & >Ha2 & >Ha3 & >Hframe & Hrest)". 
        (* prepare the new stack value *)
        assert (exists stack_new, (stack_new + 1)%a = Some stack_own_end) as [stack_new Hstack_new].
        { revert Hstack_own_bound'. clear. intros H. destruct (stack_own_b + 6)%a eqn:Hsome;[|solve_addr].
          exists a. solve_addr. }
        (* step through instructions in activation record *)
        iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
          [|done|iContiguous_next Hcont_rest0 0|apply Hstack_new|revert Hstack_own_bound Hstack_own_bound'; clear; solve_addr|..].
        { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb2.
          apply (contiguous_between_middle_bounds _ 3 stack_own_b) in Hcont1;[|auto]. revert Hwb2 Hcont1 Hmid. clear. solve_addr.
        }
        iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
        iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
        iDestruct "Hr_t1" as (wrt1) "Hr_t1". 
        (* we can now step through the rest of the program *)
        (* to do that wee need to open the non atomic invariant of the program *)
        iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|]. 
        rewrite Hrest_app /=. repeat rewrite app_comm_cons. 
        iDestruct (mapsto_decomposition _ _ _ (take 84 (awkward_instrs r_adv 65)) with "Hprog")
          as "[Hprog_done [Ha Hprog] ]". 
        { simpl. inversion Hscall_length as [Heq]. rewrite Heq. omega. }
        (* let's prove some practical lemmas before continuing *)
        (* assert (last (rest0_first :: a9 :: rest0) = Some a_last) as Hlast0. *)
        (* { rewrite Hrest_app in Hlast. repeat rewrite app_comm_cons in Hlast. *)
        (*   by rewrite -last_app_eq in Hlast; [|simpl;lia]. } *)
        iCombine "Ha" "Hprog_done" as "Hprog_done".
        (* sub r_t1 0 7 *)
        iPrologue rest0 Hrest_length "Hprog".
        iApply (wp_add_sub_lt_success_z_z with "[$HPC $Hr_t1 $Hinstr]");
          [apply sub_z_z_i|right;left;eauto|iContiguous_next Hcont_rest0 1|apply PermFlows_refl|iCorrectPC s_last a_last|..]. 
        iEpilogue "(HPC & Hinstr & Hr_t1)".
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* lea r_stk r_t1 *)
        iPrologue rest0 Hrest_length "Hprog". 
        assert ((stack_new + (0 - 7))%a = Some a4) as Hpop.
        { assert ((a4 + 1)%a = Some stack_own_b) as Ha0;[iContiguous_next Hcont1 2|].
          revert Ha0 Hstack_own_bound' Hstack_new. clear. solve_addr. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
          [apply lea_r_i|apply PermFlows_refl|iCorrectPC s_last a_last|iContiguous_next Hcont_rest0 2|apply Hpop|auto..].
        iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
        (* pop r_stk r_adv *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a13;a14;a15] (a16::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a4 + (0 - 1))%a = Some a3) as Hpop.
        { rewrite -(addr_add_assoc a3 _ 1);[apply addr_add_0|iContiguous_next Hcont1 1]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_adv Ha3"];
          [split;[|split];iCorrectPC s_last a_last| apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|
           iContiguous_next Hcont_rest0 3|iContiguous_next Hcont_rest0 4|iContiguous_next Hcont_rest0 5|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_adv & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_self *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a16;a17;a18] (a19::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a3 + (0 - 1))%a = Some a2) as Hpop.
        { rewrite -(addr_add_assoc a2 _ 1);[apply addr_add_0|iContiguous_next Hcont1 0]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_t0 Ha2"];
          [split;[|split];iCorrectPC s_last a_last| apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|
           iContiguous_next Hcont_rest0 6|iContiguous_next Hcont_rest0 7|iContiguous_next Hcont_rest0 8|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_t0 & Ha2 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_env *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a19;a20;a21] (a22::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a2 + (0 - 1))%a = Some b_r') as Hpop.
        { rewrite -(addr_add_assoc b_r' _ 1);[apply addr_add_0|auto]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Hb_r"];
          [split;[|split];iCorrectPC s_last a_last| apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|
           iContiguous_next Hcont_rest0 9|iContiguous_next Hcont_rest0 10|iContiguous_next Hcont_rest0 11|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_env & Hb_r & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* store r_env 1 *)
        iPrologue rest0 Hrest_length "Hprog".
        (* Storing 1 will always constitute a public future world of W3 *)
        iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a23)
                       ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                       ∗ a22 ↦ₐ[pc_p] store_z r_env 1
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
              [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC s_last a_last|
               iContiguous_next Hcont_rest0 12|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ". iFrame.
            rewrite (insert_id _ i);[|auto].
            destruct W3 as [W3_std [W3_loc_pub W3_lo_priv] ]. iFrame. eauto. 
          - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
              [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC s_last a_last|
               iContiguous_next Hcont_rest0 12|auto|].
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
        iDestruct (big_sepL2_app_inv _ [a23;a24] (a25::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Hb_r"];
          [split;iCorrectPC s_last a_last|apply PermFlows_refl|auto|iContiguous_next Hcont_rest0 13|iContiguous_next Hcont_rest0 14|auto|..].
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
        (* push r_stk r_self *)
        do 2 (destruct rest0;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a25;a26] (a27::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_t0 Ha2"];
          [split;iCorrectPC s_last a_last|apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|iContiguous_next Hcont_rest0 15|
           iContiguous_next Hcont_rest0 16|iContiguous_next Hcont1 0|..].
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha2)". iCombine "Hpush" "Hprog_done" as "Hprog_done". 
        (* SECOND SCALL *)
        (* before invoking the scall spec, we need to revoke the adversary stack region *)
        iMod (monotone_revoke_keep_alt _ (region_addrs stack_own_last e_r) with "[$Hsts $Hr]") as "(Hsts & Hr & Hstack_adv)";[apply NoDup_ListNoDup, region_addrs_NoDup|..]. 
        { rewrite Hstack_eq.
          iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_adv]".
          iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hr".
          rewrite /read_write_cond. iFrame. iPureIntro.
          assert (region_state_pwl W3 y) as Hlookup;[|auto].
          revert Hrevoked; rewrite Forall_forall =>Hrevoked.
          apply region_state_pwl_monotone with W''; eauto.
          - apply Hrevoked. rewrite Hstack_eq.
            apply elem_of_app;right.
            apply elem_of_list_lookup. eauto. 
          - rewrite /W'' /region_state_pwl /std_sta /=.
            apply close_list_std_sta_revoked; [apply elem_of_list_fmap_1, elem_of_list_lookup; eauto|]. 
            apply Hrevoked. rewrite Hstack_eq.
            apply elem_of_app;right.
            apply elem_of_list_lookup. eauto.
        }
        (* we now want to extract the final element of the local stack, which will now be handed off to the adversary *)
        do 2 (iDestruct (big_sepL_sep with "Hstack_adv") as "[Hstack_adv _]").
        (* we will need to split off the last element to adv *)
        assert (forall stack_own_b : Addr, (stack_own_b <= stack_own_end)%Z -> region_addrs stack_own_b stack_own_last = region_addrs stack_own_b stack_own_end ++ [stack_own_end]) as Hstack_localeq'.
        { intros stack_own_b' Hle. rewrite (region_addrs_decomposition _ stack_own_end).
          - repeat f_equiv. assert( (stack_own_end + 1)%a = Some stack_own_last) as ->;[|by rewrite /region_addrs /region_size Z.sub_diag /=].
            revert Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. 
          - revert Hle Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. 
        }
        
        rewrite /region_mapsto (Hstack_localeq' stack_own_b);[|revert Hstack_own_bound';clear;solve_addr]. 
        iDestruct (mapsto_decomposition _ _ _ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                                               inr (pc_p, pc_g, pc_b, pc_e, s_last)] with "Hframe") as "[Hframe Hlast']".
        { rewrite region_addrs_length /=. rewrite /region_size. revert Hstack_own_bound'; clear. solve_addr. }
        assert ([stack_own_end] ++ region_addrs stack_own_last e_r = region_addrs stack_own_end e_r) as Hstack_localeq.
        { rewrite /region_addrs. apply withinBounds_le_addr in Hwb2 as [_ Hwb2].
          assert ((stack_own_end + 1)%a = Some stack_own_last) as Hincr;[revert Hstack_own_bound Hstack_own_bound';clear;solve_addr|].
          assert (region_size stack_own_end e_r = S (region_size stack_own_last e_r)) as ->.
          { revert Hstack_own_bound Hstack_own_bound' Hwb2; clear. rewrite /region_size. solve_addr. }
          simpl. f_equiv. rewrite Hincr /=. done.
        }  
        iAssert (▷ (∃ ws_adv : list Word, [[stack_own_end,e_r]]↦ₐ[RWLX][[ws_adv]]))%I with "[Hstack_adv Hlast']" as ">Hstack_adv".
        { iNext.
          iDestruct (region_addrs_exists with "Hstack_adv") as (ws_adv') "Hstack_adv".
          iDestruct (big_sepL2_sep with "Hstack_adv") as "[_ Hstack_adv]". iDestruct (big_sepL2_sep with "Hstack_adv") as "[Hstack_adv _]".
          iDestruct (mapsto_decomposition _ _ _ [inr (RWLX, Local, a2, e_r, stack_own_end)] with "[$Hstack_adv $Hlast']") as "Hstack_adv";[auto|..].
          rewrite Hstack_localeq. 
          iExists (_ :: ws_adv'). iFrame. 
        }
        iAssert (▷ (∃ ws_own : list Word, [[a4,stack_own_end]]↦ₐ[RWLX][[ws_own]]))%I with "[Hframe Ha3]" as ">Hstack_own".
        { iNext. 
          iExists ((inr (E, Global, b, e, a)) :: _). rewrite /region_mapsto.
          assert ([a4] ++ region_addrs stack_own_b stack_own_end = region_addrs a4 stack_own_end) as <-.
          { rewrite /region_addrs.
            assert ((a4 + 1)%a = Some stack_own_b) as Hincr;[iContiguous_next Hcont1 2|].
            assert (region_size a4 stack_own_end = S (region_size stack_own_b stack_own_end)) as ->.
            { revert Hstack_own_bound' Hincr; clear. rewrite /region_size. solve_addr. }
            simpl. f_equiv. rewrite Hincr /=. done. 
          }
          iApply (mapsto_decomposition [a4] _ _ [inr (E, Global, b, e, a)]); [auto|]. iFrame. done.
        }
        (* prepare for scall *)
        (* split the program into the scall_prologue and the rest *)
        assert (contiguous_between (a27 :: rest0) a27 a_last) as Hcont_weak.
        { repeat (inversion Hcont_rest0 as [|????? Hf2']; subst; auto; clear Hcont_rest0; rename Hf2' into Hcont_rest0). }
        iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue1 rest1 s_last1)
                                                                       "(Hscall & Hprog & #Hcont)"; [eauto|..].
        clear Hcont_weak.
        iDestruct "Hcont" as %(Hcont_scall1 & Hcont_rest1 & Hrest_app1 & Hlink1). subst.
        iDestruct (big_sepL2_length with "Hscall") as %Hscall_length1. simpl in Hscall_length1.
        destruct scall_prologue1 as [|scall_prologue_first1 scall_prologue1];[inversion Hscall_length1|].
        assert (scall_prologue_first1 = a27) as <-;[inversion Hrest_app1;auto|].
        (* some important element of the stack *)
        assert ((a4 + 8)%a = Some stack_own_end) as Hstack_own_bound1.
        { assert ((a4 + 1)%a = Some stack_own_b) as Ha4;[iContiguous_next Hcont1 2|].
          revert Hstack_own_bound Hstack_own_bound' Ha4. clear. solve_addr. }
        assert ((a4 + 7)%a = Some stack_new) as Hstack_own_bound1'.
        { revert Hstack_own_bound1 Hstack_new. clear. solve_addr. }
        assert (scall_prologue_first1 < s_last1)%a as Hcontlt1.
        { revert Hscall_length1 Hlink1. clear. solve_addr. }
        assert (s_last <= scall_prologue_first1)%a as Hcontge1.
        { apply region_addrs_of_contiguous_between in Hcont_scall. subst. revert Hscall_length1 Hcont_rest0 Hcontlt1.  clear =>Hscall_length Hf2 Hcontlt.
          apply contiguous_between_middle_bounds with (i := 17) (ai := scall_prologue_first1) in Hf2;[solve_addr|auto]. 
        }
        assert (withinBounds (RWLX, Local, a2, e_r, stack_own_end) = true) as Hwb3.
        { isWithinBounds. 
          - assert ((a2 + 3)%a = Some stack_own_b) as Hincr;[apply contiguous_between_incr_addr with (i := 3) (ai := stack_own_b) in Hcont1; auto|].
            revert Hstack_own_bound' Hincr. clear. solve_addr. 
          - apply withinBounds_le_addr in Hwb2 as [_ Hwb2]. revert Hstack_own_bound Hstack_own_bound' Hwb2. clear. solve_addr. 
        } 
        (* we can now invoke the stack call prologue *)
        iApply (scall_prologue_spec with "[-]");
          last ((iFrame "HPC Hr_stk Hscall"); iSplitL "Hmreg' Hr_env Hr_self Hr_t1";[|
                 iSplitL "Hstack_own";[iNext;iFrame|
                 iSplitL "Hstack_adv";[iNext;iFrame|] ] ]);
          [| |apply Hwb3|apply Hbounds|apply Hcont_scall1|
           apply PermFlows_refl|iNotElemOfList|iContiguous_next Hcont1 1|apply Hstack_own_bound1'|apply Hstack_own_bound1| |done|..].
        { assert (s_last1 <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest1|].
          intros mid Hmid. apply isCorrectPC_inrange with a0 a_last; auto.
          revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid. clear; intros. split; solve_addr. }
        { subst. iContiguous_bounds_withinBounds a2 stack_own_last. }
        { assert (12 + 65 = 77)%Z as ->;[done|]. rewrite Hscall_length1 in Hlink1. done. }
        { iNext. iApply region_addrs_exists.
          iClose_genpur_reg_map r_env "[Hr_env $Hmreg']" "Hmreg'".
          iClose_genpur_reg_map r_t0 "[Hr_self $Hmreg']" "Hmreg'".
          repeat (rewrite -(delete_commute _ r_t1)). 
          iClose_genpur_reg_map r_t1 "[Hr_t1 $Hmreg']" "Hmreg'".
          iDestruct ("Hfull'") as %Hfull. 
          iDestruct (big_sepM_to_big_sepL _ (list_difference all_registers [PC; r_stk; r_adv]) with "Hmreg'") as "$Hmlist". 
          - apply NoDup_ListNoDup,NoDup_list_difference. apply all_registers_NoDup.
          - intros r0 Hin. apply elem_of_list_difference in Hin as [Hin Hnin].
            revert Hnin. repeat rewrite not_elem_of_cons. intros (Hne1 & Hne2 & Hne3 & _).
            destruct (decide (r0 = r_t1));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            destruct (decide (r0 = r_t0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            destruct (decide (r0 = r_env));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            rewrite delete_insert_delete. repeat (rewrite lookup_delete_ne;auto). apply Hfull. }
        iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hstack_adv & Hscall)".
        iDestruct (big_sepL2_length with "Hprog") as %Hrest_length1. simpl in Hrest_length1.
        assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last1 a_last) as Hvpc2.
        { intros mid Hmid. assert (a0 <= s_last1)%a as Hle.
          { apply contiguous_between_bounds in Hcont_scall1.
            apply contiguous_between_bounds in Hcont_scall.
            revert Hcont_scall Hcont_scall1 Hcontge1 Hcontge;clear. solve_addr.
          } 
          apply isCorrectPC_inrange with a0 a_last; auto.
          revert Hmid Hle. clear. solve_addr. }
        (* jmp r_adv *)
        destruct rest1;[inversion Hrest_length1|]. 
        iPrologue rest1 Hrest_length1 "Hprog". apply contiguous_between_cons_inv_first in Hcont_rest1 as Heq. subst s_last1. 
        iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
          [apply jmp_i|apply PermFlows_refl|iCorrectPC a27 a_last|..].
        iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".
        (* again we are jumping to unknown code. We will now need to close all our invariants so we can reestablish the FTLR 
           on the new state *)
        (* we close the invariant for our program *)
        iMod ("Hcls'" with "[Hprog_done Hprog Hinstr Hscall $Hna]") as "Hna".
        { iNext. iDestruct "Hprog_done" as "(Hpush2 & push1 & Ha19 & Hpop1 & Hpop2 & Hpop3 &
                                             Ha8 & Ha9 & Hrest0_first & Hprog_done)".
          iApply (big_sepL2_app with "Hprog_done [-]").
          iFrame "Hrest0_first Ha9 Ha8". 
          iApply (big_sepL2_app with "Hpop3 [-]").
          iApply (big_sepL2_app with "Hpop2 [-]").
          iApply (big_sepL2_app with "Hpop1 [-]").
          iFrame "Ha19".
          iApply (big_sepL2_app with "push1 [-]").
          iApply (big_sepL2_app with "Hpush2 [-]").
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
        (* to make the proofs easier, we assert that stack_end is indeed the last element of the stack *)
        assert (list.last (a2 :: a3 :: a4 :: stack_own_b :: stack_own) = Some stack_own_end) as Hlast.
        { apply contiguous_between_link_last with a2 stack_own_last; [auto|apply gt_Sn_O|].
          revert Hstack_own_bound Hstack_own_bound'; clear. solve_addr. }
        (* we start by asserting that the state of stack_own_end was indeed revoked in the world prior to the call *)
        assert (std_sta W'' !! countable.encode (stack_own_end) = Some (countable.encode Revoked) ∧ rel_is_std_i W'' (countable.encode stack_own_end)) as [Ha Hstd_a].
        { rewrite Hstack_eq in Hrevoked. apply Forall_app in Hrevoked as [Hrevoked_last Hrevoked].
          apply (Forall_lookup_1 _ _ (length (a2 :: a3 :: a4 :: stack_own_b :: stack_own) - 1) stack_own_end)
            in Hrevoked_last as [Hrel_last Hlookup_last]; [auto|by rewrite -last_lookup].
          rewrite /W'' /std_sta /rel_is_std_i /std_rel /=. split; auto.
          rewrite -close_list_std_sta_same; auto.
          assert (stack_own_end ∉ region_addrs_aux stack_own_last (region_size stack_own_last e_r)) as Hnin.
          { rewrite /region_addrs. apply region_addrs_not_elem_of. revert Hstack_own_bound Hstack_own_bound'. clear. solve_addr. }
          intros Hcontr. apply elem_of_list_fmap in Hcontr as [y  [Hy Hcont] ]. 
          apply encode_inj in Hy; subst. contradiction.
        }
        (* as a result we know that it is now either temporary or revoked (in the public future world W3) *)
        apply (region_state_Revoked_monotone _ _ _ Hstd_a Hrelated3) in Ha.
        (* finally we can now close the region: a_last' will be in state revoked in revoke(W3) *)
        assert (∀ k x, ([stack_own_end] ++ region_addrs stack_own_last e_r) !! k = Some x ->
                       revoke_std_sta W3.1.1 !! countable.encode x = Some (countable.encode Revoked)) as Hlookup_revoked.
        { intros k x Hsome.
          rewrite Hstack_eq in Hrevoked. apply Forall_app in Hrevoked as [Hrevoked_last Hrevoked].
          destruct k. 
          + apply (Forall_lookup_1 _ _ (length (a2 :: a3 :: a4 :: stack_own_b :: stack_own) - 1) stack_own_end)
              in Hrevoked_last as [Hrel_last Hlookup_last]; [auto|by rewrite -last_lookup].
            inversion Hsome; subst.
            destruct Ha as [Hrevoked_a | Htemporary_a]; [by apply revoke_lookup_Revoked|by apply revoke_lookup_Temp].
          + apply revoke_lookup_Temp. inversion Hsome. 
            apply (Forall_lookup_1 _ _ k x) in Hrevoked as [Hstd_x Hrevoked_x]; auto. 
            apply region_state_pwl_monotone with W''; auto.
            rewrite /W'' /region_state_pwl /std_sta /=.
            apply close_list_std_sta_revoked; auto. 
            apply elem_of_list_fmap. exists x. split; auto. apply elem_of_list_lookup_2 with k. auto.
        }
        iMod (monotone_close _ (region_addrs stack_own_end e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
                with "[$Hsts $Hr Hstack_adv ]") as "[Hsts Hex]".
        { iClear "Hreg' Hfull' full Hlocal Hrelj Hf4 Hrel Hinv Hadv_val".
          rewrite Hstack_eq. 
          iDestruct (region_addrs_zeroes_trans with "Hstack_adv") as "Hstack_adv".
          rewrite /region_mapsto -Hstack_localeq.
          iDestruct (big_sepL_app with "Hstack_adv") as "[ [Hs_last' _] Hstack_adv]". 
          iDestruct (big_sepL_app with "Hstack_val") as "[Hstack_last Hstack_val']".
          iDestruct (big_sepL_lookup _ _ (length (a2 :: a3 :: a4 :: stack_own_b :: stack_own) - 1) stack_own_end with "Hstack_last") as "Hs_last_val";[by rewrite -last_lookup|].
          iApply big_sepL_sep. iSplitL.
          - iApply big_sepL_app. iSplitL "Hs_last'". 
            + iSimpl. iSplit;[|auto]. iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
              * iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
              * by repeat (rewrite fixpoint_interp1_eq /=).
            + iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hy".
              iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
              * iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
              * by repeat (rewrite fixpoint_interp1_eq /=).
          - iApply big_sepL_sep; iFrame "#". iSplit;[auto|]. iApply big_sepL_forall. iPureIntro.
            auto. 
        }
        (* finally we allocate a new local region for the local stack *)
        iMod (sts_alloc_loc _ Live local_rel_pub local_rel_priv with "Hsts")
          as (k) "(Hsts & % & % & Hstate & #Hrelk)".
        iMod (na_inv_alloc logrel_nais ⊤ (regN.@"stack_1") (∃ x:local_state, sts_state_loc k x
                                 ∗ match x with
                                   | Live => a2 ↦ₐ[RWLX] inr (RWX, Global, d, d', d)
                                           ∗ a3 ↦ₐ[RWLX] inr (E, g_ret, b_ret, e_ret, a_ret)
                                           ∗ [[a4,stack_own_end]]↦ₐ[RWLX][[ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                                                                             inr (pc_p, pc_g, pc_b, pc_e, a27);
                                                                             inr (RWLX, Local, a2, e_r, stack_new)] ]]
                                           ∗ ([∗ list] x ∈ l', (∃ (x0 : Perm) (x1 : prodO STS STS * Word → iProp Σ),
                                                                   temp_resources W x1 x x0 ∗ rel x x0 x1)
                                                                 ∗ ⌜std_sta (revoke W) !! countable.encode x = Some (countable.encode Revoked)⌝)
                                   | Released => emp
                                   end)%I
                with "[Hstack_own Hstate Hb_r Ha2 Hrest]")
          as "#Hlocal_1".
        { iNext. iExists Live. iFrame. }
        (* for future use, we will need to know that i is not equal to j *)
        assert (i ≠ k) as Hneik.
        { assert (i ∈ dom (gset positive) (close_list (countable.encode <$> region_addrs stack_own_last e_r) (revoke W4)).2.1) as Hcontr.
          - apply elem_of_dom. rewrite lookup_insert_ne;[rewrite lookup_insert|auto]. eauto.
          - intros Heq; subst. contradiction.
        }
        (* The resulting world is a private future world of W3 *)
        iSimpl in "Hsts". 
        evar (W5 : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
        instantiate (W5 :=
                       (close_list_std_sta (countable.encode <$> region_addrs stack_own_end e_r) (std_sta (revoke W4)), std_rel (revoke W4),
                        (<[k:=countable.encode Live]> (<[j:=countable.encode Released]> (<[i:=countable.encode true]> W3.2.1)),
                         <[k:=(convert_rel local_rel_pub, convert_rel local_rel_priv)]> W3.2.2))).
        assert (related_sts_pub_world (close_list (countable.encode <$> region_addrs stack_own_end e_r) (revoke W4)) W5) as Hrelated5'.
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
                          (<[r_stk := inr (RWLX, Local, stack_own_end, e_r, stack_new)]>
                           (<[r_t0  := inr (E, Local, a2, e_r, a4)]>
                            (<[r_adv := inr (E, Global, b, e, a)]>
                             (create_gmap_default
                                (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
        (* We have all the resources of r *)
        iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r2))
          with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
        { iApply (registers_mapsto_resources with "Hr_gen Hr_stk Hr_t0 Hr_adv HPC"). } 
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
        iAssert ([∗ list] a ∈ region_addrs stack_own_end e_r, read_write_cond a RWLX (fixpoint interp1)
                                                             ∗ ⌜region_state_pwl W5 a⌝ ∧ ⌜region_std W5 a⌝)%I as "#Hstack_adv_val". 
        { rewrite Hstack_eq.
          iDestruct (big_sepL_app with "Hstack_val") as "[Hstack_last Hstack_val']".
          iDestruct (big_sepL_lookup _ _ (length (a2 :: a3 :: a4 :: stack_own_b :: stack_own) - 1) stack_own_end with "Hstack_last")
            as "Hs_last_val";[by rewrite -last_lookup|].
          iApply big_sepL_sep. iSplit.
          - rewrite /region_mapsto -Hstack_localeq. 
            iApply big_sepL_app. iFrame "Hs_last_val".
            iSplit;[auto|]. 
            iApply (big_sepL_mono with "Hstack_val'").
            iIntros (g y Hsome) "Hy". iFrame.
          - iApply big_sepL_forall. iPureIntro.
            intros g y Hsome. split. 
            + apply close_list_std_sta_revoked; auto.
              apply elem_of_list_fmap. exists y. split; auto. apply elem_of_list_lookup_2 with g. auto.
              rewrite /W4 /revoke /std_sta /=. apply Hlookup_revoked with g. 
              rewrite -Hstack_localeq in Hsome. auto. 
            + eapply related_sts_rel_std.
              { apply related_sts_priv_trans_world with W3;auto.
                apply related_sts_priv_pub_trans_world with W'';auto. eauto. }
              rewrite Hstack_eq in Hrevoked.
              apply Forall_app in Hrevoked as [Hrevoked_last Hrevoked].
              revert Hrevoked. rewrite Forall_forall =>Hrevoked.
              apply (Forall_lookup_1 _ _ (length (a2 :: a3 :: a4 :: stack_own_b :: stack_own) - 1) stack_own_end)
                in Hrevoked_last as [Hrel_last Hlookup_last]; [|by rewrite -last_lookup].
              rewrite -Hstack_localeq in Hsome.
              destruct g.
              * simpl in Hsome; inversion Hsome as [Heq]. rewrite -Heq. eauto.
              * simpl in Hsome. apply Hrevoked. apply elem_of_list_lookup; eauto.  
        }   
        (* We are now ready to show that all registers point to a valid word *)
        iDestruct (sts_full_world_std with "[] Hsts") as %Hstd5;[iPureIntro;split;apply related_sts_priv_refl|].     
        iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W5 (r2 !r! r1))%I
          with "[-Hsts Hr Hmaps Hvalid Hna]" as "Hreg".
        { iIntros (r1).
          assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
              [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
          { destruct (decide (r1 = PC)); [by left|right].
            destruct (decide (r1 = r_stk)); [by left|right].
            destruct (decide (r1 = r_t0)); [by left|right].
            destruct (decide (r1 = r_adv)); [by left|right;auto].  
          }
          - iIntros "%". contradiction.
          - assert (r2 !! r_stk = Some (inr (RWLX, Local, stack_own_end, e_r, stack_new))) as Hr_stk; auto. 
            rewrite /RegLocate Hr_stk. repeat rewrite fixpoint_interp1_eq. 
            iIntros (_). iExists RWLX. iSplitR; [auto|].
            iAssert ([∗ list] a ∈ region_addrs stack_own_end e_r, read_write_cond a RWLX (fixpoint interp1)
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
            assert (r2 !! r_t0 = Some (inr (E, Local, a2, e_r, a4))) as Hr_t0; auto. 
            rewrite /RegLocate Hr_t0. repeat rewrite fixpoint_interp1_eq. iSimpl. 
            (* prove continuation *)
            iAlways.
            iIntros (r3 W6 Hrelated6).
            iNext. iSimpl. 
            iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)". 
            iSplit; [auto|rewrite /interp_conf].
            (* get the PC, currently pointing to the activation record *)
            iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
            iAssert (⌜∃ M, dom_equal W6.1.1 M⌝)%I as %Hdom_equal.
            { rewrite region_eq /region_def. iDestruct "Hr" as (M) "(_ & #Hdom & _)".
              iDestruct "Hdom" as %Hdom. iPureIntro. exists M. apply Hdom. }
            (* get some registers *)
            iGet_genpur_reg_map r3 r_t1 "Hmreg'" "Hfull3" "[Hr_t1 Hmreg']".
            iGet_genpur_reg_map r3 r_stk "Hmreg'" "Hfull3" "[Hr_stk Hmreg']".
            iGet_genpur_reg_map r3 r_adv "Hmreg'" "Hfull3" "[Hr_adv Hmreg']".
            iGet_genpur_reg_map r3 r_env "Hmreg'" "Hfull3" "[Hr_env Hmreg']".
            iGet_genpur_reg_map r3 r_t0 "Hmreg'" "Hfull3" "[Hr_t0 Hmreg']".
            (* we open the local stack *)
            iMod (na_inv_open logrel_nais ⊤ ⊤ with "Hlocal_1 Hna") as "(Hframe & Hna & Hcls)";auto.
            (* we need to assert that the local state is Live *)
            iDestruct (bi.later_exist with "Hframe") as (x) "[>Hstate Hframe]". 
            iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hj'.
            iDestruct (sts_full_rel_loc with "Hsts Hrelk") as %Hrel'. 
            assert (x = Live) as ->.
            { apply (local_state_related_sts_pub W5 W6 k); auto; rewrite /W5 /= lookup_insert; auto. }
            iDestruct "Hframe" as "(>Hb_r & >Ha2 & >Hframe & Hrest)". 
            (* prepare the new stack value *)
            assert (∃ stack_new_1, (stack_new_1 + 1)%a = Some stack_new) as [stack_new_1 Hstack_new_1].
            { revert Hstack_own_bound' Hstack_new. clear. intros H. destruct (stack_own_b + 5)%a eqn:Hsome;[|solve_addr].
              exists a. solve_addr. }
            (* step through instructions in activation record *)
            iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
              [|done|iContiguous_next Hcont_rest1 0|apply Hstack_new_1|revert Hstack_own_bound1 Hstack_own_bound1'; clear; solve_addr|..].
            { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb3.
              apply (contiguous_between_middle_bounds _ 2 a4) in Hcont1;[|auto].
              revert Hwb3 Hcont1 Hmid. clear. solve_addr. 
            }
            iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
            iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
            iDestruct "Hr_t1" as (wrt1') "Hr_t1".
            (* we don't want to close the stack invariant yet, as we will now need to pop it *)
            (* go through rest of the program. We will now need to open the invariant and destruct it into its done and prog part *)
            (* sub r_t1 0 7 *)
            iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|]. 
            rewrite Hrest_app1 /=. repeat rewrite app_comm_cons. rewrite app_assoc.
            rewrite /awkward_example /awkward_instrs.
            iDestruct (mapsto_decomposition _ _ _ ([store_z r_env 0] ++
                                                   push_r_instrs r_stk r_env ++
                                                   push_r_instrs r_stk r_t0 ++
                                                   push_r_instrs r_stk r_adv ++
                                                   scall_prologue_instrs 65 r_adv ++
                                                   [jmp r_adv;
                                                    sub_z_z r_t1 0 7;
                                                    lea_r r_stk r_t1] ++
                                                   pop_instrs r_stk r_adv ++
                                                   pop_instrs r_stk r_t0 ++
                                                   pop_instrs r_stk r_env ++
                                                   [store_z r_env 1] ++
                                                   push_r_instrs r_stk r_env ++
                                                   push_r_instrs r_stk r_t0 ++
                                                   scall_prologue_instrs 65 r_adv) with "Hprog")
              as "[Hprog_done [Ha Hprog] ]". 
            { simpl. inversion Hscall_length as [Heq]. inversion Hscall_length1 as [Heq']. rewrite app_length Heq /=. rewrite Heq'. done. }
            (* let's prove some practical lemmas before continuing *)
            (* assert (last (rest1_first :: a27 :: rest1) = Some a_last) as Hlast1. *)
            (* { rewrite Hrest_app in Hlast. repeat rewrite app_comm_cons in Hlast. *)
            (*   rewrite -last_app_eq in Hlast;[|simpl;apply gt_Sn_O]. *)
            (*   rewrite Hrest_app1 in Hlast. repeat rewrite app_comm_cons in Hlast. *)
            (*   by rewrite -last_app_eq in Hlast;[|simpl;apply gt_Sn_O]. } *)
            iCombine "Ha" "Hprog_done" as "Hprog_done".
            (* sub r_t1 0 7 *)
            iPrologue rest1 Hrest_length1 "Hprog".
            iApply (wp_add_sub_lt_success_z_z with "[$HPC Hr_t1 $Hinstr]");
              [apply sub_z_z_i|right;left;eauto|iContiguous_next Hcont_rest1 1|apply PermFlows_refl|iCorrectPC a27 a_last|
               iSimpl;iFrame;eauto|].
            iEpilogue "(HPC & Hinstr & Hr_t1)".
            iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* lea r_stk r_t1 *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            assert ((stack_new_1 + (0 - 7))%a = Some a3) as Hpop1.
            { assert ((a4 + 1)%a = Some stack_own_b) as Hincr;[iContiguous_next Hcont1 2|].
              assert ((a3 + 1)%a = Some a4) as Hincr';[iContiguous_next Hcont1 1|].
              revert Hstack_own_bound1' Hincr Hincr' Hstack_new_1. clear. solve_addr. }
            iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
              [apply lea_r_i|apply PermFlows_refl|iCorrectPC a27 a_last|
               iContiguous_next Hcont_rest1 2|apply Hpop1|auto..].
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* pop r_stk r_t0 *)
            do 3 (destruct rest1; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a30;a31;a32] (a33::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a3 + (0 - 1))%a = Some a2) as Hpop1.
            { rewrite -(addr_add_assoc a2 _ 1);[apply addr_add_0|iContiguous_next Hcont1 0]. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_t0 Ha2"];
              [split;[|split];iCorrectPC a27 a_last|apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|iContiguous_next Hcont_rest1 3|iContiguous_next Hcont_rest1 4|iContiguous_next Hcont_rest1 5|apply Hpop1|].
            iNext. iIntros "(HPC & Hpop & Hr_t0 & Ha2 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* pop r_stk r_env *)
            do 3 (destruct rest1; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a33;a34;a35] (a36::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a2 + (0 - 1))%a = Some b_r') as Hpop1.
            { revert Hb_r'. clear. solve_addr. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Hb_r"];
              [split;[|split];iCorrectPC a27 a_last|apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|iContiguous_next Hcont_rest1 6|iContiguous_next Hcont_rest1 7|iContiguous_next Hcont_rest1 8|apply Hpop1|].
            iNext. iIntros "(HPC & Hpop & Hr_env & Hb_r & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* we have now arrived at the final load of the environment. we must here assert that the loaded
               value is indeed 1. We are able to show this since W6 is a public future world of W5, in which 
               invariant i is in state true *)
            (* load r_adv r_env *)
            iPrologue rest1 Hrest_length1 "Hprog".
            iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a37)
                                ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                                ∗ a36 ↦ₐ[pc_p] load_r r_adv r_env
                                ∗ sts_full_world sts_std W6
                                ∗ r_adv ↦ᵣ inl 1%Z
                                -∗ WP Seq (Instr Executable) {{ v, φ v }})
                            -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
              with "[HPC Hinstr Hr_env Hr_adv Hsts]" as "Hload_step".
            { iIntros (φ') "Hφ'".
              iInv ι as (x) "[>Hstate Hb]" "Hcls".
              iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hi.
              assert (x = true) as ->.
              { apply related_pub_lookup_local with W5 W6 i;auto.
                do 2 (rewrite lookup_insert_ne; auto). apply lookup_insert. }
              iDestruct "Hb" as ">Hb".
              iAssert (⌜(d =? a36)%a = false⌝)%I as %Hne.
              { destruct (d =? a36)%a eqn:Heq;auto. apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
                iDestruct (cap_duplicate_false with "[$Hinstr $Hb]") as "Hfalse";[|done].
                eapply isCorrectPC_contiguous_range with (a := a0) in Hvpc;[|eauto|];last (by apply elem_of_cons;left). 
                destruct pc_p;auto.
                inversion Hvpc as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
              iApply (wp_load_success with "[$HPC $Hinstr $Hr_adv $Hr_env Hb]");
                [apply load_r_i|apply PermFlows_refl|iCorrectPC a27 a_last
                 |auto|iContiguous_next Hcont_rest1 9|rewrite Hne;iFrame;iPureIntro;apply PermFlows_refl|rewrite Hne].
              iNext. iIntros "(HPC & Hr_adv & Ha36 & Hr_env & Hd)".
              iMod ("Hcls" with "[Hstate Hd]") as "_".
              { iNext. iExists true. iFrame. }
              iModIntro. iApply wp_pure_step_later;auto;iNext.
              iApply "Hφ'". iFrame. 
            }
            iApply "Hload_step".
            iNext. iIntros "(HPC & Hr_env & Ha36 & Hsts & Hr_t2)".
            (* We can now assert that r_adv indeed points to 1 *)
            (* move r_t1 PC *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            iApply (wp_move_success_reg_fromPC with "[$HPC $Hr_t1 $Hinstr]");
              [apply move_r_i|apply PermFlows_refl|iCorrectPC a27 a_last|
               iContiguous_next Hcont_rest1 10|auto|..].
            iEpilogue "(HPC & Hinstr & Hr_t1)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* lea r_t1 5 *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            do 2 (destruct rest1;[inversion Hrest_length1|]).
            assert ((a37 + 59)%a = Some a_last) as Hincr.
            { revert Hcont_rest1 Hrest_length1. clear. intros Hcont_rest1 Hrest_length1.
              assert ((a27 + 10)%a = Some a37);[eapply contiguous_between_incr_addr with (i:=10) (ai:=a37) in Hcont_rest1;auto|].
              apply contiguous_between_length in Hcont_rest1. solve_addr. }
            iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t1]");
              [apply lea_z_i|apply PermFlows_refl|iCorrectPC a27 a_last|
               iContiguous_next Hcont_rest1 11|apply Hincr|auto|..].
            { apply isCorrectPC_range_npE in Hvpc; auto. revert Hf2;clear; intros H. apply contiguous_between_length in H. solve_addr. }
            iEpilogue "(HPC & Hinstr & Hr_t1)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* sub r_t2 r_t2 1 *)
            iDestruct "Hprog" as "[Hinstr Hprog]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hinstr $Hr_t2]");
              [apply sub_r_z_i|right;left;eauto|iContiguous_next Hcont_rest1 12|apply PermFlows_refl|iCorrectPC a27 a_last|..]. 
            iEpilogue "(HPC & Hinstr & Hr_t2)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* jnz r_self *)
            iDestruct "Hprog" as "[Hinstr Hprog]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_jnz_success_next with "[$HPC $Hinstr $Hr_t1 $Hr_t2]");
              [apply jnz_i|apply PermFlows_refl|iCorrectPC a27 a_last|iContiguous_next Hcont_rest1 13|..].
            iEpilogue "(HPC & Hinstr & Hr_t2)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".  
            (* Since the assertion succeeded, we are now ready to jump back to the adv who called us *)
            (* Before we can return to the adversary, we must clear the stack and registers. This will 
               allow us to release the local frame, and show we are in a public future world by reinstating 
               the full stack invariant *)
            iDestruct (sts_full_world_std with "[] Hsts") as %Hstd6;[iPureIntro;split;apply related_sts_priv_refl|].     
            iMod (monotone_revoke_keep_alt _ (region_addrs stack_own_end e_r) with "[$Hsts $Hr]") as "(Hsts & Hr & Hstack_adv)";[apply NoDup_ListNoDup, region_addrs_NoDup|..]. 
            { iClear "Hreg' Hfull' full Hlocal Hrelj Hf4 Hrel Hinv Hadv_val Hfull2 Hfull3 Hlocal_1 Hrelk Hreg3".
              iAssert ( [∗ list] a39 ∈ region_addrs stack_own_end e_r, ⌜std_sta W6 !! countable.encode a39 = Some (countable.encode Temporary)⌝
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
            iAssert (▷ (∃ ws : list Word, [[a2,e_r]]↦ₐ[RWLX][[ws]]))%I with "[Hstack_adv Hframe Hb_r Ha2]" as ">Hstack".
            { iNext.
              iDestruct (region_addrs_exists with "Hstack_adv") as (ws_adv') "Hstack_adv".
              iDestruct (big_sepL2_sep with "Hstack_adv") as "[_ Hstack_adv]". iDestruct (big_sepL2_sep with "Hstack_adv") as "[Hstack_adv _]".
              rewrite /region_mapsto Hstack_eq app_assoc -Hstack_localeq.
              repeat rewrite app_comm_cons. iDestruct (big_sepL2_length with "Hstack_adv") as %Hadv_len.
              destruct ws_adv'; [inversion Hadv_len|]. iDestruct "Hstack_adv" as "[Hstack_own_end Hstack_adv]". 
              iExists ((_ :: _ :: _ ++ [w12]) ++ ws_adv'). 
              assert  (a4 :: stack_own_b :: stack_own = region_addrs a4 stack_own_last) as ->.
              { apply region_addrs_of_contiguous_between; auto. revert Hcont1. clear. intros Hcont1.
                repeat (inversion Hcont1 as [|????? Hcont1']; subst; auto; clear Hcont1; rename Hcont1' into Hcont1). }
              assert (region_addrs a4 stack_own_last = region_addrs a4 stack_own_end ++ [stack_own_end]) as Hlocal_eq''.
              { apply Hstack_localeq'. assert ((a4 + 1)%a = Some stack_own_b) as Hle;[iContiguous_next Hcont1 2|].
                revert Hstack_own_bound' Hle; clear; solve_addr. }
              rewrite Hlocal_eq''. 
              iApply mapsto_decomposition;[|iSimpl;iFrame "Hstack_adv Hb_r Ha2"].
              2: { iApply mapsto_decomposition;[|iFrame;done].
                   assert ((a4 + 8)%a = Some stack_own_end).
                   { assert ((a4 + 1)%a = Some stack_own_b) as Hincr';[iContiguous_next Hcont1 2|].
                     revert Hincr' Hstack_own_bound'. clear. solve_addr. }
                   rewrite /= region_addrs_length. apply incr_addr_region_size_iff; auto. }
              rewrite -Hlocal_eq''. revert Hlength_own Hcont1; clear; intros Hlength_own Hcont1.
              assert ((a2 + 2)%a = Some a4). apply contiguous_between_incr_addr with (i:=2) (ai:=a4) in Hcont1 as Hincr;auto. 
              apply region_addrs_of_contiguous_between in Hcont1. rewrite Hcont1 region_addrs_length /region_size in Hlength_own.
              rewrite /= region_addrs_length /region_size. solve_addr. 
            }
            (* We are now ready to clear the stack *)
            assert (contiguous_between (a41 :: rest1) a41 a_last) as Hcont_weak.
            { repeat (inversion Hcont_rest1 as [|????? Hf2']; subst; auto; clear Hcont_rest1; rename Hf2' into Hcont_rest1). }
            iDestruct (contiguous_between_program_split with "Hprog") as (mclear_addrs rclear_addrs rclear_first)
                                                                           "(Hmclear & Hrclear & #Hcont)"; [eauto|].
            iDestruct "Hcont" as %(Hcont_mclear & Hcont_rest2 & Hstack_eq2 & Hlink2).
            iDestruct (big_sepL2_length with "Hmclear") as %Hmclear_length.
            assert (7 < (length mclear_addrs)) as Hlt7;[rewrite Hmclear_length /=;lia|].
            assert (17 < (length mclear_addrs)) as Hlt17;[rewrite Hmclear_length /=;lia|].
            apply lookup_lt_is_Some_2 in Hlt7 as [ai Hai].
            apply lookup_lt_is_Some_2 in Hlt17 as [aj Haj].
            assert (ai + 10 = Some aj)%a.
            { rewrite (_: 10%Z = Z.of_nat (10 : nat)).
              eapply contiguous_between_incr_addr_middle; [eapply Hcont_mclear|..]. all: eauto. }
            assert (a41 < rclear_first)%a as Hcontlt2.
            { revert Hmclear_length Hlink2. clear. solve_addr. }
            assert (a27 <= a41)%a as Hcontge2.
            { apply region_addrs_of_contiguous_between in Hcont_scall1. subst.
              revert Hscall_length1 Hcont_rest1 Hcontlt1 Hcontlt2. clear =>Hscall_length Hf2 Hcontlt Hcontlt2.
              apply contiguous_between_middle_bounds with (i := 14) (ai := a41) in Hf2;[solve_addr|auto].
            }
            iApply (mclear_spec with "[-]"); last (rewrite /region_mapsto; iFrame "HPC Hr_stk Hstack");
              [ apply Hcont_mclear | ..]; eauto.
            { assert (rclear_first <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest2|].
              intros mid Hmid. apply isCorrectPC_inrange with a0 a_last; auto.
              revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid Hcontlt2 Hcontge2. clear; intros. split; try solve_addr.
            }
            { apply PermFlows_refl. }
            { apply PermFlows_refl. } 
            { apply withinBounds_le_addr in Hwb2. revert Hwb2; clear; solve_addr. }
            rewrite /mclear.
            destruct (strings.length mclear_addrs =? strings.length (mclear_instrs r_stk 10 2))%nat eqn:Hcontr;
              [|rewrite Hmclear_length in Hcontr;inversion Hcontr].
            iFrame "Hmclear".
            iDestruct "Hr_t2" as "[Hr_t1 Hr_t2]". 
            iGet_genpur_reg_map r3 r_t3 "Hmreg'" "Hfull3" "[Hr_t3 Hmreg']".
            iGet_genpur_reg_map r3 r_t4 "Hmreg'" "Hfull3" "[Hr_t4 Hmreg']".
            iGet_genpur_reg_map r3 r_t5 "Hmreg'" "Hfull3" "[Hr_t5 Hmreg']".
            iGet_genpur_reg_map r3 r_t6 "Hmreg'" "Hfull3" "[Hr_t6 Hmreg']".
            iGet_genpur_reg_map r3 r_t2 "Hmreg'" "Hfull3" "[Hr_t2' Hmreg']".
            iSplitL "Hr_t4". iNext; eauto.
            iSplitL "Hr_t1". iNext; eauto.
            iSplitL "Hr_t2'". iNext; eauto.
            iSplitL "Hr_t3". iNext; eauto.
            iSplitL "Hr_t5". iNext; eauto.
            iSplitL "Hr_t6". iNext; eauto.
            iNext. iIntros "(HPC & Hr_t1 & Hr_t2' & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6 & Hr_stk & Hstack & Hmclear)".
            (* insert general purpose registers back into map *)
            repeat (rewrite -(delete_commute _ r_t2)). 
            iClose_genpur_reg_map r_t2 "[Hr_t2' $Hmreg']" "Hmreg'".
            rewrite delete_insert_delete. 
            repeat (rewrite -(delete_insert_ne _ _ r_t2); [|auto]).
            iClose_genpur_reg_map r_t6 "[Hr_t6 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t6); [|auto]).
            iClose_genpur_reg_map r_t5 "[Hr_t5 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t5); [|auto]).
            iClose_genpur_reg_map r_t4 "[Hr_t4 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t4); [|auto]).
            iClose_genpur_reg_map r_t3 "[Hr_t3 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t3); [|auto]).
            repeat (rewrite -(delete_commute _ r_t1)). 
            iClose_genpur_reg_map r_t1 "[Hr_t1 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t1); [|auto]).
            repeat (rewrite -(delete_commute _ r_env)). 
            iClose_genpur_reg_map r_env "[Hr_env $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_env); [|auto]).
            repeat (rewrite -(delete_commute _ r_adv)). 
            iClose_genpur_reg_map r_adv "[Hr_t2 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_adv); [|auto]).
            repeat (rewrite -(delete_commute _ r_stk)). 
            iClose_genpur_reg_map r_stk "[Hr_stk $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_stk); [|auto]).
            (* We are now ready to close the stack invariant *)
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
            evar (W7 : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
            instantiate (W7 := (revoke (W6.1, (<[k:=countable.encode Released]> W6.2.1, W6.2.2)))).
            assert (related_sts_priv_world W6 W7) as Hrelated7.
            { apply related_sts_priv_trans_world with (revoke W6);[apply revoke_related_sts_priv;auto|].
              apply revoke_monotone;auto. apply related_priv_local_3; auto. 
            }
            assert (related_sts_priv_world (revoke_std_sta W.1.1, W.1.2, (<[i:=countable.encode false]> W.2.1, W.2.2)) W7)
              as Hrelated8.
            { apply related_sts_priv_trans_world with W6; [|auto].
              apply related_sts_priv_pub_trans_world with W5; [|auto].
              apply related_sts_priv_trans_world with W3; [|auto].
              apply related_sts_priv_pub_trans_world with W''; auto. }
            iAssert (sts_full_world sts_std W7) with "Hsts" as "Hsts". 
            iAssert (region W7) with "Hr" as "Hr".
            iAssert (⌜Forall (λ a : Addr, region_type_revoked W7 a) (region_addrs a2 e_r)⌝)%I as %Hrevoked7.
            { iRevert (Hrevoked). repeat rewrite Forall_forall. iIntros (Hrevoked). iIntros (x Hx).
              specialize (Hrevoked _ Hx). 
              apply elem_of_list_lookup in Hx as [x0 Hx0]. 
              iDestruct (big_sepL_lookup _ _ x0 x Hx0 with "Hstack_val") as "#Hrel_x".
              assert (∃ (ρ : region_type), (std_sta W7) !! (countable.encode x) = Some (countable.encode ρ)) as [ρ Hρ].
              { destruct Hrevoked as [Hrevoked_x Hstd_x].
                eapply related_sts_priv_world_std_sta_region_type;[apply Hrelated8|eauto|eauto].
              }
              destruct ρ;[| |auto]. 
              - iDestruct (region_open_temp_pwl _ _ _ _ Hρ with "[$Hrel_x $Hr $Hsts]") as (v) "(_ & _ & _ & Hcontr & _)";[auto|..].
                rewrite /region_mapsto.
                iDestruct (big_sepL2_extract_l _ _ _ _ _ Hx0 with "Hstack") as "[_ Hcontr']".
                iDestruct "Hcontr'" as (b0) "Hcontr'".
                iDestruct (cap_duplicate_false with "[$Hcontr $Hcontr']") as "Hfalse"; [auto..|by iApply bi.False_elim].
              - iDestruct (region_open_perm _ _ _ _ Hρ with "[$Hrel_x $Hr $Hsts]") as (v) "(_ & _ & _ & Hcontr & _)";[auto|..].
                rewrite /region_mapsto.
                iDestruct (big_sepL2_extract_l _ _ _ _ _ Hx0 with "Hstack") as "[_ Hcontr']".
                iDestruct "Hcontr'" as (b0) "Hcontr'".
                iDestruct (cap_duplicate_false with "[$Hcontr $Hcontr']") as "Hfalse"; [auto..|by iApply bi.False_elim].
            }
            iMod (monotone_close _ (region_addrs a2 e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
                with "[$Hsts $Hr Hstack]") as "[Hsts Hex]".
            { iDestruct (region_addrs_zeroes_trans with "Hstack") as "Hstack".
              iDestruct (big_sepL_sep with "[Hstack_val Hstack]") as "Hstack ";[iFrame "Hstack";iFrame "Hstack_val"|]. 
              iApply (big_sepL_mono with "Hstack") . 
              iIntros (k0 y Hsome) "[Hy Hr]". 
              rewrite /temp_resources. iFrame. 
              iSplit;[|iPureIntro]. 
              - iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
               * iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
               * by repeat (rewrite fixpoint_interp1_eq /=).
              - revert Hrevoked7; rewrite Forall_forall =>Hrevoked7. apply Hrevoked7. 
                apply elem_of_list_lookup; eauto.    
            }
            (* We are now ready to clear the registers *)
            iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length. 
            destruct rclear_addrs;[inversion Hrclear_length|].
            apply contiguous_between_cons_inv_first in Hcont_rest2 as Heq. subst rclear_first.
            iDestruct (contiguous_between_program_split with "Hrclear") as (rclear jmp_addrs jmp_addr)
                                                                           "(Hrclear & Hjmp & #Hcont)"; [eauto|].
            iDestruct "Hcont" as %(Hcont_rclear & Hcont_rest3 & Hstack_eq3 & Hlink3).
            clear Hrclear_length. iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
            assert (a42 < jmp_addr)%a as Hcontlt3.
            { revert Hrclear_length Hlink3. clear. rewrite /all_registers /=. solve_addr. }
            iApply (rclear_spec with "[-]"); last (iFrame "HPC Hrclear").
            { eauto. }
            { apply not_elem_of_list; apply elem_of_cons; by left. }
            { destruct rclear; inversion Hcont_rclear; eauto. inversion Hrclear_length. }
            { assert (jmp_addr <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest3|].
              intros mid Hmid. apply isCorrectPC_inrange with a0 a_last; auto.
              revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid Hcontlt2 Hcontge2 Hcontlt3. clear; intros. split; solve_addr.
            }
            { apply PermFlows_refl. }
            iSplitL "Hmreg'". 
            { iNext. iApply region_addrs_exists. iDestruct "Hfull3" as %Hfull3. 
              iApply (big_sepM_to_big_sepL with "Hmreg'");
                [apply NoDup_ListNoDup,NoDup_list_difference,all_registers_NoDup|].
              intros r0 Hin. assert (r0 ≠ PC ∧ r0 ≠ r_t0) as [Hne1 Hne2].
              { split; intros Hcontreq; subst r0. apply (not_elem_of_list PC all_registers [PC;r_t0]);auto. apply elem_of_cons; left; auto.
                apply (not_elem_of_list r_t0 all_registers [PC;r_t0]);auto. apply elem_of_cons; right; apply elem_of_cons; auto.
              }
              repeat (rewrite lookup_delete_ne;auto).
              destruct (decide (r_stk = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto]. 
              destruct (decide (r_adv = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto]. 
              destruct (decide (r_env = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto]. 
              destruct (decide (r_t1 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t3 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t4 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t5 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t6 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t2 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              apply Hfull3. 
            }
            iNext. iIntros "(HPC & Hmreg' & Hrclear)".
            (* We can now finally jump to the return capability *)
            (* jmp r_t0 *)
            iDestruct (big_sepL2_length with "Hjmp") as %Hjmp_length.
            destruct jmp_addrs; [inversion Hjmp_length|].
            destruct jmp_addrs; [|inversion Hjmp_length].
            apply contiguous_between_cons_inv_first in Hcont_rest3 as Heq; subst jmp_addr.
            iDestruct "Hjmp" as "[Hinstr _]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_t0]");
              [apply jmp_i|apply PermFlows_refl|..].
            { (* apply contiguous_between_bounds in Hcont_rest3 as Hle. *)
              inversion Hcont_rest3 as [| a' b' c' l'' Hnext Hcont_rest4 Heq Hnil Heq'].
              inversion Hcont_rest4; subst. 
              apply Hvpc2. revert Hcontge2 Hcontlt2 Hcontlt3 Hnext. clear. solve_addr. }
            (* we must now invoke the callback validity of the adversary. This means we must show we 
               are currently in a public future world of W! *)
            rewrite /enter_cond /interp_expr /interp_conf. iSimpl in "Hcallback".
            assert (related_sts_pub_world W (close_list (countable.encode <$> (l' ++ region_addrs a2 e_r)) W7)) as Hrelated9. 
            { rewrite /W7. revert Hrelated6. rewrite /W5 /W4.
              revert H3 H4 H5 H6 Hw3rel Hrelated3. rewrite /W''. rewrite /revoke /close_list /std_sta /std_rel /loc /=.
              intros. eapply related_pub_local_2; eauto; simpl; auto.
              revert Hwb2 Hwb3. clear. intros Hwb2 Hwb3.
              apply withinBounds_le_addr in Hwb2.
              apply withinBounds_le_addr in Hwb3. solve_addr. }
            iAssert (future_world g_ret W (close_list (countable.encode <$> (l' ++ region_addrs a2 e_r)) W7))%I as "#Hfuture". 
            { destruct g_ret; iSimpl.
              - iPureIntro. apply related_sts_pub_priv_world. apply Hrelated9.
              - iPureIntro. apply Hrelated9.
            } 
            evar (r4 : gmap RegName Word).
            instantiate (r4 := <[PC := inl 0%Z]>
                              (<[r_t0 := inr (E, g_ret, b_ret, e_ret, a_ret)]>
                               (create_gmap_default
                                  (list_difference all_registers [PC; r_t0]) (inl 0%Z)))).
            iDestruct ("Hcallback" $! r4 with "Hfuture") as "Hcallback_now".
            iEpilogue "(HPC & Hinstr & Hr_t0)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".  
            (* We must now reinstate all the invariants, and show that we are in a public future world *)
            (* we start by closing the program invariant *)
            iMod ("Hcls'" with "[$Hna Hprog_done Hmclear Hrclear Ha36]") as "Hna". 
            { iNext. iDestruct "Hprog_done" as "(Ha43 & Ha40 & Ha39 & Ha38 & Ha37 & 
                                                 Hpop2 & Hpop1 & Ha29 & Ha28 & Ha27 & Hprog_done)".
              iApply (big_sepL2_app with "Hprog_done [-]").
              iFrame "Ha27 Ha28 Ha29". 
              iApply (big_sepL2_app with "Hpop1 [-]").
              iApply (big_sepL2_app with "Hpop2 [-]").
              iFrame "Ha37 Ha38 Ha39 Ha40 Ha36". rewrite Hstack_eq2 Hstack_eq3.
              iApply (big_sepL2_app with "Hmclear [-]").
              iApply (big_sepL2_app with "Hrclear [-]").
              iFrame. done.
            } 
            (* next we close the local stack invariant, which has now been released *)
            iMod ("Hcls" with "[$Hna Hstate]") as "Hna". 
            { iNext. iExists Released. iFrame. }
            iClear "Hlocal_1 Hlocal Hf4 full Hfull' Hfull2 Hreg'".
            iDestruct "Hstack_adv_val'" as "#Hstack_adv_val'". 
            iDestruct (big_sepL_forall with "Hrevoked") as %Hrevoked8. 
            iSimpl in "HPC".
            (* Since we are in a public future world to W, we can now also close the rest of the temporary regions *)
            rewrite /close_list fmap_app -close_list_std_sta_idemp in Hrelated9.
            iMod (monotone_close_list_region _ (close_list_std_sta (countable.encode <$> region_addrs a2 e_r) (std_sta W7),
                                                std_rel W7, loc W7) with "[] [$Hsts $Hex Hrest]") as "[Hsts Hr]".
            { iPureIntro. apply Hrelated9. }
            { iApply (big_sepL_mono with "Hrest"). iIntros (k' y Hsome) "Hr".
              iDestruct "Hr" as "[Hr Hrev]". iDestruct "Hr" as (x0 x1) "[Htemp Hrel]".
              iExists x0,x1. iFrame.
            }
            iSpecialize ("Hcallback_now" with "[Hsts Hr Hmreg' HPC Hr_t0 Hna]"). 
            { rewrite /close_list /std_rel /std_sta.
              rewrite close_list_std_sta_idemp fmap_app. iSimpl in "Hr Hsts". iFrame "Hna Hr Hsts". iSplitR;[iSplit|].
              - iPureIntro. clear. 
                intros x. rewrite /= /r4.
                destruct (decide (PC = x));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                destruct (decide (r_t0 = x));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                exists (inl 0%Z). apply create_gmap_default_lookup.
                apply elem_of_list_difference. split;[apply all_registers_correct|].
                repeat (apply not_elem_of_cons; split;[auto|try apply not_elem_of_nil]).
              - iIntros (r0 Hne). rewrite /RegLocate.
                rewrite /r4 lookup_insert_ne;auto.
                destruct (decide (r_t0 = r0));[subst;rewrite lookup_insert|].
                + rewrite -close_list_std_sta_idemp. iApply (interp_monotone $! Hrelated9).
                  rewrite /interp /= fixpoint_interp1_eq /=. iFrame "Hcallback". 
                + rewrite lookup_insert_ne;[|auto]. 
                  assert (r0 ∈ (list_difference all_registers [PC; r_t0])) as Hin.
                  { apply elem_of_list_difference. split;[apply all_registers_correct|].
                    repeat (apply not_elem_of_cons; split;[auto|try apply not_elem_of_nil]). }
                  rewrite fixpoint_interp1_eq. iRevert (Hin).
                  rewrite (create_gmap_default_lookup _ (inl 0%Z : Word) r0).
                  iIntros (Hin). rewrite Hin. iSimpl. done. 
              - rewrite /registers_mapsto (insert_insert _ PC).
                iApply (big_sepM_insert_2 with "[HPC]"); first iFrame.
                iApply (big_sepM_insert_2 with "[Hr_t0]"); first iFrame.
                assert ((list_difference all_registers [PC;r_t0]) =
                        [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12;
                         r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24;
                         r_t25; r_t26; r_t27; r_t28; r_t29; r_t30; r_t31]) as ->; first auto. 
                rewrite /create_gmap_default. iSimpl in "Hmreg'". 
                repeat (iDestruct "Hmreg'" as "[Hr Hmreg']";
                        iApply (big_sepM_insert_2 with "[Hr]"); first iFrame).
                done.
            }  
            iDestruct "Hcallback_now" as "[_ Hcallback_now]".
            iApply wp_wand_l. iFrame "Hcallback_now". 
            iIntros (v) "Hv". 
            iIntros (halted). 
            iDestruct ("Hv" $! halted) as (r0 W0) "(#Hfull & Hmreg' & #Hrelated & Hna & Hsts & Hr)". 
            iDestruct ("Hrelated") as %Hrelated10.
            iExists r0,W0. iFrame "Hfull Hmreg' Hsts Hr Hna".
            iPureIntro. 
            eapply related_sts_priv_trans_world;[|apply Hrelated10].
            eapply related_sts_priv_trans_world;[apply Hrelated7|].
            apply related_sts_pub_priv_world. apply close_list_related_sts_pub; auto.     
          - rewrite Hr_t30. 
            assert (r2 !! r_adv = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
            rewrite /RegLocate Hr_t30_some. repeat rewrite fixpoint_interp1_eq. iSimpl. 
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
            repeat rewrite fixpoint_interp1_eq. iPureIntro. auto.
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
  Qed. 

End awkward_example. 
