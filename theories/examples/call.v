From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers macros.

  
Section scall.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* Macro for a heap based calling convention *)

  (* 
     The calling convention performs the following steps:
     
     1. It allocates heap space to store the activation record, the current r_env and the continuation
     2. It creates a copy of the PC and moves it to point to the continuing instruction
     3. It stores the activation record, r_env, and continuation 
     4. It restricts the allocated capability to be an E capability (a closure)
     5. It clears all registers except r1, rt_0 and the parameters
   *)

  Definition hw_1 := encodeInstr (Mov r_t1 (inr PC)).
  Definition hw_2 := encodeInstr (Lea r_t1 (inl 5%Z)).
  Definition hw_3 := encodeInstr (Load r_t2 r_t1).
  Definition hw_4 := encodeInstr (Lea r_t1 (inl 1%Z)).
  Definition hw_5 := encodeInstr (Load PC r_t1).

  Fixpoint store_locals_instrs r1 locals :=
    match locals with
    | [] => []
    | r :: locals => (store_r r1 r)
                 :: (lea_z r1 1)
                 :: store_locals_instrs r1 locals
    end.

  Definition store_locals a r1 locals :=
    ([∗ list] a_i;i ∈ a;(store_locals_instrs r1 locals), a_i ↦ₐ i)%I. 

  (* helper lemma for the length of the registers *)
  Ltac iRegNotEq Hne :=
    repeat (apply not_elem_of_cons in Hne;
            (let Hneq := fresh "Hneq" in destruct Hne as [Hneq Hne])); auto.


  (* -------------------------------- LTACS ------------------------------------------- *)
  
  (* Tactic for destructing a list into elements *)
  Ltac destruct_list l :=
    match goal with
    | H : strings.length l = _ |- _ =>
      let a := fresh "a" in
      let l' := fresh "l" in
      destruct l as [|a l']; [inversion H|];
      repeat (let a' := fresh "a" in
              destruct l' as [|a' l'];[by inversion H|]);
      destruct l'; [|by inversion H]
    end.

  Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [| a' a]; inversion Hlen; simpl
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

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.


  Lemma store_locals_spec_middle
        (* cont *) φ
        (* list of locals *) r1 locals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l a_l :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    region_size a_l e_l = strings.length locals →
    strings.length locals > 0 →
    writeAllowed p_l = true → withinBounds (p_l,b_l,e_l,a_l) = true ->

    (▷ store_locals a r1 locals
   ∗ ▷ PC ↦ᵣ inr (p,b,e,a_first)
   ∗ ▷ r1 ↦ᵣ inr (p_l,b_l,e_l,a_l)
   ∗ ▷ ([∗ list] r;w ∈ locals;wsr, r ↦ᵣ w)
   ∗ ▷ (∃ ws, [[a_l,e_l]]↦ₐ[[ws]])
   ∗ ▷ (PC ↦ᵣ inr (p,b,e,a_last)
           ∗ r1 ↦ᵣ inr (p_l,b_l,e_l,e_l)
           ∗ ([∗ list] r;w ∈ locals;wsr, r ↦ᵣ w)
           ∗ [[a_l,e_l]]↦ₐ[[wsr]]
           ∗ store_locals a r1 locals
           -∗ WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa Hwb) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)". 
    iLöb as "IH" forall (a_l locals a a_first wsr Hvpc Hcont Hnz Hsize Hwb).
    destruct locals as [|r locals]. 
    { (* our base case should be 1, not 0 *) inversion Hnz. }
    destruct locals as [|r' locals]. 
    - (* base case: 1 local *)
      rewrite /store_locals /store_locals_instrs. 
      iDestruct "Hbl" as (ws) "Hbl".
      iDestruct (big_sepL2_length with "Hlocals") as %Hlength_locals.
      iDestruct (big_sepL2_length with "Hbl") as %Hlength_bl.
      rewrite region_addrs_length Hsize in Hlength_bl.
      destruct wsr;[inversion Hlength_locals|]. destruct wsr;[|inversion Hlength_locals]. 
      destruct ws;[inversion Hlength_bl|]. destruct ws;[|inversion Hlength_bl].
      assert (region_addrs a_l e_l = [a_l]) as Heq_locals;[ by rewrite /region_addrs Hsize /=|]. 
      rewrite /region_mapsto Heq_locals.
      iDestruct "Hlocals" as "[Hr _]". 
      iDestruct "Hbl" as "[Ha_l _]".
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      (* store r_t1 r *)
      destruct_list a.
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->. 
      iPrologue "Hprog". 
      iApply (wp_store_success_reg with "[$HPC $Hi $Hr $Ha_l $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|split;auto|]. 
      iEpilogue "(HPC & Hprog_done & Hr & Hr_t1 & Ha_l)".
      (* lea r_t1 1 *)
      pose proof (contiguous_between_last _ _ _ a Hcont eq_refl) as Hlast.
      assert (a_l + 1 = Some e_l)%a as Hnext.
      { rewrite /region_size /= in Hsize. revert Hsize;clear;solve_addr. }
      iPrologue "Hprog". 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hlast|apply Hnext|destruct p_l;auto;inversion Hwa|].
      iEpilogue "(HPC & Hi & Hr_t1)". 
      (* φ *)
      iApply "Hcont".
      iFrame. iSplit;auto.
    - (* rewrite /store_locals /store_locals_instrs.  *)
      iDestruct "Hbl" as (ws) "Hbl".
      iDestruct (big_sepL2_length with "Hlocals") as %Hlength_locals.
      iDestruct (big_sepL2_length with "Hbl") as %Hlength_bl.
      rewrite region_addrs_length Hsize in Hlength_bl.
      destruct wsr;[inversion Hlength_locals|].
      destruct ws;[inversion Hlength_bl|].
      iDestruct "Hlocals" as "[Hr Hlocals]".
      assert (is_Some (a_l + 1)%a) as [a_l' Ha_l'].
      { rewrite /region_size /= in Hsize. destruct (a_l + 1)%a eqn:Hnone;eauto. revert Hnone Hsize;clear;solve_addr. }
      assert (region_addrs a_l e_l = a_l :: region_addrs a_l' e_l) as Heq.
      { rewrite /region_addrs Hsize /= Ha_l' /=.
        f_equiv. assert (region_size a_l' e_l = S (strings.length locals)) as ->;auto.
        revert Hsize Ha_l'; rewrite /region_size; clear;solve_addr. }
      rewrite /region_mapsto Heq. 
      iDestruct "Hbl" as "[Ha_l Hbl]".
      (* store r_t1 r *)
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog. simpl in Hlength_prog. 
      destruct a;[inversion Hlength_prog|].
      destruct a0;[inversion Hlength_prog|]. 
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->. 
      iPrologue "Hprog". 
      iApply (wp_store_success_reg with "[$HPC $Hi $Hr $Ha_l $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|split;auto|]. 
      iEpilogue "(HPC & Hprog_done & Hr & Hr_t1 & Ha_l)".
      (* lea r_t1 1 *) simpl in Hlength_prog. 
      destruct a1;[inversion Hlength_prog|]. 
      iPrologue "Hprog". 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 1|apply Ha_l'|destruct p_l;auto;inversion Hwa|].
      iEpilogue "(HPC & Hi & Hr_t1)". 
      (* IH *)
      iApply ("IH" $! a_l' (r' :: locals) (a :: a1) a with "[] [] [] [] [] Hprog HPC Hr_t1 Hlocals [Hbl]").
      + iPureIntro. eapply isCorrectPC_range_restrict;[eauto|].
        assert (a_first + 1 = Some a0)%a;[iContiguous_next Hcont 0|].
        assert (a0 + 1 = Some a)%a;[iContiguous_next Hcont 1|].
        split;[revert H H0;clear|clear];solve_addr.
      + iPureIntro.
        assert (a_first + 1 = Some a0)%a;[iContiguous_next Hcont 0|].
        assert (a0 + 1 = Some a)%a;[iContiguous_next Hcont 1|].
        inversion Hcont;simplify_eq.
        inversion H6;simplify_eq. auto.
      + iPureIntro;simpl. lia.
      + iPureIntro. simpl in *.
        revert Hsize Ha_l'. rewrite /region_size. clear. solve_addr.
      + iPureIntro. simpl in *.
        revert Hsize Ha_l' Hwb. rewrite /region_size. clear. intros.
        apply andb_true_intro. 
        apply andb_prop in Hwb. revert Hwb. rewrite !Z.leb_le !Z.ltb_lt.
        intros. 
        split; try solve_addr. 
      + eauto.
      + iNext. iIntros "(HPC & Hr_t1 & Hlocals & Hbl & Hprog)".
        iApply "Hcont". iFrame.
  Qed.
                                                          
      
  Lemma store_locals_spec
        (* cont *) φ
        (* list of locals *) r1 locals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    region_size b_l e_l = strings.length locals →
    strings.length locals > 0 → (* we assume the length of locals is non zero, or we would not be able to take a step before invoking continuation *)
    writeAllowed p_l = true →

    (▷ store_locals a r1 locals
   ∗ ▷ PC ↦ᵣ inr (p,b,e,a_first)
   ∗ ▷ r1 ↦ᵣ inr (p_l,b_l,e_l,b_l)
   ∗ ▷ ([∗ list] r;w ∈ locals;wsr, r ↦ᵣ w)
   ∗ ▷ (∃ ws, [[b_l,e_l]]↦ₐ[[ws]])
   ∗ ▷ (PC ↦ᵣ inr (p,b,e,a_last)
           ∗ r1 ↦ᵣ inr (p_l,b_l,e_l,e_l)
           ∗ ([∗ list] r;w ∈ locals;wsr, r ↦ᵣ w)
           ∗ [[b_l,e_l]]↦ₐ[[wsr]]
           ∗ store_locals a r1 locals
           -∗ WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)". 
    iApply (store_locals_spec_middle with "[$HPC $Hprog $Hr_t1 $Hlocals $Hbl $Hcont]");eauto. 
    simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt.
    split;[clear;lia|].
    rewrite /region_size in Hsize. lia.
  Qed. 


  Definition call_instrs f_m offset_to_cont r1 (locals params : list RegName) :=
    (* allocate and store locals *)
    malloc_instrs f_m (strings.length locals) ++
    store_locals_instrs r_t1 locals ++
    (* allocate the space for the activation record *)              
    [move_r r_t2 r_t1] ++
    malloc_instrs f_m 7 ++
    (* store the activation code *)
    [move_r r_t0 r_t1;
    store_z r_t0 hw_1;
    lea_z r_t0 1;
    store_z r_t0 hw_2;
    lea_z r_t0 1;
    store_z r_t0 hw_3;
    lea_z r_t0 1;
    store_z r_t0 hw_4;
    lea_z r_t0 1;
    store_z r_t0 hw_5;
    lea_z r_t0 1;
    (* store locals cap *)
    store_r r_t0 r_t2;
    lea_z r_t0 1;
    (* prepare and store continuation *)
    move_r PC r_t1;
    lea_z r_t1 offset_to_cont;
    store_r r_t0 r_t1;
    (* setup return capability *)
    lea_z r_t0 (-6);
    restrict_z r_t0 e] ++
    (* clear all registers except params, PC, r_t0 and r1 *)
    rclear_instrs (list_difference all_registers [PC;r_t0;r1]++params) ++
    (* jmp to r1 *)
    [jmp r1].

  Definition offset_to_cont_call params :=
    5 + (strings.length (rclear_instrs (list_difference all_registers params))) - 3. 

  Definition call a f_m r1 locals params :=
    ([∗ list] a_i;w ∈ a;(call_instrs f_m (offset_to_cont_call params) r1 locals params), a_i ↦ₐ w)%I. 

  Lemma call_spec
        (* pc *) a p b e a_first a_last
        (* malloc *) f_m b_m e_m mallocN EN
        (* linking *) b_link a_link e_link a_entry
        (* call *) r1 mlocals mparams wadv
        (* remaining registers *) (rmap rmap' : gmap RegName Word)
        (* cont *) φ :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    withinBounds (RW, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    strings.length (map_to_list mlocals).*1 > 0 →
    
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r1 ]} ∖ (dom (gset RegName) mparams) ∖ (dom (gset RegName) mlocals) →
    dom (gset RegName) rmap' = all_registers_s ∖ {[ PC; r_t0; r1 ]} ∖ (dom (gset RegName) mparams) →
    {[r_t1; r_t2; r_t3; r_t4; r_t5]} ⊆ dom (gset RegName) rmap → (* we need to know that neither params nor locals use these gen pur registers *)
    ↑mallocN ⊆ EN →

    (▷ call a f_m r1 (map_to_list mlocals).*1 (map_to_list mparams).*1
    ∗ ▷ PC ↦ᵣ inr (p,b,e,a_first)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ b ↦ₐ inr (RO,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ inr (E,b_m,e_m,b_m)
    (* registers *)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ mparams, r_i ↦ᵣ w_i)
    ∗ ▷ (∃ w, r_t0 ↦ᵣ w)
    ∗ ▷ r1 ↦ᵣ wadv
    ∗ ▷ ([∗ map] r_i↦w_i ∈ mlocals, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ ((∃ b_c e_c b_l e_l, PC ↦ᵣ updatePcPerm wadv
            ∗ ([∗ map] r_i↦_ ∈ rmap', r_i ↦ᵣ inl 0%Z)
            ∗ ([∗ map] r_i↦w_i ∈ mparams, r_i ↦ᵣ w_i)
            ∗ r1 ↦ᵣ wadv
            ∗ r_t0 ↦ᵣ inr (E,b_c,e_c,b_c)
            ∗ [[b_c,e_c]]↦ₐ[[ [inl hw_1;inl hw_2;inl hw_3;inl hw_4;inl hw_5;inr (RWX,b_l,e_l,e_l);inr (p,b,e,a_last)] ]]
            ∗ [[b_l,e_l]]↦ₐ[[ (map_to_list mparams).*2 ]]
            ∗ na_own logrel_nais EN)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hwb Hlink Hnz Hdom1 Hdom2 Hsub Hnainv)
            "(>Hprog & >HPC & #Hnainv & Hown & >Hb & >Ha_entry & >Hgen & >Hparams & >Hr_t0 & >Hr1 & >Hlocals & Hcont)".
    (* prepare the registers *)
    iDestruct "Hr_t0" as (w) "Hr_t0". 
    iAssert (⌜mparams ##ₘmlocals⌝)%I as %Hdisj1.
    { rewrite map_disjoint_spec. iIntros (i x y Hx Hy).
      iDestruct (big_sepM_delete _ _ i with "Hparams") as "[Hi1 Hparams]";[eauto|].
      iDestruct (big_sepM_delete _ _ i with "Hlocals") as "[Hi2 Hlocals]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    iAssert (⌜mparams ##ₘrmap⌝)%I as %Hdisj2.
    { rewrite map_disjoint_spec. iIntros (i x y Hx Hy).
      iDestruct (big_sepM_delete _ _ i with "Hparams") as "[Hi1 Hparams]";[eauto|].
      iDestruct (big_sepM_delete _ _ i with "Hgen") as "[Hi2 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    iAssert (⌜mlocals ##ₘrmap⌝)%I as %Hdisj3.
    { rewrite map_disjoint_spec. iIntros (i x y Hx Hy).
      iDestruct (big_sepM_delete _ _ i with "Hgen") as "[Hi1 Hgen]";[eauto|].
      iDestruct (big_sepM_delete _ _ i with "Hlocals") as "[Hi2 Hlocals]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    iAssert (⌜PC ∉ dom (gset RegName) mparams ∧ r_t0 ∉ dom (gset RegName) mparams ∧ r1 ∉ dom (gset RegName) mparams⌝)%I as %Hdisj4.
    { repeat iSplit; iIntros (Hcontr); apply elem_of_gmap_dom in Hcontr as [? Hi];
        (iDestruct (big_sepM_delete with "Hparams") as "[Hi1 Hparams]";[by eauto|]). 
      by iDestruct (regname_dupl_false with "Hi1 HPC") as "Hfalse". 
      by iDestruct (regname_dupl_false with "Hi1 Hr_t0") as "Hfalse". 
      by iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse". 
    }
    iAssert (⌜PC ∉ dom (gset RegName) mlocals ∧ r_t0 ∉ dom (gset RegName) mlocals ∧ r1 ∉ dom (gset RegName) mlocals⌝)%I as %Hdisj5.
    { repeat iSplit; iIntros (Hcontr); apply elem_of_gmap_dom in Hcontr as [? Hi];
        (iDestruct (big_sepM_delete with "Hlocals") as "[Hi1 Hlocals]";[by eauto|]). 
      by iDestruct (regname_dupl_false with "Hi1 HPC") as "Hfalse". 
      by iDestruct (regname_dupl_false with "Hi1 Hr_t0") as "Hfalse". 
      by iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse". 
    }
    
    iDestruct (big_sepM_union with "[$Hlocals $Hgen]") as "Hlocalsgen";[auto|].
    iDestruct (big_sepM_union with "[$Hparams $Hlocalsgen]") as "Hparamslocalsgen";[apply map_disjoint_union_r_2;auto|].
    iAssert (⌜(mparams ∪ (mlocals ∪ rmap)) !! r1 = None⌝)%I as %Hnone.
    { destruct ((mparams ∪ (mlocals ∪ rmap)) !! r1) eqn:Hsome;auto.
      iDestruct (big_sepM_delete _ _ r1 with "Hparamslocalsgen") as "[Hi1 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse". done. }
    iAssert (⌜(mparams ∪ (mlocals ∪ rmap)) !! r_t0 = None⌝)%I as %Hnone'.
    { destruct ((mparams ∪ (mlocals ∪ rmap)) !! r_t0) eqn:Hsome;auto.
      iDestruct (big_sepM_delete _ _ r_t0 with "Hparamslocalsgen") as "[Hi1 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hr_t0") as "Hfalse". done. }
    iAssert (⌜r1 ≠ PC⌝)%I as %Hne1.
    { iIntros (->). iDestruct (regname_dupl_false with "HPC Hr1") as "Hfalse". done. }
    iAssert (⌜r1 ≠ r_t0⌝)%I as %Hne2.
    { iIntros (->). iDestruct (regname_dupl_false with "Hr_t0 Hr1") as "Hfalse". done. }
    iDestruct (big_sepM_insert with "[$Hparamslocalsgen $Hr1]") as "Hparamslocalsgen";[auto|].

    assert (dom (gset RegName) (<[r1:=wadv]> (mparams ∪ (mlocals ∪ rmap))) = all_registers_s ∖ {[PC; r_t0]}) as Hdomeq.
    { rewrite dom_insert_L !dom_union_L. revert Hdom1 Hne1 Hne2 Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5. clear. intros Hdom1 Hne1 Hne2 Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5. 
      assert (all_registers_s ∖ {[PC; r_t0]} = {[r1]} ∪ all_registers_s ∖ {[PC; r_t0; r1]}) as ->. 
      { rewrite -!difference_difference_L.
        rewrite -union_difference_L; auto.
        apply subseteq_difference_r;[set_solver|].
        apply subseteq_difference_r;[set_solver|].
        apply all_registers_subseteq. }
      rewrite Hdom1. rewrite -!difference_difference_L -!union_difference_L; auto.
      repeat (apply subseteq_difference_r;[set_solver|]). apply all_registers_subseteq.
      repeat (apply subseteq_difference_r;[set_solver|]). apply all_registers_subseteq.
      apply subseteq_difference_r;[apply map_disjoint_dom;auto|]. 
      repeat (apply subseteq_difference_r;[set_solver|]). apply all_registers_subseteq.
    } 
    
    (* malloc f_m |locals| *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog rest1 link1) "(Hmalloc_prog & Hprog & #Hcont1)";[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont1 & Hcont2 & Heqapp1 & Hlink1).
    rewrite -/(malloc _ _ _ _).
    iApply (malloc_spec with "[- $HPC $Hnainv $Hown $Hb $Ha_entry $Hmalloc_prog $Hr_t0 $Hparamslocalsgen]");auto;[|apply Hcont1|..].
    { eapply isCorrectPC_range_restrict;eauto. split;[clear;solve_addr|]. apply contiguous_between_bounds in Hcont2. auto. }
    iNext. iIntros "(HPC & Hmalloc & Hb & Ha_entry & Hregion & Hr_t0 & Hna & Hparamslocalsgen)".
    iDestruct "Hregion" as (b_l e_l Hlocals_size) "(Hr_t1 & Hbl)". 
    
    
    
End call.
