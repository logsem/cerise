From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers macros.


Lemma NoDup_fst {A B : Type} (l : list (A*B)) :
  NoDup l.*1 -> NoDup l.
Proof.
  intros Hdup.
  induction l.
  - apply NoDup_nil.
  - destruct a. simpl in Hdup. apply NoDup_cons_iff in Hdup as [Hin Hdup].
    apply NoDup_cons_iff. split;auto.
    intros Hcontr%elem_of_list_In.
    apply Hin. apply elem_of_list_In.
    apply elem_of_list_fmap.
    exists (a,b). simpl. split;auto.
Qed.

Lemma fst_elem_of_cons {A B} `{EqDecision A} (l : list A) (x : A) :
  forall (l' : list B), In x (zip l l').*1 →
  In x l.
Proof.
  induction l.
  - intros l' Hin. inversion Hin.
  - intros l' Hin. simpl. destruct (decide (a = x)).
    + subst. left. auto.
    + right. destruct l';[done|].
      apply IHl with l'.
      destruct Hin as [Hcontr | Hin];[done|].
      auto. 
Qed.

Lemma length_fst_snd {A B} `{Countable A} (m : gmap A B) :
  strings.length (map_to_list m).*1 = strings.length (map_to_list m).*2.
Proof.
  induction m using map_ind.
  - rewrite map_to_list_empty. auto.
  - rewrite map_to_list_insert;auto. simpl. auto.
Qed. 
      
Lemma map_to_list_delete {A B} `{Countable A} `{EqDecision A} (m : gmap A B) (i : A) (x : B) :
  ∀ l, (i,x) :: l ≡ₚmap_to_list m ->
       NoDup (i :: l.*1) →
       (map_to_list (delete i m)) ≡ₚl.
Proof.
  intros l Hl Hdup.
  assert ((i,x) ∈ map_to_list m) as Hin.
  { rewrite -Hl. constructor. }
  assert (m !! i = Some x) as Hsome.
  { apply elem_of_map_to_list; auto. }
  apply Permutation.NoDup_Permutation;auto. 
  apply NoDup_ListNoDup, NoDup_map_to_list.
  apply NoDup_fst. apply NoDup_cons_iff in Hdup as [? ?]. auto. 
  intros [i0 x0]. split.
  - intros Hinx%elem_of_list_In%elem_of_map_to_list.
    assert (i ≠ i0) as Hne;[intros Hcontr;subst;simplify_map_eq|simplify_map_eq]. 
    apply elem_of_list_In.
    assert ((i0, x0) ∈ (i, x) :: l) as Hin'.
    { rewrite Hl. apply elem_of_map_to_list. auto. }
    apply elem_of_cons in Hin' as [Hcontr | Hin'];auto. 
    simplify_eq.
  - intros Hinx%elem_of_list_In.
    apply elem_of_list_In. apply elem_of_map_to_list. 
    assert (i ≠ i0) as Hne;[|simplify_map_eq].
    { intros Hcontr;subst.
      assert (NoDup ((i0, x) :: l)) as Hdup'.
      { rewrite Hl. apply NoDup_ListNoDup, NoDup_map_to_list. }
      assert (i0 ∈ l.*1) as Hinl.
      { apply elem_of_list_fmap. exists (i0,x0). simpl. split;auto. }
      apply NoDup_cons_iff in Hdup as [Hcontr ?]. apply Hcontr. apply elem_of_list_In. auto. 
    }
    assert ((i0, x0) ∈ (i, x) :: l) as Hin'.
    { constructor. auto. }
    revert Hin'. rewrite Hl =>Hin'. apply elem_of_map_to_list in Hin'. 
    auto.
Qed.


Lemma NoDup_map_to_list_fst (A B : Type) `{EqDecision A} `{Countable A}
       (m : gmap A B):
  NoDup (map_to_list m).*1.
Proof.
  induction m as [|i x m] using map_ind. 
  - rewrite map_to_list_empty. simpl. apply NoDup_nil. 
  - rewrite map_to_list_insert;auto.
    simpl. rewrite NoDup_cons_iff. split.
    + intros Hcontr%elem_of_list_In%elem_of_list_fmap.
      destruct Hcontr as [ab [Heqab Hcontr] ]. 
      destruct ab as [a b]. subst. simpl in *.
      apply elem_of_map_to_list in Hcontr. rewrite Hcontr in H0. inversion H0.
    + auto. 
Qed.

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

  Ltac disjoint_from_rmap rmap :=
    match goal with
    | Hsub : _ ⊆ dom (gset RegName) rmap |- _ !! ?r = _ => 
      assert (is_Some (rmap !! r)) as [x Hx];[apply elem_of_gmap_dom;apply Hsub;constructor|];
      apply map_disjoint_Some_l with rmap x;auto;apply map_disjoint_union_r_2;auto
    end.
  


  Lemma store_locals_spec_middle
        (* cont *) φ
        (* list of locals *) r1 locals mlocals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l a_l :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    region_size a_l e_l = strings.length locals →
    strings.length locals > 0 →
    writeAllowed p_l = true → withinBounds (p_l,b_l,e_l,a_l) = true ->
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length locals = length wsr ->

    (▷ store_locals a r1 locals
   ∗ ▷ PC ↦ᵣ inr (p,b,e,a_first)
   ∗ ▷ r1 ↦ᵣ inr (p_l,b_l,e_l,a_l)
   ∗ ▷ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
   ∗ ▷ (∃ ws, [[a_l,e_l]]↦ₐ[[ws]])
   ∗ ▷ (PC ↦ᵣ inr (p,b,e,a_last)
           ∗ r1 ↦ᵣ inr (p_l,b_l,e_l,e_l)
           ∗ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
           ∗ [[a_l,e_l]]↦ₐ[[wsr]]
           ∗ store_locals a r1 locals
           -∗ WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa Hwb Hperm Hlength) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)".
    iInduction (locals) as [|r locals] "IH" forall (a_l mlocals wsr a a_first Hvpc Hcont Hnz Hsize Hwb Hperm Hlength). 
    { apply Permutation.Permutation_nil in Hperm. inversion Hnz. }
    destruct locals as [|r' locals]. 
    - destruct wsr;[inversion Hlength|]. destruct wsr;[|inversion Hlength]. 
      apply Permutation_sym, Permutation_singleton in Hperm. 
      assert (mlocals = {[r:=w]}) as Heq;[|subst mlocals]. 
      { apply map_to_list_inj. rewrite map_to_list_singleton. apply Permutation_singleton. auto. }
      rewrite big_sepM_singleton. 
      rewrite /store_locals /store_locals_instrs. 
      iDestruct "Hbl" as (ws) "Hbl".
      iDestruct (big_sepL2_length with "Hbl") as %Hlength_bl.
      rewrite region_addrs_length Hsize in Hlength_bl.
      destruct ws;[inversion Hlength_bl|]. destruct ws;[|inversion Hlength_bl].
      assert (region_addrs a_l e_l = [a_l]) as Heq_locals;[ by rewrite /region_addrs Hsize /=|]. 
      rewrite /region_mapsto Heq_locals.
      iDestruct "Hbl" as "[Ha_l _]".
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      (* store r_t1 r *)
      destruct_list a.
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->. 
      iPrologue "Hprog". 
      iApply (wp_store_success_reg with "[$HPC $Hi $Hlocals $Ha_l $Hr_t1]");
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
      iFrame. done.
    - destruct wsr;[inversion Hlength|]. destruct wsr;[inversion Hlength|]. 
      simpl in *. 
      assert (mlocals !! r = Some w) as Hrw. 
      { apply elem_of_map_to_list. rewrite -Hperm. constructor. } 
      iDestruct (big_sepM_delete _ _ r with "Hlocals") as "[Hr Hlocals]";[eauto|]. 
      assert (is_Some (a_l + 1)%a) as [a_l' Ha_l'].
      { rewrite /region_size /= in Hsize. destruct (a_l + 1)%a eqn:Hnone;eauto.
        simpl in Hsize. revert Hnone Hsize;clear;solve_addr. }
      assert (region_addrs a_l e_l = a_l :: region_addrs a_l' e_l) as Heq.
      { rewrite /region_addrs Hsize /=. rewrite Ha_l' /=.  
        f_equiv. assert (region_size a_l' e_l = S (strings.length locals)) as ->;auto.
        revert Ha_l' Hsize;clear. rewrite /region_size. solve_addr. 
      }
      rewrite /region_mapsto Heq.
      iDestruct "Hbl" as (ws) "Hbl".
      iDestruct (big_sepL2_length with "Hbl") as %Hlengthbl.
      destruct ws;[inversion Hlengthbl|]. 
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
      iApply ("IH" $! a_l' (delete r mlocals) (w0 :: wsr) with "[] [] [] [] [] [] [] Hprog HPC Hr_t1 Hlocals [Hbl]").
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
      + iPureIntro. rewrite map_to_list_delete;eauto.
        assert (NoDup (r :: r' :: locals))%I as HNoDup.
        { assert (r :: r' :: locals = (zip (r :: r' :: locals) (w :: w0 :: wsr)).*1). 
          { simpl. f_equal. f_equal. assert (list_fmap (RegName * Word)%type RegName fst (zip locals wsr) = (zip locals wsr).*1) as ->;[auto|].
            rewrite fst_zip;auto. lia. }
          rewrite H.
          assert (zip (r :: r' :: locals) (w :: w0 :: wsr) = (r, w) :: (r', w0) :: zip locals wsr) as ->;auto. 
          rewrite Hperm. apply NoDup_map_to_list_fst. apply _. }
        clear -HNoDup Hlength. apply NoDup_cons_iff in HNoDup as [? HNoDup].
        apply NoDup_cons_iff. split.
        { intros Hcontr. apply H.
          apply fst_elem_of_cons with (w0 :: wsr). auto. }
        simpl. assert (list_fmap (RegName * Word)%type RegName fst (zip locals wsr) = (zip locals wsr).*1) as ->;auto.
        rewrite fst_zip;auto. lia. 
      + eauto.
      + eauto. 
      + iNext. iIntros "(HPC & Hr_t1 & Hlocals & Hbl & Hprog)".
        iApply "Hcont". iFrame.
        iApply (big_sepM_delete);[|iFrame]. apply elem_of_map_to_list. rewrite -Hperm. constructor. 
  Qed.
                                                          
      
  Lemma store_locals_spec
        (* cont *) φ
        (* list of locals *) r1 mlocals locals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    region_size b_l e_l = strings.length locals →
    strings.length locals > 0 → (* we assume the length of locals is non zero, or we would not be able to take a step before invoking continuation *)
    writeAllowed p_l = true →
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length locals = length wsr -> 

    (▷ store_locals a r1 locals
   ∗ ▷ PC ↦ᵣ inr (p,b,e,a_first)
   ∗ ▷ r1 ↦ᵣ inr (p_l,b_l,e_l,b_l)
   ∗ ▷ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
   ∗ ▷ (∃ ws, [[b_l,e_l]]↦ₐ[[ws]])
   ∗ ▷ (PC ↦ᵣ inr (p,b,e,a_last)
           ∗ r1 ↦ᵣ inr (p_l,b_l,e_l,e_l)
           ∗ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
           ∗ [[b_l,e_l]]↦ₐ[[wsr]]
           ∗ store_locals a r1 locals
           -∗ WP Seq (Instr Executable) {{ φ }})
   
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa Hperm Hlen) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)". 
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
    iAssert (⌜∀ r, r ∈ {[r_t1; r_t2; r_t3; r_t4; r_t5]} → r ≠ r1⌝)%I as %Hneregs.
    { iIntros (r Hin Hcontr). subst. apply Hsub in Hin.
      apply elem_of_gmap_dom in Hin as [x Hx].
      iDestruct (big_sepM_delete with "Hgen") as "[Hr Hgen]";[apply Hx|].
      by iDestruct (regname_dupl_false with "Hr Hr1") as "Hfalse". 
    }
    
    iDestruct (big_sepM_union with "[$Hlocals $Hparams]") as "Hlocalsparams";[auto|].
    iDestruct (big_sepM_union with "[$Hgen $Hlocalsparams]") as "Hgenlocalsparams";[apply map_disjoint_union_r_2;auto|].
    iAssert (⌜(rmap ∪ (mlocals ∪ mparams)) !! r1 = None⌝)%I as %Hnone.
    { destruct ((rmap ∪ (mlocals ∪ mparams)) !! r1) eqn:Hsome;auto.
      iDestruct (big_sepM_delete _ _ r1 with "Hgenlocalsparams") as "[Hi1 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse". done. }
    iAssert (⌜(rmap ∪ (mlocals ∪ mparams)) !! r_t0 = None⌝)%I as %Hnone'.
    { destruct ((rmap ∪ (mlocals ∪ mparams)) !! r_t0) eqn:Hsome;auto.
      iDestruct (big_sepM_delete _ _ r_t0 with "Hgenlocalsparams") as "[Hi1 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hr_t0") as "Hfalse". done. }
    iAssert (⌜r1 ≠ PC⌝)%I as %Hne1.
    { iIntros (->). iDestruct (regname_dupl_false with "HPC Hr1") as "Hfalse". done. }
    iAssert (⌜r1 ≠ r_t0⌝)%I as %Hne2.
    { iIntros (->). iDestruct (regname_dupl_false with "Hr_t0 Hr1") as "Hfalse". done. }
    iDestruct (big_sepM_insert with "[$Hgenlocalsparams $Hr1]") as "Hgenlocalsparams";[auto|].

    assert (dom (gset RegName) (<[r1:=wadv]> (rmap ∪ (mlocals ∪ mparams))) = all_registers_s ∖ {[PC; r_t0]}) as Hdomeq.
    { rewrite dom_insert_L !dom_union_L. revert Hdom1 Hne1 Hne2 Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5. clear. intros Hdom1 Hne1 Hne2 Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5. 
      assert (all_registers_s ∖ {[PC; r_t0]} = {[r1]} ∪ all_registers_s ∖ {[PC; r_t0; r1]}) as ->. 
      { rewrite -!difference_difference_L.
        rewrite -union_difference_L; auto.
        apply subseteq_difference_r;[set_solver|].
        apply subseteq_difference_r;[set_solver|].
        apply all_registers_subseteq. }
      assert (dom (gset RegName) rmap ∪ (dom (gset RegName) mlocals ∪ dom (gset RegName) mparams) =
              dom (gset RegName) mparams ∪ (dom (gset RegName) mlocals ∪ dom (gset RegName) rmap)) as ->.
      { rewrite (union_comm_L _ (dom _ mparams)). rewrite union_assoc_L. rewrite (union_comm_L _ (dom _ mparams)).
        rewrite -union_assoc_L. rewrite (union_comm_L _ (dom _ mlocals)). auto. }
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
    iApply (wp_wand_l _ _ _ (λne v, ((φ v ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)))%I. iSplitR.
    { iIntros (v) "[H|H] /=";auto. }
    iApply (malloc_spec with "[- $HPC $Hnainv $Hown $Hb $Ha_entry $Hmalloc_prog $Hr_t0 $Hgenlocalsparams]");auto;[|apply Hcont1|..].
    { eapply isCorrectPC_range_restrict;eauto. split;[clear;solve_addr|]. apply contiguous_between_bounds in Hcont2. auto. }
    iNext. iIntros "(HPC & Hmalloc & Hb & Ha_entry & Hregion & Hr_t0 & Hna & Hgenlocalsparams)".
    iDestruct "Hregion" as (b_l e_l Hlocals_size) "(Hr_t1 & Hbl)".

    (* in order to store the locals, we need to extract locals from the map *)
    rewrite !delete_insert_ne;auto. 2: { apply Hneregs. constructor. }
    rewrite delete_union. rewrite !insert_union_l.
    rewrite (delete_notin (mlocals ∪ mparams));[|disjoint_from_rmap rmap]. 
    iDestruct (big_sepM_union with "Hgenlocalsparams") as "[Hgen Hlocalsparams]".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap|]).
      apply map_disjoint_insert_l_2. apply lookup_union_None in Hnone as [? ?];auto.
      apply map_disjoint_delete_l. apply map_disjoint_union_r_2;auto. }
    iDestruct (big_sepM_union with "Hlocalsparams") as "[Hlocals Hparams]";auto.
    
    (* store locals *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (storelocals_prog rest2 link2) "(Hstorelocals_prog & Hprog & #Hcont2)";[apply Hcont2|].
    iDestruct "Hcont2" as %(Hcont3 & Hcont4 & Heqapp2 & Hlink2).
    iApply (store_locals_spec _ _ _ _ ((map_to_list mlocals).*2) with "[- $HPC $Hstorelocals_prog $Hr_t1 $Hlocals]");[|apply Hcont3|auto..].
    { eapply isCorrectPC_range_restrict;[apply Hvpc|].
      apply contiguous_between_bounds in Hcont1.
      apply contiguous_between_bounds in Hcont4. auto. }
    { clear -Hlocals_size. rewrite /region_size. solve_addr. }
    { rewrite zip_fst_snd. auto. }
    { apply length_fst_snd. }
    iSplitL "Hbl";[eauto|]. 
    iNext. iIntros "(HPC & Hr_t1 & Hmlocals & Hbl & Hstorelocals_prog)".

    (* prepare for the rest of the program: new correct PC range, get length of rest2, and assert its first element is link2 *)
    assert (isCorrectPC_range p b e link2 a_last) as Hvpc1.
    { eapply isCorrectPC_range_restrict;[apply Hvpc|]. split;[|clear;solve_addr].
      apply contiguous_between_bounds in Hcont1.
      apply contiguous_between_bounds in Hcont3. clear -Hcont3 Hcont1 Hlink2. solve_addr. }
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog. 
    destruct rest2 as [|? rest2];[inversion Hlength_prog|].
    apply contiguous_between_cons_inv_first in Hcont4 as Heq; subst a0.

    (* get some general purpose registers *)
    iDestruct (big_sepM_delete with "Hgen") as "[Hr_t2 Hgen]";[apply lookup_insert|].

    (* move r_t2 r_t1 *)
    destruct rest2 as [|? rest2];[inversion Hlength_prog|].
    iPrologue "Hprog". 
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link2 a_last|iContiguous_next Hcont4 0|]. 
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)". iCombine "Hstorelocals_prog Hmalloc" as "Hprog_done".
    iCombine "Hi" "Hprog_done" as "Hprog_done". 

    (* malloc 7 *)
    (* prepare the registers *)
    iDestruct (big_sepM_insert with "[$Hgen $Hr_t2]") as "Hgen";[apply lookup_delete|rewrite insert_delete insert_insert].
    rewrite -delete_insert_ne;[|apply Hneregs;constructor]. rewrite -!delete_insert_ne;auto. 
    iDestruct (big_sepM_insert with "[$Hgen $Hr_t1]") as "Hgen";[apply lookup_delete|rewrite insert_delete]. 
    iDestruct (big_sepM_union with "[$Hmlocals $Hparams]") as "Hlocalsparams";[auto|]. 
    iDestruct (big_sepM_union with "[$Hgen $Hlocalsparams]") as "Hgenlocalsparams".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap|]).
      apply map_disjoint_insert_l_2;[|apply map_disjoint_union_r_2];auto. apply lookup_union_None in Hnone as [? ?];auto. }
    (* we assert the register state has the needed domain *)
    assert (dom (gset RegName) (<[r_t1:=inr (RWX, b_l, e_l, e_l)]> (<[r_t2:=inr (RWX, b_l, e_l, e_l)]> (<[r_t3:=inl 0%Z]>
            (<[r_t4:=inl 0%Z]> (<[r_t5:=inl 0%Z]> (<[r1:=wadv]> rmap))))) ∪ (mlocals ∪ mparams)) = all_registers_s ∖ {[PC; r_t0]}) as Hdomeq'. 
    { rewrite dom_union_L 5!dom_insert_L.
      assert ({[r_t1]} ∪ ({[r_t2]} ∪ ({[r_t3]} ∪ ({[r_t4]} ∪ ({[r_t5]}
             ∪ dom (gset RegName) (<[r1:=wadv]> rmap))))) = dom (gset RegName) (<[r1:=wadv]> rmap)) as ->.
      { clear -Hsub. rewrite dom_insert_L. set_solver. }
      rewrite -dom_union_L -insert_union_l. auto. }    
    
    (* prepare the program memory *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog2 rest3 link3) "(Hmalloc & Hprog & #Hcont5)".
    { apply contiguous_between_cons_inv in Hcont4 as [?[? [? Hcont5] ] ].
      apply contiguous_between_cons_inv_first in Hcont5 as Heq;subst x. apply Hcont5. }
    iDestruct "Hcont5" as %(Hcont5 & Hcont6 & Heqapp3 & Hlink3).

    (* apply malloc spec *)
    iApply (malloc_spec 7 with "[- $HPC $Hnainv $Hna $Hb $Ha_entry $Hmalloc $Hr_t0 $Hgenlocalsparams]");auto;[|apply Hcont5|clear;lia|].
    { eapply isCorrectPC_range_restrict;eauto.
      assert (link2 + 1 = Some a0)%a as Hnext;[iContiguous_next Hcont4 0|]. 
      apply contiguous_between_bounds in Hcont6. clear -Hnext Hcont6. solve_addr. }
    iNext. iIntros "(HPC & Hmalloc & Hb & Ha_entry & Hregion & Hr_t0 & Hna & Hgenlocalsparams)".
    iDestruct "Hregion" as (b_l' e_l' Hact_size) "(Hr_t1 & Hbl')".
    
End call.
