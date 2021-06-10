From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import rules_binary logrel_binary fundamental_binary. 
From cap_machine.examples Require Import macros macros_binary macros_helpers malloc_binary counter_binary.
From stdpp Require Import countable.

Section counter_example_preamble.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.


  Definition counter_left_instrs :=
    incr_instrs ++ read_instrs.

  Definition counter_right_instrs :=
    decr_instrs ++ read_neg_instrs. 

  Definition counter_left a :=
    ([∗ list] a_i;w ∈ a;counter_left_instrs, a_i ↦ₐ w )%I.

  Definition counter_right a :=
    ([∗ list] a_i;w ∈ a;counter_right_instrs, a_i ↣ₐ w )%I.
  
  Definition counter_left_instrs_length : Z :=
    Eval cbv in (length (counter_left_instrs)).
  Definition incr_instrs_length : Z :=
    Eval cbv in (length (incr_instrs)).
  Definition read_instrs_length : Z :=
    Eval cbv in (length (read_instrs)).

  Definition counter_right_instrs_length : Z :=
    Eval cbv in (length (counter_right_instrs)).
  Definition decr_instrs_length : Z :=
    Eval cbv in (length (decr_instrs)).
  Definition read_neg_instrs_length : Z :=
    Eval cbv in (length (read_neg_instrs)).
  
  (* [f_m] is the offset of the malloc capability *)
  (* [offset_to_counter] is the offset between the [move_r r_t1 PC] instruction
  and the code of the implementation counter, which will be the concatenation of: incr;read *)
  Definition counter_left_preamble_instrs (f_m offset_to_counter: Z) :=
    malloc_instrs f_m 1%nat ++
    [store_z r_t1 0;
    move_r r_t2 r_t1;
    move_r r_t1 PC;
    move_r r_t8 r_t2; (* we keep a copy of the capability for the other closures *)
    move_r r_t9 r_t1; (* same for PC *)
    (* closure for incr *)
    lea_z r_t1 offset_to_counter] ++
    crtcls_instrs f_m ++
    [move_r r_t10 r_t1;
    move_r r_t2 r_t8;
    move_r r_t1 r_t9;
    (* closure for read *)
    lea_z r_t1 (offset_to_counter + incr_instrs_length)] ++
    crtcls_instrs f_m ++
    (* cleanup *)
    [move_r r_t2 r_t10;
    move_z r_t10 0;
    move_z r_t8 0;
    move_z r_t9 0;
    jmp r_t0].

  (* [f_m] is the offset of the malloc capability *)
  (* [offset_to_counter] is the offset between the [move_r r_t1 PC] instruction
  and the code of the specification counter, which will be the concatenation of: decr;read_neg *)
  Definition counter_right_preamble_instrs (f_m offset_to_counter: Z) :=
    malloc_instrs f_m 1%nat ++
    [store_z r_t1 0;
    move_r r_t2 r_t1;
    move_r r_t1 PC;
    move_r r_t8 r_t2; (* we keep a copy of the capability for the other closures *)
    move_r r_t9 r_t1; (* same for PC *)
    (* closure for incr *)
    lea_z r_t1 offset_to_counter] ++
    crtcls_instrs f_m ++
    [move_r r_t10 r_t1;
    move_r r_t2 r_t8;
    move_r r_t1 r_t9;
    (* closure for read *)
    lea_z r_t1 (offset_to_counter + decr_instrs_length)] ++
    crtcls_instrs f_m ++
    (* cleanup *)
    [move_r r_t2 r_t10;
    move_z r_t10 0;
    move_z r_t8 0;
    move_z r_t9 0;
    jmp r_t0].
  
  Definition counter_left_preamble f_m offset_to_counter ai :=
    ([∗ list] a_i;w_i ∈ ai;(counter_left_preamble_instrs f_m offset_to_counter), a_i ↦ₐ w_i)%I.
  Definition counter_right_preamble f_m offset_to_counter ai :=
    ([∗ list] a_i;w_i ∈ ai;(counter_right_preamble_instrs f_m offset_to_counter), a_i ↣ₐ w_i)%I.
  
  (* Compute the offset from the start of the program to the move_r r_t1 PC
     instruction. Will be used later to compute [offset_to_awkward]. *)
  (* This is somewhat overengineered, but could be easily generalized to compute
     offsets for other programs if needed. *)
  (* The two preambles have the same number of instructions, so we can here use the same value
     to calculate the offset *)
  Definition counter_preamble_move_offset_ : Z.
  Proof.
    unshelve refine (let x := _ : Z in _). {
      set instrs := counter_left_preamble_instrs 0 0.
      assert (sig (λ l1, ∃ l2, instrs = l1 ++ l2)) as [l1 _]; [do 2 eexists | exact (length l1)].

      assert (forall A (l1 l2 l3 l4: list A), l2 = l3 ++ l4 → l1 ++ l2 = (l1 ++ l3) ++ l4) as step_app.
      { intros * ->. by rewrite app_assoc. }
      assert (forall A (l1 l2 l3: list A) x, l1 = l2 ++ l3 → x :: l1 = (x :: l2) ++ l3) as step_cons.
      { intros * ->. reflexivity. }
      assert (forall A (l1 l2: list A) x, x :: l1 = l2 → x :: l1 = l2) as prepare_cons.
      { auto. }
      assert (forall A (l: list A), l = [] ++ l) as stop.
      { reflexivity. }

      unfold instrs, counter_left_preamble_instrs.
      (* Program-specific part *)
      eapply step_app.
      repeat (eapply prepare_cons;
              lazymatch goal with
              | |- move_r r_t1 PC :: _ = _ => fail
              | _ => eapply step_cons end).
      eapply stop.
    }
    exact x.
  Defined.

  Definition counter_preamble_move_offset : Z :=
    Eval cbv in counter_preamble_move_offset_.

  Definition counter_preamble_instrs_length : Z :=
    Eval cbv in (length (counter_left_preamble_instrs 0 0)).


  (* The following two lemmas show that the created closures are valid *)

  Definition cls_inv b_cls e_cls b_cls' e_cls' pc1 pc2 c1 pcs1 pcs2 c2 : iProp Σ :=
    ([[b_cls,e_cls]]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; pc1; c1] ]]
     ∗ [[b_cls',e_cls']]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; pc2; c1] ]]
     ∗ [[b_cls,e_cls]]↣ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; pcs1; c2] ]]
     ∗ [[b_cls',e_cls']]↣ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; pcs2; c2] ]])%I.
  
  Lemma incr_decr_closure_valid incr_prog decr_prog
        restc srestc count_incrdecrN countN count_clsN
        b_cls e_cls (* incr/decr closure *)
        b_cls' e_cls' (* read/read_neg closure *)
        pc_p pc_b pc_e counter_first counter_end linkc (* left PC values *)
        pcs_p pcs_b pcs_e scounter_first scounter_end slinkc (* right PC values *)
        b_cell e_cell (* left counter *)
        bs_cell es_cell (* right counter *):

    pc_p ≠ E → pcs_p ≠ E →

    contiguous_between incr_prog counter_first linkc →
    contiguous_between decr_prog scounter_first slinkc →
    isCorrectPC_range pc_p pc_b pc_e counter_first counter_end →
    isCorrectPC_range pcs_p pcs_b pcs_e scounter_first scounter_end →
    
    contiguous_between restc linkc counter_end →
    contiguous_between srestc slinkc scounter_end →
    (b_cell + 1)%a = Some e_cell →
    (bs_cell + 1)%a = Some es_cell →
    nclose specN ## ↑countN →
    
    ⊢ (spec_ctx -∗ inv countN (counter_inv b_cell bs_cell) -∗
     na_inv logrel_nais count_incrdecrN (incr_left incr_prog ∗ decr_right decr_prog) -∗
     na_inv logrel_nais count_clsN (cls_inv b_cls e_cls b_cls' e_cls' (WCap pc_p pc_b pc_e counter_first)
                                            (WCap pc_p pc_b pc_e linkc) (WCap RWX b_cell e_cell b_cell)
                                            
                                            (WCap pcs_p pcs_b pcs_e scounter_first) (WCap pcs_p pcs_b pcs_e slinkc)
                                            (WCap RWX bs_cell es_cell bs_cell)) -∗
     na_own logrel_nais ⊤ -∗
    interp (WCap E b_cls e_cls b_cls,WCap E b_cls e_cls b_cls))%I.
  Proof.
    iIntros (Hnp Hnps Hcont_incr Hcont_decr Hvpc_counter Hvspc_counter Hcont_restc Hcont_srestc Hbe_cell Hbes_cell Hnclose)
            "#Hspec #Hcounter_inv #Hincr #Hcls_inv HnaI". 
    rewrite /interp fixpoint_interp1_eq /=. iSplit;auto.
    iIntros (r') "". iNext. iModIntro.
    iIntros "(#Hr_valid & Hregs' & Hsegs' & HnaI & Hj)". destruct r' as [r1' r2']. simpl. 
    iDestruct (interp_reg_eq _ _ (WCap RX b_cls e_cls b_cls) with "Hr_valid") as %Heq.
    iDestruct "Hr_valid" as "[Hr'_full Hr'_valid]"; iDestruct "Hr'_full" as %Hr'_full.
    assert (∀ x : RegName, is_Some (r1' !! x)) as Hr'_full_left;[intros x; destruct Hr'_full with x;eauto|].
    assert (∀ x : RegName, is_Some (r2' !! x)) as Hr'_full_right;[intros x; destruct Hr'_full with x;eauto|]. 
    pose proof (regmap_full_dom _ Hr'_full_left) as Hdom_r'.
    pose proof (regmap_full_dom _ Hr'_full_right) as Hdom_s'.
    
    iSplitR; [auto|]. rewrite /interp_conf.
    
    iDestruct (na_inv_acc with "Hcls_inv HnaI") as ">(>(Hcls & Hcls' & Hscls & Hscls') & Hna & Hcls_close)";
      [auto..|].
    
    rewrite /registers_mapsto /spec_registers_mapsto.
    rewrite -(insert_delete r1') -(insert_delete r2').

    iDestruct (big_sepM_insert with "Hregs'") as "[HPC Hregs']". by apply lookup_delete. 
    destruct (Hr'_full_left r_t1) as [r1v ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs'") as "[Hr1 Hregs']".
      by rewrite lookup_delete_ne //.
    destruct (Hr'_full_left r_env) as [renvv ?].
    iDestruct (big_sepM_delete _ _ r_env with "Hregs'") as "[Hrenv Hregs']".
      by rewrite !lookup_delete_ne //.
      
    iDestruct (big_sepM_insert with "Hsegs'") as "[HsPC Hsegs']". by apply lookup_delete. 
    destruct (Hr'_full_right r_t1) as [rs1v ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hsegs'") as "[Hs1 Hsegs']".
      by rewrite lookup_delete_ne //.
    destruct (Hr'_full_right r_env) as [senvv ?].
    iDestruct (big_sepM_delete _ _ r_env with "Hsegs'") as "[Hsenv Hsegs']".
      by rewrite !lookup_delete_ne //.

    (* Run the closure activation code *)
    iApply (closure_activation_spec with "[- $HPC $Hr1 $Hrenv $Hcls]");
      [done| |done|..].
    { intros ? [? ?]. constructor; try split; auto. }
    rewrite updatePcPerm_cap_non_E //;[].
    iIntros "(HPC & Hr1 & Hrenv & Hcls)".
    iMod (closure_activation_spec_step with "[$Hspec $Hj $HsPC $Hs1 $Hsenv $Hscls]")
      as "(Hj & HsPC & Hs1 & Hsenv & Hscls)";
      [done| |done|auto..].
    { intros ? [? ?]. constructor; try split; auto. }
    rewrite updatePcPerm_cap_non_E //;[].
    
    (* close the invariant for the closure *)
    iDestruct ("Hcls_close" with "[Hcls Hcls' Hscls Hscls' $Hna]") as ">Hna".
    { iNext. iFrame. }
    
    destruct (Hr'_full_left r_t0) as [r0v Hr0v].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs'") as "[Hr0 Hregs']".
      by rewrite !lookup_delete_ne // lookup_delete_ne //.
      
   destruct (Hr'_full_right r_t0) as [s0v Hs0v].
   iDestruct (big_sepM_delete _ _ r_t0 with "Hsegs'") as "[Hs0 Hsegs']".
      by rewrite !lookup_delete_ne // lookup_delete_ne //.
      
    iApply (incr_spec with "[$Hspec $Hj $HPC $HsPC $Hr0 $Hs0 $Hrenv $Hsenv $Hregs' $Hsegs' $Hna $Hincr Hr1 Hs1 $Hcounter_inv]");
      [| |apply Hcont_incr|apply Hcont_decr|auto|auto| | |apply Hnclose|..].
    { eapply isCorrectPC_range_restrict; [apply Hvpc_counter|]. split;[clear;solve_addr|].
      apply contiguous_between_bounds in Hcont_restc. apply Hcont_restc. }
    { eapply isCorrectPC_range_restrict; [apply Hvspc_counter|]. split;[clear;solve_addr|].
      apply contiguous_between_bounds in Hcont_srestc. apply Hcont_srestc. }
    { rewrite !dom_delete_L Hdom_r'. clear. set_solver. }
    { rewrite !dom_delete_L Hdom_s'. clear. set_solver. }
    { iSplitL "Hr1";[eauto|]. iSplitL;[eauto|]. iSplit. 
      - iDestruct ("Hr'_valid" $! r_t0 with "[]") as "Hval";[auto|]. rewrite /RegLocate Hr0v Hs0v /interp//.
      - iIntros (reg Hne). iDestruct ("Hr'_valid" $! reg with "[]") as "Hval";[done|]. 
        rewrite /RegLocate !fixpoint_interp1_eq. 
        destruct (decide (reg = r_t0));[subst;rewrite !lookup_delete;done|rewrite !(lookup_delete_ne _ r_t0)//]. 
        destruct (decide (reg = r_env));[subst;rewrite !lookup_delete;done|rewrite !(lookup_delete_ne _ r_env)//]. 
        destruct (decide (reg = r_t1));[subst;rewrite !lookup_delete;done|rewrite !(lookup_delete_ne _ r_t1)//]. 
        rewrite !(lookup_delete_ne _ PC)//. 
    }
    { iNext. iIntros (?) "HH". iIntros (->). iApply "HH". eauto. }
  Qed.

  Lemma read_read_neg_closure_valid read_prog read_neg_prog restc srestc
        read_readnegN countN count_clsN
        b_cls e_cls (* incr/decr closure *)
        b_cls' e_cls' (* read/read_neg closure *)
        pc_p pc_b pc_e counter_first counter_end linkc (* left PC values *)
        pcs_p pcs_b pcs_e scounter_first scounter_end slinkc (* right PC values *)
        b_cell e_cell (* left counter *)
        bs_cell es_cell (* right counter *):

    pc_p ≠ E → pcs_p ≠ E →

    contiguous_between read_prog linkc counter_end →
    contiguous_between read_neg_prog slinkc scounter_end →
    isCorrectPC_range pc_p pc_b pc_e counter_first counter_end →
    isCorrectPC_range pcs_p pcs_b pcs_e scounter_first scounter_end →

    contiguous_between restc counter_first linkc →
    contiguous_between srestc scounter_first slinkc →
    
    (b_cell + 1)%a = Some e_cell →
    (bs_cell + 1)%a = Some es_cell →
    nclose specN ## ↑countN →
    
    ⊢ (spec_ctx -∗ inv countN (counter_inv b_cell bs_cell) -∗
     na_inv logrel_nais read_readnegN (read_left read_prog ∗ read_right read_neg_prog) -∗
     na_inv logrel_nais count_clsN (cls_inv b_cls e_cls b_cls' e_cls' (WCap pc_p pc_b pc_e counter_first)
                                            (WCap pc_p pc_b pc_e linkc) (WCap RWX b_cell e_cell b_cell)
                                            
                                            (WCap pcs_p pcs_b pcs_e scounter_first) (WCap pcs_p pcs_b pcs_e slinkc)
                                            (WCap RWX bs_cell es_cell bs_cell)) -∗
     na_own logrel_nais ⊤ -∗
    interp (WCap E b_cls' e_cls' b_cls',WCap E b_cls' e_cls' b_cls'))%I.
  Proof.
    iIntros (Hnp Hnps Hcont_incr Hcont_decr Hvpc_counter Hvspc_counter Hcont_restc Hcont_srestc Hbe_cell Hbes_cell Hnclose)
            "#Hspec #Hcounter_inv #Hincr #Hcls_inv HnaI". 
    rewrite /interp fixpoint_interp1_eq /=. iSplit;auto.
    iIntros (r') "". iNext. iModIntro.
    iIntros "(#Hr_valid & Hregs' & Hsegs' & HnaI & Hj)". destruct r' as [r1' r2']. simpl. 
    iDestruct (interp_reg_eq _ _ (WCap RX b_cls e_cls b_cls) with "Hr_valid") as %Heq.
    iDestruct "Hr_valid" as "[Hr'_full Hr'_valid]"; iDestruct "Hr'_full" as %Hr'_full.
    assert (∀ x : RegName, is_Some (r1' !! x)) as Hr'_full_left;[intros x; destruct Hr'_full with x;eauto|].
    assert (∀ x : RegName, is_Some (r2' !! x)) as Hr'_full_right;[intros x; destruct Hr'_full with x;eauto|]. 
    pose proof (regmap_full_dom _ Hr'_full_left) as Hdom_r'.
    pose proof (regmap_full_dom _ Hr'_full_right) as Hdom_s'.
    
    iSplitR; [auto|]. rewrite /interp_conf.
    
    iDestruct (na_inv_acc with "Hcls_inv HnaI") as ">(>(Hcls & Hcls' & Hscls & Hscls') & Hna & Hcls_close)";
      [auto..|].
    
    rewrite /registers_mapsto /spec_registers_mapsto.
    rewrite -(insert_delete r1') -(insert_delete r2').

    iDestruct (big_sepM_insert with "Hregs'") as "[HPC Hregs']". by apply lookup_delete. 
    destruct (Hr'_full_left r_t1) as [r1v ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs'") as "[Hr1 Hregs']".
      by rewrite lookup_delete_ne //.
    destruct (Hr'_full_left r_env) as [renvv ?].
    iDestruct (big_sepM_delete _ _ r_env with "Hregs'") as "[Hrenv Hregs']".
      by rewrite !lookup_delete_ne //.
      
    iDestruct (big_sepM_insert with "Hsegs'") as "[HsPC Hsegs']". by apply lookup_delete. 
    destruct (Hr'_full_right r_t1) as [rs1v ?].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hsegs'") as "[Hs1 Hsegs']".
      by rewrite lookup_delete_ne //.
    destruct (Hr'_full_right r_env) as [senvv ?].
    iDestruct (big_sepM_delete _ _ r_env with "Hsegs'") as "[Hsenv Hsegs']".
      by rewrite !lookup_delete_ne //.

    (* Run the closure activation code *)
    iApply (closure_activation_spec with "[- $HPC $Hr1 $Hrenv $Hcls']");
      [done| |done|..].
    { intros ? [? ?]. constructor; try split; auto. }
    rewrite updatePcPerm_cap_non_E //;[].
    iIntros "(HPC & Hr1 & Hrenv & Hcls')".
    iMod (closure_activation_spec_step with "[$Hspec $Hj $HsPC $Hs1 $Hsenv $Hscls']")
      as "(Hj & HsPC & Hs1 & Hsenv & Hscls')";
      [done| |done|auto..].
    { intros ? [? ?]. constructor; try split; auto. }
    rewrite updatePcPerm_cap_non_E //;[].
    
    (* close the invariant for the closure *)
    iDestruct ("Hcls_close" with "[Hcls Hcls' Hscls Hscls' $Hna]") as ">Hna".
    { iNext. iFrame. }
    
    destruct (Hr'_full_left r_t0) as [r0v Hr0v].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs'") as "[Hr0 Hregs']".
      by rewrite !lookup_delete_ne // lookup_delete_ne //.
      
   destruct (Hr'_full_right r_t0) as [s0v Hs0v].
   iDestruct (big_sepM_delete _ _ r_t0 with "Hsegs'") as "[Hs0 Hsegs']".
     by rewrite !lookup_delete_ne // lookup_delete_ne //.
   
   iApply (read_spec with "[$Hspec $Hj $HPC $HsPC $Hr0 $Hs0 $Hrenv $Hsenv $Hregs' $Hsegs' $Hna $Hincr Hr1 Hs1 $Hcounter_inv]");
      [| |apply Hcont_incr|apply Hcont_decr|auto|auto| | |apply Hnclose|..].
    { eapply isCorrectPC_range_restrict; [apply Hvpc_counter|]. split;[|clear;solve_addr].
      apply contiguous_between_bounds in Hcont_restc. apply Hcont_restc. }
    { eapply isCorrectPC_range_restrict; [apply Hvspc_counter|]. split;[|clear;solve_addr].
      apply contiguous_between_bounds in Hcont_srestc. apply Hcont_srestc. }
    { rewrite !dom_delete_L Hdom_r'. clear. set_solver. }
    { rewrite !dom_delete_L Hdom_s'. clear. set_solver. }
    { iSplitL "Hr1";[eauto|]. iSplitL;[eauto|]. iSplit. 
      - iDestruct ("Hr'_valid" $! r_t0 with "[]") as "Hval";[auto|]. rewrite /RegLocate Hr0v Hs0v /interp//.
      - iIntros (reg Hne). iDestruct ("Hr'_valid" $! reg with "[]") as "Hval";[done|]. 
        rewrite /RegLocate !fixpoint_interp1_eq. 
        destruct (decide (reg = r_t0));[subst;rewrite !lookup_delete;done|rewrite !(lookup_delete_ne _ r_t0)//]. 
        destruct (decide (reg = r_env));[subst;rewrite !lookup_delete;done|rewrite !(lookup_delete_ne _ r_env)//]. 
        destruct (decide (reg = r_t1));[subst;rewrite !lookup_delete;done|rewrite !(lookup_delete_ne _ r_t1)//]. 
        rewrite !(lookup_delete_ne _ PC)//. 
    }
    { iNext. iIntros (?) "HH". iIntros (->). iApply "HH". eauto. }
  Qed.




  Definition countN : namespace := nroot .@ "awkN".
  Definition count_invN : namespace := countN .@ "inv".
  Definition count_incrN : namespace := countN .@ "incr".
  Definition count_readN : namespace := countN .@ "read".
  Definition count_clsN : namespace := countN .@ "cls".
  Definition count_env : namespace := countN .@ "env". 
  
  Lemma counter_preamble_spec (f_m offset_to_counter: Z) r
        pc_p pc_b pc_e pcs_p pcs_b pcs_e
        ai a_first a_end b_link e_link a_link a_entry 
        ais s_first s_end bs_link es_link s_link s_entry 
        mallocN b_m e_m
        ai_counter counter_first counter_end a_move
        ais_counter counter_sfirst counter_send s_move :

    isCorrectPC_range pc_p pc_b pc_e a_first a_end →
    isCorrectPC_range pcs_p pcs_b pcs_e s_first s_end →

    contiguous_between ai a_first a_end →
    contiguous_between ais s_first s_end →
    
    
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    
    withinBounds bs_link es_link s_entry = true →
    (s_link + f_m)%a = Some s_entry →
    
    
    (a_first + counter_preamble_move_offset)%a = Some a_move →
    (a_move + offset_to_counter)%a = Some counter_first →
    isCorrectPC_range pc_p pc_b pc_e counter_first counter_end →
    contiguous_between ai_counter counter_first counter_end →
    
    (s_first + counter_preamble_move_offset)%a = Some s_move →
    (s_move + offset_to_counter)%a = Some counter_sfirst →
    isCorrectPC_range pcs_p pcs_b pcs_e counter_sfirst counter_send →
    contiguous_between ais_counter counter_sfirst counter_send →

    spec_ctx 
    (* Code of the preambles *)
    ∗ counter_left_preamble f_m offset_to_counter ai
    ∗ counter_right_preamble f_m offset_to_counter ais

    (* Code of the counter examples themselves *)
    ∗ counter_left ai_counter
    ∗ counter_right ais_counter

    (** Resources for malloc and assert **)
    (* assume that a pointer to the linking table (where the malloc capa is) is at offset 0 of PC *)
    ∗ na_inv logrel_nais mallocN (malloc_inv_binary b_m e_m)
    ∗ pc_b ↦ₐ (WCap RO b_link e_link a_link)
    ∗ a_entry ↦ₐ (WCap E b_m e_m b_m)
    ∗ pcs_b ↣ₐ (WCap RO bs_link es_link s_link)
    ∗ s_entry ↣ₐ (WCap E b_m e_m b_m)

    -∗
    interp_expr interp r (WCap pc_p pc_b pc_e a_first,WCap pcs_p pcs_b pcs_e s_first).
  Proof.
    rewrite /interp_expr /=.
    iIntros (Hvpc Hvpc' Hcont Hcont' Hwb_malloc Ha_entry Hwb_malloc' Hs_entry
                  Ha_lea H_counter_offset Hvpc_counter Hcont_counter
                  Ha_lea' H_counter_offset' Hvpc_counter'). iIntros (Hcont_counter').
    iIntros "(#Hspec & Hprog & Hsprog & Hcounter & Hscounter & #Hinv_malloc & Hpc_b & Ha_entry & Hpcs_b & Hs_entry)
             ([#Hr_full #Hr_valid] & Hregs & Hsegs & HnaI & Hj)".
    iDestruct "Hr_full" as %Hr_full.
    rewrite /full_map.
    iSplitR; auto. rewrite /interp_conf.
    
    (* put the code for the counter example in an invariant *)
    (* we separate the invariants into its tree functions *)
    iDestruct (contiguous_between_program_split with "Hcounter") as (incr_prog restc linkc)
                                                                   "(Hincr & Hread & #Hcont)";[apply Hcont_counter|].
    iDestruct "Hcont" as %(Hcont_incr & Hcont_restc & Heqappc & Hlinkrestc).
    iDestruct (contiguous_between_program_split with "Hscounter") as (decr_prog restc' linkc')
                                                                   "(Hdecr & Hreadneg & #Hcont)";[apply Hcont_counter'|].
    iDestruct "Hcont" as %(Hcont_decr & Hcont_restc' & Heqappc' & Hlinkrestc').
    iDestruct (big_sepL2_length with "Hincr") as %incr_length.
    iDestruct (big_sepL2_length with "Hread") as %read_length.
    iDestruct (big_sepL2_length with "Hdecr") as %decr_length.
    iDestruct (big_sepL2_length with "Hreadneg") as %readneg_length.

    iCombine "Hincr" "Hdecr" as "Hincr".
    iCombine "Hread" "Hreadneg" as "Hread". 
    
    iDestruct (na_inv_alloc logrel_nais _ count_incrN with "Hincr") as ">#Hincr".
    iDestruct (na_inv_alloc logrel_nais _ count_readN with "Hread") as ">#Hread".
    
    rewrite /registers_mapsto /spec_registers_mapsto.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]".
      by rewrite lookup_insert //. rewrite delete_insert_delete //.
    iDestruct (big_sepM_delete _ _ PC with "Hsegs") as "[HsPC Hsegs]".
      by rewrite lookup_insert //. rewrite delete_insert_delete //.
    destruct (Hr_full r_t0) as [ [r0 Hr0] [s0 Hs0] ].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr0 Hregs]". by rewrite !lookup_delete_ne//.
    iDestruct (big_sepM_delete _ _ r_t0 with "Hsegs") as "[Hs0 Hsegs]". by rewrite !lookup_delete_ne//.
    assert (∀ x : RegName, is_Some (r.1 !! x)) as Hr'_full_left;[intros x; destruct Hr_full with x;eauto|].
    assert (∀ x : RegName, is_Some (r.2 !! x)) as Hr'_full_right;[intros x; destruct Hr_full with x;eauto|]. 
    pose proof (regmap_full_dom _ Hr'_full_left) as Hdom_r'.
    pose proof (regmap_full_dom _ Hr'_full_right) as Hdom_s'.
    
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    iDestruct (big_sepL2_length with "Hsprog") as %Hslength.
    
    assert (pc_p ≠ E).
    { eapply isCorrectPC_range_perm_non_E. eapply Hvpc.
      pose proof (contiguous_between_length _ _ _ Hcont) as HH. rewrite Hlength /= in HH.
      revert HH; clear; solve_addr. }

    assert (pcs_p ≠ E).
    { eapply isCorrectPC_range_perm_non_E. eapply Hvpc'.
      pose proof (contiguous_between_length _ _ _ Hcont') as HH. rewrite Hslength /= in HH.
      revert HH; clear; solve_addr. }
    
    (* malloc 1 *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_malloc ai_rest a_malloc_end) "(Hmalloc & Hprog & #Hcont)"; [apply Hcont|].
    iDestruct "Hcont" as %(Hcont_malloc & Hcont_rest & Heqapp & Hlink).
    iDestruct (contiguous_between_program_split with "Hsprog") as
        (ais_malloc ais_rest as_malloc_end) "(Hsmalloc & Hsprog & #Hcont)"; [apply Hcont'|].
    iDestruct "Hcont" as %(Hcont_smalloc & Hcont_srest & Heqapp' & Hlink').
    
    iDestruct (big_sepL2_length with "Hmalloc") as %Hai_malloc_len.
    iDestruct (big_sepL2_length with "Hsmalloc") as %Hais_malloc_len.
    
    assert (isCorrectPC_range pc_p pc_b pc_e a_first a_malloc_end) as Hvpc1.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest). clear; solve_addr. }
    assert (isCorrectPC_range pc_p pc_b pc_e a_malloc_end a_end) as Hvpc2.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_malloc). clear; solve_addr. }
    assert (isCorrectPC_range pcs_p pcs_b pcs_e s_first as_malloc_end) as Hvpc1'.
    { eapply isCorrectPC_range_restrict. apply Hvpc'.
      generalize (contiguous_between_bounds _ _ _ Hcont_srest). clear; solve_addr. }
    assert (isCorrectPC_range pcs_p pcs_b pcs_e as_malloc_end s_end) as Hvpc2'.
    { eapply isCorrectPC_range_restrict. apply Hvpc'.
      generalize (contiguous_between_bounds _ _ _ Hcont_smalloc). clear; solve_addr. }
    
    rewrite - !/(malloc _ _ _).
    iApply (wp_wand with "[-]").
    iApply (malloc_s_spec with "[- $Hspec $Hj $HPC $HsPC $Hmalloc $Hsmalloc $Hpc_b $Hpcs_b $Ha_entry $Hs_entry $Hr0 $Hs0 $Hregs $Hsegs $Hinv_malloc $HnaI]");
      [apply Hvpc1|apply Hvpc1'|eapply Hcont_malloc|eapply Hcont_smalloc|eapply Hwb_malloc|eapply Ha_entry|eapply Hwb_malloc'|eapply Hs_entry|auto..].
    { rewrite !dom_delete_L Hdom_r' difference_difference_L //. }
    { rewrite !dom_delete_L Hdom_s' difference_difference_L //. }
    iNext. iIntros "(Hj & HPC & HsPC & Hmalloc & Hsmalloc & Hpc_b & Hpcs_b & Ha_entry & Hs_entry & HH & Hr0 & Hs0 & HnaI & Hregs & Hsegs)".
    iDestruct "HH" as (b_cell e_cell Hbe_cell) "(Hr1 & Hs1 & Hcell & Hscell)".
    iDestruct (region_mapsto_single with "Hcell") as (cellv) "(Hcell & _)". revert Hbe_cell; clear; solve_addr.
    iDestruct (region_mapsto_single_spec with "Hscell") as (cellv') "(Hscell & _)". revert Hbe_cell; clear; solve_addr.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    iDestruct (big_sepL2_length with "Hsprog") as %Hlength_srest.
    2: { iIntros (?) "[HH | ->]". iApply "HH". iIntros (Hv). inversion Hv. }
    
    destruct ai_rest as [| a l]; [by inversion Hlength|].
    destruct ais_rest as [| a' l']; [by inversion Hslength|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest) as ->.
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_srest) as ->.
    (* store_z r_t1 0 *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    destruct l' as [| ? l']; [by inversion Hlength_srest|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_store_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hs1 $Hsi $Hscell]")
      as "(Hj & HsPC & Hsprog_done & Hs1 & Hb_scell)";
      [apply decode_encode_instrW_inv|iCorrectPC as_malloc_end s_end|
       iContiguous_next Hcont_srest 0|auto..].
    { split; auto. apply le_addr_withinBounds; revert Hbe_cell; clear; solve_addr. }
    iApply (wp_store_success_z with "[$HPC $Hr1 $Hi $Hcell]");
      [apply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|
       iContiguous_next Hcont_rest 0|..].
    { auto. }
    { apply le_addr_withinBounds; revert Hbe_cell; clear; solve_addr. }
    iEpilogue_both "(HPC & Hprog_done & Hr1 & Hb_cell)".
    iCombine "Hprog_done" "Hmalloc" as "Hprog_done". iCombine "Hsprog_done" "Hsmalloc" as "Hsprog_done".
    (* move_r r_t2 r_t1 *)
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr2 Hregs]".
      by rewrite lookup_insert. rewrite delete_insert_delete.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hsegs") as "[Hs2 Hsegs]".
      by rewrite lookup_insert. rewrite delete_insert_delete.
    destruct l as [| a_move' l]; [by inversion Hlength_rest|]. destruct l' as [| as_move' l']; [by inversion Hlength_srest|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] _ _ _ _ _ _ r_t2 _ r_t1 with "[$Hspec $Hj $HsPC $Hsi $Hs1 $Hs2]")
      as "(Hj & HsPC & Hsi & Hs2 & Hs1)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_malloc_end s_end|iContiguous_next Hcont_srest 1|auto..].
    iApply (wp_move_success_reg _ _ _ _ _ _ _ r_t2 _ r_t1 with "[$HPC $Hi $Hr1 $Hr2]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 1|..].
    iEpilogue_both "(HPC & Hi & Hr2 & Hr1)". iCombinePtrn. 
    (* move_r r_t1 PC *)
    destruct l as [| ? l]; [by inversion Hlength_rest|]. destruct l' as [| ? l']; [by inversion Hlength_srest|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs1]")
      as "(Hj & HsPC & Hsi & Hs1)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_malloc_end s_end|iContiguous_next Hcont_srest 2|auto..].
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 2|..].
    iEpilogue_both "(HPC & Hi & Hr1)". iCombinePtrn. 
    (* move_r r_t8 r_t2 *)
    destruct Hr_full with r_t8 as [ [? Hrt8] [? Hst8] ].
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]".
    { rewrite lookup_delete_ne;[|by auto]. rewrite !lookup_insert_ne;auto; rewrite !lookup_delete_ne;auto. eauto. }
    iDestruct (big_sepM_delete _ _ r_t8 with "Hsegs") as "[Hr_s8 Hsegs]".
    { rewrite lookup_delete_ne;[|by auto]. rewrite !lookup_insert_ne;auto; rewrite !lookup_delete_ne;auto. eauto. }
    destruct l as [| ? l]; [by inversion Hlength_rest|]. destruct l' as [| ? l']; [by inversion Hlength_srest|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hr_s8 $Hs2]")
      as "(Hj & HsPC & Hsi & Hs_t8 & Hs2)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_malloc_end s_end|iContiguous_next Hcont_srest 3|auto..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t8 $Hr2]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 3|..].
    iEpilogue_both "(HPC & Hi & Hr_t8 & Hr2)". iCombinePtrn. 
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hsegs $Hs_t8]") as "Hsegs";[apply lookup_delete|rewrite insert_delete].
    (* move_r r_t9 r_t1 *)
    destruct Hr_full with r_t9 as [ [? Hrt9] [? Hst9] ].
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t8 Hregs]".
    { rewrite lookup_insert_ne;[|by auto]. rewrite lookup_delete_ne;auto. rewrite !lookup_insert_ne;auto; rewrite !lookup_delete_ne;auto. eauto. }
    iDestruct (big_sepM_delete _ _ r_t9 with "Hsegs") as "[Hs_t8 Hsegs]".
    { rewrite lookup_insert_ne;[|by auto]. rewrite lookup_delete_ne;auto. rewrite !lookup_insert_ne;auto; rewrite !lookup_delete_ne;auto. eauto. }
    destruct l as [| ? l]; [by inversion Hlength_rest|]. destruct l' as [| ? l']; [by inversion Hlength_srest|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t8 $Hs1]")
      as "(Hj & HsPC & Hsi & Hs_t8 & Hs1)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_malloc_end s_end|iContiguous_next Hcont_srest 4|auto..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t8 $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 4|..].
    iEpilogue_both "(HPC & Hi & Hr_t8 & Hr1)". iCombinePtrn. 
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hsegs $Hs_t8]") as "Hsegs";[apply lookup_delete|rewrite insert_delete].

    (* lea_z r_t1 offset_to_awkward *)
    
    assert (a_move' = a_move) as ->.
    { assert ((a_first + (length ai_malloc + 2))%a = Some a_move') as HH.
      { rewrite Hai_malloc_len /= in Hlink |- *.
        generalize (contiguous_between_incr_addr_middle _ _ _ 0 2 _ _ Hcont_rest eq_refl eq_refl).
        revert Hlink; clear; solve_addr. }
      revert HH Ha_lea. rewrite Hai_malloc_len. cbn. clear.
      unfold counter_preamble_move_offset. solve_addr. }
    assert (as_move' = s_move) as ->.
    { assert ((s_first + (length ais_malloc + 2))%a = Some as_move') as HH.
      { rewrite Hais_malloc_len /= in Hlink' |- *.
        generalize (contiguous_between_incr_addr_middle _ _ _ 0 2 _ _ Hcont_srest eq_refl eq_refl).
        revert Hlink'; clear; solve_addr. }
      revert HH Ha_lea'. rewrite Hais_malloc_len. cbn. clear.
      unfold counter_preamble_move_offset. solve_addr. }
    
    destruct l as [| ? l]; [by inversion Hlength_rest|]. destruct l' as [| ? l']; [by inversion Hlength_srest|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_lea_success_z _ [SeqCtx] _ _ _ _ _ _ _ _ _ _ _ _ counter_sfirst with "[$Hspec $Hj $HsPC $Hsi $Hs1]")
      as "(Hj & HsPC & Hsi & Hs1)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_malloc_end s_end|iContiguous_next Hcont_srest 5
       |assumption|done|auto..].
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ counter_first with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 5
       |assumption|done|..].
    (* { destruct (isCorrectPC_range_perm _ _ _ _ _ _ Hvpc) as [-> | [-> | ->] ]; auto. *)
    (*   generalize (contiguous_between_middle_bounds _ (length ai_malloc) a_malloc_end _ _ Hcont ltac:(subst ai; rewrite list_lookup_middle; auto)). clear. solve_addr. } *)
    iEpilogue_both "(HPC & Hi & Hr1)". iCombinePtrn. 
    (* crtcls *)
    
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls ai_rest a_crtcls_end) "(Hcrtcls & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 6%nat _ _ _ Hcont_rest eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_;_;_]). 2: eapply Hcont_rest.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls & Hcont_rest1 & Heqapp1 & Hlink1).
    iDestruct (contiguous_between_program_split with "Hsprog") as
        (ais_crtcls ais_rest as_crtcls_end) "(Hscrtcls & Hsprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 6%nat _ _ _ Hcont_srest eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_;_;_]). 2: eapply Hcont_srest.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_scrtcls & Hcont_rest1' & Heqapp1' & Hlink1').
    
    assert (a_malloc_end <= a7)%a as Ha1_after_malloc.
    { eapply contiguous_between_middle_bounds'. apply Hcont_rest. repeat constructor. }
    assert (as_malloc_end <= a8)%a as Ha1_after_malloc'.
    { eapply contiguous_between_middle_bounds'. apply Hcont_srest. repeat constructor. }
    
    iApply (wp_wand with "[-]").
    iApply (crtcls_spec with "[- $Hspec $Hj $HPC $HsPC $Hcrtcls $Hscrtcls $Hpc_b $Hpcs_b $Ha_entry $Hs_entry $Hr0 $Hs0 $Hregs $Hsegs $Hr1 $Hs1 $Hr2 $Hs2 $HnaI $Hinv_malloc]");
      [| |apply Hcont_crtcls|apply Hcont_scrtcls|apply Hwb_malloc|apply Ha_entry|apply Hwb_malloc'|apply Hs_entry| | |done|auto|..].
    { eapply isCorrectPC_range_restrict. apply Hvpc2. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest1. }
    { eapply isCorrectPC_range_restrict. apply Hvpc2'. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest1'. }
    { rewrite !dom_insert_L dom_delete_L !dom_insert_L !dom_delete_L Hdom_r'.
      clear. set_solver-. }
    { rewrite !dom_insert_L dom_delete_L !dom_insert_L !dom_delete_L Hdom_s'.
      clear. set_solver-. }
    2: { iIntros (?) "[ H | -> ]". iApply "H". iIntros (HC). congruence. }
    iNext. iIntros "(Hj & HPC & Hcrtcls & HsPC & Hscrtcls & Hpc_b & Hpcs_b & Ha_entry & Hs_entry & HH)".
    iDestruct "HH" as (b_cls e_cls Hbe_cls) "(Hr1 & Hs1 & Hbe_cls & Hbes_cls & Hr0 & Hs0 & Hr2 & Hs2 & HnaI & Hregs & Hsegs)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest1.
    iDestruct (big_sepL2_length with "Hsprog") as %Hlength_rest1'.

    (* register map cleanup *)
    
    assert (forall (r : gmap RegName Word) w1 w2, <[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]> (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> (<[r_t7:=WInt 0%Z]>
                  (<[r_t9:=w1]> (<[r_t8:=w2]>
                  (delete r_t2 (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]> (<[r_t5:=WInt 0%Z]> (delete r_t1 (delete r_t0 (delete PC r))))))))))))) =
                 <[r_t9:=w1]> (<[r_t8:=w2]> (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]>
                  (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> (<[r_t7:=WInt 0%Z]> (delete r_t2 (delete r_t1 (delete r_t0 (delete PC r))))))))))
           ) as Heqregs1. 
    { clear. intros r w1 w2. set (regs := <[r_t9:=w1]> (<[r_t8:=w2]>
                                     (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]> (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> (<[r_t7:=WInt 0%Z]>
                                       (delete r_t2 (delete r_t1 (delete r_t0 (delete PC r))))))))))). 
      rewrite !delete_insert_ne;auto.
      repeat (rewrite (insert_commute _ r_t3);[|by auto]). rewrite insert_insert. 
      repeat (rewrite (insert_commute _ r_t4);[|by auto]). rewrite insert_insert.
      repeat (rewrite (insert_commute _ r_t5);[|by auto]). rewrite insert_insert. 
      repeat (rewrite (insert_commute _ r_t6);[|by auto]). repeat (rewrite (insert_commute _ r_t7);[|by auto]).
      auto.       
    }
    
    rewrite (Heqregs1 r.1). rewrite (Heqregs1 r.2). 
    
    assert (isCorrectPC_range pc_p pc_b pc_e a_crtcls_end a_end) as Hvpc3. 
    { eapply isCorrectPC_range_restrict. apply Hvpc2.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest1).
      revert Ha1_after_malloc Hlink1. clear; solve_addr. }
    assert (isCorrectPC_range pcs_p pcs_b pcs_e as_crtcls_end s_end) as Hvpc3'. 
    { eapply isCorrectPC_range_restrict. apply Hvpc2'.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest1').
      revert Ha1_after_malloc' Hlink1'. clear; solve_addr. }

    (* move r_t10 r_t1 *)
    destruct Hr_full with r_t10 as [ [? Hrt10] [? Hst10] ].
    iDestruct (big_sepM_delete _ _ r_t10 with "Hregs") as "[Hr_t10 Hregs]".
    { rewrite !lookup_insert_ne;auto. rewrite !lookup_delete_ne;auto. eauto. }
    iDestruct (big_sepM_delete _ _ r_t10 with "Hsegs") as "[Hs_t10 Hsegs]".
    { rewrite !lookup_insert_ne;auto. rewrite !lookup_delete_ne;auto. eauto. }
    
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest1|].
    destruct ais_rest as [| ? ais_rest]; [by inversion Hlength_rest1'|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest1) as ->.
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest1') as ->.
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest1|].
    destruct ais_rest as [| ? ais_rest]; [by inversion Hlength_rest1'|].
    
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t10 $Hs1]")
      as "(Hj & HsPC & Hsi & Hs_t10 & Hs1)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_crtcls_end s_end|iContiguous_next Hcont_rest1' 0|auto..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t10 $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end a_end|iContiguous_next Hcont_rest1 0|..].
    iEpilogue_both "(HPC & Hi & Hr_t10 & Hr1)". iCombinePtrn. 
    iDestruct (big_sepM_insert _ _ r_t10 with "[$Hregs $Hr_t10]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert _ _ r_t10 with "[$Hsegs $Hs_t10]") as "Hsegs";[apply lookup_delete|rewrite insert_delete].
    (* move r_t2 r_t8 *)
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]".
    { rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert. eauto. }
    iDestruct (big_sepM_delete _ _ r_t8 with "Hsegs") as "[Hs_t8 Hsegs]".
    { rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert. eauto. }
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest1|]. destruct ais_rest as [| ? ais_rest]; [by inversion Hlength_rest1'|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2 $Hs_t8]")
      as "(Hj & HsPC & Hsi & Hs2 & Hs_t8)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_crtcls_end s_end|iContiguous_next Hcont_rest1' 1|auto..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr2 $Hr_t8]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end a_end|iContiguous_next Hcont_rest1 1|..].
    iEpilogue_both "(HPC & Hi & Hr2 & Hr_t8)". iCombinePtrn. 
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|].
    rewrite insert_delete (insert_commute _ r_t8 r_t10) // (insert_commute _ r_t8 r_t9)// insert_insert.
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hsegs $Hs_t8]") as "Hsegs";[apply lookup_delete|].
    rewrite insert_delete (insert_commute _ r_t8 r_t10)// (insert_commute _ r_t8 r_t9)// insert_insert.
    (* move r_t1 r_t9 *)
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t9 Hregs]";[rewrite lookup_insert_ne// lookup_insert;eauto|].
    iDestruct (big_sepM_delete _ _ r_t9 with "Hsegs") as "[Hs_t9 Hsegs]";[rewrite lookup_insert_ne// lookup_insert;eauto|].
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest1|]. destruct ais_rest as [| ? ais_rest]; [by inversion Hlength_rest1'|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs1 $Hs_t9]")
      as "(Hj & HsPC & Hsi & Hs1 & Hs_t9)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_crtcls_end s_end|iContiguous_next Hcont_rest1' 2|auto..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr1 $Hr_t9]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end a_end|iContiguous_next Hcont_rest1 2|..].
    iEpilogue_both "(HPC & Hi & Hr1 & Hr_t9)". iCombinePtrn.
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t9]") as "Hregs";[apply lookup_delete|rewrite insert_delete !(insert_commute _ _ r_t9)// insert_insert].
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hsegs $Hs_t9]") as "Hsegs";[apply lookup_delete|rewrite insert_delete insert_insert].
    (* lea r_t1 offset_to_counter + length incr_instrs *)
    assert ((a_move + (offset_to_counter + (length incr_instrs)))%a = Some linkc) as H_counter_offset1.
    { revert Hlinkrestc H_counter_offset incr_length. clear. intros. solve_addr. }
    assert ((s_move + (offset_to_counter + (length decr_instrs)))%a = Some linkc') as H_counter_offset1'.
    { revert Hlinkrestc' H_counter_offset' decr_length. clear. intros. solve_addr. }
    destruct ai_rest as [| ? ai_rest]; [by inversion Hlength_rest1|]. destruct ais_rest as [| ? ais_rest]; [by inversion Hlength_rest1'|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_lea_success_z _ [SeqCtx] _ _ _ _ _ _ _ _ _ _ _ _ linkc' with "[$Hspec $Hj $HsPC $Hsi $Hs1]")
      as "(Hj & HsPC & Hsi & Hs1)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_crtcls_end s_end|iContiguous_next Hcont_rest1' 3|assumption|done|auto..].
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ linkc with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end a_end|iContiguous_next Hcont_rest1 3|assumption|done|..].
    iEpilogue_both "(HPC & Hi & Hr1)". iCombinePtrn. 

    (* crtcls *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls' ai_rest' a_crtcls_end') "(Hcrtcls' & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 4%nat _ _ _ Hcont_rest1 eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_]). 2: eapply Hcont_rest1.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls2 & Hcont_rest2 & Heqapp2 & Hlink2).
    
    iDestruct (contiguous_between_program_split with "Hsprog") as
        (ais_crtcls' ais_rest' as_crtcls_end') "(Hscrtcls' & Hsprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 4%nat _ _ _ Hcont_rest1' eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_]). 2: eapply Hcont_rest1'.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls2' & Hcont_rest2' & Heqapp2' & Hlink2').
    
    assert (a_crtcls_end <= a15)%a as Ha1_after_crtcls.
    { eapply contiguous_between_middle_bounds'. apply Hcont_rest1. repeat constructor. }
    assert (as_crtcls_end <= a16)%a as Ha1_after_crtcls'.
    { eapply contiguous_between_middle_bounds'. apply Hcont_rest1'. repeat constructor. }
    
    iApply (wp_wand with "[-]").
    iApply (crtcls_spec with "[- $Hspec $Hj $HPC $HsPC $Hcrtcls' $Hscrtcls' $Hpc_b $Hpcs_b $Ha_entry $Hs_entry $Hr0 $Hs0 $Hregs $Hsegs $Hr1 $Hs1 $Hr2 $Hs2 $HnaI $Hinv_malloc]");
      [| |apply Hcont_crtcls2|apply Hcont_crtcls2'|apply Hwb_malloc|apply Ha_entry|apply Hwb_malloc'|apply Hs_entry| | |auto|done|auto..].
    { eapply isCorrectPC_range_restrict. apply Hvpc3. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest2. }
    { eapply isCorrectPC_range_restrict. apply Hvpc3'. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest2'. }
    { rewrite !dom_insert_L !dom_delete_L Hdom_r'. clear. set_solver-. }
    { rewrite !dom_insert_L !dom_delete_L Hdom_s'. clear. set_solver-. }
    2: { iIntros (?) "[ H | -> ]". iApply "H". iIntros (HC). congruence. }
    iNext. iIntros "(Hj & HPC & Hcrtcls' & HsPC & Hscrtcls' & Hpc_b & Hpcs_b & Ha_entry & Hs_entry & HH)".
    iDestruct "HH" as (b_cls' e_cls' Hbe_cls') "(Hr1 & Hs1 & Hbe_cls' & Hbes_cls' & Hr0 & Hs0 & Hr2 & Hs2 & HnaI & Hregs & Hsegs)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest2.
    iDestruct (big_sepL2_length with "Hsprog") as %Hlength_rest2'.
    (* register map cleanup *)
    do 2 (repeat (rewrite (insert_commute _ _ r_t7);[|by auto]);rewrite insert_insert).
    do 2 (repeat (rewrite (insert_commute _ _ r_t6);[|by auto]);rewrite insert_insert). 
    do 2 (repeat (rewrite (insert_commute _ _ r_t5);[|by auto]);rewrite insert_insert).
    do 2 (repeat (rewrite (insert_commute _ _ r_t4);[|by auto]);rewrite insert_insert).
    do 2 (repeat (rewrite (insert_commute _ _ r_t3);[|by auto]);rewrite insert_insert). 

    (* FINAL CLEANUP BEFORE RETURN *)
    assert (isCorrectPC_range pc_p pc_b pc_e a_crtcls_end' a_end) as Hvpc4. 
    { eapply isCorrectPC_range_restrict. apply Hvpc3.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest2).
      revert Ha1_after_malloc Ha1_after_crtcls Hlink2 Hlink1. clear; solve_addr. }
    assert (isCorrectPC_range pcs_p pcs_b pcs_e as_crtcls_end' s_end) as Hvpc4'. 
    { eapply isCorrectPC_range_restrict. apply Hvpc3'.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest2').
      revert Ha1_after_malloc' Ha1_after_crtcls' Hlink2' Hlink1'. clear; solve_addr. }

    (* move r_t2 r_t10 *)
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest2|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest2) as ->.
    destruct ais_rest' as [| ? ais_rest']; [by inversion Hlength_rest2'|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest2') as ->.
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest2|].
    destruct ais_rest' as [| ? ais_rest']; [by inversion Hlength_rest2'|].
    iPrologue_both "Hprog" "Hsprog".
    rewrite !(insert_commute _ _ r_t10);auto. 
    iDestruct (big_sepM_delete _ _ r_t10 with "Hregs") as "[Hr_t10 Hregs]";[apply lookup_insert|].
    iDestruct (big_sepM_delete _ _ r_t10 with "Hsegs") as "[Hs_t10 Hsegs]";[apply lookup_insert|]. 
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs2 $Hs_t10]")
      as "(Hj & HsPC & Hsi & Hs2 & Hs_t10)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_crtcls_end' s_end|iContiguous_next Hcont_rest2' 0|auto..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr2 $Hr_t10]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|iContiguous_next Hcont_rest2 0|..].
    iEpilogue_both "(HPC & Hi & Hr2 & Hr_t10)". iCombinePtrn. 
    (* move r_t10 0 *)
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest2|]. destruct ais_rest' as [| ? ais_rest']; [by inversion Hlength_rest2'|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t10]")
      as "(Hj & HsPC & Hsi & Hs_t10)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_crtcls_end' s_end|iContiguous_next Hcont_rest2' 1|auto..].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t10]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|iContiguous_next Hcont_rest2 1|..].
    iEpilogue_both "(HPC & Hi & Hr_t10)". iCombinePtrn. 
    iDestruct (big_sepM_insert _ _ r_t10 with "[$Hregs $Hr_t10]") as "Hregs";[apply lookup_delete|rewrite insert_delete insert_insert].
    iDestruct (big_sepM_insert _ _ r_t10 with "[$Hsegs $Hs_t10]") as "Hsegs";[apply lookup_delete|rewrite insert_delete insert_insert].
    (* move r_t8 0 *)
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]". 
    { repeat (rewrite lookup_insert_ne;[|by auto]). apply lookup_insert. }
    iDestruct (big_sepM_delete _ _ r_t8 with "Hsegs") as "[Hs_t8 Hsegs]". 
    { repeat (rewrite lookup_insert_ne;[|by auto]). apply lookup_insert. }
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest2|]. destruct ais_rest' as [| ? ais_rest']; [by inversion Hlength_rest2'|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t8]")
      as "(Hj & HsPC & Hsi & Hs_t8)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_crtcls_end' s_end|iContiguous_next Hcont_rest2' 2|auto..].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t8]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|iContiguous_next Hcont_rest2 2|..].
    iEpilogue_both "(HPC & Hi & Hr_t8)". iCombinePtrn.
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hsegs $Hs_t8]") as "Hsegs";[apply lookup_delete|rewrite insert_delete].
    (* move r_t9 0 *)
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t9 Hregs]". 
    { repeat (rewrite lookup_insert_ne;[|by auto]). apply lookup_insert. }
    iDestruct (big_sepM_delete _ _ r_t9 with "Hsegs") as "[Hs_t9 Hsegs]". 
    { repeat (rewrite lookup_insert_ne;[|by auto]). apply lookup_insert. }
    destruct ai_rest' as [| ? ai_rest']; [by inversion Hlength_rest2|]. destruct ais_rest' as [| ? ais_rest']; [by inversion Hlength_rest2'|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t9]")
      as "(Hj & HsPC & Hsi & Hs_t9)";
      [eapply decode_encode_instrW_inv|iCorrectPC as_crtcls_end' s_end|iContiguous_next Hcont_rest2' 3|auto..].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t9]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|iContiguous_next Hcont_rest2 3|..].
    iEpilogue_both "(HPC & Hi & Hr_t9)". iCombinePtrn.
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t9]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hsegs $Hs_t9]") as "Hsegs";[apply lookup_delete|rewrite insert_delete].
    
    (* WE WILL NOW PREPARE THΕ JUMP *)
    iCombine "Hbes_cls" "Hbes_cls'" as "Hbes_cls".
    iCombine "Hbe_cls'" "Hbes_cls" as "Hbe_cls'". 
    iCombine "Hbe_cls" "Hbe_cls'" as "Hbe_cls".
    iDestruct (na_inv_alloc logrel_nais _ count_clsN with "Hbe_cls") as ">#Hcls_inv".
    
    (* in preparation of jumping, we allocate the counter invariant *)
    (* in this closure creation, the two programs have the same address as the counter. This is not necessary however! *)
    iDestruct (inv_alloc countN _ (counter_inv b_cell b_cell) with "[Hb_cell Hb_scell]") as ">#Hcounter_inv".
    { iNext. rewrite /counter_inv. iExists 0. assert ((- 0%nat)%Z = 0)%Z as ->;[clear;lia|]. iFrame. }
    (* we also allocate a non atomic invariant for the environment table *)
    (* iMod (na_inv_alloc logrel_nais _ count_env *)
    (*                    (pc_b ↦ₐ WCap (RO,b_link,e_link,a_link) ∗ a_entry' ↦ₐ fail_cap)%I *)
    (*         with "[$Ha_entry' $Hpc_b]") as "#Henv". *)

    (* jmp *)
    destruct ai_rest' as [| ? ai_rest']; [|by inversion Hlength_rest2]. destruct ais_rest' as [| ? ais_rest']; [|by inversion Hlength_rest2'].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs0]")
      as "(Hj & HsPC & Hsi & Hs0)";
      [apply decode_encode_instrW_inv|iCorrectPC as_crtcls_end' s_end|auto..].
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply decode_encode_instrW_inv|iCorrectPC a_crtcls_end' a_end|..].
    
    (* the current state of registers is valid *)
    iAssert (interp (WCap E b_cls e_cls b_cls,WCap E b_cls e_cls b_cls))%I as "#Hvalid_cls".
    { iApply (incr_decr_closure_valid with "Hspec Hcounter_inv Hincr Hcls_inv");auto.
      apply Hvpc_counter. apply Hvpc_counter'. apply Hcont_restc. apply Hcont_restc'. solve_ndisj. }
    
    iAssert (interp (WCap E b_cls' e_cls' b_cls',WCap E b_cls' e_cls' b_cls'))%I as "#Hvalid_cls'".
    { iApply (read_read_neg_closure_valid with "Hspec Hcounter_inv Hread Hcls_inv");auto.
      apply Hcont_restc. apply Hcont_restc'. apply Hvpc_counter. apply Hvpc_counter'.
      apply Hcont_incr. apply Hcont_decr. solve_ndisj. }
    
    unshelve iPoseProof ("Hr_valid" $! r_t0 _) as "#Hr0_valid". done.
    rewrite /(RegLocate _ r_t0) /(RegLocate _ r_t0) Hr0 Hs0.
    
    (* either we fail, or we use the continuation in rt0 *)
    iDestruct (jmp_or_fail_spec with "Hspec Hr0_valid") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm r0))). 
    2 : { iEpilogue_both "(HPC & Hi & Hr0)". iApply "Hcont". iFrame "HPC". iIntros (Hcontr);done. }
    iDestruct "Hcont" as (p b e ? Heq) "#Hcont". 
    simplify_eq. 
    
    (* prepare the continuation *)
    iEpilogue_both "(HPC & Hi & Hr0)". iCombinePtrn. 
    
    (* Put the registers back in the map *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete //. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr0]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne // lookup_delete //. }
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). do 2 rewrite lookup_delete_ne //.
      apply lookup_delete. }
    iDestruct (big_sepM_insert with "[$Hsegs $Hs2]") as "Hsegs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete //. }
    iDestruct (big_sepM_insert with "[$Hsegs $Hs1]") as "Hsegs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete. }
    iDestruct (big_sepM_insert with "[$Hsegs $Hs0]") as "Hsegs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne // lookup_delete //. }
    iDestruct (big_sepM_insert with "[$Hsegs $HsPC]") as "Hsegs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). do 2 rewrite lookup_delete_ne //.
      apply lookup_delete. }
    
    do 2 (repeat (rewrite -(delete_insert_ne _ r_t2) //;[]);rewrite insert_delete).
    do 2 (repeat (rewrite -(delete_insert_ne _ r_t1) //;[]);rewrite insert_delete).
    do 2 (repeat (rewrite -(delete_insert_ne _ r_t0) //;[]);rewrite insert_delete).
    do 2 (repeat (rewrite -(delete_insert_ne _ PC) //;[]);rewrite insert_delete).
       
    rewrite -(insert_insert _ PC (updatePcPerm s0) (WInt 0%Z))  -(insert_insert _ PC _ (WInt 0%Z)).
    
    match goal with |- context [ ([∗ map] k↦y ∈ <[PC:=_]> ?r, _)%I ] => set r'' := r end.
    match goal with |- context [ ([∗ map] k↦y ∈ <[PC:=updatePcPerm s0]> ?r, _)%I ] => set s'' := r end.
    iDestruct (interp_eq with "Hr0_valid") as %<-.
    iAssert (full_map (r'',s'')) as %Hr''_full.
    { rewrite /full_map. iIntros (rr). iPureIntro. split.
      - rewrite elem_of_gmap_dom /r''.
        rewrite !dom_insert_L regmap_full_dom //.
        generalize (all_registers_s_correct rr). clear; set_solver.
      - rewrite elem_of_gmap_dom /s''.
        rewrite !dom_insert_L regmap_full_dom //.
        generalize (all_registers_s_correct rr). clear; set_solver. }
    iSpecialize ("Hcont" $! (r'',s'') with "[$Hj $Hregs $Hsegs $HnaI]").
    { rewrite /interp_reg. iSplit; [iPureIntro; apply Hr''_full|].
      iIntros (rr Hrr). simpl. rewrite /RegLocate /r'' /s''.
      consider_next_reg_both rr PC. done. consider_next_reg_both rr r_t0. consider_next_reg_both rr r_t1.
      consider_next_reg_both rr r_t2.
      repeat (
      match goal with |- context [ <[?r := _]> _ ] =>
                      consider_next_reg_both rr r; [by rewrite (fixpoint_interp1_eq (WInt 0%Z, WInt 0%Z))|]
      end ). 
      
      consider_next_reg_both rr r_t9. congruence.
      consider_next_reg_both rr r_t8. congruence.
      unshelve iSpecialize ("Hr_valid" $! rr _); auto. 
    }
    (* apply the continuation *)
    iDestruct "Hcont" as "[_ Hcallback_now]".
    iApply wp_wand_l. iFrame "Hcallback_now".
    iIntros (v) "Hφ". iIntros (Hne).
    iDestruct ("Hφ" $! Hne) as (r0) "(Hfull & Hregs & Hna)".
    iExists r0. iFrame.
  Qed.


End counter_example_preamble.
