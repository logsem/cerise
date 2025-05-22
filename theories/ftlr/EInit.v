From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base sorting.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_EInit.

(* TODO move *)
Lemma logical_range_map_insert (b e : Addr) (v : Version) (w w': LWord) (lw : list LWord) :
  (b < e)%a ->
  <[ (b,v) := w']> (logical_range_map b e (w::lw) v) = logical_range_map b e (w'::lw) v.
Proof.
  intros Hb.
  rewrite /logical_range_map.
  rewrite finz_seq_between_cons //.
  cbn.
  by rewrite insert_insert.
Qed.

Lemma HdRel_zip_fst {A B} (R: A -> A -> bool) (a : A) (b : B) (la : list A) (lb : list B) :
  HdRel R a la ->
  (HdRel (pair_fst_leb R) (a,b) (zip la lb)).
Proof.
  generalize dependent lb.
  induction la as [|a' la]; intros lb Hsorted ;cbn in *; first done.
  - destruct lb; first done.
    apply HdRel_cons.
    apply HdRel_inv in Hsorted.
    by rewrite /pair_fst_leb.
Qed.

Lemma HdRel_merge_sort_cons {A} (R : A -> A -> bool) (a : A) (la : list A) :
  HdRel R a la -> merge_sort R (a::la) = a::(merge_sort R la).
Proof.
  generalize dependent a.
  induction la as [|a' la] ; intros a HdRel_a ; cbn in *; first done.
  rewrite /merge_sort_aux.
Admitted.


Lemma Sorted_sort_zip_fst {A B} (R : A -> A -> bool) (la : list A) (lb : list B) :
  Sorted R la ->
  (merge_sort (pair_fst_leb R) (zip la lb)) = (zip la lb).
Proof.
  generalize dependent lb.
  induction la as [|a la]; intros lb Hsorted ;cbn in *; first done.
  - destruct lb; first done.
    inversion Hsorted; simplify_eq.
    eapply (HdRel_zip_fst _ _ b _ lb) in H2.
    rewrite HdRel_merge_sort_cons; auto.
    rewrite IHla; auto.
Qed.

Lemma Sorted_sort_zip (la : list LAddr) (lw : list LWord) :
  Sorted laddr_leb la ->
  (merge_sort lmem_leb (zip la lw)) = (zip la lw).
Proof.
  intros Hsorted.
  by apply Sorted_sort_zip_fst.
Qed.

Lemma finz_seq_between_addr_StronglySorted_aux (a : Addr) (n : nat) :
  StronglySorted addr_leb (finz.seq_between (a^- (n))%f a).
Proof.
  induction n.
  - rewrite finz_add_0_default.
    rewrite finz_seq_between_empty; last solve_addr; apply SSorted_nil.
  - destruct (decide ( (a ^+ - S n)%a < a)%a); cycle 1.
    + rewrite finz_seq_between_empty; last solve_addr; apply SSorted_nil.
    + rewrite finz_seq_between_cons; last done.
    replace ( ((a ^+ - S n) ^+ 1)%a ) with (a ^+ - n)%a; last solve_finz.
    apply SSorted_cons; auto.
    apply Forall_forall.
    intros x Hx.
    apply elem_of_finz_seq_between in Hx.
    rewrite /addr_leb.
    rewrite Is_true_true.
    apply Z.leb_le.
    solve_finz.
Qed.

Lemma finz_seq_between_addr_StronglySorted (b e : Addr) :
  StronglySorted addr_leb (finz.seq_between b e).
Proof.
  destruct (decide (b < e))%a; cycle 1.
  - rewrite finz_seq_between_empty; last solve_addr; apply SSorted_nil.
  - assert (∃ n:nat, b = (e ^- n)%f) as [n ->].
    { admit. }
    apply finz_seq_between_addr_StronglySorted_aux.
Admitted.
Lemma finz_seq_between_laddr_Sorted (la : list Addr) v :
  Sorted addr_leb la
  -> Sorted laddr_leb ((λ a : Addr, (a, v)) <$> la).
Proof.
  apply Sorted_fmap.
  intros a1 a2 Ha. rewrite /laddr_leb /pair_fst_leb //=.
Qed.

Global Instance merge_sort_Permutation_proper
  {A} (R : relation A) `{Htotal: Total A R}
  `{Htransitive: Transitive A R}
  `{ AntiSymm A eq R }
  `{∀ x y, Decision (R x y)} :
  Proper (Permutation ==> eq) (merge_sort R).
Proof.
  rewrite /Proper /respectful.
  intros l1 l2 Hp.
  pose proof (Sorted_merge_sort R l1) as Hsorted1.
  pose proof (Sorted_merge_sort R l2) as Hsorted2.
  pose proof (merge_sort_Permutation R l1) as Hsort_l1.
  pose proof (merge_sort_Permutation R l2) as Hsort_l2.
  assert ( merge_sort R l1 ≡ₚ merge_sort R l2 ) as Hp'.
  { eapply Permutation_trans; eauto.
    eapply Permutation_trans; eauto.
    done.
  }
  eapply Sorted_unique in Hp'; eauto.
Qed.

Global Instance lmem_leb_total : Total lmem_leb.
Proof.
  intros aw1 aw2.
Admitted.

Global Instance lmem_leb_transitive : Transitive lmem_leb.
Proof.
  intros aw1 aw2 aw3 H12 H13.
  rewrite /lmem_leb /laddr_leb /= in H12,H13 |- *.
  cbn in *.
  rewrite /pair_fst_leb /addr_leb in H12,H13 |- *.
  destruct aw1 as [ [] ]
  ; destruct aw2 as [ [] ]
  ; destruct aw3 as [ [] ]
  ; cbn in *.
  rewrite !Is_true_true in H12,H13 |- *.
  rewrite !Z.leb_le in H12,H13 |- *.
  lia.
Qed.

Global Instance lmem_leb_AntiSymm : AntiSymm eq lmem_leb.
Proof.
  intros aw1 aw2.
Admitted.


Lemma word_to_lword_get_word_int (w : LWord) (v : Version) :
  is_zL w ->
  word_to_lword (lword_get_word w) v = w.
Proof.
  intros Hw.
  destruct w ; cbn in * ; done.
Qed.

Lemma otype_unification (ot1 ot2 : OType) (n : ENum) :
  tid_of_otype ot1 = Some n ->
  Z.even ot1 = true ->
  finz.of_z (2 * n) = Some ot2 ->
  ot1 = ot2.
Proof.
  intros Htidx Htidx_even Hot_ec.
  rewrite /tid_of_otype in Htidx.
  rewrite Htidx_even in Htidx.
  assert (n = (Z.to_nat ot1 `div` 2)) as -> by (by injection Htidx); clear Htidx.
  assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat ot1) 2)) = (Z.to_nat ot1) ).
  {
    rewrite -(Nat2Z.inj_mul 2).
    rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
    2:{
      destruct ot1.
      rewrite /Z.even in Htidx_even.
      cbn in *.
      destruct z; cbn in *.
      + rewrite Z2Nat.inj_0.
        apply PeanoNat.Nat.divide_0_r.
      + rewrite Z2Nat.inj_pos.
        destruct p; cbn in * ; try done.
        rewrite Pos2Nat.inj_xO.
        apply Nat.divide_factor_l.
      + rewrite Z2Nat.inj_neg.
        apply PeanoNat.Nat.divide_0_r.
    }
    rewrite PeanoNat.Nat.mul_comm.
    rewrite (PeanoNat.Nat.div_mul (Z.to_nat ot1) 2); done.
  }
  solve_addr.
Qed.

Lemma unique_in_registersL_twice
  (rcode rdata : RegName) (lregs : LReg)
  p b e a v
  p' b' e' a' v' :
  rcode ≠ rdata ->
  lregs !! rcode = Some (LCap p b e a v) ->
  lregs !! rdata = Some (LCap p' b' e' a' v') ->
  unique_in_registersL lregs (Some rcode) (LCap p b e a v) ->
  unique_in_registersL lregs (Some rdata) (LCap p' b' e' a' v') ->
  (finz.seq_between b e) ## (finz.seq_between b' e').
Proof.
  intros Hneq Hrcode Hrdata Hunique_code Hunique_data.
  rewrite /unique_in_registersL in Hunique_code.
  rewrite /unique_in_registersL in Hunique_data.
  eapply map_Forall_lookup_1 in Hunique_code; last eapply Hrdata.
  eapply map_Forall_lookup_1 in Hunique_data; last eapply Hrcode.
  rewrite decide_False // in Hunique_code.
  rewrite decide_False // in Hunique_data.
  rewrite /overlap_wordL /overlap_word /= in Hunique_code, Hunique_data.
  intros x Hx Hx'.
  rewrite !elem_of_finz_seq_between in Hx, Hx'.
  destruct ((b <? b')%a) eqn:Hbb'; solve_finz.
Qed.


Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}
          {contract_enclaves : @CustomEnclavesMap Σ MP}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Local Hint Resolve finz_seq_between_NoDup list_remove_elem_NoDup : core.

  Ltac iHide0 irisH coqH :=
    let coqH := fresh coqH in
    match goal with
    | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
        set (coqH := prop)
    end.

  Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
    iHide0 irisH coqH.

  Ltac name_current_mask name :=
    match goal with
    | _ : _ |- context [ wp _ ?mask _ _ ] =>
        set (name := mask)
    end.

  (* TODO move *)
  Global Instance elem_of_dec `{EqDecision A} (a : A) (l : list A) : Decision (a ∈ l).
  Proof.
    induction l; cbn.
    - right. apply not_elem_of_nil.
    - destruct (decide (a = a0)); subst.
      + left; set_solver.
      + destruct IHl.
        * left; set_solver.
        * right; set_solver.
  Qed.

  Global Instance disjoint_dec `{EqDecision A} (l1 l2 : list A) : Decision (l1 ## l2).
  Proof.
    induction l1; cbn.
    - left; set_solver.
    - destruct (decide (a ∈ l2)).
      + right; set_solver.
      + destruct IHl1.
        * left; set_solver.
        * right; set_solver.
  Qed.

  Lemma compute_mask_disjoint_namespace (E : coPset) (N : namespace) (ls : gset LAddr) :
    disjoint (A:= coPset) (↑N) (↑logN) ->
    ↑N ⊆ E ->
    ↑N ⊆ compute_mask E ls.
  Proof.
    rewrite /compute_mask.
    revert E.
    induction ls using set_ind_L; intros E HN HNE.
    { set_solver. }
    rewrite set_fold_disj_union_strong; [|set_solver..].
    rewrite set_fold_singleton.
    apply IHls; [done|].
    eapply namespaces.coPset_subseteq_difference_r; auto.
    by apply ndot_preserve_disjoint_r.
  Qed.

  Lemma is_valid_updated_lmemory_lmem_subset
    (glmem llmem llmem' llmem'' : LMem) (la : list Addr) (v : Version) :
    llmem ⊆ llmem' ->
    is_valid_updated_lmemory glmem llmem' la v llmem'' ->
    is_valid_updated_lmemory glmem llmem la v llmem''.
  Proof.
    move: glmem llmem llmem' v.
    induction la as [|a la IHla]
    ; intros * Hsubset (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated)
    ; first (cbn in * ; eauto).
    - rewrite /is_valid_updated_lmemory.
      repeat split; eauto; cbn; eapply map_subseteq_trans; eauto.
    - destruct_cons; destruct Hupdated_a as [ lwa Hlwa ].
      rewrite /is_valid_updated_lmemory.
      repeat split; eauto.
      + eapply update_version_region_mono in Hsubset; eauto.
        eapply map_subseteq_trans; eauto.
      + eapply map_subseteq_trans; eauto.
      + rewrite Forall_cons; split; first eapply lookup_weaken_None; eauto.
        rewrite !Forall_forall in HmaxMem |- *.
        intros a' Ha'. apply HmaxMem in Ha'.
        eapply lookup_weaken_None; eauto.
  Qed.

  Lemma logical_region_map_disjoint
    (la1 la2 : list Addr) (lw1 lw2 : list LWord) (v1 v2 : Version) :
    la1 ## la2 ->
    length la1 = length lw1 ->
    logical_region_map la1 lw1 v1 ##ₘ logical_region_map la2 lw2 v2.
  Proof.
    intros Hdis Hlen.
    rewrite /logical_region_map.
    eapply map_disjoint_list_to_map_zip_l ; first by rewrite map_length.
    rewrite Forall_forall.
    intros a Ha.
    apply elem_of_list_fmap in Ha.
    destruct Ha as (x & -> & Hx).
    apply not_elem_of_list_to_map_1.
    intro Hcontra.
    rewrite elem_of_list_fmap in Hcontra.
    destruct Hcontra as ( [y vy] & ? & Hy); simplify_eq.
    cbn in *.
    apply elem_of_zip_l in Hy.
    apply elem_of_list_fmap in Hy.
    destruct Hy as (y' & -> & Hy').
    set_solver.
  Qed.

  Set Nested Proofs Allowed.

  Lemma einit_case (lregs : leibnizO LReg)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version)
    (lw_pc : LWord) (rcode rdata : RegName) (P : D):
    ftlr_instr lregs p_pc b_pc e_pc a_pc v_pc lw_pc (EInit rcode rdata) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "[#Hcontract #Hsystem_inv] #IH #Hinv #Hinva #Hreg #(Hread & Hwrite & %HpersP) Hown Ha HP Hcls HPC Hmap".
    specialize (HpersP lw_pc).
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)) as [Hx|Hx].
      rewrite Hx lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hrcode now, to instantiate the existentials in step 1 *)
    assert (∃ p_code b_code e_code a_code v_code,
               read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs)
                 rcode p_code b_code e_code a_code v_code)
      as (p_code & b_code & e_code & a_code & v_code & HVrcode).
    {
      specialize Hsome' with rcode as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p_code b_code e_code a_code v_code|] | ]; try done.
      by repeat eexists.
    }
    (* Initializing the names for the values of Hrdata now, to instantiate the existentials in step 1 *)
    assert (∃ p_data b_data e_data a_data v_data,
               read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs)
                 rdata p_data b_data e_data a_data v_data)
      as (p_data & b_data & e_data & a_data & v_data & HVrdata).
    {
      specialize Hsome' with rdata as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p_data b_data e_data a_data v_data|] | ]; try done.
      by repeat eexists.
    }
    name_current_mask mask_init.


    (* rewrite /custom_enclave_inv. *)
    (* iInv (custom_enclaveN) as "Hsystem" "Hsystem_cls". *)
    (* iDestruct "Hsystem" as (ecn otn) "(>HEC & >%Hot & Hseal_alloc & Hseal_free & Hcontract)". *)
      (* iHide "Hsystem_cls" as hsystem_cls. *)

    destruct (decide (PC = rcode)) as [?|Hrcode_neq_pc]; simplify_map_eq.
    { admit. }
    destruct (decide (PC = rdata)) as [?|Hrdata_neq_pc]; simplify_map_eq.
    { admit. }

    - pose proof (Hsome rcode) as [wcode Hlregs_rcode].
      rewrite /read_reg_inr in HVrcode; simplify_map_eq.
      iAssert (interp wcode) as "#Hinterp_wcode" ; first (iApply ("Hreg" $! rcode); eauto).
      pose proof (Hsome rdata) as [wdata Hlregs_rdata].
      rewrite /read_reg_inr in HVrdata; simplify_map_eq.
      iAssert (interp wdata) as "#Hinterp_wdata" ; first (iApply ("Hreg" $! rdata); eauto).

      iAssert (⌜allows_einit (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) rcode⌝)%I
        as "%Hreserved_wcode".
      { iIntros (p b e a v Hrcode HreadAllowed).
        rewrite lookup_insert_ne // in Hrcode.
        rewrite Hrcode in Hlregs_rcode; simplify_eq.
        iDestruct (readAllowed_not_reserved with "Hinterp_wcode") as "%Hreserved_code"; done.
      }
      iAssert (⌜allows_einit (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) rdata⌝)%I
        as "%Hreserved_wdata".
      { iIntros (p b e a v Hrdata HreadAllowed).
        rewrite lookup_insert_ne // in Hrdata.
        rewrite Hrdata in Hlregs_rdata; simplify_eq.
        iDestruct (readAllowed_not_reserved with "Hinterp_wdata") as "%Hreserved_data"; done.
      }

      destruct (is_log_cap wcode) eqn:Hwcode; cycle 1.
      { (* wcode in not a capability *)
        iDestruct (memMap_resource_1 with "Ha") as "Hmem".
        iInv "Hsystem_inv" as "Hsys" "Hcls_sys".
        iDestruct "Hsys" as (Ecn ot_ec) "(>HEC & >%Hot_ec & Halloc & Hfree & #Hcustom_inv)".

        iApply (wp_einit with "[$Hmap $Hmem $HEC]")
        ;eauto
        ; [ by simplify_map_eq
          | rewrite /subseteq /map_subseteq /set_subseteq_instance
            ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
          | by simplify_map_eq
          |
          ].
        iNext.
        iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
        iDestruct "Hspec" as "[Hspec | Hspec]".
        (* Contradiction *)
        + iDestruct "Hspec"
            as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v eid)
                 "(%Htidx_next & %Htidx & %Htidx_even & %Heid & %Hot & %Hrcode & %Hrdata
          & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
          & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
          & %Hincr & -> & Henclave_live & #Henclave_all)".
          exfalso.
          clear -Hrcode_neq_pc Hrcode Hlregs_rcode Hwcode.
          simplify_map_eq.
          rewrite Hlregs_rcode in Hrcode; simplify_eq.
        + iDestruct "Hspec" as "(_ & -> & -> & ->)".
          iApply wp_pure_step_later; auto.
          iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
          { iNext. iExists Ecn, ot_ec.
            iFrame "∗#%".
          }
          iDestruct (memMap_resource_1 with "Hmem") as "Ha".
          iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
          iNext; iIntros "_".
          iApply wp_value; auto. iIntros; discriminate.
      }
      destruct_word wcode; cbn in HVrcode, Hwcode ; simplify_eq.

      destruct (decide (p_code = RX)) as [->|Hrx]; cycle 1.
      { (* wcode in not a RX capability *)
        iDestruct (memMap_resource_1 with "Ha") as "Hmem".
        iInv "Hsystem_inv" as "Hsys" "Hcls_sys".
        iDestruct "Hsys" as (Ecn ot_ec) "(>HEC & >%Hot_ec & Halloc & Hfree & #Hcustom_inv)".

        iApply (wp_einit with "[$Hmap $Hmem $HEC]")
        ;eauto
        ; [ by simplify_map_eq
          | rewrite /subseteq /map_subseteq /set_subseteq_instance
            ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
          | by simplify_map_eq
          |
          ].
        iNext.
        iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
        iDestruct "Hspec" as "[Hspec | Hspec]".
        (* Contradiction *)
        + iDestruct "Hspec"
            as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v eid)
                 "(%Htidx_next & %Htidx & %Htidx_even & %Heid & %Hot & %Hrcode & %Hrdata
          & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
          & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
          & %Hincr & -> & Henclave_live & #Henclave_all)".
          exfalso.
          clear -Hrcode_neq_pc Hrcode Hlregs_rcode Hrx.
          simplify_map_eq.
          rewrite Hlregs_rcode in Hrcode; simplify_eq.
        + iDestruct "Hspec" as "(_ & -> & -> & ->)".
          iApply wp_pure_step_later; auto.
          iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
          { iNext. iExists Ecn, ot_ec.
            iFrame "∗#%".
          }
          iDestruct (memMap_resource_1 with "Hmem") as "Ha".
          iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
          iNext; iIntros "_".
          iApply wp_value; auto. iIntros; discriminate.
      }

      destruct (is_log_cap wdata) eqn:Hwdata; cycle 1.
      { (* wdata in not a capability *)
        iDestruct (memMap_resource_1 with "Ha") as "Hmem".
        iInv "Hsystem_inv" as "Hsys" "Hcls_sys".
        iDestruct "Hsys" as (Ecn ot_ec) "(>HEC & >%Hot_ec & Halloc & Hfree & #Hcustom_inv)".

        iApply (wp_einit with "[$Hmap $Hmem $HEC]")
        ;eauto
        ; [ by simplify_map_eq
          | rewrite /subseteq /map_subseteq /set_subseteq_instance
            ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
          | by simplify_map_eq
          |
          ].
        iNext.
        iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
        iDestruct "Hspec" as "[Hspec | Hspec]".
        (* Contradiction *)
        + iDestruct "Hspec"
            as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v eid)
                 "(%Htidx_next & %Htidx & %Htidx_even & %Heid & %Hot & %Hrcode & %Hrdata
          & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
          & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
          & %Hincr & -> & Henclave_live & #Henclave_all)".
          exfalso.
          clear -Hrdata_neq_pc Hrdata Hlregs_rdata Hwdata.
          simplify_map_eq.
          rewrite Hlregs_rdata in Hrdata; simplify_eq.
        + iDestruct "Hspec" as "(_ & -> & -> & ->)".
          iApply wp_pure_step_later; auto.
          iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
          { iNext. iExists Ecn, ot_ec.
            iFrame "∗#%".
          }
          iDestruct (memMap_resource_1 with "Hmem") as "Ha".
          iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
          iNext; iIntros "_".
          iApply wp_value; auto. iIntros; discriminate.
      }
      destruct_word wdata; cbn in HVrdata, Hwdata ; simplify_eq.

      destruct (decide (p_data = RW)) as [->|Hrx]; cycle 1.
      { (* wdata in not a RW capability *)
        iDestruct (memMap_resource_1 with "Ha") as "Hmem".
        iInv "Hsystem_inv" as "Hsys" "Hcls_sys".
        iDestruct "Hsys" as (Ecn ot_ec) "(>HEC & >%Hot_ec & Halloc & Hfree & #Hcustom_inv)".

        iApply (wp_einit with "[$Hmap $Hmem $HEC]")
        ;eauto
        ; [ by simplify_map_eq
          | rewrite /subseteq /map_subseteq /set_subseteq_instance
            ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
          | by simplify_map_eq
          |
          ].
        iNext.
        iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
        iDestruct "Hspec" as "[Hspec | Hspec]".
        (* Contradiction *)
        + iDestruct "Hspec"
            as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v eid)
                 "(%Htidx_next & %Htidx & %Htidx_even & %Heid & %Hot & %Hrcode & %Hrdata
          & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
          & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
          & %Hincr & -> & Henclave_live & #Henclave_all)".
          exfalso.
          clear -Hrdata_neq_pc Hrdata Hlregs_rdata Hrx.
          simplify_map_eq.
          rewrite Hlregs_rdata in Hrdata; simplify_eq.
        + iDestruct "Hspec" as "(_ & -> & -> & ->)".
          iApply wp_pure_step_later; auto.
          iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
          { iNext. iExists Ecn, ot_ec.
            iFrame "∗#%".
          }
          iDestruct (memMap_resource_1 with "Hmem") as "Ha".
          iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
          iNext; iIntros "_".
          iApply wp_value; auto. iIntros; discriminate.
      }

      destruct ( decide (a_pc ∈ (finz.seq_between b_code e_code)))
      as [Hcode_apc_disjoint|Hcode_apc_disjoint].
      { (* code overlap with pc, the sweep will fail *)
        (* TODO opsem will fail *)
        admit.
      }

      destruct ( decide (a_pc ∈ (finz.seq_between b_data e_data)))
      as [Hdata_apc_disjoint|Hdata_apc_disjoint].
      { (* data overlap with pc, the sweep will fail *)
        (* TODO opsem will fail *)
        admit.
      }

      destruct ( decide ((finz.seq_between b_code e_code) ## (finz.seq_between b_data e_data)))
      as [Hcode_data_disjoint|Hcode_data_disjoint]; cycle 1.
      { (* code and data overlap, the sweep will fail *)
        (* TODO opsem will fail *)
        admit.
      }


      (* Open the code region *)
      iDestruct (interp_open_region $ mask_init with "Hinterp_wcode")
        as (Ps_code) "[%Hlen_Ps_code Hmod]" ; eauto.
      { eapply Forall_forall. intros a' Ha'.
        subst mask_init.
        eapply namespaces.coPset_subseteq_difference_r; auto.
        assert (a' ≠ a_pc) by set_solver.
        solve_ndisj.
      }
      iMod "Hmod" as (lws_code) "(%Hlen_lws_code & %Hpers_Ps_code
      & Hcode & HPs_code & Hreadcond_Ps_code & Hcls_code)".
      name_current_mask mask_code.

      (* Open the data region *)
      iDestruct (interp_open_region $ mask_code with "Hinterp_wdata")
        as (Ps_data) "[%Hlen_Ps_data Hmod]" ; eauto.
      { eapply Forall_forall. intros a' Ha'.
        subst mask_code mask_init.
        rewrite /compute_mask_region.
        rewrite -compute_mask_difference.
        2: {
          rewrite not_elem_of_list_to_set.
          intro Hcontra.
          rewrite elem_of_list_fmap in Hcontra.
          destruct Hcontra as (a'' & ? & Ha'') ; simplify_eq.
        }
        eapply namespaces.coPset_subseteq_difference_r; auto.
        + assert (a' ≠ a_pc) by set_solver.
          solve_ndisj.
        + apply compute_mask_elem_of; set_solver.
      }
      iMod "Hmod" as (lws_data) "(%Hlen_lws_data & %Hpers_Ps_data
      & Hdata & HPs_data & Hreadcond_Ps_data & Hcls_data)".
      name_current_mask mask_data.

      iDestruct (big_sepM_union with "[$Hcode $Hdata]") as "Hmem".
      { rewrite /logical_region_map.
        apply map_disjoint_list_to_map_zip_r_2; auto.
        + cbn in *; f_equal; simplify_eq.
          by rewrite map_length.
        + apply Forall_forall.
          intros la Hla.
          apply not_elem_of_list_to_map_1.
          rewrite fst_zip; eauto.
          * intro Hcontra.
            rewrite !elem_of_list_fmap in Hla,Hcontra.
            destruct Hla as (la' & -> & Hla').
            destruct Hcontra as (la'' & ? & Hla''); simplify_eq.
            set_solver.
          * cbn.
            rewrite map_length.
            cbn in Hlen_lws_code; simplify_eq.
            lia.
      }
      iDestruct (big_sepM_insert with "[$Hmem $Ha]") as "Hmem".
      { rewrite lookup_union.
        rewrite !logical_region_notin; auto.
      }

      iInv "Hsystem_inv" as "Hsys" "Hcls_sys".
      {
        subst mask_data mask_code mask_init.
        rewrite /compute_mask_region.
        eapply compute_mask_disjoint_namespace ; eauto; first solve_ndisj.
        eapply compute_mask_disjoint_namespace ; eauto; first solve_ndisj.
        eapply namespaces.coPset_subseteq_difference_r; auto; first solve_ndisj.
      }
      iDestruct "Hsys" as (Ecn ot_ec) "(>HEC & >%Hot_ec & Halloc & Hfree & #Hcustom_inv)".
      name_current_mask mask_sys.

      destruct (decide (b_code < e_code)%a) as [Hb_code|Hb_code]; cycle 1.
      { (* The code cap is expected to have space for the data cap in its first address *)
        admit. (* opsem will fail *)
      }
      rewrite (finz_seq_between_cons b_code) //.
      rewrite (finz_seq_between_cons b_code) // in Hlen_lws_code.
      destruct lws_code as [|lws_code1 lws_code]; first (by cbn in Hlen_lws_code).

      destruct (decide (b_data < e_data)%a) as [Hdata|Hdata]; cycle 1.
      { (* The data cap is expected to have space for the seal cap in its first address *)
        admit. (* opsem will fail *) }
      rewrite (finz_seq_between_cons b_data) //.
      rewrite (finz_seq_between_cons b_data) // in Hlen_lws_data.
      destruct lws_data as [|lws_data1 lws_data]; first (by cbn in Hlen_lws_data).



      destruct (ot_ec + 2)%ot as [ot_ec2|] eqn:Hot_ec2; cycle 1.
      { (* The opsem expect to be able to allocate the 2 next otypes *)
        (* opsem will fail *)
        admit.
      }

      destruct (decide (is_Some (a_pc + 1)%a)) as [Hpca_next | Hpca_next]; cycle 1.
      { (* The opsem expect to be able to allocate the 2 next otypes *)
        (* opsem will fail *)
        admit.
      }

      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ; eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC  & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]"; cycle 1.
      {
        iDestruct "Hspec" as "(%Hspec & -> & -> & ->)".
        exfalso.
        inversion Hspec
          as [ wcode Hrcode Hwcode
             | p b e a v Hrcode Hrx
             | p b e a v Hrcode Hbe
             | wdata Hrdata Hwdata
             | p b e a v Hrdata Hrx
             | p b e a v Hrdata Hbe
             | code_b code_e code_a code_v data_b data_e data_a data_v Hrcode Hrdata Hincr
             | Htidx Htidx_even Hot
          ].
        - rewrite lookup_insert_ne // Hlregs_rcode in Hrcode; simplify_eq.
        - rewrite lookup_insert_ne // Hlregs_rcode in Hrcode; simplify_eq.
        - rewrite lookup_insert_ne // Hlregs_rcode in Hrcode; simplify_eq.
        - rewrite lookup_insert_ne // Hlregs_rdata in Hrdata; simplify_eq.
        - rewrite lookup_insert_ne // Hlregs_rdata in Hrdata; simplify_eq.
        - rewrite lookup_insert_ne // Hlregs_rdata in Hrdata; simplify_eq.
        - incrementLPC_inv; simplify_map_eq; eauto.
          rewrite Hincr /is_Some in Hpca_next; naive_solver.
        - opose proof (otype_unification ot ot_ec Ecn _ _ _) as -> ; eauto.
          by rewrite Hot in Hot_ec2.
      }
      clear Hpca_next.

      iDestruct "Hspec"
        as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v eid)
             "(%Htidx_next & %Htidx & %Htidx_even & %Heid & %Hot & %Hrcode & %Hrdata
          & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
          & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
          & %Hincr & -> & Henclave_live & #Henclave_all)".


      simplify_map_eq.
      incrementLPC_inv as (p_pc'&b_pc'&e_pc'&a_pc'&v_pc'& ? & HPC & Z & Hregs'); simplify_map_eq.
      match goal with
      | _ : _ |- context [ enclave_cur ?ECN ?I ] =>
          set (I_ECn := I)
      end.

      rewrite Hrcode in Hlregs_rcode; simplify_eq.
      rewrite Hrdata in Hlregs_rdata; simplify_eq.
      opose proof (otype_unification ot ot_ec Ecn _ _ _) as -> ; eauto.
      clear Hot_ec2 ot_ec2.

        rewrite (finz_seq_between_cons ot_ec); last solve_addr.
        rewrite (finz_seq_between_cons (ot_ec ^+ 1)%ot); last solve_addr.
        iEval (rewrite !list_to_set_cons) in "Hfree".
        iDestruct (big_sepS_union with "Hfree") as "[Hfree_ot_ec_0 Hfree]".
        { admit. }
        iDestruct (big_sepS_union with "Hfree") as "[Hfree_ot_ec_1 Hfree]".
        { admit. }
        rewrite !big_sepS_singleton.

        set (lmem' :=
              <[(b_data, v_data + 1):=LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec]>
                             (<[(b_code, v_code+1):=LCap RW b_data e_data a_data (v_data + 1)]> lmem'')).

        (* Derive pure predicates about a_pc' *)
        assert ( lmem'' !! (a_pc', v_pc') = Some lw_pc ) as Hmem''_pca.
        { eapply is_valid_updated_lmemory_preserves_lmem; eauto.
          by simplify_map_eq.
        }
        assert ( lmem' !! (a_pc', v_pc') = Some lw_pc ) as Hmem'_pca.
        { subst lmem'.
          rewrite lookup_insert_ne //=; cycle 1.
          { intro; simplify_eq.
            apply Hdata_apc_disjoint.
            rewrite finz_seq_between_cons //=.
            set_solver+.
          }
          rewrite lookup_insert_ne //=; cycle 1.
          { intro; simplify_eq.
            apply Hcode_apc_disjoint.
            rewrite finz_seq_between_cons //=.
            set_solver+.
          }
        }
        rewrite -(insert_id lmem' (a_pc', v_pc') lw_pc); auto.
        iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha Hmem]".
        match goal with
        | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
            set (lmem0 := m)
        end.

        (* Derive pure predicates about the previous code_region*)
        assert ( logical_range_map b_code e_code (lws_code1::lws_code) v_code ⊆ lmem'' )
          as Hmem''_code.
        {
          eapply is_valid_updated_lmemory_lmem_incl
            with (la := (finz.seq_between b_code e_code))
                 (v:= v_code)
          ; eauto.
          eapply is_valid_updated_lmemory_lmem_subset; last eassumption.
          eapply map_subseteq_trans; cycle 1.
          + eapply insert_subseteq.
            rewrite lookup_union.
            rewrite !logical_region_notin; auto.
            * by cbn ; f_equal.
            * rewrite -finz_seq_between_cons //=.
            * by cbn ; f_equal.
            * rewrite -finz_seq_between_cons //=.
          + rewrite -finz_seq_between_cons //=.
            eapply map_union_subseteq_l.
        }
        assert ( logical_range_map b_code e_code (lws_code1::lws_code) v_code ⊆ lmem' )
          as Hmem'_code.
        {
          subst lmem'.
          eapply insert_subseteq_r.
          { eapply logical_range_notin; admit. (* easy *) }
          eapply insert_subseteq_r.
          { eapply logical_range_version_neq; last lia. admit. (* easy *) }
          done.
        }
        assert ( logical_range_map b_code e_code (lws_code1::lws_code) v_code ⊆ lmem0 )
          as Hmem0_code.
        {
          subst lmem0.
          eapply delete_subseteq_r; last done.
          apply logical_range_notin; last done.
          admit. (* easy *)
        }
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hcode_prev Hmem]"
        ; first (eapply Hmem0_code).
        match goal with
        | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
            set (lmem1 := m)
        end.


        (* Derive pure predicates about the new code_region*)
        assert
          (logical_range_map b_code e_code (lws_code1::lws_code) (v_code + 1) ⊆ lmem'')
          as Hmem''_code_next.
        {
          clear -Hvalid_update_code Hlen_lws_code Hlen_lws_data Hcode_apc_disjoint
                   Hdata_apc_disjoint Hcode_data_disjoint
                   Hb_code Hdata.
          eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
          assert (v' = v_code+1 /\ (a' ∈ (finz.seq_between b_code e_code)))
            as [-> Ha'_in_be].
          {
           eapply logical_range_map_some_inv; eauto.
           rewrite finz_seq_between_cons //=.
           by cbn ; f_equal.
          }
          destruct Hvalid_update_code as (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated).
          eapply lookup_weaken; last eapply Hcompatibility.
          rewrite update_version_region_preserves_lmem_next; eauto.
          + eapply lookup_weaken;eauto.
            rewrite lookup_insert_ne; last admit.
            rewrite lookup_union.
            replace (
               logical_region_map (b_data :: finz.seq_between (b_data ^+ 1)%a e_data) (lws_data1 :: lws_data) v_data !! (a', v_code)
              ) with (None : option LWord).
            2:{ admit. }
            rewrite option_union_right_id.
            rewrite -finz_seq_between_cons //.
            rewrite (logical_region_map_lookup_versions _ _ _ v_code) in Hlw'; eauto.
            admit.
          + rewrite lookup_insert_ne //=; last (intro ; set_solver).
            rewrite lookup_union.
            rewrite (logical_region_notin _ _ v_data); auto; cycle 1.
            { by cbn ; f_equal. }
            { rewrite -finz_seq_between_cons //=.
              intro.
              eapply elem_of_disjoint; eauto.
            }
            rewrite option_union_right_id.
            rewrite -finz_seq_between_cons //=.
            eapply logical_range_version_neq; eauto; last lia.
            rewrite finz_seq_between_cons //=; cbn ; by f_equal.
        }
        assert
          (logical_range_map b_code e_code (LCap RW b_data e_data a_data (v_data + 1)::lws_code) (v_code + 1) ⊆ lmem')
          as Hmem'_code_next.
        {
          clear -Hvalid_update_code Hlen_lws_code Hlen_lws_data Hcode_apc_disjoint
                   Hdata_apc_disjoint Hcode_data_disjoint
                   Hb_code Hdata Hmem''_code_next.
          subst lmem'.
          eapply insert_subseteq_r.
          { eapply logical_range_notin; admit. (* easy *) }
          rewrite -(logical_range_map_insert _ _ _ lws_code1); auto.
          by apply insert_mono.
        }
        assert ( logical_range_map b_code e_code (LCap RW b_data e_data a_data (v_data + 1)::lws_code) (v_code + 1) ⊆ lmem0 )
          as Hmem0_code_next.
        {
          subst lmem0.
          eapply delete_subseteq_r; last done.
          apply logical_range_notin; last done.
          admit. (* easy *)
        }
        assert ( logical_range_map b_code e_code (LCap RW b_data e_data a_data (v_data + 1)::lws_code) (v_code + 1) ⊆ lmem1 )
          as Hmem1_code_next.
        {
          subst lmem1.
          eapply (delete_subseteq_list_r); eauto.
          rewrite /logical_range_map.
          apply map_disjoint_list_to_map_zip_l.
          { admit. }
          apply Forall_forall.
          intros y Hy.
          apply not_elem_of_list_to_map.
          intro Hcontra.
          rewrite elem_of_list_fmap in Hcontra.
          destruct Hcontra as ([ [y' vy'] wy'] & -> & Hcontra).
          eapply elem_of_zip_l in Hcontra.
          rewrite /logical_region in Hy, Hcontra.
          rewrite !elem_of_list_fmap in Hy,Hcontra.
          destruct Hy as (? & ? & _); simplify_eq.
          destruct Hcontra as (? & ? & _); simplify_eq.
          cbn in H; simplify_eq.
          lia.
        }
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hcode Hmem]"
        ; first (eapply Hmem1_code_next).
        match goal with
        | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
            set (lmem2 := m)
        end.

        (* Derive pure predicates about the previous data_region*)
        assert ( logical_range_map b_data e_data (lws_data1::lws_data) v_data ⊆ lmem'' )
          as Hmem''_data.
        {
          eapply is_valid_updated_lmemory_lmem_incl
            with (la := (finz.seq_between b_data e_data))
                 (v:= v_data)
          ; eauto.
          eapply is_valid_updated_lmemory_lmem_subset; last eassumption.
          eapply map_subseteq_trans; cycle 1.
          + eapply insert_subseteq.
            rewrite lookup_union.
            rewrite !logical_region_notin; auto.
            * by cbn ; f_equal.
            * rewrite -finz_seq_between_cons //=.
            * by cbn ; f_equal.
            * rewrite -finz_seq_between_cons //=.
          + rewrite -!finz_seq_between_cons //=.
            eapply map_union_subseteq_r.
            apply logical_region_map_disjoint; auto.
            by rewrite finz_seq_between_cons //=; cbn ; f_equal.
        }
        assert ( logical_range_map b_data e_data (lws_data1::lws_data) v_data ⊆ lmem' )
          as Hmem'_data.
        {
          subst lmem'.
          eapply insert_subseteq_r.
          { eapply logical_range_version_neq; last lia. admit. (* easy *) }
          eapply insert_subseteq_r.
          { eapply logical_range_notin; admit. (* easy *) }
          done.
        }
        assert ( logical_range_map b_data e_data (lws_data1::lws_data) v_data ⊆ lmem0 )
          as Hmem0_data.
        {
          subst lmem0.
          eapply delete_subseteq_r; last done.
          apply logical_range_notin; last done.
          admit. (* easy *)
        }
        assert ( logical_range_map b_data e_data (lws_data1::lws_data) v_data ⊆ lmem1 )
          as Hmem1_data.
        {
          subst lmem1.
          admit.
        }
        assert ( logical_range_map b_data e_data (lws_data1::lws_data) v_data ⊆ lmem2 )
          as Hmem2_data.
        {
          subst lmem2.
          admit.
        }
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hdata_prev Hmem]"
        ; first (eapply Hmem2_data).
        match goal with
        | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
            set (lmem3 := m)
        end.

        (* Derive pure predicates about the new data_region*)
        assert
          (logical_range_map b_data e_data (lws_data1::lws_data) (v_data + 1) ⊆ lmem'')
          as Hmem''_data_next.
        {
          clear -Hvalid_update_data Hlen_lws_code Hlen_lws_data Hdata_apc_disjoint
                   Hdata_apc_disjoint Hcode_data_disjoint
                   Hb_code Hdata.
          eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
          assert (v' = v_data+1 /\ (a' ∈ (finz.seq_between b_data e_data)))
            as [-> Ha'_in_be].
          {
           eapply logical_range_map_some_inv; eauto.
           rewrite finz_seq_between_cons //=.
           by cbn ; f_equal.
          }
          destruct Hvalid_update_data as (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated).
          eapply lookup_weaken; last eapply Hcompatibility.
          rewrite update_version_region_preserves_lmem_next; eauto.
          + admit. (* see Hgl_llmem *)
          + rewrite lookup_insert_ne //=; last (intro ; set_solver).
            rewrite lookup_union.
            rewrite (logical_region_notin _ _ v_code); auto; cycle 1.
            { by cbn ; f_equal. }
            { rewrite -finz_seq_between_cons //=.
              intro.
              eapply elem_of_disjoint; eauto.
            }
            rewrite option_union_left_id.
            rewrite -finz_seq_between_cons //=.
            eapply logical_range_version_neq; eauto; last lia.
            rewrite finz_seq_between_cons //=; cbn ; by f_equal.
        }
        assert
          (logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem')
          as Hmem'_data_next.
        {
          clear -Hvalid_update_data Hlen_lws_code Hlen_lws_data
                   Hcode_apc_disjoint Hdata_apc_disjoint Hcode_data_disjoint
                   Hb_code Hdata Hmem''_data_next.
          subst lmem'.
          rewrite insert_commute.
          2:{ intro ; simplify_eq. admit. (* should be easy with Hcode_data_disjoint *) }
          eapply insert_subseteq_r.
          { eapply logical_range_notin; admit. (* easy *) }
          rewrite -(logical_range_map_insert _ _ _ lws_data1); auto.
          by apply insert_mono.
        }
        assert ( logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem0 )
          as Hmem0_data_next.
        {
          subst lmem0.
          eapply delete_subseteq_r; last done.
          apply logical_range_notin; last done.
          admit. (* easy *)
        }
        assert ( logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem1 )
          as Hmem1_data_next.
        {
          subst lmem1.
          admit.
        }
        assert ( logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem2 )
          as Hmem2_data_next.
        {
          subst lmem2.
          admit.
        }
        assert ( logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem3 )
          as Hmem3_data_next.
        {
          subst lmem3.
          admit.
        }
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hdata Hmem]"
        ; first (eapply Hmem3_data_next).
        iClear "Hmem".
        clear
          Hmem''_data_next Hmem'_data_next Hmem0_data_next Hmem1_data_next Hmem2_data_next Hmem3_data_next lmem3
          Hmem''_data Hmem'_data Hmem0_data Hmem1_data Hmem2_data lmem2
          Hmem''_code_next Hmem'_code_next Hmem0_code_next Hmem1_code_next lmem1
          Hmem''_code Hmem'_code Hmem0_code lmem0
          Hmem''_pca Hmem'_pca lmem'
        .
        clear Hvalid_update_code Hvalid_update_data
          Hunique_regs_data Hunique_regs_code.

        iAssert (interp (LCap p_pc' b_pc' e_pc' x v_pc')) as "Hinterp_next_PC".
        { iApply interp_weakening_next_PC; eauto. }

       destruct (custom_enclaves !! I_ECn) as
         [ [Hcus_enclave_code Hcus_enclave_addr Hcus_enclave_enc Hcus_enclave_sign] |] eqn:HI_ECn.
        * (* CASE WHERE THE IDENTITY IS A KNOWN ENCLAVE *)
          set ( new_enclave := {| code := Hcus_enclave_code; code_region := Hcus_enclave_addr; Penc := Hcus_enclave_enc; Psign := Hcus_enclave_sign |} ).
          iMod (seal_store_update_alloc _ Hcus_enclave_enc with "Hfree_ot_ec_0") as "#Hseal_pred_enc".
          iMod (seal_store_update_alloc _ Hcus_enclave_sign with "Hfree_ot_ec_1") as "#Hseal_pred_sign".
          iAssert ( custom_enclave_contract_gen ) as "Hcontract'" ; eauto.
          iSpecialize ("Hcontract'" $!
                         mask_sys I_ECn
                         b_code e_code (v_code+1)
                         b_data e_data a_data (v_data+1)
                         lws_data ot_ec new_enclave).

          pose proof custom_enclaves_wf as [Hwf_map Hwf_map_z].

          iDestruct ( big_sepM_to_big_sepL2 with "Hcode" ) as "Hcode".
          { admit. (* trivial *) }
          { admit. (* trivial *) }
          iDestruct ( big_sepM_to_big_sepL2 with "Hdata" ) as "Hdata".
          { admit. (* trivial *) }
          { admit. (* trivial *) }

          assert (I_ECn = hash_concat (hash Hcus_enclave_addr) (hash Hcus_enclave_code)) as
            HI_ECn_eq.
          {
            clear -Hwf_map HI_ECn new_enclave.
            opose proof (map_Forall_lookup_1 _ custom_enclaves I_ECn new_enclave) as H.
            apply H in Hwf_map; eauto; cbn in *.
          }

          iMod ("Hcontract'" with
                 "[] [] [] [] [] [$Hseal_pred_enc $Hseal_pred_sign Hcode Hdata]")
                 as "#Hinterp_enclave"
          ; eauto.
          {
            iPureIntro.
            clear -HI_ECn_eq.
            subst I_ECn.
            apply hash_concat_inj' in HI_ECn_eq.
            destruct HI_ECn_eq as [-> ?]; simplify_eq.
            done.
          }
          {
            iPureIntro.
            clear -HI_ECn_eq.
            subst I_ECn.
            apply hash_concat_inj' in HI_ECn_eq.
            destruct HI_ECn_eq as [-> ?]; simplify_eq.
            done.
          }
          { iPureIntro.
            clear -HI_ECn_eq Hb_code Hlen_lws_code.
            subst I_ECn.
            apply hash_concat_inj' in HI_ECn_eq.
            destruct HI_ECn_eq as [-> ?]; simplify_eq.
            rewrite map_length.
            setoid_rewrite merge_sort_Permutation.
            rewrite map_length.
            rewrite map_to_list_length.

            rewrite map_filter_insert_False.
            2: admit.
            rewrite map_filter_delete.
            rewrite map_size_delete.
            replace (
                filter (λ '(a, _), laddr_get_addr a ∈ finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code ∧ laddr_get_version a = v_code)
                  (logical_region_map (Hcus_enclave_addr :: finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code) (lws_code1 :: lws_code) v_code
                     ∪ logical_region_map (b_data :: finz.seq_between (b_data ^+ 1)%a e_data) (lws_data1 :: lws_data) v_data) !! (
                    a_pc', v_pc')
              ) with (None : option LWord).
            2: admit.
            simpl.
            replace
              (
                (filter (λ '(a, _), laddr_get_addr a ∈ finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code ∧ laddr_get_version a = v_code)
                   (logical_region_map (Hcus_enclave_addr :: finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code) (lws_code1 :: lws_code) v_code
                      ∪ logical_region_map (b_data :: finz.seq_between (b_data ^+ 1)%a e_data) (lws_data1 :: lws_data) v_data))
              )
              with
              (logical_region_map (finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code) lws_code v_code).
            { rewrite map_size_list_to_map.
              2: admit.
              rewrite length_zip_l.
              2: admit.
              rewrite map_length.
              rewrite finz_seq_between_length.
              pose proof (finz_incr_iff_dist Hcus_enclave_addr e_code
                            (finz.dist Hcus_enclave_addr e_code))
              as [_ ?].
              replace
                (Hcus_enclave_addr + (finz.dist Hcus_enclave_addr e_code + 1))%a
                  with (Hcus_enclave_addr + (finz.dist Hcus_enclave_addr e_code + 1)%nat)%a; last solve_addr.
              rewrite Z.add_1_r.
              replace (Hcus_enclave_addr + Z.succ (finz.dist (Hcus_enclave_addr ^+ 1)%a e_code))%a
                with (Hcus_enclave_addr + (S (finz.dist (Hcus_enclave_addr ^+ 1)%a e_code)))%a
              ; last solve_addr.
              rewrite -finz_dist_S; last solve_addr.
              apply H; solve_addr.
            }
            rewrite map_filter_union; cycle 1.
            { rewrite /logical_region_map.
              (* eapply map_disjoint_list_to_map_zip_l; first admit. *)
              (* rewrite Forall_forall *)
              admit.
            }
            replace (
                filter (λ '(a, _), laddr_get_addr a ∈ finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code ∧ laddr_get_version a = v_code)
                  (logical_region_map (Hcus_enclave_addr :: finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code) (lws_code1 :: lws_code) v_code)
              ) with (logical_region_map (finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code) lws_code v_code).
            2: {
              rewrite /logical_region_map.
              rewrite !/logical_region.
              rewrite fmap_cons.
              simpl zip at 1.
              simpl list_to_map at 1.
              rewrite map_filter_insert_False.
              2: admit.
              rewrite map_filter_delete.
              rewrite delete_notin.
              2: admit.
              rewrite map_filter_id; first done.
              intros [a v] w Ha.
              apply elem_of_list_to_map in Ha; last admit.
              apply elem_of_zip_l in Ha.
              rewrite elem_of_list_fmap in Ha.
              destruct Ha as (? & -> & ?); auto.
            }
            replace (
                filter (λ '(a, _), laddr_get_addr a ∈ finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code ∧ laddr_get_version a = v_code)
                  (logical_region_map (b_data :: finz.seq_between (b_data ^+ 1)%a e_data) (lws_data1 :: lws_data) v_data)
              ) with (∅ : LMem).
            2: { symmetry.
                 apply map_filter_empty_iff.
                 admit.
            }
            by rewrite map_union_empty.
          }
          {
            replace ((λ w : Word, word_to_lword w (v_code + 1)) <$> code new_enclave) with lws_code
            ; first iFrame "∗#".
            (* clear -HI_ECn_eq. *)
            subst I_ECn.
            apply hash_concat_inj' in HI_ECn_eq.
            destruct HI_ECn_eq as [-> ?]; simplify_eq.
            cbn.

            replace (
                (filter (λ '(a, _), laddr_get_addr a ∈ finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code ∧ laddr_get_version a = v_code)
                   (<[(a_pc', v_pc'):=lw_pc]>
                      (<[(Hcus_enclave_addr, v_code):=lws_code1]>
                         (list_to_map (zip ((λ a : Addr, (a, v_code)) <$> finz.seq_between (Hcus_enclave_addr ^+ 1)%a e_code) lws_code))
                           ∪ <[(b_data, v_data):=lws_data1]>
                         (list_to_map (zip ((λ a : Addr, (a, v_data)) <$> finz.seq_between (b_data ^+ 1)%a e_data) lws_data)))))
              )
              with
              (
               (list_to_map (zip ((λ a : Addr, (a, v_code)) <$> finz.seq_between
                                    (Hcus_enclave_addr ^+ 1)%a e_code) lws_code)) : gmap LAddr LWord
              ).
            2: { admit. }


            erewrite merge_sort_Permutation_proper; last apply map_to_list_to_map; try apply _.
            2:{ admit. }

            rewrite Sorted_sort_zip.
            2: {
              apply finz_seq_between_laddr_Sorted.
              apply StronglySorted_Sorted.
              apply finz_seq_between_addr_StronglySorted.
            }
            rewrite snd_zip.
            2: { admit. }
            rewrite -list_fmap_compose.
            rewrite (Forall_fmap_ext_1 _ id); first by rewrite list_fmap_id.
            rewrite Forall_forall.
            intros w Hw; cbn.

            apply word_to_lword_get_word_int.
            apply map_Forall_insert_1_2 in Hcode_z.
            2: { admit. }
            apply map_Forall_union in Hcode_z.
            2: { admit. }
            destruct Hcode_z as [Hcode_z _].
            clear -Hcode_z Hw.
            (* Should be fine from Hcode_z *)
            admit.
            }

          iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_".
          { iNext.
            iExists (Ecn +1), (ot_ec ^+ 2)%ot.
            replace ((ot_ec ^+1) ^+1)%ot with (ot_ec ^+ 2)%ot by solve_addr + Hot.
            iFrame.
            iSplitR.
            { iPureIntro; solve_addr. }
            iSplitL "Halloc".
            { rewrite (finz_seq_between_split _ ot_ec (ot_ec ^+ 2)%ot); last solve_addr + Hot.
              rewrite list_to_set_app_L.
              rewrite big_sepS_union; last admit.
              iFrame.
              rewrite (finz_seq_between_cons ot_ec); last solve_addr + Hot.
              rewrite (finz_seq_between_cons (ot_ec ^+ 1)%ot); last solve_addr + Hot.
              rewrite (finz_seq_between_empty ((ot_ec ^+ 1) ^+ 1)%ot); last solve_addr + Hot.
              rewrite !list_to_set_cons list_to_set_nil.
              rewrite big_sepS_union; last admit.
              rewrite big_sepS_union; last admit.
              rewrite big_sepS_empty.
              rewrite !big_sepS_singleton.
              iSplit; [|iSplit]; try (iExists _ ;iFrame "#"); done.
            }
            iModIntro.
            iIntros (I tid_I ot_I ce_I) "%Htid_I (Henclave_I & %Hcustom_I & %Hhas_seal_I)".
            destruct (decide (tid_I = Ecn)) as [-> |Htid_I_ECn].
            { (* if tid_I = ECn, then it should be the predicate that had just been initialised *)
              assert (ot_ec = if Z.even ot_I then ot_I else (ot_I ^+ -1)%ot) as Hot'.
              { rewrite /has_seal in Hhas_seal_I.
                destruct (finz.of_z ot_I) eqn:Hot_I ; cbn in Hhas_seal_I; try done.
                apply finz_of_z_is_Some_spec in Hot_I.
                rewrite /tid_of_otype in Hhas_seal_I.
                destruct ( Z.even ot_I ) eqn:Hot_I_even.
                + assert (Z.even f = true) as Hf_even by (by rewrite Hot_I).
                  rewrite Hf_even in Hhas_seal_I.
                  assert (Ecn = (Z.to_nat f `div` 2)) as HEcn_eq by (by injection Hhas_seal_I).
                  clear Hhas_seal_I.
                  rewrite HEcn_eq in Hot_ec.
                  clear -Hot_ec Hot_I Hf_even.
                  assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat f) 2)) = (Z.to_nat f) ).
                  {
                  rewrite -(Nat2Z.inj_mul 2).
                  rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
                    2:{
                      destruct f.
                      rewrite /Z.even in Hf_even.
                      cbn in *.
                      destruct z; cbn in *.
                      + rewrite Z2Nat.inj_0.
                        apply PeanoNat.Nat.divide_0_r.
                      + rewrite Z2Nat.inj_pos.
                        destruct p; cbn in * ; try done.
                        rewrite Pos2Nat.inj_xO.
                        apply Nat.divide_factor_l.
                      + rewrite Z2Nat.inj_neg.
                        apply PeanoNat.Nat.divide_0_r.
                    }
                    rewrite PeanoNat.Nat.mul_comm.
                    rewrite (PeanoNat.Nat.div_mul (Z.to_nat f) 2); done.
                  }
                  solve_addr.
                + assert (Z.even f = false) as Hf_even by (by rewrite Hot_I).
                  rewrite Hf_even in Hhas_seal_I.
                  assert (Ecn = (Z.to_nat (f ^- 1)%f `div` 2) ) as HEcn_eq by (by injection Hhas_seal_I).
                  clear Hhas_seal_I.
                  rewrite HEcn_eq in Hot_ec.
                  clear -Hot_ec Hot_I Hf_even.
                  assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat (f ^- 1)%f) 2)) = (Z.to_nat (f ^- 1)%f) ).
                  {
                  rewrite -(Nat2Z.inj_mul 2).
                  rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
                    2:{
                      destruct f.
                      rewrite /Z.even in Hf_even.
                      cbn in *.
                      destruct z; cbn in *; try done.
                      destruct p; cbn in * ; try done.
                      + remember (finz.FinZ (Z.pos p~1) finz_lt finz_nonneg) as p1.
                        destruct (p1 ^- 1)%f eqn:HP1.
                        assert (z = Z.pos p~0).
                        { solve_finz. }

                        assert (  (((Z.pos p~0) <? ONum)%Z) = true ) as finz_lt2 by solve_finz.
                        assert (  ((0 <=? (Z.pos p~0))%Z) = true ) as finz_nonneg2 by solve_finz.
                        replace (finz.FinZ z finz_lt0 finz_nonneg0) with
                          (finz.FinZ (Z.pos p~0) finz_lt2 finz_nonneg2) by solve_finz.
                        cbn.
                        rewrite Z2Nat.inj_pos.
                        rewrite Pos2Nat.inj_xO.
                        apply Nat.divide_factor_l.
                      + remember (finz.FinZ 1 finz_lt finz_nonneg) as p1.
                        destruct (p1 ^- 1)%f eqn:HP1.
                        assert (z = 0).
                        { solve_finz. }

                        assert (  ((0 <? ONum)%Z) = true ) as finz_lt2 by solve_finz.
                        assert (  ((0 <=? 0)%Z) = true ) as finz_nonneg2 by solve_finz.
                        replace (finz.FinZ z finz_lt0 finz_nonneg0) with
                          (finz.FinZ 0 finz_lt2 finz_nonneg2) by solve_finz.
                        cbn.
                        rewrite Z2Nat.inj_0.
                        apply PeanoNat.Nat.divide_0_r.
                    }
                    rewrite PeanoNat.Nat.mul_comm.
                    rewrite (PeanoNat.Nat.div_mul (Z.to_nat (f ^- 1)%f) 2); done.
                  }
                  rewrite H in Hot_ec.
                  solve_addr.
              }
              iDestruct (enclave_all_agree _ I_ECn I with "[$Henclave_all $Henclave_I]") as "->".
              rewrite Hcustom_I in HI_ECn ; simplify_eq.
              destruct (Z.even ot_I); cbn in *; iFrame "#".
              replace (((ot_I ^+ -1) ^+ 1)%f) with ot_I by solve_finz.
              iFrame "#".
            }
            { (* tid_I ≠ Ecn*)
              assert (0 <= tid_I < Ecn) as Htid_I' by lia.
              iApply ("Hcustom_inv" with "[] [$Henclave_I]"); eauto.
            }
          }
          iModIntro.

          iMod ("Hcls_data" with "[Hdata_prev HPs_data Hreadcond_Ps_data]") as "_".
          {
            iNext.
            destruct Ps_data; first done.
            admit.
            (* iApply region_inv_construct; auto. *)
          }
          iModIntro.

          iMod ("Hcls_code" with "[Hcode_prev HPs_code Hreadcond_Ps_code]") as "_".
          {
            iNext.
            admit.
            (* iApply region_inv_construct; auto. *)
          }
          iModIntro.

          iMod ("Hcls" with "[Ha HP]") as "_";[iExists lw_pc;iFrame|iModIntro].
          rewrite (insert_commute _ rcode PC) // (insert_commute _ rdata PC) // insert_insert.
          iClear "Hcontract'".
          iApply wp_pure_step_later; auto.
          iNext; iIntros "_".
          iApply ("IH" $! (<[rdata:=LInt 0]> (<[rcode:=LCap E b_code e_code (b_code ^+ 1)%a (v_code + 1)]> lregs)) with "[%] [] [Hregs] [$Hown]"); eauto.
          { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
          {
            iIntros (ri ? Hri Hvs).
            destruct (decide (ri = rdata)); simplify_map_eq; first by rewrite !fixpoint_interp1_eq.
            destruct (decide (ri = rcode)); simplify_map_eq; first by rewrite !fixpoint_interp1_eq.
            iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
          }



        * (* CASE WHERE THE IDENTITY IS NOT A KNOWN ENCLAVE *)
          iMod (seal_store_update_alloc _ interp with "Hfree_ot_ec_0") as "#Hseal_pred_enc".
          iMod (seal_store_update_alloc _ interp with "Hfree_ot_ec_1") as "#Hseal_pred_sign".

          iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_".
          { iNext.
            iExists (Ecn +1), (ot_ec ^+2)%ot.
            replace ((ot_ec ^+1) ^+1)%ot with (ot_ec ^+2)%ot by solve_addr + Hot.
            iFrame.
            iSplitR.
            { iPureIntro; solve_addr. }
            iSplitL "Halloc".
            { rewrite (finz_seq_between_split _ ot_ec (ot_ec ^+2)%ot); last solve_addr + Hot.
              rewrite list_to_set_app_L.
              rewrite big_sepS_union; last admit.
              iFrame.
              rewrite (finz_seq_between_cons ot_ec); last solve_addr + Hot.
              rewrite (finz_seq_between_cons (ot_ec ^+ 1)%ot); last solve_addr + Hot.
              rewrite (finz_seq_between_empty ((ot_ec ^+ 1) ^+ 1)%ot); last solve_addr + Hot.
              rewrite !list_to_set_cons list_to_set_nil.
              rewrite big_sepS_union; last admit.
              rewrite big_sepS_union; last admit.
              rewrite big_sepS_empty.
              rewrite !big_sepS_singleton.
              iSplit; [|iSplit]; try (iExists _ ;iFrame "#"); done.
            }
            iModIntro.
            iIntros (I tid_I ot_I ce_I) "%Htid_I (Henclave_I & %Hcustom_I & %Hhas_seal_I)".
            destruct (decide (tid_I = Ecn)) as [-> |Htid_I_ECn].
            { (* if tid_I = ECn, then it should be the predicate that had just been initialised *)
              assert (ot_ec = if Z.even ot_I then ot_I else (ot_I ^+ -1)%ot) as Hot'.
              { rewrite /has_seal in Hhas_seal_I.
                destruct (finz.of_z ot_I) eqn:Hot_I ; cbn in Hhas_seal_I; try done.
                apply finz_of_z_is_Some_spec in Hot_I.
                rewrite /tid_of_otype in Hhas_seal_I.
                destruct ( Z.even ot_I ) eqn:Hot_I_even.
                + assert (Z.even f = true) as Hf_even by (by rewrite Hot_I).
                  rewrite Hf_even in Hhas_seal_I.
                  assert (Ecn = (Z.to_nat f `div` 2)) as HEcn_eq by (by injection Hhas_seal_I).
                  clear Hhas_seal_I.
                  rewrite HEcn_eq in Hot_ec.
                  clear -Hot_ec Hot_I Hf_even.
                  assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat f) 2)) = (Z.to_nat f) ).
                  {
                  rewrite -(Nat2Z.inj_mul 2).
                  rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
                    2:{
                      destruct f.
                      rewrite /Z.even in Hf_even.
                      cbn in *.
                      destruct z; cbn in *.
                      + rewrite Z2Nat.inj_0.
                        apply PeanoNat.Nat.divide_0_r.
                      + rewrite Z2Nat.inj_pos.
                        destruct p; cbn in * ; try done.
                        rewrite Pos2Nat.inj_xO.
                        apply Nat.divide_factor_l.
                      + rewrite Z2Nat.inj_neg.
                        apply PeanoNat.Nat.divide_0_r.
                    }
                    rewrite PeanoNat.Nat.mul_comm.
                    rewrite (PeanoNat.Nat.div_mul (Z.to_nat f) 2); done.
                  }
                  solve_addr.
                + assert (Z.even f = false) as Hf_even by (by rewrite Hot_I).
                  rewrite Hf_even in Hhas_seal_I.
                  assert (Ecn = (Z.to_nat (f ^- 1)%f `div` 2) ) as HEcn_eq by (by injection Hhas_seal_I).
                  clear Hhas_seal_I.
                  rewrite HEcn_eq in Hot_ec.
                  clear -Hot_ec Hot_I Hf_even.
                  assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat (f ^- 1)%f) 2)) = (Z.to_nat (f ^- 1)%f) ).
                  {
                  rewrite -(Nat2Z.inj_mul 2).
                  rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
                    2:{
                      destruct f.
                      rewrite /Z.even in Hf_even.
                      cbn in *.
                      destruct z; cbn in *; try done.
                      destruct p; cbn in * ; try done.
                      (* destruct ( (finz.FinZ (Z.pos p~1) finz_lt finz_nonneg) ^- 1)%f. *)
                      (* cbn. *)
                      + remember (finz.FinZ (Z.pos p~1) finz_lt finz_nonneg) as p1.
                        destruct (p1 ^- 1)%f eqn:HP1.
                        assert (z = Z.pos p~0).
                        { solve_finz. }

                        assert (  (((Z.pos p~0) <? ONum)%Z) = true ) as finz_lt2 by solve_finz.
                        assert (  ((0 <=? (Z.pos p~0))%Z) = true ) as finz_nonneg2 by solve_finz.
                        replace (finz.FinZ z finz_lt0 finz_nonneg0) with
                          (finz.FinZ (Z.pos p~0) finz_lt2 finz_nonneg2) by solve_finz.
                        cbn.
                        rewrite Z2Nat.inj_pos.
                        rewrite Pos2Nat.inj_xO.
                        apply Nat.divide_factor_l.
                      + remember (finz.FinZ 1 finz_lt finz_nonneg) as p1.
                        destruct (p1 ^- 1)%f eqn:HP1.
                        assert (z = 0).
                        { solve_finz. }

                        assert (  ((0 <? ONum)%Z) = true ) as finz_lt2 by solve_finz.
                        assert (  ((0 <=? 0)%Z) = true ) as finz_nonneg2 by solve_finz.
                        replace (finz.FinZ z finz_lt0 finz_nonneg0) with
                          (finz.FinZ 0 finz_lt2 finz_nonneg2) by solve_finz.
                        cbn.
                        rewrite Z2Nat.inj_0.
                        apply PeanoNat.Nat.divide_0_r.
                    }
                    rewrite PeanoNat.Nat.mul_comm.
                    rewrite (PeanoNat.Nat.div_mul (Z.to_nat (f ^- 1)%f) 2); done.
                  }
                  rewrite H in Hot_ec.
                  solve_addr.
              }
              iDestruct (enclave_all_agree _ I_ECn I with "[$Henclave_all $Henclave_I]") as "->".
              rewrite Hcustom_I in HI_ECn ; simplify_eq.
            }
            { (* tid_I ≠ Ecn*)
              assert (0 <= tid_I < Ecn) as Htid_I' by lia.
              iApply ("Hcustom_inv" with "[] [$Henclave_I]"); eauto.
            }
          }
          iModIntro.


          iDestruct "HPs_data" as "#HPs_data".
          iDestruct "Hreadcond_Ps_data" as "#Hreadcond_Ps_data".
          iMod ("Hcls_data" with "[Hdata_prev HPs_data Hreadcond_Ps_data]") as "_".
          {
            iNext.
            admit.
            (* iApply region_inv_construct; auto. *)
          }
          iModIntro.

          assert (Persistent (([∗ list] y1;y2 ∈ lws_code;Ps_code, (y2 : D) y1)%I)) as Hpers_Ps_code'.
          { clear -Hpers_Ps_code.
            admit. }
          iDestruct "HPs_code" as "#HPs_code".
          iDestruct "Hreadcond_Ps_code" as "#Hreadcond_Ps_code".
          iMod ("Hcls_code" with "[Hcode_prev HPs_code Hreadcond_Ps_code]") as "_".
          {
            iNext.
            admit.
            (* iApply region_inv_construct; auto. *)
          }
          iModIntro.

          iMod ("Hcls" with "[Ha HP]") as "_";[iExists lw_pc;iFrame|iModIntro].

          iMod (inv_alloc (attestN.@Ecn) _ ((∃ I : EIdentity, enclave_cur Ecn I) ∨ enclave_prev Ecn) with "[Henclave_live]")
                 as "#Hattest".
          { by iNext; iLeft; iExists I_ECn. }
          iAssert (interp (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec)) as "Hinterp_seal".
          { iEval (rewrite fixpoint_interp1_eq /=).
            assert (ot_ec < ot_ec ^+ 2)%ot as Hot' by solve_finz.
            assert (ot_ec ^+ 1 < ot_ec ^+ 2)%ot as Hot'' by solve_finz.
            assert (ot_ec ^+ 2 <= ot_ec ^+ 2)%ot as Hot''' by solve_finz.

            iSplit;[|iSplit].
            + rewrite /safe_to_seal.
              iEval (rewrite finz_seq_between_cons //).
              iEval (rewrite finz_seq_between_cons //).
              replace ((ot_ec ^+ 1) ^+ 1)%f with (ot_ec ^+ 2)%ot by solve_finz.
              iEval (rewrite finz_seq_between_empty //).
              rewrite 2!big_sepL_cons big_sepL_nil.
              iSplit; [|iSplit]; last done; iExists interp; iFrame "#";auto; iSplit.
              * iPureIntro; intros w; apply interp_persistent.
              * rewrite /write_cond /=; iNext ; iModIntro; iIntros (w) "$".
              * iPureIntro; intros w; apply interp_persistent.
              * rewrite /write_cond /=; iNext ; iModIntro; iIntros (w) "$".
            + rewrite /safe_to_unseal.
              iEval (rewrite finz_seq_between_cons //).
              iEval (rewrite finz_seq_between_cons //).
              replace ((ot_ec ^+ 1) ^+ 1)%f with (ot_ec ^+ 2)%ot by solve_finz.
              iEval (rewrite finz_seq_between_empty //).
              rewrite 2!big_sepL_cons big_sepL_nil.
              iSplit; [|iSplit]; last done; iExists interp; iFrame "#";auto.
              * rewrite /read_cond /=; iNext ; iModIntro; iIntros (w) "$".
              * rewrite /read_cond /=; iNext ; iModIntro; iIntros (w) "$".
            + rewrite /safe_to_attest.
              iEval (rewrite finz_seq_between_cons //).
              iEval (rewrite finz_seq_between_cons //).
              replace ((ot_ec ^+ 1) ^+ 1)%f with (ot_ec ^+ 2)%ot by solve_finz.
              iEval (rewrite finz_seq_between_empty //).
              rewrite 2!big_sepL_cons big_sepL_nil.
              iSplit; [|iSplit]; last done; iExists Ecn; iFrame "#"; iPureIntro; auto.
              rewrite /tid_of_otype in Htidx |- *.
              rewrite Htidx_even in Htidx.
              assert (Z.even (ot_ec ^+ 1)%f = false) as Heven'.
              { admit. }
              rewrite Heven'.
              by replace ( (ot_ec ^+ 1 ^- 1)%f ) with ot_ec by solve_finz.
          }

          iMod (region_valid_alloc _ RW b_data e_data a_data (v_data + 1)
                  (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec :: lws_data) with
                 "[HPs_data] [Hdata]")
          as "#Hinterp_data_new".
          { done. }
          { done. }
          { rewrite big_sepL_cons; iFrame "#".
            admit.
          }
          { iClear "#". clear.
            admit.
          }

          iMod (region_valid_alloc _ RX b_code e_code a_code (v_code + 1)
                  (LCap RW b_data e_data a_data (v_data + 1) :: lws_code) with
                 "[HPs_code] [Hcode]")
          as "#Hinterp_code_new".
          { done. }
          { done. }
          { rewrite big_sepL_cons; iFrame "#".
            admit.
          }
          { iClear "#". clear.
            admit.
          }

          iAssert (interp (LCap E b_code e_code (b_code ^+ 1)%a (v_code + 1))) as
            "Hinterp_entry_enclave".
          { iApply (interp_weakening with "IH Hinterp_code_new"); eauto; solve_addr. }

          rewrite (insert_commute _ rcode PC) // (insert_commute _ rdata PC) // insert_insert.
          iApply wp_pure_step_later; auto.
          iNext; iIntros "H£'".
          iApply ("IH" $! (<[rdata:=LInt 0]> (<[rcode:=LCap E b_code e_code (b_code ^+ 1)%a (v_code + 1)]> lregs)) with "[%] [] [Hregs] [$Hown]"); eauto.
          { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
          {
            iIntros (ri ? Hri Hvs).
            destruct (decide (ri = rdata)); simplify_map_eq; first by rewrite !fixpoint_interp1_eq.
            destruct (decide (ri = rcode)); simplify_map_eq; first by rewrite !fixpoint_interp1_eq.
            iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
          }
  Admitted.




          (* iApply wp_pure_step_later; auto. *)

          (* in the custom enclaves *)
        (* TODO I_ECn ∈ dom custom_enclaves *)

      (* iDestruct (read_allowed_inv with "Hinterp_wdata") as "HH". *)

      (* iEval (rewrite fixpoint_interp1_eq). *)
      (* (* wsrc is a lcap *) *)
      (* destruct (is_sealed wsrc) eqn:His_sealed. *)
      (* + (* wsrc is either E-cap or sealed cap *) *)
      (*   rewrite memMap_resource_1. *)
      (*   iApply (wp_isunique with "[$Hmap $Ha]") *)
      (*   ; eauto *)
      (*   ; [ by simplify_map_eq *)
      (*     | rewrite /subseteq /map_subseteq /set_subseteq_instance *)
      (*       ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto *)
      (*     | by simplify_map_eq *)
      (*     |]. *)
      (*   iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)". *)
      (*   inversion Hspec as [| ? Hlwsrc Hcannot_read Hunique_regs Hmem' Hincr_PC | |] *)
      (*   ; simplify_map_eq. *)
      (*   { (* case sweep success cap : contradiction *) *)
      (*     rewrite H0 in Hlregs_src; simplify_map_eq. *)
      (*     by destruct p0 ; cbn in * ; try congruence. *)
      (*   } *)
      (*   { (* case sweep success is_sealed *) *)
      (*     cbn in *; simplify_eq. *)
      (*     rewrite -memMap_resource_1. *)
      (*     iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro]. *)
      (*     iApply wp_pure_step_later; auto. *)
      (*     iNext; iIntros "_". *)
      (*     incrementLPC_inv; simplify_map_eq. *)
      (*     assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq). *)
      (*     simplify_map_eq. *)
      (*     rewrite (insert_commute _ _ PC) // insert_insert. *)
      (*     iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto. *)
      (*     { intro; by repeat (rewrite lookup_insert_is_Some'; right). } *)
      (*     { *)
      (*       iIntros (ri ? Hri Hvs). *)
      (*       destruct (decide (ri = dst)); simplify_map_eq. *)
      (*       by rewrite !fixpoint_interp1_eq. *)
      (*       iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto. *)
      (*     } *)
      (*     iModIntro. *)
      (*     rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto. *)
      (*   } *)
      (*   { (* case sweep false*) *)
      (*     cbn in *; simplify_eq. *)
      (*     rewrite -memMap_resource_1. *)
      (*     iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro]. *)
      (*     iApply wp_pure_step_later; auto. *)
      (*     iNext; iIntros "_". *)
      (*     incrementLPC_inv; simplify_map_eq. *)
      (*     assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq). *)
      (*     simplify_map_eq. *)
      (*     rewrite (insert_commute _ _ PC) // insert_insert. *)
      (*     iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto. *)
      (*     { intro; by repeat (rewrite lookup_insert_is_Some'; right). } *)
      (*     { *)
      (*       iIntros (ri ? Hri Hvs). *)
      (*       destruct (decide (ri = dst)); simplify_map_eq. *)
      (*       by rewrite !fixpoint_interp1_eq. *)
      (*       iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto. *)
      (*     } *)
      (*     iModIntro. *)
      (*     rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto. *)
      (*   } *)
      (*   {  (* Fail *) *)
      (*     rewrite -memMap_resource_1. *)
      (*     iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro]. *)
      (*     iApply wp_pure_step_later; auto. *)
      (*     iNext; iIntros "_"; iApply wp_value; auto. *)
      (*     iIntros; discriminate. *)
      (*   } *)
      (* + (* wsrc is an actual capability, with at least read permission *) *)
      (*   destruct_lword wsrc ; simplify_eq ; clear Hcap. *)
      (*   destruct (readAllowed p0) eqn:Hread; cycle 1. *)
      (*   { (* Case O-cap *) *)
      (*     destruct p0 eqn:Hp0 ; cbn in His_sealed, Hread ; try congruence. *)
      (*     rewrite memMap_resource_1. *)
      (*     iApply (wp_isunique with "[$Hmap $Ha]") *)
      (*     ; eauto *)
      (*     ; [ by simplify_map_eq *)
      (*       | rewrite /subseteq /map_subseteq /set_subseteq_instance *)
      (*         ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto *)
      (*       | by simplify_map_eq *)
      (*       |]. *)
      (*     iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)". *)
      (*     inversion Hspec as *)
      (*       [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC *)
      (*       | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC *)
      (*       | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hmem' Hincr_PC *)
      (*       | ? ? Hfail] *)
      (*     ; simplify_map_eq *)
      (*     ; try (rewrite Hlregs_src in Hlwsrc ; simplify_eq) *)
      (*     ; cycle 1. *)
      (*     { (* case sweep false*) *)
      (*       cbn in *; simplify_eq. *)
      (*       rewrite -memMap_resource_1. *)
      (*       iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro]. *)
      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_". *)
      (*       incrementLPC_inv; simplify_map_eq. *)
      (*       assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq). *)
      (*       simplify_map_eq. *)
      (*       rewrite (insert_commute _ _ PC) // insert_insert. *)
      (*       iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto. *)
      (*       { intro; by repeat (rewrite lookup_insert_is_Some'; right). } *)
      (*       { *)
      (*         iIntros (ri ? Hri Hvs). *)
      (*         destruct (decide (ri = dst)); simplify_map_eq. *)
      (*         by rewrite !fixpoint_interp1_eq. *)
      (*         iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto. *)
      (*       } *)
      (*       iModIntro. *)
      (*       rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto. *)
      (*     } *)
      (*     {  (* Fail *) *)
      (*       rewrite -memMap_resource_1. *)
      (*       iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro]. *)
      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_"; iApply wp_value; auto. *)
      (*       iIntros; discriminate. *)
      (*     } *)
      (*     { (* case sweep true cap *) *)
      (*       assert ( lmem' !! (a, v) = Some lw ) as Hmem'_pca. *)
      (*       { eapply is_valid_updated_lmemory_preserves_lmem; eauto. *)
      (*         apply finz_seq_between_NoDup. *)
      (*         by simplify_map_eq. *)
      (*       } *)
      (*       rewrite -(insert_id lmem' (a,v) lw). *)
      (*       iDestruct (big_sepM_insert_delete with "Hmem") as "[Hmem _]". *)
      (*       iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro]. *)
      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_". *)
      (*       incrementLPC_inv; simplify_map_eq. *)
      (*       assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq). *)
      (*       simplify_map_eq. *)
      (*       do 2 (rewrite (insert_commute _ _ PC) //) ; rewrite insert_insert. *)
      (*       iApply ("IH" $! (<[dst := (LInt 1)]> (<[src:=LCap p1 b1 e1 a1 (v1 + 1)]> lregs)) *)
      (*                with "[%] [] [Hmap] [$Hown]"); eauto. *)
      (*       { intro; by repeat (rewrite lookup_insert_is_Some'; right). } *)
      (*       { *)
      (*         iIntros (ri ? Hri Hvs). *)
      (*         destruct (decide (ri = dst)) ; simplify_map_eq *)
      (*         ; first by rewrite !fixpoint_interp1_eq. *)
      (*         destruct (decide (ri = src)) ; rewrite Hlwsrc' in Hlregs_src ; simplify_map_eq *)
      (*         ; first by rewrite !fixpoint_interp1_eq. *)
      (*         iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto. *)
      (*       } *)
      (*       rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto. *)
      (*       done. *)
      (*     } *)
      (*   } *)
      (*   clear His_sealed. *)

      (*   assert (NoDup (finz.seq_between b0 e0)) as HNoDup_range by apply finz_seq_between_NoDup. *)

      (*   destruct (decide (a ∈ finz.seq_between b0 e0)) as [ Ha_in_src | Ha_notin_src ]. *)
      (*   * (* There's no need to open the invariant of the region, *)
      (*        because we know that pc and src overlap *) *)
      (*     rewrite memMap_resource_1. *)
      (*     iApply (wp_isunique with "[$Hmap $Ha]") *)
      (*     ; eauto *)
      (*     ; [ by simplify_map_eq *)
      (*       | rewrite /subseteq /map_subseteq /set_subseteq_instance *)
      (*         ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto *)
      (*       | by simplify_map_eq *)
      (*       |]. *)
      (*     iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)". *)
      (*     inversion Hspec as *)
      (*       [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC *)
      (*       | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC *)
      (*       | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hmem' Hincr_PC *)
      (*       | ? ? Hfail] *)
      (*     ; simplify_map_eq *)
      (*     ; try (rewrite Hlregs_src in Hlwsrc' ; simplify_eq) *)
      (*     ; try (rewrite Hlregs_src in Hlwsrc ; simplify_eq). *)
      (*     { (* case sweep true cap : contradiction *) *)
      (*       exfalso. clear -Hunique_regs Ha_in_src Hsrc_neq_pc Hbae. *)
      (*       apply map_Forall_insert_1_1 in Hunique_regs. *)
      (*       rewrite decide_False //= in Hunique_regs. *)
      (*       apply Hunique_regs. *)
      (*       rewrite elem_of_finz_seq_between in Ha_in_src. *)
      (*       destruct Ha_in_src; cbn. *)
      (*       destruct (b1 <? b)%a; solve_addr. *)
      (*     } *)
      (*     { (* case sweep true is_sealed : contradiction *) *)
      (*       exfalso. *)
      (*       clear -Hread Hnot_sealed. *)
      (*       by destruct p0 ; cbn in *. *)
      (*     } *)
      (*     { (* case sweep false*) *)
      (*       cbn in *; simplify_eq. *)
      (*       rewrite -memMap_resource_1. *)
      (*       iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro]. *)
      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_". *)
      (*       incrementLPC_inv; simplify_map_eq. *)
      (*       assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq). *)
      (*       simplify_map_eq. *)
      (*       rewrite (insert_commute _ _ PC) // insert_insert. *)
      (*       iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto. *)
      (*       { intro; by repeat (rewrite lookup_insert_is_Some'; right). } *)
      (*       { *)
      (*         iIntros (ri ? Hri Hvs). *)
      (*         destruct (decide (ri = dst)); simplify_map_eq. *)
      (*         by rewrite !fixpoint_interp1_eq. *)
      (*         iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto. *)
      (*       } *)
      (*       iModIntro. *)
      (*       rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto. *)
      (*     } *)
      (*     {  (* case fail *) *)
      (*       rewrite -memMap_resource_1. *)
      (*       iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro]. *)
      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_"; iApply wp_value; auto. *)
      (*       iIntros; discriminate. *)
      (*     } *)

      (*   * (* src ≠ PC *) *)
      (*     iMod (interp_open_region_notin with "Hinterp_src") *)
      (*       as (Ps lws) "(%Hlen_Ps & %Hlen_lws & %Hpers & Hrange & HPrange & #Hread_cond & Hcls_src)"; auto. *)
      (*     { *)
      (*       apply Forall_forall; intros a' Ha'. *)
      (*       assert (a' ≠ a) by (intro ; set_solver). *)
      (*       apply namespaces.coPset_subseteq_difference_r; [solve_ndisj|set_solver]. *)
      (*     } *)

      (*     iDestruct (big_sepM_insert with "[$Hrange $Ha]") as "Hmem" *)
      (*     ; first ( by apply logical_range_notin ). *)

      (*     iApply (wp_isunique with "[$Hmap $Hmem]") *)
      (*     ; eauto *)
      (*     ; [ by simplify_map_eq *)
      (*       | rewrite /subseteq /map_subseteq /set_subseteq_instance *)
      (*         ; intros rr _; apply elem_of_dom *)
      (*         ; rewrite lookup_insert_is_Some'; *)
      (*         eauto *)
      (*       | by simplify_map_eq *)
      (*       |]. *)
      (*     iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)". *)
      (*     destruct Hspec as *)
      (*       [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC *)
      (*       | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC *)
      (*       | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hmem' Hincr_PC *)
      (*       | ? ? Hfail] *)
      (*     ; simplify_map_eq *)
      (*     ; try (rewrite Hlwsrc' in Hlregs_src; simplify_eq) *)
      (*     ; try (rewrite Hlwsrc in Hlregs_src; simplify_eq) *)
      (*     ; try (cbn in Hlwsrc' ; simplify_eq) *)
      (*     ; cycle 1. *)
      (*     { (* Sweep false  *) *)
      (*       iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]" *)
      (*       ; first (eapply logical_range_notin; eauto). *)
      (*       iMod ("Hcls_src" with "[Hmem HPrange]") as "_". *)
      (*       { *)
      (*         iNext. *)
      (*         iApply region_inv_construct; auto. *)
      (*       } *)
      (*       iModIntro. *)
      (*       iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame). *)
      (*       iModIntro. *)
      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_". *)
      (*       incrementLPC_inv; simplify_map_eq. *)
      (*       assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq). *)
      (*       simplify_map_eq. *)
      (*       rewrite (insert_commute _ _ PC) // insert_insert. *)
      (*       iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto. *)
      (*       { intro; by repeat (rewrite lookup_insert_is_Some'; right). } *)
      (*       { *)
      (*         iIntros (ri ? Hri Hvs). *)
      (*         destruct (decide (ri = dst)); simplify_map_eq. *)
      (*         by rewrite !fixpoint_interp1_eq. *)
      (*         iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto. *)
      (*       } *)
      (*       iModIntro. *)
      (*       rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto. *)
      (*     } *)
      (*    { (* Sweep false  *) *)
      (*       iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]" *)
      (*       ; first (eapply logical_range_notin; eauto). *)
      (*       iMod ("Hcls_src" with "[Hmem HPrange]") as "_". *)
      (*       { *)
      (*         iNext. *)
      (*         iApply region_inv_construct; auto. *)
      (*       } *)
      (*       iModIntro. *)
      (*       iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame). *)
      (*       iModIntro. *)
      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_". *)
      (*       incrementLPC_inv; simplify_map_eq. *)
      (*       assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq). *)
      (*       simplify_map_eq. *)
      (*       rewrite (insert_commute _ _ PC) // insert_insert. *)
      (*       iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto. *)
      (*       { intro; by repeat (rewrite lookup_insert_is_Some'; right). } *)
      (*       { *)
      (*         iIntros (ri ? Hri Hvs). *)
      (*         destruct (decide (ri = dst)); simplify_map_eq. *)
      (*         by rewrite !fixpoint_interp1_eq. *)
      (*         iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto. *)
      (*       } *)
      (*       iModIntro. *)
      (*       rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto. *)
      (*     } *)
      (*     { (* Fail *) *)
      (*       iDestruct (big_sepM_insert with "Hmem") as "[Ha Hrange]" *)
      (*       ; first ( by apply logical_range_notin ). *)
      (*       iMod ("Hcls_src" with "[Hrange HPrange]") as "_". *)
      (*       { *)
      (*         iNext. *)
      (*         iApply region_inv_construct; auto. *)
      (*       } *)
      (*       iModIntro. *)
      (*       iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame). *)
      (*       iModIntro. *)
      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_"; iApply wp_value; auto. *)
      (*       iIntros; discriminate. *)
      (*     } *)

      (*     { (* Sweep true  *) *)

  (* TODO SEE HERE *)
      (*       incrementLPC_inv *)
      (*         as (p_pc' & b_pc' & e_pc' &a_pc' &v_pc' & ? & HPC & Z & Hregs') *)
      (*       ; simplify_map_eq. *)
      (*       assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq); simplify_map_eq. *)
      (*       do 2 (rewrite (insert_commute _ _ PC) //); rewrite insert_insert. *)

      (*       assert ( lmem' !! (a_pc', v_pc') = Some lw ) as Hmem'_pca. *)
      (*       { eapply is_valid_updated_lmemory_preserves_lmem; eauto. *)
      (*         by simplify_map_eq. *)
      (*       } *)

      (*       assert ( logical_range_map b0 e0 lws v0 ⊆ lmem' ) *)
      (*         as Hmem'_be. *)
      (*       { *)
      (*         eapply is_valid_updated_lmemory_lmem_incl with (la := (finz.seq_between b0 e0)) *)
      (*         ; eauto. *)
      (*         eapply is_valid_updated_lmemory_insert; eauto. *)
      (*         eapply logical_range_notin; eauto. *)
      (*         eapply Forall_forall; intros a Ha. *)
      (*         eapply logical_range_version_neq; eauto; last lia. *)
      (*       } *)
      (*       assert *)
      (*         (logical_range_map b0 e0 lws (v0 + 1) ⊆ lmem') *)
      (*         as Hmem'_be_next. *)
      (*       { clear -Hupd Hlen_lws HNoDup_range Ha_notin_src. *)
      (*         eapply map_subseteq_spec; intros [a' v'] lw' Hlw'. *)
      (*         assert (v' = v0+1 /\ (a' ∈ (finz.seq_between b0 e0))) as [? Ha'_in_be] *)
      (*             by (eapply logical_range_map_some_inv; eauto); simplify_eq. *)
      (*         destruct Hupd. *)
      (*         eapply lookup_weaken; last eauto. *)
      (*         rewrite update_version_region_preserves_lmem_next; eauto. *)
      (*         all: rewrite lookup_insert_ne //=; last (intro ; set_solver). *)
      (*         erewrite logical_range_map_lookup_versions; eauto. *)
      (*         eapply logical_range_version_neq; eauto; lia. *)
      (*       } *)

      (*       rewrite -(insert_id lmem' (a_pc', v_pc') lw); auto. *)
      (*       iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha Hmem]". *)
      (*       eapply delete_subseteq_r with (k := ((a_pc', v_pc') : LAddr)) in Hmem'_be *)
      (*       ; last (eapply logical_region_notin; eauto). *)
      (*       iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange Hmem]" *)
      (*       ; first (eapply Hmem'_be). *)
      (*       eapply delete_subseteq_r with (k := ((a_pc', v_pc') : LAddr)) in Hmem'_be_next *)
      (*       ; last (eapply logical_region_notin ; eauto). *)
      (*       eapply delete_subseteq_list_r *)
      (*         with (m3 := list_to_map (zip (map (λ a : Addr, (a, v0)) (finz.seq_between b0 e0)) lws)) *)
      (*         in Hmem'_be_next *)
      (*       ; eauto *)
      (*       ; last (by eapply update_logical_memory_region_disjoint). *)
      (*       iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange' Hmem]" *)
      (*       ; first (eapply Hmem'_be_next); iClear "Hmem". *)
      (*       iDestruct "HPrange" as "#HPrange". *)

      (*       iMod (region_valid_alloc _ b0 e0 a0 (v0 +1) lws p0 *)
      (*              with "[HPrange] [Hrange']") *)
      (*       as "#Hinterp_src_next". *)
      (*       { destruct p0 ; cbn in * ; try congruence; done. } *)
      (*       { iDestruct (big_sepL2_const_sepL_r _ lws with "[Hread_cond]") as "Hread_P0". *)
      (*         iSplit ; last iFrame "Hread_cond". *)
      (*         by rewrite Hlen_lws. *)
      (*         cbn. *)
      (*         iDestruct ( big_sepL2_sep_sepL_r with "[$Hread_cond $HPrange]") as "HPs". *)
      (*         iClear *)
      (*           "IH Hinv Hinva Hreg Hread Hwrite Hinterp_src Hread_P0 HPrange". *)
      (*         iDestruct (big_sepL2_alt with "HPs") as "[_ HPs']". *)
      (*         iAssert ( *)
      (*             (∀ (k : nat) (x0 : leibnizO LWord * D), *)
      (*                 ⌜zip lws Ps !! k = Some x0⌝ *)
      (*                 → x0.2 x0.1 ∗ □ (∀ lw0 : LWord, x0.2 lw0 -∗ fixpoint interp1 lw0) -∗ interp x0.1) *)
      (*           )%I as "bla". *)
      (*         { iIntros (? ? ?) "[Ha Hpa]"; by iDestruct ("Hpa" with "Ha") as "?". } *)
      (*         iDestruct (big_sepL_impl _ (fun _ xy => interp xy.1) with "HPs' bla" *)
      (*                   ) as "blaa". *)
      (*         iDestruct (big_sepL2_alt (fun _ lw _ => interp lw) lws Ps with "[$blaa]") as "blaaa". *)
      (*         by rewrite Hlen_lws. *)
      (*         by iDestruct (big_sepL2_const_sepL_l (fun _ lw => interp lw) lws Ps with "blaaa") as "[? ?]". *)
      (*       } *)
      (*       { iClear "#". clear -Hlen_Ps Hlen_lws. *)
      (*         iApply big_sepL2_alt. *)
      (*         iSplit; first (iPureIntro; rewrite map_length; lia). *)
      (*         iDestruct (big_sepM_list_to_map with "Hrange'") as "?" ; last iFrame. *)
      (*         rewrite fst_zip; first (apply NoDup_logical_region). *)
      (*         rewrite /logical_region map_length ; lia. *)
      (*       } *)

      (*       iMod ("Hcls_src" with "[Hrange HPrange]") as "_". *)
      (*       { *)
      (*         iNext. *)
      (*         iApply region_inv_construct; auto. *)
      (*       } *)
      (*       iModIntro. *)
      (*       iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame). *)
      (*       iModIntro. *)

      (*       iApply wp_pure_step_later; auto. *)
      (*       iNext; iIntros "_". *)
      (*       simplify_map_eq. *)
      (*       iApply ("IH" $! (<[dst := _]> (<[ src := _ ]> lregs)) with "[%] [] [Hmap] [$Hown]") *)
      (*       ; eauto. *)
      (*       { intro; by repeat (rewrite lookup_insert_is_Some'; right). } *)
      (*       { iIntros (r1 lw1 Hr1 Hlw1). *)
      (*         destruct (decide (r1 = dst)) as [ |Hr1_dst] *)
      (*         ; simplify_map_eq; first (rewrite !fixpoint_interp1_eq //=). *)
      (*         destruct (decide (r1 = src)) as [ |Hr1_src] *)
      (*         ; simplify_map_eq; first done. *)
      (*         iApply "Hreg"; eauto. } *)
      (*       { rewrite !fixpoint_interp1_eq //= ; destruct p_pc'; destruct Hp ; done. } *)
      (*     } *)
  (* Admitted. *)

  (* (** Predicate that defines when the contents of a register can be swept; *)
  (*     i.e. when the register contains a capability with at least R permissions... *) *)
  (* Definition reg_allows_einit_code *)
  (*   (lregs : LReg) (r : RegName) *)
  (*   (p : Perm) (b e a : Addr) (v : Version):= *)
  (*   lregs !! r = Some (LCap p b e a v) ∧ p = RX. *)

  (* Definition code_addresses (a_pc : Addr) (code_la : list Addr) *)
  (*   := (list_remove_elem a_pc code_la). *)
  (* Definition allow_einit_code_mask *)
  (*   (a_pc : Addr) (v_pc : Version) (code_la : list Addr) (code_v : Version): coPset := *)
  (*   compute_mask_region (⊤ ∖ ↑logN.@(a_pc, v_pc)) (code_addresses a_pc code_la) code_v. *)

  (* Lemma allow_einit_code_mask_remove_nodup *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (la_code : list Addr) (v_code : Version) : *)
  (*   NoDup la_code -> *)
  (*   allow_einit_code_mask a_pc v_pc (code_addresses a_pc la_code) v_code = *)
  (*   allow_einit_code_mask a_pc v_pc la_code v_code. *)
  (* Proof. *)
  (*   intros HNoDup. *)
  (*   by rewrite /allow_einit_code_mask /code_addresses list_remove_elem_idem. *)
  (* Qed. *)


  (* Definition interp_list_pred *)
  (*   (lws : list LWord) (Ps : list D) (has_later : bool) : iProp Σ := *)
  (*   ([∗ list] lw;Pw ∈ lws;Ps, (if has_later then ▷ (Pw : D) lw else (Pw : D) lw)). *)

  (* Definition interp_list_persistent *)
  (*   (lws : list LWord) (Ps : list D) : iProp Σ := *)
  (*   ( ⌜ Persistent ([∗ list] lw;Pw ∈ lws;Ps, (Pw : D) lw) ⌝ ). *)

  (* Definition interp_list_readcond *)
  (*   (lws : list LWord) (Ps : list D) (has_later : bool) : iProp Σ := *)
  (*   ( if has_later *)
  (*     then [∗ list] Pa ∈ Ps, read_cond Pa interp *)
  (*     else [∗ list] Pa ∈ Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw) *)
  (*   )%I. *)

  (* Definition interp_list_close *)
  (*   (la : list Addr) (Ps : list D) (v : Version) (E E' : coPset) : iProp Σ := *)
  (*   ( (▷ ([∗ list] a_Pa ∈ zip la Ps, (interp_ref_inv a_Pa.1 v a_Pa.2))) ={E', E }=∗ True). *)

  (* (* this will help us close the invariant again... *) *)
  (* (* it states which properties are enforced on all the lws *) *)
  (* Definition resources_open_invariant_code *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (la_code : list Addr) (v_code : Version) *)
  (*   (lws_code : list LWord) (Ps_code : list D) *)
  (*   (has_later : bool) *)
  (*   : iProp Σ := *)

  (*   let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_code_mask a_pc v_pc la_code v_code in *)

  (*   interp_list_pred lws_code Ps_code has_later *)
  (*   ∗ interp_list_persistent lws_code Ps_code *)
  (*   ∗ interp_list_readcond lws_code Ps_code has_later *)
  (*   ∗ interp_list_close la_code Ps_code v_code E0 E1. *)

  (* Definition allows_einit_code (lregs : LReg) (r : RegName) := *)
  (*   ∀ p b e a v, *)
  (*   lregs !! r = Some (LCap p b e a v) *)
  (*   -> readAllowed p = true *)
  (*   -> (finz.seq_between b e) ## reserved_addresses. *)

  (* Definition allows_einit_data (lmem : LMem) (b : Addr) (v : Version) := *)
  (*   ∀ p' b' e' a' v', *)
  (*   lmem !! (b,v) = Some (LCap p' b' e' a' v') *)
  (*   -> readAllowed p' = true *)
  (*   -> (finz.seq_between b' e') ## reserved_addresses. *)

  (* Definition einit_code_mask_cond *)
  (*   (lregs : LReg) (src : RegName) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) *)
  (*   (a_pc : Addr) (v_pc : Version) := *)
  (*   decide (reg_allows_einit_code lregs src p_code b_code e_code a_code v_code *)
  (*           /\ (src = PC \/ a_pc ∉ (finz.seq_between b_code e_code))). *)

  (* Definition allow_einit_code_resources *)
  (*   (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) *)
  (*   := *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_code_mask a_pc v_pc la_code v_code in *)

  (*   (⌜read_reg_inr lregs src p_code b_code e_code a_code v_code⌝ ∗ *)
  (*    ⌜allows_einit_code lregs src⌝ ∗ *)
  (*    if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
  (*    then *)
  (*     (|={E0, E1}=> (* we open this invariant with all the points-tos from b to e *) *)
  (*        ∃ (lws_code :list LWord), *)
  (*        ⌜ length lws_code = length la_code ⌝ *)
  (*        ∗ ([∗ map] la↦lw ∈ (logical_region_map la_code lws_code v_code), la ↦ₐ lw) (* here you get all the points-tos *) *)
  (*        ∗ resources_open_invariant_code a_pc v_pc la_code v_code lws_code Ps_code true)%I *)
  (*    else True)%I. *)


  (* Lemma create_einit_code_resources *)
  (*   (lregs : LReg) (src : RegName) *)
  (*   (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) : *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)

  (*   read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_code b_code e_code a_code v_code *)
  (*   -> a_pc ∈ finz.seq_between b_pc e_pc *)
  (*   → (∀ (r : RegName) lw, ⌜r ≠ PC⌝ → ⌜lregs !! r = Some lw⌝ → (fixpoint interp1) lw) *)
  (*   -∗ interp (LCap p_pc b_pc e_pc a_pc v_pc) *)
  (*   -∗ (∃ (Ps_code : list D), *)
  (*          ⌜ length la_code = length Ps_code ⌝ *)
  (*          ∗ allow_einit_code_resources *)
  (*              (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src *)
  (*              a_pc v_pc *)
  (*              p_code b_code e_code a_code v_code Ps_code). *)
  (* Proof. *)
  (*   intros * Hread Hapc_inbounds. *)
  (*   iIntros "#Hreg #Hinterp_pc". *)
  (*   apply list_remove_elem_in in Hapc_inbounds. *)
  (*   destruct Hapc_inbounds as (la' & <- & Hapc_inbounds). *)
  (*   rewrite /allow_einit_code_resources /einit_code_mask_cond. *)
  (*   case_decide as Hallows; cycle 1. *)
  (*   { iExists (repeat (λne _, True%I) (length la_code)); iFrame "%". *)
  (*     iSplit; first by rewrite repeat_length. *)
  (*     iSplit; last done. *)
  (*     iIntros (p b e a v Hlv HreadAllowed). *)
  (*     destruct (decide (src = PC)) as [-> | Hneq_src_pc] ; simplify_map_eq. *)
  (*     + iDestruct (readAllowed_not_reserved with "Hinterp_pc") as "%"; auto. *)
  (*     + iAssert (interp (LCap p b e a v)) as "Hinterp_src". *)
  (*       { iApply "Hreg"; eauto. } *)
  (*       iDestruct (readAllowed_not_reserved with "Hinterp_src") as "%"; auto. *)
  (*   } *)
  (*   iFrame "%". *)
  (*   cbn in Hapc_inbounds. *)
  (*   apply bind_Some in Hapc_inbounds. *)
  (*   destruct Hapc_inbounds as (? & Hrem & ?) ; simplify_eq. *)
  (*   rewrite /reg_allows_einit_code in Hallows. *)
  (*   destruct Hallows as ( (Hreg & HreadAllowed) & Hdecide). *)
  (*   assert (la_code ⊆+ finz.seq_between b_code e_code) *)
  (*     as Hla_subseteq by apply list_remove_elem_submsteq. *)
  (*   assert (NoDup la_code) as Hla_NoDup by (by apply list_remove_elem_NoDup). *)
  (*   rewrite /read_reg_inr in Hread; simplify_map_eq. *)

  (*   destruct (decide (src = PC)) as [-> | Hneq_src_pc] ; simplify_map_eq. *)
  (*   (* src = PC *) *)
  (*   - rewrite /allow_einit_code_mask /code_addresses. *)
  (*     rewrite list_remove_elem_idem; last done. *)
  (*     iDestruct (interp_open_region $ (⊤ ∖ ↑logN.@(a_code, v_code)) with "Hinterp_pc") *)
  (*       as (Ps) "[%Hlen_Ps Hmod]" ; eauto. *)
  (*     { eapply Forall_forall. intros a' Ha'. *)
  (*       subst la_code. *)
  (*       eapply namespaces.coPset_subseteq_difference_r; auto. *)
  (*       assert (a' ≠ a_code). *)
  (*       { *)
  (*         eapply list_remove_elem_neq; cycle 1 ; eauto. *)
  (*         apply list_remove_Some in Hrem. *)
  (*         setoid_rewrite Hrem; set_solver. *)
  (*       } *)
  (*       solve_ndisj. *)
  (*     } *)
  (*     iExists Ps. *)
  (*     iSplit ; first by subst. *)
  (*     iSplit. *)
  (*     { iIntros (p b e a v Hsrc HreadAllowedp). *)
  (*       iDestruct (readAllowed_not_reserved with "Hinterp_pc") as "%"; auto. *)
  (*       by simplify_map_eq. *)
  (*     } *)
  (*     iMod "Hmod". *)
  (*     iDestruct "Hmod" as (lws) "(%Hlws & %Hpers & Hmem & HPs & HPs' & Hclose)". *)
  (*     iExists lws. *)
  (*     iFrame; iFrame "%". *)
  (*     iModIntro. *)
  (*     iIntros "H". *)
  (*     iDestruct ("Hclose" with "H") as "Hclose". *)
  (*     rewrite /allow_einit_code_mask /code_addresses. *)
  (*     rewrite list_remove_elem_notin. *)
  (*     subst la_code. *)
  (*     iFrame. *)
  (*     apply not_elemof_list_remove_elem; done. *)

  (*   (* src ≠ PC *) *)
  (*   - destruct Hdecide as [Hcontra|Ha_notin_rem] ; first contradiction. *)
  (*     iAssert (interp (LCap RX b_code e_code a_code v_code)) as "#Hinterp_code" *)
  (*     ; first (iApply "Hreg"; eauto). *)
  (*     iDestruct (interp_open_region $ (⊤ ∖ ↑logN.@(a_pc, v_pc)) with "Hinterp_code") *)
  (*       as (Ps) "[%Hlen_Ps Hmod]" ; eauto. *)
  (*     { apply Forall_forall; intros a' Ha'. *)
  (*       subst la_code. *)
  (*       assert (a' ≠ a_pc). *)
  (*       { intro ; subst. by apply not_elemof_list_remove_elem in Ha'. } *)
  (*       apply namespaces.coPset_subseteq_difference_r; [solve_ndisj|set_solver]. *)
  (*     } *)
  (*     iExists Ps. *)
  (*     iSplit ; first by subst. *)
  (*     iSplit. *)
  (*     { iIntros (p b e a v Hsrc HreadAllowedp). *)
  (*       iDestruct (readAllowed_not_reserved with "Hinterp_code") as "%"; auto. *)
  (*       by simplify_map_eq. *)
  (*     } *)
  (*     iMod "Hmod". *)
  (*     rewrite allow_einit_code_mask_remove_nodup; auto. *)
  (*     iDestruct "Hmod" as (lws) "(%Hlws & %Hpers & Hmem & HPs & HPs' & Hclose)". *)
  (*     iExists lws. *)
  (*     iFrame; iFrame "%". *)
  (*     iModIntro. *)
  (*     iIntros "H". *)
  (*     iDestruct ("Hclose" with "H") as "Hclose". *)
  (*     by rewrite allow_einit_code_mask_remove_nodup. *)
  (* Qed. *)

  (* Definition allow_einit_code_mem *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) *)
  (*   (has_later : bool) := *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)

  (*   (⌜read_reg_inr lregs src p_code b_code e_code a_code v_code⌝ ∗ *)
  (*    if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
  (*    then (∃ (lws_code : list LWord), *)
  (*             ⌜length lws_code = length la_code⌝ *)
  (*             ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> (logical_region_map la_code lws_code v_code)⌝ *)
  (*             ∗ resources_open_invariant_code a_pc v_pc la_code v_code lws_code Ps_code has_later)%I *)
  (*    else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I. *)

  (* Lemma einit_code_resources_implies_mem_map *)
  (*   (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) *)
  (*   : *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_code_mask a_pc v_pc la_code v_code in *)

  (*   allow_einit_code_resources lregs src a_pc v_pc p_code b_code e_code a_code v_code Ps_code *)
  (*   -∗ (a_pc, v_pc) ↦ₐ lw_pc *)
  (*   ={ E0, *)
  (*        if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
  (*        then E1 *)
  (*        else E0 *)
  (*     }=∗ *)
  (*   ∃ lmem : LMem, *)
  (*     allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code true *)
  (*     ∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw). *)
  (* Proof. *)
  (*   intros *. *)
  (*   iIntros "HSweepRes Ha_pc". *)
  (*   iDestruct "HSweepRes" as "(%Hread & [ %Hreserved HSweepRes ] )". *)
  (*   subst E1. *)
  (*   rewrite /einit_code_mask_cond. *)
  (*   case_decide as Hallows; cycle 1. *)
  (*     - iExists _. *)
  (*       iSplitR "Ha_pc". *)
  (*       + iFrame "%". *)
  (*         rewrite /einit_code_mask_cond; case_decide; first by exfalso. auto. *)
  (*       + iModIntro. by iApply memMap_resource_1. *)
  (*     - iMod "HSweepRes" as (lws) "(%Hlws & Hmem & HSweepRest)". *)
  (*       iExists _. *)
  (*       iSplitL "HSweepRest". *)
  (*       * iFrame "%". *)
  (*         rewrite decide_True; auto. *)
  (*       * iModIntro. *)
  (*         destruct Hallows as ((Hrinr & Hra) & Hne). *)
  (*         iDestruct (big_sepM_insert with "[$Hmem $Ha_pc]") as "Hmem" ; cycle 1 ; auto. *)
  (*         rewrite /logical_region_map. *)
  (*         apply not_elem_of_list_to_map_1. *)
  (*         rewrite fst_zip. *)
  (*         2: { rewrite Hlws /logical_region fmap_length; lia. } *)
  (*         rewrite /logical_region. *)
  (*         intro Hcontra. clear -Hcontra. *)
  (*         eapply elem_of_list_fmap_2 in Hcontra. *)
  (*         destruct Hcontra as (a & Heq & Hcontra) ; simplify_eq. *)
  (*         apply not_elemof_list_remove_elem in Hcontra; auto. *)
  (* Qed. *)


  (* Lemma mem_map_implies_pure_conds *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) *)
  (*   (Ps_code : list D) (has_later : bool) : *)
  (*   allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code has_later *)
  (*   -∗ ⌜lmem !! (a_pc, v_pc) = Some lw_pc⌝. *)
  (* Proof. *)
  (*   iIntros "(% & HSweepRes)". *)
  (*   rewrite /einit_code_mask_cond. *)
  (*   case_decide as Hallows. *)
  (*   - pose (Hallows' := Hallows). *)
  (*     destruct Hallows' as ((Hreg & Hread) & Hdecide). *)
  (*     iDestruct "HSweepRes" as (lws) "(%Hlen & -> & HSweepRest)". *)
  (*     by simplify_map_eq. *)
  (*   - iDestruct "HSweepRes" as "->". *)
  (*     by simplify_map_eq. *)
  (* Qed. *)

  (* Lemma allow_einit_code_mem_later *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) *)
  (*   (Ps_code : list D) : *)
  (*   allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code true *)
  (*   -∗ ▷ allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code false. *)
  (* Proof. *)
  (*   iIntros "[% HSweepMem]". *)
  (*   rewrite !/allow_einit_code_mem /= /einit_code_mask_cond. iSplit;[auto|]. *)
  (*   case_decide; last (iNext;iFrame). *)
  (*   iApply bi.later_exist_2. iDestruct "HSweepMem" as (lws) "(%&%&HSweepRest)". *)
  (*     iExists lws. *)
  (*     iDestruct "HSweepRest" as "(?&?&?&?)"; iFrame "%∗"; iNext ; iFrame. *)
  (* Qed. *)


    (* iAssert ( ⌜ *)
    (*             if ( einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src a_pc v_pc ) *)
    (*             then (∃ dcap, lmem !! (b_src, v_src) = Some dcap) *)
    (*             else True ⌝ )%I as "%Hdcap". *)
    (* { *)
    (*   rewrite /allow_einit_code_mem. *)
    (*   iDestruct "HEinitCodeMem" as "(_ & HEinitCodeMem)". *)
    (*   match goal with *)
    (*   | _ : _ |- context [ einit_code_mask_cond ?regs ?r ?p ?b ?e ?a ?v ?apc ?vpc] => *)
    (*       set (Hmask := einit_code_mask_cond regs r p b e a v apc vpc) *)
    (*   end. *)
    (*   destruct Hmask as [Hmask|] *)
    (*   ; rewrite /einit_code_mask_cond *)
    (*   ; [ iEval (rewrite decide_True //) | iEval (rewrite decide_False //)] *)
    (*   ; last done. *)
    (*   iDestruct "HEinitCodeMem" as (lws_code) "(%Hlength_lws_code & %Hlmem & _)"; subst. *)
    (*   iPureIntro. *)
    (*   destruct Hmask as [Hreg_allow Hcond]. *)
    (*   destruct Hcond as [-> | Hapc]. *)
    (*   - rewrite /reg_allows_einit_code in Hreg_allow; simplify_map_eq. *)
    (*     destruct Hreg_allow as [? ->]; simplify_eq. *)
    (*     destruct (decide ( b_src = a_src )) as [-> | Hbsrc]. *)
    (*     + by exists lw_pc; simplify_map_eq. *)
    (*     + destruct lws_code. *)
    (*       ++ exfalso. *)
    (*          cbn in *. *)
    (*          symmetry in Hlength_lws_code. *)
    (*          apply length_zero_iff_nil in Hlength_lws_code. *)
    (*          rewrite /code_addresses in Hlength_lws_code. *)
    (*          assert (b_src ∈  list_remove_elem a_src (finz.seq_between b_src e_src)) as Hcontra. *)
    (*          { admit. } *)
    (*          rewrite Hlength_lws_code in Hcontra. *)
    (*          set_solver. *)
    (*       ++ exists l. *)
    (*          rewrite lookup_insert_ne. *)
    (*          2:{ intro ; simplify_eq. } *)
    (*          rewrite /logical_region_map. *)
    (*          apply elem_of_list_to_map_1. *)
    (*          admit. *)
    (*          admit. *)
    (*   - destruct lws_code. *)
    (*     ++ exfalso. *)
    (*        cbn in *. *)
    (*        symmetry in Hlength_lws_code. *)
    (*        apply length_zero_iff_nil in Hlength_lws_code. *)
    (*        rewrite /code_addresses in Hlength_lws_code. *)
    (*        rewrite list_remove_elem_notin in Hlength_lws_code; auto. *)

    (*        assert (b_src ∈  list_remove_elem a_src (finz.seq_between b_src e_src)) as Hcontra. *)
    (*          { admit. } *)
    (*          rewrite Hlength_lws_code in Hcontra. *)
    (*          set_solver. *)
    (*       ++ exists l. *)
    (*          rewrite lookup_insert_ne. *)
    (*          2:{ intro ; simplify_eq. } *)
    (*          rewrite /logical_region_map. *)
    (*          apply elem_of_list_to_map_1. *)
    (*          admit. *)
    (*          admit. *)

    (*       by exists lw_pc; simplify_map_eq. *)




    (*   admit. *)
    (*   + rewrite /einit_code_mask_cond. *)
    (*   set ( Hmask := (einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src a_pc v_pc) ). *)
    (*   destruct *)
    (*     (einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src *)
    (*        a_src v_src a_pc v_pc) *)
    (*       as [Hmask|Hmask]. *)


    (* } *)


  (* Lemma einit_case (lregs : leibnizO LReg) *)
  (*   (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version) *)
  (*   (lw_pc : LWord) (src : RegName) (P : D): *)
  (*   ftlr_instr lregs p_pc b_pc e_pc a_pc v_pc lw_pc (EInit src) P. *)
  (* Proof. *)
  (*   intros Hp Hsome HcorrectLPC Hbae Hi. *)
  (*   iIntros "#IH #Hinv #Hinva #Hreg #(Hread & Hwrite & %HpersP) Hown Ha #HP Hcls HPC Hmap". *)
  (*   specialize (HpersP lw_pc). *)
  (*   rewrite delete_insert_delete. *)
  (*   iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /="; *)
  (*     [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. *)

  (*   (* To read out PC's name later, and needed when calling wp_load *) *)
  (*   assert(∀ x : RegName, is_Some (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs !! x)) as Hsome'. *)
  (*   { *)
  (*     intros. destruct (decide (x = PC)) as [Hx|Hx]. *)
  (*     rewrite Hx lookup_insert; unfold is_Some. by eexists. *)
  (*     by rewrite lookup_insert_ne. *)
  (*   } *)

  (*   (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *) *)
  (*   assert (∃ p_src b_src e_src a_src v_src, read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src) *)
  (*     as (p_src & b_src & e_src & a_src & v_src & HV_Src). *)
  (*   { *)
  (*     specialize Hsome' with src as Hsrc. *)
  (*     destruct Hsrc as [wsrc Hsome_src]. *)
  (*     unfold read_reg_inr. rewrite Hsome_src. *)
  (*     destruct wsrc as [|[ p_src b_src e_src a_src v_src|] | ]; try done. *)
  (*     by repeat eexists. *)
  (*   } *)

  (*   (* Step 1: prepare all resources necessary to open the invariants of the argument (the cap given in is_unique), if necessary, *)
  (*      and store all the resources obtained from the region in allow_load_res *) *)
  (*   iDestruct (create_einit_code_resources with "[$Hreg] [$Hinv]") as (Ps_code) "[%Hlen_Ps HEinitCodeRes]" *)
  (*   ; [ eassumption *)
  (*     | by apply elem_of_finz_seq_between *)
  (*     |]. *)

  (*   (* Ompen the invariants! *) *)
  (*   (* Step 2: derive the concrete map of memory we need, and any spatial predicates holding over it *) *)
  (*   iMod (einit_code_resources_implies_mem_map with "HEinitCodeRes Ha") as (lmem) "[HEinitCodeMem HMemCodeRes]". *)
  (*   (* rename the big masks to easy names *) *)
  (*   set (E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc)). *)
  (*   set (E1 := allow_einit_code_mask a_pc v_pc (code_addresses a_pc (finz.seq_between b_src e_src)) v_src). *)

  (*   (* Step 3:  derive the non-spatial conditions over the memory map*) *)
  (*   iDestruct (mem_map_implies_pure_conds with "HEinitCodeMem") as %HReadPC. *)

  (*   (* Step 4: move the later outside, so that we can remove it after applying wp_isunique *) *)
  (*   (* iDestruct (allow_einit_code_mem_later with "HSweepMem") as "HSweepMem"; auto. *) *)

  (*   iAssert ( ⌜ allows_einit_code (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src ⌝)%I as "%Hallows_einit_code". *)
  (*   { iDestruct "HEinitCodeRes" as "(_&%HeinitCodeRes&_)". *)
  (*     iPureIntro. apply HeinitCodeRes. *)
  (*   } *)

  (*   (* iAssert ( ⌜ *) *)
  (*   (*             if ( einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src a_pc v_pc ) *) *)
  (*   (*             then (∃ dcap, lmem !! (b_src, v_src) = Some dcap) *) *)
  (*   (*             else True ⌝ )%I as "%Hdcap". *) *)
  (*   (* { admit. } *) *)


  (*   Set Nested Proofs Allowed. *)
  (*   Fixpoint list_remove_elem_list `{A : Type} `{EqDecision A} (la' la : list A) : list A := *)
  (*     match la' with *)
  (*     | [] => la *)
  (*     | h::t => list_remove_elem h (list_remove_elem_list t la) *)
  (*     end. *)

  (*   Definition data_addresses (a_pc : Addr) (la_code la_data : list Addr) *)
  (*     := (list_remove_elem_list (a_pc::la_code) la_data). *)

  (*   Definition allow_einit_data_mask *)
  (*     (a_pc : Addr) (v_pc : Version) *)
  (*     (la_code : list Addr) (v_code : Version) *)
  (*     (la_data : list Addr) (v_data : Version) *)
  (*     : coPset := *)
  (*     let mask_code := allow_einit_code_mask a_pc v_pc la_code v_code in *)
  (*     compute_mask_region mask_code (data_addresses a_pc la_code la_data) v_data. *)

  (* Definition read_lmem_inr (lmem : LMem) (a : Addr) (v : Version) p' b' e' a' v' := *)
  (*   match lmem !! (a,v) with *)
  (*     | Some (LCap p'' b'' e'' a'' v'') => (LCap p'' b'' e'' a'' v'') = LCap p' b' e' a' v' *)
  (*     | Some _ => True *)
  (*     | None => False end. *)

  (* Definition mem_allows_einit_data *)
  (*   (lmem : LMem) (a : Addr) (v : Version) *)
  (*   (p' : Perm) (b' e' a' : Addr) (v' : Version):= *)
  (*   lmem !! (a,v) = Some (LCap p' b' e' a' v') ∧ p' = RW. *)

  (* Definition einit_data_mask_cond *)
  (*   (lmem : LMem) (b_code : Addr) (v_code : Version) *)
  (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) *)
  (*   (a_pc : Addr) (v_pc : Version) := *)
  (*   decide ( *)
  (*       mem_allows_einit_data lmem b_code v_code p_data b_data e_data a_data v_data *)
  (*       ∧ a_pc ∉ (finz.seq_between b_data e_data) *)
  (*     ). *)

  (* Definition interp_list_pred_data *)
  (*   (lws : list LWord) (Ps : list D) (has_later : bool) : iProp Σ := *)
  (*   ([∗ list] lw;Pw ∈ lws;Ps, (if has_later then ▷▷ (Pw : D) lw else (Pw : D) lw)). *)

  (* Definition interp_list_persistent_data *)
  (*   (lws : list LWord) (Ps : list D) : iProp Σ := *)
  (*   ( ⌜ Persistent ([∗ list] lw;Pw ∈ lws;Ps, (Pw : D) lw) ⌝ ). *)

  (* Definition interp_list_readcond_data *)
  (*   (lws : list LWord) (Ps : list D) (has_later : bool) : iProp Σ := *)
  (*   ( if has_later *)
  (*     then [∗ list] Pa ∈ Ps, ▷ read_cond Pa interp *)
  (*     else [∗ list] Pa ∈ Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw) *)
  (*   )%I. *)

  (* Definition interp_list_close_data *)
  (*   (la : list Addr) (Ps : list D) (v : Version) (E E' : coPset) : iProp Σ := *)
  (*   ( ▷ (▷ ([∗ list] a_Pa ∈ zip la Ps, (interp_ref_inv a_Pa.1 v a_Pa.2))) ={E', E }=∗ True). *)

  (* Definition resources_open_invariant_data *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (la_code : list Addr) (v_code : Version) *)
  (*   (la_data : list Addr) (v_data : Version) (lws_data : list LWord) (Ps_data : list D) *)
  (*   (has_later : bool) *)
  (*   : iProp Σ := *)

  (*   (* let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *) *)
  (*   let E1 := allow_einit_code_mask a_pc v_pc la_code v_code : coPset in *)
  (*   let E2 := allow_einit_data_mask a_pc v_pc la_code v_code la_data v_data : coPset in *)

  (*   interp_list_pred_data lws_data Ps_data has_later *)
  (*   ∗ interp_list_persistent_data lws_data Ps_data *)
  (*   ∗ interp_list_readcond_data lws_data Ps_data has_later *)
  (*   ∗ interp_list_close_data la_data Ps_data v_data E1 E2. *)


  (* Definition allow_einit_data_resources *)
  (*   (* (lregs : LReg) *) *)
  (*   (lmem : LMem) *)
  (*   (* (src : RegName) *) *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) *)
  (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) (Ps_data : list D) *)
  (*   := *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let la_data  := data_addresses a_pc la_code (finz.seq_between b_data e_data) in *)
  (*   let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_code_mask a_pc v_pc la_code v_code : coPset in *)
  (*   let E1' := *)
  (*     (if einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src *)
  (*           a_src v_src a_pc v_pc then E1 else E0) *)
  (*   in *)
  (*   let E2 := allow_einit_data_mask a_pc v_pc la_code v_code la_data v_data : coPset in *)

  (*   ( *)
  (*     (* ⌜read_reg_inr lregs src p_code b_code e_code a_code v_code⌝ ∗ *) *)
  (*     ⌜read_lmem_inr lmem b_code v_code p_data b_data e_data a_data v_data⌝ ∗ *)
  (*     (* ⌜allows_einit_code lregs src⌝ ∗ *) *)
  (*     ⌜allows_einit_data lmem b_code v_code ⌝ ∗ *)
  (*    if einit_data_mask_cond lmem b_code v_code p_data b_data e_data a_data v_data a_pc v_pc *)
  (*    then *)
  (*     (|={E1, E2}=> (* we open this invariant with all the points-tos from b to e *) *)
  (*        ∃ (lws_data :list LWord), *)
  (*        ⌜ length lws_data = length la_data ⌝ *)
  (*        ∗ ([∗ map] la↦lw ∈ (logical_region_map la_data lws_data v_data), la ↦ₐ lw) (* here you get all the points-tos *) *)
  (*        ∗ resources_open_invariant_data a_pc v_pc la_code v_code la_data v_data lws_data Ps_data true)%I *)
  (*    else True)%I. *)


    (* Lemma create_einit_data_resources *)
    (*   (lregs : LReg) (lmem : LMem) (src : RegName) *)
    (*   (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
    (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) *)
    (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) : *)

    (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
    (*   let la_data  := data_addresses a_pc la_code (finz.seq_between b_data e_data) in *)
    (*   read_lmem_inr lmem b_code v_code p_data b_data e_data a_data v_data → *)

    (*   (allow_einit_code_resources *)
    (*      (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src a_pc v_pc *)
    (*      p_code b_code e_code a_code v_code Ps_code) -∗ *)
    (*   (allow_einit_code_mem *)
    (*     lmem (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src a_pc v_pc *)
    (*     lw_pc p_code b_code e_code a_code v_code Ps_code true) -∗ *)
    (*   ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw) -∗ *)

    (* (∃ (Ps_data : list D), *)
    (*        ⌜ length la_data = length Ps_data ⌝ *)
    (*        (* old resources *) *)
    (*        ∗ (allow_einit_code_resources *)
    (*             (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src a_pc v_pc *)
    (*             p_code b_code e_code a_code v_code Ps_code) *)
    (*        ∗ (allow_einit_code_mem *)
    (*             lmem (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src a_pc v_pc *)
    (*             lw_pc p_code b_code e_code a_code v_code Ps_code true) *)
    (*        ∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw) *)
    (*        (* new resources *) *)
    (*        ∗ allow_einit_data_resources *)
    (*            (* (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) *) *)
    (*            lmem *)
    (*            (* src *) *)
    (*            a_pc v_pc *)
    (*            p_code b_code e_code a_code v_code Ps_code *)
    (*            p_data b_data e_data a_data v_data Ps_data *)
    (* ). *)
    (* Admitted. *)

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    (* assert (∃ p_data b_data e_data a_data v_data, *)
    (*            read_lmem_inr lmem b_src v_src  p_data b_data e_data a_data v_data) *)
    (*   as (p_data & b_data & e_data & a_data & v_data & HV_data). *)
    (* { admit. } *)

    (* iDestruct (create_einit_data_resources with "[$HEinitCodeRes] [$HEinitCodeMem] [$HMemCodeRes]") *)
    (*   as (Ps_data) "(%Hlen_Ps_data & _ & HEinitCodeMem & Hmem & HEinitDataRes)"; first eassumption. *)


  (* Definition allow_einit_data_mem *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) (lws_code : list LWord) *)
  (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) (Ps_data : list D) *)
  (*   (has_later : bool) := *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let la_data  := data_addresses a_pc la_code (finz.seq_between b_data e_data) in *)

  (*   ( *)
  (*     ⌜read_reg_inr lregs src p_code b_code e_code a_code v_code⌝ ∗ *)
  (*     ⌜read_lmem_inr lmem b_code v_code p_data b_data e_data a_data v_data⌝ ∗ *)
  (*     if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
  (*     then *)
  (*       (if einit_data_mask_cond lmem b_code v_code p_data b_data e_data a_data v_data a_pc v_pc *)
  (*        then *)
  (*          (∃ (lws_data : list LWord), *)
  (*              ⌜length lws_data = length la_data⌝ *)
  (*              ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> *)
  (*                          (logical_region_map la_code lws_code v_code *)
  (*                             ∪ logical_region_map la_data lws_data v_data)⌝ *)
  (*              ∗ resources_open_invariant_data a_pc v_pc la_code v_code la_data v_data lws_data Ps_data has_later)%I *)
  (*        else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> (logical_region_map la_code lws_code v_code)⌝ *)
  (*       ) *)
  (*       ∗ resources_open_invariant_code a_pc v_pc la_code v_code lws_code Ps_code has_later *)
  (*     else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I. *)

    (* ( *)
    (*  if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
    (*  then (∃ (lws_code : list LWord), *)
    (*           ⌜length lws_code = length la_code⌝ *)
    (*           ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> (logical_region_map la_code lws_code v_code)⌝ *)
    (*           ∗ resources_open_invariant_code a_pc v_pc la_code v_code lws_code Ps_code has_later)%I *)
    (*  else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I. *)

  (* Lemma einit_data_resources_implies_mem_map *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) (lws_code : list LWord) *)
  (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) (Ps_data : list D) : *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let la_data  := data_addresses a_pc la_code (finz.seq_between b_data e_data) in *)
  (*   (* let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *) *)
  (*   let E1 := allow_einit_code_mask a_pc v_pc la_code v_code : coPset in *)
  (*   let E2 := allow_einit_data_mask a_pc v_pc la_code v_code la_data v_data : coPset in *)

  (*   allow_einit_code_resources lregs src a_pc v_pc p_code b_code e_code a_code v_code Ps_code *)
  (*   allow_einit_data_resources lregs src a_pc v_pc p_code b_code e_code a_code v_code Ps_code *)
  (*   -∗ (a_pc, v_pc) ↦ₐ lw_pc *)
  (*   ={ E0, *)
  (*        if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
  (*        then E1 *)
  (*        else E0 *)
  (*     }=∗ *)
  (*   ∃ lmem : LMem, *)
  (*     allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code true *)
  (*     ∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw). *)




  (* "HMemCodeRes" : [∗ map] la↦lw ∈ lmem, la ↦ₐ lw *)


  (*   iAssert ( ⌜ allows_einit_data lmem  ⌝)%I as "%Hallows_einit_code". *)
  (*   { iDestruct "HEinitCodeRes" as "(_&%HeinitCodeRes&_)". *)
  (*     iPureIntro. apply HeinitCodeRes. *)
  (*   } *)

  (*   iApply (wp_einit with "[$Hmap $HMemCodeRes]") *)
  (*   ; eauto *)
  (*   ; [ by simplify_map_eq *)
  (*     | rewrite /subseteq /map_subseteq /set_subseteq_instance *)
  (*       ; intros rr _; apply elem_of_dom *)
  (*       ; rewrite lookup_insert_is_Some'; *)
  (*       eauto *)
  (*     | | | ]. *)

  (* Admitted. *)






  (* (** Predicate that defines when the contents of a register can be swept; *)
  (*     i.e. when the register contains a capability with at least R permissions... *) *)
  (* Definition reg_allows_einit *)
  (*   (lregs : LReg) (lmem : LMem) (r : RegName) *)
  (*   (b e a : Addr) (v : Version) *)
  (*   (b' e' a' : Addr) (v' : Version):= *)
  (*   lregs !! r = Some (LCap RX b e a v) *)
  (*   ∧ lmem !! (a,v) = Some (LCap RW b' e' a' v'). *)

  (* (* TODO move stdpp_extra *) *)
  (* Fixpoint list_remove_elem_list `{A : Type} `{EqDecision A} (la' la : list A) : list A := *)
  (*   match la' with *)
  (*   | [] => la *)
  (*   | h::t => list_remove_elem h (list_remove_elem_list t la) *)
  (*   end. *)

  (* Definition code_addresses (a_pc : Addr) (code_la : list Addr) *)
  (*   := (list_remove_elem a_pc code_la). *)

  (* Definition allow_einit_mask_code *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (code_la : list Addr) (code_v : Version) *)
  (*   : coPset := *)
  (*   let pc_mask := (⊤ ∖ ↑logN.@(a_pc, v_pc)) in *)
  (*   compute_mask_region pc_mask (code_addresses a_pc code_la) code_v. *)

  (* Definition data_addresses (a_pc : Addr) (code_la data_la : list Addr) *)
  (*   := (list_remove_elem_list (a_pc::code_la) data_la). *)

  (* Definition allow_einit_mask_data *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (code_la : list Addr) (code_v : Version) *)
  (*   (data_la : list Addr) (data_v : Version) *)
  (*   : coPset := *)
  (*   let code_mask := allow_einit_mask_code a_pc v_pc code_la code_v in *)
  (*   compute_mask_region code_mask (data_addresses a_pc code_la data_la) data_v. *)

  (* (* Lemma allow_einit_mask_remove_nodup *) *)
  (* (*   (a_pc : Addr) (v_pc : Version) (code_la data_la : list Addr) (v : Version) : *) *)
  (* (*   NoDup code_la -> *) *)
  (* (*   NoDup data_la -> *) *)
  (* (*   allow_sweep_mask a_pc v_pc (list_remove_elem a_pc la) v = *) *)
  (* (*   allow_sweep_mask a_pc v_pc la v. *) *)
  (* (* Proof. *) *)
  (* (*   intros HNoDup. *) *)
  (* (*   by rewrite /allow_sweep_mask list_remove_elem_idem. *) *)
  (* (* Qed. *) *)

  (* (* this will help us close the invariant again... *) *)
  (* (* it states which properties are enforced on all the lws *) *)


  (* Definition region_open_resources *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (code_la : list Addr) (code_v : Version) *)
  (*   (code_lws : list LWord) (code_Ps : list D) *)
  (*   (data_la : list Addr) (data_v : Version) *)
  (*   (data_lws : list LWord) (data_Ps : list D) *)
  (*   (has_later : bool) *)
  (*   : iProp Σ := *)

  (*   let E := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_mask_code a_pc v_pc code_la code_v in *)
  (*   let E2 := allow_einit_mask_data a_pc v_pc code_la code_v data_la data_v in *)

  (*   ([∗ list] lw;Pw ∈ code_lws;code_Ps, (if has_later then ▷ (Pw : D) lw else (Pw : D) lw)) *)
  (*   ∗ ([∗ list] lw;Pw ∈ data_lws;data_Ps, (if has_later then ▷▷ (Pw : D) lw else (Pw : D) lw)) *)

  (*   ∗ ( ⌜ Persistent ([∗ list] lw;Pw ∈ code_lws;code_Ps, (Pw : D) lw) ⌝ ) (* All properties P are persistent *) *)
  (*   ∗ ( ⌜ Persistent ([∗ list] lw;Pw ∈ data_lws;data_Ps, (Pw : D) lw) ⌝ ) (* All properties P are persistent *) *)

  (*   ∗ ( if has_later *)
  (*       then ([∗ list] Pa ∈ code_Ps, read_cond Pa interp) *)
  (*            ∗ ([∗ list] Pa ∈ data_Ps, ▷ read_cond Pa interp) *)
  (*              (* the read cond holds *) *)
  (*       else ([∗ list] Pa ∈ code_Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw)) *)
  (*              ∗ ([∗ list] Pa ∈ data_Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw)) *)
  (*     )%I *)

  (*   ∗ (▷▷ ([∗ list] a_Pa ∈ zip data_la code_Ps, (interp_ref_inv a_Pa.1 data_v a_Pa.2)) ={E2, E1 }=∗ True) *)
  (*   ∗ (▷ ([∗ list] a_Pa ∈ zip code_la data_Ps, (interp_ref_inv a_Pa.1 code_v a_Pa.2)) ={E1, E }=∗ True). *)

  (* Definition einit_mask_cond *)
  (*   (lregs : LReg) (lmem : LMem) *)
  (*   (src : RegName) (b_code e_code a_code : Addr) (v_code : Version) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) *)
  (*   (a_pc : Addr) (v_pc : Version) := *)
  (*   decide (reg_allows_einit lregs lmem src b_code e_code a_code v_code b_data e_data a_data v_data *)
  (*           /\ (src = PC \/ a_pc ∉ (finz.seq_between b_code e_code)) *)
  (*           /\ a_pc ∉ (finz.seq_between b_data e_data) *)
  (*     ). *)

  (* (* Description of what the resources are supposed to look like after opening the region *) *)
  (* (*    if we need to, but before closing the region up again*) *)

  (* Definition allow_einit_res *)
  (*   (lregs : LReg) (lmem : LMem) *)
  (*   (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (b_code e_code a_code : Addr) (v_code : Version) (code_Ps : list D) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) (data_Ps : list D) *)
  (*   := *)

  (*   let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in *)
  (*   let E   := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_mask_code a_pc v_pc code_la v_code in *)
  (*   let E2 := allow_einit_mask_data a_pc v_pc code_la v_code data_la v_data in *)

  (*   (⌜read_reg_inr lregs src RX b_code e_code a_code v_code⌝ ∗ *)
  (*    ⌜allows_einit lregs lmem src⌝ ∗ *)
  (*    if einit_mask_cond lregs lmem *)
  (*         src b_code e_code a_code v_code *)
  (*         b_data e_data a_data v_data *)
  (*         a_pc v_pc *)
  (*    then *)
  (*     (|={E, E2}=> (* we open this invariant with all the points-tos from b to e *) *)
  (*        ∃ (code_lws : list LWord) (data_lws : list LWord), *)
  (*        ⌜ length code_lws = length code_la ⌝ *)
  (*        ∗ ⌜ length data_lws = length data_la ⌝ *)
  (*        ∗ ([∗ map] la↦lw ∈ (logical_region_map code_la code_lws v_code), la ↦ₐ lw) (* here you get all the points-tos *) *)
  (*        ∗ ([∗ map] la↦lw ∈ (logical_region_map data_la data_lws v_data), la ↦ₐ lw) *)
  (*        ∗ region_open_resources a_pc v_pc *)
  (*            code_la v_code code_lws code_Ps *)
  (*            data_la v_data data_lws data_Ps *)
  (*            true)%I *)
  (*    else True)%I. *)

  (* (* this does not yet open the invariant *) *)
  (* Lemma create_einit_res *)
  (*   (lregs : LReg) (lmem : LMem) *)
  (*   (src : RegName) *)
  (*   (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version) *)
  (*   (b_code e_code a_code : Addr) (v_code : Version) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) : *)

  (*   let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in *)

  (*   read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src RX b_code e_code a_code v_code *)
  (*   -> a_pc ∈ finz.seq_between b_pc e_pc *)
  (*   → (∀ (r : RegName) lw, ⌜r ≠ PC⌝ → ⌜lregs !! r = Some lw⌝ → (fixpoint interp1) lw) *)
  (*   -∗ interp (LCap p_pc b_pc e_pc a_pc v_pc) *)
  (*   -∗ (∃ (code_Ps : list D) (data_Ps  : list D), *)
  (*          ⌜ length code_la = length code_Ps ⌝ *)
  (*          ∗ ⌜length data_la = length data_Ps ⌝ *)
  (*          ∗ allow_einit_res *)
  (*              (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) lmem src *)
  (*              a_pc v_pc *)
  (*              b_code e_code a_code v_code code_Ps *)
  (*              b_data e_data a_data v_data data_Ps *)
  (*      ). *)
  (* Proof. *)
  (* Admitted. *)

  (* Definition allow_einit_mem *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)

  (*   (b_code e_code a_code : Addr) (v_code : Version) (code_Ps : list D) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) (data_Ps : list D) *)

  (*   (has_later : bool) := *)

  (*   let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in *)

  (*   (⌜read_reg_inr lregs src RX b_code e_code a_code v_code⌝ ∗ *)
  (*    if einit_mask_cond lregs lmem *)
  (*         src b_code e_code a_code v_code *)
  (*         b_data e_data a_data v_data *)
  (*         a_pc v_pc *)
  (*    then (∃ (code_lws : list LWord) (data_lws : list LWord), *)
  (*          ⌜ length code_la = length code_lws ⌝ *)
  (*          ∗ ⌜length data_la = length data_lws ⌝ *)
  (*          ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> *)
  (*                      (logical_region_map code_la code_lws v_code *)
  (*                         ∪ logical_region_map data_la data_lws v_data)⌝ *)
  (*             ∗ region_open_resources a_pc v_pc *)
  (*                 code_la v_code code_lws code_Ps *)
  (*                 data_la v_data data_lws data_Ps *)
  (*                 has_later) *)
  (*    else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I. *)

  (* (* Create the lmem with the points-tos we need for the is_unique case *) *)
  (* Lemma einit_res_implies_mem_map *)
  (*   (lregs : LReg) (lmem : LMem) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)

  (*   (b_code e_code a_code : Addr) (v_code : Version) (code_Ps : list D) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) (data_Ps : list D) : *)

  (*   let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in *)

  (*   let E   := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_mask_code a_pc v_pc code_la v_code in *)
  (*   let E2 := allow_einit_mask_data a_pc v_pc code_la v_code data_la v_data in *)

  (*   allow_einit_res lregs src a_pc v_pc lw_pc *)
  (*     b_code e_code a_code v_code code_Ps *)
  (*     b_data e_data a_data v_data data_Ps *)
  (*   -∗ (a_pc, v_pc) ↦ₐ lw_pc *)
  (*   ={ E, *)
  (*        if einit_mask_cond lregs *)
  (*         src b_code e_code a_code v_code *)
  (*         b_data e_data a_data v_data *)
  (*         a_pc v_pc *)
  (*        then E2 *)
  (*        else E *)
  (*     }=∗ *)
  (*   ∃ lmem : LMem, *)
  (*     allow_einit_mem lmem lregs src a_pc v_pc lw_pc *)
  (*                     b_code e_code a_code v_code code_Ps *)
  (*                     b_data e_data a_data v_data data_Ps *)
  (*                     true *)
  (*     ∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw). *)
  (* Proof. *)
  (*   intros *. *)
  (*   iIntros "HSweepRes Ha_pc". *)
  (*   iDestruct "HSweepRes" as "(%Hread & [ %Hreserved HSweepRes ] )". *)
  (*   subst E'. *)
  (*   rewrite /sweep_mask_cond. *)
  (*   case_decide as Hallows; cycle 1. *)
  (*     - iExists _. *)
  (*       iSplitR "Ha_pc". *)
  (*       + iFrame "%". *)
  (*         rewrite /sweep_mask_cond; case_decide; first by exfalso. auto. *)
  (*       + iModIntro; iNext. by iApply memMap_resource_1. *)
  (*     - iMod "HSweepRes" as (lws) "(%Hlws & Hmem & HSweepRest)". *)
  (*       iExists _. *)
  (*       iSplitL "HSweepRest". *)
  (*       * iFrame "%". *)
  (*         rewrite decide_True; auto. *)
  (*       * iModIntro;iNext. *)
  (*         destruct Hallows as ((Hrinr & Hra) & Hne). *)
  (*         iDestruct (big_sepM_insert with "[$Hmem $Ha_pc]") as "Hmem" ; cycle 1 ; auto. *)
  (*         rewrite /logical_region_map. *)
  (*         apply not_elem_of_list_to_map_1. *)
  (*         rewrite fst_zip. *)
  (*         2: { rewrite Hlws /logical_region fmap_length; lia. } *)
  (*         rewrite /logical_region. *)
  (*         intro Hcontra. clear -Hcontra. *)
  (*         eapply elem_of_list_fmap_2 in Hcontra. *)
  (*         destruct Hcontra as (a & Heq & Hcontra) ; simplify_eq. *)
  (*         apply not_elemof_list_remove_elem in Hcontra; auto. *)
  (* Qed. *)



End fundamental.
