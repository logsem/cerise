From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine.rules Require Export rules. 
From cap_machine Require Export lang region.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

(** CMRA for heap and its predicates. Contains: *)
(* CMRA for relatedness between locations and saved prop names *)
(* CMRA for saved predicates *)
Definition relUR : ucmraT := gmapUR Addr (agreeR (prodO gnameO (leibnizO Perm))).

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_saved_pred :> savedPredG Σ ((STS_states * STS_rels) * Word);
  heapG_rel :> inG Σ (authR relUR);
  γrel : gname
}.

Section heap.
  Context `{heapG Σ, memG Σ, regG Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Notation WORLD := (leibnizO (STS_states * STS_rels)).
  Implicit Types W : WORLD.
  
  Definition REL_def l p γ : iProp Σ := own γrel (◯ {[ l := to_agree (γ,p) ]}).
  Definition REL_aux : { x | x = @REL_def }. by eexists. Qed.
  Definition REL := proj1_sig REL_aux.
  Definition REL_eq : @REL = @REL_def := proj2_sig REL_aux.
  
  Definition RELS_def (M : relUR) : iProp Σ := own γrel (● M).
  Definition RELS_aux : { x | x = @RELS_def }. by eexists. Qed.
  Definition RELS := proj1_sig RELS_aux.
  Definition RELS_eq : @RELS = @RELS_def := proj2_sig RELS_aux.

  Definition rel_def (l : Addr) (p : Perm) (φ : (WORLD * Word) -> iProp Σ) : iProp Σ :=
    (∃ (γpred : gnameO), REL l p γpred 
                       ∗ saved_pred_own γpred φ)%I.
  Definition rel_aux : { x | x = @rel_def }. by eexists. Qed.
  Definition rel := proj1_sig rel_aux.
  Definition rel_eq : @rel = @rel_def := proj2_sig rel_aux.

  Global Instance rel_persistent l p (φ : (WORLD * Word) -> iProp Σ) :
    Persistent (rel l p φ).
  Proof. rewrite rel_eq /rel_def REL_eq /REL_def. apply _. Qed.
  
  Definition future_mono (φ : ((STS_states * STS_rels) * Word) -> iProp Σ) : iProp Σ :=
    (□ ∀ W W' v, ⌜related_sts_pub W.1 W'.1 W.2 W'.2⌝ → φ (W,v) -∗ φ (W',v))%I. 
  
  Definition region_def W : iProp Σ := 
    (∃ (M : relUR), RELS M
                         ∗ [∗ map] a↦γp ∈ M, ∃ γpred (v : Word) (p : Perm) φ,
                                               ⌜γp = to_agree (γpred,p)⌝
                                             ∗ ⌜p ≠ O⌝
                                             ∗ (a ↦ₐ[p] v)
                                             ∗ future_mono φ
                                             ∗ saved_pred_own γpred φ
                                             ∗ ▷ φ (W,v))%I.
  Definition region_aux : { x | x = @region_def }. by eexists. Qed.
  Definition region := proj1_sig region_aux.
  Definition region_eq : @region = @region_def := proj2_sig region_aux.

  Lemma reg_in γ R n r:
    (own γ (● R) ∗ own γ (◯ {[n := to_agree r]}) -∗
        ⌜R = <[n := to_agree r]>(delete n R)⌝)%I.
  Proof.
    iIntros "[H1 H2]".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro.
    apply auth_both_valid in Hv; destruct Hv as [Hv1 Hv2].
    specialize (Hv2 n).
    apply singleton_included in Hv1.
    destruct Hv1 as (y & Heq & Hi).
    revert Hv2; rewrite Heq => Hv2.
    revert Hi; rewrite Some_included_total => Hi.
    apply to_agree_uninj in Hv2 as [y' Hy].
    revert Hi Heq; rewrite -Hy => Hi Heq.
    apply to_agree_included in Hi; subst.
    revert Heq; rewrite -Hi => Heq.
    rewrite insert_delete insert_id; auto. eapply leibniz_equiv. apply Heq.
    Unshelve. 
  Admitted.

  Lemma rels_agree a γ1 γ2 p1 p2 :
    REL a p1 γ1 ∗ REL a p2 γ2 -∗ ⌜γ1 = γ2⌝ ∧ ⌜p1 = p2⌝.
  Proof.
    rewrite REL_eq /REL_def.
    iIntros "[Hγ1 Hγ2]".
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
    iPureIntro.
    rewrite -auth_frag_op op_singleton in Hval.
    apply singleton_valid in Hval.
    apply agree_op_invL' in Hval.
    by inversion Hval. 
  Qed. 

  Lemma rel_agree a p1 p2 φ1 φ2 :
    rel a p1 φ1 ∗ rel a p2 φ2 -∗ ⌜p1 = p2⌝ ∗ (∀ x, ▷ (φ1 x ≡ φ2 x)). 
  Proof.
    iIntros "[Hr1 Hr2]".
    rewrite rel_eq /rel_def. 
    iDestruct "Hr1" as (γ1) "[Hrel1 Hpred1]".
    iDestruct "Hr2" as (γ2) "[Hrel2 Hpred2]".
    iDestruct (rels_agree with "[$Hrel1 $Hrel2]") as %[-> ->].
    iSplitR;[auto|]. iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed. 
    
  Lemma extend_region E W l p v φ `{∀ W v, Persistent (φ (W,v))}:
    (⌜p ≠ O⌝ → future_mono φ →
    region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region W ∗ rel l p φ)%I.
  Proof.
    iIntros (Hpne) "#Hmono Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* Cannot have two capability ghost resources: contradiction *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (γpred' v' p' φ') "(_ & % & Hl' & _)".
      by iDestruct (cap_duplicate_false with "[$Hl $Hl']") as %Hcontr. 
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> M) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      by apply alloc_singleton_local_update. 
    }
    iApply fupd_frame_l. iSplitL "HR Hpreds Hl".
    - iExists _. iFrame "HR #".
      iApply big_sepM_insert; auto.
      iFrame. iExists γpred,v,_,φ. iSplitR;[auto|]. iFrame "∗ #". done. 
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done. 
  Qed.

  Definition open_region_def (a : Addr) (W : WORLD) : iProp Σ :=
    (∃ M, RELS M ∗
    [∗ map] l↦γ ∈ (delete a M), ∃ γpred v p φ, ⌜γ = to_agree (γpred,p)⌝
                                  ∗ ⌜p ≠ O⌝                           
                                  ∗ (l ↦ₐ[p] v)
                                  ∗ future_mono φ
                                  ∗ saved_pred_own γpred φ
                                  ∗ ▷ φ (W,v))%I.
  Definition open_region_aux : { x | x = @open_region_def }. by eexists. Qed.
  Definition open_region := proj1_sig open_region_aux.
  Definition open_region_eq : @open_region = @open_region_def := proj2_sig open_region_aux.

  Lemma region_open W l p φ :
    rel l p φ ∗ region W -∗ ∃ v, open_region l W
                               ∗ (l ↦ₐ[p] v)
                               ∗ ⌜p ≠ O⌝
                               ∗ ▷ future_mono φ
                               ∗ ▷ φ (W,v).
  Proof.
    iIntros "[Hrel Hreg]".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M) "(HM & Hpreds)". 
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & #Hmono & #Hφ' & Hφv)".  
    inversion H2; subst.
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv". 
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq -HMeq. iFrame "∗ #". 
    - iSplitR;[auto|]. iSplitR. 
      + rewrite /future_mono.
        iApply later_intuitionistically_2. iAlways.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a0,a1) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a,a1) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq'"). 
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq''"). iFrame. 
      + iNext. iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  Lemma region_close W l φ p v :
    open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_mono φ ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros "(Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _,_,_,_. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame.
  Qed.  
  
  Fixpoint delete_list {K V : Type} `{Countable K, EqDecision K}
             (ks : list K) (m : gmap K V) : gmap K V :=
    match ks with
    | k :: ks' => delete k (delete_list ks' m)
    | [] => m
    end.

  Lemma delete_list_insert {K V : Type} `{Countable K, EqDecision K}
        (ks : list K) (m : gmap K V) (l : K) (v : V) :
    l ∉ ks →
    delete_list ks (<[l:=v]> m) = <[l:=v]> (delete_list ks m).
  Proof.
    intros Hnin.
    induction ks; auto.
    simpl.
    apply not_elem_of_cons in Hnin as [Hneq Hnin]. 
    rewrite -delete_insert_ne; auto.
    f_equal. by apply IHks.
  Qed.

  Lemma delete_list_delete {K V : Type} `{Countable K, EqDecision K}
        (ks : list K) (m : gmap K V) (l : K) :
    l ∉ ks →
    delete_list ks (delete l m) = delete l (delete_list ks m).
  Proof.
    intros Hnin.
    induction ks; auto.
    simpl.
    apply not_elem_of_cons in Hnin as [Hneq Hnin]. 
    rewrite -delete_commute; auto.
    f_equal. by apply IHks.
  Qed. 

  Definition open_region_many_def (l : list Addr) (W : WORLD) : iProp Σ :=
    (∃ M, RELS M ∗
         [∗ map] l↦γ ∈ (delete_list l M), ∃ γpred v p φ, ⌜γ = to_agree (γpred,p)⌝
                                  ∗ ⌜p ≠ O⌝                                          
                                  ∗ l ↦ₐ[p] v
                                  ∗ future_mono φ
                                  ∗ saved_pred_own γpred φ
                                  ∗ ▷ φ (W,v))%I.
  Definition open_region_many_aux : { x | x = @open_region_many_def }. by eexists. Qed.
  Definition open_region_many := proj1_sig open_region_many_aux.
  Definition open_region_many_eq : @open_region_many = @open_region_many_def := proj2_sig open_region_many_aux.

   Lemma region_open_prepare l W :
    (open_region l W ∗-∗ open_region_many [l] W)%I.
  Proof.
    iSplit; iIntros "Hopen";
    rewrite open_region_eq open_region_many_eq /=;
    iFrame. 
  Qed.

  Lemma region_open_next W φ ls l p :
    l ∉ ls →
    open_region_many ls W ∗ rel l p φ -∗
    ∃ v, open_region_many (l :: ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ ▷ future_mono φ ∗ ▷ φ (W,v). 
  Proof.
    rewrite open_region_many_eq . 
    iIntros (Hnin) "[Hopen #Hrel]".
    rewrite /open_region_many_def /=. 
    rewrite rel_eq /rel_def /rel_def /region_def REL_eq RELS_eq /rel /region /REL /RELS. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M) "(HM & Hpreds)". 
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & #Hmono & #Hφ' & Hφv)".  
    inversion H2; subst.
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv". 
    - rewrite /open_region.
      iExists _. repeat (rewrite -HMeq). iFrame "∗ #".
    - iSplitR;[auto|]. iSplitR.
      + rewrite /future_mono.
        iApply later_intuitionistically_2. iAlways.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a0,a1) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a,a1) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq'"). 
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq''"). iFrame. 
      + iNext. 
        iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_close_next W φ ls l p v :
    l ∉ ls ->
    open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_mono φ ∗ ▷ φ (W,v) ∗ rel l p φ -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def. 
    iIntros (Hnin) "(Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _,_,_,_. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -delete_list_delete; auto. rewrite -delete_list_insert; auto.
    rewrite -HMeq. 
    iFrame "# ∗".
  Qed.
    
End heap. 

Ltac auto_equiv :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
  | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

Class logrel_na_invs Σ :=
  {
    logrel_na_invG :> na_invG Σ;
    logrel_nais : na_inv_pool_name;
    wγ : gname
  }.

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation WORLD := (leibnizO (STS_states * STS_rels)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).
  
  (* -------------------------------------------------------------------------------- *)

  (* interp expression definitions *)
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Definition interp_reg (interp : D) : R :=
   λne W (reg : leibnizO Reg), (full_map reg ∧ 
       ∀ (r : RegName), (⌜r ≠ PC⌝ → interp W (reg !r! r)))%I.

  Definition interp_conf fs fr : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ →
              ∃ r fs' fr', full_map r ∧ registers_mapsto r
                                      ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                      ∗ na_own logrel_nais ⊤                           
                                      ∗ sts_full fs' fr'
                                      ∗ region (fs',fr') }})%I.

  Definition interp_expr (interp : D) r : D :=
    (λne W w, ∃ fs fr, ⌜fs = W.1⌝
                     ∧ ⌜fr = W.2⌝ ∧
                     (interp_reg interp W r ∗ registers_mapsto (<[PC:=w]> r)
                      ∗ region W
                      ∗ sts_full fs fr
                      ∗ na_own logrel_nais ⊤ -∗
                      ⌜match w with inr _ => True | _ => False end⌝ ∧
                      interp_conf fs fr))%I.

  (* condition definitions *)
  Program Definition read_write_cond l p (interp : D) : iProp Σ :=
    rel l p (λne Wv, interp Wv.1 Wv.2).
  Next Obligation.
  Proof. solve_proper. Qed. 
  Global Instance read_write_cond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) read_write_cond.
  Proof.
    rewrite /read_write_cond rel_eq /rel. solve_proper_prepare.
    f_equiv =>γ. f_equiv.
    apply saved_anything_ne.
    solve_proper. 
  Qed.

  Definition future_world g W W' : iProp Σ :=
    (match g with
    | Local => ⌜related_sts_pub W.1 W'.1 W.2 W'.2⌝
    | Global => ⌜related_sts_priv W.1 W'.1 W.2 W'.2⌝
    end)%I. 
  
  Definition exec_cond W b e g p (interp : D) : iProp Σ :=
    (∀ a r W', ⌜a ∈ₐ [[ b , e ]]⌝ → future_world g W W' →
            ▷ interp_expr interp r W' (inr ((p,g),b, e,a)))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond. 
  Proof. unfold exec_cond. solve_proper. Qed. 
    
  Definition enter_cond W b e a g (interp : D) : iProp Σ :=
    (∀ r W', future_world g W W' →
        ▷ interp_expr interp r W' (inr ((RX,g),b,e,a)))%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond. 
  Proof. unfold enter_cond. solve_proper. Qed.  
  
  (* interp definitions *)
  Definition interp_z : D := λne _ w, ⌜match w with inl z => True | _ => False end⌝%I.
  
  Definition interp_cap_O : D := λne _ _, True%I.

  Definition interp_cap_RO (interp : D) : D :=
    λne _ w, (match w with
              | inr ((RO,g),b,e,a) =>
                ∃ p, ⌜PermFlows RO p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
              | _ => False
              end)%I.
  
  Definition interp_cap_RW (interp : D) : D :=
    λne _ w, (match w with
              | inr ((RW,g),b,e,a) =>
                ∃ p, ⌜PermFlows RW p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
              | _ => False
              end)%I.
  
  Definition interp_cap_RWL (interp : D) : D :=
    λne _ w, (match w with
              | inr ((RWL,g),b,e,a) =>
                ∃ p, ⌜PermFlows RWL p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
              | _ => False
              end)%I.

  Definition interp_cap_RX (interp : D) : D :=
    λne W w, (match w with inr ((RX,g),b,e,a) =>
                           ∃ p, ⌜PermFlows RX p⌝ ∗
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)) 
                                 ∗ □ exec_cond W b e g RX interp
             | _ => False end)%I.  

  Definition interp_cap_E (interp : D) : D :=
    λne W w, (match w with
              | inr ((E,g),b,e,a) => □ enter_cond W b e a g interp
              | _ => False
              end)%I.
  
  Definition interp_cap_RWX (interp : D) : D :=
    λne W w, (match w with inr ((RWX,g),b,e,a) =>
                           ∃ p, ⌜PermFlows RWX p⌝ ∗
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)) 
                                 ∗ □ exec_cond W b e g RWX interp
             | _ => False end)%I.
  
  Definition interp_cap_RWLX (interp : D) : D :=
    λne W w, (match w with inr ((RWLX,g),b,e,a) =>
                           ∃ p, ⌜PermFlows RWLX p⌝ ∗
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)) 
                                 ∗ □ exec_cond W b e g RWLX interp
             | _ => False end)%I.
  
  Definition interp1 (interp : D) : D :=
    (λne W w,
    match w return _ with
    | inl _ => interp_z W w
    | inr ((O, g), b, e, a) => interp_cap_O W w
    | inr ((RO, g), b, e, a) => interp_cap_RO interp W w
    | inr ((RW, g), b, e, a) => interp_cap_RW interp W w
    | inr ((RWL, g), b, e, a) => interp_cap_RWL interp W w
    | inr ((RX, g), b, e, a) => interp_cap_RX interp W w
    | inr ((E, g), b, e, a) => interp_cap_E interp W w
    | inr ((RWLX, g), b, e, a) => interp_cap_RWLX interp W w
    | inr ((RWX, g), b, e, a) => interp_cap_RWX interp W w
    end)%I.

  (* Global Instance interp_expr_contractive : *)
  (*   Contractive (interp_expr). *)
  (* Proof. solve_contractive. Qed.  *)
  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.
  Global Instance interp_cap_RO_contractive :
    Contractive (interp_cap_RO).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct c, p, p, p, p; auto.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed. 
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof. solve_proper_prepare. destruct x1; auto. destruct c, p, p, p, p; auto.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply exist_ne =>γ. apply sep_ne; auto. 
         simpl. f_equiv. solve_contractive. 
  Qed. 
  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct c, p, p, p, p; auto.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply exist_ne =>γ. apply sep_ne; auto. 
         simpl. f_equiv. solve_contractive. 
  Qed. 
  Global Instance exec_cond_contractive W b e g pl :
    Contractive (λ interp, exec_cond W b e g pl interp).
  Proof. 
    solve_contractive. 
  Qed.
  Global Instance enter_cond_contractive W b e a g :
    Contractive (λ interp, enter_cond W b e a g interp). 
  Proof.
    solve_contractive. 
  Qed. 
  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    rewrite /interp_cap_RX.
    solve_proper_prepare. 
    destruct x1; auto. destruct c, p, p, p, p; auto.
    apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. apply sep_ne; auto.
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply exist_ne =>γ. apply sep_ne; auto. 
      simpl. f_equiv. solve_contractive.
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. 
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    rewrite /interp_cap_E.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p; auto.
    solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply enter_cond_contractive. 
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    rewrite /interp_cap_RWX.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p; auto.
    apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. apply sep_ne. 
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply exist_ne =>γ. apply sep_ne; auto. 
      simpl. f_equiv. solve_contractive. 
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. 
  Qed.
  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    rewrite /interp_cap_RWLX.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p; auto.
    apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. apply sep_ne. 
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply exist_ne =>γ. apply sep_ne; auto. 
      simpl. f_equiv. solve_contractive. 
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. 
  Qed.     
    
  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn W w. 
    rewrite /interp1. 
    destruct w; [auto|].
    destruct c,p,p,p,p; first auto.
    - by apply interp_cap_RO_contractive.
    - by apply interp_cap_RW_contractive.
    - by apply interp_cap_RWL_contractive.
    - by apply interp_cap_RX_contractive.
    - by apply interp_cap_E_contractive.
    - by apply interp_cap_RWX_contractive.
    - by apply interp_cap_RWLX_contractive.
  Qed.
  
  Lemma fixpoint_interp1_eq (W : WORLD) (x : leibnizO Word) :
    fixpoint (interp1) W x ≡ interp1 (fixpoint (interp1)) W x. 
  Proof. exact: (fixpoint_unfold (interp1) W x). Qed.

  Definition interp : D :=
    λne W w, (fixpoint (interp1)) W w.
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent : Persistent (interp W w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl. 
         apply _. 
         destruct c,p,p,p,p; repeat (apply exist_persistent; intros); try apply _.
  Qed. 

  Lemma read_allowed_inv W (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' ≤ e)%Z →
    readAllowed p → (interp W (inr ((p,g),b,e,a)) →
      (∃ p', ⌜PermFlows p p'⌝ ∗ (read_write_cond a' p' interp)))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction;
    try (iDestruct "Hinterp" as (p) "[Hleast Hinterp]");
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]");
    iExists _; iFrame;
    try (iDestruct (extract_from_region_inv_2 with "Hinterp") as (w) "[Hinv _]"; eauto); 
    try (iDestruct (extract_from_region_inv with "Hinterp") as "Hinv"; eauto).
  Qed.
  
End logrel.

(* Notation "𝕍( W )" := (interp W) (at level 70). *)
(* Notation "𝔼( W )" := (λ r, interp_expression r W). *)
(* Notation "ℝ( W )" := (interp_registers W). *)
(* Notation "𝕆( W )" := (interp_conf W.1 W.2).  *)


    