From iris.algebra Require Import gmap agree auth.
From cap_machine Require Export lang sts rules_base.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred. 

(** CMRA for heap and its predicates. Contains: *)
(* CMRA for relatedness between locations and saved prop names *)
(* CMRA for saved predicates *)
Definition relUR : ucmraT := gmapUR Addr (agreeR (leibnizO (gname * Perm))).
Definition relT := gmap Addr (leibnizO (gname * Perm)). 

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_saved_pred :> savedPredG Σ (((STS_states * STS_rels) * (STS_states * STS_rels)) * Word);
  heapG_rel :> inG Σ (authR relUR);
  γrel : gname
                   }.

Section heap.
  Context `{heapG Σ, memG Σ, regG Σ, STSG Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (prodO STS STS). 
  Implicit Types W : WORLD.
  
  Definition REL_def l p γ : iProp Σ := own γrel (◯ {[ l := to_agree (γ,p) ]}).
  Definition REL_aux : { x | x = @REL_def }. by eexists. Qed.
  Definition REL := proj1_sig REL_aux.
  Definition REL_eq : @REL = @REL_def := proj2_sig REL_aux.
  
  Definition RELS_def (M : relT) : iProp Σ := own γrel (● (to_agree <$> M : relUR)).
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
  
  Definition future_pub_mono (φ : (WORLD * Word) -> iProp Σ) v : iProp Σ :=
    (□ ∀ W W', ⌜related_sts_pub_world W W'⌝ → φ (W,v) -∗ φ (W',v))%I.

  Definition future_priv_mono (φ : (WORLD * Word) -> iProp Σ) v : iProp Σ :=
    (□ ∀ W W', ⌜related_sts_priv_world W W'⌝ → φ (W,v) -∗ φ (W',v))%I.

  (* We will first define the standard STS for the shared part of the heap *)
  Inductive region_type :=
  | Temporary
  | Permanent
  | Revoked.

  Global Instance region_type_EqDecision : EqDecision region_type :=
    (fun x y => match x, y with
             | Temporary, Temporary
             | Permanent, Permanent
             | Revoked, Revoked => left eq_refl
             | _, _ => ltac:(right; auto)
             end).
  Global Instance region_type_finite : finite.Finite region_type :=
    (finite.enc_finite
       (fun x => match x with Temporary => 0%nat | Permanent => 1%nat | _ => 2%nat end)
       (fun n => match n with 0%nat => Temporary | 1%nat => Permanent | _ => Revoked end)
       3%nat
       ltac:(destruct x; cbv; auto)
       ltac:(destruct x; cbv; auto)
       ltac:(do 2 (destruct i; try lia))).
  Global Instance region_type_countable : Countable region_type.
  Proof. apply finite.finite_countable. Qed.

  Definition std_rel_pub := λ a b, (a = Revoked ∧ b = Temporary).
  Definition std_rel_priv := λ a b, a = Temporary ∨ b = Permanent.
  Global Instance sts_std : STS_STD region_type := {| Rpub := std_rel_pub; Rpriv := std_rel_priv |}.

  (* Some practical shorthands for projections *)
  Definition std W := W.1.
  Definition loc W := W.2.
  Definition std_sta W := W.1.1.
  Definition std_rel W := W.1.2.

  (* The following predicates states that the std relations map in the STS collection is standard according to sts_std *)
  Definition rel_is_std_i W i := (std_rel W) !! i = Some (convert_rel (Rpub : relation region_type),
                                                        convert_rel (Rpriv : relation region_type)). 
  Definition rel_is_std W := (∀ i, is_Some ((std_rel W) !! i) → rel_is_std_i W i).

  (* ------------------------------------------- DOM_EQUAL ----------------------------------------- *)
  (* dom_equal : we require the domain of the STS standard collection and the memory map to be equal *)

  Definition dom_equal (Wstd_sta : STS_states) (M : relT) :=
    ∀ (i : positive), is_Some (Wstd_sta !! i) ↔ (∃ (a : Addr), countable.encode a = i ∧ is_Some (M !! a)).

  Lemma dom_equal_empty : dom_equal ∅ ∅.
  Proof.
    rewrite /dom_equal =>a.
    split; intros [x Hx]; [inversion Hx|destruct Hx as [_ Hx];by inversion Hx]. 
  Qed.

  Lemma dom_equal_insert Wstd_sta M (a : Addr) x y :
    dom_equal Wstd_sta M → dom_equal (<[countable.encode a := x]> Wstd_sta) (<[a := y]> M).
  Proof.
    intros Heq.
    rewrite /dom_equal =>i.
    split; intros [z Hz]. 
    - destruct (decide ((countable.encode a) = i)); subst.
      { exists a. split;[auto|]. rewrite lookup_insert. eauto. }
      { rewrite lookup_insert_ne in Hz; auto.
        destruct Heq with i as [Heq_i _].
        destruct Heq_i as [a' [Ha' HMa'] ]; eauto.
        exists a'; split;[auto|]. rewrite lookup_insert_ne; auto.
        intros Ha. subst. done. 
      }
    - destruct Hz as [Hi Hz]. 
      destruct (decide ((countable.encode a) = i)); subst.
      { rewrite e. rewrite lookup_insert. eauto. }
      { rewrite lookup_insert_ne;auto.
        destruct Heq with (countable.encode z) as [_ Heq_i].
        apply Heq_i.
        exists z. split; auto.
        rewrite lookup_insert_ne in Hz; auto.
        intros Ha; congruence. 
      }
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- REGION_MAP ---------------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)
  
  Definition region_map_def M W :=
    ([∗ map] a↦γp ∈ M, ∃ ρ, sts_state_std (countable.encode a) ρ ∗
                            match ρ with
                            | Temporary => ∃ γpred (v : Word) (p : Perm) φ,
                                               ⌜γp = (γpred,p)⌝
                                             ∗ ⌜p ≠ O⌝
                                             ∗ a ↦ₐ[p] v
                                             ∗ (if pwl p
                                               then future_pub_mono φ v
                                               else future_priv_mono φ v)
                                             ∗ saved_pred_own γpred φ
                                             ∗ ▷ φ (W,v)
                            | Permanent => ∃ γpred (v : Word) (p : Perm) φ,
                                               ⌜γp = (γpred,p)⌝
                                             ∗ ⌜p ≠ O⌝
                                             ∗ a ↦ₐ[p] v
                                             ∗ future_priv_mono φ v
                                             ∗ saved_pred_own γpred φ
                                             ∗ ▷ φ (W,v)
                            | Revoked => emp
                            end)%I. 
        
  Definition region_def W : iProp Σ := 
    (∃ (M : relT), RELS M ∗ ⌜dom_equal (std_sta W) M⌝
                         ∗ region_map_def M W)%I. 
  Definition region_aux : { x | x = @region_def }. by eexists. Qed.
  Definition region := proj1_sig region_aux.
  Definition region_eq : @region = @region_def := proj2_sig region_aux.

  Lemma reg_in γ (R : relT) (n : Addr) (r : leibnizO (gname * Perm)) :
    (own γ (● (to_agree <$> R : relUR)) ∗ own γ (◯ {[n := to_agree r]}) -∗
        ⌜R = <[n := r]>(delete n R)⌝)%I.
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
    rewrite insert_delete insert_id /leibniz_equiv_iff => //; auto.
    revert Heq. rewrite lookup_fmap fmap_Some_equiv =>Hx.
    destruct Hx as [x [-> Hrx] ].
    apply to_agree_inj, leibniz_equiv_iff in Hrx as ->. 
    done. 
  Qed. 

  Lemma rels_agree a γ1 γ2 p1 p2 :
    REL a p1 γ1 ∗ REL a p2 γ2 -∗ ⌜γ1 = γ2⌝ ∧ ⌜p1 = p2⌝.
  Proof.
    rewrite REL_eq /REL_def.
    iIntros "[Hγ1 Hγ2]".
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
    iPureIntro.
    rewrite -auth_frag_op op_singleton in Hval.
    apply singleton_valid in Hval.
    apply (agree_op_invL' (A:=leibnizO _)) in Hval.
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


  (* When opening the region map at specific locations, 
     we will rely on assumptions on the current state of that location *)
  
  Definition temporary (W : WORLD) (l : Addr) :=
    match W.1.1 !! (countable.encode l) with
    | Some ρ => ρ = countable.encode Temporary
    | _ => False
    end.
  Definition permanent (W : WORLD) (l : Addr) :=
    match W.1.1 !! (countable.encode l) with
    | Some ρ => ρ = countable.encode Permanent
    | _ => False
    end.
  Definition revoked (W : WORLD) (l : Addr) :=
    match W.1.1 !! (countable.encode l) with
    | Some ρ => ρ = countable.encode Revoked
    | _ => False
    end.

  (* Definition and notation for updating a standard or local state in the STS collection *)
  Definition std_update (W : WORLD) (l : Addr) (a : region_type) (r1 r2 : region_type → region_type -> Prop) : WORLD :=
    ((<[countable.encode l := countable.encode a]>W.1.1,
      <[countable.encode l := (convert_rel r1,convert_rel r2)]>W.1.2), W.2). 
  Definition loc_update (W : WORLD) (l : Addr) (a : region_type) (r1 r2 : region_type → region_type -> Prop) : WORLD :=
    (W.1,(<[countable.encode l := countable.encode a]>W.2.1,
          <[countable.encode l := (convert_rel r1,convert_rel r2)]>W.2.2)).

  Notation "<s[ a := ρ , r ]s> W" := (std_update W a ρ r.1 r.2) (at level 10, format "<s[ a := ρ , r ]s> W").
  Notation "<l[ a := ρ , r ]l> W" := (loc_update W a ρ r.1 r.2) (at level 10, format "<l[ a := ρ , r ]l> W").

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- OPEN_REGION --------------------------------------- *)
  
  Definition open_region_def (a : Addr) (W : WORLD) : iProp Σ :=
    (∃ (M : relT), RELS M ∗ ⌜dom_equal (std_sta W) M⌝ ∗ region_map_def (delete a M) W)%I. 
  Definition open_region_aux : { x | x = @open_region_def }. by eexists. Qed.
  Definition open_region := proj1_sig open_region_aux.
  Definition open_region_eq : @open_region = @open_region_def := proj2_sig open_region_aux.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS FOR OPENING THE REGION MAP ----------------------------------- *)

  Lemma region_open_temp_pwl W l p φ :
    (std_sta W) !! (countable.encode l) = Some (countable.encode Temporary) →
    pwl p = true →
    rel l p φ ∗ region W ∗ sts_full_world sts_std W -∗
        ∃ v, open_region l W
           ∗ sts_full_world sts_std W
           ∗ sts_state_std (countable.encode l) Temporary
           ∗ l ↦ₐ[p] v
           ∗ ⌜p ≠ O⌝
           ∗ ▷ future_pub_mono φ v
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Htemp Hpwl) "(Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. 
    iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)".
    iDestruct "Hreg" as (M) "(HM & % & Hpreds)". 
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. 
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & Hmono & #Hφ' & Hφv)".  
    inversion H4; subst. rewrite Hpwl. iDestruct "Hmono" as "#Hmono".  
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv". 
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #".
      auto. 
    - iSplitR;[auto|]. iSplitR. 
      + rewrite /future_pub_mono.
        iApply later_intuitionistically_2. iAlways.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq''"). 
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq'"). iFrame. 
      + iNext. iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  Lemma region_open_temp_nwl W l p φ :
    (std_sta W) !! (countable.encode l) = Some (countable.encode Temporary) →
    pwl p = false →
    rel l p φ ∗ region W ∗ sts_full_world sts_std W -∗
        ∃ v, open_region l W
           ∗ sts_full_world sts_std W
           ∗ sts_state_std (countable.encode l) Temporary
           ∗ l ↦ₐ[p] v
           ∗ ⌜p ≠ O⌝
           ∗ ▷ future_priv_mono φ v
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Htemp Hpwl) "(Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M) "(HM & % & Hpreds)". 
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. 
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & Hmono & #Hφ' & Hφv)".  
    inversion H4; subst. rewrite Hpwl. iDestruct "Hmono" as "#Hmono".  
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv". 
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #".
      auto. 
    - iSplitR;[auto|]. iSplitR. 
      + rewrite /future_pub_mono.
        iApply later_intuitionistically_2. iAlways.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq''"). 
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq'"). iFrame. 
      + iNext. iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  Lemma region_open_perm W l p φ :
    (std_sta W) !! (countable.encode l) = Some (countable.encode Permanent) →
    rel l p φ ∗ region W ∗ sts_full_world sts_std W -∗
        ∃ v, open_region l W
           ∗ sts_full_world sts_std W
           ∗ sts_state_std (countable.encode l) Permanent              
           ∗ l ↦ₐ[p] v
           ∗ ⌜p ≠ O⌝
           ∗ ▷ future_priv_mono φ v
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Htemp) "(Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M) "(HM & % & Hpreds)". 
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. 
    1: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & #Hmono & #Hφ' & Hφv)".  
    inversion H4; subst.
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv". 
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #".
      auto. 
    - iSplitR;[auto|]. iSplitR. 
      + rewrite /future_priv_mono.
        iApply later_intuitionistically_2. iAlways.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq'"). 
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq''"). iFrame. 
      + iNext. iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  Lemma region_open W l p φ (ρ : region_type) :
    ρ ≠ Revoked →
    (std_sta W) !! (countable.encode l) = Some (countable.encode ρ) →
    rel l p φ ∗ region W ∗ sts_full_world sts_std W -∗
        ∃ v, open_region l W
           ∗ sts_full_world sts_std W
           ∗ sts_state_std (countable.encode l) ρ              
           ∗ l ↦ₐ[p] v
           ∗ ⌜p ≠ O⌝
           ∗ (▷ if (decide (ρ = Temporary ∧ pwl p = true))
             then future_pub_mono φ v
             else future_priv_mono φ v)
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Hne Htemp) "(Hrel & Hreg & Hfull)".
    destruct ρ; try contradiction.
    - destruct (pwl p) eqn:Hpwl.
      + iDestruct (region_open_temp_pwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
      + iDestruct (region_open_temp_nwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
    - iDestruct (region_open_perm with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
      iExists _; iFrame.
  Qed.

  (* Closing the region without updating the sts collection *)
  Lemma region_close_temp_pwl W l φ p v :
    pwl p = true →
    sts_state_std (countable.encode l) Temporary
                  ∗ open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_pub_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & % & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Temporary. iFrame. iExists _,_,p,_. rewrite Hpwl. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. auto.
  Qed.

  Lemma region_close_temp_nwl W l φ p v :
    pwl p = false →
    sts_state_std (countable.encode l) Temporary
                  ∗ open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & % & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Temporary. iFrame. iExists _,_,p,_. rewrite Hpwl. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. auto. 
  Qed.

  Lemma region_close_perm W l φ p v :
    sts_state_std (countable.encode l) Permanent
                  ∗ open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & % & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Permanent. iFrame. iExists _,_,_,_. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. auto. 
  Qed.

  Lemma region_close W l φ p v (ρ : region_type) :
    ρ ≠ Revoked →
    sts_state_std (countable.encode l) ρ
                  ∗ open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗
                  (if (decide (ρ = Temporary ∧ pwl p = true))
                   then future_pub_mono φ v
                   else future_priv_mono φ v) ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    iIntros (Hrev) "(Hstate & Hreg_open & Hl & Hp & Hmono & Hφ & Hrel)".
    destruct ρ; try contradiction.
    - destruct (pwl p) eqn:Hpwl.
      + iApply region_close_temp_pwl; eauto. iFrame.
      + iApply region_close_temp_nwl; eauto. iFrame.
    - iApply region_close_perm; eauto. iFrame.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------------- OPENING MULTIPLE LOCATIONS IN REGION --------------------------- *)
    
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
    (∃ M, RELS M ∗ ⌜dom_equal (std_sta W) M⌝ ∗ region_map_def (delete_list l M) W)%I.
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

  Lemma region_open_nil W :
    (region W ∗-∗ open_region_many [] W)%I.
  Proof.
    iSplit; iIntros "H";
    rewrite region_eq open_region_many_eq /=;
            iFrame.
  Qed.

  Lemma region_open_next_temp_pwl W φ ls l p :
    l ∉ ls →
    (std_sta W) !! (countable.encode l) = Some (countable.encode Temporary) ->
    pwl p = true →
    open_region_many ls W ∗ rel l p φ ∗ sts_full_world sts_std W -∗
                     ∃ v, open_region_many (l :: ls) W
                        ∗ sts_full_world sts_std W
                        ∗ sts_state_std (countable.encode l) Temporary
                        ∗ l ↦ₐ[p] v
                        ∗ ⌜p ≠ O⌝
                        ∗ ▷ future_pub_mono φ v
                        ∗ ▷ φ (W,v).
  Proof.
    rewrite open_region_many_eq . 
    iIntros (Hnin Htemp Hpwl) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=. 
    rewrite rel_eq /rel_def /rel_def /region_def REL_eq RELS_eq /rel /region /REL /RELS. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M) "(HM & % & Hpreds)". 
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. 
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & Hmono & #Hφ' & Hφv)".  
    inversion H4; subst. rewrite Hpwl. iDestruct "Hmono" as "#Hmono".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv". 
    - iExists _. repeat (rewrite -HMeq). iFrame "∗ #". auto. 
    - iSplitR;[auto|]. iSplitR.
      + rewrite /future_pub_mono.
        iApply later_intuitionistically_2. iAlways.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq''"). 
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq'"). iFrame. 
      + iNext. 
        iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_temp_nwl W φ ls l p :
    l ∉ ls →
    (std_sta W) !! (countable.encode l) = Some (countable.encode Temporary) ->
    pwl p = false →
    open_region_many ls W ∗ rel l p φ ∗ sts_full_world sts_std W -∗
                     ∃ v, open_region_many (l :: ls) W
                        ∗ sts_full_world sts_std W
                        ∗ sts_state_std (countable.encode l) Temporary
                        ∗ l ↦ₐ[p] v
                        ∗ ⌜p ≠ O⌝
                        ∗ ▷ future_priv_mono φ v
                        ∗ ▷ φ (W,v).
  Proof.
    rewrite open_region_many_eq . 
    iIntros (Hnin Htemp Hpwl) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=. 
    rewrite rel_eq /rel_def /rel_def /region_def REL_eq RELS_eq /rel /region /REL /RELS. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M) "(HM & % & Hpreds)". 
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. 
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & Hmono & #Hφ' & Hφv)".  
    inversion H4; subst. rewrite Hpwl. iDestruct "Hmono" as "#Hmono".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv". 
    - iExists _. repeat (rewrite -HMeq). iFrame "∗ #". auto. 
    - iSplitR;[auto|]. iSplitR.
      + rewrite /future_pub_mono.
        iApply later_intuitionistically_2. iAlways.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq''"). 
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq'"). iFrame. 
      + iNext. 
        iRewrite "Hφeq". iFrame.
  Qed.
  
  Lemma region_open_next_perm W φ ls l p :
    l ∉ ls → (std_sta W) !! (countable.encode l) = Some (countable.encode Permanent) -> 
    open_region_many ls W ∗ rel l p φ ∗ sts_full_world sts_std W -∗
                     ∃ v, sts_full_world sts_std W
                        ∗ sts_state_std (countable.encode l) Permanent
                        ∗ open_region_many (l :: ls) W
                        ∗ l ↦ₐ[p] v
                        ∗ ⌜p ≠ O⌝
                        ∗ ▷ future_priv_mono φ v
                        ∗ ▷ φ (W,v). 
  Proof.
    rewrite open_region_many_eq . 
    iIntros (Hnin Htemp) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /= /region_map_def. 
    rewrite rel_eq /rel_def /rel_def /region_def REL_eq RELS_eq /rel /region /REL /RELS. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M) "(HM & % & Hpreds)". 
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. 
    1: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H5. done. }    
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & #Hmono & #Hφ' & Hφv)".  
    inversion H4; subst. 
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv". 
    - rewrite /open_region.
      iExists _. repeat (rewrite -HMeq). iFrame "∗ #". auto. 
    - iSplitR;[auto|]. iSplitR.
      + iApply later_intuitionistically_2. iAlways.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq'"). 
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq''"). iFrame. 
      + iNext. 
        iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_close_next_temp_pwl W φ ls l p v :
    l ∉ ls ->
    pwl p = true →
    sts_state_std (countable.encode l) Temporary ∗
                  open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_pub_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
                  -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def. 
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & % & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iExists _,_,p,_. rewrite Hpwl. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -delete_list_delete; auto. rewrite -delete_list_insert; auto.
    rewrite -HMeq. 
    iFrame "# ∗". auto. 
  Qed.

  Lemma region_close_next_temp_nwl W φ ls l p v :
    l ∉ ls ->
    pwl p = false →
    sts_state_std (countable.encode l) Temporary ∗
                  open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
                  -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def. 
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & % & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iExists _,_,p,_. rewrite Hpwl. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -delete_list_delete; auto. rewrite -delete_list_insert; auto.
    rewrite -HMeq. 
    iFrame "# ∗". auto. 
  Qed.

  Lemma region_close_next_perm W φ ls l p v :
    l ∉ ls ->
    sts_state_std (countable.encode l) Permanent ∗
                  open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
                  -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def. 
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & % & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iExists _,_,_,_. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -delete_list_delete; auto. rewrite -delete_list_insert; auto.
    rewrite -HMeq. 
    iFrame "# ∗". auto. 
  Qed.

  Definition monotonicity_guarantees_region ρ w p φ :=
    (match ρ with
     | Temporary => if pwl p then future_pub_mono else future_priv_mono
     | Permanent => future_priv_mono
     | Revoked => λ (_ : prodO STS STS * Word → iProp Σ) (_ : Word), True
     end φ w)%I.

  Definition monotonicity_guarantees_decide ρ w p φ:=
    (if decide (ρ = Temporary ∧ pwl p = true)
     then future_pub_mono φ w
     else future_priv_mono φ w)%I.

   Lemma region_open_next
        (W : prodO (leibnizO (STS_states * STS_rels)) (leibnizO (STS_states * STS_rels)))
        (φ : prodO (leibnizO (STS_states * STS_rels)) (leibnizO (STS_states * STS_rels)) * Word → iProp Σ)
        (ls : list Addr) (l : Addr) (p : Perm) (ρ : region_type) (Hρnotrevoked : ρ <> Revoked):
    l ∉ ls
    → std_sta W !! countable.encode l = Some (countable.encode ρ)
    → open_region_many ls W ∗ rel l p φ ∗ sts_full_world sts_std W
                       -∗ ∃ v : Word,
        sts_full_world sts_std W
                       ∗ sts_state_std (countable.encode l) ρ
                       ∗ open_region_many (l :: ls) W
                       ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ ▷ monotonicity_guarantees_region ρ v p φ ∗
                       ▷ φ (W, v).
   Proof.
    unfold monotonicity_guarantees_region.
    intros. iIntros "H".
    destruct ρ; try congruence.
    - case_eq (pwl p); intros.
      + iDestruct (region_open_next_temp_pwl with "H") as (v) "[A [B [C D]]]"; eauto.
        iExists v. iFrame.
      + iDestruct (region_open_next_temp_nwl with "H") as (v) "[A [B [C D]]]"; eauto.
        iExists v. iFrame.
    - iApply (region_open_next_perm with "H"); eauto.
  Qed.

  Lemma region_close_next
        (W : prodO (leibnizO (STS_states * STS_rels)) (leibnizO (STS_states * STS_rels)))
        (φ : prodO (leibnizO (STS_states * STS_rels)) (leibnizO (STS_states * STS_rels)) * Word → iProp Σ)
        (ls : list Addr) (l : Addr) (p : Perm) (v : Word) (ρ : region_type) (Hρnotrevoked : ρ <> Revoked):
    l ∉ ls
    → sts_state_std (countable.encode l) ρ
                    ∗ open_region_many (l :: ls) W
                    ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ monotonicity_guarantees_region ρ v p φ ∗ ▷ φ (W, v) ∗ rel l p φ -∗
                    open_region_many ls W.
  Proof.
    unfold monotonicity_guarantees_region.
    intros. iIntros "[A [B [C [D [E [F G]]]]]]".
    destruct ρ; try congruence.
    - case_eq (pwl p); intros.
      + iApply (region_close_next_temp_pwl with "[A B C D E F G]"); eauto; iFrame.
      + iApply (region_close_next_temp_nwl with "[A B C D E F G]"); eauto; iFrame.
    - iApply (region_close_next_perm with "[A B C D E F G]"); eauto; iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT STD TRANSITIONS -------------------------- *)
  
  Lemma full_sts_world_is_Some_rel_std W (a : Addr) :
    is_Some ((std_sta W) !! (countable.encode a)) →
    sts_full_world sts_std W -∗ ⌜rel_is_std_i W (countable.encode a)⌝.
  Proof. 
    iIntros (Hsome) "[[% [% _] ] _]".
    iPureIntro. apply elem_of_subseteq in H3.
    apply elem_of_gmap_dom in Hsome. 
    specialize (H3 _ Hsome).
    specialize (H4 (countable.encode a)). apply H4. 
    apply elem_of_gmap_dom. auto.
  Qed.

  Lemma related_sts_preserve_std W W' :
    related_sts_priv_world W W' →
    rel_is_std W →
    (∀ i, is_Some ((std_rel W) !! i) → rel_is_std_i W' i). 
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]; simpl.
    destruct W' as [ [Wstd_sta' Wstd_rel'] Wloc']; simpl.
    intros [ [Hdom_sta [Hdom_rel Hrelated] ] _] Hstd i Hi. simpl in *.
    apply elem_of_gmap_dom in Hi. apply elem_of_subseteq in Hdom_rel.
    specialize (Hdom_rel _ Hi).
    apply elem_of_gmap_dom in Hdom_rel as [ [r1' r2'] Hr'].
    apply elem_of_gmap_dom in Hi as Hr.
    specialize (Hstd _ Hr). destruct Hr as [x Hr]. 
    specialize (Hrelated i _ _ _ _ Hstd Hr') as (Heq1 & Heq2 & Hrelated). 
    rewrite /std_rel /=. subst. auto.
  Qed.

  Lemma related_sts_rel_std W W' i :
    related_sts_priv_world W W' →
    rel_is_std_i W i → rel_is_std_i W' i.
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]; simpl.
    destruct W' as [ [Wstd_sta' Wstd_rel'] Wloc']; simpl.
    rewrite /rel_is_std_i. 
    intros [ [Hdom_sta [Hdom_rel Hrelated] ] _] Hi. simpl in *.
    assert (is_Some (Wstd_rel' !! i)) as [ [r1' r2'] Hr'].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_rel.
      apply Hdom_rel. apply elem_of_gmap_dom. eauto. }
    specialize (Hrelated i _ _ _ _ Hi Hr') as (-> & -> & Hrelated).
    eauto. 
  Qed.
  
  Lemma std_rel_pub_Permanent x :
    (convert_rel std_rel_pub) (countable.encode Permanent) x → x = countable.encode Permanent.
  Proof.
    intros Hrel.
    inversion Hrel as [ρ Hb].
    destruct Hb as [b [Heqρ [Heqb Hρb] ] ].
    subst. inversion Hρb. subst. apply encode_inj in Heqρ. inversion Heqρ.
  Qed.

  Lemma std_rel_pub_rtc_Permanent x y :
    x = countable.encode Permanent →
    rtc (convert_rel std_rel_pub) x y → y = countable.encode Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply std_rel_pub_Permanent in H3.
    apply IHHrtc. auto.
  Qed.

  Lemma std_rel_priv_Permanent x :
    (convert_rel std_rel_priv) (countable.encode Permanent) x → x = countable.encode Permanent.
  Proof.
    intros Hrel.
    inversion Hrel as [ρ Hb].
    destruct Hb as [b [Heqρ [Heqb Hρb] ] ].
    subst. inversion Hρb; subst; auto. apply encode_inj in Heqρ. inversion Heqρ.
  Qed.

  Lemma std_rel_priv_rtc_Permanent x y :
    x = countable.encode Permanent →
    rtc (convert_rel std_rel_priv) x y → y = countable.encode Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply std_rel_priv_Permanent in H3.
    apply IHHrtc. auto.
  Qed.

  Lemma std_rel_rtc_Permanent x y :
    x = countable.encode Permanent →
    rtc (λ x0 y0 : positive, convert_rel std_rel_pub x0 y0 ∨ convert_rel std_rel_priv x0 y0) x y →
    y = countable.encode Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc as [|x y z Hrel];auto.
    subst. destruct Hrel as [Hrel | Hrel].
    - apply std_rel_pub_Permanent in Hrel. auto.
    - apply std_rel_priv_Permanent in Hrel. auto. 
  Qed. 
      
  Lemma std_rel_pub_Temporary x :
    (convert_rel std_rel_pub) (countable.encode Temporary) x → x = countable.encode Temporary.
  Proof.
    intros Hrel.
    inversion Hrel as [ρ Hb].
    destruct Hb as [b [Heqρ [Heqb Hρb] ] ].
    subst. inversion Hρb. subst. apply encode_inj in Heqρ. inversion Heqρ.
  Qed.

  Lemma std_rel_pub_rtc_Temporary x y :
    x = countable.encode Temporary →
    rtc (convert_rel std_rel_pub) x y → y = countable.encode Temporary.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply std_rel_pub_Temporary in H3.
    apply IHHrtc. auto.
  Qed.

  Lemma std_rel_pub_Revoked x :
    (convert_rel std_rel_pub) (countable.encode Revoked) x → x = countable.encode Temporary (* ∨ x = countable.encode Revoked *).
  Proof.
    intros Hrel.
    inversion Hrel as [ρ Hb].
    destruct Hb as [b [Heqρ [Heqb Hρb] ] ].
    subst. inversion Hρb. subst. auto.
  Qed.

  Lemma std_rel_pub_rtc_Revoked x y :
    x = countable.encode Revoked →
    rtc (convert_rel std_rel_pub) x y → y = countable.encode Temporary ∨ y = countable.encode Revoked.
  Proof.
    intros Hx Hrtc.
    inversion Hrtc; subst; auto. 
    apply std_rel_pub_Revoked in H3. subst. 
    apply std_rel_pub_rtc_Temporary in H4; auto. 
  Qed. 

  Lemma std_rel_exist x y :
    (∃ (ρ : region_type), countable.encode ρ = x) → 
    rtc (λ x0 y0 : positive, convert_rel std_rel_pub x0 y0 ∨ convert_rel std_rel_priv x0 y0) x y →
    ∃ (ρ : region_type), y = countable.encode ρ. 
  Proof.
    intros Hsome Hrel.
    induction Hrel; [destruct Hsome as [ρ Hsome]; eauto|].
    destruct H3 as [Hpub | Hpriv].
    - inversion Hpub as [ρ [ρ' [Heq1 [Heq2 Hsome'] ] ] ].
      apply IHHrel. eauto.
    - inversion Hpriv as [ρ [ρ' [Heq1 [Heq2 Hsome'] ] ] ].
      apply IHHrel. eauto.
  Qed.
  
End heap.

Notation "<s[ a := ρ , r ]s> W" := (std_update W a ρ r.1 r.2) (at level 10, format "<s[ a := ρ , r ]s> W").
Notation "<l[ a := ρ , r ]l> W" := (loc_update W a ρ r.1 r.2) (at level 10, format "<l[ a := ρ , r ]l> W").
