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

  Definition pwl p : bool :=
    match p with
    | RWLX | RWL => true
    | _ => false
    end.

  (* We will first define the standard STS for the shared part of the heap *)
  Inductive region_type :=
  | Temporary
  | Permanent
  | Revoked.

  Global Instance region_type_EqDecision : EqDecision region_type.
  Proof.
    intros ρ1 ρ2.
    destruct ρ1,ρ2;
      [by left|by right|by right|by right|
         by left|by right|by right|by right|by left]. 
  Qed.
  Global Instance region_type_finite : finite.Finite region_type.
  Proof.
    refine {| finite.enum := [Temporary; Permanent; Revoked] ;
              finite.NoDup_enum := _ ;
              finite.elem_of_enum := _ |}.
    - repeat (apply NoDup_cons; split; [repeat (apply not_elem_of_cons;split;auto); apply not_elem_of_nil|]).
        by apply NoDup_nil.
    - intros ρ.
      destruct ρ;apply elem_of_cons;[by left|right|right];
        apply elem_of_cons;[by left|right];
          apply elem_of_cons; by left. 
  Qed.           
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

  (* ------------------------------------------------------------------- *)
  (* region_map is monotone with regards to public future world relation *)
  
  Lemma region_map_monotone W W' M :
    (⌜related_sts_pub_world W W'⌝ →
     region_map_def M W -∗ region_map_def M W')%I.
  Proof.
    iIntros (Hrelated) "Hr".
    iApply big_sepM_mono; iFrame. 
    iIntros (a γ Hsome) "Hm".
    iDestruct "Hm" as (ρ) "[Hstate Hm]".
    iExists ρ. iFrame. 
    destruct ρ.
    - iDestruct "Hm" as (γpred v p φ Heq HO) "(Hl & Hmono & #Hsavedφ & Hφ)".
      iExists _,_,_,_. do 2 (iSplitR;[eauto|]).
      destruct (pwl p);
      (iDestruct "Hmono" as "#Hmono"; iFrame "∗ #";
        iApply "Hmono"; iFrame; auto); 
      try (iPureIntro; by apply related_sts_pub_priv_world).      
    - iDestruct "Hm" as (γpred v p φ Heq HO) "(Hl & #Hmono & #Hsavedφ & Hφ)".
      iExists _,_,_,_. do 2 (iSplitR;[eauto|]).
      iFrame "∗ #".
      iApply "Hmono"; iFrame; auto. 
      iPureIntro. 
      by apply related_sts_pub_priv_world. 
    - done.
  Qed. 
    
  Lemma region_monotone W W' :
    (⌜dom (gset positive) (std_sta W) = dom (gset positive) (std_sta W')⌝ →
     ⌜related_sts_pub_world W W'⌝ → region W -∗ region W')%I.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite region_eq.
    iDestruct "HW" as (M) "(HM & % & Hmap)". 
    iExists (M). iFrame.
    iApply (wand_frame_r _ emp%I).
    { iIntros (_).
      iPureIntro.
      intros a. split; intros [x Hx].
      - destruct H3 with a as [Hstd _].
        apply Hstd. apply elem_of_gmap_dom.
        rewrite Hdomeq. apply elem_of_gmap_dom. eauto.
      - destruct H3 with a as [_ Hstd].
        apply elem_of_gmap_dom. rewrite -Hdomeq.
        apply elem_of_gmap_dom. eauto.
    } iSplitR;[auto|].
    iApply region_map_monotone; eauto. 
  Qed.    
    
  Lemma related_sts_pub_world_fresh W a ρ :
    (countable.encode a) ∉ dom (gset positive) (std_sta W) →
    (countable.encode a) ∉ dom (gset positive) (std_rel W) →
    related_sts_pub_world W (<s[a:=ρ,(Rpub,Rpriv)]s> W).
  Proof.
    rewrite /std_sta /std_rel. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split;[|split;[auto|] ]. 
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq. 
    - apply not_elem_of_dom in Hdom_sta.
      apply not_elem_of_dom in Hdom_rel.
      intros i r1 r2 r1' r2' Hr Hr'. 
      destruct (decide (countable.encode a = i)).
      + subst. rewrite Hr in Hdom_rel. done. 
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy. 
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy. 
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

   Lemma related_sts_pub_world_fresh_state W a ρ :
    (countable.encode a) ∉ dom (gset positive) (std_sta W) →
    rel_is_std_i W (countable.encode a) →
    related_sts_pub_world W (<s[a:=ρ,(Rpub,Rpriv)]s> W).
  Proof.
    rewrite /std_sta /std_rel. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split;[|split;[auto|] ]. 
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq. 
    - apply not_elem_of_dom in Hdom_sta.
      intros i r1 r2 r1' r2' Hr Hr'. 
      destruct (decide (countable.encode a = i)).
      + subst. rewrite /rel_is_std_i Hr in Hdom_rel. rewrite lookup_insert in Hr'. simplify_eq.
        repeat (split;auto). intros x y Hcontr. rewrite Hcontr in Hdom_sta. done. 
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy. 
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy. 
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

  Lemma related_sts_pub_world_revoked_temp W a :
    (std_sta W) !! (countable.encode a) = Some (countable.encode Revoked) ∨
    (std_sta W) !! (countable.encode a) = Some (countable.encode Temporary) →
    rel_is_std_i W (countable.encode a) →
    related_sts_pub_world W (<s[a:=Temporary,(Rpub, Rpriv)]s>W).
  Proof.
    intros Ha Hstd.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split;[|split;[auto|] ]. 
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq. 
    - intros i r1 r2 r1' r2' Hr Hr'. 
      destruct (decide (countable.encode a = i)).
      + subst. rewrite /rel_is_std_i Hr in Hstd. rewrite lookup_insert in Hr'. simplify_eq.
        repeat (split;auto). intros x y Hx Hy.
        rewrite Hx in Ha.
        destruct Ha as [Ha | Ha]; inversion Ha.
        ++ rewrite lookup_insert in Hy. inversion Hy.
           right with (countable.encode Temporary);[|left].
           exists Revoked,Temporary. repeat (split;auto).
        ++ rewrite lookup_insert in Hy. inversion Hy. left. 
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy. 
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy. 
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ----------------------- LEMMAS FOR EXTENDING THE REGION MAP ----------------------------------- *)
  
  Lemma extend_region_temp_pwl E W l p v φ `{∀ W v, Persistent (φ (W,v))}:
     p ≠ O →
     (countable.encode l) ∉ dom (gset positive) (std_sta W) →
     (countable.encode l) ∉ dom (gset positive) (std_rel W) →
     (pwl p) = true →
     (future_pub_mono φ v →
     sts_full_world sts_std W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Temporary, (Rpub,Rpriv) ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world sts_std (<s[l := Temporary, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1 Hnone2 Hpwl) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & % & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ') "[Hstate Hl']". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply not_elem_of_dom in Hnone1. 
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done. 
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W (countable.encode l) Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.     
    apply (related_sts_pub_world_fresh W l Temporary) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert. 
    iFrame "HR". iFrame.
    iSplitL;[iSplitR|].
    - iPureIntro. apply dom_equal_insert; auto. 
    - iApply big_sepM_insert; auto.
      iFrame. iExists Temporary.
      iFrame. iExists γpred,v,_,φ. iSplitR;[auto|]. iFrame "∗ #".
      iSplitR;[done|].
      rewrite Hpwl. iFrame "#".
      iNext. iApply "Hmono"; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done. 
  Qed.

  Lemma extend_region_temp_nwl E W l p v φ `{∀ W v, Persistent (φ (W,v))}:
     p ≠ O →
     (countable.encode l) ∉ dom (gset positive) (std_sta W) →
     (countable.encode l) ∉ dom (gset positive) (std_rel W) →
     (pwl p) = false →
     (future_priv_mono φ v →
     sts_full_world sts_std W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Temporary, (Rpub,Rpriv) ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world sts_std (<s[l := Temporary, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1 Hnone2 Hpwl) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & % & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ') "[Hstate Hl']". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply not_elem_of_dom in Hnone1. 
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done. 
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W (countable.encode l) Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.     
    apply (related_sts_pub_world_fresh W l Temporary) in Hnone1 as Hrelated; auto. 
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert. 
    iFrame "HR". iFrame.
    iSplitL;[iSplitR|].
    - iPureIntro. apply dom_equal_insert; auto. 
    - iApply big_sepM_insert; auto.
      iFrame. iExists Temporary.
      iFrame. iExists γpred,v,_,φ. iSplitR;[auto|]. iFrame "∗ #".
      iSplitR;[done|].
      rewrite Hpwl. iFrame "#".
      iNext. iApply "Hmono"; eauto.
      iPureIntro. by apply related_sts_pub_priv_world. 
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done. 
  Qed.

  Lemma extend_region_perm E W l p v φ `{∀ W v, Persistent (φ (W,v))}:
     p ≠ O →
     (countable.encode l) ∉ dom (gset positive) (std_sta W) →
     (countable.encode l) ∉ dom (gset positive) (std_rel W) →
     (future_priv_mono φ v →
     sts_full_world sts_std W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Permanent, (Rpub,Rpriv) ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world sts_std (<s[l := Permanent, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1 Hnone2) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & % & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ') "[Hstate Hl']". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply not_elem_of_dom in Hnone1. 
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done. 
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W (countable.encode l) Permanent
            with "[] Hfull") as "(Hfull & Hstate)"; auto.     
    apply (related_sts_pub_world_fresh W l Permanent) in Hnone1 as Hrelated; auto. 
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert. 
    iFrame "HR". iFrame.
    iSplitL;[iSplitR|].
    - iPureIntro. apply dom_equal_insert; auto. 
    - iApply big_sepM_insert; auto.
      iFrame. iExists Permanent.
      iFrame. iExists γpred,v,_,φ. iSplitR;[auto|]. iFrame "∗ #".
      iSplitR;[done|].
      iNext. iApply "Hmono"; eauto.
      iPureIntro. by apply related_sts_pub_priv_world. 
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done. 
  Qed.

  (* The following allocates a Revoked region. This allocates the saved predicate and the region state, *)
  (* but since a revoked region is empty, there is no need to assume any resources for that region *)

  Lemma extend_region_revoked E W l p φ :
     (countable.encode l) ∉ dom (gset positive) (std_sta W) →
     (countable.encode l) ∉ dom (gset positive) (std_rel W) →
     (sts_full_world sts_std W -∗ region W ={E}=∗ region (<s[l := Revoked, (Rpub,Rpriv) ]s>W)
                                               ∗ rel l p φ
                                               ∗ sts_full_world sts_std (<s[l := Revoked, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hnone1 Hnone2) "Hfull Hreg".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & % & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ') "[Hstate Hl']". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply not_elem_of_dom in Hnone1. 
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,p)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,p)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done. 
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W (countable.encode l) Revoked
            with "[] Hfull") as "(Hfull & Hstate)"; auto.     
    apply (related_sts_pub_world_fresh W l Revoked) in Hnone1 as Hrelated; auto. 
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert. 
    iFrame "HR". iFrame.
    iSplitL;[iSplitR|].
    - iPureIntro. apply dom_equal_insert; auto. 
    - iApply big_sepM_insert; auto.
      iFrame. iExists Revoked. iFrame. 
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done.
  Qed.

  (* As a followup of above, the following lemma takes a revoked region and makes it Temporary. *)

  Lemma update_region_revoked_temp_pwl E W l p v φ `{∀ W v, Persistent (φ (W,v))} :
    (std_sta W) !! (countable.encode l) = Some (countable.encode Revoked) →
    p ≠ O → pwl p = true →
    (future_pub_mono φ v -∗
    sts_full_world sts_std W -∗
    region W -∗
    l ↦ₐ[p] v -∗ φ (W,v) -∗ rel l p φ ={E}=∗ region (<s[l := Temporary, (Rpub,Rpriv) ]s>W)
                             ∗ sts_full_world sts_std (<s[l := Temporary, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hrev HO Hpwl) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M) "(Hγrel & Hdom & Hpreds)".
    iDestruct "Hdom" as %Hdom. 
    rewrite RELS_eq /RELS_def. 
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]". 
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".     
    iDestruct "Hl'" as (ρ) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    iDestruct (sts_full_rel_state_std with "Hsts Hstate") as %Hstd. 
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. apply encode_inj in Hρrev. subst. 
    iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Temporary,(Rpub, Rpriv)]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto. }
    iDestruct (region_map_monotone $! Hrelated with "Hr") as "Hr".
    iDestruct ("Hmono" $! _ _ Hrelated with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { specialize (Hdom (countable.encode l)).
      destruct Hdom as [ [a [Heq [x Hsome] ] ] _];[eauto|].
      apply encode_inj in Heq; subst. eauto. }
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame.
      iExists γ, v, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). iFrame.
      rewrite Hpwl. iFrame "#". }
    apply insert_id in Hstd.
    rewrite /std_update /= Hstd. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iPureIntro. 
    apply insert_id in Hsome. rewrite -Hsome.
    by apply dom_equal_insert. 
  Qed.

   Lemma update_region_revoked_temp_nwl E W l p v φ `{∀ W v, Persistent (φ (W,v))} :
    (std_sta W) !! (countable.encode l) = Some (countable.encode Revoked) →
    p ≠ O →
    (future_priv_mono φ v -∗
    sts_full_world sts_std W -∗
    region W -∗
    l ↦ₐ[p] v -∗ φ (W,v) -∗ rel l p φ ={E}=∗ region (<s[l := Temporary, (Rpub,Rpriv) ]s>W)
                             ∗ sts_full_world sts_std (<s[l := Temporary, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hrev HO) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M) "(Hγrel & Hdom & Hpreds)".
    iDestruct "Hdom" as %Hdom. 
    rewrite RELS_eq /RELS_def. 
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]". 
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".     
    iDestruct "Hl'" as (ρ) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    iDestruct (sts_full_rel_state_std with "Hsts Hstate") as %Hstd. 
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. apply encode_inj in Hρrev. subst. 
    iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Temporary,(Rpub, Rpriv)]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto. }
    assert (related_sts_priv_world W (<s[l := Temporary,(Rpub, Rpriv)]s> W)) as Hrelated'.
    { apply related_sts_pub_priv_world. auto. }
    iDestruct (region_map_monotone $! Hrelated with "Hr") as "Hr".
    iDestruct ("Hmono" $! _ _ Hrelated' with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { specialize (Hdom (countable.encode l)).
      destruct Hdom as [ [a [Heq [x Hsome] ] ] _];[eauto|].
      apply encode_inj in Heq; subst. eauto. }
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame.
      iExists γ, v, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). iFrame.
      destruct (pwl p); iFrame "#".
      iIntros (W' W'' Hrelated''). iAlways. iIntros "HφW'".
      iApply ("Hmono" with "[] HφW'").
      iPureIntro. apply related_sts_pub_priv_world; auto. 
    } 
    apply insert_id in Hstd.
    rewrite /std_update /= Hstd. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iPureIntro. 
    apply insert_id in Hsome. rewrite -Hsome.
    by apply dom_equal_insert. 
  Qed. 
    
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
        rewrite decide_True; auto.
      + iDestruct (region_open_temp_nwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
        rewrite decide_False;auto. 
        intros [_ Hcontr]. done.
    - iDestruct (region_open_perm with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
      iExists _; iFrame.
      rewrite decide_False; auto. intros [Hcontr _]. done.
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
        rewrite decide_True; auto.
      + iApply region_close_temp_nwl; eauto. iFrame.
        rewrite decide_False; auto. intros [_ Hcontr]. done.
    - iApply region_close_perm; eauto. iFrame.
      rewrite decide_False; auto. intros [Hcontr _]. done.
  Qed.

  (* --------------------------------------------------------------------------------------------------------- *)
  (* --------------------------------------------- REVOCATION ------------------------------------------------ *)
  (* --------------------------------------------------------------------------------------------------------- *)

  (* 
     Revocation turns every temporary location state to revoked. 
     Revocation is crucial to privately update state: in general, 
     region states are only monotone with regards to public future 
     world. To do a private update, we must thus revoke all temp 
     regions, after which we only have regions that are indeed 
     monotone wrt private future world.
   *)
  

  (* Revocation only changes the states of the standard STS collection *)
  Definition revoke_std_sta : STS_states → STS_states :=
    fmap (λ v, if ((countable.encode Temporary) =? v)%positive then countable.encode Revoked else v). 
  Definition revoke W : WORLD := ((revoke_std_sta (std_sta W),std_rel W), loc W).

  (* A weaker revocation which only revokes elements from a list *)
  Fixpoint revoke_list_std_sta (l : list positive) (fs : STS_states) : STS_states :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => if ((countable.encode Temporary) =? j)%positive
                          then <[i := countable.encode Revoked]> (revoke_list_std_sta l' fs)
                          else (revoke_list_std_sta l' fs)
               | None => (revoke_list_std_sta l' fs)
               end
    end.
  Definition revoke_list l W : WORLD := ((revoke_list_std_sta l (std_sta W),std_rel W), loc W).


  (* -------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT REVOKE ---------------------------- *)
  
  Lemma revoke_list_swap Wstd_sta l a b :
    revoke_list_std_sta (a :: b :: l) Wstd_sta = revoke_list_std_sta (b :: a :: l) Wstd_sta.
  Proof.
    destruct (decide (a = b)).
    - subst. done.
    - simpl. destruct (Wstd_sta !! b) eqn:Hb,(Wstd_sta !! a) eqn:Ha; try reflexivity.
      destruct (countable.encode Temporary =? p0)%positive eqn:Hp0,
               (countable.encode Temporary =? p)%positive eqn:Hp; try reflexivity. 
      rewrite insert_commute; auto.
  Qed.

  Lemma revoke_list_swap_middle Wstd_sta l1 l2 a :
    revoke_list_std_sta (l1 ++ a :: l2) Wstd_sta = revoke_list_std_sta (a :: l1 ++ l2) Wstd_sta.
  Proof.
    induction l1.
    - done.
    - assert (a :: (a0 :: l1) ++ l2 = a :: a0 :: l1 ++ l2) as -> ; auto.
      assert ((a0 :: l1) ++ a :: l2 = a0 :: l1 ++ a :: l2) as ->; auto. 
      rewrite revoke_list_swap. simpl. rewrite IHl1. done.
  Qed.

  Lemma revoke_list_permutation Wstd_sta l1 l2 :
    l1 ≡ₚ l2 →
    revoke_list_std_sta l1 Wstd_sta = revoke_list_std_sta l2 Wstd_sta.
  Proof.
    intros Hperm. 
    induction Hperm using Permutation_ind.
    - done.
    - simpl. destruct (Wstd_sta !! x); auto.
      destruct (countable.encode Temporary =? p)%positive; auto.
      f_equiv. done.
    - by rewrite revoke_list_swap.
    - by rewrite IHHperm1 IHHperm2.
  Qed.

  Lemma revoke_list_insert_insert i x y l m :
    <[i:=x]> (revoke_list_std_sta l (<[i:=y]> m)) = <[i:=x]> (revoke_list_std_sta l m).
  Proof.
    induction l. 
    - simpl. rewrite insert_insert. done.
    - simpl. destruct (m !! a) eqn:Hsome.
      + destruct (decide (a = i)).
        * subst. rewrite lookup_insert. 
          destruct (countable.encode Temporary =? y)%positive,(countable.encode Temporary =? p)%positive;
            try rewrite insert_insert; auto.
          rewrite IHl. rewrite insert_insert;auto.
        * rewrite lookup_insert_ne;auto. rewrite Hsome.
          destruct (countable.encode Temporary =? p)%positive;auto.
          do 2 (rewrite (insert_commute _ i a);auto). 
          f_equiv. done.
      + destruct (decide (a = i)).
        * subst. rewrite lookup_insert.
          destruct (countable.encode Temporary =? y)%positive; auto.
          rewrite insert_insert. done.
        * rewrite lookup_insert_ne;auto. rewrite Hsome.
          done. 
  Qed.

  Lemma revoke_list_not_elem_of i x l m :
    i ∉ l →
    <[i:=x]> (revoke_list_std_sta l m) = revoke_list_std_sta l (<[i:=x]> m).
  Proof.
    induction l;intros Hnin.
    - done.
    - apply not_elem_of_cons in Hnin as [Hneq Hnin]. 
      simpl. destruct (m !! a) eqn:Hsome.
      + rewrite lookup_insert_ne;auto. rewrite Hsome.
        destruct (countable.encode Temporary =? p)%positive; auto.
        rewrite insert_commute;auto. f_equiv. auto.
      + rewrite lookup_insert_ne;auto. rewrite Hsome.
        auto.
  Qed.

  Lemma revoke_list_not_elem_of_lookup i l m :
    i ∉ l →
    (revoke_list_std_sta l m) !! i = m !! i.
  Proof.
    induction l; intros Hnin. 
    - done.
    - apply not_elem_of_cons in Hnin as [Hneq Hnin]. 
      simpl. destruct (m !! a) eqn:Hsome.
      + destruct (countable.encode Temporary =? p)%positive; auto.
        rewrite lookup_insert_ne; auto. 
      + auto.
  Qed.

  Lemma revoke_list_dom_std_sta (Wstd_sta : STS_states) :
    revoke_std_sta Wstd_sta = revoke_list_std_sta (map_to_list Wstd_sta).*1 Wstd_sta.
  Proof.
    induction Wstd_sta using map_ind.
    - rewrite /revoke /revoke_std_sta /=. 
        by rewrite fmap_empty map_to_list_empty /revoke_list /std_sta /std_rel /=.
    - rewrite /revoke /revoke_std_sta /=.
      rewrite fmap_insert.
      apply map_to_list_insert with m i x in H3 as Hperm.
      apply (fmap_Permutation fst) in Hperm. 
      rewrite /revoke_list (revoke_list_permutation _ _ ((i, x) :: map_to_list m).*1); auto.
      rewrite /= lookup_insert.
      destruct (countable.encode Temporary =? x)%positive; auto.
      + rewrite /revoke_std_sta in IHWstd_sta. rewrite IHWstd_sta. 
        rewrite revoke_list_insert_insert. repeat f_equiv. 
      + rewrite /revoke_std_sta in IHWstd_sta. rewrite IHWstd_sta. 
        apply revoke_list_not_elem_of.
        intros Hcontr. apply (elem_of_list_fmap_2 fst) in Hcontr.
        destruct Hcontr as [ [y1 y2] [Hy Hyin] ]. subst.
        apply elem_of_map_to_list in Hyin. simpl in *. congruence.
  Qed. 
  
  Lemma revoke_list_dom W :
    revoke W = revoke_list (map_to_list W.1.1).*1 W.
  Proof.
    by rewrite /revoke_list /= -revoke_list_dom_std_sta /revoke /std_sta. 
  Qed.

  Lemma map_to_list_fst {A B : Type} `{EqDecision A, Countable A} (m : gmap A B) i :
    i ∈ (map_to_list m).*1 ↔ (∃ x, (i,x) ∈ (map_to_list m)).
  Proof.
    split.
    - intros Hi.
      destruct (m !! i) eqn:Hsome.
      + exists b. by apply elem_of_map_to_list.
      + rewrite -(list_to_map_to_list m) in Hsome.
        eapply not_elem_of_list_to_map in Hsome. done. 
    - intros [x Hix].
      apply elem_of_list_fmap.
      exists (i,x). auto. 
  Qed.       

  Lemma revoke_list_lookup_Some Wstd_sta l (i : positive) :
    is_Some (Wstd_sta !! i) ↔ is_Some ((revoke_list_std_sta l Wstd_sta) !! i). 
  Proof.
    split.
    - induction l.
      + done.
      + intros [x Hx]. 
      simpl.
      destruct (Wstd_sta !! a);[|apply IHl;eauto].
      destruct (countable.encode Temporary =? p)%positive;[|apply IHl;eauto].
      destruct (decide (a = i)).
        * subst. rewrite lookup_insert. eauto.
        * rewrite lookup_insert_ne;eauto. 
    - induction l.
      + done.
      + intros [x Hx].
        simpl in Hx.
        destruct (Wstd_sta !! a) eqn:Hsome;eauto. 
        destruct (countable.encode Temporary =? p)%positive;[|apply IHl;eauto].
        destruct (decide (a = i)).
        * subst. eauto. 
        * rewrite lookup_insert_ne in Hx;eauto. 
  Qed.
  
  Lemma revoke_lookup_Some W (i : positive) :
    is_Some ((std_sta W) !! i) ↔ is_Some ((std_sta (revoke W)) !! i).
  Proof.
    rewrite revoke_list_dom.
    apply revoke_list_lookup_Some. 
  Qed.

  Lemma revoke_lookup_None W (i : positive) :
    (std_sta W) !! i = None <-> (std_sta (revoke W)) !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply revoke_lookup_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply revoke_lookup_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
  Qed. 

  Lemma revoke_std_sta_lookup_Some Wstd_sta (i : positive) :
    is_Some (Wstd_sta !! i) ↔ is_Some (revoke_std_sta Wstd_sta !! i).
  Proof.
    split; intros Hi. 
    - assert (std_sta (Wstd_sta, ∅ : STS_rels, (∅,∅)) = Wstd_sta) as Heq;auto.
      rewrite -Heq in Hi. 
      apply (revoke_lookup_Some ((Wstd_sta,∅),∅) i) in Hi. 
      auto.
    - assert (std_sta (Wstd_sta, ∅ : STS_rels, (∅,∅)) = Wstd_sta) as <-;auto.
      apply (revoke_lookup_Some ((Wstd_sta,∅),∅) i). 
      auto.
  Qed. 

  Lemma revoke_list_nin Wstd_sta (l : list positive) (i : positive) :
    i ∉ l → (revoke_list_std_sta l Wstd_sta) !! i = Wstd_sta !! i.
  Proof.
    intros Hnin.
    induction l.
    - done.
    - apply not_elem_of_cons in Hnin as [Hneq Hnin].
      simpl. destruct (Wstd_sta !! a); auto.
      destruct  (countable.encode Temporary =? p)%positive;auto. 
      rewrite lookup_insert_ne; auto.
  Qed. 
      
  Lemma revoke_list_lookup_Temp (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    (Wstd_sta !! i = Some (countable.encode Temporary)) →
    (revoke_list_std_sta (i :: l) Wstd_sta) !! i = Some (countable.encode Revoked). 
  Proof.
    intros Hp.
    rewrite /= Hp Positive_as_OT.eqb_refl. 
    apply lookup_insert. 
  Qed.

  Lemma revoke_list_lookup_middle_Temp (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∈ l →
    (Wstd_sta !! i = Some (countable.encode Temporary)) →
    (revoke_list_std_sta l Wstd_sta) !! i = Some (countable.encode Revoked). 
  Proof.
    intros Hin Hp.
    apply elem_of_list_split in Hin as [l1 [l2 ->] ].
    rewrite revoke_list_swap_middle.
    by apply revoke_list_lookup_Temp. 
  Qed.

  Lemma revoke_lookup_Temp Wstd_sta i :
    (Wstd_sta !! i = Some (countable.encode Temporary)) →
    (revoke_std_sta Wstd_sta) !! i = Some (countable.encode Revoked).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    apply revoke_list_lookup_middle_Temp; auto.
    apply map_to_list_fst. exists (countable.encode Temporary).
      by apply elem_of_map_to_list.
  Qed. 

  Lemma revoke_list_lookup_Revoked (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    (Wstd_sta !! i = Some (countable.encode Revoked)) →
    (revoke_list_std_sta (i :: l) Wstd_sta) !! i = Some (countable.encode Revoked). 
  Proof.
    intros Hp.
    induction l.
    - rewrite /= Hp.
      destruct (countable.encode Temporary =? countable.encode Revoked)%positive; [|done]. apply lookup_insert. 
    - rewrite revoke_list_swap /=.
      destruct (Wstd_sta !! a); auto.
      destruct (countable.encode Temporary =? p)%positive; auto. 
      rewrite Hp.
      destruct (decide (a = i)).
      + subst. apply lookup_insert.
      + rewrite lookup_insert_ne;auto.
        rewrite /= Hp in IHl.
        destruct (countable.encode Temporary =? countable.encode Revoked)%positive; auto. 
  Qed.

  Lemma revoke_list_lookup_middle_Revoked (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∈ l →
    (Wstd_sta !! i = Some (countable.encode Revoked)) →
    (revoke_list_std_sta l Wstd_sta) !! i = Some (countable.encode Revoked). 
  Proof.
    intros Hin Hp.
    apply elem_of_list_split in Hin as [l1 [l2 ->] ].
    rewrite revoke_list_swap_middle.
    by apply revoke_list_lookup_Revoked. 
  Qed.

  Lemma revoke_lookup_Revoked Wstd_sta i :
    (Wstd_sta !! i = Some (countable.encode Revoked)) →
    (revoke_std_sta Wstd_sta) !! i = Some (countable.encode Revoked).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    apply revoke_list_lookup_middle_Revoked; auto.
    apply map_to_list_fst. exists (countable.encode Revoked).
      by apply elem_of_map_to_list.
  Qed. 

  Lemma revoke_list_lookup_Perm (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    (Wstd_sta !! i = Some (countable.encode Permanent)) →
    (revoke_list_std_sta (i :: l) Wstd_sta) !! i = Some (countable.encode Permanent). 
  Proof.
    induction l.
    - intros Hp.
      rewrite /= Hp. 
      destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|done].
      apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr. 
    - intros Hp.
      (* apply not_elem_of_cons in Hin as [Hneq Hin].  *)
      rewrite revoke_list_swap.
      rewrite /=.
      destruct (decide (i = a)).
      + subst. rewrite Hp. 
        destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr.
        * apply Positive_as_DT.eqb_eq,encode_inj in Hcontr. inversion Hcontr.
        * specialize (IHl Hp).
          by rewrite /= Hp Hcontr in IHl. 
      + destruct (Wstd_sta !! a).
        * rewrite Hp. destruct (countable.encode Temporary =? p)%positive.
          ** destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
             apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
             rewrite lookup_insert_ne;auto.
             specialize (IHl Hp). 
               by rewrite /= Hp Hcontr in IHl. 
          ** destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
             apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
             specialize (IHl Hp). 
               by rewrite /= Hp Hcontr in IHl. 
        * rewrite Hp. 
          destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
          apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
          specialize (IHl Hp). 
            by rewrite /= Hp Hcontr in IHl. 
  Qed.

  Lemma revoke_list_lookup_middle_Perm (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∈ l →
    (Wstd_sta !! i = Some (countable.encode Permanent)) →
    (revoke_list_std_sta l Wstd_sta) !! i = Some (countable.encode Permanent). 
  Proof.
    intros Hin Hp.
    apply elem_of_list_split in Hin as [l1 [l2 ->] ].
    rewrite revoke_list_swap_middle.
    by apply revoke_list_lookup_Perm. 
  Qed.

  Lemma revoke_lookup_Perm Wstd_sta i :
    (Wstd_sta !! i = Some (countable.encode Permanent)) →
    (revoke_std_sta Wstd_sta) !! i = Some (countable.encode Permanent).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    apply revoke_list_lookup_middle_Perm; auto.
    apply map_to_list_fst. exists (countable.encode Permanent).
      by apply elem_of_map_to_list.
  Qed. 

  Lemma revoke_list_lookup_None (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∉ l →
    (Wstd_sta !! i = None →
     (revoke_list_std_sta (i :: l) Wstd_sta) !! i = None).
  Proof.
    intros Hin Hnone.
    induction l. 
    - by rewrite /= Hnone. 
    - rewrite revoke_list_swap.
      apply not_elem_of_cons in Hin as [Hneq Hin]. 
      rewrite /= Hnone in IHl.
      rewrite /= Hnone.
      destruct (Wstd_sta !! a); auto.
      destruct (countable.encode Temporary =? p)%positive; auto. 
      rewrite lookup_insert_ne;auto.
  Qed.

  
  Lemma revoke_list_lookup_non_temp (Wstd_sta : STS_states) (l : list positive) (i : positive) (ρ : region_type) :
    i ∈ l →
    (revoke_list_std_sta l Wstd_sta) !! i = Some (countable.encode ρ) → ρ ≠ Temporary.
  Proof.
    intros Hin Hsome Hcontr.
    subst. induction l.
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + subst. simpl in *.
        destruct (Wstd_sta !! a) eqn:Ha.
        * destruct (countable.encode Temporary =? p)%positive eqn:Htemp.
          ** rewrite lookup_insert in Hsome. inversion Hsome as [Hcontr].
             apply encode_inj in Hcontr. done.
          ** destruct (decide (a ∈ l));[apply IHl; auto|]. 
             rewrite revoke_list_nin in Hsome; auto. rewrite Ha in Hsome.
             inversion Hsome as [Hcontr]. subst.
             apply Positive_as_OT.eqb_neq in Htemp. done. 
        * destruct (decide (a ∈ l));[apply IHl; auto|]. 
          rewrite revoke_list_nin in Hsome; auto. congruence.
      + simpl in *.
        destruct (Wstd_sta !! a) eqn:Ha.
        * destruct (countable.encode Temporary =? p)%positive eqn:Htemp.
          ** apply IHl; auto.
             destruct (decide (i = a)); subst.
             { rewrite lookup_insert in Hsome. inversion Hsome as [Hcontr].
               apply encode_inj in Hcontr. done. }
             rewrite lookup_insert_ne in Hsome; auto.
          ** apply IHl; auto. 
        * apply IHl; auto.
  Qed.

  Lemma revoke_std_sta_lookup_non_temp Wstd_sta (i : positive) (ρ : region_type) :
    (revoke_std_sta Wstd_sta) !! i = Some (countable.encode ρ) → ρ ≠ Temporary.
  Proof.
    intros Hin. 
    rewrite revoke_list_dom_std_sta in Hin.
    apply revoke_list_lookup_non_temp with Wstd_sta ((map_to_list Wstd_sta).*1) i; auto.
    rewrite /std_sta /= in Hin.
    assert (is_Some (Wstd_sta !! i)) as [x Hsome].
    { rewrite revoke_list_lookup_Some. eauto. }
    apply map_to_list_fst. exists x. 
    apply elem_of_map_to_list. done. 
  Qed.   

  Lemma revoke_lookup_non_temp W (i : positive) (ρ : region_type) :
    (std_sta (revoke W)) !! i = Some (countable.encode ρ) → ρ ≠ Temporary.
  Proof.
    intros Hin. 
    rewrite revoke_list_dom in Hin.
    apply revoke_list_lookup_non_temp with W.1.1 ((map_to_list W.1.1).*1) i; auto.
    rewrite /std_sta /= in Hin.
    assert (is_Some (W.1.1 !! i)) as [x Hsome].
    { rewrite revoke_list_lookup_Some. eauto. }
    apply map_to_list_fst. exists x. 
    apply elem_of_map_to_list. done. 
  Qed.    

  Lemma revoke_monotone_dom Wstd_sta Wstd_sta' :
    dom (gset positive) Wstd_sta ⊆ dom (gset positive) Wstd_sta' →
    dom (gset positive) (revoke_std_sta Wstd_sta) ⊆ dom (gset positive) (revoke_std_sta Wstd_sta').
  Proof.
    intros Hdom.
    induction Wstd_sta using map_ind.
    - rewrite /revoke_std_sta fmap_empty dom_empty.
      apply empty_subseteq.
    - apply elem_of_subseteq in Hdom. 
      assert (is_Some (Wstd_sta' !! i)) as Hsome. 
      { apply elem_of_gmap_dom;apply Hdom.
        apply elem_of_gmap_dom. rewrite lookup_insert. eauto. } 
      apply elem_of_subseteq. intros j Hj.
      apply elem_of_gmap_dom in Hj; apply elem_of_gmap_dom.
      destruct (decide (i=j));subst. 
      { by apply (revoke_std_sta_lookup_Some Wstd_sta'). }
      { rewrite -revoke_std_sta_lookup_Some.
        apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom. apply Hdom.
        apply elem_of_gmap_dom. rewrite lookup_insert_ne;auto.
        apply (revoke_std_sta_lookup_Some) in Hj. rewrite lookup_insert_ne in Hj;auto.
      }
  Qed.

  Lemma revoke_monotone_lookup Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Wstd_sta' !! i →
    revoke_std_sta Wstd_sta !! i = revoke_std_sta Wstd_sta' !! i.
  Proof.
    intros Heq.
    induction Wstd_sta using map_ind.
    - rewrite lookup_empty in Heq.
      rewrite /revoke_std_sta fmap_empty lookup_empty lookup_fmap.
      destruct (Wstd_sta' !! i) eqn:Hnone; inversion Heq.
      rewrite Hnone. done.
    - destruct (decide (i0 = i)).
      + subst. rewrite lookup_insert in Heq.
        rewrite /revoke_std_sta fmap_insert lookup_fmap lookup_insert -Heq /=.
        done.
      + rewrite lookup_insert_ne in Heq;auto.
        specialize (IHWstd_sta Heq). 
        rewrite /revoke_std_sta fmap_insert lookup_insert_ne;auto.
  Qed. 

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

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT STD TRANSITIONS -------------------------- *)
  
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
  
  Lemma std_rel_priv_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (convert_rel std_rel_priv) x y → rtc (convert_rel (std_rel_priv)) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - inversion Hjk as [ρ Hρ].
      destruct Hρ as [ρ' [Hjρ [Hkρ' Hρρ'] ] ].
      subst. destruct ρ,ρ'; inversion Hρρ'; try discriminate; auto.
      + apply std_rel_priv_rtc_Permanent in Hrtc; auto; subst.
        apply revoke_lookup_Temp in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq. 
        right with (countable.encode Permanent); [|left]. 
        exists Revoked, Permanent. repeat (split;auto). by right.
      + apply std_rel_priv_rtc_Permanent in Hrtc; auto; subst.
        apply revoke_lookup_Temp in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq. 
        right with (countable.encode Permanent); [|left]. 
        exists Revoked, Permanent. repeat (split;auto). by right.
      + assert (∃ (ρ : region_type), h = countable.encode ρ) as [ρ Hρ]. 
        { apply std_rel_exist with (countable.encode Revoked); eauto.
          apply rtc_or_intro_l. auto. }
        apply revoke_lookup_Temp in Hx as Hxtemp.
        rewrite Hxtemp in Hx'. inversion Hx'; simplify_eq.
        destruct ρ.
        * apply revoke_lookup_Temp in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.
        * apply revoke_lookup_Perm in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          right with (countable.encode Permanent); [|left]. 
          exists Revoked, Permanent. repeat (split;auto). by right.
        * apply revoke_lookup_Revoked in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.         
      + apply std_rel_priv_rtc_Permanent in Hrtc; auto; subst.
        apply revoke_lookup_Revoked in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq. 
        right with (countable.encode Permanent); [|left]. 
        exists Revoked, Permanent. repeat (split;auto).
  Qed.

  Lemma std_rel_pub_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (convert_rel std_rel_pub) x y → rtc (convert_rel (std_rel_pub)) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - inversion Hjk as [ρ Hρ].
      destruct Hρ as [ρ' [Hjρ [Hkρ' Hρρ'] ] ].
      subst. destruct ρ,ρ'; inversion Hρρ'; try discriminate; auto.
      apply std_rel_pub_rtc_Temporary in Hrtc; auto. subst. 
      apply revoke_lookup_Revoked in Hx as Hxtemp.
      apply revoke_lookup_Temp in Hy as Hyperm.
      rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
      inversion Hx'; inversion Hy'; simplify_eq. 
      left. 
  Qed.

  Ltac revoke_i W1 W2 i :=
    (match goal with
     | H : W1 !! i = Some (countable.encode _)
           , H' : W2 !! i = Some (countable.encode _) |- _ =>
       let Hxtemp := fresh "Hxtemp" in
       let Hytemp := fresh "Hytemp" in 
      try (apply revoke_lookup_Temp in H as Hxtemp);
      try (apply revoke_lookup_Perm in H as Hxtemp);
      try (apply revoke_lookup_Revoked in H as Hxtemp);
      try (apply revoke_lookup_Temp in H' as Hytemp);
      try (apply revoke_lookup_Perm in H' as Hytemp);
      try (apply revoke_lookup_Revoked in H' as Hytemp);simplify_eq
    end).

  Lemma std_rel_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (λ x0 y0 : positive, convert_rel std_rel_pub x0 y0 ∨ convert_rel std_rel_priv x0 y0) x y →
    rtc (λ x0 y0 : positive, convert_rel std_rel_pub x0 y0 ∨ convert_rel std_rel_priv x0 y0) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc. 
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - destruct Hjk as [Hjk | Hjk]. 
      + inversion Hjk as [ρ Hρ].
        destruct Hρ as [ρ' [Hjρ [Hkρ' Hρρ'] ] ].
        subst. destruct ρ,ρ'; inversion Hρρ'; try discriminate; auto.
        apply std_rel_exist in Hrtc as [ρ Hρ]; eauto. subst.
        destruct ρ; revoke_i Wstd_sta Wstd_sta' i; try left.
        right with (countable.encode Permanent); [|left]. right. 
        exists Revoked, Permanent. repeat (split;auto). by right.
      + inversion Hjk as [ρ Hρ].
        destruct Hρ as [ρ' [Hjρ [Hkρ' Hρρ'] ] ].
        subst. apply std_rel_exist in Hrtc as [ρ'' Hρ'']; eauto. subst.
        destruct ρ,ρ',ρ''; inversion Hρρ'; try discriminate; auto;
          revoke_i Wstd_sta Wstd_sta' i; try left;
        (right with (countable.encode Permanent); [|left]; right; 
          exists Revoked, Permanent; repeat (split;auto); by right).
  Qed.
  
  (* --------------------------------------------------------------------------------- *)
  (* ----------- A REVOKED REGION IS MONOTONE WRT PRIVATE FUTURΕ WORLDS -------------- *)
  
  Lemma revoke_monotone W W' :
    rel_is_std W ->
    related_sts_priv_world W W' → related_sts_priv_world (revoke W) (revoke W').
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
    destruct W' as [ [Wstd_sta' Wstd_rel'] [Wloc_sta' Wloc_rel'] ];
    rewrite /revoke /std_sta /std_rel /=. 
    intros Hstd [(Hdom_sta & Hdom_rel & Htransition) Hrelated_loc]. 
    apply revoke_monotone_dom in Hdom_sta.
    split;[split;[auto|split;[auto|] ]|auto].
    intros i r1 r2 r1' r2' Hr Hr'.
    simpl in *.
    assert ((r1,r2) = (convert_rel std_rel_pub, convert_rel std_rel_priv)) as Heq.
    { apply Some_inj. rewrite -Hr. apply Hstd. eauto. }
    simplify_eq. 
    specialize (Htransition i _ _ r1' r2' Hr Hr') as [<- [<- Htransition] ]. 
    split;[auto|split;[auto|] ]. 
    intros x' y' Hx' Hy'.
    assert (is_Some (Wstd_sta !! i)) as [x Hx]; [apply revoke_std_sta_lookup_Some; eauto|]. 
    assert (is_Some (Wstd_sta' !! i)) as [y Hy]; [apply revoke_std_sta_lookup_Some; eauto|].
    apply std_rel_monotone with x y Wstd_sta Wstd_sta' i; auto. 
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------- REVOKED W IS A PRIVATE FUTURE WORLD TO W ---------------------- *)
  
  Lemma revoke_list_related_sts_priv_cons W l i :
    (is_Some ((std_rel W) !! i) → rel_is_std_i W i) →
    related_sts_priv_world W (revoke_list l W) → related_sts_priv_world W (revoke_list (i :: l) W).
  Proof.
    intros Hstd Hpriv.
    rewrite /revoke_list /=.
    destruct (std_sta W !! i) eqn:Hsome; auto.
    destruct (countable.encode Temporary =? p)%positive eqn:Htemp; auto.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]. 
    destruct Hpriv as [(Hdoms & Hdomr & Ha) Hloc]; auto.
    split;simpl;auto.
    rewrite /related_sts_priv.
    apply Positive_as_OT.eqb_eq in Htemp. 
    simpl in *. 
    split;[|split].
    - etrans;[|apply dom_insert_subseteq];auto.
    - auto.
    - intros j r1 r2 r1' r2' Hr Hr'.
      rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
      intros x y Hx Hy. 
      destruct (decide (i = j)).
      { subst. assert (is_Some (Wstd_rel !! j)) as Hasome; eauto.
        rewrite Hstd in Hr; eauto. inversion Hr. 
        rewrite Hsome in Hx. inversion Hx.
        rewrite lookup_insert in Hy. inversion Hy.
        right with (countable.encode Revoked);[|left].
        right. cbv. exists Temporary, Revoked. 
        split;[auto|split;[auto|] ].
          by left. 
      }
      rewrite lookup_insert_ne in Hy;auto.
      specialize (Ha j r1 r2 r1 r2 Hr Hr) as (_ & _ & Ha). 
      subst. apply Ha; auto.
  Qed. 

  Lemma revoke_list_related_sts_priv W l :
    rel_is_std W →
    related_sts_priv_world W (revoke_list l W).
  Proof.
    induction l.
    - split; apply related_sts_priv_refl.
    - split;[|apply related_sts_priv_refl].
      apply revoke_list_related_sts_priv_cons; auto. 
  Qed.

  Lemma revoke_related_sts_priv W :
    rel_is_std W →
    related_sts_priv_world W (revoke W).
  Proof.
    intros Hstd.
    rewrite revoke_list_dom. apply revoke_list_related_sts_priv.
    done. 
  Qed.
    
  (* If a full private future world of W is standard, then W is standard *)
  Lemma sts_full_world_std W W' :
    (⌜related_sts_priv_world W W'⌝
      -∗ sts_full_world sts_std W'
    → ⌜rel_is_std W⌝)%I. 
  Proof.
    iIntros (Hrelated) "Hfull".
    iDestruct "Hfull" as "[[% [% _] ] _]".
    iPureIntro.
    intros i Hx.
    destruct Hrelated as [ (Hdom_std & Hdom_rel & Htransition) _].
    assert ((∀ x : positive, x ∈ (dom (gset positive) W.1.2) → x ∈ (dom (gset positive) W'.1.2))) as H_std_elem_rel;
      [by apply elem_of_subseteq|].
    assert (i ∈ dom (gset positive) W.1.2) as H_i_rel; [by apply elem_of_dom|].
    specialize (H_std_elem_rel i H_i_rel).
    apply elem_of_dom in H_std_elem_rel as [ [r1' r2'] Hr'].
    apply elem_of_dom in H_i_rel as [ [r1 r2] Hr].
    specialize (Htransition i r1 r2 r1' r2' Hr Hr') as (Heq1 & Heq2 & _).
    assert (is_Some (W'.1.2 !! i)) as Hsome'; eauto.    
    rewrite H4 in Hr'; auto.
    by inversion Hr'; subst. 
  Qed.

  (* Helper lemmas for reasoning about a revoked domain *)

  Lemma dom_equal_empty_inv_r Wstd_sta :
    dom_equal Wstd_sta ∅ → Wstd_sta = ∅.
  Proof.
    intros Hdom. 
    apply map_empty.
    intros i.
    destruct Hdom with i as [Hdom1 Hdom2]. 
    apply eq_None_not_Some.
    intros Hsome. specialize (Hdom1 Hsome) as [a [_ [x Hcontr] ] ].
    inversion Hcontr.
  Qed.

  Lemma dom_equal_empty_inv_l M :
    dom_equal ∅ M → M = ∅.
  Proof.
    intros Hdom. 
    apply map_empty.
    intros i.
    destruct Hdom with (countable.encode i) as [Hdom1 Hdom2]. 
    apply eq_None_not_Some.
    intros Hsome.
    assert (∃ a : Addr, countable.encode a = countable.encode i ∧ is_Some (M !! a)) as Ha; eauto.
    specialize (Hdom2 Ha) as [x Hcontr].
    inversion Hcontr.
  Qed.

  Lemma dom_equal_revoke_list W M l : 
    dom_equal (std_sta W) M →
    dom_equal (std_sta (revoke_list l W)) M.
  Proof.
    intros Hdom.
    induction l.
    - done.
    - rewrite /revoke_list /=.
      destruct (std_sta W !! a) eqn:Hsome; auto.
      destruct Hdom with a as [Hdom1 Hdom2].
      destruct (countable.encode Temporary =? p)%positive eqn:Htemp;auto.
      rewrite /std_sta /=. 
      split.
      + intros [x Hi].
        destruct (decide (a = i));subst; eauto.
        rewrite lookup_insert_ne in Hi;auto. 
        destruct IHl with i as [Hdomi1 Hdomi2].
        apply Hdomi1. eauto.
      + intros [a' [Heq [x Hx] ] ]; simplify_eq.
        destruct (decide (a = (countable.encode a')));subst; eauto.
        * rewrite lookup_insert;eauto.
        * rewrite lookup_insert_ne;auto.
          apply IHl. eauto.
  Qed.

  Lemma dom_equal_revoke_list' W M l : 
    dom_equal (std_sta (revoke_list l W)) M →
    dom_equal (std_sta W) M.
  Proof.
    intros Hdom.
    induction l.
    - done.
    - rewrite /revoke_list /= in Hdom.
      destruct (std_sta W !! a) eqn:Hsome; auto.
      destruct Hdom with a as [Hdom1 Hdom2].
      destruct (countable.encode Temporary =? p)%positive eqn:Htemp;auto.
      rewrite /std_sta /=. 
      split.
      + intros [x Hi].
        destruct (decide (a = i));subst.
        * apply Hdom1. rewrite /revoke_list /std_sta /= lookup_insert.
          eauto. 
        * rewrite /revoke_list /std_sta /= in Hdom. 
          destruct Hdom with i as [Hdomi1 _].
          apply Hdomi1. rewrite lookup_insert_ne; auto.
          apply revoke_list_lookup_Some. eauto. 
      + intros [a' [Heq [x Hx] ] ]; simplify_eq.
        rewrite /revoke_list /std_sta /= in Hdom.
        destruct Hdom with (countable.encode a') as [Hdom1i Hdom2i]. 
        destruct (decide (a = (countable.encode a')));subst; eauto.
        rewrite lookup_insert_ne in Hdom2i; auto.
        rewrite revoke_list_lookup_Some. apply Hdom2i.
        exists a'. split; eauto.
  Qed.

  Lemma dom_equal_revoke W M :
    dom_equal (std_sta W) M <->
    dom_equal (std_sta (revoke W)) M.
  Proof.
    rewrite revoke_list_dom. split; [apply dom_equal_revoke_list|apply dom_equal_revoke_list'].
  Qed. 

  Lemma related_sts_priv_weaken fs fr gs gr i x :
    i ∉ dom (gset positive) fs →
    related_sts_priv fs (<[i:=x]> gs) fr gr →
    related_sts_priv fs gs fr gr.
  Proof.
    intros Hnin [Hdom_std [Hdom_loc Hrelated] ].
    split;[|split;auto].
    - rewrite dom_insert_L in Hdom_std.
      apply elem_of_subseteq.
      apply elem_of_subseteq in Hdom_std.
      intros x' Hx'. specialize (Hdom_std x' Hx').
      destruct (decide (x' = i)); [subst;contradiction|].
      apply elem_of_union in Hdom_std as [Hcontr | Hgs]; auto.
      apply elem_of_singleton_1 in Hcontr. contradiction. 
    - intros i' r1 r2 r1' r2' Hr Hr'.
      edestruct Hrelated as (Heq & Heq' & Hstate); eauto; subst.
      repeat (split;auto).
      intros x' y Hx' Hy.
      destruct (decide (i = i')); subst.
      + exfalso. apply Hnin. apply elem_of_gmap_dom. 
        eauto.
      + apply Hstate; auto.
        rewrite lookup_insert_ne;auto. 
  Qed.

  (* Helper lemma for reasoning about the current state of a region map *)
  Lemma big_sepM_exists {A B C : Type} `{EqDecision A, Countable A} (m : gmap A B) (φ : A → C -> B → iProp Σ) :
    (([∗ map] a↦b ∈ m, ∃ c, φ a c b) ∗-∗ (∃ (m' : gmap A C), [∗ map] a↦c;b ∈ m';m, φ a c b))%I.
  Proof.
    iSplit. 
    - iIntros "Hmap".
      iInduction (m) as [| a x m Hnone] "IH" using map_ind.
      + iExists empty. done.
      + iDestruct (big_sepM_insert with "Hmap") as "[Hc Hmap]"; auto.
        iDestruct "Hc" as (c) "Hc".
        iDestruct ("IH" with "Hmap") as (m') "Hmap".
        iExists (<[a:=c]> m').
        iApply (big_sepM2_insert_2 with "Hc").
        iFrame.
    - iIntros "Hmap".
      iDestruct "Hmap" as (m') "Hmap". 
      iInduction (m) as [| a x m Hnone] "IH" using map_ind forall (m').
      + done.
      + iDestruct (big_sepM2_dom with "Hmap") as %Hdom. 
        assert (is_Some (m' !! a)) as [ρ Hρ].
        { apply elem_of_gmap_dom. rewrite Hdom dom_insert_L.
          apply elem_of_union_l, elem_of_singleton; auto. }    
        rewrite -(insert_id m' a ρ); auto.
        rewrite -insert_delete. 
        iDestruct (big_sepM2_insert with "Hmap") as "[Hφ Hmap]";[apply lookup_delete|auto|].
        iApply big_sepM_insert;auto.
        iDestruct ("IH" with "Hmap") as "Hmap". iFrame.
        iExists ρ. iFrame. 
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- IF THΕ FULL STS IS REVOKED, WΕ CAN REVOKE REGION ------------------- *)

  Lemma monotone_revoke_region_def M W :
    ⌜dom_equal (std_sta W) M⌝ -∗ ⌜rel_is_std W⌝ -∗
     sts_full_world sts_std (revoke W) -∗ region_map_def M W -∗
     sts_full_world sts_std (revoke W) ∗ region_map_def M (revoke W).
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc].
    iIntros (Hdom Hstd) "Hfull Hr".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Htemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[_ Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      eapply revoke_lookup_non_temp; eauto. 
    }
    iFrame.
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iApply (big_sepM2_mono with "Hr"). 
    iIntros (a ρ γp Hm' HM) "/= Ha". 
    specialize (Htemp a ρ Hm').
    destruct ρ;[contradiction| |done]. 
    iDestruct "Ha" as (γpred v p φ) "(Hγp & Hne & Ha & #Hmono & Hpred & Hφ)".
    iExists _,_,_,_. iFrame "∗ #".
    iNext. iApply ("Hmono" with "[] Hφ"). 
    iPureIntro. apply revoke_related_sts_priv. auto.
    Unshelve. apply _. 
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- A REVOKED W IS MONOTONE WRT PRIVATE FUTURE WORLD ------------------- *)
  
  Lemma monotone_revoke_list_region_def_mono M W W' :
    ⌜related_sts_priv_world W W'⌝ -∗ ⌜dom_equal (std_sta W') M⌝ -∗
     sts_full_world sts_std (revoke W) -∗ region_map_def M (revoke W) -∗
     sts_full_world sts_std (revoke W) ∗ region_map_def M (revoke W').
  Proof.
    iIntros (Hrelated Hdom) "Hfull Hr".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Htemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[_ Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro. eapply revoke_lookup_non_temp; eauto. 
    }
    iDestruct (sts_full_world_std (revoke W) with "[] [$Hfull]") as %Hstd.
    { iPureIntro. split;apply related_sts_priv_refl. }
    iFrame. 
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame. 
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hsomeρ Hsomeγp) "Ha /=".
    specialize (Htemp a ρ Hsomeρ). 
    destruct ρ;[contradiction| |done].
    iDestruct "Ha" as (γpred v p φ) "(Heq & HpO & Ha & #Hmono & Hpred & Hφ)". 
    iExists _,_,_,_; iFrame "∗ #".
    iNext. iApply "Hmono";[|iFrame].
    iPureIntro. apply revoke_monotone; auto.
    Unshelve. apply _. 
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ---------------- IF WΕ HAVE THE REGION, THEN WE CAN REVOKE THE FULL STS ---------------- *)

  (* This matches the temprary resources in the map *)
  Definition temp_resources (W : WORLD) φ (a : Addr) (p : Perm) : iProp Σ :=
    (∃ (v : Word),
           ⌜p ≠ O⌝
          ∗ a ↦ₐ[p] v
          ∗ (if pwl p
             then future_pub_mono φ v
             else future_priv_mono φ v)
          ∗ φ (W,v))%I. 
  
  Lemma monotone_revoke_list_sts_full_world_keep W (l : list positive) (l' : list Addr) p φ :
    (⌜NoDup l'⌝ → ⌜NoDup l⌝ → ⌜countable.encode <$> l' ⊆+ l⌝ →
    ([∗ list] a ∈ l', ⌜(std_sta W) !! (countable.encode a) = Some (countable.encode Temporary)⌝ ∧ rel a p φ)
    ∗ sts_full_world sts_std W ∗ region W
    ==∗ (sts_full_world sts_std (revoke_list l W) ∗ region W
                        ∗ [∗ list] a ∈ l', ▷ temp_resources W φ a p ∗ rel a p φ))%I.
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]. 
    rewrite /std_sta region_eq /region_def /=.
    iInduction (l) as [|x l] "IH" forall (l'); 
    iIntros (Hdup' Hdup Hsub) "(#Hrel & Hfull & Hr)".
    - iFrame. apply submseteq_nil_r,fmap_nil_inv in Hsub as ->. repeat rewrite big_sepL_nil. done. 
    - destruct (decide (x ∈ (countable.encode <$> l'))). 
      + apply elem_of_list_split in e as [l1 [l2 Heq] ].
        rewrite Heq in Hsub.
        iRevert (Hsub Hdup Hdup'). rewrite -(NoDup_fmap countable.encode l') Heq -Permutation_middle. iIntros (Hsub Hdup Hdup').
        apply NoDup_cons in Hdup as [Hnin Hdup]. 
        apply NoDup_cons in Hdup' as [Hnin' Hdup'].
        assert (∃ a : Addr, x = countable.encode a ∧ a ∈ l') as [a [Hxa Ha] ].
        { apply elem_of_list_fmap_2. rewrite Heq. apply elem_of_app. right. apply elem_of_list_here. }
        apply elem_of_Permutation in Ha as [l'' Hleq]. rewrite Hleq /=. 
        iDestruct "Hrel" as "[ [Htemp Hx] Hrel]".
        iDestruct "Htemp" as %Htemp. 
        iMod ("IH" with "[] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        { iPureIntro. apply submseteq_cons_l in Hsub as [k' [Hperm Hsub] ].
          apply Permutation.Permutation_cons_inv in Hperm.
          apply NoDup_cons_12 with a. rewrite -Hleq. apply NoDup_fmap_1 with countable.encode.
          rewrite Heq -Permutation_middle. apply NoDup_cons; auto. }
        { iPureIntro. apply fmap_Permutation with countable.encode in Hleq.
          revert Hleq. rewrite Heq -Permutation_middle fmap_cons Hxa. intros Hleq.
          apply Permutation.Permutation_cons_inv in Hleq. rewrite -Hleq.
          apply submseteq_cons_l in Hsub as [k' [Hperm Hsub] ].
          apply Permutation.Permutation_cons_inv in Hperm.
          rewrite Hperm. done. }
        rewrite /revoke_list /= /std_sta /=.
        rewrite Hxa Htemp Positive_as_OT.eqb_refl.
        rewrite rel_eq /rel_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. 
        iDestruct "Hx" as (γpred) "#(Hγpred & Hφ)".
        iDestruct "Hr" as (M) "(HM & % & Hpreds)". 
        (* assert that γrel = γrel' *)
        iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq.
        rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
        iDestruct "Hpreds" as "[Ha Hpreds]".
        iDestruct "Ha" as (ρ) "[Hstate Ha]". 
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        simpl in Hlookup. 
        simpl in Hlookup. subst. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
        rewrite Htemp in Hlookup. inversion Hlookup; simplify_eq.
        iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iFrame "∗ #". iClear "IH". 
        iDestruct (big_sepM_insert _ _ a (γpred, p) with "[$Hpreds Hstate]") as "Hpreds"; [apply lookup_delete|..].
        iExists Revoked. iFrame. rewrite -HMeq.
        iModIntro. iSplitL "Hpreds HM".
        ++ iExists M. iFrame. auto. 
        ++ iSplitL.
           +++ iDestruct "Ha" as (γpred0 v p0 φ0 Heq0 Hp0) "(Hx & Hmono & #Hsaved & Hφ0)"; simplify_eq.
               iExists v.
               iDestruct (saved_pred_agree _ _ _ (Wstd_sta, Wstd_rel, Wloc, v) with "Hφ Hsaved") as "#Hφeq". iFrame.
               iSplitR; auto.
               iDestruct (internal_eq_iff with "Hφeq") as "Hφeq'". 
               iSplitL "Hmono";[|by iNext; iApply "Hφeq'"].
               destruct (pwl p0).
               { iDestruct "Hmono" as "#Hmono".
                 iApply later_intuitionistically_2. iAlways.
                 repeat (iApply later_forall_2; iIntros (W W')).
                 iDestruct (saved_pred_agree _ _ _ (W', v) with "Hφ Hsaved") as "#HφWeq'".
                 iDestruct (internal_eq_iff with "HφWeq'") as "HφWeq''".
                 iDestruct (saved_pred_agree _ _ _ (W, v) with "Hφ Hsaved") as "#HφWeq".
                 iDestruct (internal_eq_iff with "HφWeq") as "HφWeq'''". 
                 iAlways. iIntros (Hrelated) "HφW". iApply "HφWeq''". iApply "Hmono"; eauto.
                 iApply "HφWeq'''"; auto. }
               { iDestruct "Hmono" as "#Hmono".
                 iApply later_intuitionistically_2. iAlways.
                 repeat (iApply later_forall_2; iIntros (W W')).
                 iDestruct (saved_pred_agree _ _ _ (W', v) with "Hφ Hsaved") as "#HφWeq'".
                 iDestruct (internal_eq_iff with "HφWeq'") as "HφWeq''".
                 iDestruct (saved_pred_agree _ _ _ (W, v) with "Hφ Hsaved") as "#HφWeq".
                 iDestruct (internal_eq_iff with "HφWeq") as "HφWeq'''". 
                 iAlways. iIntros (Hrelated) "HφW". iApply "HφWeq''". iApply "Hmono"; eauto.
                 iApply "HφWeq'''"; auto. }
           +++ iExists γpred. iFrame "#".
      + apply NoDup_cons in Hdup as [Hnin Hdup].
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hcontr _] ] ].
        2: { exfalso. apply n. rewrite Hcontr. apply elem_of_list_here. }
        iMod ("IH" with "[] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        iDestruct "Hr" as (M) "(HM & #Hdom & Hr)". iDestruct "Hdom" as %Hdom. iClear "IH". 
        rewrite /revoke_list /std_sta /=.
        destruct (Wstd_sta !! x) eqn:Hsome.
        2: { iFrame. iModIntro. iExists M. iFrame. auto. }
        destruct (countable.encode Temporary =? p0)%positive eqn:Htemp.
        2: { iFrame. iModIntro. iExists M. iFrame. auto. }
        assert (∃ a:Addr, countable.encode a = x ∧ is_Some (M !! a)) as [a [Heqa [γp Hsomea] ] ].
        { destruct Hdom with (countable.encode x) as [ [a [Heq Ha] ] _]; eauto. }
        iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hx Hr]"; eauto.
        iDestruct "Hx" as (ρ) "[Hstate Hρ]".
        iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]". rewrite Heqa. iFrame. 
        iDestruct (big_sepM_delete _ _ a with "[Hstate $Hr Hρ]") as "Hr"; eauto.
        iExists Revoked; rewrite Heqa; iFrame.
        iModIntro. iFrame. iExists M. iFrame. auto. 
  Qed.
            
  Lemma monotone_revoke_sts_full_world_keep W (l : list Addr) p φ :
    ⌜NoDup l⌝ -∗
    ([∗ list] a ∈ l, ⌜(std_sta W) !! (countable.encode a) = Some (countable.encode Temporary)⌝ ∧ rel a p φ)
    ∗ sts_full_world sts_std W ∗ region W
    ==∗ (sts_full_world sts_std (revoke W) ∗ region W ∗
                        ([∗ list] a ∈ l, ▷ temp_resources W φ a p ∗ rel a p φ)).
  Proof.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert (⌜countable.encode <$> l ⊆+ (map_to_list W.1.1).*1⌝)%I as %Hsub.
    { iClear "Hfull Hr". iInduction l as [| x l] "IH".
      - rewrite fmap_nil. iPureIntro. apply submseteq_nil_l.
      - rewrite fmap_cons /=. iDestruct "Hl" as "[ [Hin _] Hl]".
        iDestruct "Hin" as %Hin. apply NoDup_cons in Hdup as [Hnin Hdup].
        iDestruct ("IH" with "[] Hl") as %Hsub; auto. 
        iPureIntro.
        assert (countable.encode x ∈ (map_to_list W.1.1).*1) as Helem.
        { apply map_to_list_fst. exists (countable.encode Temporary). by apply elem_of_map_to_list. }
        apply elem_of_Permutation in Helem as [l' Hl']. rewrite Hl'.
        apply submseteq_skip. revert Hsub. rewrite Hl'; intros Hsub.
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto. 
        assert (countable.encode x ∈ countable.encode <$> l) as Hcontr. 
        { rewrite Heq. apply elem_of_list_here. }
        apply elem_of_list_fmap_2 in Hcontr as [y [Hxy Hy] ]. 
        apply encode_inj in Hxy. subst. contradiction. 
    }
    iMod (monotone_revoke_list_sts_full_world_keep _ (map_to_list W.1.1).*1 l 
            with "[] [] [] [$Hl $Hfull $Hr]") as "(Hfull & Hr & Hi)"; auto. 
    { iPureIntro. apply NoDup_fst_map_to_list. }
    iFrame. done. 
  Qed.

  
  (* The following statement discards all the resources of temporary regions *)
  Lemma monotone_revoke_list_sts_full_world M W l :
    ⌜∀ (i : positive), i ∈ l → ∃ (a : Addr), countable.encode a = i ∧ is_Some (M !! a)⌝ -∗
    ⌜NoDup l⌝ -∗
    sts_full_world sts_std W ∗ region_map_def M W
    ==∗ (sts_full_world sts_std (revoke_list l W) ∗ region_map_def M W).
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]. 
    rewrite /std_sta /=. 
    iIntros (Hin Hdup) "[Hfull Hr]".
    iInduction (l) as [|x l] "IH". 
    - iFrame. done. 
    - apply NoDup_cons in Hdup as [Hnin Hdup]. 
      iMod ("IH" with "[] [] Hfull Hr") as "[Hfull Hr]"; auto.
      { iPureIntro. intros a Ha. apply Hin. apply elem_of_cons. by right. }
      rewrite /revoke_list /= /std_sta /=. 
      destruct (Wstd_sta !! x) eqn:Hsome;[|by iFrame]. 
      destruct (countable.encode Temporary =? p)%positive eqn:Htemp;[|by iFrame]. 
      destruct Hin with x as [a [Heq [γp Hsomea] ] ];[apply elem_of_list_here|].
      iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hρ Hr]"; eauto.
      iDestruct "Hρ" as (ρ') "(Hstate & Ha)".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup. 
      simpl in Hlookup. subst. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
      apply base.positive_beq_true in Htemp. 
      rewrite Hsome -Htemp in Hlookup. inversion Hlookup; simplify_eq.
      iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
      iFrame.
      iDestruct (big_sepM_delete _ _ a with "[$Hr Hstate]") as "$"; eauto.
      iExists Revoked. iFrame.
  Qed.

  (* The following statement discards all the resources of temporary regions *)
  Lemma monotone_revoke_sts_full_world W :
    sts_full_world sts_std W ∗ region W
    ==∗ (sts_full_world sts_std (revoke W) ∗ region W).
  Proof.
    iIntros "[Hfull Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M) "(HM & #Hdom & Hr)".
    iDestruct "Hdom" as %Hdom. 
    rewrite revoke_list_dom.
    iMod (monotone_revoke_list_sts_full_world _ _ (map_to_list W.1.1).*1
            with "[] [] [$Hfull $Hr]") as "[Hfull Hr]".
    { iPureIntro. intros i Hin. apply map_to_list_fst in Hin as [x Hin].
      destruct Hdom with i as [Hdom1 _].
      apply Hdom1. exists x. by apply elem_of_map_to_list. 
    }
    { iPureIntro. apply NoDup_fst_map_to_list. }
    iFrame.
    iModIntro. iExists M. iFrame. done. 
  Qed.


  Lemma submseteq_dom (l : list positive) (Wstd_sta : STS_states) :
    Forall (λ i : positive, Wstd_sta !! i = Some (countable.encode Temporary)) l
    → NoDup l → l ⊆+ (map_to_list Wstd_sta).*1.
  Proof.
    generalize l. 
    induction Wstd_sta using map_ind.
    + intros l' Htemps Hdup. destruct l'; auto. inversion Htemps. subst. discriminate. 
    + intros l' Htemps Hdup. rewrite map_to_list_insert; auto.
      cbn.
      (* destruct on i being an element of l'! *)
      destruct (decide (i ∈ l')).
      ++ apply elem_of_list_split in e as [l1 [l2 Heq] ].
         rewrite Heq -Permutation_middle.
         apply submseteq_skip. 
         rewrite Heq in Hdup.
         apply NoDup_app in Hdup as [Hdup1 [Hdisj Hdup2] ]. 
         apply NoDup_cons in Hdup2 as [Helem2 Hdup2].
         assert (i ∉ l1) as Helem1.
         { intros Hin. specialize (Hdisj i Hin). apply not_elem_of_cons in Hdisj as [Hcontr _]. done. }
         apply IHWstd_sta.
         +++ revert Htemps. repeat rewrite Forall_forall. intros Htemps.
             intros j Hin.
             assert (j ≠ i) as Hne.
             { intros Hcontr; subst. apply elem_of_app in Hin as [Hcontr | Hcontr]; congruence. }
             rewrite -(Htemps j);[rewrite lookup_insert_ne;auto|].
             subst. apply elem_of_app. apply elem_of_app in Hin as [Hin | Hin]; [left;auto|right].
             apply elem_of_cons;by right. 
         +++ apply NoDup_app; repeat (split;auto).
             intros j Hj. specialize (Hdisj j Hj). apply not_elem_of_cons in Hdisj as [_ Hl2];auto.
      ++ apply submseteq_cons. apply IHWstd_sta; auto.
         revert Htemps. repeat rewrite Forall_forall. intros Htemps j Hin.
         specialize (Htemps j Hin).
         assert (i ≠ j) as Hneq; [intros Hcontr; subst; congruence|].
         rewrite lookup_insert_ne in Htemps;auto. 
  Qed. 


  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------ WE CAN REVOKΕ A REGION AND STS COLLECTION PAIR ---------------------- *)
  (* ---------------------------------------------------------------------------------------- *)
  
  Lemma monotone_revoke W :
    sts_full_world sts_std W ∗ region W ==∗ sts_full_world sts_std (revoke W) ∗ region (revoke W).
  Proof.
    iIntros "[HW Hr]".
    iDestruct (sts_full_world_std W W with "[] HW") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|]. 
    iMod (monotone_revoke_sts_full_world with "[$HW $Hr]") as "[HW Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M) "(HM & % & Hpreds)". 
    iDestruct (monotone_revoke_region_def with "[] [] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iExists _. iFrame.
    iPureIntro. by apply (dom_equal_revoke W M).
  Qed.

  Lemma monotone_revoke_keep W l p φ :
    NoDup l ->
    ([∗ list] a ∈ l, ⌜(std_sta W) !! (countable.encode a) = Some (countable.encode Temporary)⌝ ∧ rel a p φ)
      ∗ sts_full_world sts_std W ∗ region W ==∗ sts_full_world sts_std (revoke W) ∗ region (revoke W)
      ∗ [∗ list] a ∈ l, (▷ temp_resources W φ a p ∗ rel a p φ)
                     ∗ ⌜(std_sta (revoke W)) !! (countable.encode a) = Some (countable.encode Revoked)⌝.
  Proof.
    iIntros (Hdup) "(Hl & HW & Hr)".
    iDestruct (sts_full_world_std W W with "[] HW") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|].
    iAssert (⌜Forall (λ a, std_sta W !! countable.encode a = Some (countable.encode Temporary)) l⌝)%I as %Htemps.
    { iDestruct (big_sepL_and with "Hl") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iMod (monotone_revoke_sts_full_world_keep with "[] [$HW $Hr $Hl]") as "(HW & Hr & Hl)"; eauto.
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M) "(HM & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iSplitL "HW HM".
    - iExists _. iFrame. iPureIntro. by apply (dom_equal_revoke W M).
    - iApply big_sepL_sep. iFrame. iApply big_sepL_forall. iPureIntro.
      revert Htemps. rewrite (Forall_lookup _ l). intros Hl i a Ha; auto.
      specialize (Hl i a Ha). rewrite /revoke. apply revoke_lookup_Temp. done. 
  Qed.

  
  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------ WE CAN UPDATE A REVOKED WORLD BACK TO TEMPORARY  -------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* closing will take every revoked element of l and reinstate it as temporary *)
  Fixpoint close_list_std_sta (l : list positive) (fs : STS_states) : STS_states :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => if ((countable.encode Revoked) =? j)%positive
                          then <[i := countable.encode Temporary]> (close_list_std_sta l' fs)
                          else (close_list_std_sta l' fs)
               | None => (close_list_std_sta l' fs)
               end
    end.
  Definition close_list l W : WORLD := ((close_list_std_sta l (std_sta W),std_rel W), loc W).

  Lemma close_list_std_sta_is_Some Wstd_sta l i :
    is_Some (Wstd_sta !! i) <-> is_Some (close_list_std_sta l Wstd_sta !! i).
  Proof.
    split.
    - induction l.
      + done.
      + intros [x Hx]. 
      simpl.
      destruct (Wstd_sta !! a);[|apply IHl;eauto].
      destruct (countable.encode Revoked =? p)%positive;[|apply IHl;eauto].
      destruct (decide (a = i)).
        * subst. rewrite lookup_insert. eauto.
        * rewrite lookup_insert_ne;eauto. 
    - induction l.
      + done.
      + intros [x Hx].
        simpl in Hx.
        destruct (Wstd_sta !! a) eqn:Hsome;eauto. 
        destruct (countable.encode Revoked =? p)%positive;[|apply IHl;eauto].
        destruct (decide (a = i)).
        * subst. eauto. 
        * rewrite lookup_insert_ne in Hx;eauto. 
  Qed.

  Lemma close_list_std_sta_None Wstd_sta l i :
    Wstd_sta !! i = None <-> close_list_std_sta l Wstd_sta !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply close_list_std_sta_is_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. revert Hcontr. rewrite close_list_std_sta_is_Some =>Hcontr.
      apply eq_None_not_Some in Hcontr; eauto.
  Qed. 

  Lemma close_list_std_sta_same Wstd_sta l i :
    i ∉ l → Wstd_sta !! i = close_list_std_sta l Wstd_sta !! i.
  Proof.
    intros Hnin. induction l.
    - done.
    - simpl. apply not_elem_of_cons in Hnin as [Hne Hnin]. 
      destruct (Wstd_sta !! a); auto.
      destruct (countable.encode Revoked =? p)%positive; auto.
      rewrite lookup_insert_ne; auto.
  Qed.

  Lemma close_list_std_sta_revoked Wstd_sta l i :
    i ∈ l -> Wstd_sta !! i = Some (countable.encode Revoked) →
    close_list_std_sta l Wstd_sta !! i = Some (countable.encode Temporary).
  Proof.
    intros Hin Hrev. induction l.
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + subst. simpl. rewrite Hrev.
        destruct (countable.encode Revoked =? countable.encode Revoked)%positive eqn:Hcontr. 
        * rewrite lookup_insert; auto.
        * apply Positive_as_DT.eqb_neq in Hcontr. 
          contradiction.
      + simpl. destruct (Wstd_sta !! a); auto.
        destruct (countable.encode Revoked =? p)%positive; auto.
        destruct (decide (i = a)); subst.
        * rewrite lookup_insert; auto.
        * rewrite lookup_insert_ne;auto.
  Qed.
          
  Lemma close_list_related_sts_pub_cons W a l :
    rel_is_std W →
    related_sts_pub_world (revoke W) (close_list l (revoke W)) →
    related_sts_pub_world (revoke W) (close_list_std_sta (a :: l) (std_sta (revoke W)), std_rel (revoke W), loc (revoke W)).
  Proof.
    rewrite /close_list /=. intros Hstd IHl.
    destruct (std_sta (revoke W) !! a) eqn:Hsome; auto.
    destruct (countable.encode Revoked =? p)%positive eqn:Hrev;auto.
    apply related_sts_pub_trans_world with (close_list l (revoke W)); auto.
    split;[|apply related_sts_pub_refl].
    split;[|split].
    + rewrite dom_insert /close_list /=.
      apply union_subseteq_r.
    + by rewrite /close_list /=.
    + rewrite /close_list /=. intros i r1 r2 r1' r2' Hr Hr'.
      rewrite Hr in Hr'. inversion Hr'.
      repeat (split;auto).
      intros x y Hx Hy.
      destruct (decide (i = a)); subst.
      ++ rewrite lookup_insert in Hy. inversion Hy.
         apply Positive_as_DT.eqb_eq in Hrev. subst.
         destruct (decide (a ∈ l)).
         +++ apply close_list_std_sta_revoked with _ l _ in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. left.
         +++ rewrite (close_list_std_sta_same _ l) in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. right with (countable.encode Temporary);[|left].
             assert (is_Some (std_rel W !! a)) as Hstda; eauto.
             specialize (Hstd a Hstda). rewrite Hstd in Hr. inversion Hr.
             exists Revoked,Temporary. repeat (split;auto).
      ++ rewrite lookup_insert_ne in Hy; auto.
         rewrite Hx in Hy. inversion Hy. left.
  Qed. 
         
  Lemma close_list_related_sts_pub W l :
    rel_is_std W → 
    related_sts_pub_world (revoke W) (close_list l (revoke W)).
  Proof.
    intros Hstd.
    induction l.
    - rewrite /close_list /=. split; apply related_sts_pub_refl.
    - apply close_list_related_sts_pub_cons; auto. 
  Qed.

  Lemma close_list_related_sts_pub_insert' Wstd_sta Wstd_rel Wloc i l :
    rel_is_std (Wstd_sta,Wstd_rel,Wloc) → 
    i ∉ l → revoke_std_sta (std_sta (Wstd_sta, Wstd_rel, Wloc)) !! i = Some (countable.encode Revoked) ->
    related_sts_pub_world
      (close_list_std_sta l (revoke_std_sta (std_sta (Wstd_sta, Wstd_rel, Wloc))), std_rel (Wstd_sta, Wstd_rel, Wloc), Wloc)
      (<[i:=countable.encode Temporary]> (close_list_std_sta l (revoke_std_sta (std_sta (Wstd_sta, Wstd_rel, Wloc)))),
       std_rel (Wstd_sta, Wstd_rel, Wloc), Wloc).
  Proof.
    intros Hstd Hnin Hlookup.
    split;[|apply related_sts_pub_refl]; simpl.
    split;[|split]; auto.
    + apply elem_of_subseteq. intros j Hj.
      rewrite dom_insert_L. apply elem_of_union. right.
      apply elem_of_dom. apply elem_of_dom in Hj. done. 
    + intros j r1 r2 r1' r2' Hr Hr'.
      assert (is_Some (Wstd_rel !! j)) as Hsome; eauto.
      rewrite Hstd in Hr; auto. rewrite Hstd in Hr'; auto. inversion Hr; inversion Hr'; subst.
      repeat (split;auto). intros x y Hx Hy.
      destruct (decide (i = j)); subst.
      * rewrite lookup_insert in Hy. rewrite -(close_list_std_sta_same _ l) in Hx; auto. 
        rewrite Hlookup in Hx. inversion Hx; inversion Hy; subst.
        right with (countable.encode Temporary);[|left].
        exists Revoked, Temporary. repeat (split;auto).
      * rewrite lookup_insert_ne in Hy; auto. rewrite Hx in Hy. inversion Hy. left.
  Qed.

  Lemma close_list_related_sts_pub_insert Wstd_sta Wstd_rel Wloc i l :
    rel_is_std (Wstd_sta,Wstd_rel,Wloc) → 
    i ∉ l → revoke_std_sta (std_sta (Wstd_sta, Wstd_rel, Wloc)) !! i = Some (countable.encode Revoked) ->
    related_sts_pub_world
      (revoke_std_sta Wstd_sta, Wstd_rel, Wloc)
      (<[i:=countable.encode Temporary]> (close_list_std_sta l (revoke_std_sta (std_sta (Wstd_sta, Wstd_rel, Wloc)))),
       std_rel (Wstd_sta, Wstd_rel, Wloc), Wloc).
  Proof.
    intros Hstd Hnin Hlookup.
    apply related_sts_pub_trans_world with (close_list_std_sta l (revoke_std_sta (std_sta (Wstd_sta, Wstd_rel, Wloc))),
                                            std_rel (Wstd_sta, Wstd_rel, Wloc), Wloc).
    - apply close_list_related_sts_pub with _ l in Hstd. apply Hstd.
    - apply close_list_related_sts_pub_insert'; auto. 
  Qed.

  Lemma monotone_revoked_close_sub W l p φ :
    ([∗ list] a ∈ l, temp_resources (revoke W) φ a p ∗ rel a p φ
                                    ∗ ⌜(std_sta (revoke W)) !! (countable.encode a) = Some (countable.encode Revoked)⌝)
    ∗ sts_full_world sts_std (revoke W) ∗ region (revoke W) ==∗
    sts_full_world sts_std (close_list (countable.encode <$> l) (revoke W))
    ∗ region (close_list (countable.encode <$> l) (revoke W)).
  Proof.
    iIntros "(Hl & Hfull & Hr)".
    iAssert (⌜NoDup l⌝)%I as %Hdup.
    { iClear "Hfull Hr".
      iInduction (l) as [|x l] "IH".
      - iPureIntro. by apply NoDup_nil.
      - iDestruct "Hl" as "[Ha Hl]". 
        iDestruct ("IH" with "Hl") as %Hdup.
        iAssert (⌜x ∉ l⌝)%I as %Hnin.
        { iIntros (Hcontr). iDestruct (big_sepL_elem_of _ _ x with "Hl") as "[Ha' Hcontr]"; auto.
          rewrite /temp_resources /=.
          iDestruct "Ha" as "(Ha & _)".
          iDestruct "Ha" as (v) "(% & Ha & _)".
          iDestruct "Ha'" as (v') "(% & Ha' & _)".
          iApply (cap_duplicate_false with "[$Ha $Ha']"); auto. 
        } iPureIntro. apply NoDup_cons. split; auto. 
    }
    iInduction (l) as [|x l] "IH". 
    - iFrame. done.
    - apply NoDup_cons in Hdup as [Hdup Hnin]. 
      iDestruct "Hl" as "[ [Hx #[Hrel Hrev] ] Hl]". rewrite fmap_cons /=. 
      rewrite /close_list region_eq /region_def /std_sta /std_rel /=.
      iMod ("IH" $! Hnin with "Hl Hfull Hr") as "(Hfull & Hr)"; auto.
      iClear "IH".
      destruct W as [ [Wstd_sta Wstd_rel] Wloc].
      iDestruct (sts_full_world_std with "[] Hfull") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|].
      iDestruct "Hx" as (a HO) "(Hx & Hmono & Hφ)".
      iDestruct "Hr" as (M) "(HM & #Hdom & Hr)". iDestruct "Hdom" as %Hdom.
      rewrite rel_eq /rel_def REL_eq RELS_eq. iDestruct "Hrel" as (γpred) "[HREL Hpred]".
      iDestruct (reg_in γrel M with "[$HM $HREL]") as %HMeq. rewrite HMeq. 
      iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hstate Hr]"; [apply lookup_insert|].
      iDestruct "Hstate" as (ρ) "[Hρ Hstate]". 
      iDestruct (sts_full_state_std with "Hfull Hρ") as %Hx''.      
      rewrite -(close_list_std_sta_same _ (countable.encode <$> l) _) in Hx''.
      2: { intros Hcontr. apply elem_of_list_fmap_2 in Hcontr as [y [Hxy Hcontr] ].
           apply encode_inj in Hxy; subst. contradiction. }
      rewrite  Hx''. iFrame. iSimplifyEq. rewrite Positive_as_OT.eqb_refl.
      iMod (sts_update_std _ _ _ Temporary with "Hfull Hρ") as "[Hfull Hρ] /=". iFrame. 
      iModIntro. iExists M. rewrite HMeq.
      iDestruct (big_sepM_delete _ _ x with "[Hρ Hr Hx Hmono Hφ]") as "$"; [apply lookup_insert|..].
      { do 2 (rewrite delete_insert;[|apply lookup_delete]).
        iSplitR "Hr".
        - iExists Temporary. iFrame. rewrite /future_pub_mono. iExists γpred,a,p,φ.
          repeat (iSplit; auto).
          iAssert (future_pub_mono φ a) as "#Hmono'".
          { destruct (pwl p); iDestruct "Hmono" as "#Hmono"; iAlways.
            - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). auto.
            - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto.
          }
          iFrame "# ∗".
          iNext. iApply "Hmono'"; iFrame.
          iPureIntro. apply close_list_related_sts_pub_insert; auto.
          intros Hcontr. apply elem_of_list_fmap in Hcontr as [y [Heq Hy] ].
          apply encode_inj in Heq; subst. contradiction. 
        - iApply (big_sepM_mono with "Hr").
          iIntros (a' γp Hsome) "Hρ /=". iDestruct "Hρ" as (ρ) "[Hstate Hρ]".
          iExists ρ. iFrame. destruct ρ; auto.
          + iDestruct "Hρ" as (γpred' v p' φ0) "(Heq & HO & Ha' & Hmono & Hpred & Hφ0)".
            iExists _,_,_,_.
            iAssert (future_pub_mono φ0 v) as "#Hmono'".
            { destruct (pwl p'); iDestruct "Hmono" as "#Hmono"; iAlways.
              - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). auto.
              - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto.
            } iFrame. 
            iNext. iApply ("Hmono'" with "[] Hφ0"). iPureIntro.
            apply close_list_related_sts_pub_insert'; auto.
            intros Hcontr. apply elem_of_list_fmap in Hcontr as [y [Heq Hy] ].
            apply encode_inj in Heq; subst. contradiction. 
          + iDestruct "Hρ" as (γpred' v p' φ0) "(Heq & HO & Ha' & #Hmono & Hpred & Hφ0)".
            iExists _,_,_,_. iFrame "∗ #". 
            iNext. iApply ("Hmono" with "[] Hφ0"). iPureIntro.
            apply related_sts_pub_priv_world.
            apply close_list_related_sts_pub_insert'; auto.
            intros Hcontr. apply elem_of_list_fmap in Hcontr as [y [Heq Hy] ].
            apply encode_inj in Heq; subst. contradiction. 
      }
      do 2 (rewrite -HMeq). iFrame. iPureIntro.
      (* The domains remain equal *)
      intros i. destruct Hdom with i as [Hdom1 Hdom2].
      destruct Hdom with (countable.encode x) as [Hdomx1 Hdomx2]. 
      split.
      + intros Hsome. destruct (decide (i = countable.encode x)); subst. 
        ++ apply Hdomx1. 
           apply close_list_std_sta_is_Some. eauto.
        ++ rewrite lookup_insert_ne in Hsome; auto.
      + intros [a0 [Heq Hsome] ]. destruct (decide (i = countable.encode x)); subst. 
        ++ rewrite e. rewrite lookup_insert. eauto. 
        ++ rewrite lookup_insert_ne; auto. destruct Hdom2 as [xa0 Ha0]; eauto.
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

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
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
  Program Definition interp_reg (interp : D) : R :=
   λne (W : WORLD) (reg : leibnizO Reg), (full_map reg ∧ 
                                          ∀ (r : RegName), (⌜r ≠ PC⌝ → interp W (reg !r! r)))%I.
  Solve All Obligations with solve_proper. 

  Definition interp_conf W : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ →
              ∃ r W', full_map r ∧ registers_mapsto r
                   ∗ ⌜related_sts_priv_world W W'⌝
                   ∗ na_own logrel_nais ⊤                           
                   ∗ sts_full_world sts_std W'
                   ∗ region W' }})%I.

  Program Definition interp_expr (interp : D) r : D :=
    (λne W w, (interp_reg interp W r ∗ registers_mapsto (<[PC:=w]> r)
                                     ∗ region W
                                     ∗ sts_full_world sts_std W
                                     ∗ na_own logrel_nais ⊤ -∗
                                     ⌜match w with inr _ => True | _ => False end⌝ ∧ interp_conf W))%I.
  Solve All Obligations with solve_proper. 

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
    | Local => ⌜related_sts_pub_world W W'⌝
    | Global => ⌜related_sts_priv_world W W'⌝
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

  Definition region_state_pwl W (a : Addr) : Prop :=
    (std_sta W) !! (countable.encode a) = Some (countable.encode Temporary).

  Definition region_state_nwl W (a : Addr) (l : Locality) : Prop :=
    match l with
     | Local => (std_sta W) !! (countable.encode a) = Some (countable.encode Temporary)
               ∨ (std_sta W) !! (countable.encode a) = Some (countable.encode Permanent)
    | Global => (std_sta W) !! (countable.encode a) = Some (countable.encode Permanent)
    end.

  (* For simplicity we might want to have the following statement in valididy of caps. However, it is strictly not 
     necessary since it can be derived form full_sts_world *)
  Definition region_std W (a : Addr) : Prop := rel_is_std_i W (countable.encode a).
  
  Definition interp_cap_RO (interp : D) : D :=
    λne W w, (match w with
              | inr ((RO,g),b,e,a) =>
                ∃ p, ⌜PermFlows RO p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp) ∧ ⌜region_state_nwl W a g⌝ ∧ ⌜region_std W a⌝
              | _ => False
              end)%I.
  
  Definition interp_cap_RW (interp : D) : D :=
    λne W w, (match w with
              | inr ((RW,g),b,e,a) =>
                ∃ p, ⌜PermFlows RW p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp) ∧ ⌜region_state_nwl W a g⌝ ∧ ⌜region_std W a⌝
              | _ => False
              end)%I.
  
  Definition interp_cap_RWL (interp : D) : D :=
    λne W w, (match w with
              | inr ((RWL,Local),b,e,a) =>
                ∃ p, ⌜PermFlows RWL p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp) ∧ ⌜region_state_pwl W a⌝ ∧ ⌜region_std W a⌝
              | _ => False
              end)%I.

  Definition interp_cap_RX (interp : D) : D :=
    λne W w, (match w with inr ((RX,g),b,e,a) =>
                           ∃ p, ⌜PermFlows RX p⌝ ∗
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_nwl W a g⌝ ∧ ⌜region_std W a⌝)
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
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_nwl W a g⌝ ∧ ⌜region_std W a⌝) 
                                 ∗ □ exec_cond W b e g RWX interp
             | _ => False end)%I.
  
  Definition interp_cap_RWLX (interp : D) : D :=
    λne W w, (match w with inr ((RWLX,Local),b,e,a) =>
                           ∃ p, ⌜PermFlows RWLX p⌝ ∗
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_pwl W a⌝ ∧ ⌜region_std W a⌝) 
                                 ∗ □ exec_cond W b e Local RWLX interp
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
         apply and_ne; auto. 
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
         apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto. 
         simpl. f_equiv. solve_contractive. 
  Qed. 
  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct c, p, p, p, p, l; auto.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto. 
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
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto. 
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
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto. 
      simpl. f_equiv. solve_contractive. 
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. 
  Qed.
  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    rewrite /interp_cap_RWLX.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p, l; auto.
    apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. apply sep_ne. 
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto. 
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
         destruct c,p,p,p,p; destruct l; repeat (apply exist_persistent; intros); try apply _.
  Qed. 

  Lemma read_allowed_inv W (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' ≤ e)%Z →
    readAllowed p → (interp W (inr ((p,g),b,e,a)) →
      (∃ p', ⌜PermFlows p p'⌝ ∗ (read_write_cond a' p' interp)))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p,g; try contradiction;
    try (iDestruct "Hinterp" as (p) "[Hleast Hinterp]");
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]");
    iExists _; iFrame; 
    try (iDestruct (extract_from_region_inv_2 with "Hinterp") as (w) "[ [Hinv _] _]"; eauto); 
    try (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv _]"; eauto).
    - done.
    - done.
      Unshelve. exact RWL. exact RWLX. 
  Qed.
  
End logrel.

(* Notation "𝕍( W )" := (interp W) (at level 70). *)
(* Notation "𝔼( W )" := (λ r, interp_expression r W). *)
(* Notation "ℝ( W )" := (interp_registers W). *)
(* Notation "𝕆( W )" := (interp_conf W.1 W.2).  *)


    
