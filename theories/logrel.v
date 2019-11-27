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
  
  Definition std_update (W : WORLD) (l : Addr) (a : region_type) (r1 r2 : region_type → region_type -> Prop) : WORLD :=
    ((<[countable.encode l := countable.encode a]>W.1.1,
      <[countable.encode l := (convert_rel r1,convert_rel r2)]>W.1.2), W.2). 
  Definition loc_update (W : WORLD) (l : Addr) (a : region_type) (r1 r2 : region_type → region_type -> Prop) : WORLD :=
    (W.1,(<[countable.encode l := countable.encode a]>W.2.1,
          <[countable.encode l := (convert_rel r1,convert_rel r2)]>W.2.2)).

  Notation "<s[ a := ρ , r ]s> W" := (std_update W a ρ r.1 r.2) (at level 10, format "<s[ a := ρ , r ]s> W").
  Notation "<l[ a := ρ , r ]l> W" := (loc_update W a ρ r.1 r.2) (at level 10, format "<l[ a := ρ , r ]l> W").

  Definition open_region_def (a : Addr) (W : WORLD) : iProp Σ :=
    (∃ (M : relT), RELS M ∗ ⌜dom_equal (std_sta W) M⌝ ∗ region_map_def (delete a M) W)%I. 
  Definition open_region_aux : { x | x = @open_region_def }. by eexists. Qed.
  Definition open_region := proj1_sig open_region_aux.
  Definition open_region_eq : @open_region = @open_region_def := proj2_sig open_region_aux.

  Lemma related_sts_pub_priv_world W W' :
    related_sts_pub_world W W' -> related_sts_priv_world W W'.
  Proof.
    intros [Hstd Hloc].
    split; apply related_sts_pub_priv; auto.
  Qed.

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
    std_rel W !! (countable.encode a) = Some (convert_rel (Rpub : relation region_type),convert_rel (Rpriv : relation region_type)) →
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
      + subst. rewrite Hr in Hdom_rel. rewrite lookup_insert in Hr'. simplify_eq.
        repeat (split;auto). intros x y Hcontr. rewrite Hcontr in Hdom_sta. done. 
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy. 
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy. 
        inversion Hy; inversion Hr'; subst.
        left.
  Qed. 
  
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

  (* Closing the region without updating the world *)
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

  (* Next we need to define revocation of memory *)

  (* Revocation only changes the states of the standard STS collection *)
  Definition revoke_std_sta : STS_states → STS_states :=
    fmap (λ v, if ((countable.encode Temporary) =? v)%positive then countable.encode Revoked else v
         (* match countable.decode v with *)
         (* | Some Temporary => countable.encode Revoked *)
         (* | _ => v *)
         (* end *) ). 
  Definition revoke W : WORLD := ((revoke_std_sta (std_sta W),std_rel W), loc W).

  (* A weaker revocation which only revokes elements from a list *)
  Fixpoint revoke_list_std_sta (l : list positive) (fs : STS_states) : STS_states :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => if ((countable.encode Temporary) =? j)%positive
                          then <[i := countable.encode Revoked]> (revoke_list_std_sta l' fs)
                          else (revoke_list_std_sta l' fs)
               (* match countable.decode j with *)
               (* | Some Temporary => <[i := countable.encode Revoked]> (revoke_list_std_sta l' fs) *)
               (* | _ => (revoke_list_std_sta l' fs) *)
               (* end *)
               | None => (revoke_list_std_sta l' fs)
               end
    end.
  Definition revoke_list l W : WORLD := ((revoke_list_std_sta l (std_sta W),std_rel W), loc W).

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
    
  Lemma revoke_list_dom W :
    revoke W = revoke_list (map_to_list W.1.1).*1 W.
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]. 
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
      + rewrite /std_rel /std_sta /=. 
        rewrite /revoke /revoke_list /revoke_std_sta /std_sta /std_rel /= in IHWstd_sta.
        inversion IHWstd_sta.
        do 2 f_equiv. 
        rewrite revoke_list_insert_insert. repeat f_equiv. auto.
      + rewrite /std_rel /std_sta /=. do 2 f_equiv.
        rewrite /revoke /revoke_list /revoke_std_sta /std_sta /std_rel /= in IHWstd_sta.
        inversion IHWstd_sta. rewrite H5.
        apply revoke_list_not_elem_of.
        intros Hcontr. apply (elem_of_list_fmap_2 fst) in Hcontr.
        destruct Hcontr as [ [y1 y2] [Hy Hyin] ]. subst.
        apply elem_of_map_to_list in Hyin. simpl in *. congruence.
  Qed.

  Lemma map_to_list_fst {A B : Type} `{EqDecision A, Countable A} (m : gmap A B) i :
    i ∈ (map_to_list m).*1 ↔ (∃ x, (i,x) ∈ (map_to_list m)).
  Proof.
    split.
    - intros Hi.
      destruct (m !! i) eqn:Hsome.
      + exists b. by apply elem_of_map_to_list.
      + apply not_elem_of_list_to_map in Hi; [done|].
          by rewrite list_to_map_to_list.
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

  Lemma revoke_list_lookup_Perm (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∉ l →
    (Wstd_sta !! i = Some (countable.encode Permanent)) →
    (revoke_list_std_sta (i :: l) Wstd_sta) !! i = Some (countable.encode Permanent). 
  Proof.
    induction l.
    - intros Hin Hp.
      rewrite /= Hp. 
      destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|done].
      apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr. 
    - intros Hin Hp.
      apply not_elem_of_cons in Hin as [Hneq Hin]. 
      rewrite revoke_list_swap. 
      rewrite /=.
      destruct (Wstd_sta !! a).
      + rewrite Hp. destruct (countable.encode Temporary =? p)%positive.
        * destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
          apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
          rewrite lookup_insert_ne;auto.
          specialize (IHl Hin Hp). 
          by rewrite /= Hp Hcontr in IHl. 
        * destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
          apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
          specialize (IHl Hin Hp). 
          by rewrite /= Hp Hcontr in IHl. 
      + rewrite Hp. 
        destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
        apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
        specialize (IHl Hin Hp). 
          by rewrite /= Hp Hcontr in IHl. 
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

  Lemma revoke_monotone W W' :
    related_sts_priv_world W W' → related_sts_priv_world (revoke W) (revoke W').
  Proof.
    revert W'. 
    destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
    induction Wstd_sta using map_ind;intros W';
    destruct W' as [ [Wstd_sta' Wstd_rel'] [Wloc_sta' Wloc_rel'] ];
    rewrite /revoke /std_sta /std_rel /=;
    intros [Hrelated_std Hrelated_loc];
    split;auto;simpl in *. 
    - destruct Hrelated_std as (Hdom_sta & Hdom_rel & Htransition). split;[|split;auto].
      + rewrite /revoke_std_sta fmap_empty dom_empty. done.
      + intros i r1 r2 r1' r2' Hr Hr'.
        specialize (Htransition i r1 r2 r1' r2' Hr Hr') as (-> & -> & Htransition).
        repeat (split;auto).
        intros x y Hcontr.
        inversion Hcontr.
    - destruct Hrelated_std as (Hdom_sta & Hdom_rel & Htransition). split;[|split;auto].
      + apply elem_of_subseteq in Hdom_sta. 
        assert (is_Some (Wstd_sta' !! i)) as Hsome. 
        { apply elem_of_gmap_dom;apply Hdom_sta.
          apply elem_of_gmap_dom. rewrite lookup_insert. eauto. } 
        apply elem_of_subseteq. intros j Hj.
        apply elem_of_gmap_dom in Hj; apply elem_of_gmap_dom.
        destruct (decide (i=j));subst. 
        { by apply (revoke_std_sta_lookup_Some Wstd_sta'). }
        { apply (revoke_std_sta_lookup_Some) in Hj. rewrite lookup_insert_ne in Hj;auto.
          admit. 
        }
  Admitted. 
    
  Lemma map_size_insert_Some {K A} `{EqDecision K, Countable K} i x (m : gmap K A) :
    is_Some(m !! i) → size (<[i:=x]> m) = (size m).
  Proof. induction m using map_ind.
         - intros [y Hcontr]; inversion Hcontr.
         - intros Hsome.
           destruct (decide (i = i0)). 
           + subst.
             rewrite insert_insert. 
             unfold size, map_size.
             do 2 (rewrite map_to_list_insert; auto).
           + rewrite insert_commute;auto. 
             unfold size, map_size.
             rewrite map_to_list_insert;[|rewrite lookup_insert_ne;auto].
             rewrite (map_to_list_insert _ i0);auto.
             simpl. f_equal. apply IHm.
             rewrite lookup_insert_ne in Hsome;auto. 
  Qed.

  Lemma revoke_list_related_sts_priv_cons W l i :
    (is_Some (W.1.2 !! i) → W.1.2 !! i = Some (convert_rel (Rpub : relation region_type),
                                               convert_rel (Rpriv : relation region_type))) →
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
    (∀ (i : positive), is_Some(W.1.2 !! i) → W.1.2 !! i = Some (convert_rel (Rpub : relation region_type),
                                                                convert_rel (Rpriv : relation region_type))) →
    related_sts_priv_world W (revoke_list l W).
  Proof.
    induction l.
    - split; apply related_sts_priv_refl.
    - split;[|apply related_sts_priv_refl].
      apply revoke_list_related_sts_priv_cons; auto. 
  Qed.

  Lemma revoke_related_sts_priv W :
    (∀ (i : positive), is_Some(W.1.2 !! i) → W.1.2 !! i = Some (convert_rel (Rpub : relation region_type),
                                                                convert_rel (Rpriv : relation region_type))) →
    related_sts_priv_world W (revoke W).
  Proof.
    intros Hstd.
    rewrite revoke_list_dom. apply revoke_list_related_sts_priv.
    done. 
  Qed.

  Lemma revoke_list_size W l :
    size (revoke_list l W).1.1 = size W.1.1. 
  Proof.
    induction l.
    - done.
    - destruct W as [Wstd Wloc].
      destruct Wstd as [Wstd_sta Wstd_rel].
      rewrite /= /std_sta /=. rewrite /= /std_sta /= in IHl. 
      destruct (Wstd_sta !! a) eqn:Hsome.
      + destruct (countable.encode Temporary =? p)%positive; auto.
        rewrite (map_size_insert_Some); auto.
        apply revoke_list_lookup_Some. eauto.
      + apply IHl.
  Qed.
    
  (* TODO: choose between:
     1) restate revoke so that it only actually revokes the temporary in the M map
     2) change region definition to related the domains of M and Wstd_sta to be equal
        (we can argue that we want Wstd_sta to exactly represent the map M, and thus 
        revoke should cover all temps in Wstd_sta)
   *)

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

  (* Lemma dom_equal_revoke W M : *)
  (*   dom_equal (std_sta W) M → dom_equal (std_sta (revoke W)) M. *)
  (* Proof. *)
  (* Admitted. *)
  
  (* Lemma dom_equal_insert_delete m M (x : positive) (a : Addr) : *)
  (*   dom_equal (<[countable.encode a:=x]> m) M → *)
  (*   dom_equal m (delete a M). *)
  (* Proof. *)
  (*   Admitted.  *)

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
  
  Lemma monotone_revoke_list_region_def M W W' :
    ⌜related_sts_priv_world W W'⌝ -∗
     ⌜dom_equal (std_sta W') M⌝ -∗
     sts_full_world sts_std (revoke W) -∗
     region_map_def M (revoke W) -∗ region_map_def M (revoke W') ∗ sts_full_world sts_std (revoke W).
  Proof.
    iIntros (Hrelated Hdom) "Hfull Hr".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Htemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[_ Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro. admit. 
    }
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
    iPureIntro. by apply revoke_monotone.
  Admitted.     
    
  Lemma sts_full_world_std W W' :
    (⌜related_sts_priv_world W W'⌝
      -∗ sts_full_world sts_std W'
    → ⌜∀ (i : positive), is_Some(W.1.2 !! i) → W.1.2 !! i = Some (convert_rel (Rpub : relation region_type),
                                                                convert_rel (Rpriv : relation region_type))⌝)%I. 
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

  Lemma monotone_revoke_list_sts_full_world M W l :
    ⌜∀ (i : positive), i ∈ l→∃ (a : Addr), countable.encode a = i ∧ is_Some (M !! a)⌝ -∗
    ⌜NoDup l⌝ -∗
    sts_full_world sts_std W ∗ region_map_def M W
    ==∗ (sts_full_world sts_std (revoke_list l W)
          ∗ region_map_def M W).
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

  Lemma monotone_revoke_sts_full_world W :
    sts_full_world sts_std W ∗ region W
    ==∗ (sts_full_world sts_std (revoke W)
          ∗ region W).
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

  
  
  Lemma monotone_revoke W :
    sts_full_world sts_std W ∗ region W ==∗ sts_full_world sts_std (revoke W) ∗ region (revoke W).
  Proof.
    iIntros "[HW Hr]".
    iMod (monotone_revoke_sts_full_world with "[] [$HW Hr]") as "[HW Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M) "(HM & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "Hpreds") as "Hpreds".
    iModIntro. iFrame. iExists _. iFrame.
    iPureIntro. by apply dom_equal_revoke.
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
         [∗ map] l↦γ ∈ (delete_list l M), ∃ ρ, sts_state_std (countable.encode l) ρ ∗
                            match ρ with
                            | Temporary => ∃ γpred (v : Word) (p : Perm) φ,
                                               ⌜γ = to_agree (γpred,p)⌝
                                             ∗ ⌜p ≠ O⌝
                                             ∗ l ↦ₐ[p] v
                                             ∗ future_pub_mono φ
                                             ∗ saved_pred_own γpred φ
                                             ∗ ▷ φ (W,v)
                            | Permanent => ∃ γpred (v : Word) (p : Perm) φ,
                                               ⌜γ = to_agree (γpred,p)⌝
                                             ∗ ⌜p ≠ O⌝
                                             ∗ l ↦ₐ[p] v
                                             ∗ future_priv_mono φ
                                             ∗ saved_pred_own γpred φ
                                             ∗ ▷ φ (W,v)
                            | Revoked => emp
                            end)%I. 
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

  Lemma region_open_next_temp W φ ls l p :
    l ∉ ls → (std_sta W) !! (countable.encode l) = Some (countable.encode Temporary) -> 
    open_region_many ls W ∗ rel l p φ ∗ sts_full_world W -∗
                     ∃ v, sts_full_world W
                        ∗ sts_state_std (countable.encode l) Temporary
                        ∗ open_region_many (l :: ls) W
                        ∗ l ↦ₐ[p] v
                        ∗ ⌜p ≠ O⌝
                        ∗ ▷ future_pub_mono φ
                        ∗ ▷ φ (W,v). 
  Proof.
    rewrite open_region_many_eq . 
    iIntros (Hnin Htemp) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /=. 
    rewrite rel_eq /rel_def /rel_def /region_def REL_eq RELS_eq /rel /region /REL /RELS. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M) "(HM & Hpreds)". 
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. 
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H4. done. }
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H4. done. }    
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & #Hmono & #Hφ' & Hφv)".  
    inversion H3; subst.
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv". 
    - rewrite /open_region.
      iExists _. repeat (rewrite -HMeq). iFrame "∗ #".
    - iSplitR;[auto|]. iSplitR.
      + rewrite /future_pub_mono.
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

  Lemma region_open_next_perm W φ ls l p :
    l ∉ ls → (std_sta W) !! (countable.encode l) = Some (countable.encode Permanent) -> 
    open_region_many ls W ∗ rel l p φ ∗ sts_full_world W -∗
                     ∃ v, sts_full_world W
                        ∗ sts_state_std (countable.encode l) Permanent
                        ∗ open_region_many (l :: ls) W
                        ∗ l ↦ₐ[p] v
                        ∗ ⌜p ≠ O⌝
                        ∗ ▷ future_priv_mono φ
                        ∗ ▷ φ (W,v). 
  Proof.
    rewrite open_region_many_eq . 
    iIntros (Hnin Htemp) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /=. 
    rewrite rel_eq /rel_def /rel_def /region_def REL_eq RELS_eq /rel /region /REL /RELS. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M) "(HM & Hpreds)". 
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. 
    1: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H4. done. }
    2: { iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
         rewrite Htemp in Hcontr. inversion Hcontr. apply countable.encode_inj in H4. done. }    
    iDestruct "Hl" as (γpred' v p' φ') "(% & % & Hl & #Hmono & #Hφ' & Hφv)".  
    inversion H3; subst.
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv". 
    - rewrite /open_region.
      iExists _. repeat (rewrite -HMeq). iFrame "∗ #".
    - iSplitR;[auto|]. iSplitR.
      + iApply later_intuitionistically_2. iAlways.
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

  Lemma region_close_next_temp W φ ls l p v :
    l ∉ ls ->
    sts_state_std (countable.encode l) Temporary ∗
                  open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_pub_mono φ ∗ ▷ φ (W,v) ∗ rel l p φ
                  -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def. 
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iExists _,_,_,_. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -delete_list_delete; auto. rewrite -delete_list_insert; auto.
    rewrite -HMeq. 
    iFrame "# ∗".
  Qed.

  Lemma region_close_next_perm W φ ls l p v :
    l ∉ ls ->
    sts_state_std (countable.encode l) Permanent ∗
                  open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ ∗ ▷ φ (W,v) ∗ rel l p φ
                  -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def. 
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M) "(HM & Hpreds)".
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iExists _,_,_,_. iFrame "∗ #". (iSplitR;[eauto|]). done. }
    iExists _.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -delete_list_delete; auto. rewrite -delete_list_insert; auto.
    rewrite -HMeq. 
    iFrame "# ∗".
  Qed.

  (* ------------------------------- REVOCATION ------------------------------- *)
  (* We now need to define a way to revoke all temporary regions of a world.
     We will define a singular revoke action, which revokes a particulat location
     and returns the given resources, with the updated Word. However, we require  *)
  
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


    