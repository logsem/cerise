From iris.algebra Require Import gmap agree auth.
From cap_machine Require Export lang sts rules_base.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export invariants na_invariants saved_prop.
(* import [stdpp.countable] before [cap_machine.lang]; this way [encode] and
   [decode] refer to [countable.encode] and [countable.decode], instead of
   [cap_lang.encode]/[cap_lang.decode]. *)
From stdpp Require Import countable.
Import uPred. 

(** CMRA for heap and its predicates. Contains: *)
(* CMRA for relatedness between locations and saved prop names *)
(* CMRA for saved predicates *)
Definition relUR : ucmraT := gmapUR Addr (agreeR (leibnizO (gname * Perm))).
Definition relT := gmap Addr (leibnizO (gname * Perm)). 

(* We will first define the standard STS for the shared part of the heap *)
Inductive region_type :=
| Temporary
| Permanent
| Revoked
| Static of gmap Addr (Perm * Word).

Inductive std_rel_pub : region_type -> region_type -> Prop :=
| Std_pub_Revoked_Temporary : std_rel_pub Revoked Temporary
| Std_pub_Static_Temporary m : std_rel_pub (Static m) Temporary.

Inductive std_rel_priv : region_type -> region_type -> Prop :=
| Std_priv_from_Temporary ρ : std_rel_priv Temporary ρ
| Std_priv_Revoked_Permanent : std_rel_priv Revoked Permanent.

Global Instance sts_std : STS_STD region_type :=
    {| Rpub := std_rel_pub; Rpriv := std_rel_priv |}.

Class heapPreG Σ := HeapPreG {
  heapPreG_invPreG : invPreG Σ;
  heapPreG_saved_pred :> savedPredG Σ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word);
  heapPreG_rel :> inG Σ (authR relUR);
}.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_saved_pred :> savedPredG Σ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word);
  heapG_rel :> inG Σ (authR relUR);
  γrel : gname
}.

Definition heapPreΣ :=
  #[ GFunctor (authR relUR) ].

Instance subG_heapPreΣ {Σ}:
  subG heapPreΣ Σ →
  invPreG Σ →
  subG (savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word)) Σ →
  heapPreG Σ.
Proof. solve_inG. Qed.

Section REL_defs.
  Context {Σ:gFunctors} {heapg : heapG Σ}.

  Definition REL_def l p γ : iProp Σ := own γrel (◯ {[ l := to_agree (γ,p) ]}).
  Definition REL_aux : { x | x = @REL_def }. by eexists. Qed.
  Definition REL := proj1_sig REL_aux.
  Definition REL_eq : @REL = @REL_def := proj2_sig REL_aux.

  Definition RELS_def (M : relT) : iProp Σ := own γrel (● (to_agree <$> M : relUR)).
  Definition RELS_aux : { x | x = @RELS_def }. by eexists. Qed.
  Definition RELS := proj1_sig RELS_aux.
  Definition RELS_eq : @RELS = @RELS_def := proj2_sig RELS_aux.

  Definition rel_def (l : Addr) (p : Perm) (φ : ((STS_std_states Addr region_type * (STS_states * STS_rels)) * Word) -> iProp Σ) : iProp Σ :=
    (∃ (γpred : gnameO), REL l p γpred 
                       ∗ saved_pred_own γpred φ)%I.
  Definition rel_aux : { x | x = @rel_def }. by eexists. Qed.
  Definition rel := proj1_sig rel_aux.
  Definition rel_eq : @rel = @rel_def := proj2_sig rel_aux.
End REL_defs.

Section heapPre.
  Context {Σ:gFunctors} {heappreg : heapPreG Σ}.

  Lemma heap_init :
    (|==> ∃ (heapg: heapG Σ), RELS (∅ : relT))%I.
  Proof.
    iMod (own_alloc (A:= (authR relUR)) (● (to_agree <$> (∅: relT) : relUR))) as (γ) "H".
    { rewrite map_fmap_empty. by apply auth_auth_valid. }
    iMod (@wsat.wsat_alloc _ heapPreG_invPreG) as (HI) "?".
    iModIntro. iExists (HeapG _ HI _ _ γ). rewrite RELS_eq /RELS_def. done.
  Qed.

End heapPre.

Section heap.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Global Instance region_type_EqDecision : EqDecision region_type :=
    (fun x y => match x, y with
             | Temporary, Temporary
             | Permanent, Permanent
             | Revoked, Revoked => left eq_refl
             | Static m1, Static m2 => ltac:(solve_decision)
             | _, _ => ltac:(right; auto)
             end).

  Global Instance region_type_countable : Countable region_type.
  Proof.
    set encode := fun ty => match ty with
                         | Temporary => 1
                         | Permanent => 2
                         | Revoked => 3
                         | Static m => 3 + (encode m)
                         end%positive.
    set decode := (fun n =>
                     if decide (n = 1) then Some Temporary
                     else if decide (n = 2) then Some Permanent
                          else if decide (n = 3) then Some Revoked
                               else
                                 match decode (n-3) with
                                 | Some m => Some (Static m)
                                 | None => None
                                 end)%positive.
    eapply (Build_Countable _ _ encode decode).
    intro ty. destruct ty; try reflexivity.
    unfold encode, decode.
    repeat match goal with |- context [ decide ?x ] =>
                           destruct (decide x); [ exfalso; lia |] end.
    rewrite Pos.add_comm Pos.add_sub decode_encode //.
  Qed.

  Global Instance rel_persistent l p (φ : (WORLD * Word) -> iProp Σ) :
    Persistent (rel l p φ).
  Proof. rewrite rel_eq /rel_def REL_eq /REL_def. apply _. Qed.
  
  Definition future_pub_mono (φ : (WORLD * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ W W', ⌜related_sts_pub_world W W'⌝ → φ (W,v) -∗ φ (W',v))%I.

  Definition future_priv_mono (φ : (WORLD * Word) -> iProp Σ) v : iProp Σ :=
    (□ ∀ W W', ⌜related_sts_priv_world W W'⌝ → φ (W,v) -∗ φ (W',v))%I.

  (* Some practical shorthands for projections *)
  Definition std W := W.1.
  Definition loc W := W.2.

  (* The following predicates states that the std relations map in the STS collection is standard according to sts_std *)
  (* Definition rel_is_std_i W i := (std_rel W) !! i = Some (convert_rel (Rpub : relation region_type), *)
  (*                                                       convert_rel (Rpriv : relation region_type)).  *)
  (* Definition rel_is_std W := (∀ i, is_Some ((std_rel W) !! i) → rel_is_std_i W i). *)

  (* ------------------------------------------- DOM_EQUAL ----------------------------------------- *)
  (* dom_equal : we require the domain of the STS standard collection and the memory map to be equal *)

  (*Definition dom_equal (Wstd_sta : STS_states) (M : relT) :=
    ∀ (i : positive), is_Some (Wstd_sta !! i) ↔ (∃ (a : Addr), countable.encode a = i ∧ is_Some (M !! a)).

  Lemma dom_equal_empty : dom_equal ∅ ∅.
  Proof.
    rewrite /dom_equal =>a.
    split; intros [x Hx]; [inversion Hx|destruct Hx as [_ Hx];by inversion Hx]. 
  Qed.

  Lemma dom_equal_insert Wstd_sta M (a : Addr) x y :
    dom_equal Wstd_sta M → dom_equal (<[encode a := x]> Wstd_sta) (<[a := y]> M).
  Proof.
    intros Heq.
    rewrite /dom_equal =>i.
    split; intros [z Hz]. 
    - destruct (decide ((encode a) = i)); subst.
      { exists a. split;[auto|]. rewrite lookup_insert. eauto. }
      { rewrite lookup_insert_ne in Hz; auto.
        destruct Heq with i as [Heq_i _].
        destruct Heq_i as [a' [Ha' HMa'] ]; eauto.
        exists a'; split;[auto|]. rewrite lookup_insert_ne; auto.
        intros Ha. subst. done. 
      }
    - destruct Hz as [Hi Hz]. 
      destruct (decide ((encode a) = i)); subst.
      { rewrite e. rewrite lookup_insert. eauto. }
      { rewrite lookup_insert_ne;auto.
        destruct Heq with (encode z) as [_ Heq_i].
        apply Heq_i.
        exists z. split; auto.
        rewrite lookup_insert_ne in Hz; auto.
        intros Ha; congruence. 
      }
  Qed.

  Lemma dom_equal_change_l (W1 W2: STS_states) (M: relT):
    dom_equal W1 M →
    dom (gset positive) W1 = dom (gset positive) W2 →
    dom_equal W2 M.
  Proof.
    unfold dom_equal. intros HH1 Hdom.
    intros i. rewrite elem_of_gmap_dom -Hdom -elem_of_gmap_dom //.
  Qed.*)

  (* Asserting that a location is in a specific state in a given World *)

  Definition temporary (W : WORLD) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = Temporary
    | _ => False
    end.
  Definition permanent (W : WORLD) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = Permanent
    | _ => False
    end.
  Definition revoked (W : WORLD) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = Revoked
    | _ => False
    end.
  Definition static (W : WORLD) (m: gmap Addr (Perm * Word)) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = (Static m)
    | _ => False
    end.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- REGION_MAP ---------------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  Definition region_map_def M (Mρ: gmap Addr region_type) W :=
    ([∗ map] a↦γp ∈ M, ∃ ρ, ⌜Mρ !! a = Some ρ⌝ ∗
                            sts_state_std a ρ ∗
                            ∃ γpred p φ, ⌜γp = (γpred,p)⌝ ∗ ⌜∀ Wv, Persistent (φ Wv)⌝ ∗ saved_pred_own γpred φ ∗
                            match ρ with
                            | Temporary => ∃ (v : Word),
                                               ⌜p ≠ O⌝
                                             ∗ a ↦ₐ[p] v
                                             ∗ (if pwl p
                                               then future_pub_mono φ v
                                               else future_priv_mono φ v)
                                             ∗ ▷ φ (W,v)
                            | Permanent => ∃ (v : Word),
                                               ⌜p ≠ O⌝
                                             ∗ a ↦ₐ[p] v
                                             ∗ future_priv_mono φ v
                                             ∗ ▷ φ (W,v)
                            | Static m => ∃ p v, ⌜m !! a = Some (p, v)⌝
                                             ∗ ⌜p ≠ O⌝
                                             ∗ a ↦ₐ[p] v
                                             ∗ ⌜∀ a', a' ∈ dom (gset Addr) m →
                                                      Mρ !! a' = Some (Static m)⌝
                            | Revoked => emp
                            end)%I.

  Definition region_def W : iProp Σ := 
    (∃ (M : relT) Mρ, RELS M ∗ ⌜dom (gset Addr) W.1 = dom (gset Addr) M⌝
                            ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝
                            ∗ region_map_def M Mρ W)%I. 
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


  (* Definition and notation for updating a standard or local state in the STS collection *)
  Definition std_update (W : WORLD) (l : Addr) (a : region_type) : WORLD :=
    (<[ l := a]>W.1, W.2).
  Definition loc_update (W : WORLD) (l : Addr) (a : region_type) (r1 r2 : region_type → region_type -> Prop) : WORLD :=
    (W.1,(<[encode l := encode a]>W.2.1,
          <[encode l := (convert_rel r1,convert_rel r2)]>W.2.2)).

  Notation "<s[ a := ρ ]s> W" := (std_update W a ρ) (at level 10, format "<s[ a := ρ ]s> W").
  Notation "<l[ a := ρ , r ]l> W" := (loc_update W a ρ r.1 r.2) (at level 10, format "<l[ a := ρ , r ]l> W").

  (* ------------------------------------------------------------------- *)
  (* region_map is monotone with regards to public future world relation *)

  Lemma region_map_monotone W W' M Mρ :
    (⌜related_sts_pub_world W W'⌝ →
     region_map_def M Mρ W -∗ region_map_def M Mρ W')%I.
  Proof.
    iIntros (Hrelated) "Hr".
    iApply big_sepM_mono; iFrame.
    iIntros (a γ Hsome) "Hm".
    iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
    iExists ρ. iFrame. iSplitR;[auto|].
    destruct ρ.
    - iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v Hne) "(Hl & Hmono & Hφ)".
      iExists _,_,_. do 2 (iSplitR;[eauto|]).
      iFrame "#". iExists _. iSplitR;eauto. 
      destruct (pwl p);
      (iDestruct "Hmono" as "#Hmono"; iFrame "∗ #";
        iApply "Hmono"; iFrame; auto);
      try (iPureIntro; by apply related_sts_pub_priv_world).
    - iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v Hne) "(Hl & #Hmono & Hφ)".
      iExists _,_,_. do 2 (iSplitR;[eauto|]).
      iFrame "∗ #". iExists _. iFrame "∗ #". iSplit;auto. 
      iApply "Hmono"; iFrame "∗ #"; auto.
      iPureIntro.
      by apply related_sts_pub_priv_world.
    - done.
    - done. 
  Qed. 

  Lemma region_monotone W W' :
    (⌜dom (gset Addr) W.1 = dom (gset Addr) W'.1⌝ →
     ⌜related_sts_pub_world W W'⌝ → region W -∗ region W')%I.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite region_eq.
    iDestruct "HW" as (M Mρ) "(HM & % & % & Hmap)".
    iExists M, Mρ. iFrame.
    iSplitR; [iPureIntro;congruence|]. 
    iSplitR;[auto|].
    iApply region_map_monotone; eauto.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- OPEN_REGION --------------------------------------- *)

  Definition open_region_def (a : Addr) (W : WORLD) : iProp Σ :=
    (∃ (M : relT) Mρ, RELS M ∗ ⌜dom (gset Addr) W.1 = dom (gset Addr) M⌝
                            ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝
                            ∗ region_map_def (delete a M) (delete a Mρ) W)%I.
  Definition open_region_aux : { x | x = @open_region_def }. by eexists. Qed.
  Definition open_region := proj1_sig open_region_aux.
  Definition open_region_eq : @open_region = @open_region_def := proj2_sig open_region_aux.

  (* open_region is monotone wrt public future worlds *)
  Lemma open_region_monotone l W W':
    dom (gset Addr) W.1 = dom (gset Addr) W'.1 →
    related_sts_pub_world W W' →
    (open_region l W -∗ open_region l W')%I.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite open_region_eq /open_region_def.
    iDestruct "HW" as (M Mρ) "(Hm & % & % & Hmap)". iExists M, Mρ. iFrame.
    iSplitR;[iPureIntro;congruence|]. 
    iSplitR; auto.
    iApply region_map_monotone; eauto.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS FOR OPENING THE REGION MAP ----------------------------------- *)

  Lemma region_map_delete_nonstatic M Mρ W l :
    (forall m, Mρ !! l ≠ Some (Static m)) →
    region_map_def (delete l M) Mρ W -∗
    region_map_def (delete l M) (delete l Mρ) W.
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a = l)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
    iDestruct "Hl" as (v Hne) "(% & Hmono & Hφ & Hothers)".
    iExists _,_,_. do 2 (iSplitR;[eauto|]).
    iDestruct "Hothers" as %Hothers. iFrame "#". 
    iExists _, _. iSplitR; eauto. iFrame. iPureIntro.
    intros a' Ha'. destruct (decide (a' = l)).
    { subst. exfalso. apply Hothers in Ha'. congruence. }
    { by simplify_map_eq. }
  Qed.

  Lemma region_open_temp_pwl W l p φ :
    (std W) !! l = Some Temporary →
    pwl p = true →
    rel l p φ ∗ region W ∗ sts_full_world W -∗
        ∃ v, open_region l W
           ∗ sts_full_world W
           ∗ sts_state_std l Temporary
           ∗ l ↦ₐ[p] v
           ∗ ⌜p ≠ O⌝
           ∗ ▷ future_pub_mono φ v
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Htemp Hpwl) "(Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. 
    iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)".
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH1 Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & Hmono & Hφv)".    
    inversion HH1; subst. rewrite Hpwl. iDestruct "Hmono" as "#Hmono".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv". 
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #".
      iExists Mρ. do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. by congruence.
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
    (std W) !! l = Some Temporary →
    pwl p = false →
    rel l p φ ∗ region W ∗ sts_full_world W -∗
        ∃ v, open_region l W
           ∗ sts_full_world W
           ∗ sts_state_std l Temporary
           ∗ l ↦ₐ[p] v
           ∗ ⌜p ≠ O⌝
           ∗ ▷ future_priv_mono φ v
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Htemp Hpwl) "(Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)".
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & Hmono & Hφv)".    
    inversion HH; subst. rewrite Hpwl. iDestruct "Hmono" as "#Hmono".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv". 
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #".
      iExists _. do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. by congruence.
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
    (std W) !! l = Some Permanent →
    rel l p φ ∗ region W ∗ sts_full_world W -∗
        ∃ v, open_region l W
           ∗ sts_full_world W
           ∗ sts_state_std l Permanent              
           ∗ l ↦ₐ[p] v
           ∗ ⌜p ≠ O⌝
           ∗ ▷ future_priv_mono φ v
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Htemp) "(Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. 
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)".
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #Hmono & Hφv)".    
    inversion HH; subst.
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv". 
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #".
      iExists _. do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. by congruence.
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
    ρ = Temporary ∨ ρ = Permanent →
    (std W) !! l = Some ρ →
    rel l p φ ∗ region W ∗ sts_full_world W -∗
        ∃ v, open_region l W
           ∗ sts_full_world W
           ∗ sts_state_std l ρ              
           ∗ l ↦ₐ[p] v
           ∗ ⌜p ≠ O⌝
           ∗ (▷ if (decide (ρ = Temporary ∧ pwl p = true))
             then future_pub_mono φ v
             else future_priv_mono φ v)
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Hne Htemp) "(Hrel & Hreg & Hfull)".
    destruct ρ; try (destruct Hne; exfalso; congruence).
    - destruct (pwl p) eqn:Hpwl.
      + iDestruct (region_open_temp_pwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
      + iDestruct (region_open_temp_nwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
    - iDestruct (region_open_perm with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
      iExists _; iFrame.
  Qed.

  (* It is important here that we have (delete l Mρ) and not simply Mρ.
     Otherwise, [Mρ !! l] could in principle map to a static region (although
     it's not the case in practice), that it would be incorrect to overwrite
     with a non-static state. *)
  Lemma region_map_undelete_nonstatic M Mρ W l :
    (forall m, Mρ !! l ≠ Some (Static m)) →
    region_map_def (delete l M) (delete l Mρ) W -∗
    region_map_def (delete l M) Mρ W.
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a = l)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (γpred' p' φ' HH1 Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (p v HH2 Hne) "(Hl & Hothers)".
    iDestruct "Hothers" as %Hothers.
    iExists _, _,_. iSplitR; eauto. iFrame "∗ #". iSplitR;auto.
    iExists _,_. iFrame. repeat iSplit;auto. iPureIntro.
    intros a' Ha'. apply Hothers in Ha'.
    destruct (decide (a' = l)); by simplify_map_eq.
  Qed.

  Lemma region_map_insert_nonstatic ρ M Mρ W l :
    (forall m, ρ ≠ Static m) →
    region_map_def (delete l M) (delete l Mρ) W -∗
    region_map_def (delete l M) (<[ l := ρ ]> Mρ) W.
  Proof.
    iIntros (?) "HH".
    rewrite {1}(_: delete l Mρ = delete l (<[ l := ρ ]> Mρ)). 2: by rewrite delete_insert_delete//.
    iDestruct (region_map_undelete_nonstatic with "HH") as "HH".
    { intro. simplify_map_eq. congruence. }
    auto.
  Qed.

  Lemma full_sts_Mρ_agree W M Mρ (ρ: region_type) :
    (* NB: only the forward direction of dom_equal (std_sta W) M is actually needed *)
    dom (gset Addr) (std W) = dom (gset Addr) M →
    (* NB: only one direction of this assumption is needed, and only for the reverse *)
  (*      direction of the lemma *)
    dom (gset Addr) Mρ = dom (gset Addr) M →
    sts_full_world W -∗
    region_map_def M Mρ W -∗
    ⌜∀ a:Addr, (std W) !! a = Some ρ ↔ Mρ !! a = Some ρ⌝.
  Proof.
    iIntros (HWM HMMρ) "Hfull Hr".
    iAssert (∀ a:Addr, ⌜ std W !! a = Some ρ ⌝ → ⌜ Mρ !! a = Some ρ ⌝)%I as %?.
    { iIntros (a Haρ).
      assert (is_Some (M !! a)) as [γp Hγp].
      { apply elem_of_gmap_dom.
        rewrite -HWM. apply elem_of_gmap_dom. eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). apply encode_injective.
      rewrite Haρ in Haρ'. congruence. }
    iAssert (∀ a:Addr, ⌜ Mρ !! a = Some ρ ⌝ → ⌜ std W !! a = Some ρ ⌝)%I as %?.
    { iIntros (a HMρa).
      assert (is_Some (M !! a)) as [γp Hγp].
      { rewrite elem_of_gmap_dom -HMMρ -elem_of_gmap_dom. eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). rewrite HMρa in Hρ'. congruence. }
    iPureIntro. intros. split; eauto.
  Qed.

  Lemma full_sts_static_all W m (l : Addr) :
    (std W) !! l = Some (Static m) →
    sts_full_world W -∗
    region W -∗
    ⌜forall a, a ∈ dom (gset Addr) m -> static W m a⌝.
  Proof. 
    iIntros (Hstatic) "Hsts Hr".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom1 & #Hdom2 & Hr)".
    iDestruct "Hdom1" as %Hdom1. iDestruct "Hdom2" as %Hdom2.
    iDestruct (full_sts_Mρ_agree _ _ _ (Static m) with "Hsts Hr") as %[Hag _]; auto.
    pose proof (Hag Hstatic) as Hl. 
    iIntros (a Hdom).
    assert (is_Some (M !! l)) as [γp Hsome].
    { apply elem_of_gmap_dom. rewrite -Hdom1. apply elem_of_gmap_dom. eauto. }
    rewrite /region_map_def.
    iDestruct (big_sepM_delete _ _ l with "Hr") as "[Hl Hr]";[eauto|].
    iDestruct "Hl" as (ρ Hρ) "(Hstate & Hρ)".
    rewrite Hl in Hρ. inversion Hρ.
    iDestruct "Hρ" as (γpred p φ Hpv Hpers) "(#Hsaved & Hl)".
    iDestruct "Hl" as (p' v Hpv' Hne') "[Hl #Hall]". iDestruct "Hall" as %Hall.
    iDestruct (big_sepM_delete _ _ l with "[$Hr Hl Hstate]") as "Hr";[eauto|..].
    { iExists ρ. iSplitR;subst;auto. iFrame. iExists _,_,_. repeat iSplit;eauto. iExists _,_. iFrame. auto. }
    iDestruct (full_sts_Mρ_agree _ _ _ (Static m) with "Hsts Hr") as %[_ Hag']; auto.
    iPureIntro.
    rewrite /static.
    pose proof (Hall _ Hdom) as Ha. rewrite /std in Hag'. 
    pose proof (Hag' Ha) as ->. auto. 
  Qed.

  (* Closing the region without updating the sts collection *)
  Lemma region_close_temp_pwl W l φ p v `{forall Wv, Persistent (φ Wv)} :
    pwl p = true →
    sts_state_std l Temporary
                  ∗ open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_pub_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonstatic Temporary with "Hpreds") as "Hpreds". by congruence.
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Temporary. iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    iFrame. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    iExists _, _. rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close_temp_nwl W l φ p v `{forall Wv, Persistent (φ Wv)} :
    pwl p = false →
    sts_state_std l Temporary
                  ∗ open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonstatic Temporary with "Hpreds") as "Hpreds". by congruence.
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Temporary. iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    iExists _,_. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close_perm W l φ p v `{forall Wv, Persistent (φ Wv)}:
    sts_state_std l Permanent
                  ∗ open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.

    iDestruct (region_map_insert_nonstatic Permanent with "Hpreds") as "Hpreds". by congruence.
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Permanent. iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,_,_. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    iExists _,_. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq. 
    rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close W l φ p v (ρ : region_type) `{forall Wv, Persistent (φ Wv)} :
    ρ = Temporary ∨ ρ = Permanent →
    sts_state_std l ρ
                  ∗ open_region l W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗
                  (if (decide (ρ = Temporary ∧ pwl p = true))
                   then future_pub_mono φ v
                   else future_priv_mono φ v) ∗ ▷ φ (W,v) ∗ rel l p φ
    -∗ region W.
  Proof.
    iIntros (Htp) "(Hstate & Hreg_open & Hl & Hp & Hmono & Hφ & Hrel)".
    destruct ρ; try (destruct Htp; exfalso; congruence).
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

  Lemma delete_list_permutation {A B} `{Countable A, EqDecision A}
        (l1 l2: list A) (m: gmap A B):
    l1 ≡ₚ l2 → delete_list l1 m = delete_list l2 m.
  Proof.
    induction 1.
    { reflexivity. }
    { cbn. rewrite IHPermutation //. }
    { cbn. rewrite delete_commute //. }
    { rewrite IHPermutation1 //. }
  Qed.

  Definition open_region_many_def (l : list Addr) (W : WORLD) : iProp Σ :=
    (∃ M Mρ, RELS M ∗ ⌜dom (gset Addr) (std W) = dom (gset Addr) M⌝
                    ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝
                    ∗ region_map_def (delete_list l M) (delete_list l Mρ) W)%I.
  Definition open_region_many_aux : { x | x = @open_region_many_def }. by eexists. Qed.
  Definition open_region_many := proj1_sig open_region_many_aux.
  Definition open_region_many_eq : @open_region_many = @open_region_many_def := proj2_sig open_region_many_aux.

  Lemma open_region_many_monotone l W W':
    dom (gset Addr) (std W) = dom (gset Addr) (std W') →
    related_sts_pub_world W W' →
    (open_region_many l W -∗ open_region_many l W')%I.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite open_region_many_eq /open_region_many_def.
    iDestruct "HW" as (M Mρ) "(Hm & % & % & Hmap)". iExists M, Mρ. iFrame.
    iSplitR;[iPureIntro;congruence|]. 
    iSplitR; auto.
    iApply region_map_monotone; eauto.
  Qed.

  Lemma open_region_many_permutation l1 l2 W:
    l1 ≡ₚ l2 → (open_region_many l1 W -∗ open_region_many l2 W)%I.
  Proof.
    intros Hperm.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros "H". iDestruct "H" as (? ?) "(? & % & % & ?)".
    rewrite !(delete_list_permutation l1 l2) //. iExists _,_. iFrame. eauto.
  Qed.

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
    (std W) !! l = Some Temporary ->
    pwl p = true →
    open_region_many ls W ∗ rel l p φ ∗ sts_full_world W -∗
                     ∃ v, open_region_many (l :: ls) W
                        ∗ sts_full_world W
                        ∗ sts_state_std l Temporary
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
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & Hmono & Hφv)".    
    inversion HH; subst. rewrite Hpwl. iDestruct "Hmono" as "#Hmono".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv".
    - iExists _,_. repeat (rewrite -HMeq). iFrame "∗ #".
      do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. by congruence.
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
    (std W) !! l = Some Temporary ->
    pwl p = false →
    open_region_many ls W ∗ rel l p φ ∗ sts_full_world W -∗
                     ∃ v, open_region_many (l :: ls) W
                        ∗ sts_full_world W
                        ∗ sts_state_std l Temporary
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
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & Hmono & Hφv)".    
    inversion HH; subst. rewrite Hpwl. iDestruct "Hmono" as "#Hmono".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv". 
    - iExists _,_. repeat (rewrite -HMeq). iFrame "∗ #".
      do 2 (iSplitR; eauto). iApply region_map_delete_nonstatic; auto.
      by congruence.
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
    l ∉ ls → (std W) !! l = Some Permanent -> 
    open_region_many ls W ∗ rel l p φ ∗ sts_full_world W -∗
                     ∃ v, sts_full_world W
                        ∗ sts_state_std l Permanent
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
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto. 
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. 
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #Hmono & Hφv)".    
    inversion HH; subst.
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv". 
    - rewrite /open_region.
      iExists _,_. repeat (rewrite -HMeq). iFrame "∗ #". do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. by congruence.
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

  Lemma region_close_next_temp_pwl W φ ls l p v `{forall Wv, Persistent (φ Wv)} :
    l ∉ ls ->
    pwl p = true →
    sts_state_std l Temporary ∗
                  open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_pub_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
                  -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonstatic Temporary with "Hpreds") as "Hpreds". congruence.
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    rewrite -(delete_list_delete _ M) //.
    rewrite -(delete_list_insert _ (delete l M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists (<[l:=(γpred,p) ]> (delete l M)), (<[l:=Temporary]> Mρ). iFrame.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close_next_temp_nwl W φ ls l p v `{forall Wv, Persistent (φ Wv)} :
    l ∉ ls ->
    pwl p = false →
    sts_state_std l Temporary ∗
                  open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
                  -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonstatic Temporary with "Hpreds") as "Hpreds". congruence.
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    rewrite -(delete_list_delete _ M) // -(delete_list_insert _ (delete l M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists _, _. iFrame.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; auto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close_next_perm W φ ls l p v `{forall Wv, Persistent (φ Wv)} :
    l ∉ ls ->
    sts_state_std l Permanent ∗
                  open_region_many (l::ls) W ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l p φ
                  -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def. 
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonstatic Permanent with "Hpreds") as "Hpreds". congruence.
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,_,_. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    rewrite -(delete_list_delete _ M) // -(delete_list_insert _ (delete _ M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists _, _. iFrame.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; auto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Definition monotonicity_guarantees_region ρ w p φ :=
    (match ρ with
     | Temporary => if pwl p then future_pub_mono else future_priv_mono
     | Permanent => future_priv_mono
     | Revoked => λ (_ : WORLD * Word → iProp Σ) (_ : Word), True
     | Static _ => λ (_ :WORLD * Word → iProp Σ) (_ : Word), True
     end φ w)%I.

  Definition monotonicity_guarantees_decide ρ w p φ:=
    (if decide (ρ = Temporary ∧ pwl p = true)
     then future_pub_mono φ w
     else future_priv_mono φ w)%I.

   Lemma region_open_next
        (W : WORLD)
        (φ : WORLD * Word → iProp Σ)
        (ls : list Addr) (l : Addr) (p : Perm) (ρ : region_type)
        (Hρnotrevoked : ρ <> Revoked) (Hρnotstatic : ¬ exists g, ρ = Static g):
    l ∉ ls
    → std W !! l = Some ρ
    → open_region_many ls W ∗ rel l p φ ∗ sts_full_world W
                       -∗ ∃ v : Word,
        sts_full_world W
                       ∗ sts_state_std l ρ
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
    - exfalso. apply Hρnotstatic. eauto. 
  Qed.

  Lemma region_close_next
        (W : WORLD)
        (φ : WORLD * Word → iProp Σ)
        `{forall Wv, Persistent (φ Wv)}
        (ls : list Addr) (l : Addr) (p : Perm) (v : Word) (ρ : region_type)
        (Hρnotrevoked : ρ <> Revoked) (Hρnotstatic : ¬ exists g, ρ = Static g):
    l ∉ ls
    → sts_state_std l ρ
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
    - exfalso. apply Hρnotstatic. eauto. 
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT STD TRANSITIONS -------------------------- *)
  
  (*Lemma full_sts_world_is_Some_rel_std W (a : Addr) :
    is_Some ((std_sta W) !! (encode a)) →
    sts_full_world sts_std W -∗ ⌜rel_is_std_i W (encode a)⌝.
  Proof. 
    iIntros (Hsome) "[[% [% _] ] _]".
    iPureIntro. apply elem_of_subseteq in H3.
    apply elem_of_gmap_dom in Hsome. 
    specialize (H3 _ Hsome).
    specialize (H4 (encode a)). apply H4.
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

  (* If a full private future world of W is standard, then W is standard *)
  Lemma sts_full_world_priv_std W W' :
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

  Lemma sts_full_world_std W :
    sts_full_world sts_std W -∗ ⌜rel_is_std W⌝.
  Proof.
    iIntros. iApply sts_full_world_priv_std; eauto. iPureIntro.
    apply related_sts_priv_world_refl.
  Qed.*)

  Lemma std_rel_pub_Permanent x :
    std_rel_pub Permanent x → x = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_rtc_Permanent x y :
    x = Permanent →
    rtc std_rel_pub x y → y = Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply std_rel_pub_Permanent in H.
    apply IHHrtc. auto.
  Qed.

  Lemma std_rel_priv_Permanent x :
    std_rel_priv Permanent x → x = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel; done. 
  Qed.

  Lemma std_rel_priv_rtc_Permanent x y :
    x = Permanent →
    rtc std_rel_priv x y → y = Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply std_rel_priv_Permanent in H.
    apply IHHrtc. auto.
  Qed.

  Lemma std_rel_rtc_Permanent x y :
    x = Permanent →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_priv x0 y0) x y →
    y = Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc as [|x y z Hrel];auto.
    subst. destruct Hrel as [Hrel | Hrel].
    - apply std_rel_pub_Permanent in Hrel. auto.
    - apply std_rel_priv_Permanent in Hrel. auto. 
  Qed. 
      
  Lemma std_rel_pub_Temporary x :
    std_rel_pub Temporary x → x = Temporary.
  Proof.
    intros Hrel.
    inversion Hrel. 
  Qed.

  Lemma std_rel_pub_rtc_Temporary x y :
    x = Temporary →
    rtc std_rel_pub x y → y = Temporary.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply std_rel_pub_Temporary in H.
    apply IHHrtc. auto.
  Qed.

  Lemma std_rel_pub_Revoked x :
    std_rel_pub Revoked x → x = Temporary (* ∨ x = countable.encode Revoked *).
  Proof.
    intros Hrel.
    inversion Hrel. auto. 
  Qed.

  Lemma std_rel_pub_rtc_Revoked x y :
    x = Revoked →
    rtc std_rel_pub x y → y = Temporary ∨ y = Revoked.
  Proof.
    intros Hx Hrtc.
    inversion Hrtc; subst; auto. 
    apply std_rel_pub_Revoked in H. subst. 
    apply std_rel_pub_rtc_Temporary in H0; auto. 
  Qed. 

  (* Lemma std_rel_exist x y : *)
  (*   (∃ (ρ : region_type), countable.encode ρ = x) →  *)
  (*   rtc (λ x0 y0 : positive, convert_rel std_rel_pub x0 y0 ∨ convert_rel std_rel_priv x0 y0) x y → *)
  (*   ∃ (ρ : region_type), y = countable.encode ρ.  *)
  (* Proof. *)
  (*   intros Hsome Hrel. *)
  (*   induction Hrel; [destruct Hsome as [ρ Hsome]; eauto|]. *)
  (*   destruct H3 as [Hpub | Hpriv]. *)
  (*   - inversion Hpub as [ρ [ρ' [Heq1 [Heq2 Hsome'] ] ] ]. *)
  (*     apply IHHrel. eauto. *)
  (*   - inversion Hpriv as [ρ [ρ' [Heq1 [Heq2 Hsome'] ] ] ]. *)
  (*     apply IHHrel. eauto. *)
  (* Qed. *)

  Lemma std_rel_pub_Static x g :
    std_rel_pub (Static g) x → x = Temporary (* ∨ x = encode Revoked *).
  Proof.
    intros Hrel.
    inversion Hrel. auto. 
  Qed.

  Lemma std_rel_pub_rtc_Static x y g :
    x = (Static g) →
    rtc std_rel_pub x y → y = Temporary ∨ y = (Static g).
  Proof.
    intros Hx Hrtc.
    inversion Hrtc; subst; auto. 
    apply std_rel_pub_Static in H. subst. 
    apply std_rel_pub_rtc_Temporary in H0; auto. 
  Qed. 
  
End heap.

Notation "<s[ a := ρ ]s> W" := (std_update W a ρ) (at level 10, format "<s[ a := ρ ]s> W").
Notation "<l[ a := ρ , r ]l> W" := (loc_update W a ρ r.1 r.2) (at level 10, format "<l[ a := ρ , r ]l> W").
