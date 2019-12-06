From iris.algebra Require Import auth agree gmap excl.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import tactics.
Import uPred.


(** The CMRA for the heap of STS.
    We register the state and the transition relation. *)
Definition sts_stateUR := authUR (gmapUR positive (exclR (leibnizO positive))).

Definition sts_relUR :=
  authUR (gmapUR positive (agreeR (leibnizO ((positive → positive → Prop) * (positive → positive → Prop))))).

Definition STS_states : Type := gmap positive positive.
Definition STS_rels : Type := gmap positive ((positive → positive → Prop) * (positive → positive → Prop)).

(** The CMRA for the thread pool. *)
Class STSG Σ :=
  { sts_state_inG :> inG Σ sts_stateUR;
    sts_rel_inG :> inG Σ sts_relUR;
    γs_std : gname;
    γs_loc : gname;
    γr_std : gname;
    γr_loc : gname;}.

Class STS_STD A :=
  { Rpub : relation A;
    Rpriv : relation A;}. 

Section definitionsS.
  Context `{STSG Σ} `{Countable A}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (prodO STS STS). 
  Implicit Types W : WORLD.

  Definition sts_state_std (i : positive) (x : A) : iProp Σ
    := own (A := sts_stateUR) γs_std (◯ {[ i := Excl (encode x) ]}).

  Definition sts_state_loc (i : positive) (x : A) : iProp Σ
    := own (A := sts_stateUR) γs_loc (◯ {[ i := Excl (encode x) ]}).

  Definition convert_rel (R : A → A → Prop) : positive → positive → Prop :=
    λ x y, ∃ a b, x = encode a ∧ y = encode b ∧ R a b.

  (* for the standard map we will only have the standard sts *)
  Definition sts_rel_std (sts_std : STS_STD A) (i : positive) : iProp Σ :=
    own (A := sts_relUR) γr_std (◯ {[ i := to_agree ((convert_rel Rpub,convert_rel Rpriv)) ]}).
  
  Definition sts_rel_loc (i : positive) (R : A → A → Prop) (P : A → A → Prop) : iProp Σ :=
    own (A := sts_relUR) γr_loc (◯ {[ i := to_agree ((convert_rel R,convert_rel P)) ]}).

  Definition sts_subset (fr : STS_rels) : Prop :=
    ∀ i (r r' : positive → positive → Prop),
      fr !! i = Some (r,r') → (∀ a b, r a b → r' a b). 

  Program Definition sts_full `{STSG Σ} γs γr (fs : STS_states) (fr : STS_rels) : iProp Σ
    := (own (A := sts_stateUR) γs (● (Excl <$> fs))
            ∗ own (A := sts_relUR) γr (● (to_agree <$> fr)))%I.
  Program Definition sts_full_std `{STSG Σ} (sts_std : STS_STD A) γs γr (fs : STS_states) (fr : STS_rels) : iProp Σ
    := (⌜dom (gset positive) fs ⊆ dom (gset positive) fr⌝
       ∗ ⌜∀ i, is_Some(fr !! i) → fr !! i = Some (convert_rel Rpub,convert_rel Rpriv)⌝
       ∗ own (A := sts_stateUR) γs (● (Excl <$> fs))
       ∗ own (A := sts_relUR) γr (● (to_agree <$> fr)))%I.
  Program Definition sts_full_world `{STSG Σ} (sts_std : STS_STD A) W : iProp Σ :=
    ((sts_full_std sts_std γs_std γr_std W.1.1 W.1.2) ∗ (sts_full γs_loc γr_loc W.2.1 W.2.2))%I. 

  Definition related_sts_pub (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom (gset positive) fs ⊆ dom (gset positive) gs ∧
    dom (gset positive) fr ⊆ dom (gset positive) gr ∧
    ∀ i r1 r2 r1' r2', fr !! i = Some (r1,r2) → gr !! i = Some (r1',r2') →
                       r1 = r1' ∧ r2 = r2' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → rtc r1 x y).

  Definition related_sts_priv (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom (gset positive) fs ⊆ dom (gset positive) gs ∧
    dom (gset positive) fr ⊆ dom (gset positive) gr ∧
    ∀ i r1 r2 r1' r2', fr !! i = Some (r1,r2) → gr !! i = Some (r1',r2') →
                       r1 = r1' ∧ r2 = r2' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → (rtc (λ x y, (r1 x y ∨ r2 x y)) x y)).

  Definition related_sts_pub_world W W' :=
    related_sts_pub W.1.1 W'.1.1 W.1.2 W'.1.2 ∧
    related_sts_pub W.2.1 W'.2.1 W.2.2 W'.2.2.

  Definition related_sts_priv_world W W' :=
    related_sts_priv W.1.1 W'.1.1 W.1.2 W'.1.2 ∧
    related_sts_priv W.2.1 W'.2.1 W.2.2 W'.2.2.

  Global Instance sts_rel_std_Persistent i sts_stg : Persistent (sts_rel_std sts_stg i).
  Proof. apply _. Qed.
  Global Instance sts_rel_loc_Persistent i R P : Persistent (sts_rel_loc i R P).
  Proof. apply _. Qed.
  
  Global Instance sts_rel_std_Timeless i sts_stg : Timeless (sts_rel_std sts_stg i).
  Proof. apply _. Qed.
  Global Instance sts_rel_loc_Timeless i R P : Timeless (sts_rel_loc i R P).
  Proof. apply _. Qed.
  
  Global Instance sts_state_std_Timeless i x : Timeless (sts_state_std i x).
  Proof. apply _. Qed.
  Global Instance sts_state_loc_Timeless i x : Timeless (sts_state_loc i x).
  Proof. apply _. Qed.
  
  Global Instance sts_full_Timeless γs γr fs fr : Timeless (sts_full γs γr fs fr).
  Proof. apply _. Qed.
  Global Instance sts_full_world_Timeless sts_stg W : Timeless (sts_full_world sts_stg W). 
  Proof. apply _. Qed. 
  
End definitionsS.

Typeclasses Opaque sts_state_std sts_state_loc sts_rel_std sts_rel_loc sts_full
            related_sts_pub related_sts_priv.

Lemma rtc_implies {A : Type} (R Q : A → A → Prop) (x y : A) :
  (∀ r q, R r q → Q r q) →
  rtc R x y → rtc Q x y.
Proof.
  intros Himpl HR.
  induction HR.
  - done.
  - apply Himpl in H.
    apply rtc_once in H. 
    apply rtc_transitive with y; auto.
Qed.

Lemma rtc_or_intro {A : Type} (R Q : A → A → Prop) (x y : A) :
  rtc (λ a b, R a b) x y →
  rtc (λ a b, R a b ∨ Q a b) x y.
Proof.
  intros HR. induction HR.
  - done.
  - apply rtc_transitive with y; auto. 
    apply rtc_once. by left.
Qed. 

Lemma rtc_or_intro_l {A : Type} (R Q : A → A → Prop) (x y : A) :
    rtc (λ a b, R a b) x y →
    rtc (λ a b, Q a b ∨ R a b) x y.
  Proof.
    intros HR. induction HR.
    - done.
    - apply rtc_transitive with y; auto.
      apply rtc_once. by right.
  Qed.
    
Section STS.
  Context `{STSG Σ} `{Countable A} `{sts_std : STS_STD A}.
  Implicit Types x y : positive.
  Implicit Types a b : A.
  Implicit Types fs gs : STS_states.
  Implicit Types fr_pub fr_priv gr_pub gr_priv : STS_rels.
  Implicit Types R Q : A → A → Prop.
  Implicit Types Rp : positive → positive → Prop.

  Lemma elem_of_gmap_dom {K V : Type} `{EqDecision K} `{Countable K}
        (m : gmap K V) (i : K) :
    is_Some (m !! i) ↔ i ∈ dom (gset K) m.  
  Proof.
    split.
    - intros [x Hsome].
      apply elem_of_dom. eauto.
    - intros Hin.
      by apply elem_of_dom in Hin. 
  Qed. 
      
  Lemma related_sts_pub_refl fs fr : related_sts_pub fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; trivial.
    intros; simplify_eq; eauto using rtc_refl.
  Qed.

  Lemma related_sts_priv_refl fs fr : related_sts_priv fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; trivial.
    intros; simplify_eq;
    eauto using rtc_refl.
  Qed.

  Lemma related_sts_pub_priv fs fr gs gr :
    related_sts_pub fs gs fr gr → related_sts_priv fs gs fr gr.
  Proof.
    rewrite /related_sts_pub /related_sts_priv. 
    intros [Hf1 [Hf2 Hf3]].
    do 2 (split; auto). intros. 
    specialize (Hf3 i r1 r2 r1' r2' H1 H2) as (Hr1 & Hr2 & Hrtc); auto.
    subst. repeat (split;auto). intros.
    specialize (Hrtc x y H3 H4). 
    inversion Hrtc.
    - left.
    - right with y0; auto.
      apply rtc_or_intro. apply H6.
  Qed. 

  Lemma related_sts_pub_trans fs fr gs gr hs hr :
    related_sts_pub fs gs fr gr → related_sts_pub gs hs gr hr →
    related_sts_pub fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [x1 x2].
    edestruct Hf3 as [Heq1 [Heq2 Hrtc] ] ; eauto; simplify_eq. 
    edestruct Hg3 as [Heq1 [Heq2 Hrtc'] ] ; eauto; simplify_eq. 
    repeat (split;auto).
    intros x y Hx Hy. 
    destruct Hf1;eauto.
    etrans;eauto. 
  Qed.
  
  Lemma related_sts_priv_pub_trans fs fr gs gr hs hr :
    related_sts_priv fs gs fr gr → related_sts_pub gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [x1 x2].
    edestruct Hf3 as [Heq1 [Heq2 Hrtc] ] ; eauto; simplify_eq. 
    edestruct Hg3 as [Heq1 [Heq2 Hrtc'] ] ; eauto; simplify_eq. 
    repeat (split;auto).
    intros x y Hx Hy. 
    destruct Hf1;eauto.
    etrans;eauto. 
    apply rtc_or_intro; auto. 
  Qed.

  Lemma related_sts_pub_priv_trans fs fr gs gr hs hr :
    related_sts_pub fs gs fr gr → related_sts_priv gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [x1 x2].
    edestruct Hf3 as [Heq1 [Heq2 Hrtc] ] ; eauto; simplify_eq. 
    edestruct Hg3 as [Heq1 [Heq2 Hrtc'] ] ; eauto; simplify_eq. 
    repeat (split;auto).
    intros x y Hx Hy. 
    destruct Hf1;eauto.
    etrans;eauto. 
    apply rtc_or_intro; auto. 
  Qed.

  Lemma related_sts_priv_trans fs fr gs gr hs hr :
    related_sts_priv fs gs fr gr → related_sts_priv gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [x1 x2].
    edestruct Hf3 as [Heq1 [Heq2 Hrtc] ] ; eauto; simplify_eq. 
    edestruct Hg3 as [Heq1 [Heq2 Hrtc'] ] ; eauto; simplify_eq. 
    repeat (split;auto).
    intros x y Hx Hy. 
    destruct Hf1;eauto.
    etrans;eauto. 
  Qed.

  (* Helper functions for transitivity of sts pairs *)
  Lemma related_sts_pub_priv_trans_world W W' W'' :
    related_sts_pub_world W W' -> related_sts_priv_world W' W'' ->
    related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split. 
    - apply related_sts_pub_priv_trans with W'.1.1 W'.1.2; auto.
    - apply related_sts_pub_priv_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_priv_pub_trans_world W W' W'' :
    related_sts_priv_world W W' -> related_sts_pub_world W' W'' ->
    related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split. 
    - apply related_sts_priv_pub_trans with W'.1.1 W'.1.2; auto.
    - apply related_sts_priv_pub_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_priv_trans_world W W' W'' :
    related_sts_priv_world W W' -> related_sts_priv_world W' W'' ->
    related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split. 
    - apply related_sts_priv_trans with W'.1.1 W'.1.2; auto.
    - apply related_sts_priv_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_pub_trans_world W W' W'' :
    related_sts_pub_world W W' -> related_sts_pub_world W' W'' ->
    related_sts_pub_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split. 
    - apply related_sts_pub_trans with W'.1.1 W'.1.2; auto.
    - apply related_sts_pub_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_pub_priv_world W W' :
    related_sts_pub_world W W' -> related_sts_priv_world W W'.
  Proof.
    intros [Hstd Hloc].
    split; apply related_sts_pub_priv; auto.
  Qed.

  Lemma sts_full_rel_std W (i : positive) :
    (sts_full_world sts_std W -∗ sts_rel_std sts_std i -∗
                    ⌜W.1.2 !! i = Some (convert_rel (Rpub : relation A), convert_rel (Rpriv : relation A))⌝)%I.
  Proof.
    rewrite /sts_rel_std /sts_full_world /sts_full.
    destruct W as [[fs fr] Wloc].
    (* iIntros "[% [_ H1]] H2". *)
    iIntros "[[_ [% [_ H1]]] _] H2 /=".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid;
      iPureIntro.
    specialize (Hv i).
    revert HR. rewrite /= singleton_included;
      intros [z [Hz HR]]; revert HR; rewrite Some_included_total; intros HR.
    rewrite lookup_fmap in Hz, Hv.
    destruct (fr !! i) eqn:Heq; rewrite Heq /= in Hz, Hv; last by inversion Hz.
    revert Hv; rewrite Hz; intros [u Hu]%to_agree_uninj.
    revert HR; rewrite -Hu; intros HR%to_agree_included%leibniz_equiv;
      simplify_eq.
    inversion Hz as [? ? Hz'|]; simplify_eq.
    revert Hz'; rewrite -Hu. intros Hz'%(to_agree_inj (A:=leibnizO _) p _)%leibniz_equiv. 
    by rewrite Hz'.  
  Qed.

  Lemma sts_full_rel_loc W i R P :
    sts_full_world sts_std W -∗ sts_rel_loc i R P -∗ ⌜W.2.2 !! i = Some (convert_rel R,convert_rel P)⌝.
  Proof.
    rewrite /sts_rel_loc /sts_full_world /sts_full.
    destruct W as [Wstd [fs fr]].
    (* iIntros "[% [_ H1]] H2". *)
    iIntros "[_ [_ H1]] H2 /=".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid;
      iPureIntro.
    specialize (Hv i).
    revert HR. rewrite /= singleton_included;
      intros [z [Hz HR]]; revert HR; rewrite Some_included_total; intros HR.
    rewrite lookup_fmap in Hz, Hv.
    destruct (fr !! i) eqn:Heq; rewrite Heq /= in Hz, Hv; last by inversion Hz.
    revert Hv; rewrite Hz; intros [u Hu]%to_agree_uninj.
    revert HR; rewrite -Hu; intros HR%to_agree_included%leibniz_equiv;
      simplify_eq.
    inversion Hz as [? ? Hz'|]; simplify_eq.
    revert Hz'; rewrite -Hu. intros Hz'%(to_agree_inj (A:=leibnizO _) p _)%leibniz_equiv. 
    by rewrite Hz'.  
  Qed.
      
  Lemma sts_full_state_std W i a :
    sts_full_world sts_std W -∗ sts_state_std i a -∗ ⌜W.1.1 !! i = Some (encode a)⌝.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std.
    (* iIntros "[% [H1 _]] H2". *)
    destruct W as [[fs fr] Wloc]. 
    iIntros "[[_ [_ [H1 _] ] ] _] H2". 
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= singleton_included;
      intros [z [Hz HR]].
    rewrite lookup_fmap in Hz Hv.
    destruct (fs !! i) eqn:Heq; rewrite Heq /= in Hz Hv; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
  Qed.

  Lemma sts_full_state_loc W i a :
    sts_full_world sts_std W -∗ sts_state_loc i a -∗ ⌜W.2.1 !! i = Some (encode a)⌝.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_loc.
    (* iIntros "[% [H1 _]] H2". *)
    destruct W as [Wstd [fs fr] ]. 
    iIntros "[_ [H1 _]] H2". 
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= singleton_included;
      intros [z [Hz HR]].
    rewrite lookup_fmap in Hz Hv.
    destruct (fs !! i) eqn:Heq; rewrite Heq /= in Hz Hv; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
  Qed.

  Lemma sts_dealloc_std W i a :
    sts_full_world sts_std W ∗ sts_state_std i a ==∗ sts_full_world sts_std (delete i W.1.1,W.1.2,W.2). 
  Proof.
    rewrite /sts_full_world /sts_full /sts_rel_std /sts_state_std.
    destruct W as [[fs fr] Wloc]. 
    iIntros "[ [[% [% [H1 H2] ] ] Hloc] Hstate] /=".
    iCombine "H1" "Hstate" as "H1". 
    iMod (own_update
            (A := sts_stateUR)
            _ _
            (● (Excl <$> (delete i fs)))
            with "H1") as "H1".
    { apply auth_update_dealloc.
      rewrite fmap_delete /=.
      apply: delete_singleton_local_update. }
    iFrame. iModIntro. iPureIntro. split; auto.
    etrans;[|eauto].
    simpl. rewrite dom_delete_L.
    by apply subseteq_difference_l. 
  Qed. 
    
  Lemma sts_alloc_std W a :
    sts_full_world sts_std W ==∗
             ∃ i, sts_full_world sts_std (((<[i := encode a ]>W.1.1),(<[i := (convert_rel (Rpub : relation A),convert_rel (Rpriv : relation A)) ]>W.1.2)),W.2)
                  ∗ ⌜i ∉ dom (gset positive) W.1.1⌝ ∗ ⌜i ∉ dom (gset positive) W.1.2⌝
                  ∗ sts_state_std i a ∗ sts_rel_std sts_std i.
  Proof.
    rewrite /sts_full_world /sts_full /sts_rel_std /sts_state_std.
    (* iIntros "[Hd [H1 H2]]". *)
    (* iDestruct "Hd" as %Hd. *)
    destruct W as [[fs fr] Wloc]. 
    iIntros "[[% [% [H1 H2] ] ] Hloc] /=".
    assert (fresh (dom (gset positive) fs ∪ dom (gset positive) fr) ∉
                    (dom (gset positive) fs ∪ dom (gset positive) fr)) as Hfresh.
    { apply is_fresh. }
    apply not_elem_of_union in Hfresh as [Hfs Hfr]. 
    iMod (own_update
            (A := sts_stateUR)
            _ _
            (● (Excl <$>
                <[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := encode a]> fs)
            ⋅ ◯ {[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := Excl (encode a)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    iMod (own_update
            (A := sts_relUR)
            _ _
            (● (to_agree <$>
                <[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := (convert_rel Rpub,convert_rel Rpriv)]> fr)
            ⋅ ◯ {[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := to_agree (convert_rel Rpub,convert_rel Rpriv)]})
            with "H2") as "[H2 Hr]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    iModIntro.
    iExists _; iFrame.
    repeat iSplit; auto.
    - iPureIntro. do 2 rewrite dom_insert_L.
      apply union_mono_l. auto. 
    - iPureIntro. intros i [x Hx].
      destruct (decide (fresh (dom (gset positive) fs ∪ dom (gset positive) fr) = i)).
      + subst. rewrite lookup_insert. auto.
      + rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne in Hx; auto.
        apply H2. eauto.       
  Qed.

  Lemma sts_alloc_std_i W i a :
    ⌜i ∉ dom (gset positive) W.1.1⌝ -∗ (* ⌜i ∉ dom (gset positive) W.1.2⌝ -∗ *)
    sts_full_world sts_std W ==∗
                    sts_full_world sts_std (((<[i := encode a ]>W.1.1),(<[i := (convert_rel (Rpub : relation A),convert_rel (Rpriv: relation A)) ]>W.1.2)),W.2)
                  ∗ sts_state_std i a.
  Proof.
    rewrite /sts_full_world /sts_full /sts_rel_std /sts_state_std /=.
    (* iIntros "[Hd [H1 H2]]". *)
    (* iDestruct "Hd" as %Hd. *)
    destruct W as [[fs fr] Wloc]. rewrite /sts_full_std. 
    iIntros (Hfresh1) "[[% [% [H1 H2] ] ] Hloc] /=".
    iMod (own_update
            (A := sts_stateUR)
            _ _
            (● (Excl <$>
                <[i := encode a]> fs)
            ⋅ ◯ {[i := Excl (encode a)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    destruct (decide (i ∈ dom (gset positive) fr)). 
    - (* i is already in the domain of fr. We know from sts_full_world that it must map to std_sts *)
      apply elem_of_dom,H2 in e.
      iFrame. iSplitR;[|iSplitR]. 
      + iModIntro. iPureIntro. do 2 rewrite dom_insert_L.
        apply union_mono_l. auto.
      + iPureIntro. intros i0 [x Hx].
        destruct (decide (i0 = i)).
        * subst. rewrite lookup_insert. auto.
        * rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne in Hx; auto.
          apply H2. eauto.
      + rewrite (insert_id fr i (convert_rel Rpub, convert_rel Rpriv)); auto.
    - iMod (own_update
            (A := sts_relUR)
            _ _
            (● (to_agree <$>
                <[i := (convert_rel Rpub,convert_rel Rpriv)]> fr)
            ⋅ ◯ {[i := to_agree (convert_rel Rpub,convert_rel Rpriv)]})
            with "H2") as "[H2 Hr]".
      { apply auth_update_alloc.
        rewrite fmap_insert /=.
        apply: alloc_singleton_local_update; last done.
        apply (not_elem_of_dom (D := gset positive)).
        rewrite dom_fmap.
        auto. }
      iModIntro. iFrame. iSplit. 
      + iPureIntro. do 2 rewrite dom_insert_L.
        apply union_mono_l. auto.
      + iPureIntro. intros i0 [x Hx].
      destruct (decide (i0 = i)).
        * subst. rewrite lookup_insert. auto.
        * rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne in Hx; auto.
          apply H2. eauto.
  Qed.

  Lemma sts_alloc_loc W a R P:
    sts_full_world sts_std W ==∗
             ∃ i, sts_full_world sts_std (W.1,((<[i := encode a ]>W.2.1),(<[i := (convert_rel R,convert_rel P) ]>W.2.2)))
                  ∗ ⌜i ∉ dom (gset positive) W.2.1⌝ ∗ ⌜i ∉ dom (gset positive) W.2.2⌝
                  ∗ sts_state_loc i a ∗ sts_rel_loc i R P.
  Proof.
    rewrite /sts_full_world /sts_full /sts_rel_loc /sts_state_loc.
    (* iIntros "[Hd [H1 H2]]". *)
    (* iDestruct "Hd" as %Hd. *)
    destruct W as [Wstd [fs fr]]. 
    iIntros "[Hstd [H1 H2]] /=".
    assert (fresh (dom (gset positive) fs ∪ dom (gset positive) fr) ∉
                    (dom (gset positive) fs ∪ dom (gset positive) fr)).
    { apply is_fresh. }
    apply not_elem_of_union in H1 as [Hfs Hfr]. 
    iMod (own_update
            (A := sts_stateUR)
            _ _
            (● (Excl <$>
                <[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := encode a]> fs)
            ⋅ ◯ {[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := Excl (encode a)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    iMod (own_update
            (A := sts_relUR)
            _ _
            (● (to_agree <$>
                <[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := (convert_rel R,convert_rel P)]> fr)
            ⋅ ◯ {[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := to_agree (convert_rel R,convert_rel P)]})
            with "H2") as "[H2 Hr]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    iModIntro.
    iExists _; iFrame.
    repeat iSplit; auto. 
  Qed.

  Lemma sts_update_std W i a b :
    sts_full_world sts_std W -∗ sts_state_std i a ==∗
    sts_full_world sts_std (((<[i := encode b ]>W.1.1),W.1.2),W.2) ∗ sts_state_std i b.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_std with "Hsf Hi") as %Hfs.
    rewrite /sts_full_world /sts_full /sts_rel_std /sts_state_std.
    destruct W as [[fs fr] Wloc]. 
    iDestruct "Hsf" as "[[% [% [H1 H2] ] ] Hloc] /=".
    iCombine "H1" "Hi" as "H1".
    iMod (own_update (A := sts_stateUR)
            _ _
            (● (<[i := Excl (encode b)]> (Excl <$> fs))
               ⋅ ◯ {[i := Excl (encode b)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      rewrite lookup_fmap Hfs //=.
      by apply exclusive_local_update. }
    iFrame. rewrite fmap_insert (* dom_insert_L *) (* subseteq_union_1_L *);
              first iModIntro; iFrame.  iSplit;auto.
    iPureIntro.
    rewrite dom_insert_L. rewrite subseteq_union_1_L; auto.
    apply elem_of_subseteq_singleton. apply elem_of_gmap_dom. eauto. 
  Qed.

  Lemma sts_update_loc W i a b :
    sts_full_world sts_std W -∗ sts_state_loc i a ==∗
    sts_full_world sts_std (W.1,((<[i := encode b ]>W.2.1),W.2.2)) ∗ sts_state_loc i b.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_loc with "Hsf Hi") as %Hfs.
    rewrite /sts_full_world /sts_full /sts_rel_loc /sts_state_loc.
    destruct W as [Wstd [fs fr]]. 
    iDestruct "Hsf" as "[Hdst [H1 H2]] /=".
    iCombine "H1" "Hi" as "H1".
    iMod (own_update (A := sts_stateUR)
            _ _
            (● (<[i := Excl (encode b)]> (Excl <$> fs))
               ⋅ ◯ {[i := Excl (encode b)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      rewrite lookup_fmap Hfs //=.
      by apply exclusive_local_update. }
    rewrite fmap_insert (* dom_insert_L *) (* subseteq_union_1_L *);
      first iModIntro; iFrame.
  Qed.

End STS.
