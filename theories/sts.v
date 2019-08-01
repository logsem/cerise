From iris.algebra Require Import auth agree gmap.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import tactics.
Import uPred.


(** The CMRA for the heap of STS.
    We register the state and the transition relation. *)
Definition sts_stateUR := authUR (gmapUR positive (exclR (leibnizC positive))).

Definition sts_relUR :=
  authUR (gmapUR positive (agreeR (leibnizC (positive → positive → Prop)))).

Definition STS_states : Type := gmap positive positive.
Definition STS_rels : Type := gmap positive (positive → positive → Prop).

(** The CMRA for the thread pool. *)
Class STSG Σ :=
  { sts_state_inG :> inG Σ sts_stateUR;
    sts_rel_pub_inG :> inG Σ sts_relUR;
    sts_rel_priv_inG :> inG Σ sts_relUR;
    sts_state_name : gname;
    sts_rel_pub_name : gname;
    sts_rel_priv_name : gname; }.

Section definitionsS.
  Context `{STSG Σ} `{Countable A}.

  Definition sts_state (i : positive) (x : A) : iProp Σ
    := own (A := sts_stateUR) sts_state_name (◯ {[ i := Excl (encode x) ]}).

  Definition convert_rel (R : A → A → Prop) : positive → positive → Prop :=
    λ x y, ∃ a b, x = encode a ∧ y = encode b ∧ R a b.

  Definition sts_rel_pub (i : positive) (R : A → A → Prop) : iProp Σ :=
    own (A := sts_relUR) sts_rel_pub_name (◯ {[ i := to_agree (convert_rel R) ]}).

  Definition sts_rel_priv (i : positive) (R : A → A → Prop) : iProp Σ :=
    own (A := sts_relUR) sts_rel_priv_name (◯ {[ i := to_agree (convert_rel R) ]}).

  Definition sts_subset (fr_pub fr_priv : STS_rels) : Prop :=
    ∀ i (r_pub r_priv : positive → positive → Prop), fr_pub !! i = Some r_pub → fr_priv !! i = Some r_priv →
                      (∀ a b, r_pub a b → r_priv a b). 

  (* very weird bug!!!
     Any two of these conjuncts are ok on their own but not all three!
     But, it works with program!!!!!!!!!!! *)
  Program Definition sts_full `{STSG Σ} (fs : STS_states) (fr_pub fr_priv : STS_rels) : iProp Σ
    := ((⌜dom (gset positive) fs = dom (gset positive) fr_priv⌝ ∧ 
        ⌜dom (gset positive) fr_priv = dom (gset positive) fr_pub⌝)
        ∗ ⌜sts_subset fr_pub fr_priv⌝
        ∗ own (A := sts_stateUR) sts_state_name (● (Excl <$> fs))
        ∗ own (A := sts_relUR) sts_rel_pub_name (● (to_agree <$> fr_pub))
        ∗ own (A := sts_relUR) sts_rel_priv_name (● (to_agree <$> fr_priv)))%I.

  Definition related_sts (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom (gset positive) fs ⊆ dom (gset positive) gs ∧
    dom (gset positive) fr ⊆ dom (gset positive) gr ∧
    ∀ i x y r r', fs !! i = Some x → gs !! i = Some y →
                  fr !! i = Some r → gr !! i = Some r' → r = r' ∧ rtc r x y.

  Global Instance sts_rel_pub_Persistent i R : Persistent (sts_rel_pub i R).
  Proof. apply _. Qed.

  Global Instance sts_rel_priv_Persistent i R : Persistent (sts_rel_priv i R).
  Proof. apply _. Qed.

  Global Instance sts_rel_pub_Timeless i R : Timeless (sts_rel_pub i R).
  Proof. apply _. Qed.

  Global Instance sts_rel_priv_Timeless i R : Timeless (sts_rel_priv i R).
  Proof. apply _. Qed.

  Global Instance sts_state_Timeless i x : Timeless (sts_state i x).
  Proof. apply _. Qed.

  Global Instance sts_full_Timeless fs fr_pub fr_priv : Timeless (sts_full fs fr_pub fr_priv).
  Proof. apply _. Qed.

End definitionsS.

Typeclasses Opaque sts_state sts_rel_pub sts_rel_priv sts_full related_sts.

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

Section STS.
  Context `{STSG Σ} `{Countable A}.
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
      
  Lemma related_sts_refl fs fr : related_sts fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq; eauto using rtc_refl.
  Qed.

  Lemma related_sts_trans fs fr gs gr hs hr :
    related_sts fs gs fr gr → related_sts gs hs gr hr → related_sts fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i x y r r' Hfs Hhs Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf1; eauto; destruct Hf2; eauto.
    edestruct Hf3; eauto; edestruct Hg3; eauto; simplify_eq.
    split; etrans; eauto.
  Qed.

  Lemma sts_full_rel_priv fs fr_pub fr_priv i R :
    sts_full fs fr_pub fr_priv -∗ sts_rel_priv i R -∗ ⌜fr_priv !! i = Some (convert_rel R)⌝.
  Proof.
    rewrite /sts_full /sts_rel_priv.
    iIntros "[% [_ (_ & _ & H1)]] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= left_id singleton_included;
      intros [z [Hz HR]]; revert HR; rewrite Some_included_total; intros HR.
    rewrite lookup_fmap in Hz, Hv.
    destruct (fr_priv !! i) eqn:Heq; rewrite Heq /= in Hz, Hv; last by inversion Hz.
    revert Hv; rewrite Hz; intros [u Hu]%to_agree_uninj.
    revert HR; rewrite -Hu; intros HR%to_agree_included%leibniz_equiv;
      simplify_eq.
    inversion Hz as [? ? Hz'|]; simplify_eq.
    revert Hz'; rewrite -Hu; intros Hz'%to_agree_inj%leibniz_equiv; simplify_eq.
    by eauto.
  Qed.

   Lemma sts_full_rel_pub fs fr_pub fr_priv i R :
    sts_full fs fr_pub fr_priv -∗ sts_rel_pub i R -∗ ⌜fr_pub !! i = Some (convert_rel R)⌝.
  Proof.
    rewrite /sts_full /sts_rel_pub.
    iIntros "[% [_ (_ & H1 & _)]] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= left_id singleton_included;
      intros [z [Hz HR]]; revert HR; rewrite Some_included_total; intros HR.
    rewrite lookup_fmap in Hz, Hv.
    destruct (fr_pub !! i) eqn:Heq; rewrite Heq /= in Hz, Hv; last by inversion Hz.
    revert Hv; rewrite Hz; intros [u Hu]%to_agree_uninj.
    revert HR; rewrite -Hu; intros HR%to_agree_included%leibniz_equiv;
      simplify_eq.
    inversion Hz as [? ? Hz'|]; simplify_eq.
    revert Hz'; rewrite -Hu; intros Hz'%to_agree_inj%leibniz_equiv; simplify_eq.
    by eauto.
  Qed.

  Lemma sts_full_rel_pub_priv fs fr_pub fr_priv gs gr_pub gr_priv :
    sts_full fs fr_pub fr_priv -∗
    ⌜related_sts fs gs fr_pub gr_pub⌝ -∗
    sts_full gs gr_pub gr_priv -∗
    ⌜∀ i fi gi, fr_priv !! i = Some fi → gr_priv !! i = Some gi → fi = gi⌝ -∗
    ⌜related_sts fs gs fr_priv gr_priv⌝.
  Proof.
    iIntros "Hffull % Hgfull %". destruct a as (Hfs & Hfrpub & Hrel). 
    rename a0 into Hpriv. 
    rewrite /sts_full.
    iDestruct "Hgfull" as "([% %] & % & _ & _)".
    iDestruct "Hffull" as "([% %] & % & _ & _)".
    iPureIntro. 
    split; auto. split.
    - by rewrite H2 H5. 
    - intros i x y r_priv r_priv' Hfsi Hgsi Hfr_privi Hgr_privi.
      rewrite /sts_subset in H6, H3.
      assert (is_Some (gr_pub !! i)) as [gr_pub_i Hsomeg].
      { assert (i ∈ dom (gset positive) gr_priv); [apply elem_of_gmap_dom;eauto|]. 
        apply elem_of_gmap_dom. by rewrite -H2. }
      assert (is_Some (fr_pub !! i)) as [fr_pub_i Hsomef].
      { assert (i ∈ dom (gset positive) fr_priv); [apply elem_of_gmap_dom;eauto|]. 
        apply elem_of_gmap_dom. by rewrite -H5. }
      (* specialize H3 with i gr_pub_i r_priv' x y. *)
      (* specialize H6 with i gr_pub_i r_priv x y. *)
      assert (fr_pub_i = gr_pub_i ∧ rtc fr_pub_i x y) as [Hfrgrpub Hxy];
        [apply Hrel with i; auto|].
      assert (r_priv = r_priv');
        [apply Hpriv with i; auto|].
      split; auto.
      apply rtc_implies with gr_pub_i; try congruence.
        apply H3 with i; try congruence.  
  Qed. 
      
  Lemma sts_full_state fs fr_pub fr_priv i a :
    sts_full fs fr_pub fr_priv -∗ sts_state i a -∗ ⌜fs !! i = Some (encode a)⌝.
  Proof.
    rewrite /sts_full /sts_state.
    iIntros "[% [_ [H1 _]]] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= left_id singleton_included;
      intros [z [Hz HR]].
    rewrite lookup_fmap in Hz Hv.
    destruct (fs !! i) eqn:Heq; rewrite Heq /= in Hz Hv; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
  Qed.

  Lemma sts_alloc fs fr_pub fr_priv a R Q :
    (∀ x y, (convert_rel R) x y → (convert_rel Q) x y) →
    sts_full fs fr_pub fr_priv ==∗
             ∃ i, sts_full (<[i := encode a ]>fs) (<[i := convert_rel R ]>fr_pub)
                           (<[i := convert_rel Q ]>fr_priv)
                           ∗ ⌜i ∉ dom (gset positive) fs⌝
                           ∗ ⌜i ∉ dom (gset positive) fr_pub⌝
                           ∗ ⌜i ∉ dom (gset positive) fr_priv⌝
                  ∗ sts_state i a ∗ sts_rel_pub i R ∗ sts_rel_priv i Q.
  Proof.
    rewrite /sts_full /sts_rel_pub /sts_rel_priv /sts_state.
    iIntros (HRQ) "[Hd [% [H1 [H2 H2']]]]".
    iDestruct "Hd" as %[Hd Hd'].
    iMod (own_update
            (A := sts_stateUR)
            _ _
            (● (Excl <$>
                <[fresh (dom (gset positive) fs) := encode a]> fs)
            ⋅ ◯ {[fresh (dom (gset positive) fs) := Excl (encode a)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      apply is_fresh. }
    iMod (own_update
            (A := sts_relUR)
            _ _
            (● (to_agree <$>
                <[fresh (dom (gset positive) fs) := convert_rel R]> fr_pub)
            ⋅ ◯ {[fresh (dom (gset positive) fs) := to_agree (convert_rel R)]})
            with "H2") as "[H2 Hr]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap Hd Hd'.
      apply is_fresh. }
    iMod (own_update
            (A := sts_relUR)
            _ _
            (● (to_agree <$>
                <[fresh (dom (gset positive) fs) := convert_rel Q]> fr_priv)
            ⋅ ◯ {[fresh (dom (gset positive) fs) := to_agree (convert_rel Q)]})
            with "H2'") as "[H2' Hr']".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap Hd Hd'.
      apply is_fresh. }
    iModIntro.
    iExists _; iFrame.
    repeat iSplit; try iPureIntro;
      rewrite ?dom_insert_L ?Hd Hd'; try apply is_fresh; auto.
    rewrite /sts_subset.
    intros i r_pub r_priv Hpub Hpriv a' b' Ha'.
    destruct (decide (fresh (dom (gset positive) fr_pub) = i)).
    - rewrite e lookup_insert in Hpub, Hpriv. rewrite lookup_insert in Hpriv.
      inversion Hpub; inversion Hpriv.
      apply HRQ. congruence.
    - rewrite lookup_insert_ne in Hpub; auto.
      rewrite lookup_insert_ne in Hpriv; auto.
      rewrite /sts_subset in H1. apply H1 with i r_pub; auto. 
  Qed.

  Lemma sts_update fs fr_pub fr_priv i a b :
    sts_full fs fr_pub fr_priv -∗ sts_state i a ==∗
    sts_full (<[i := encode b ]>fs) fr_pub fr_priv ∗ sts_state i b.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state with "Hsf Hi") as %Hfs.
    rewrite /sts_full /sts_rel_pub /sts_rel_priv /sts_state.
    iDestruct "Hsf" as "[Hd [H1 [H2 [H3 H4]]]]".
    iDestruct "Hd" as %Hd.
    iCombine "H2" "Hi" as "H2".
    iMod (own_update (A := sts_stateUR)
            _ _
            (● (<[i := Excl (encode b)]> (Excl <$> fs))
               ⋅ ◯ {[i := Excl (encode b)]})
            with "H2") as "[H2 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      rewrite lookup_fmap Hfs //=.
      by apply exclusive_local_update. }
    rewrite fmap_insert dom_insert_L subseteq_union_1_L;
      first by iModIntro; iFrame.
    apply elem_of_subseteq_singleton, elem_of_dom; eauto.
  Qed.

End STS.
