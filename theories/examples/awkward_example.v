From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec. 
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static.
From cap_machine.examples Require Import region_macros stack_macros scall malloc.
From stdpp Require Import countable.

Lemma big_sepM_to_big_sepL {Σ : gFunctors} {A B : Type} `{EqDecision A} `{Countable A}
      (r : gmap A B) (lr : list A) (φ : A → B → iProp Σ) :
  NoDup lr →
  (∀ r0, r0 ∈ lr → ∃ b, r !! r0 = Some b) →
  ([∗ map] k↦y ∈ r, φ k y) -∗ ([∗ list] y ∈ lr, ∃ b, φ y b).
Proof.
  iInduction (lr) as [ | r0 ] "IHl" forall (r); iIntros (Hdup Hlookup) "Hmap".
  - done.
  - assert (∃ b, r !! r0 = Some b) as [b Hr0].
    { apply Hlookup. apply elem_of_cons. by left. } 
    iDestruct (big_sepM_delete _ _ r0 with "Hmap") as "[Hr0 Hmap]"; eauto.
    iSplitL "Hr0".
    + iExists b. iFrame. 
    + iApply ("IHl" with "[] [] [$Hmap]").
      { iPureIntro. apply NoDup_cons_12 in Hdup. auto. }
      iPureIntro.
      intros r1 Hr1.
      destruct (decide (r0 = r1)).
      * subst. apply NoDup_cons in Hdup as [Hnelem Hdup]. contradiction. 
      * rewrite lookup_delete_ne;auto. apply Hlookup.
        apply elem_of_cons. by right.
Qed.

Lemma NoDup_of_sepL2_exclusive {Σ : gFunctors} {A B: Type} (l1: list A) (l2: list B) (Φ: A -> B -> iProp Σ):
  (∀ a x1 x2, Φ a x1 -∗ Φ a x2 -∗ False) -∗
  ([∗ list] a;x ∈ l1;l2, Φ a x) -∗
  ⌜NoDup l1⌝.
Proof.
  revert l2. induction l1 as [| a1' l1].
  { iIntros (?) "_ _". iPureIntro. constructor. }
  { iIntros (l2) "HΦ H". destruct l2 as [| a2' l2]; [done|]. cbn. iDestruct "H" as "[Ha1 H]".
    iDestruct (IHl1 with "HΦ H") as %?.
    iAssert (⌜a1' ∉ l1⌝)%I as %?.
    { iIntros (Hin). destruct (elem_of_list_lookup_1 _ _ Hin) as [k ?].
      iDestruct (big_sepL2_length with "H") as %Hlen12.
      destruct (lookup_lt_is_Some_2 l2 k).
      { rewrite -Hlen12 -lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_lookup with "H") as "Ha1'"; eauto.
      iApply ("HΦ" with "Ha1 Ha1'"). }
    iPureIntro. by constructor. }
Qed.

Lemma region_mapsto_cons `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
                           MonRef: MonRefG (leibnizO _) CapR_rtc Σ, Heap: heapG Σ}
      (b b' e : Addr) (w : Word) (ws : list Word) (p : Perm) :
  (b + 1)%a = Some b' → (b' <= e)%a →
  [[b, e]] ↦ₐ [p] [[ w :: ws ]] ⊣⊢ b ↦ₐ[p] w ∗ [[b', e]] ↦ₐ [p] [[ ws ]].
Proof.
  intros Hb' Hb'e.
  rewrite /region_mapsto.
  rewrite (region_addrs_decomposition b b e).
  2: revert Hb' Hb'e; clear; intros; split; solve_addr.
  rewrite interp_weakening.region_addrs_empty /=.
  2: clear; solve_addr.
  rewrite (_: ^(b + 1) = b')%a.
  2: revert Hb' Hb'e; clear; intros; solve_addr.
  eauto.
Qed.

Lemma elements_list_to_set {A} `{Countable A} (l: list A) :
  NoDup l →
  elements (list_to_set l : gset A) ≡ₚ l.
Proof.
  induction l.
  - intros. rewrite list_to_set_nil elements_empty //.
  - intros ND. rewrite list_to_set_cons elements_union_singleton.
    + rewrite IHl //. eauto using NoDup_cons_12.
    + rewrite not_elem_of_list_to_set. by apply NoDup_cons_11.
Qed.

Definition lists_to_static_region (l1: list Addr) (l2: list Word) (p: Perm): gmap Addr (Perm * Word) :=
  list_to_map (zip l1 (map (λ w, (p, w)) l2)).

Definition lists_to_static_region_perms (l1 : list Addr) (l2 : list (Perm * Word))
  : gmap Addr (Perm * Word) :=
  list_to_map (zip l1 l2).

Lemma lists_to_static_region_cons a w l1 l2 p :
  lists_to_static_region (a :: l1) (w :: l2) p =
  <[ a := (p, w) ]> (lists_to_static_region l1 l2 p).
Proof. reflexivity. Qed.

Lemma lists_to_static_region_perms_cons a pw l1 l2 :
  lists_to_static_region_perms (a :: l1) (pw :: l2) =
  <[ a :=  (pw.1,pw.2)]> (lists_to_static_region_perms l1 l2).
Proof. destruct pw. cbn. reflexivity. Qed.

Lemma lists_to_static_region_perms_repeat (l1 : list Addr) (l2 : list Word) p :
  lists_to_static_region l1 l2 p =
  lists_to_static_region_perms l1 (zip (repeat p (length l2)) l2). 
Proof.
  revert l2. induction l1;intros l2; auto.
  destruct l2;auto. 
  rewrite cons_length /=. 
  rewrite lists_to_static_region_cons lists_to_static_region_perms_cons.
  f_equiv. auto.
Qed. 

Lemma lists_to_static_region_lookup_None l1 l2 p a :
  a ∉ l1 → lists_to_static_region l1 l2 p !! a = None.
Proof.
  revert l2. induction l1; eauto; []. intros l2 [? ?]%not_elem_of_cons.
  destruct l2.
  { cbn. eauto. }
  { rewrite lists_to_static_region_cons. rewrite lookup_insert_None. eauto. }
Qed.

Lemma lists_to_static_region_perms_lookup_None l1 l2 a :
  a ∉ l1 → lists_to_static_region_perms l1 l2 !! a = None.
Proof.
  revert l2. induction l1; eauto; []. intros l2 [? ?]%not_elem_of_cons.
  destruct l2.
  { cbn. eauto. }
  { rewrite lists_to_static_region_perms_cons. rewrite lookup_insert_None. eauto. }
Qed.

Lemma list_to_map_lookup_is_Some {A B} `{Countable A, EqDecision A} (l: list (A * B)) (a: A) :
  is_Some ((list_to_map l : gmap A B) !! a) ↔ a ∈ l.*1.
Proof.
  induction l.
  - cbn. split; by inversion 1.
  - cbn. rewrite lookup_insert_is_Some' elem_of_cons.
    split; intros [HH|HH]; eauto; rewrite -> IHl in *; auto.
Qed.

Lemma zip_app {A B} (l1 l1': list A) (l2 l2' : list B) :
  length l1 = length l2 ->
  zip (l1 ++ l1') (l2 ++ l2') = zip l1 l2 ++ zip l1' l2'.
Proof.
  revert l2. induction l1;intros l2 Hlen.
  - destruct l2;[|inversion Hlen]. done.
  - destruct l2;[inversion Hlen|]. simpl.
    f_equiv. auto. 
Qed. 
    
Lemma lists_to_static_region_dom l1 l2 p :
  length l1 = length l2 →
  dom (gset Addr) (lists_to_static_region l1 l2 p) = list_to_set l1.
Proof.
  intros Hlen. apply elem_of_equiv_L. intros x.
  rewrite /lists_to_static_region elem_of_dom elem_of_list_to_set.
  split. by intros [? ?%elem_of_list_to_map_2%elem_of_zip_l].
  intros Hx.
  destruct (elem_of_list_lookup_1 _ _ Hx) as [xi Hxi].
  pose proof (lookup_lt_Some _ _ _ Hxi).
  rewrite list_to_map_lookup_is_Some fst_zip // map_length. lia.
Qed.

Lemma lists_to_static_perms_region_dom l1 l2 :
  length l1 = length l2 →
  dom (gset Addr) (lists_to_static_region_perms l1 l2) = list_to_set l1.
Proof.
  intros Hlen. apply elem_of_equiv_L. intros x.
  rewrite /lists_to_static_region elem_of_dom elem_of_list_to_set.
  split. by intros [? ?%elem_of_list_to_map_2%elem_of_zip_l].
  intros Hx.
  destruct (elem_of_list_lookup_1 _ _ Hx) as [xi Hxi].
  pose proof (lookup_lt_Some _ _ _ Hxi).
  rewrite list_to_map_lookup_is_Some fst_zip //. lia.
Qed.

Lemma big_sepL2_to_static_region {Σ: gFunctors} l1 l2 p (Φ : _ → _ → iProp Σ) Ψ :
  NoDup l1 →
  □ (∀ a w, ⌜a ∈ l1⌝ -∗ ⌜w ∈ l2⌝ -∗ Φ a w -∗ Ψ a (p, w)) -∗
  ([∗ list] a;w ∈ l1;l2, Φ a w) -∗
  ([∗ map] a↦pv ∈ lists_to_static_region l1 l2 p, Ψ a pv).
Proof.
  revert l2. induction l1; intros l2 ND.
  { cbn in *. iIntros "_ _". by iApply big_sepM_empty. }
  { iIntros "#Ha H". iDestruct (big_sepL2_cons_inv_l with "H") as (w l2' ->) "[HΦ H]".
    rewrite lists_to_static_region_cons. iApply big_sepM_insert.
    by apply lists_to_static_region_lookup_None, NoDup_cons_11.
    iSplitL "HΦ". { iApply "Ha"; try (iPureIntro; constructor). auto. }
    iApply IHl1; auto.
    by eauto using NoDup_cons_12.
    iModIntro. iIntros. iApply "Ha"; auto; iPureIntro; by constructor. }
Qed.

Lemma big_sepL2_to_static_region_perms {Σ: gFunctors} l1 l2 (Φ : _ → _ → _ -> iProp Σ) Ψ :
  NoDup l1 →
  □ (∀ k a w, ⌜l1 !! k = Some a⌝ -∗ ⌜l2 !! k = Some w⌝ -∗ Φ a w.1 w.2 -∗ Ψ a w) -∗
  ([∗ list] a;w ∈ l1;l2, Φ a w.1 w.2) -∗
  ([∗ map] a↦pv ∈ lists_to_static_region_perms l1 l2, Ψ a pv).
Proof.
  revert l2. induction l1; intros l2 ND.
  { cbn in *. iIntros "_ _". by iApply big_sepM_empty. }
  { iIntros "#Ha H". iDestruct (big_sepL2_cons_inv_l with "H") as (w l2' ->) "[HΦ H]".
    rewrite lists_to_static_region_perms_cons. iApply big_sepM_insert.
    by apply lists_to_static_region_perms_lookup_None, NoDup_cons_11.
    iSplitL "HΦ". { destruct w. simpl. iApply ("Ha" $! 0); try (iPureIntro; constructor). eauto. }
    iApply IHl1; auto.
    by eauto using NoDup_cons_12.
    iModIntro. iIntros. iApply ("Ha" $! (S k)); auto; iPureIntro. }
Qed.

Lemma static_region_perms_to_big_sepL2 {Σ: gFunctors} l1 l2 (Φ : _ → _ → _ -> iProp Σ) Ψ :
  NoDup l1 → length l1 = length l2 ->
  □ (∀ k a w, ⌜l1 !! k = Some a⌝ -∗ ⌜l2 !! k = Some w⌝ -∗ Ψ a w -∗ Φ a w.1 w.2) -∗
  ([∗ map] a↦pv ∈ lists_to_static_region_perms l1 l2, Ψ a pv) -∗
  ([∗ list] a;w ∈ l1;l2, Φ a w.1 w.2). 
Proof.
  revert l2. induction l1; intros l2 ND Hlen.
  { cbn in *. iIntros "_ _". destruct l2;[|inversion Hlen]. done. }
  { iIntros "#Ha H". destruct l2;[inversion Hlen|]. iDestruct (big_sepM_delete with "H") as "[Hψ H]". 
    rewrite lists_to_static_region_perms_cons. apply lookup_insert.
    iSplitL "Hψ". { iApply ("Ha" $! 0); try (iPureIntro; constructor). destruct p;simpl. eauto. }
    iApply IHl1; auto.
    by eauto using NoDup_cons_12.
    iModIntro. iIntros. iApply ("Ha" $! (S k)); auto; iPureIntro.
    rewrite lists_to_static_region_perms_cons.
    rewrite delete_insert. auto. by apply lists_to_static_region_perms_lookup_None, NoDup_cons_11. }
Qed.

Lemma big_sepL2_zip_repeat {Σ: gFunctors} {A B C : Type} l1 l2 (Φ : A → B -> C -> iProp Σ) (b : B) :
  (([∗ list] y1;y2 ∈ l1;l2, Φ y1 b y2) ∗-∗
  [∗ list] y1;y2 ∈ l1;(zip (repeat b (length l2)) l2), Φ y1 y2.1 y2.2)%I. 
Proof.
  iSplit.
  { iIntros "Hl".
    iInduction l1 as [|a l1] "IH" forall (l2).
    - iDestruct (big_sepL2_length with "Hl") as %Hlength. 
      destruct l2;[|inversion Hlength]. done.
    - iDestruct (big_sepL2_length with "Hl") as %Hlength. 
      destruct l2;[inversion Hlength|].
      iDestruct "Hl" as "[Hy Hl]".
      simpl. iFrame. by iApply "IH".
  }
  { iIntros "Hl".
    iInduction l1 as [|a l1] "IH" forall (l2).
    - iDestruct (big_sepL2_length with "Hl") as %Hlength. 
      destruct l2;[|inversion Hlength]. done.
    - iDestruct (big_sepL2_length with "Hl") as %Hlength. 
      destruct l2;[inversion Hlength|].
      iDestruct "Hl" as "[Hy Hl]".
      simpl. iFrame. by iApply "IH".
  }
Qed.

(* Helper lemma to extract registers from a big_sepL2 *)
Lemma big_sepL2_extract_l `{Σ : gFunctors} {A B : Type}
      (i : nat) (ai : A) (a : list A) (b : list B) (φ : A -> B -> iProp Σ) :
  a !! i = Some ai ->
  (([∗ list] a_i;b_i ∈ a;b, φ a_i b_i) -∗
    (∃ b', [∗ list] a_i;b_i ∈ (delete i a);b', φ a_i b_i) ∗ ∃ b, φ ai b)%I.
Proof. 
  iIntros (Hsome) "Hl".
  iDestruct (big_sepL2_length with "Hl") as %Hlength.      
  assert (take i a ++ drop i a = a) as Heqa;[apply take_drop|]. 
  assert (take i b ++ drop i b = b) as Heqb;[apply take_drop|]. 
  rewrite -Heqa -Heqb.
  iDestruct (big_sepL2_app_inv with "Hl") as "[Htake Hdrop]". 
  { apply lookup_lt_Some in Hsome.
    do 2 (rewrite take_length_le;[|lia]). done. 
  }
  apply take_drop_middle in Hsome as Hcons.
  assert (ai :: drop (S i) a = drop i a) as Hh.
  { apply app_inv_head with (take i a). congruence. }
  rewrite -Hh.
  iDestruct (big_sepL2_length with "Hdrop") as %Hlength'.      
  destruct (drop i b);[inversion Hlength'|].
  iDestruct "Hdrop" as "[Hφ Hdrop]".
  iSplitR "Hφ";[|eauto].
  iExists (take i b ++ l). rewrite Hcons. 
  iDestruct (big_sepL2_app with "Htake Hdrop") as "Hl". 
  rewrite delete_take_drop. iFrame.
Qed.

(* Lemma about zip and repeat *)
Lemma zip_repeat_lookup_l {A B : Type} (l : list A) k (b : B) :
  k < length l -> 
  ∃ a, zip (repeat b (length l)) l !! k = Some (b, a). 
Proof.
  revert k. induction l; intros k Hlen.  
  - simpl in Hlen. lia.
  - simpl. destruct k;eauto. 
    apply IHl. simpl in Hlen. lia.
Qed.     
    
Lemma length_zip_l {A B} (l1: list A) (l2: list B) :
  length l1 ≤ length l2 → length (zip l1 l2) = length l1.
Proof.
  revert l2. induction l1; intros l2 Hl2; auto.
  destruct l2; cbn in Hl2. exfalso; lia.
  cbn. rewrite IHl1; auto. lia.
Qed.

Section awkward_example.
Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

   Notation STS := (leibnizO (STS_states * STS_rels)).
   Notation WORLD := (leibnizO (STS * STS)). 
   Implicit Types W : WORLD.
   
   (* choose a special register for the environment and adv pointer *)
   (* note that we are here simplifying the environment to simply point to one location *)      
   Definition r_env : RegName := r_t30.
   Definition r_adv : RegName := r_t28.

   (* Lemma which splits a list of temp resources into its persistent and non persistent parts *)
   Lemma temp_resources_split l W : 
     ([∗ list] a ∈ l, (∃ (p : Perm) (φ : prodO STS STS * Word → iPropI Σ),
                          ⌜∀ Wv : prodO STS STS * Word, Persistent (φ Wv)⌝ ∗ temp_resources W φ a p ∗ rel a p φ)
                        ∗ ⌜std_sta (revoke W) !! encode a = Some (encode Revoked)⌝) -∗
     ∃ (pws : list (Perm * Word)), □ ([∗ list] a;wp ∈ l;pws, ∃ φ, ⌜∀ Wv : prodO STS STS * Word, Persistent (φ Wv)⌝
                                                             ∗ ⌜wp.1 ≠ O⌝
                                                             ∗ φ (W,wp.2)
                                                             ∗ rel a wp.1 φ
                                                             ∗ (if pwl wp.1 then future_pub_mono φ wp.2
                                                                else future_priv_mono φ wp.2))
                          ∗ ⌜Forall (λ a, std_sta (revoke W) !! encode a = Some (encode Revoked)) l⌝
                          ∗ ([∗ list] a;wp ∈ l;pws, a ↦ₐ[wp.1] wp.2).
   Proof.
     rewrite /temp_resources. 
     iIntros "Hl".
     iAssert ([∗ list] a ∈ l, ∃ (p : Perm) (v : Word), (∃ (φ : prodO STS STS * Word → iPropI Σ), 
                            ⌜∀ Wv : prodO STS STS * Word, Persistent (φ Wv)⌝
                            ∗ ⌜p ≠ O⌝
                            ∗ a ↦ₐ[p] v ∗ (if pwl p then future_pub_mono φ v else future_priv_mono φ v) ∗ φ (W, v)
                            ∗ rel a p φ ∗ ⌜std_sta (revoke W) !! encode a = Some (encode Revoked)⌝))%I
       with "[Hl]" as "Hl".
     { iApply (big_sepL_mono with "Hl").
       iIntros (k y Hy) "Hy".
       iDestruct "Hy" as "[Hy Hy']".
       iDestruct "Hy" as (p φ) "(Hpers & Hv & Hrel)".
       iDestruct "Hv" as (v) "(Hne & Hy & Hmono & Hφ)".
       iExists p,v,φ. iFrame. 
     }
     iDestruct (region_addrs_exists_zip with "Hl") as (wps) "Hl".
     iExists wps. iSplit. 
     - iAssert ([∗ list] a;wp ∈ l;wps, ∃ φ, ⌜∀ Wv : prodO STS STS * Word, Persistent (φ Wv)⌝
                                                             ∗ ⌜wp.1 ≠ O⌝
                                                             ∗ φ (W,wp.2)
                                                             ∗ rel a wp.1 φ
                                                             ∗ (if pwl wp.1 then future_pub_mono φ wp.2
                                                                else future_priv_mono φ wp.2))%I
         with "[Hl]" as "Hl". 
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as (φ) "(Hpers & Hne & Hy & Hmono & Hφ & Hrel & Hrev)".
         iExists φ. iFrame. 
       }
       iDestruct (region_addrs_exists2 with "Hl") as (φs Hlen) "Hl".
       iDestruct (big_sepL2_sep with "Hl") as "[Hpers Hl]".
       iDestruct (big_sepL2_length with "Hl") as %Hlength. 
       iDestruct (big_sepL2_to_big_sepL_r with "Hpers") as "Hpers";auto. 
       iDestruct (big_sepL_forall with "Hpers") as %Hpers.
       iAssert ([∗ list] y1;y2 ∈ l;zip wps φs, □ (⌜y2.1.1 ≠ O⌝
                                        ∗ y2.2 (W, y2.1.2)
                                          ∗ rel y1 y2.1.1 y2.2
                                            ∗ (if pwl y2.1.1
                                               then future_pub_mono y2.2 y2.1.2
                                               else future_priv_mono y2.2 y2.1.2)))%I
         with "[Hl]" as "Hl".
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         apply Hpers with (Wv:=(W,y2.1.2)) in Hy2.
         destruct (pwl y2.1.1) eqn:Hpwl.
         - iDestruct "Hy" as "#(Hne & Hy & Hrel & Hmono)".
           iAlways. rewrite Hpwl. iFrame "#".
         - iDestruct "Hy" as "#(Hne & Hy & Hrel & Hmono)".
           iAlways. rewrite Hpwl. iFrame "#".
       }
       iDestruct "Hl" as "#Hl". 
       iAlways. iApply region_addrs_exists2.
       iExists φs. iSplit;auto.
       iApply big_sepL2_sep. iSplit.
       + iApply big_sepL2_to_big_sepL_r;auto. iApply big_sepL_forall. auto.
       + iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as "#(Hne & Hy & Hrel & Hmono)".
         iFrame "#".
     - iAssert ([∗ list] a0;bc0 ∈ l;wps, (∃ φ : prodO STS STS * Word → iPropI Σ,
                                    ⌜∀ Wv : prodO STS STS * Word, Persistent (φ Wv)⌝
                                    ∗ ⌜bc0.1 ≠ O⌝
                                      ∗ a0 ↦ₐ[bc0.1] bc0.2
                                        ∗ (if pwl bc0.1 then future_pub_mono φ bc0.2 else future_priv_mono φ bc0.2)
                                          ∗ φ (W, bc0.2)
                                            ∗ rel a0 bc0.1 φ)
                                              ∗ ⌜std_sta (revoke W) !! encode a0 =
                                         Some (encode Revoked)⌝)%I
         with "[Hl]" as "Hl".
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as (φ) "(?&?&?&?&?&?&?)".
         iFrame. iExists _. iFrame. 
       }
       iDestruct (big_sepL2_sep with "Hl") as "[Hl #Hrev]".
       iDestruct (big_sepL2_length with "Hl") as %Hlength.
       iSplit.
       + iDestruct (big_sepL2_to_big_sepL_l with "Hrev") as "Hrev'";auto. 
         iDestruct (big_sepL_forall with "Hrev'") as %Hrev.
         iPureIntro. apply Forall_forall. intros x Hin.
         apply elem_of_list_lookup in Hin as [k Hin].
           by apply Hrev with (x:=k).
       + iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as (φ) "(?&?&?&?&?&?)".
         iFrame.
   Qed. 
         

   (* TODO: move to region_invariants_static *)
   Lemma region_has_static_addr_Forall (W:WORLD) (a:Addr) (m: gmap Addr (Perm*Word)):
     std_sta W !! encode a = Some (encode (Static m)) →
     region W ∗ sts_full_world sts_std W
            -∗ ⌜Forall (λ a':Addr, std_sta W !! encode a' = Some (encode (Static m)))
            (elements (dom (gset Addr) m))⌝.
   Proof.
     iIntros (?) "(Hr & Hsts)". rewrite region_eq /region_def.
     iDestruct "Hr" as (M Mρ) "(? & % & Hdom & Hr)". iDestruct "Hdom" as %Hdom.
     iDestruct (full_sts_Mρ_agree with "Hsts Hr") as %Hagree; eauto.

     iDestruct (region_map_has_static_addr with "[$Hr $Hsts]") as %[HH ?]; eauto.
     iPureIntro. rewrite -set_Forall_elements. intros x Hx. rewrite Hagree. auto.
   Qed.

   (* helper lemma to state that a fresh allocation creates a public future world *)
   Lemma related_sts_pub_fresh (W : STS) a ρ i:
     i ∉ dom (gset positive) W.1 →
     i ∉ dom (gset positive) W.2 →
     related_sts_pub W.1 (<[i:=a]> W.1) W.2 (<[i:=ρ]> W.2).
   Proof.
     intros Hdom_sta Hdom_rel.
     rewrite /related_sts_pub. split;[|split;[auto|] ].
     - apply dom_insert_subseteq.
     - apply dom_insert_subseteq.
     - apply not_elem_of_dom in Hdom_sta.
       apply not_elem_of_dom in Hdom_rel.
       intros j r1 r2 r1' r2' Hr Hr'.
       destruct (decide (j = i)).
       + subst. rewrite Hr in Hdom_rel. done.
       + rewrite lookup_insert_ne in Hr'; auto.
         rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
         intros x y Hx Hy.
         rewrite lookup_insert_ne in Hy;auto.
         rewrite Hx in Hy.
         inversion Hy; inversion Hr'; subst.
         left.
   Qed.
     
  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _ 
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end. 

  Ltac iContiguous_bounds i j :=
    eapply contiguous_between_middle_bounds' with (a0 := i) (an := j);
    [ eauto | cbn; solve [ repeat constructor ] ].

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_bounds_withinBounds a0 an :=
    apply isWithinBounds_bounds_alt' with a0 an; auto; [];
    iContiguous_bounds a0 an.

  Lemma isCorrectPC_range_npE p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p ≠ E.
  Proof.
    intros HH1 HH2. 
    destruct (isCorrectPC_range_perm _ _ _ _ _ _ HH1 HH2) as [?| [?|?] ]; 
      congruence.
  Qed.

  Ltac isWithinBounds := rewrite /withinBounds; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; simpl; auto.

  Ltac iNotElemOfList :=
    repeat (apply not_elem_of_cons; split;[auto|]); apply not_elem_of_nil.  

  Ltac addr_succ :=
    match goal with
    | H : _ |- (?a1 + ?z)%a = Some ?a2 =>
      rewrite /incr_addr /=; do 2 f_equal; apply eq_proofs_unicity; decide equality
    end.

   (* The following ltac gets out the next general purpuse register *)
   Ltac get_genpur_reg Hr_gen wsr ptr :=
     let w := fresh "wr" in 
       destruct wsr as [? | w wsr]; first (by iApply bi.False_elim);
       iDestruct Hr_gen as ptr.

   Ltac iDestructList Hlength l :=
     (repeat (let a := fresh "a" in destruct l as [|a l];[by inversion Hlength|]));
     destruct l;[|by inversion l].

   Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

   Ltac iPrologue_pre l Hl :=
     destruct l; [inversion Hl|]; iApply (wp_bind (fill [SeqCtx])).
   
   Ltac iPrologue l Hl prog := 
     iPrologue_pre l Hl;
     iDestruct prog as "[Hinstr Hprog]".     

  Ltac iEpilogue intro_ptrn :=
    iNext; iIntros intro_ptrn; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac iLookupR Hl :=
    rewrite /= lookup_app_r;rewrite Hl /=;auto.

  Lemma push_z_instrs_extract a i j z prog p' :
    contiguous_between a i j →
    ([∗ list] a_i;w_i ∈ a; (push_z_instrs r_stk z ++ prog), a_i ↦ₐ[p'] w_i) -∗
    ∃ a' push2 a_rest,
      (([∗ list] a_i;w_i ∈ [i; push2];push_z_instrs r_stk z, a_i ↦ₐ[p'] w_i) ∗
       [∗ list] a_i;w_i ∈ a'; prog, a_i ↦ₐ[p'] w_i) ∗
       ⌜ a = [i; push2] ++ a'
         ∧ (i + 1 = Some push2)%a
         ∧ (push2 + 1 = Some a_rest)%a
         ∧ contiguous_between a' a_rest j ⌝.
  Proof.
    intros. iIntros "HH".
    iDestruct (contiguous_between_program_split with "HH") as (a_push a' a_rest) "(Hpush & ? & #Hcont)"; eauto.
    iDestruct "Hcont" as %(Hcont1 & ? & -> & Hrest).
    iDestruct (big_sepL2_length with "Hpush") as %Hpushlength.
    destruct (contiguous_2 a_push) as (push1 & push2 & -> & Ha12); auto.
    { rewrite contiguous_iff_contiguous_between; eauto. }
    assert (push1 = i) as ->. { inversion Hcont1; auto. }
    iExists a', push2, a_rest. iFrame. iPureIntro. repeat split; eauto.
    cbn in Hrest. revert Ha12 Hrest; clear. solve_addr.
  Qed.

  Ltac iPush_z prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let push2 := fresh "push2" in
    let Ha1 := fresh "Ha1" in
    let Ha2 := fresh "Ha2" in
    let Ha := fresh "Ha" in
    iDestruct (push_z_instrs_extract with prog) as (a_rest push2 cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha2 & Ha);
    iApply (push_z_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha"; eauto;
    clear Ha1 Ha2; last iRename "Hprog" into prog.

  Lemma push_r_instrs_extract a i j r prog p' :
    contiguous_between a i j →
    ([∗ list] a_i;w_i ∈ a; (push_r_instrs r_stk r ++ prog), a_i ↦ₐ[p'] w_i) -∗
    ∃ a' push2 a_rest,
      (([∗ list] a_i;w_i ∈ [i; push2];push_r_instrs r_stk r, a_i ↦ₐ[p'] w_i) ∗
       [∗ list] a_i;w_i ∈ a'; prog, a_i ↦ₐ[p'] w_i) ∗
       ⌜ a = [i; push2] ++ a'
         ∧ (i + 1 = Some push2)%a
         ∧ (push2 + 1 = Some a_rest)%a
         ∧ contiguous_between a' a_rest j ⌝.
  Proof.
    intros. iIntros "HH".
    iDestruct (contiguous_between_program_split with "HH") as (a_push a' a_rest) "(Hpush & ? & #Hcont)"; eauto.
    iDestruct "Hcont" as %(Hcont1 & ? & -> & Hrest).
    iDestruct (big_sepL2_length with "Hpush") as %Hpushlength.
    destruct (contiguous_2 a_push) as (push1 & push2 & -> & Ha12); auto.
    { rewrite contiguous_iff_contiguous_between; eauto. }
    assert (push1 = i) as ->. { inversion Hcont1; auto. }
    iExists a', push2, a_rest. iFrame. iPureIntro. repeat split; eauto.
    cbn in Hrest. revert Ha12 Hrest; clear. solve_addr.
  Qed.

  Ltac iPush_r prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let push2 := fresh "push2" in
    let Ha1 := fresh "Ha1" in
    let Ha2 := fresh "Ha2" in
    let Ha := fresh "Ha" in
    iDestruct (push_r_instrs_extract with prog) as (a_rest push2 cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha2 & Ha);
    iApply (push_r_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha Hreg";
    last iRename "Hprog" into prog.
  
  Ltac iGet_genpur_reg Hr_gen Hwsr wsr ptr :=
    let w := fresh "wr" in 
    destruct wsr as [? | w wsr]; first (by inversion Hwsr);
    iDestruct Hr_gen as ptr.
  
  Ltac iGet_genpur_reg_map r' reg Hgen_reg Hfull Hgen_ptrn :=
    let w := fresh "w" in
    let Hw := fresh "Hw" in 
    iAssert (⌜∃ w, r' !! reg = Some w⌝)%I as %[w Hw];
    first iApply Hfull;
    iDestruct (big_sepM_delete _ _ reg with Hgen_reg) as Hgen_ptrn;
    [repeat (rewrite lookup_delete_ne; auto; (try by (rewrite lookup_insert_ne; eauto)))|].
  
  Ltac iClose_genpur_reg_map reg Hgen_ptrn Hgen :=
    repeat (rewrite -(delete_insert_ne _ reg); [|auto]);
    iDestruct (big_sepM_insert _ _ reg with Hgen_ptrn) as Hgen;[apply lookup_delete|iFrame|rewrite insert_delete].
  
   (* Recall that the malloc subroutine lies in b_m e_m *)

   (* assume that r1 contains an executable pointer to the malloc subroutine *)
   (* Definition awkward_preamble_instrs r1 offset_to_awkward := *)
   (*   [move_r r_t0 PC; *)
   (*   lea_z r_t0 3; *)
   (*   jmp r1; *)
   (*   move_r r_self PC; *)
   (*   lea_z r_self offset_to_awkward; *)
   (*   jmp r_self]. *)
   
   (* assume r1 contains an executable pointer to adversarial code *)
  (* assume r0 contains an executable pointer to the awkward example *)
   Definition awkward_instrs (r1 : RegName) epilogue_off :=
     [store_z r_env 0] ++
     push_r_instrs r_stk r_env ++
     push_r_instrs r_stk r_t0 ++
     push_r_instrs r_stk r1 ++
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r1 ++
     pop_instrs r_stk r_t0 ++
     pop_instrs r_stk r_env ++
     [store_z r_env 1] ++
     push_r_instrs r_stk r_env ++
     push_r_instrs r_stk r_t0 ++ 
     scall_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r_t0 ++
     pop_instrs r_stk r_env ++
     (* assert that the cap in r_env points to 1 *)
     [load_r r1 r_env;
     move_r r_t1 PC;
     lea_z r_t1 62; (* offset to assertion failure. for now this is the adress after the program *)
     sub_r_z r1 r1 1;
     jnz r_t1 r1] ++
     (* in this version, we clear only the local stack frame before returning *)
     (* first we prepare the stack to only point to the local stack frame *)
     [getb r_t1 r_stk;
     add_r_z r_t2 r_t1 10;
     subseg_r_r r_stk r_t1 r_t2] ++ 
     mclear_instrs r_stk 10 2 ++
     rclear_instrs (list_difference all_registers [PC;r_t0]) ++
     [jmp r_t0].

   (* TODO: possibly add fail subroutine to awkward example? *)
  
   (* Definition awkward_preamble a p r1 offset_to_awkward := *)
   (*   ([∗ list] a_i;w_i ∈ a;(awkward_preamble_instrs r1 offset_to_awkward), a_i ↦ₐ[p] w_i)%I. *)
   
   Definition awkward_example (a : list Addr) (p : Perm) (r1 : RegName) epilogue_off : iProp Σ :=
     ([∗ list] a_i;w_i ∈ a;(awkward_instrs r1 epilogue_off), a_i ↦ₐ[p] w_i)%I.

   
   Definition awk_inv i a :=
     (∃ x:bool, sts_state_loc i x
           ∗ if x
             then a ↦ₐ[RWX] inl 1%Z
             else a ↦ₐ[RWX] inl 0%Z)%I.

   Definition awk_rel_pub := λ a b, a = false ∨ b = true.
   Definition awk_rel_priv := λ (a b : bool), True.

   (* useful lemma about awk rels *)
   Lemma rtc_rel_pub y x :
     y = (encode true) ->
     rtc (convert_rel awk_rel_pub) y x ->
     x = (encode true).
   Proof.
     intros Heq Hrtc.
     induction Hrtc; auto. 
     rewrite Heq in H3. 
     inversion H3 as [y' [b [Heq1 [Heq2 Hy] ] ] ].
     inversion Hy; subst; auto.
     apply encode_inj in Heq1. inversion Heq1.
   Qed.
   Lemma rtc_rel_pub' x :
     rtc (convert_rel awk_rel_pub) (encode true) (encode x) ->
     x = true.
   Proof.
     intros Hrtc. 
     apply encode_inj.
     apply rtc_rel_pub with (encode true); auto.
   Qed.
   Lemma rtc_rel_pub_false y x :
     y = (encode false) ->
     rtc (convert_rel awk_rel_pub) y x ->
     x = (encode true) ∨ x = (encode false).
   Proof.
     intros Heq Hrtc.
     induction Hrtc; auto. 
     rewrite Heq in H3. 
     inversion H3 as [y' [b [Heq1 [Heq2 Hy] ] ] ]. subst. 
     destruct b;apply encode_inj in Heq1;auto;subst. 
     left. eapply rtc_rel_pub; eauto. 
   Qed.
     
   Inductive local_state :=
   | Live
   | Released.
   Instance local_state_EqDecision : EqDecision local_state.
   Proof.
     intros ρ1 ρ2.
     destruct ρ1,ρ2;
       [by left|by right|by right| by left]. 
   Qed.
   Instance local_state_finite : finite.Finite local_state.
   Proof.
     refine {| finite.enum := [Live;Released] ;
               finite.NoDup_enum := _ ;
               finite.elem_of_enum := _ |}.
     - repeat (apply NoDup_cons; split; [repeat (apply not_elem_of_cons;split;auto); apply not_elem_of_nil|]).
         by apply NoDup_nil.
     - intros ρ.
       destruct ρ;apply elem_of_cons;[by left|right];
           apply elem_of_cons; by left.
   Qed.
   Global Instance local_state_countable : Countable local_state.
   Proof. apply finite.finite_countable. Qed.
   Instance local_state_inhabited: Inhabited local_state := populate (Live).
   
   Definition local_rel_pub := λ (a b : local_state), a = b.
   Definition local_rel_priv := λ (a b : local_state), (a = Live ∨ b = Released).

   (* useful lemmas about local state *)
   Lemma rtc_id_eq x y : 
     rtc (convert_rel (λ a b : local_state, a = b)) x y → x = y.
   Proof.
     intros Hrtc.
     induction Hrtc; auto.
     inversion H3 as (b & Hb1 & Hb2 & Hb3 & Hb4). congruence.
   Qed.
   Lemma local_state_related_sts_pub W W' j x :
     related_sts_pub_world W W' ->
     W.2.1 !! j = Some (encode Live) ->
     W.2.2 !! j = Some (convert_rel local_rel_pub, convert_rel local_rel_priv) ->
     W'.2.1 !! j = Some (encode x) ->
     W'.2.2 !! j = Some (convert_rel local_rel_pub, convert_rel local_rel_priv) ->
     x = Live.
   Proof.
     intros Hrelated Hjx Hj Hjx' Hj'. 
     destruct Hrelated as (_ & Hsub1 & Hsub2 & Hrelated).
     specialize (Hrelated j _ _ _ _ Hj Hj') as (_ & _ & Htrans).
     specialize (Htrans _ _ Hjx Hjx').
     destruct x; auto.
     apply rtc_id_eq in Htrans. apply encode_inj in Htrans.
     inversion Htrans. 
   Qed. 
     
   Definition awk_W W i : WORLD := (W.1,(<[i:=encode false]>W.2.1,<[i:=(convert_rel awk_rel_pub,convert_rel awk_rel_priv)]>W.2.2)).

   (* namespace definitions for the regions *)
   Definition regN : namespace := nroot .@ "regN".

   (* The proof of the awkward example goes through a number of worlds.
      Below are some helper lemmas and definitions about how these worlds 
      are related *)
   Lemma related_priv_local_1 W i :
     W.2.1 !! i = Some (encode true) ->
     W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     related_sts_priv_world W (W.1, (<[i:=encode false]> W.2.1, W.2.2)).
   Proof.
     intros Hlookup Hrel. 
     split;[apply related_sts_priv_refl|simpl].
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros j r1 r2 r1' r2' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x y Hx Hy.
     destruct (decide (i = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. rewrite Hlookup in Hx. inversion Hr; inversion Hx; subst.
       right with (encode false);[|left].
       right. exists true,false. repeat (split;auto).
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst. left.
   Qed.

   Lemma related_priv_local_2 W i j :
     i ≠ j ->
     W.2.1 !! j = Some (encode Live) ->
     W.2.2 !! j = Some (convert_rel local_rel_pub, convert_rel local_rel_priv) ->
     related_sts_priv_world (W.1, (<[i:=encode true]> W.2.1, W.2.2))
                            (W.1.1, std_rel (W.1, (<[i:=encode true]> W.2.1, W.2.2)),
                             (<[j:=encode Released]> (<[i:=encode true]> W.2.1), W.2.2)).
   Proof.
     intros Hne Hlookup Hrel.
     split;[apply related_sts_priv_refl|simpl].
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros k r1 r2 r1' r2' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x y Hx Hy.
     destruct (decide (k = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. rewrite lookup_insert_ne in Hx;auto.
       rewrite Hlookup in Hx. inversion Hr; inversion Hx; subst.
       right with (encode Released);[|left].
       right. exists Live,Released. repeat (split;auto). by left. 
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst. left.
   Qed.

   Lemma related_priv_local_3 W j :
     W.2.1 !! j = Some (encode Live) ->
     W.2.2 !! j = Some (convert_rel local_rel_pub, convert_rel local_rel_priv) ->
     related_sts_priv_world W (W.1, (<[j:=encode Released]> W.2.1, W.2.2)).
   Proof.
     intros Hlookup Hrel.
     split;[apply related_sts_priv_refl|simpl].
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros k r1 r2 r1' r2' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x y Hx Hy.
     destruct (decide (k = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. 
       rewrite Hlookup in Hx. inversion Hr; inversion Hx; subst.
       right with (encode Released);[|left].
       right. exists Live,Released. repeat (split;auto). by left. 
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst. left.
   Qed. 
     
   Lemma related_pub_local_1 Wloc i (x : bool) :
     Wloc.1 !! i = Some (encode x) ->
     Wloc.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     related_sts_pub Wloc.1 (<[i:=encode true]> Wloc.1) Wloc.2 Wloc.2.
   Proof.
     intros Hx Hrel.
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros j r1 r2 r1' r2' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x' y Hx' Hy.
     destruct (decide (i = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. rewrite Hx in Hx'. inversion Hr; inversion Hx; subst.
       right with (encode true);[|left].
       exists x,true. inversion Hx'. subst. repeat (split;auto).
       destruct x; rewrite /awk_rel_pub; auto. 
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx' in Hy; inversion Hy; subst. left.
   Qed.

   Lemma related_pub_lookup_local W W' i x :
     related_sts_pub_world W W' ->
     W.2.1 !! i = Some (encode true) ->
     W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     W'.2.1 !! i = Some (encode x) -> x = true.
   Proof.
     intros Hrelated Hi Hr Hi'.
     destruct Hrelated as [_ [Hdom1 [Hdom2 Htrans] ] ].
     assert (is_Some (W'.2.2 !! i)) as [r' Hr'].
     { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom2. apply Hdom2.
       apply elem_of_gmap_dom. eauto. }
     destruct r' as [r1' r2']. 
     specialize (Htrans i _ _ _ _ Hr Hr') as [Heq1 [Heq2 Htrans] ].
     subst. specialize (Htrans _ _ Hi Hi').
     apply rtc_rel_pub'; auto. 
   Qed.

   (* The following lemma asserts that the world upon return is indeed a public future world of W *)
   (* As the first step we want to show that if we assert that the closed region corresponds to ALL the 
      temporary region, then closing a revoked W equals W *)

   (* NB: with static regions, the previous version of this
      lemma does not hold anymore! The issue is, that any static regions in W 
      may be temporary in W3. From there, revoke W3 makes in revoked. Since we did not remember it in l (which only 
      remembered the temporary resources in W), we lost them and do not get a public future world by only reinstating l.
      The solution is to additionally remember all the (non stack) temporary resources when doing the second revoke, in 
      between the two adversary calls. In that case, we get a new list l'' which together with the stack from c to e gives
      us ALL temporary resources in W3. Now, once we reinstate those we will know that the static regions in W became temporary, 
      which will also give us a public future world in the end. 
    *)

   (* a core difference with the previous version of the lemma: we are not closing the world at the end. 
      Rather, we are updating all the Static regions back into Temporary ones *)
   
   Lemma related_pub_local_2 W W' W3 W6 b e l l' l1 l2 m1 m2 i j c c' :
     W' = ((revoke_std_sta W.1.1,W.1.2),(<[i:=encode false]> W.2.1,W.2.2))
     -> (b <= c < e)%a ∧ (b <= c' < e)%a
     (* dom_equal, so that we know that positives in W6 are encoded addresses *)
     -> (exists M, dom_equal (std_sta W) M)
     (* l is the list of all revoked resources in W *)
     -> (forall a : Addr, W.1.1 !! (encode a) = Some (encode Temporary) <-> a ∈ l)
     (* l' is the list of all addition revoked resources in W3 (other than [c,e)) *)
     -> (forall a : Addr, W3.1.1 !! (encode a) = Some (encode Temporary) <-> a ∈ l')
     (* m1 and m2 are the maps containing the local frame and the rest of the temporary resources *)
     -> (l ≡ₚl1 ++ (region_addrs b e) ∧ l' ≡ₚl2 ++ (region_addrs c e) ∧
        elements (dom (gset Addr) m1) ≡ₚl1 ++ l2 ∧ elements (dom (gset Addr) m2) ≡ₚregion_addrs b c')
     (* j is a fresh invariant *)
     -> j ∉ dom (gset positive) W'.2.1 → j ∉ dom (gset positive) W'.2.2
     (* i is the awkward invariant *)
     → W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)
     -> (∃ (b : bool), W.2.1 !! i = Some (encode b))
     (* all worlds are standard *)
     -> rel_is_std W ∧ rel_is_std W3 ∧ rel_is_std W6             
     → related_sts_pub_world
         (close_list_std_sta (encode <$> region_addrs c e) (revoke_std_sta W.1.1), W.1.2,
          (<[j:=encode Live]> (<[i:=encode false]> W.2.1),
           <[j:=(convert_rel local_rel_pub, convert_rel local_rel_priv)]> W.2.2)) W3
     → related_sts_pub_world
         (close_list (encode <$> region_addrs c' e)
                     (std_update_multiple
                        (std_update_multiple
                           (revoke
                              (W3.1.1, std_rel (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2)),
                               (<[j:=encode Released]> (<[i:=encode true]> W3.2.1), W3.2.2)))
                           (elements (dom (gset Addr) m2)) (Static m2)) (elements (dom (gset Addr) m1)) (Static m1))) W6
     → related_sts_pub_world W (std_update_temp_multiple W6 ((l1 ++ l2) ++ (region_addrs b c'))).
   Proof.
     intros Heq [Hbounds1 Hbounds2] Hdom Hiff1 Hiff2 Happ Hj1 Hj2 Hawk [x Hawki] (HstdW1 & HstdW3 & HstdW6) Hrelated1 Hrelated2. 
     subst W'.
     destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
     destruct W3 as [ [Wstd_sta3 Wstd_rel3] [Wloc_sta3 Wloc_rel3] ]. 
     destruct W6 as [ [Wstd_sta6 Wstd_rel6] [Wloc_sta6 Wloc_rel6] ].
     simpl in *.
     split; simpl. 
     - (* standard resources *)
       destruct Hrelated1 as [Hstd_related1 _]. 
       destruct Hrelated2 as [Hstd_related2 _]. simpl in *. 
       destruct Hstd_related2 as [Hstd_sta_dom2 [Hstd_rel_dom2 Hstd_related2] ].
       destruct Hstd_related1 as [Hstd_sta_dom1 [Hstd_rel_dom1 Hstd_related1] ].
       (* the states domain of W1 is a substset of W2 *)
       assert (dom (gset positive) Wstd_sta ⊆ dom (gset positive) Wstd_sta6) as Hsub.
       { rewrite -close_list_dom_eq -revoke_dom_eq in Hstd_sta_dom1. etrans;eauto.
         etrans;[|apply Hstd_sta_dom2].
         rewrite -close_list_dom_eq. 
         repeat (etrans;[|apply std_update_multiple_sta_dom_subseteq]).
         rewrite -revoke_dom_eq. done. 
       }
       assert (dom (gset positive) Wstd_rel ⊆ dom (gset positive) Wstd_rel6) as Hsub'.
       { etrans;eauto. etrans;[|apply Hstd_rel_dom2].
         repeat (etrans;[|apply std_update_multiple_rel_dom_subseteq]). auto. 
       }
       split;[|split].
       + etrans;[|apply std_update_multiple_sta_dom_subseteq]. auto. 
       + etrans;eauto. etrans;[|apply std_update_multiple_rel_dom_subseteq]. etrans;eauto.
       + intros k r1 r2 r1' r2' Hr Hr'.
         assert (is_Some (Wstd_rel3 !! k)) as [ [s1 s2] Hs].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hstd_rel_dom1. apply Hstd_rel_dom1. 
           assert (k ∈ dom (gset positive) Wstd_rel) as Hin;[apply elem_of_gmap_dom;eauto|auto]. } 
         specialize (Hstd_related1 k r1 r2 s1 s2 Hr Hs) as [Heq1 [Heq2 Hstd_related1] ]. subst.
         destruct (decide (k ∈ encode <$> (l1 ++ l2) ++ (region_addrs b c'))).
         * (* k is a revoked element, which is updated to static at the end *)
           assert (is_Some (Wstd_rel6 !! k)) as [ [r6 r6'] Hr6]. 
           { apply elem_of_gmap_dom. apply elem_of_subseteq in Hsub'; apply Hsub'. apply elem_of_gmap_dom;eauto. }
           destruct Happ as (Heq1' & Heq2' & Heq3' & Heq4'). 
           edestruct Hstd_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated2] ];[|eauto|]. 
           { destruct (decide (k ∈ encode <$> l1 ++ l2)).
             - revert e1. rewrite -Heq3' =>e1. rewrite std_rel_update_multiple_lookup_std_i;auto.
             - rewrite std_rel_update_multiple_lookup_same_i;auto.
               destruct (decide (k ∈ encode <$> region_addrs b c')).
               + revert e1. rewrite -Heq4' =>e1. rewrite std_rel_update_multiple_lookup_std_i;auto.
               + rewrite std_rel_update_multiple_lookup_same_i;auto. rewrite /std_rel /=.
                 apply HstdW3. eauto. rewrite Heq4'. done. 
               + rewrite Heq3'. done. 
           }
           rewrite std_rel_update_multiple_lookup_std_i in Hr';auto. inversion Hr';subst.
           assert (is_Some (Wstd_rel !! k)) as Hsome;eauto. apply HstdW1 in Hsome. rewrite Hsome in Hr. 
           inversion Hr; subst. 
           repeat split;auto.
           intros x0 y Hx0 Hy. rewrite std_sta_update_multiple_lookup_in_i in Hy;auto. inversion Hy; subst.
           (* apply elem_of_list_fmap in e0 as [a [Heqa e0] ]. subst. *)
           rewrite fmap_app in e0. apply elem_of_app in e0 as [Hl | Hl']. 
           ** (* k is either a revoked elements in l1, or l2 *)
             rewrite fmap_app in Hl. apply elem_of_app in Hl as [Hl | Hl'].
             *** (* k is a revoked element in W, which means it is Temporary in W *)
               assert (Wstd_sta !! k = Some (encode Temporary)) as Htemp.
               { apply elem_of_list_fmap in Hl as [y [-> Ha] ].
                 apply Hiff1. rewrite Heq1'. apply elem_of_app. by left. }
               rewrite Htemp in Hx0; inversion Hx0; subst. left.
             *** (* k is a revoked element in W3, which means it is Temporary in W3 *)
               assert (Wstd_sta3 !! k = Some (encode Temporary)) as Htemp.
               { apply elem_of_list_fmap in Hl' as [y [-> Ha] ].
                 apply Hiff2. rewrite Heq2'. apply elem_of_app. by left. }
               (* if x0 is temp we are done *)
               destruct (decide (x0 = encode Temporary));[subst;left|].
               (* o/w it will get revoked, then possibly closed: either case we are in a public future world *)
               assert (Wstd_sta !! k ≠ Some (encode Temporary)) as Hne;[congruence|].
               rewrite -revoke_monotone_lookup_same in Hx0; auto.
               (* if x0 is revoked we are done *)
               destruct (decide (x0 = encode Revoked));[subst;right with (encode Temporary);[|left]|].
               exists Revoked,Temporary. repeat split;auto. constructor.
               (* otherwise we know that Temporary is in a public future state to x0 by the first related1 *)
               assert (revoke_std_sta Wstd_sta !! k ≠ Some (encode Revoked)) as Hne';[congruence|].
               rewrite (close_list_std_sta_same_alt _ (encode <$> region_addrs c e)) in Hx0; auto.
           ** (* k is a revoked element in [b,c'] *)
             assert (Wstd_sta !! k = Some (encode Temporary)) as Htemp.
             { apply elem_of_list_fmap in Hl' as [y [-> Ha] ].
               apply Hiff1. rewrite Heq1'. apply elem_of_app. right.
               rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr]. 
               apply elem_of_app. by left.
             }
             rewrite Htemp in Hx0; inversion Hx0; subst. left.
         * destruct Happ as [Heq1' [Heq2' [Heqapp1 Heqapp2] ] ]. repeat rewrite fmap_app in n.
           apply not_elem_of_app in n as [Hn1 Hbc'].
           apply not_elem_of_app in Hn1 as [Hl1 Hl2].
           rewrite std_rel_update_multiple_lookup_same_i /std_rel /= in Hr';auto.
           2: { repeat rewrite fmap_app. repeat (apply not_elem_of_app;split;auto). }
           edestruct Hstd_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated2] ];[|eauto|]. 
           { rewrite std_rel_update_multiple_lookup_same_i;[|rewrite Heqapp1 fmap_app; apply not_elem_of_app;auto].
             rewrite std_rel_update_multiple_lookup_same_i; [|rewrite Heqapp2; auto]. eauto. }
           subst. repeat split;auto.
           intros x0 y Hx0 Hy.
           assert (exists a : Addr, k = encode a) as [a Heqa].
           { destruct Hdom as [M Hdom]. destruct Hdom with k as [Hdom1 Hdom2]. 
             assert (is_Some (Wstd_sta !! k)) as Hsome; eauto.
             apply Hdom1 in Hsome as [a [Heqa _] ]. eauto. 
           } 
           assert (k ∈ dom (gset positive) Wstd_sta3) as Hin3. 
           { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_dom.
             apply close_list_std_sta_is_Some. rewrite -revoke_std_sta_lookup_Some. eauto. }
           
           apply elem_of_dom in Hin3 as [y3 Hy3].
           (* we have two more cases, either k is an element of the stack passed on to adv call 2, 
              or k was never a revoked element *)
           destruct (decide (k ∈ encode <$> region_addrs c' e)).
           ** (* k is an element of the stack and was revoked in W *)
             assert (Wstd_sta !! k = Some (encode Temporary)) as Htemp.
             { subst. 
               apply Hiff1. rewrite Heq1'. apply elem_of_app. right.
               rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr]. 
               apply elem_of_app. right. revert e0. clear. set_solver. 
             }
             rewrite Htemp in Hx0; inversion Hx0; subst.
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { repeat rewrite fmap_app. repeat (apply not_elem_of_app;split;auto). }
             destruct (decide ((encode a) ∈ encode <$> region_addrs c e)) as [Hce | Hce].
             *** (* if k is in [c,e], we know its temporary by Hiff2 *)
               apply Hrelated2; auto.
               apply close_list_std_sta_revoked; auto. 
               rewrite std_sta_update_multiple_lookup_same_i;auto. 
               2: { rewrite Heqapp1. rewrite fmap_app. apply not_elem_of_app;split;auto. }
               rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heqapp2;auto]. 
               rewrite /revoke /std_sta /=. apply revoke_lookup_Temp; auto.
               apply Hiff2. rewrite Heq2'. revert Hce; clear; set_solver. 
             *** (* otherwise we must assert that it could have been revoked, then closed before the second call *)
               assert (rtc r1' (encode Revoked) y3) as Hrelated.
               { apply Hstd_related1; auto. rewrite -close_list_std_sta_same; auto.
                 apply revoke_lookup_Temp; auto. }
               apply Hrelated2; auto. apply close_list_std_sta_revoked; auto.
               rewrite std_sta_update_multiple_lookup_same_i;auto. 
               2: { rewrite Heqapp1. rewrite fmap_app. apply not_elem_of_app;split;auto. }
               rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heqapp2;auto]. 
               apply revoke_lookup_Revoked; auto.
                assert (is_Some (Wstd_rel !! (encode a))) as Hsome;eauto.
               apply HstdW1 in Hsome. rewrite Hsome in Hr; inversion Hr; subst.
               apply std_rel_pub_rtc_Revoked in Hrelated; auto.
               destruct Hrelated as [Htempy3 | Hrevy3];subst;auto.
               apply Hiff2 in Hy3. exfalso. revert Hy3. rewrite Heq2' =>Hy3. 
               apply elem_of_app in Hy3 as [Hcontr | Hcontr];[revert Hcontr Hl2; clear;set_solver|
                                                              revert Hcontr Hce; clear;set_solver].
           ** (* if k is never a revoked element, we can apply its transitions during the two future world relations *)
             assert (k ∉ encode <$> region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ c'). rewrite fmap_app. apply not_elem_of_app. auto.
               revert Hbounds2. clear. solve_addr. }
             assert (k ∉ encode <$> region_addrs c e) as Hce.
             { rewrite (region_addrs_split _ c) in Hbe. rewrite fmap_app in Hbe. apply not_elem_of_app in Hbe as [Hbc Hce].
               auto. revert Hbounds1. clear. solve_addr. }
             trans y3.
             *** apply Hstd_related1; auto. rewrite -close_list_std_sta_same; auto.
                 rewrite revoke_monotone_lookup_same;auto.
                 intros Hcontr. subst. 
                 apply Hiff1 in Hcontr. revert Hcontr. rewrite Heq1' =>Hcontr. 
                 apply elem_of_app in Hcontr as [Hcontr | Hcontr];[revert Hcontr Hl1; clear;set_solver|
                                                                   revert Hcontr Hbe; clear;set_solver].
             *** rewrite std_sta_update_multiple_lookup_same_i in Hy.
                 2: { repeat rewrite fmap_app. repeat (apply not_elem_of_app;split;auto). }
                 apply Hrelated2; auto.
                 rewrite -close_list_std_sta_same; auto. 
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heqapp1 fmap_app;apply not_elem_of_app;split;auto].
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heqapp2; auto].
                 rewrite revoke_monotone_lookup_same;auto.
                 intros Hcontr. subst. apply Hiff2 in Hcontr. revert Hcontr. rewrite Heq2' =>Hcontr.
                 apply elem_of_app in Hcontr as [Hcontr | Hcontr];[revert Hcontr Hl2; clear;set_solver|
                                                                   revert Hcontr Hce; clear;set_solver].
     - (* owned resources *)
       destruct Hrelated1 as [_ Hloc_related1]. 
       destruct Hrelated2 as [_ Hloc_related2]. simpl in *. 
       destruct Hloc_related2 as [Hloc_sta_dom2 [Hloc_rel_dom2 Hloc_related2] ].
       destruct Hloc_related1 as [Hloc_sta_dom1 [Hloc_rel_dom1 Hloc_related1] ].
       split;[|split].
       + rewrite std_update_multiple_loc_sta /=.
         etrans;[|apply Hloc_sta_dom2]. repeat rewrite std_update_multiple_loc_sta /=.
         trans (dom (gset positive) Wloc_sta3);[|repeat rewrite dom_insert_L;clear;set_solver].
         etrans;[|apply Hloc_sta_dom1]. repeat rewrite dom_insert_L;clear;set_solver. 
       + rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom2]. 
         repeat rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom1].
         rewrite dom_insert_L;clear;set_solver. 
       + rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /=.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related2.
         intros k r1 r2 r1' r2' Hr Hr'.
         assert (is_Some (Wloc_rel3 !! k)) as [ [s1 s2] Hs].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hloc_rel_dom1; apply Hloc_rel_dom1.
           assert (k ∈ dom (gset positive) Wloc_rel) as Hin;[apply elem_of_gmap_dom;eauto|].
           rewrite dom_insert_L. revert Hin. clear. set_solver. }
         assert (j ≠ k) as Hne.
         { intros Hcontr;subst. assert (k ∈ dom (gset positive) Wloc_rel); [|done].
           apply elem_of_dom. eauto. }
         edestruct Hloc_related1 with (i0:=k) as [Heq1 [Heq2 Hrelated] ];[rewrite lookup_insert_ne;eauto|eauto|subst]. 
         edestruct Hloc_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated'] ];[eauto|eauto|subst]. 
         repeat split;auto. intros x0 y Hx0 Hy. rewrite lookup_insert_ne in Hrelated;auto.
         assert (is_Some (Wloc_sta3 !! k)) as [y3 Hy3].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hloc_sta_dom1; apply Hloc_sta_dom1.
           assert (k ∈ dom (gset positive) Wloc_sta) as Hin;[apply elem_of_gmap_dom;eauto|].
           repeat rewrite dom_insert_L. revert Hin. clear. set_solver. }
         rewrite lookup_insert_ne in Hrelated';auto.
         destruct (decide (i = k));[subst|].
         * rewrite Hawk in Hr. inversion Hr; subst.           
           rewrite lookup_insert in Hrelated. rewrite lookup_insert in Hrelated'.
           rewrite Hawki in Hx0. inversion Hx0;subst.
           destruct x;[apply Hrelated'; auto|].
           etrans;[|apply Hrelated']; auto. right with (encode true);[|left].
           exists false,true. repeat split;auto. by constructor. 
         * rewrite lookup_insert_ne in Hrelated;auto. rewrite lookup_insert_ne in Hrelated';auto.
           etrans;[apply Hrelated|apply Hrelated']; eauto.
   Qed.
   (* The above lemma is not enough. Now with static regions, we also need to have a final world which is a public 
      future world to W3. This is not true as long as we have ANY live release pattern. *)

   (* TODO: move these to region.v file *)
   Lemma region_addrs_weak n a b e :
     a ∈ region_addrs_aux b (S n) ->
     (b + n)%a = Some e -> 
     a ≠ e ->
     a ∈ region_addrs_aux b n.
   Proof.
     revert b. induction n;intros b Hin Hb Hne.
     - simpl in Hin. apply elem_of_list_singleton in Hin. subst.
       rewrite addr_add_0 in Hb. inversion Hb. contradiction.
     - simpl. destruct (decide (a = b)).
       + subst. apply elem_of_cons. by left.
       + apply elem_of_cons. right.
         simpl in Hin. apply elem_of_cons in Hin.
         destruct Hin as [Hcontr | Hin];[contradiction|]. 
         apply IHn;auto. solve_addr.
   Qed. 
   
   Lemma region_addrs_elem_of_lt (a b e : Addr) n :
    a ∈ region_addrs_aux b n -> (b + n)%a = Some e -> (a < e)%a.
   Proof.
     rewrite /region_addrs. intros Hin.
     revert e. induction n; intros e.
     - inversion Hin.
     - intros He. 
       assert (exists e', (b + n)%a = Some e') as [e' He'].
       { rewrite Nat2Z.inj_succ in He. 
         assert (Z.succ n = n + 1)%Z as Heq;[lia|]. rewrite Heq in He.
         destruct (b + n)%a eqn:Hsome.
         { rewrite (addr_add_assoc _ a0) in He;auto. eauto. }
         exfalso. solve_addr.
       } 
       destruct n. 
       + rewrite addr_add_0 in He'. inversion He'. subst.
         simpl in Hin. apply elem_of_list_singleton in Hin. subst.
         solve_addr.
       + destruct (decide (a = e'));[subst;solve_addr|].
         rewrite /lt_addr. trans e';[|solve_addr]. 
         apply IHn;auto. apply region_addrs_weak with (e:=e');auto. 
   Qed.

   Lemma region_addrs_elem_of_ge (a b : Addr) n :
    a ∈ region_addrs_aux b n -> (b <= a)%a.
   Proof.
     rewrite /region_addrs.
     revert b. induction n;intros b Hin. 
     - inversion Hin.
     - simpl in Hin.
       apply elem_of_cons in Hin as [Heq | Hin]. 
       + subst. solve_addr. 
       + rewrite /le_addr. trans ^(b + 1)%a;[solve_addr|]. 
         apply IHn;auto.
   Qed.
   
   Lemma region_addrs_not_elem_of_le a (n : nat) :
     forall b a', (b + n)%a = Some a -> (a <= a')%a -> a' ∉ (region_addrs_aux b n).
   Proof.
     induction n.
     - intros b a' Ha' Hle. apply not_elem_of_nil.
     - intros b a' Ha' Hle. apply not_elem_of_cons.
       split.
       + intros Hcontr;subst. solve_addr. 
       + apply IHn;solve_addr. 
   Qed.
   
   Lemma region_addrs_xor_elem_of (a b c e : Addr) :
     (b <= c < e)%Z -> 
     a ∈ region_addrs b e ->
     (a ∈ region_addrs b c ∧ a ∉ region_addrs c e) ∨ (a ∉ region_addrs b c ∧ a ∈ region_addrs c e).
   Proof.
     intros Hbounds Ha.
     rewrite (region_addrs_split _ c) in Ha;auto.
     apply elem_of_app in Ha as [Hbc | Hce]. 
     - left. split;auto. apply region_addrs_not_elem_of.
       eapply region_addrs_elem_of_lt;eauto.
       assert (contiguous_between (region_addrs b c) b c).
       { apply contiguous_between_of_region_addrs; auto. solve_addr. }
       apply elem_of_list_lookup in Hbc as [k Hk].
       rewrite -region_addrs_length. 
       apply contiguous_between_length;auto. 
     - right. split;auto.
       assert (contiguous_between (region_addrs b c) b c).
       { apply contiguous_between_of_region_addrs; auto. solve_addr. }
       apply region_addrs_not_elem_of_le with (a:=c).
       + rewrite -region_addrs_length. 
         apply contiguous_between_length;auto. 
       + apply region_addrs_elem_of_ge with (region_size c e);auto. 
     - solve_addr. 
   Qed.        

   (* Instead we must use static regions all the way through *)
   
   Lemma related_pub_local_3 W W' W3 W6 b e l l' l1 l2 m1 m2 i c c' :
     W' = ((revoke_std_sta W.1.1,W.1.2),(<[i:=encode false]> W.2.1,W.2.2))
     -> (b <= c < e)%a ∧ (b <= c' < e)%a
     (* dom_equal, so that we know that positives in W6 are encoded addresses *)
     -> (exists M, dom_equal (std_sta W) M)
     (* l is the list of all revoked resources in W *)
     -> (forall a : Addr, W.1.1 !! (encode a) = Some (encode Temporary) <-> a ∈ l)
     (* l' is the list of all addition revoked resources in W3 (other than [c,e)) *)
     -> (forall a : Addr, W3.1.1 !! (encode a) = Some (encode Temporary) <-> a ∈ l')
     (* m1 and m2 are the maps containing the local frame and the rest of the temporary resources *)
     -> (l ≡ₚl1 ++ (region_addrs b e) ∧ l' ≡ₚl2 ++ (region_addrs c e) ∧
        elements (dom (gset Addr) m1) ≡ₚl1 ++ (region_addrs b c)
        ∧ elements (dom (gset Addr) m2) ≡ₚl1 ++ l2 ++ (region_addrs b c'))
     (* i is the awkward invariant *)
     → W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)
     -> (∃ (b : bool), W.2.1 !! i = Some (encode b))
     (* all worlds are standard *)
     -> rel_is_std W ∧ rel_is_std W3 ∧ rel_is_std W6
     → related_sts_pub_world
         (close_list (encode <$> region_addrs c e)
                     (std_update_multiple
                        (revoke (W.1,((<[i:=encode false]> W.2.1), W.2.2)))
                     (elements (dom (gset Addr) m1))
                     (Static m1))) W3
     → related_sts_pub_world
         (close_list (encode <$> region_addrs c' e)
                     (std_update_multiple
                        (std_update_multiple
                           (revoke (W3.1, ((<[i:=encode true]> W3.2.1), W3.2.2)))
                           (elements (dom (gset Addr) m1))
                           Revoked)
                     (elements (dom (gset Addr) m2))
                     (Static m2))) W6
     → related_sts_pub_world W (std_update_temp_multiple W6 (elements (dom (gset Addr) m2))).
   Proof.
     intros Heq [Hbounds1 Hbounds2] Hdom Hiff1 Hiff2 Happ Hawk [x Hawki] (HstdW1 & HstdW3 & HstdW6) Hrelated1 Hrelated2. 
     subst W'.
     simpl in *.
     split; simpl. 
     - (* standard resources *)
       destruct Hrelated1 as [Hstd_related1 _]. 
       destruct Hrelated2 as [Hstd_related2 _]. simpl in *. 
       destruct Hstd_related2 as [Hstd_sta_dom2 [Hstd_rel_dom2 Hstd_related2] ].
       destruct Hstd_related1 as [Hstd_sta_dom1 [Hstd_rel_dom1 Hstd_related1] ].
       assert (dom (gset positive) (std_sta W) ⊆ dom (gset positive) (std_sta W6)) as Hsub.
       { rewrite -close_list_dom_eq in Hstd_sta_dom1.
         trans (dom (gset positive) (std_sta W3)).
         - etrans;[|apply Hstd_sta_dom1]. etrans;[|apply std_update_multiple_sta_dom_subseteq].
           rewrite -revoke_dom_eq. done.
         - etrans;[|apply Hstd_sta_dom2].
           rewrite -close_list_dom_eq. 
           repeat (etrans;[|apply std_update_multiple_sta_dom_subseteq]).
           rewrite -revoke_dom_eq. done. 
       }
       assert (dom (gset positive) (std_rel W) ⊆ dom (gset positive) (std_rel W6)) as Hsub'.
       { etrans;eauto. etrans;[|apply Hstd_rel_dom2].
         repeat (etrans;[|apply std_update_multiple_rel_dom_subseteq]).
         etrans;[|apply Hstd_rel_dom1]. etrans;[|apply std_update_multiple_rel_dom_subseteq]. auto. 
       }
       split;[|split].
       + etrans;[|apply std_update_multiple_sta_dom_subseteq]. auto. 
       + etrans;eauto. etrans;[|apply std_update_multiple_rel_dom_subseteq]. etrans;eauto.
       + intros k r1 r2 r1' r2' Hr Hr'.
         destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
         destruct W3 as [ [Wstd_sta3 Wstd_rel3] [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ [Wstd_sta6 Wstd_rel6] [Wloc_sta6 Wloc_rel6] ].
         simpl in *.
         assert (is_Some (Wstd_rel3 !! k)) as [ [s1 s2] Hs].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hstd_rel_dom1. apply Hstd_rel_dom1. 
           assert (k ∈ dom (gset positive) Wstd_rel) as Hin;[apply elem_of_gmap_dom;eauto|auto].
           eapply elem_of_subseteq;[|apply Hin]. rewrite -elem_of_subseteq.
           etrans;[|apply std_update_multiple_rel_dom_subseteq]. auto. 
         }
         edestruct Hstd_related1 with (i0:=k) as [Heqrs1 [Heqrs2 Hrelated1] ];[|eauto|]. 
         { rewrite -std_update_multiple_std_rel_eq; eauto. }
         destruct (decide (k ∈ encode <$> l1 ++ l2 ++ (region_addrs b c'))).
         * (* k is a revoked element, which is updated to static at the end *)
           apply elem_of_list_fmap in e0 as [a [Ha e0] ]. subst. 
           assert (is_Some (Wstd_rel6 !! (encode a))) as [ [r6 r6'] Hr6].
           { apply elem_of_gmap_dom. apply elem_of_subseteq in Hsub'; apply Hsub'. apply elem_of_gmap_dom;eauto. }
           destruct Happ as (Heq1' & Heq2' & Heq3' & Heq4'). 
           edestruct Hstd_related2 with (i0:=encode a) as [Heq1 [Heq2 Hrelated2] ];[|eauto|].
           { rewrite std_rel_update_multiple_lookup_std_i;auto. apply elem_of_list_fmap. repeat eexists. by rewrite Heq4'. }
           rewrite std_rel_update_multiple_lookup_std_i in Hr';auto.
           2: { apply elem_of_list_fmap. repeat eexists. rewrite Heq4'. auto. }
           inversion Hr';subst.
           assert (is_Some (Wstd_rel !! (encode a))) as Hsome;eauto. apply HstdW1 in Hsome. rewrite Hsome in Hr.
           inversion Hr; subst. 
           repeat split;auto.
           intros x0 y Hx0 Hy. rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
           2: { apply elem_of_list_fmap. repeat eexists. rewrite Heq4'. auto. }
           inversion Hy; subst.
           (* apply elem_of_list_fmap in e0 as [a [Heqa e0] ]. subst. *)
           apply elem_of_app in e0 as [Hl1 | Hl']. 
           ** (* k is a revoked element in l1 *)
             assert (Wstd_sta !! (encode a) = Some (encode Temporary)) as Htemp.
             { apply Hiff1. rewrite Heq1'. apply elem_of_app. by left. }
             rewrite Htemp in Hx0; inversion Hx0; subst. left.
           ** (* k is a either revoked element in l2 or [b,c'] *)
             apply elem_of_app in Hl' as [Hl2 | Hbc']. 
             *** (* k is a revoked element in l2 *)
               assert (Wstd_sta3 !! (encode a) = Some (encode Temporary)) as Htemp.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. by left. }
               (* if x0 is temp we are done *)
               destruct (decide (x0 = encode Temporary));[subst;left|].
               (* o/w it cannot be an element of either l1 or [b,e], which means it will not get set to static *)
               apply Hrelated1; auto. 
               assert (a ∉ l1 ++ region_addrs b e) as Hnin.
               { rewrite -Heq1'. intros Hin. apply Hiff1 in Hin. rewrite Hx0 in Hin. inversion Hin. contradiction. }
               apply not_elem_of_app in Hnin as [Hl1 Hbe].
               rewrite (region_addrs_split _ c) in Hbe;[|revert Hbounds1;clear;solve_addr].
               apply not_elem_of_app in Hbe as [Hbc Hce].
               rewrite -close_list_std_sta_same.
               rewrite std_sta_update_multiple_lookup_same.
               rewrite revoke_monotone_lookup_same;auto.
               rewrite Hx0. intros Hcontr; inversion Hcontr; contradiction.
               rewrite Heq3'. apply not_elem_of_app. split;auto.
               revert Hce. clear. set_solver.
             *** (* k is a revoked element in [b,c'] *)
               assert (Wstd_sta !! (encode a) = Some (encode Temporary)) as Htemp.
               { apply Hiff1. rewrite Heq1'. apply elem_of_app. right.
                 rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr].
                 apply elem_of_app. by left. }
               rewrite Hx0 in Htemp. inversion Htemp. left. 
         * destruct Happ as [Heq1' [Heq2' [Heq3' Heq4'] ] ]. repeat rewrite fmap_app in n.
           apply not_elem_of_app in n as [Hl1 Hn1].
           apply not_elem_of_app in Hn1 as [Hl2 Hbc'].
           rewrite std_rel_update_multiple_lookup_same_i /std_rel /= in Hr';auto.
           2: { rewrite Heq4'. repeat rewrite fmap_app. repeat (apply not_elem_of_app;split;auto). }
           edestruct Hstd_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated2] ];[|eauto|]. 
           { rewrite std_rel_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
             destruct (decide (k ∈ encode <$> region_addrs b c)).
             - apply std_rel_update_multiple_lookup_std_i. rewrite Heq3'. revert e0;clear;set_solver. 
             - rewrite std_rel_update_multiple_lookup_same_i;[|rewrite Heq3';revert n Hl1;clear;set_solver].
               rewrite HstdW3;eauto. }
           assert (is_Some (Wstd_rel !! k)) as Hstd;eauto.
           apply HstdW1 in Hstd. rewrite Hstd in Hr; inversion Hr; subst.
           repeat split;auto.
           intros x0 y Hx0 Hy.
           assert (exists a : Addr, k = encode a) as [a Heqa].
           { destruct Hdom as [M Hdom]. destruct Hdom with k as [Hdom1 Hdom2]. 
             assert (is_Some (Wstd_sta !! k)) as Hsome; eauto.
             apply Hdom1 in Hsome as [a [Heqa _] ]. eauto. 
           }
           subst. 
           (* we have two more cases, either k is an element of the stack passed on to adv call 2, 
              or k was never a revoked element *)
           destruct (decide (a ∈ region_addrs c' e)). 
           ** (* k is an element of the stack and was revoked in W *)
             assert (Wstd_sta !! (encode a) = Some (encode Temporary)) as Htemp.
             { subst. 
               apply Hiff1. rewrite Heq1'. apply elem_of_app. right.
               rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr]. 
               apply elem_of_app. right. revert e0. clear. set_solver. 
             }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. repeat rewrite fmap_app. repeat (apply not_elem_of_app;split;auto). }
             destruct (decide (a ∈ region_addrs c e)) as [Hce | Hce]. 
             *** (* if k is in [c,e], we know its temporary by Hiff2 *)
               assert (Wstd_sta3 !! (encode a) = Some (encode Temporary)) as Htemp3.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. right. revert Hce;clear;set_solver. }
               subst. rewrite Htemp in Hx0. inversion Hx0; subst. apply Hrelated2; auto.
               apply close_list_std_sta_revoked. 
               { apply elem_of_list_fmap. repeat eexists. auto. }
               rewrite std_sta_update_multiple_lookup_same;auto. 
               2: { rewrite Heq4'. revert Hl1 Hl2 Hbc'. clear. set_solver. }
               (* if a is in [c,e] and [c',e],it cannot also be in [b,c] *)
               assert (a ∉ region_addrs b c) as Hbc.
               { destruct (decide (c < c')%a). 
                 - rewrite (region_addrs_split _ c) in Hbc';[|revert Hbounds1 l0;clear;solve_addr].
                   revert Hbc'; clear; set_solver.
                 - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                   destruct (decide (c = c'));[subst;revert Hbc';clear;set_solver|].
                   apply region_addrs_xor_elem_of with (c:=c) in e0;[|revert Hbounds1 Hle;clear;solve_addr]. 
                   rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                   apply not_elem_of_app;split;[revert Hbc';clear;set_solver|].
                   revert Hce e0;clear. set_solver. 
               } 
               rewrite std_sta_update_multiple_lookup_same;auto.
               2: { rewrite Heq3'. revert Hl1 Hbc. clear. set_solver. }
               rewrite /revoke /std_sta /=. apply revoke_lookup_Temp; auto.
             *** (* otherwise we must assert that it could have been revoked, then closed before the second call *)
               (* apply Hrelated2; auto. *)
               assert (Wstd_sta3 !! (encode a) ≠ Some (encode Temporary)) as Htemp3.
               { intros Hcontr. apply Hiff2 in Hcontr. subst. 
                 revert Hcontr. rewrite Heq2'. revert Hce Hl2. clear; intros. set_solver. }
               assert ((encode a) ∈ dom (gset positive) Wstd_sta3) as Hin3.
               { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_dom.
                 apply close_list_std_sta_is_Some.
                 apply std_sta_update_multiple_is_Some. 
                 rewrite -revoke_std_sta_lookup_Some. eauto. }
               apply elem_of_dom in Hin3 as [y3 Hy3].
               rewrite Hx0 in Htemp. inversion Htemp. subst.
               (* if a is in [c,e],it must also be in [b,c] *)
               assert (a ∈ region_addrs b c) as Hbc.
               { destruct (decide (c < c')%a). 
                 - rewrite (region_addrs_split _ c') in Hce;[|revert Hbounds2 l0;clear;solve_addr].
                   revert Hce e0; clear; set_solver.
                 - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                   rewrite (region_addrs_split _ c) in e0;[|revert Hbounds1 Hle;clear;solve_addr].
                   apply elem_of_app in e0 as [Hc'c | Hcontr];[|contradiction].
                   rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                   apply elem_of_app. by right. 
               }
               (* before the first call, the resource is set of Static *)
               assert (rtc (convert_rel std_rel_pub) (encode (Static m1)) y3) as Hrelated.
               { apply Hrelated1;auto. 
                 rewrite -close_list_std_sta_same;[|revert Hce;clear;set_solver].
                 apply std_sta_update_multiple_lookup_in. rewrite Heq3'. apply elem_of_app. by right. }
               (* we know that it stayed Static since y3 is not Temporary *)
               apply std_rel_pub_rtc_Static with (g:=m1) in Hrelated as [-> | ->];auto;[contradiction|].
               apply Hrelated2; auto.
               apply close_list_std_sta_revoked; [revert e0;clear;set_solver|].
               rewrite std_sta_update_multiple_lookup_same_i;auto. 
               2: { rewrite Heq4'. revert Hbc' Hl1 Hl2. clear. set_solver. }
               rewrite std_sta_update_multiple_lookup_in;auto.
               rewrite Heq3'. revert Hbc;clear;set_solver. 
           ** (* if k is never a revoked element, we can apply its transitions during the two future world relations *)
             assert ((encode a) ∈ dom (gset positive) Wstd_sta3) as Hin3.
             { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_dom.
               apply close_list_std_sta_is_Some.
               apply std_sta_update_multiple_is_Some. 
               rewrite -revoke_std_sta_lookup_Some. eauto. }
             apply elem_of_dom in Hin3 as [y3 Hy3].
             assert ((encode a) ∉ encode <$> region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ c'). revert Hbc' n. clear. set_solver.
               revert Hbounds2. clear. solve_addr. }
             assert ((encode a) ∉ encode <$> region_addrs b c) as Hbc.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             assert ((encode a) ∉ encode <$> region_addrs c e) as Hce.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. revert Hl1 Hl2 Hbc'. clear. set_solver. }
             trans y3. 
             *** apply Hrelated1; auto.
                 rewrite -close_list_std_sta_same; [|revert Hce;clear;set_solver].
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver].
                 rewrite revoke_monotone_lookup_same;auto.
                 intros Hcontr. subst. apply Hiff1 in Hcontr. revert Hcontr. rewrite Heq1' =>Hcontr.
                 revert Hcontr Hl1 Hbe;clear;set_solver.
             *** apply Hrelated2;auto. 
                 rewrite -close_list_std_sta_same; [|revert n;clear;set_solver]. 
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver].
                 rewrite revoke_monotone_lookup_same;auto.
                 intros Hcontr. apply Hiff2 in Hcontr. revert Hcontr. rewrite Heq2' =>Hcontr.
                 revert Hcontr Hl1 Hl2 Hce;clear;set_solver.
     - (* owned resources *)
       destruct Hrelated1 as [_ Hloc_related1]. 
       destruct Hrelated2 as [_ Hloc_related2]. simpl in *. 
       destruct Hloc_related2 as [Hloc_sta_dom2 [Hloc_rel_dom2 Hloc_related2] ].
       destruct Hloc_related1 as [Hloc_sta_dom1 [Hloc_rel_dom1 Hloc_related1] ].
       split;[|split].
       + rewrite std_update_multiple_loc_sta /=.
         etrans;[|apply Hloc_sta_dom2]. repeat rewrite std_update_multiple_loc_sta /=.
         trans (dom (gset positive) W3.2.1);[|rewrite dom_insert_L;clear;set_solver].
         etrans;[|apply Hloc_sta_dom1]. rewrite std_update_multiple_loc_sta /=.
         rewrite dom_insert_L;clear;set_solver. 
       + rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom2]. 
         repeat rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom1].
         by rewrite std_update_multiple_loc_rel /=.
       + rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /=.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related2.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related1.
         destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
         destruct W3 as [ [Wstd_sta3 Wstd_rel3] [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ [Wstd_sta6 Wstd_rel6] [Wloc_sta6 Wloc_rel6] ].
         simpl in *. 
         intros k r1 r2 r1' r2' Hr Hr'.
         assert (is_Some (Wloc_rel3 !! k)) as [ [s1 s2] Hs].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hloc_rel_dom1; apply Hloc_rel_dom1.
           assert (k ∈ dom (gset positive) Wloc_rel) as Hin;[apply elem_of_gmap_dom;eauto|].
           rewrite std_update_multiple_loc_rel. auto. }
         edestruct Hloc_related1 with (i0:=k) as [Heq1 [Heq2 Hrelated] ];[eauto|eauto|subst]. 
         edestruct Hloc_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated'] ];[eauto|eauto|subst]. 
         repeat split;auto. intros x0 y Hx0 Hy. 
         assert (is_Some (Wloc_sta3 !! k)) as [y3 Hy3].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hloc_sta_dom1; apply Hloc_sta_dom1.
           assert (k ∈ dom (gset positive) Wloc_sta) as Hin;[apply elem_of_gmap_dom;eauto|].
           rewrite std_update_multiple_loc_sta. 
           repeat rewrite dom_insert_L. revert Hin. clear. set_solver. }
         destruct (decide (i = k));[subst|].
         * rewrite Hawk in Hr. inversion Hr; subst.           
           rewrite lookup_insert in Hrelated. rewrite lookup_insert in Hrelated'.
           rewrite Hawki in Hx0. inversion Hx0;subst.
           destruct x;[apply Hrelated'; auto|].
           etrans;[|apply Hrelated']; auto. right with (encode true);[|left].
           exists false,true. repeat split;auto. by constructor. 
         * rewrite lookup_insert_ne in Hrelated;auto. rewrite lookup_insert_ne in Hrelated';auto.
           etrans;[apply Hrelated|apply Hrelated']; eauto.
   Qed.

   Lemma related_pub_local_4 W W' W3 W6 b e l l' l1 l2 m1 m2 i c c' :
     W' = ((revoke_std_sta W.1.1,W.1.2),(<[i:=encode false]> W.2.1,W.2.2))
     -> (b <= c < e)%a ∧ (b <= c' < e)%a
     (* as a technicality, we need to be able to know that if i is in the domain of the states in W, 
        then it will also be in the domain of relations in W *)
     -> dom (gset positive) (std_sta W) ⊆ dom (gset positive) (std_rel W)
     (* dom_equal, so that we know that positives in W6 are encoded addresses *)
     -> (exists M, dom_equal (std_sta W3) M)
     (* l is the list of all revoked resources in W *)
     -> (forall a : Addr, W.1.1 !! (encode a) = Some (encode Temporary) <-> a ∈ l)
     (* l' is the list of all addition revoked resources in W3 (other than [c,e)) *)
     -> (forall a : Addr, W3.1.1 !! (encode a) = Some (encode Temporary) <-> a ∈ l')
     (* m1 and m2 are the maps containing the local frame and the rest of the temporary resources *)
     -> (l ≡ₚl1 ++ (region_addrs b e) ∧ l' ≡ₚl2 ++ (region_addrs c e) ∧
        elements (dom (gset Addr) m1) ≡ₚl1 ++ (region_addrs b c)
        ∧ elements (dom (gset Addr) m2) ≡ₚl1 ++ l2 ++ (region_addrs b c'))
     (* i is the awkward invariant *)
     → W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)
     -> (∃ (b : bool), W.2.1 !! i = Some (encode b))
     (* all worlds are standard *)
     -> rel_is_std W ∧ rel_is_std W3 ∧ rel_is_std W6
     → related_sts_pub_world
         (close_list (encode <$> region_addrs c e)
                     (std_update_multiple
                        (revoke (W.1,((<[i:=encode false]> W.2.1), W.2.2)))
                     (elements (dom (gset Addr) m1))
                     (Static m1))) W3
     → related_sts_pub_world
         (close_list (encode <$> region_addrs c' e)
                     (std_update_multiple
                        (std_update_multiple
                           (revoke (W3.1, ((<[i:=encode true]> W3.2.1), W3.2.2)))
                           (elements (dom (gset Addr) m1))
                           Revoked)
                     (elements (dom (gset Addr) m2))
                     (Static m2))) W6
     → related_sts_pub_world W3 (std_update_temp_multiple W6 (elements (dom (gset Addr) m2))).
   Proof.
     intros Heq [Hbounds1 Hbounds2] HsubW Hdom3 Hiff1 Hiff2 Happ Hawk [x Hawki] (HstdW1 & HstdW3 & HstdW6)
            Hrelated1 Hrelated2. 
     subst W'.
     simpl in *.
     split; simpl. 
     - (* standard resources *)
       destruct Hrelated1 as [Hstd_related1 _]. 
       destruct Hrelated2 as [Hstd_related2 _]. simpl in *. 
       destruct Hstd_related2 as [Hstd_sta_dom2 [Hstd_rel_dom2 Hstd_related2] ].
       destruct Hstd_related1 as [Hstd_sta_dom1 [Hstd_rel_dom1 Hstd_related1] ].
       assert (dom (gset positive) (std_sta W3) ⊆ dom (gset positive) (std_sta W6)) as Hsub.
       { etrans;[|apply Hstd_sta_dom2].
         rewrite -close_list_dom_eq. 
         repeat (etrans;[|apply std_update_multiple_sta_dom_subseteq]).
         rewrite -revoke_dom_eq. done. 
       }
       assert (dom (gset positive) (std_rel W3) ⊆ dom (gset positive) (std_rel W6)) as Hsub'.
       { etrans;[|apply Hstd_rel_dom2].
         repeat (etrans;[|apply std_update_multiple_rel_dom_subseteq]). auto. 
       }
       split;[|split].
       + etrans;[|apply std_update_multiple_sta_dom_subseteq]. auto. 
       + etrans;[|apply std_update_multiple_rel_dom_subseteq]. auto. 
       + intros k r1 r2 r1' r2' Hr Hr'.
         destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
         destruct W3 as [ [Wstd_sta3 Wstd_rel3] [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ [Wstd_sta6 Wstd_rel6] [Wloc_sta6 Wloc_rel6] ].
         simpl in *.
         (* assert (is_Some (Wstd_rel3 !! k)) as [ [s1 s2] Hs]. *)
         (* { apply elem_of_gmap_dom. apply elem_of_subseteq in Hstd_rel_dom1. apply Hstd_rel_dom1.  *)
         (*   assert (k ∈ dom (gset positive) Wstd_rel) as Hin;[apply elem_of_gmap_dom;eauto|auto]. *)
         (*   eapply elem_of_subseteq;[|apply Hin]. rewrite -elem_of_subseteq. *)
         (*   etrans;[|apply std_update_multiple_rel_dom_subseteq]. auto.  *)
         (* } *)
         (* edestruct Hstd_related1 with (i0:=k) as [Heqrs1 [Heqrs2 Hrelated1] ];[|eauto|].  *)
         (* { rewrite -std_update_multiple_std_rel_eq; eauto. } *)
         destruct (decide (k ∈ encode <$> l1 ++ l2 ++ (region_addrs b c'))).
         * (* k is a revoked element, which is updated to static at the end *)
           apply elem_of_list_fmap in e0 as [a [Ha e0] ]. subst. 
           assert (is_Some (Wstd_rel6 !! (encode a))) as [ [r6 r6'] Hr6].
           { apply elem_of_gmap_dom. apply elem_of_subseteq in Hsub'; apply Hsub'. apply elem_of_gmap_dom;eauto. }
           destruct Happ as (Heq1' & Heq2' & Heq3' & Heq4'). 
           edestruct Hstd_related2 with (i0:=encode a) as [Heq1 [Heq2 Hrelated2] ];[|eauto|].
           { rewrite std_rel_update_multiple_lookup_std_i;auto. apply elem_of_list_fmap. repeat eexists. by rewrite Heq4'. }
           rewrite std_rel_update_multiple_lookup_std_i in Hr';auto.
           2: { apply elem_of_list_fmap. repeat eexists. rewrite Heq4'. auto. }
           inversion Hr';subst.
           assert (is_Some (Wstd_rel3 !! (encode a))) as Hsome;eauto.
           apply HstdW3 in Hsome. rewrite Hsome in Hr.
           inversion Hr; subst.
           repeat split;auto.
           intros x0 y Hx0 Hy. rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
           2: { apply elem_of_list_fmap. repeat eexists. rewrite Heq4'. auto. }
           inversion Hy; subst.
           (* apply elem_of_list_fmap in e0 as [a [Heqa e0] ]. subst. *)
           apply elem_of_app in e0 as [Hl1 | Hl']. 
           ** (* k is a revoked element in l1 *)
             assert (Wstd_sta !! (encode a) = Some (encode Temporary)) as Htemp.
             { apply Hiff1. rewrite Heq1'. apply elem_of_app. by left. }
             assert (is_Some (Wstd_rel !! (encode a))) as [ [r1 r1'] Hr1].
             { apply elem_of_gmap_dom. apply elem_of_subseteq in HsubW. apply HsubW. apply elem_of_gmap_dom. eauto. }
             edestruct Hstd_related1 with (i0:=encode a) as [Heqr1 [Heqr2 Hrelated1] ];[|eauto|].
             { rewrite -std_update_multiple_std_rel_eq; eauto. }
             (* in this case x0 is either Temporary or Static *)
             assert (rtc r1 (encode (Static m1)) x0) as Hrtc.
             { apply Hrelated1;auto.
               rewrite -close_list_std_sta_same_alt.
               - apply std_sta_update_multiple_lookup_in. rewrite Heq3'. revert Hl1;clear;set_solver.
               - rewrite std_sta_update_multiple_lookup_in;[|rewrite Heq3';revert Hl1;clear;set_solver].
                 intros Hcontr. inversion Hcontr as [Heq]. apply encode_inj in Heq. done. 
             }
             subst. 
             apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->]. 
             left. right with (encode Temporary);[|left].
             repeat eexists. constructor. auto. 
           ** (* k is a either revoked element in l2 or [b,c'] *)
             apply elem_of_app in Hl' as [Hl2 | Hbc']. 
             *** (* k is a revoked element in l2 *)
               assert (Wstd_sta3 !! (encode a) = Some (encode Temporary)) as Htemp.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. by left. }
               (* if x0 is temp we are done *)
               rewrite Htemp in Hx0. inversion Hx0. left. 
             *** (* k is a revoked element in [b,c'] *)
               assert (a ∈ region_addrs b e) as Hbe.
               { rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr].
                 apply elem_of_app. by left. }
               assert (Wstd_sta !! (encode a) = Some (encode Temporary)) as Htemp.
               { apply Hiff1. rewrite Heq1'. apply elem_of_app. by right. }
               assert (is_Some (Wstd_rel !! (encode a))) as [ [r1 r1'] Hr1].
               { apply elem_of_gmap_dom. apply elem_of_subseteq in HsubW. apply HsubW. apply elem_of_gmap_dom. eauto. }
               edestruct Hstd_related1 with (i0:=encode a) as [Heqr1 [Heqr2 Hrelated1] ];[|eauto|].
               { rewrite -std_update_multiple_std_rel_eq; eauto. }
               destruct (decide (a ∈ l1 ++ region_addrs b c)). 
               **** (* a was static during the first call *)
                 assert (rtc r1 (encode (Static m1)) x0) as Hrtc.
                 { apply Hrelated1;auto.
                   rewrite -close_list_std_sta_same_alt.
                   - apply std_sta_update_multiple_lookup_in. rewrite Heq3'. revert e0;clear;set_solver.
                   - rewrite std_sta_update_multiple_lookup_in;[|rewrite Heq3';revert e0;clear;set_solver].
                     intros Hcontr. inversion Hcontr as [Heq]. apply encode_inj in Heq. done. 
                 }
                 subst. 
                 apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->]. 
                 left. right with (encode Temporary);[|left].
                 repeat eexists. constructor. auto. 
               **** (* a was temporary during the first call *)
                 assert (a ∈ region_addrs c e) as Hce.
                 { rewrite (region_addrs_split _ c) in Hbe;[|revert Hbounds1;clear;solve_addr].
                   revert n Hbe;clear;set_solver. }
                 assert (rtc r1 (encode Temporary) x0) as Hrtc.
                 { apply Hrelated1;auto.
                   apply close_list_std_sta_revoked;[revert Hce;clear;set_solver|].
                   rewrite std_sta_update_multiple_lookup_same;[|rewrite Heq3';auto].
                   apply revoke_lookup_Temp. auto. 
                 } subst. 
                 apply std_rel_pub_rtc_Temporary in Hrtc as ->;auto. left. 
         * destruct Happ as [Heq1' [Heq2' [Heq3' Heq4'] ] ]. repeat rewrite fmap_app in n.
           apply not_elem_of_app in n as [Hl1 Hn1].
           apply not_elem_of_app in Hn1 as [Hl2 Hbc'].
           rewrite std_rel_update_multiple_lookup_same_i /std_rel /= in Hr';auto.
           2: { rewrite Heq4'. repeat rewrite fmap_app. repeat (apply not_elem_of_app;split;auto). }
           edestruct Hstd_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated2] ];[|eauto|]. 
           { rewrite std_rel_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
             destruct (decide (k ∈ encode <$> region_addrs b c)).
             - apply std_rel_update_multiple_lookup_std_i. rewrite Heq3'. revert e0;clear;set_solver. 
             - rewrite std_rel_update_multiple_lookup_same_i;[|rewrite Heq3';revert n Hl1;clear;set_solver].
               rewrite HstdW3;eauto. } subst. 
           assert (is_Some (Wstd_rel3 !! k)) as Hstd;eauto.
           apply HstdW3 in Hstd. rewrite Hstd in Hr; inversion Hr; subst.
           repeat split;auto.
           intros x0 y Hx0 Hy.
           assert (exists a : Addr, k = encode a) as [a Heqa].
           { destruct Hdom3 as [M Hdom]. destruct Hdom with k as [Hdom1 Hdom2]. 
             assert (is_Some (Wstd_sta3 !! k)) as Hsome; eauto.
             apply Hdom in Hsome as [a [Heqa _] ]. eauto. 
           }
           subst. 
           (* we have two more cases, either k is an element of the stack passed on to adv call 2, 
              or k was never a revoked element *)
           destruct (decide (a ∈ region_addrs c' e)). 
           ** (* k is an element of the stack and was revoked in W *)
             assert (Wstd_sta !! (encode a) = Some (encode Temporary)) as Htemp.
             { apply Hiff1. rewrite Heq1'. apply elem_of_app. right.
               rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr]. 
               apply elem_of_app. right. revert e0. clear. set_solver. 
             }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. repeat rewrite fmap_app. repeat (apply not_elem_of_app;split;auto). }
             assert (is_Some (Wstd_rel !! (encode a))) as [ [r1 r1'] Hr1].
             { apply elem_of_gmap_dom. apply elem_of_subseteq in HsubW. apply HsubW. apply elem_of_gmap_dom. eauto. }
             edestruct Hstd_related1 with (i0:=encode a) as [Heqr1 [Heqr2 Hrelated1] ];[|eauto|].
             { rewrite -std_update_multiple_std_rel_eq; eauto. }
             destruct (decide (a ∈ region_addrs c e)) as [Hce | Hce]. 
             *** (* if k is in [c,e], we know its temporary by Hiff2 *)
               assert (Wstd_sta3 !! (encode a) = Some (encode Temporary)) as Htemp3.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. right. revert Hce;clear;set_solver. }
               rewrite Htemp3 in Hx0. inversion Hx0; subst. apply Hrelated2; auto.
               apply close_list_std_sta_revoked;[revert e0;clear;set_solver|]. 
               rewrite std_sta_update_multiple_lookup_same;auto. 
               2: { rewrite Heq4'. revert Hl1 Hl2 Hbc'. clear. set_solver. }
               (* if a is in [c,e] and [c',e],it cannot also be in [b,c] *)
               assert (a ∉ region_addrs b c) as Hbc.
               { destruct (decide (c < c')%a). 
                 - rewrite (region_addrs_split _ c) in Hbc';[|revert Hbounds1 l0;clear;solve_addr].
                   revert Hbc'; clear; set_solver.
                 - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                   destruct (decide (c = c'));[subst;revert Hbc';clear;set_solver|].
                   apply region_addrs_xor_elem_of with (c:=c) in e0;[|revert Hbounds1 Hle;clear;solve_addr]. 
                   rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                   apply not_elem_of_app;split;[revert Hbc';clear;set_solver|].
                   revert Hce e0;clear. set_solver. 
               } 
               rewrite std_sta_update_multiple_lookup_same;auto.
               2: { rewrite Heq3'. revert Hl1 Hbc. clear. set_solver. }
               rewrite /revoke /std_sta /=. apply revoke_lookup_Temp; auto.
             *** (* otherwise we must assert that it could have been revoked, then closed before the second call *)
               (* apply Hrelated2; auto. *)
               assert (Wstd_sta3 !! (encode a) ≠ Some (encode Temporary)) as Htemp3.
               { intros Hcontr. apply Hiff2 in Hcontr. subst. 
                 revert Hcontr. rewrite Heq2'. revert Hce Hl2. clear; intros. set_solver. }
               (* if a is not in [c,e],it must also be in [b,c] *)
               assert (a ∈ region_addrs b c) as Hbc.
               { destruct (decide (c < c')%a). 
                 - rewrite (region_addrs_split _ c') in Hce;[|revert Hbounds2 l0;clear;solve_addr].
                   revert Hce e0; clear; set_solver.
                 - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                   rewrite (region_addrs_split _ c) in e0;[|revert Hbounds1 Hle;clear;solve_addr].
                   apply elem_of_app in e0 as [Hc'c | Hcontr];[|contradiction].
                   rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                   apply elem_of_app. by right. 
               }
               (* before the first call, the resource is set of Static *)
               subst. 
               assert (rtc (convert_rel std_rel_pub) (encode (Static m1)) x0) as Hrelated.
               { apply Hrelated1;auto. 
                 rewrite -close_list_std_sta_same;[|revert Hce;clear;set_solver].
                 apply std_sta_update_multiple_lookup_in. rewrite Heq3'. apply elem_of_app. by right. }
               assert (rtc (convert_rel std_rel_pub) (encode Temporary) y) as Hrelated'.
               { apply Hrelated2;auto. 
                 apply close_list_std_sta_revoked;[revert e0;clear;set_solver|]. 
                 rewrite std_sta_update_multiple_lookup_same;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
                 apply std_sta_update_multiple_lookup_in. rewrite Heq3'. revert Hbc;clear;set_solver. }
               apply std_rel_pub_rtc_Temporary in Hrelated' as ->;auto.
               apply std_rel_pub_rtc_Static with (g:=m1) in Hrelated as [-> | ->];auto;[left|].
               right with (encode Temporary);[|left].
               repeat eexists. constructor. 
           ** (* if k is never a revoked element, we can apply its transitions during the second future world relations *)
             assert ((encode a) ∉ encode <$> region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ c'). revert Hbc' n. clear. set_solver.
               revert Hbounds2. clear. solve_addr. }
             assert ((encode a) ∉ encode <$> region_addrs b c) as Hbc.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             assert ((encode a) ∉ encode <$> region_addrs c e) as Hce.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. revert Hl1 Hl2 Hbc'. clear. set_solver. }
             apply Hrelated2;auto. 
             rewrite -close_list_std_sta_same; [|revert n;clear;set_solver]. 
             rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
             rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver].
             rewrite revoke_monotone_lookup_same;auto.
             intros Hcontr. apply Hiff2 in Hcontr. revert Hcontr. rewrite Heq2' =>Hcontr.
             revert Hcontr Hl1 Hl2 Hce;clear;set_solver.
     - (* owned resources *)
       destruct Hrelated1 as [_ Hloc_related1]. 
       destruct Hrelated2 as [_ Hloc_related2]. simpl in *. 
       destruct Hloc_related2 as [Hloc_sta_dom2 [Hloc_rel_dom2 Hloc_related2] ].
       destruct Hloc_related1 as [Hloc_sta_dom1 [Hloc_rel_dom1 Hloc_related1] ].
       split;[|split].
       + repeat rewrite std_update_multiple_loc_sta /=.
         etrans;[|apply Hloc_sta_dom2]. repeat rewrite std_update_multiple_loc_sta /=.
         rewrite dom_insert_L;clear;set_solver. 
       + rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom2]. 
         repeat rewrite std_update_multiple_loc_rel /=. auto. 
       + rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /=.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related2.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related1.
         destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
         destruct W3 as [ [Wstd_sta3 Wstd_rel3] [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ [Wstd_sta6 Wstd_rel6] [Wloc_sta6 Wloc_rel6] ].
         simpl in *. 
         intros k r1 r2 r1' r2' Hr Hr'.
         edestruct Hloc_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated'] ];[eauto|eauto|subst]. 
         repeat split;auto. intros x0 y Hx0 Hy. 
         destruct (decide (i = k));[subst|].
         * edestruct Hloc_related1 with (i:=k) as [Heq1 [Heq2 Hrelated] ];[eauto|eauto|subst].
           apply Hrelated with (x:=encode false) in Hx0;[|apply lookup_insert].
           apply Hrelated' with (x:=encode true) in Hy;[|apply lookup_insert].
           apply rtc_rel_pub_false in Hx0 as [-> | ->];auto.
           apply rtc_rel_pub in Hy as ->;auto.
           right with (encode true);[|left].
           repeat eexists. constructor. auto.  
         * (* we distinguish between the case where k exists i W, or allocated in W3 *)
           rewrite lookup_insert_ne in Hrelated';auto.           
   Qed.
         

  Lemma registers_mapsto_resources pc_w stk_w rt0_w adv_w pc_w' :
    ([∗ list] r_i ∈ list_difference all_registers [PC; r_stk; r_t0; r_adv], r_i ↦ᵣ inl 0%Z)
      -∗ r_stk ↦ᵣ stk_w
      -∗ r_t0 ↦ᵣ rt0_w
      -∗ r_adv ↦ᵣ adv_w
      -∗ PC ↦ᵣ pc_w' -∗
     registers_mapsto (<[PC:=pc_w']> (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z))))))). 
  Proof.
    iIntros "Hgen_reg Hr_stk Hr_t0 Hr_adv HPC".
    rewrite /registers_mapsto (insert_insert _ PC).
    iApply (big_sepM_insert_2 with "[HPC]"); first iFrame.
    iApply (big_sepM_insert_2 with "[Hr_stk]"); first iFrame.
    iApply (big_sepM_insert_2 with "[Hr_t0]"); first iFrame.
    iApply (big_sepM_insert_2 with "[Hr_adv]"); first iFrame.
    assert ((list_difference all_registers [PC; r_stk; r_t0; r_adv]) =
            [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12;
             r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24;
             r_t25; r_t26; r_t27; r_t29; r_t30]) as ->; first auto. 
    rewrite /create_gmap_default. iSimpl in "Hgen_reg". 
    repeat (iDestruct "Hgen_reg" as "[Hr Hgen_reg]";
            iApply (big_sepM_insert_2 with "[Hr]"); first iFrame).
    done.
  Qed.

  Lemma r_full (pc_w stk_w rt0_w adv_w : Word) :
    full_map (Σ:=Σ) (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
  Proof.
    iIntros (r0).
    iPureIntro.
    assert (r0 ∈ all_registers); [apply all_registers_correct|].
    destruct (decide (r0 = PC)); [subst;rewrite lookup_insert; eauto|]. 
    rewrite lookup_insert_ne;auto.
    destruct (decide (r0 = r_stk)); [subst;rewrite lookup_insert; eauto|]. 
    rewrite lookup_insert_ne;auto.
    destruct (decide (r0 = r_t0)); [subst;rewrite lookup_insert; eauto|]. 
    rewrite lookup_insert_ne;auto.
    destruct (decide (r0 = r_adv)); [subst;rewrite lookup_insert; eauto|].
    rewrite lookup_insert_ne;auto.
    assert (¬ r0 ∈ [PC; r_stk; r_t0; r_adv]).
    { repeat (apply not_elem_of_cons; split; auto). apply not_elem_of_nil. }
    exists (inl 0%Z).
    apply create_gmap_default_lookup. apply elem_of_list_difference. auto.
  Qed.

  Lemma r_zero (pc_w stk_w rt0_w adv_w : Word) r1 :
    r1 ≠ r_stk → r1 ≠ PC → r1 ≠ r_t0 → r1 ≠ r_adv →
    (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))) !r! r1 = inl 0%Z.
  Proof.
    intros Hr_stk HPC Hr_t0 Hr_t30. rewrite /RegLocate.
    destruct (<[PC:=pc_w]>
              (<[r_stk:=stk_w]>
               (<[r_t0:=rt0_w]>
                (<[r_adv:=adv_w]> (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv])
                                                       (inl 0%Z)))))
                !! r1) eqn:Hsome; rewrite Hsome; last done.
    do 4 (rewrite lookup_insert_ne in Hsome;auto).
    assert (Some s = Some (inl 0%Z)) as Heq.
    { rewrite -Hsome. apply create_gmap_default_lookup.
      apply elem_of_list_difference. split; first apply all_registers_correct.
      repeat (apply not_elem_of_cons;split;auto).
      apply not_elem_of_nil. 
    } by inversion Heq. 
  Qed.     

  (* The validity of adversary region is monotone wrt private future worlds *)
  Lemma adv_monotone W W' b e :
    related_sts_priv_world W W' →
    rel_is_std W ->
    (([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std_sta W !! encode a = Some (encode Permanent)⌝ ∧ ⌜region_std W a⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std_sta W' !! encode a = Some (encode Permanent)⌝ ∧ ⌜region_std W' a⌝))%I.
  Proof.
    iIntros (Hrelated Hstd) "Hr".
    iApply (big_sepL_mono with "Hr").
    iIntros (k y Hsome) "(Hy & Hperm & Hstd)". 
    iFrame.
    iDestruct "Hperm" as %Hperm.
    iDestruct "Hstd" as %region_std. 
    iPureIntro; split. 
    - apply (region_state_nwl_monotone_nl _ W') in Hperm; auto.
    - apply (related_sts_preserve_std W); auto. eauto.
  Qed.

  Lemma adv_stack_monotone W W' b e :
    related_sts_pub_world W W' ->
    rel_is_std W ->
    (([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                     ∧ ⌜region_state_pwl W a⌝ ∧ ⌜region_std W a⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                       ∧ ⌜region_state_pwl W' a⌝ ∧ ⌜region_std W' a⌝))%I.
  Proof.
    iIntros (Hrelated Hstd) "Hstack_adv". 
    iApply (big_sepL_mono with "Hstack_adv").
    iIntros (k y Hsome) "(Hr & Htemp & Hstd)".
    iDestruct "Htemp" as %Htemp. iDestruct "Hstd" as %Hstd'. 
    iFrame. iPureIntro; split.
    - apply (region_state_pwl_monotone _ W') in Htemp; auto.
    - apply (related_sts_preserve_std W); auto; [|eauto].
      apply related_sts_pub_priv_world. auto. 
  Qed. 

  (* Helper lemma about private future worlds *)
  (* TODO: move this in sts? *)
  Lemma related_sts_priv_world_std_sta_is_Some W W' i :
    related_sts_priv_world W W' -> is_Some ((std_sta W) !! i) -> is_Some ((std_sta W') !! i).
  Proof.
    intros [ [Hdom1 [_ _] ] _] Hsome.
    apply elem_of_gmap_dom in Hsome.
    apply elem_of_gmap_dom.
    apply elem_of_subseteq in Hdom1. auto.
  Qed.

  Lemma related_sts_priv_world_std_rel_is_Some W W' i :
    related_sts_priv_world W W' -> is_Some ((std_rel W) !! i) -> is_Some ((std_rel W') !! i).
  Proof.
    intros [ [_ [Hdom1 _] ] _] Hsome.
    apply elem_of_gmap_dom in Hsome.
    apply elem_of_gmap_dom.
    apply elem_of_subseteq in Hdom1. auto.
  Qed.

  Lemma related_sts_priv_world_std_sta_region_type W W' (i : positive) (ρ : region_type) :
    related_sts_priv_world W W' ->
    (std_sta W) !! i = Some (encode ρ) ->
    rel_is_std_i W i ->
    ∃ (ρ' : region_type), (std_sta W') !! i = Some (encode ρ').
  Proof.
    intros Hrelated Hρ Hrel.
    assert (is_Some ((std_sta W') !! i)) as [x Hx].
    { apply related_sts_priv_world_std_sta_is_Some with W; eauto. }
    assert (is_Some ((std_rel W') !! i)) as [r Hr].
    { apply related_sts_priv_world_std_rel_is_Some with W; eauto. }
    destruct Hrelated as [ [Hdom1 [Hdom2 Hrevoked] ] _].
    destruct r as [r1 r2]. 
    specialize (Hrevoked i _ _ _ _ Hrel Hr) as [Heq1 [Heq2 Hrelated] ].
    specialize (Hrelated _ _ Hρ Hx). simplify_eq. 
    apply std_rel_exist in Hrelated as [ρ' Hρ'];[|eauto]. simplify_eq.
    eauto. 
  Qed.
  
  (* Shorthand definition for an adress being currently temporary/revoked *)
  Definition region_type_revoked W (a : Addr) :=
    (std_sta W) !! (encode a) = Some (encode Revoked).
  Definition region_type_temporary W (a : Addr) :=
    (std_sta W) !! (encode a) = Some (encode Temporary).

  (* TODO: move *)
  Definition mapsto_nO (a: Addr) (p: Perm) (w: Word) := (a ↦ₐ[p] w ∗ ⌜p ≠ O⌝)%I.
  Notation "a ↦ₐ < p > w" := (mapsto_nO a p w)
    (at level 20, p at level 50, format "a  ↦ₐ < p >  w") : bi_scope.

  Lemma region_mapsto_to_nO (b e: Addr) (p: Perm) (ws: list Word) :
    p ≠ O →
    [[b,e]] ↦ₐ [p] [[ws]] -∗
    ([∗ list] k↦a;w ∈ (region_addrs b e);ws, a ↦ₐ<p> w)%I.
  Proof.
    intros. rewrite /region_mapsto. iIntros "H".
    iApply (big_sepL2_mono with "H"). intros. cbn. rewrite /mapsto_nO. eauto.
  Qed.

   (* the following spec is for the f4 subroutine of the awkward example, jumped to after dynamically allocating into r_env *)
  Lemma f4_spec W pc_p pc_g pc_b pc_e (* PC *)
        b e a (* adv *)
        g_ret b_ret e_ret a_ret (* return cap *)
        f4_addrs (* f2 *)
        d d' i (* dynamically allocated memory given by preamble, connected to invariant i *)
        a_first a_last (* special adresses *) 
        (b_r e_r b_r' : Addr) (* stack *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between f4_addrs a_first a_last ->
    
    (* Stack assumptions *)
    (0%a ≤ e_r)%Z ∧ (0%a ≤ b_r)%Z -> (* this assumption will not be necessary once addresses are finite *)
    region_size b_r e_r > 11 -> (* we must assume the stack is large enough for needed local state *)
    (b_r' + 1)%a = Some b_r ->

    (* malloc'ed memory assumption *)
    (d + 1)%a = Some d' ->
    
    (* Finally, we must assume that the stack is currently in a temporary state *)
    (* (forall (a : Addr), W.1.1 !! (encode a) = Some (encode Temporary) <-> a ∈ (region_addrs b_r e_r)) -> *)
    Forall (λ a, region_type_temporary W a ∧ rel_is_std_i W (encode a)) (region_addrs b_r e_r) ->

    {{{ r_stk ↦ᵣ inr ((RWLX,Local),b_r,e_r,b_r')
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ inr ((E,g_ret),b_ret,e_ret,a_ret) (* for now we say it's an enter cap. We will need to generalize to all words *)
      ∗ r_adv ↦ᵣ inr ((E,Global),b,e,a)
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r_adv;r_t0;r_env]; wsr, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (awk_inv i d))
      ∗ sts_rel_loc i awk_rel_pub awk_rel_priv
      (* stack *)
      ∗ ([∗ list] a ∈ (region_addrs b_r e_r), rel a RWLX (λ Wv : prodO STS STS * Word, (interp Wv.1) Wv.2))
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv code *)
      ∗ ([∗ list] a ∈ (region_addrs b e), (read_write_cond a RX interp) ∧ ⌜region_state_nwl W a Global⌝ ∧ ⌜region_std W a⌝)
      (* callback validity *)
      ∗ interp W (inr ((E,g_ret),b_ret,e_ret,a_ret))
      (* trusted code *)
      ∗ awkward_example f4_addrs pc_p r_adv 65
      (* we start out with arbitrary sts *)
      ∗ sts_full_world sts_std W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r W', full_map r ∧ registers_mapsto r
                         ∗ ⌜related_sts_priv_world W W'⌝
                         ∗ na_own logrel_nais ⊤                           
                         ∗ sts_full_world sts_std W'
                         ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hf2 Hbounds Hsize Hb_r' Hd Htemp φ)
            "(Hr_stk & HPC & Hr_t0 & Hr_adv & Hr_env & Hgen_reg & #Hι & #Hrel & #Hstack_val & Hna & #Hadv_val & #Hcallback & Hprog & Hsts & Hr) Hφ".
    (* We put the code in a non atomic invariant for each iteration of the program *)
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"prog") with "Hprog") as "#Hf4".
    (* Now we step through the program *)
    iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls)";[auto..|]. 
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct (f4_addrs);[inversion Hprog_length|].
    iDestruct "Hι" as (ι) "Hinv". 
    (* We will now need to open the invariant for d. 
       We do not know which state d is in, and may need to 
       do a private transition from 1 to 0! For that reason 
       we will first revoke region, so that we can do private 
       updates to it. We do not care about the stack resources, 
       as it currently in the revoked state. 
     *)
    iAssert (⌜dom (gset positive) (std_sta W) ⊆ dom (gset positive) (std_rel W)⌝)%I as %Hsub.
    { rewrite /sts_full_world /sts_full_std. iDestruct "Hsts" as "((% & _) & _)". auto. }
    iDestruct (sts_full_world_std with "Hsts") as %Hstd.
    iAssert (⌜exists M, dom_equal (std_sta W) M⌝)%I as %Hdom.
    { rewrite region_eq /region_def. iDestruct "Hr" as (M Mρ) "(_ & % & _)". eauto. }
    assert (Hdom_copy := Hdom). 
    apply extract_temps_split with (l:=region_addrs b_r e_r) in Hdom as [l' [Hdup Hiff] ];
      [|apply NoDup_ListNoDup,region_addrs_NoDup|apply Forall_and in Htemp as [Htemp _];apply Htemp].
    iMod (monotone_revoke_keep_some W _ (region_addrs b_r e_r) with "[$Hsts $Hr]") as "[Hsts [Hr [Hrest Hstack] ] ]";[apply Hdup|..].
    { iSplit.
      - iApply big_sepL_forall. iPureIntro. intros n. simpl. intros x Hsome. apply Hiff. apply elem_of_app; left.
        apply elem_of_list_lookup. eauto. 
      - iApply (big_sepL_mono with "Hstack_val"). iIntros (k y Hk) "Hrel". iFrame. iPureIntro.
        revert Htemp; rewrite Forall_forall =>Htemp. apply Htemp. apply elem_of_list_lookup. eauto. }
    iAssert ((▷ ∃ ws, [[b_r, e_r]]↦ₐ[RWLX][[ws]])
               ∗ ⌜Forall (λ a : Addr, region_type_revoked (revoke W) a ∧ rel_is_std_i (revoke W) (encode a)) (region_addrs b_r e_r)⌝)%I
      with "[Hstack]" as "[>Hstack #Hrevoked]".
    { iDestruct (big_sepL_sep with "Hstack") as "[Hstack #Hrevoked]".
      iDestruct (big_sepL_forall with "Hrevoked") as %Hrevoked. iSplit;[|iPureIntro].
      - iDestruct (big_sepL_sep with "Hstack") as "[Hstack _]". iNext. 
        iDestruct (region_addrs_exists with "Hstack") as (ws) "Hstack".
        iDestruct (big_sepL2_sep with "Hstack") as "[_ Hstack]".
        iDestruct (big_sepL2_sep with "Hstack") as "[Hstack _]". iExists ws. iFrame.
      - revert Htemp; repeat (rewrite Forall_forall). rewrite /revoke /std_sta /rel_is_std_i /std_rel /=.
        intros Htemp x Hx. split; [|by apply Htemp]. apply revoke_lookup_Temp. by apply Htemp. 
    }
    iDestruct "Hrevoked" as %Hrevoked.
    (* For later use it will be useful to know that W contains i *)
    (* Now we may do any private transitions to our local invariants.
       since we don't know which case we are in, we can generalize and 
       say that there exists some private future world such that   
       the store succeeded, after which the state at i is false
     *)
    iPrologue l Hprog_length "Hprog".
    apply contiguous_between_cons_inv_first in Hf2 as Heq. subst a_first. 
    iDestruct (sts_full_world_std with "Hsts") as %Hstd'.
    assert (withinBounds (RWX, Global, d, d', d) = true) as Hwb.
    { isWithinBounds;[lia|]. revert Hd; clear. solve_addr. }
    iAssert (▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a1)
              ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
              ∗ a0 ↦ₐ[pc_p] store_z r_env 0
              ∗ (∃ W',⌜(∃ b : bool, W.2.1 !! i = Some (encode b))
                        ∧ W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝ ∧ 
                    ⌜W' = ((revoke_std_sta W.1.1,W.1.2),(<[i:=encode false]> W.2.1,W.2.2))⌝ ∧
                    ⌜related_sts_priv_world (revoke W) W'⌝ ∧
                    ⌜W'.2.1 !! i = Some (encode false)⌝ ∧
                    region W' ∗ sts_full_world sts_std W' ∗
                    ⌜Forall (λ a : Addr, region_type_revoked W' a ∧ rel_is_std_i W' (encode a)) (region_addrs b_r e_r)⌝)
              -∗ WP Seq (Instr Executable) {{ v, φ v }})
        -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
      with "[HPC Hinstr Hr_env Hr Hsts]" as "Hstore_step".
    { iIntros "Hcont". 
      (* store r_env 0 *)
      iInv ι as (x) "[>Hstate Hb]" "Hcls".
      destruct x; iDestruct "Hb" as ">Hb".
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC a0 a_last|iContiguous_next Hf2 0|auto|auto|..].
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* we assert that updating the local state d to 0 is a private transition *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.        
        assert (related_sts_priv_world W (W.1, (<[i:=encode false]> W.2.1, W.2.2)))
          as Hrelated;[apply related_priv_local_1; auto|].
        (* first we can update region privately since it is revoked *)
        iAssert (sts_full_world sts_std (revoke W)
               ∗ region ((revoke W).1, (<[i:=encode false]> (revoke W).2.1, (revoke W).2.2)))%I with "[Hsts Hr]" as "[Hsts Hr]".
        { rewrite region_eq /region_def.
          iDestruct "Hr" as (M Mρ) "(HM & % & % & Hr)".
          iDestruct (monotone_revoke_list_region_def_mono_same $! Hrelated with "Hsts Hr") as "[Hsts Hr]".
          iFrame. iExists M, Mρ. iFrame. iPureIntro. auto.
        }
        (* we must update the local state of d to false *)
        iMod (sts_update_loc _ _ _ false with "Hsts Hstate") as "[Hsts Hstate]". 
        iMod ("Hcls" with "[Hstate Hd]") as "_". 
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        iExists _.
        iFrame "Hsts Hr". iSimpl.
        iPureIntro.
        split;[eauto|].
        split; [auto|]. split;[apply revoke_monotone in Hrelated; auto|split;[apply lookup_insert|] ].
        eapply Forall_impl;[apply Hrevoked|].
        intros a2 [Ha0_rev Ha0_std]. split; auto. 
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC a0 a_last|iContiguous_next Hf2 0|auto|auto|..].
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* use sts_state to assert that the current state of i is false *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.   
        (* No need to update the world, since we did not change state *)
        iMod ("Hcls" with "[Hstate Hd]") as "_". 
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        iExists _. iFrame. iPureIntro. rewrite /revoke /loc /= in Hlookup.
        apply insert_id in Hlookup as Heq. rewrite Heq. split;[eauto|]. split. 
        { destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ]. rewrite /revoke /loc /std_sta /std_rel /=. done. }
        split;[split;apply related_sts_priv_refl|split;auto].
    }
    iApply "Hstore_step". 
    iNext. iIntros "(HPC & Hr_env & Hprog_done & HW')".
    iDestruct "HW'" as (W' [Hawki Hawk] HeqW' Hrelated Hfalse) "(Hr & Hsts & #Hforall)".
    clear Hrevoked. iDestruct "Hforall" as %Hrevoked. 
    (* we prepare the stack for storing local state *)
    (* Splitting the stack into own and adv parts *)
    assert (contiguous (region_addrs b_r e_r)) as Hcont_stack;[apply region_addrs_contiguous|].
    assert (contiguous_between (region_addrs b_r e_r) b_r e_r) as Hcontiguous.
    { apply contiguous_between_of_region_addrs; auto. revert Hsize. rewrite /region_size. clear. solve_addr. }
    iDestruct "Hstack" as (ws) "Hstack". 
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 11)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { rewrite region_addrs_length in Hlength; auto. rewrite Hlength in Hsize. 
      do 11 (destruct ws as [|? ws]; [simpl in Hsize; lia|]).
           by exists [w;w0;w1;w2;w3;w4;w5;w6;w7;w8;w9],ws. }
    rewrite Happ.
    iDestruct (contiguous_between_program_split with "Hstack") as (stack_own stack_adv stack_own_last) "(Hstack_own & Hstack_adv & #Hcont)"; [eauto|].
    iDestruct "Hcont" as %(Hcont1 & Hcont2 & Hstack_eq & Hlink).
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_own. rewrite Hlength' in Hlength_own.
    rewrite Hstack_eq in Hcontiguous.
    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_f2.
    iDestruct (big_sepL2_length with "Hstack_adv") as %Hlength_adv.
    (* Getting the three top adress on the stack *)
    do 3 (destruct stack_own; [inversion Hlength_own|]; destruct ws_own;[inversion Hlength'|]).
    assert ((region_addrs b_r e_r) !! 0 = Some b_r) as Hfirst_stack.
    { apply region_addrs_first. revert Hsize; clear. rewrite /region_size. solve_addr. }
    rewrite Hstack_eq /= in Hfirst_stack. inversion Hfirst_stack as [Heq]. subst b_r.
    (* assert that the stack bounds are within bounds *)
    assert (withinBounds (RWLX,Local,a2,e_r,a2) = true ∧ withinBounds (RWLX,Local,a2,e_r,stack_own_last) = true) as [Hwb1 Hwb2].
    { split; isWithinBounds; first lia.
      - revert Hlength. rewrite Happ app_length Hlength' region_addrs_length /region_size. clear. solve_addr.
      - by eapply contiguous_between_bounds.
      - apply contiguous_between_bounds in Hcont2. simplify_eq.
        revert Hlength' Hlength Hlink Hsize Hlength_adv Hlength_own Hcont2. rewrite -region_addrs_length app_length. clear.
        rewrite region_addrs_length /region_size. solve_addr.
    }   
    (* push r_stk r_env *)
    iDestruct "Hstack_own" as "[Ha Hstack_own]".
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a1;a5] (a6::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Ha"];
      [|apply PermFlows_refl|auto|iContiguous_next Hf2 1|iContiguous_next Hf2 2|auto|..].
    { split;iCorrectPC a0 a_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_self *)
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a6;a7] (a8::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iDestruct "Hstack_own" as "[Ha2 Hstack_own]".
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_t0 Ha2"];
      [|apply PermFlows_refl| |iContiguous_next Hf2 3|
       iContiguous_next Hf2 4|iContiguous_next Hcont1 0|..].
    { split;iCorrectPC a0 a_last. }
    { iContiguous_bounds_withinBounds a2 stack_own_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha2)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_adv *)
    do 2 (destruct l;[inversion Hprog_length|]).
    iDestruct (big_sepL2_app_inv _ [a8;a9] (a10::l) with "Hprog") as "[Hpush Hprog]";[simpl;auto|].
    iDestruct "Hstack_own" as "[Ha3 Hstack_own]".
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_adv Ha3"];
      [|apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|iContiguous_next Hf2 5|
       iContiguous_next Hf2 6|iContiguous_next Hcont1 1|..].
    { split;iCorrectPC a0 a_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_adv & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* prepare for scall *)
    (* Prepare the scall prologue macro *)
    destruct stack_own as [|stack_own_b stack_own];[inversion Hlength_own|].
    assert ((stack_own_b :: stack_own) = region_addrs stack_own_b stack_own_last) as ->.
    { apply region_addrs_of_contiguous_between; auto.
      repeat (inversion Hcont1 as [|????? Hcont1']; subst; auto; clear Hcont1; rename Hcont1' into Hcont1). }      
    assert (stack_adv = region_addrs stack_own_last e_r) as ->.
    { apply region_addrs_of_contiguous_between; auto. }
    assert (contiguous_between (a10 :: l) a10 a_last) as Hcont_weak.
    { repeat (inversion Hf2 as [|????? Hf2']; subst; auto; clear Hf2; rename Hf2' into Hf2). }
    iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue rest0 s_last)
                                                                   "(Hscall & Hf2 & #Hcont)"; [eauto|..].
    clear Hfirst_stack Hcont_weak.
    iDestruct "Hcont" as %(Hcont_scall & Hcont_rest0 & Hrest_app & Hlink').
    iDestruct (big_sepL2_length with "Hscall") as %Hscall_length. simpl in Hscall_length, Hlength_f2.
    assert ((stack_own_b + 8)%a = Some stack_own_last) as Hstack_own_bound.
    { rewrite -(addr_add_assoc a2 _ 3). assert ((3 + 8) = 11)%Z as ->;[done|].
      rewrite Hlength_own in Hlink. revert Hlink; clear; solve_addr.
      apply contiguous_between_incr_addr with (i:=3) (ai:=stack_own_b) in Hcont1; auto. }
    assert (∃ a, (stack_own_b + 7)%a = Some a) as [stack_own_end Hstack_own_bound'].
    { revert Hstack_own_bound. clear. intros H. destruct (stack_own_b + 7)%a eqn:Hnone; eauto. solve_addr. }
    assert (a10 < s_last)%a as Hcontlt.
    { revert Hscall_length Hlink'. clear. solve_addr. }
    assert (a0 <= a10)%a as Hcontge.
    { apply region_addrs_of_contiguous_between in Hcont_scall. simplify_eq. revert Hscall_length Hf2 Hcontlt. clear =>Hscall_length Hf2 Hcontlt.
      apply contiguous_between_middle_bounds with (i := 7) (ai := a10) in Hf2;[solve_addr|auto]. 
    }
    (* scall *)
    iApply (scall_prologue_spec with "[-]");
      last ((iFrame "HPC Hr_stk Hscall"); iSplitL "Hgen_reg Hr_env Hr_self";[|
                                          iSplitL "Hstack_own";[iNext;iExists ws_own;iFrame|
                                                                iSplitL "Hstack_adv";[iNext;iExists ws_adv;iFrame|] ] ]);
      [| |apply Hwb2|apply Hbounds|apply Hcont_scall|apply PermFlows_refl|iNotElemOfList|iContiguous_next Hcont1 2|apply Hstack_own_bound'|apply Hstack_own_bound| |done|..].
    { assert (s_last <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest0|].
      intros mid Hmid. apply isCorrectPC_inrange with a0 a_last; auto.
      revert Hle Hcontlt Hcontge Hmid. clear; intros. split; solve_addr. }
    { simplify_eq. iContiguous_bounds_withinBounds a2 stack_own_last. }
    { assert (12 + 65 = 77)%Z as ->;[done|]. rewrite Hscall_length in Hlink'. done. }
    { iNext. iDestruct "Hgen_reg" as (wsr) "Hgen_reg".
      iExists (_ :: wsr ++ [_]).
      rewrite /all_registers /=; iFrame "Hr_self". 
      iApply (big_sepL2_app _ _ [r_t30] wsr with "Hgen_reg [Hr_env]").
      by iFrame. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hstack_adv & Hscall)".
    iDestruct (big_sepL2_length with "Hf2") as %Hf2_length. simpl in Hf2_length.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last a_last) as Hvpc1.
    { intros mid Hmid. assert (a0 <= s_last)%a as Hle;[apply contiguous_between_bounds in Hcont_scall; revert Hcont_scall Hcontge;clear; solve_addr|].
      apply isCorrectPC_inrange with a0 a_last; auto.
      revert Hmid Hle. clear. solve_addr. }
    (* jmp r_adv *)
    iDestruct (big_sepL2_length with "Hf2") as %Hrest_length; simpl in Hrest_length. 
    destruct rest0;[inversion Hrest_length|]. 
    iPrologue rest0 Hrest_length "Hf2".
    apply contiguous_between_cons_inv_first in Hcont_rest0 as Heq. subst a11. 
    iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
      [apply jmp_i|apply PermFlows_refl|iCorrectPC s_last a_last|..].
    iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".
    (* We now want to reason about unknown code. For this we invoke the fundamental theorem *)
    (* Before we can show the validity of the continuation, we need to set up the invariants 
       for local state, as well as the invariant for the stack *)
    (* We start out by closing the invariant for the program *)
    iMod ("Hcls" with "[Hprog_done Hinstr Hprog $Hna Hscall]") as "Hna". 
    { iNext. iDestruct "Hprog_done" as "(Hpush3 & Hpush2 & Hpush1 & Ha_first)".
      iFrame "Ha_first". rewrite Hrest_app. 
      iApply (big_sepL2_app with "Hpush1 [-]"). 
      iApply (big_sepL2_app with "Hpush2 [-]").
      iApply (big_sepL2_app with "Hpush3 [-]").
      iApply (big_sepL2_app with "Hscall [-]").
      iFrame. 
    }

    (* We set the local stack frame and all the leftover Temporary resources to static *)

    (* first, put together again the resources for the frame *)
    iDestruct (region_mapsto_cons with "[Ha3 Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 2| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=3) (ai:=stack_own_b) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    iDestruct (region_mapsto_cons with "[Ha2 Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 1| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=2) (ai:=a4) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    iDestruct (region_mapsto_cons with "[Hb_r Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 0| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=1) (ai:=a3) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    
    (* Next we want to define the map which will keep track of each word and permission *)
    iDestruct (temp_resources_split with "Hrest") as (pws) "[#Hrest_valid [#Hrev Hrest]]".
    iDestruct "Hrev" as %Hrev.
    match goal with |- context [ [[a2,stack_own_last]]↦ₐ[RWLX][[ ?instrs ]]%I ] =>
                    set l_frame := instrs
    end.
    set m_static1 := lists_to_static_region_perms (region_addrs a2 stack_own_last ++ l')
                                                  ((zip (repeat RWLX (length l_frame)) l_frame) ++ pws).
    
    (* we'll need that later to reason on the fact that the [zip] in the definition of
       l_frame indeed fully uses both lists *)
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_stack_own1.
    
    (* Allocate the static region containing the local stack frame and leftovers *)
    assert (NoDup (region_addrs a2 stack_own_last ++ l')) as Hdup1.
    { rewrite Permutation_app_comm.
      rewrite Hstack_eq in Hdup. apply region_addrs_of_contiguous_between in Hcont1.
      rewrite Hcont1 app_assoc in Hdup. by apply NoDup_app in Hdup as [Hdup _]. }
    iDestruct (region_revoked_to_static (W.1, (<[i:=encode false]> W.2.1, W.2.2)) m_static1
                 with "[Hsts Hr Hstack_own Hrest]") as ">[Hsts Hr]".
    { rewrite HeqW' /revoke. iFrame. rewrite /region_mapsto. 
      iApply (big_sepL2_to_static_region_perms _ _ (λ a p w, a ↦ₐ[p] w)%I with "[] [Hstack_own Hrest]").
      - auto. 
      - iAlways.
        iIntros (k y [p wy] Hin1 Hin2) "Hy /=".
        iExists p,wy.
        destruct (decide (k < length (l_frame))). 
        + rewrite lookup_app_l in Hin1;[|rewrite Hlength_stack_own1;auto].
          rewrite lookup_app_l in Hin2;[|auto].
          iExists (λ Wv, interp Wv.1 Wv.2). iFrame. 
          iSplit;[iPureIntro;apply _|].
          assert (zip (repeat RWLX (length l_frame)) l_frame !! k = Some (RWLX, wy)) as Hp.
          { apply zip_repeat_lookup_l with (b0:=RWLX) in l0 as [wy' Ha]. rewrite Hin2.
            rewrite Hin2 in Ha. inversion Ha. auto. }
          rewrite Hp in Hin2. inversion Hin2; subst.
          repeat iSplit;auto. rewrite Hstack_eq. 
          iDestruct (big_sepL_app with "Hstack_val") as "[Hframe _]".
          apply region_addrs_of_contiguous_between in Hcont1. rewrite Hcont1.
          iDestruct (big_sepL_lookup with "Hframe") as "Htest";[apply Hin1|auto].
        + assert (length l_frame <= k);[revert n;clear;lia|]. 
          rewrite lookup_app_r in Hin1;[|rewrite Hlength_stack_own1;auto].
          rewrite lookup_app_r in Hin2;[|auto].
          rewrite Hlength_stack_own1 in Hin1. simpl in Hin1,Hin2.
          iDestruct (big_sepL2_lookup with "Hrest_valid") as "Hyv";[apply Hin1|apply Hin2|].
          iDestruct "Hyv" as (φ') "(Hpers & Hne & Hφ & Hrely & Hmono)".
          iExists φ'. iFrame "∗ #". auto. 
      - iApply big_sepL2_app';[auto|iFrame].
        iApply (big_sepL2_zip_repeat _ _ (λ a p v, a ↦ₐ[p] v))%I.
        iFrame. 
    }
        
    (* Next we close the adversary stack region so that it is Temporary *)
    iDestruct (sts_full_world_std with "Hsts") as %Hstd''.
    iDestruct (big_sepL2_length with "Hrest_valid") as %Hlength_rest. 
    iMod (monotone_close _ (region_addrs stack_own_last e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
            with "[$Hsts $Hr Hstack_adv]") as "[Hsts Hr]".
    { rewrite Hstack_eq. iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_val']".
      iApply big_sepL_sep. iSplitL.
      - iDestruct (region_addrs_zeroes_trans with "Hstack_adv") as "Hstack_adv".
        iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hy".
        iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
        + iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
        + by repeat (rewrite fixpoint_interp1_eq /=).
      - iApply big_sepL_sep; iFrame "#". iApply big_sepL_forall. iPureIntro.
        rewrite Hstack_eq in Hrevoked. apply Forall_app in Hrevoked as [_ Hrevoked]. 
        intros k x Hsome.
        assert (x ∉ (region_addrs a2 stack_own_last) ++ l') as Hnin.
        { apply elem_of_list_lookup_2 in Hsome.
          apply region_addrs_of_contiguous_between in Hcont1. 
          rewrite Hstack_eq Hcont1 app_assoc in Hdup.
          revert Hdup. rewrite Permutation_app_comm =>Hdup. apply NoDup_app in Hdup as [_ [Hnin _] ].
          apply Hnin in Hsome. rewrite Permutation_app_comm. auto. 
        }
        rewrite std_sta_update_multiple_lookup_same /std_sta /=.
        apply Forall_lookup_1 with (i0:=k) (x0:=x) in Hrevoked as [Hrevoked _];auto.
        rewrite HeqW' in Hrevoked. auto.
        rewrite lists_to_static_perms_region_dom.
        rewrite elements_list_to_set;auto. repeat rewrite app_length. auto. 
    }
    
    (* Resulting world *)
    evar (W'' : prod (prod STS_states STS_rels) (prod STS_states STS_rels)).
    instantiate (W'' :=
       (close_list (encode <$> region_addrs stack_own_last e_r)
               (std_update_multiple (revoke (W.1, (<[i:=encode false]> W.2.1, W.2.2)))
                  (elements (dom (gset Addr) m_static1)) (Static m_static1)))). 
    assert (related_sts_priv_world W' W'') as HW'W''.
    { rewrite HeqW'. eapply related_sts_priv_pub_trans_world;[|apply close_list_related_sts_pub;auto].
      apply related_sts_priv_world_static; auto. 
      apply Forall_forall.
      rewrite /m_static1 lists_to_static_perms_region_dom; [|repeat rewrite app_length;rewrite Hlength_rest;auto].
      intros x Hin. revert Hin. rewrite elements_list_to_set; auto. intros Hin.
      apply elem_of_app in Hin as [Hin | Hin].
      - revert Hrevoked. rewrite HeqW' Forall_forall =>Hrevoked. apply Hrevoked.
        apply region_addrs_of_contiguous_between in Hcont1. rewrite Hstack_eq Hcont1. apply elem_of_app; by left.
      - revert Hrev. rewrite Forall_forall =>Hrev. apply Hrev. auto.       
    }
    assert (related_sts_priv_world W W'') as HWW''.
    { eapply related_sts_priv_trans_world;[apply revoke_related_sts_priv;auto|].
      eapply related_sts_priv_trans_world;[apply Hrelated|].
      auto. 
    }
    (* We choose the r *)
    evar (r : gmap RegName Word).
    instantiate (r := <[PC    := inl 0%Z]>
                     (<[r_stk := inr (RWLX, Local, stack_own_last, e_r, stack_own_end)]>
                     (<[r_t0  := inr (E, Local, a2, e_r, stack_own_b)]>
                     (<[r_adv := inr (E, Global, b, e, a)]>
                     (create_gmap_default
                        (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r))
      with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
    { iApply (registers_mapsto_resources with "Hr_gen Hr_stk Hr_t0 Hr_adv HPC"). } 
    (* r contrains all registers *)
    iAssert (full_map r) as "#full";[iApply r_full|].
    iSimpl in "Hadv_val".
    iAssert (interp_expression r W'' (inr (RX, Global, b, e, a)))
      as "Hvalid". 
    { iApply fundamental. iLeft; auto. iExists RX. iSplit;[iPureIntro;apply PermFlows_refl|]. 
      iApply (adv_monotone with "Hadv_val"); auto. }
    (* We are now ready to show that all registers point to a valid word *)
    clear Hstd''. iDestruct (sts_full_world_std with "Hsts") as %Hstd''.
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W'' (r !r! r1))%I
      with "[-Hsts Hr Hmaps Hvalid Hna Hφ]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
          [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_adv)); [by left|right;auto].  
      }
      - iIntros "%". contradiction.
      - assert (r !! r_stk = Some (inr (RWLX, Local, stack_own_last, e_r, stack_own_end))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk fixpoint_interp1_eq. 
        iIntros (_). iExists RWLX. iSplitR; [auto|].
        iAssert ([∗ list] a ∈ region_addrs stack_own_last e_r, read_write_cond a RWLX (fixpoint interp1)
                             ∧ ⌜region_state_pwl W'' a⌝ ∧ ⌜region_std W'' a⌝)%I as "#Hstack_adv_val". 
        { rewrite Hstack_eq. 
          iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_val']".
          iApply (big_sepL_mono with "Hstack_val'").
          iIntros (k y Hsome) "Hy".
          rewrite Hstack_eq in Hrevoked.
          apply Forall_app in Hrevoked as [_ Hrevoked].
          iFrame. iPureIntro;split.
          - apply close_list_std_sta_revoked.
            + apply elem_of_list_fmap. eexists _; split;[eauto|]. apply elem_of_list_lookup; eauto.
            + revert Hrevoked. rewrite Forall_forall =>Hrevoked.
              assert (y ∉ (region_addrs a2 stack_own_last) ++ l') as Hnin.
              { apply elem_of_list_lookup_2 in Hsome.
                apply region_addrs_of_contiguous_between in Hcont1. 
                rewrite Hstack_eq Hcont1 app_assoc in Hdup.
                revert Hdup. rewrite Permutation_app_comm =>Hdup. apply NoDup_app in Hdup as [_ [Hnin _] ].
                apply Hnin in Hsome. rewrite Permutation_app_comm. auto. 
              }
              rewrite std_sta_update_multiple_lookup_same /std_sta /=. rewrite HeqW' in Hrevoked. 
              apply Hrevoked. apply elem_of_list_lookup. eauto.
              rewrite lists_to_static_perms_region_dom.
              rewrite elements_list_to_set;auto. repeat rewrite app_length. auto. 
          - revert Hrevoked. rewrite Forall_forall =>Hrevoked.
            assert (y ∉ (region_addrs a2 stack_own_last) ++ l') as Hnin.
            { apply elem_of_list_lookup_2 in Hsome.
              apply region_addrs_of_contiguous_between in Hcont1. 
              rewrite Hstack_eq Hcont1 app_assoc in Hdup.
              revert Hdup. rewrite Permutation_app_comm =>Hdup. apply NoDup_app in Hdup as [_ [Hnin _] ].
              apply Hnin in Hsome. rewrite Permutation_app_comm. auto. 
            }
            rewrite /region_std. rewrite /W'' /rel_is_std_i /close_list /std_rel /=. 
            rewrite std_rel_update_multiple_lookup_same /std_sta /=. rewrite HeqW' in Hrevoked.
            apply Hrevoked. apply elem_of_list_lookup. eauto.
            rewrite lists_to_static_perms_region_dom.
            rewrite elements_list_to_set;auto. repeat rewrite app_length. auto. 
        }
        iFrame "Hstack_adv_val". 
        iAlways.
        rewrite /exec_cond.
        iIntros (y r' W3 Hay Hrelated3). iNext.
        iApply fundamental.
        + iRight. iRight. done.
        + iExists RWLX. iSplit; auto. simpl.
          iApply (adv_stack_monotone with "Hstack_adv_val"); auto. 
      - (* continuation *)
        iIntros (_).
        assert (r !! r_t0 = Some (inr (E, Local, a2, e_r, stack_own_b))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 fixpoint_interp1_eq. iSimpl. 
        (* prove continuation *)
        iAlways.
        iIntros (r' W3 Hrelated3).
        iNext.

        (* We start by asserting that the adversary stack is still temporary *)
        iAssert ([∗ list] a ∈ (region_addrs stack_own_last e_r),
                 ⌜W3.1.1 !! encode a = Some (encode Temporary)⌝
                    ∗ rel a RWLX (λ Wv : prodO STS STS * Word, ((fixpoint interp1) Wv.1) Wv.2)
                )%I as "#Hstack_adv_tmp".
        { rewrite Hstack_eq.
          iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_adv]".
          iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hr".
          rewrite /read_write_cond. iFrame. iPureIntro.
          assert (region_state_pwl W3 y) as Hlookup;[|auto].
          revert Hrevoked; rewrite HeqW' Forall_forall =>Hrevoked.
          apply region_state_pwl_monotone with W''; eauto.
          - apply related_sts_rel_std with W;auto.
            revert Htemp. rewrite Forall_forall =>Htemp. apply Htemp.
            rewrite Hstack_eq. apply elem_of_app. right. 
            apply elem_of_list_lookup;eauto. 
          - rewrite /W'' /region_state_pwl /std_sta /=.
            apply close_list_std_sta_revoked; [apply elem_of_list_fmap_1, elem_of_list_lookup; eauto|].
            assert (y ∉ (region_addrs a2 stack_own_last) ++ l') as Hnin.
            { apply elem_of_list_lookup_2 in Hsome.
              apply region_addrs_of_contiguous_between in Hcont1. 
              rewrite Hstack_eq Hcont1 app_assoc in Hdup.
              revert Hdup. rewrite Permutation_app_comm =>Hdup. apply NoDup_app in Hdup as [_ [Hnin _] ].
              apply Hnin in Hsome. rewrite Permutation_app_comm. auto. 
            }
            rewrite std_sta_update_multiple_lookup_same /std_sta /=. 
              apply Hrevoked. rewrite Hstack_eq. apply elem_of_app; right. apply elem_of_list_lookup. eauto.
              rewrite lists_to_static_perms_region_dom.
              rewrite elements_list_to_set;auto. repeat rewrite app_length. auto. 
        }
        iDestruct (big_sepL_sep with "Hstack_adv_tmp") as "[Htemp _]". 
        iDestruct (big_sepL_forall with "Htemp") as %HtempW3. iClear "Htemp". 
        
        (* we want to distinguish between the case where the local stack frame is Static (step through 
           continuation) and where the local stack frame is temporary (apply FTLR) *)
        assert (forall a, a ∈ region_addrs a2 stack_own_last ++ l' ->
                  (std_sta W3) !! (encode a) = Some (encode Temporary) ∨
                  (std_sta W3) !! (encode a) = Some (encode (Static m_static1)))
          as Hcases.
        { intros a' Hin. apply or_comm,related_sts_pub_world_static with W'';auto.
          - apply std_rel_update_multiple_lookup_std_i. 
            rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
            rewrite elements_list_to_set;auto. apply elem_of_list_fmap. repeat eexists. auto. 
          - assert (std_sta (std_update_multiple (revoke (W.1, (<[i:=encode false]> W.2.1, W.2.2)))
                            (elements (dom (gset Addr) m_static1)) (Static m_static1)) !! encode a' =
                    Some (encode (Static m_static1))) as Hlookup.
            { apply std_sta_update_multiple_lookup_in_i.
              rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
              rewrite elements_list_to_set;auto. apply elem_of_list_fmap. repeat eexists. auto. }
            rewrite -close_list_std_sta_same_alt;auto. rewrite Hlookup. intros Hcontr;inversion Hcontr as [heq].
            apply encode_inj in heq. done. 
        }
        assert (a2 ∈ region_addrs a2 stack_own_last ++ l') as Ha2in.
        { apply elem_of_app. left. apply elem_of_list_lookup. exists 0.
          apply region_addrs_of_contiguous_between in Hcont1 as <-. auto. }
        apply Hcases in Ha2in as [Hm_temp | Hm_static].
        { iSimpl. 
          iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)". 
          iSplit; [auto|rewrite /interp_conf].
          (* first we want to assert that if a2 is Temporary, the remaining addresses are also temporary *)
          iAssert (⌜∀ a : Addr, a ∈ dom (gset Addr) m_static1 → temporary W3 a⌝)%I as %Hm_frame_temp_all.
          { (* use fact that if the address is in a public future state, it is either Static or Temp. 
               If it is temp we are done. If it is static then we can use the full_sts_static_all lemma 
               to assert that a2 is also in state Static, which leads to a contradiction, as we are in the 
               case where it should be Temporary *)
            iIntros (a'). rewrite /m_static1. 
            rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
            iIntros (Hin). apply elem_of_list_to_set in Hin. 
            pose proof (Hcases a' Hin) as [Htemp' | Hstatic].
            - rewrite /temporary. rewrite Htemp'. auto.
            - iDestruct (full_sts_static_all with "Hsts Hr") as %Hforall;[eauto|]. exfalso.
              assert (a2 ∈ dom (gset Addr) m_static1) as Hin'.
              { rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                apply elem_of_list_to_set. apply elem_of_app. left. apply elem_of_list_lookup. exists 0.
                apply region_addrs_of_contiguous_between in Hcont1 as <-. auto. }
              apply Hforall in Hin'. rewrite /static Hm_temp in Hin'. apply encode_inj in Hin'. done. 
          }
          iDestruct (fundamental W3 r' RX Local a2 e_r stack_own_b with "[] [] [-]") as "[_ Hcont]";[by iLeft| |iFrame "∗ #"|..].
          { iSimpl. iExists RWLX. iSplit;[auto|].
            iApply (big_sepL_mono with "Hstack_val").
            iIntros (k y Hk) "Hrel". iFrame. iPureIntro.            
            split;[left|].
            - (* first we assert that the region is all in state temporary *)
              rewrite (region_addrs_split _ stack_own_last) in Hk. 
              assert (y ∈ region_addrs a2 stack_own_last ++ region_addrs stack_own_last e_r) as Hk'.
              { apply elem_of_list_lookup. eauto. }
              apply elem_of_app in Hk' as [Hframe | Hadv].
              + assert (y ∈ dom (gset Addr) m_static1) as Hk'.
                { rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                  apply elem_of_list_to_set. apply elem_of_app. by left. }
                apply Hm_frame_temp_all in Hk'. rewrite /temporary in Hk'.
                destruct (W3.1.1 !! encode y) eqn:Hsome;[subst;auto|inversion Hk'].
              + apply elem_of_list_lookup in Hadv as [j Hj]. by apply HtempW3 with j. 
              + split. 
                * rewrite /le_addr. trans stack_own_b;[|revert Hstack_own_bound;clear;solve_addr].
                  apply contiguous_between_middle_bounds with (i:=3) (ai:=stack_own_b) in Hcont1 as [Hle _];auto.
                * apply contiguous_between_bounds in Hcont2. auto. 
            - apply related_sts_rel_std with W.
              eapply related_sts_priv_pub_trans_world;[apply HWW''|apply Hrelated3]. 
              revert Htemp. rewrite Forall_forall =>Htemp. apply Htemp. apply elem_of_list_lookup;eauto. 
          }
          iFrame. 
        }
        
        (* Now we are in the case where m_static1 is still static. We will have to open the region and step through
           the continuation as usual. *)
        iSimpl. 
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hr & Hsts & Hna)". 
        iSplit; [auto|rewrite /interp_conf].
        (* we might need to remember that W3 is standard *)
        iDestruct (sts_full_world_std with "Hsts") as %Hstd3.
        (* since a2 is static, all of dom(m_static1) is static *)
        iDestruct (full_sts_static_all with "Hsts Hr") as %Hall_static;eauto. 
        (* get the PC, currently pointing to the activation record *)
        iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
        (* get some registers *)
        iGet_genpur_reg_map r' r_t1 "Hmreg'" "Hfull'" "[Hr_t1 Hmreg']".
        iGet_genpur_reg_map r' r_stk "Hmreg'" "Hfull'" "[Hr_stk Hmreg']".
        iGet_genpur_reg_map r' r_adv "Hmreg'" "Hfull'" "[Hr_adv Hmreg']".
        iGet_genpur_reg_map r' r_t0 "Hmreg'" "Hfull'" "[Hr_t0 Hmreg']".
        iGet_genpur_reg_map r' r_env "Hmreg'" "Hfull'" "[Hr_env Hmreg']".

        (* We will need to step through the activation record. We will therefore have to revoke m_static1. 
           Since this is a private transition, we must first revoke W3. *)

        iAssert (⌜exists M, dom_equal W3.1.1 M⌝)%I as %Hdom.
        { rewrite region_eq /region_def. iDestruct "Hr" as (M Mρ) "(_ & % & _)". iPureIntro. eauto. }
        assert (Hdom_copy3 := Hdom). 
        iDestruct (region_has_static_addr_Forall with "[$Hr $Hsts]") as %HForall_static1; eauto.
        iAssert (⌜Forall (λ a, W3.1.1 !! encode a = Some (encode Temporary))
                  (region_addrs stack_own_last e_r)⌝)%I as %Hstack_adv_tmp.
        { iApply region_state_pwl_forall_temp. iApply (big_sepL_mono with "Hstack_adv_tmp").
          iIntros (k y Hk) "[Htemp Hrel]". iFrame. iExact "Hrel". } 
        apply extract_temps_split with (l:=region_addrs stack_own_last e_r) in Hdom as [l'' [Hdup' Hiff'] ].
        2: { apply NoDup_ListNoDup, region_addrs_NoDup. }
        2: { apply Hstack_adv_tmp. }

        (* we revoke W3, and keep a list of leftovers l'' *)
        iMod (monotone_revoke_keep_some _ l'' (region_addrs stack_own_last e_r)
                with "[Hstack_adv_tmp $Hr $Hsts]") as "(Hsts & Hr & Hrest' & Hstack_adv)".
        assumption. iSplit.
        { (* TODO: lemma for that? *)
          iApply big_sepL_forall. iPureIntro. intros n. simpl. intros x Hsome. apply Hiff'. apply elem_of_app; left.
          apply elem_of_list_lookup. eauto. }
          by iApply "Hstack_adv_tmp".

        iDestruct (region_static_to_revoked with "[$Hr $Hsts]") as ">(Hsts & Hr & Hm_static1_resources & _)". eauto.

        (* finally we split up the static resources into the local stack frame and l' *)
        iAssert ([[a2,stack_own_last]] ↦ₐ[RWLX] [[l_frame]]
                ∗ [∗ list] a;pw ∈ l';pws, a ↦ₐ[pw.1] pw.2)%I with "[Hm_static1_resources]" as "[Hframe Hl']".
        { rewrite /m_static1 /region_mapsto /static_resources.
          iAssert (([∗ list] y1;y2 ∈ region_addrs a2 stack_own_last;zip (repeat RWLX (length l_frame)) l_frame, y1 ↦ₐ[y2.1] y2.2)
                     ∗ ([∗ list] a11;pw ∈ l';pws, a11 ↦ₐ[pw.1] pw.2))%I with "[-]" as "[H $]".
          { iApply (big_sepL2_app' _ _ _ (λ k a pv, a ↦ₐ[pv.1] pv.2))%I;auto.
            iApply (static_region_perms_to_big_sepL2 _ _ (λ a p w, a ↦ₐ[p] w) with "[] Hm_static1_resources")%I. 
            auto. repeat rewrite app_length. rewrite Hlength_rest. auto.
            iAlways. iIntros (? ? ? ? ?) "HH". iDestruct "HH" as (? ? ->) "?". auto.
          }
          iApply (big_sepL2_zip_repeat _ _ (λ a p w, a ↦ₐ[p] w) with "H")%I.
        }

        (* we isolate the activation record from the frame *)
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha2 Hframe]"; [iContiguous_next Hcont1 0|..].
        { apply contiguous_between_middle_bounds with (i:=1) (ai:=a3) in Hcont1;auto. revert Hcont1;clear;solve_addr. }
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha3 Hframe]"; [iContiguous_next Hcont1 1|..].
        { apply contiguous_between_middle_bounds with (i:=2) (ai:=a4) in Hcont1;auto. revert Hcont1;clear;solve_addr. }
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha4 Hframe]"; [iContiguous_next Hcont1 2|..].
        { apply contiguous_between_middle_bounds with (i:=3) (ai:=stack_own_b) in Hcont1;auto.
          revert Hcont1;clear;solve_addr. }

        (* prepare the new stack value *)
        assert (exists stack_new, (stack_new + 1)%a = Some stack_own_end) as [stack_new Hstack_new].
        { revert Hstack_own_bound'. clear. intros H. destruct (stack_own_b + 6)%a eqn:Hsome;[|solve_addr].
          exists a. solve_addr. }

        (* step through instructions in activation record *)
        iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
          [|done|iContiguous_next Hcont_rest0 0|apply Hstack_new|revert Hstack_own_bound Hstack_own_bound'; clear; solve_addr|..].
        { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb2.
          apply (contiguous_between_middle_bounds _ 3 stack_own_b) in Hcont1;[|auto]. revert Hwb2 Hcont1 Hmid. clear. solve_addr.
        }
        iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
        iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
        iDestruct "Hr_t1" as (wrt1) "Hr_t1".

        (* we can now step through the rest of the program *)
        (* to do that wee need to open the non atomic invariant of the program *)
        iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|]. 
        rewrite Hrest_app /=. repeat rewrite app_comm_cons. 
        iDestruct (mapsto_decomposition _ _ _ (take 84 (awkward_instrs r_adv 65)) with "Hprog")
          as "[Hprog_done [Ha Hprog] ]". 
        { simpl. inversion Hscall_length as [Heq]. rewrite Heq. omega. }
        (* let's prove some practical lemmas before continuing *)
        (* assert (last (rest0_first :: a9 :: rest0) = Some a_last) as Hlast0. *)
        (* { rewrite Hrest_app in Hlast. repeat rewrite app_comm_cons in Hlast. *)
        (*   by rewrite -last_app_eq in Hlast; [|simpl;lia]. } *)
        iCombine "Ha" "Hprog_done" as "Hprog_done".
        (* sub r_t1 0 7 *)
        iPrologue rest0 Hrest_length "Hprog".
        iApply (wp_add_sub_lt_success_z_z with "[$HPC $Hr_t1 $Hinstr]");
          [apply sub_z_z_i|right;left;eauto|iContiguous_next Hcont_rest0 1|apply PermFlows_refl|iCorrectPC s_last a_last|..]. 
        iEpilogue "(HPC & Hinstr & Hr_t1)".
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* lea r_stk r_t1 *)
        iPrologue rest0 Hrest_length "Hprog". 
        assert ((stack_new + (0 - 7))%a = Some a4) as Hpop.
        { assert ((a4 + 1)%a = Some stack_own_b) as Ha0;[iContiguous_next Hcont1 2|].
          revert Ha0 Hstack_own_bound' Hstack_new. clear. solve_addr. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
          [apply lea_r_i|apply PermFlows_refl|iCorrectPC s_last a_last|iContiguous_next Hcont_rest0 2|apply Hpop|auto..].
        iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
        (* pop r_stk r_adv *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a13;a14;a15] (a16::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a4 + (0 - 1))%a = Some a3) as Hpop.
        { rewrite -(addr_add_assoc a3 _ 1);[apply addr_add_0|iContiguous_next Hcont1 1]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_adv Ha4"];
          [split;[|split];iCorrectPC s_last a_last| apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|
           iContiguous_next Hcont_rest0 3|iContiguous_next Hcont_rest0 4|iContiguous_next Hcont_rest0 5|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_adv & Ha4 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_self *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a16;a17;a18] (a19::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a3 + (0 - 1))%a = Some a2) as Hpop.
        { rewrite -(addr_add_assoc a2 _ 1);[apply addr_add_0|iContiguous_next Hcont1 0]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_t0 Ha3"];
          [split;[|split];iCorrectPC s_last a_last| apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|
           iContiguous_next Hcont_rest0 6|iContiguous_next Hcont_rest0 7|iContiguous_next Hcont_rest0 8|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_t0 & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_env *)
        do 3 (destruct rest0; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a19;a20;a21] (a22::rest0) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a2 + (0 - 1))%a = Some b_r') as Hpop.
        { rewrite -(addr_add_assoc b_r' _ 1);[apply addr_add_0|auto]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Ha2"];
          [split;[|split];iCorrectPC s_last a_last| apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|
           iContiguous_next Hcont_rest0 9|iContiguous_next Hcont_rest0 10|iContiguous_next Hcont_rest0 11|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_env & Hb_r & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* store r_env 1 *)
        iPrologue rest0 Hrest_length "Hprog".
        (* Storing 1 will always constitute a public future world of 
           std_update_multiple (revoke W3) dom(m_static1) Revoked *)
        iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a23)
                       ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                       ∗ a22 ↦ₐ[pc_p] store_z r_env 1
                       ∗ region (std_update_multiple (revoke (W3.1,(<[i:=encode true]> W3.2.1,W3.2.2)))
                                                     (elements (dom (gset Addr) m_static1)) Revoked)
                       ∗ sts_full_world sts_std (std_update_multiple (revoke (W3.1,(<[i:=encode true]> W3.2.1,W3.2.2)))
                                                     (elements (dom (gset Addr) m_static1)) Revoked)
                       ∗ ⌜(∃ y : bool, W3.2.1 !! i = Some (encode y)) ∧ W3.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝
                       -∗ WP Seq (Instr Executable) {{ v, φ v }})
                   -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
          with "[HPC Hinstr Hr_env Hr Hsts]" as "Hstore_step".
        { iIntros (φ') "Hφ".
          iInv ι as (y) "[>Hstate Hb]" "Hcls".
          iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
          iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrellookup.
          rewrite std_update_multiple_loc_sta in Hlookup.
          rewrite std_update_multiple_loc_rel in Hrellookup. 
          destruct y; iDestruct "Hb" as ">Hb".
          - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
              [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC s_last a_last|
               iContiguous_next Hcont_rest0 12|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ". iFrame.            
            rewrite (insert_id _ i);[|auto].
            destruct W3 as [W3_std [W3_loc_pub W3_lo_priv] ]. iFrame.
            eauto. 
          - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
              [apply store_z_i|apply PermFlows_refl|apply PermFlows_refl|iCorrectPC s_last a_last|
               iContiguous_next Hcont_rest0 12|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod (sts_update_loc _ _ _ true with "Hsts Hstate") as "[Hsts Hstate] /=".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ".
            rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel std_update_multiple_proj_eq.
            iFrame. 
            iSplitL;[|eauto]. iApply (region_monotone with "[] [] Hr").
            + iPureIntro. rewrite /revoke /std_sta /std_rel /loc /=. erewrite std_update_multiple_std_sta_eq. eauto. 
            + iPureIntro. apply std_update_mutiple_related_monotone.
              split;[apply related_sts_pub_refl|].
              rewrite /= /loc. apply related_pub_local_1 with false; auto.
        }
        iApply "Hstore_step". iNext. iIntros "(HPC & Hr_env & Hinstr & Hr & Hsts & #HW3lookup)".
        iDestruct "HW3lookup" as %[HW3lookup Hw3rel]. 
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* push r_stk r_env *)
        do 2 (destruct rest0;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a23;a24] (a25::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Hb_r"];
          [split;iCorrectPC s_last a_last|apply PermFlows_refl|auto|iContiguous_next Hcont_rest0 13|iContiguous_next Hcont_rest0 14|auto|..].
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
        (* push r_stk r_self *)
        do 2 (destruct rest0;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a25;a26] (a27::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_t0 Ha3"];
          [split;iCorrectPC s_last a_last|apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|iContiguous_next Hcont_rest0 15|
           iContiguous_next Hcont_rest0 16|iContiguous_next Hcont1 0|..].
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done". 
        (* SECOND SCALL *)

        (* we now want to extract the final element of the local stack, which will now be handed off to the adversary *)
        do 2 (iDestruct (big_sepL_sep with "Hstack_adv") as "[Hstack_adv _]").
        (* we will need to split off the last element to adv *)
        assert (forall stack_own_b : Addr, (stack_own_b <= stack_own_end)%Z -> region_addrs stack_own_b stack_own_last = region_addrs stack_own_b stack_own_end ++ [stack_own_end]) as Hstack_localeq'.
        { intros stack_own_b' Hle. rewrite (region_addrs_decomposition _ stack_own_end).
          - repeat f_equiv. assert( (stack_own_end + 1)%a = Some stack_own_last) as ->;[|by rewrite /region_addrs /region_size Z.sub_diag /=].
            revert Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. 
          - revert Hle Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. 
        }
        
        rewrite /region_mapsto (Hstack_localeq' stack_own_b);[|revert Hstack_own_bound';clear;solve_addr]. 
        iDestruct (mapsto_decomposition _ _ _ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                                               inr (pc_p, pc_g, pc_b, pc_e, s_last)] with "Hframe") as "[Hframe Hlast']".
        { rewrite region_addrs_length /=. rewrite /region_size. revert Hstack_own_bound'; clear. solve_addr. }
        assert ([stack_own_end] ++ region_addrs stack_own_last e_r = region_addrs stack_own_end e_r) as Hstack_localeq.
        { rewrite /region_addrs. apply withinBounds_le_addr in Hwb2 as [_ Hwb2].
          assert ((stack_own_end + 1)%a = Some stack_own_last) as Hincr;[revert Hstack_own_bound Hstack_own_bound';clear;solve_addr|].
          assert (region_size stack_own_end e_r = S (region_size stack_own_last e_r)) as ->.
          { revert Hstack_own_bound Hstack_own_bound' Hwb2; clear. rewrite /region_size. solve_addr. }
          simpl. f_equiv. rewrite Hincr /=. done.
        }  
        iAssert (▷ (∃ ws_adv : list Word, [[stack_own_end,e_r]]↦ₐ[RWLX][[ws_adv]]))%I with "[Hstack_adv Hlast']" as ">Hstack_adv".
        { iNext.
          iDestruct (region_addrs_exists with "Hstack_adv") as (ws_adv') "Hstack_adv".
          iDestruct (big_sepL2_sep with "Hstack_adv") as "[_ Hstack_adv]". iDestruct (big_sepL2_sep with "Hstack_adv") as "[Hstack_adv _]".
          iDestruct (mapsto_decomposition _ _ _ [inr (RWLX, Local, a2, e_r, stack_own_end)] with "[$Hstack_adv $Hlast']") as "Hstack_adv";[auto|..].
          rewrite Hstack_localeq. 
          iExists (_ :: ws_adv'). iFrame. 
        }
        iAssert (▷ (∃ ws_own : list Word, [[a4,stack_own_end]]↦ₐ[RWLX][[ws_own]]))%I with "[Hframe Ha4]" as ">Hstack_own".
        { iNext. 
          iExists ((inr (E, Global, b, e, a)) :: _). rewrite /region_mapsto.
          assert ([a4] ++ region_addrs stack_own_b stack_own_end = region_addrs a4 stack_own_end) as <-.
          { rewrite /region_addrs.
            assert ((a4 + 1)%a = Some stack_own_b) as Hincr;[iContiguous_next Hcont1 2|].
            assert (region_size a4 stack_own_end = S (region_size stack_own_b stack_own_end)) as ->.
            { revert Hstack_own_bound' Hincr; clear. rewrite /region_size. solve_addr. }
            simpl. f_equiv. rewrite Hincr /=. done. 
          }
          iApply (mapsto_decomposition [a4] _ _ [inr (E, Global, b, e, a)]); [auto|]. iFrame. done.
        }
        (* prepare for scall *)
        (* split the program into the scall_prologue and the rest *)
        assert (contiguous_between (a27 :: rest0) a27 a_last) as Hcont_weak.
        { repeat (inversion Hcont_rest0 as [|????? Hf2']; subst; auto; clear Hcont_rest0; rename Hf2' into Hcont_rest0). }
        iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue1 rest1 s_last1)
                                                                       "(Hscall & Hprog & #Hcont)"; [eauto|..].
        clear Hcont_weak.
        iDestruct "Hcont" as %(Hcont_scall1 & Hcont_rest1 & Hrest_app1 & Hlink1). subst.
        iDestruct (big_sepL2_length with "Hscall") as %Hscall_length1. simpl in Hscall_length1.
        destruct scall_prologue1 as [|scall_prologue_first1 scall_prologue1];[inversion Hscall_length1|].
        assert (scall_prologue_first1 = a27) as <-;[inversion Hrest_app1;auto|].
        (* some important element of the stack *)
        assert ((a4 + 8)%a = Some stack_own_end) as Hstack_own_bound1.
        { assert ((a4 + 1)%a = Some stack_own_b) as Ha4;[iContiguous_next Hcont1 2|].
          revert Hstack_own_bound Hstack_own_bound' Ha4. clear. solve_addr. }
        assert ((a4 + 7)%a = Some stack_new) as Hstack_own_bound1'.
        { revert Hstack_own_bound1 Hstack_new. clear. solve_addr. }
        assert (scall_prologue_first1 < s_last1)%a as Hcontlt1.
        { revert Hscall_length1 Hlink1. clear. solve_addr. }
        assert (s_last <= scall_prologue_first1)%a as Hcontge1.
        { apply region_addrs_of_contiguous_between in Hcont_scall. subst. revert Hscall_length1 Hcont_rest0 Hcontlt1.  clear =>Hscall_length Hf2 Hcontlt.
          apply contiguous_between_middle_bounds with (i := 17) (ai := scall_prologue_first1) in Hf2;[solve_addr|auto]. 
        }
        assert (withinBounds (RWLX, Local, a2, e_r, stack_own_end) = true) as Hwb3.
        { isWithinBounds. 
          - assert ((a2 + 3)%a = Some stack_own_b) as Hincr;[apply contiguous_between_incr_addr with (i := 3) (ai := stack_own_b) in Hcont1; auto|].
            revert Hstack_own_bound' Hincr. clear. solve_addr. 
          - apply withinBounds_le_addr in Hwb2 as [_ Hwb2]. revert Hstack_own_bound Hstack_own_bound' Hwb2. clear. solve_addr. 
        } 
        (* we can now invoke the stack call prologue *)
        iApply (scall_prologue_spec with "[-]");
          last ((iFrame "HPC Hr_stk Hscall"); iSplitL "Hmreg' Hr_env Hr_self Hr_t1";[|
                 iSplitL "Hstack_own";[iNext;iFrame|
                 iSplitL "Hstack_adv";[iNext;iFrame|] ] ]);
          [| |apply Hwb3|apply Hbounds|apply Hcont_scall1|
           apply PermFlows_refl|iNotElemOfList|iContiguous_next Hcont1 1|apply Hstack_own_bound1'|apply Hstack_own_bound1| |done|..].
        { assert (s_last1 <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest1|].
          intros mid Hmid. apply isCorrectPC_inrange with a0 a_last; auto.
          revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid. clear; intros. split; solve_addr. }
        { subst. iContiguous_bounds_withinBounds a2 stack_own_last. }
        { assert (12 + 65 = 77)%Z as ->;[done|]. rewrite Hscall_length1 in Hlink1. done. }
        { iNext. iApply region_addrs_exists.
          iClose_genpur_reg_map r_env "[Hr_env $Hmreg']" "Hmreg'".
          iClose_genpur_reg_map r_t0 "[Hr_self $Hmreg']" "Hmreg'".
          repeat (rewrite -(delete_commute _ r_t1)). 
          iClose_genpur_reg_map r_t1 "[Hr_t1 $Hmreg']" "Hmreg'".
          iDestruct ("Hfull'") as %Hfull. 
          iDestruct (big_sepM_to_big_sepL _ (list_difference all_registers [PC; r_stk; r_adv]) with "Hmreg'") as "$Hmlist". 
          - apply NoDup_ListNoDup,NoDup_list_difference. apply all_registers_NoDup.
          - intros r0 Hin. apply elem_of_list_difference in Hin as [Hin Hnin].
            revert Hnin. repeat rewrite not_elem_of_cons. intros (Hne1 & Hne2 & Hne3 & _).
            destruct (decide (r0 = r_t1));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            destruct (decide (r0 = r_t0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            destruct (decide (r0 = r_env));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            rewrite delete_insert_delete. repeat (rewrite lookup_delete_ne;auto). apply Hfull. }
        iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hstack_adv & Hscall)".
        iDestruct (big_sepL2_length with "Hprog") as %Hrest_length1. simpl in Hrest_length1.
        assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last1 a_last) as Hvpc2.
        { intros mid Hmid. assert (a0 <= s_last1)%a as Hle.
          { apply contiguous_between_bounds in Hcont_scall1.
            apply contiguous_between_bounds in Hcont_scall.
            revert Hcont_scall Hcont_scall1 Hcontge1 Hcontge;clear. solve_addr.
          } 
          apply isCorrectPC_inrange with a0 a_last; auto.
          revert Hmid Hle. clear. solve_addr. }
        (* jmp r_adv *)
        destruct rest1;[inversion Hrest_length1|]. 
        iPrologue rest1 Hrest_length1 "Hprog". apply contiguous_between_cons_inv_first in Hcont_rest1 as Heq. subst s_last1. 
        iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
          [apply jmp_i|apply PermFlows_refl|iCorrectPC a27 a_last|..].
        iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".
        (* again we are jumping to unknown code. We will now need to close all our invariants so we can 
           reestablish the FTLR on the new state *)
        (* we close the invariant for our program *)
        iMod ("Hcls'" with "[Hprog_done Hprog Hinstr Hscall $Hna]") as "Hna".
        { iNext. iDestruct "Hprog_done" as "(Hpush2 & push1 & Ha19 & Hpop1 & Hpop2 & Hpop3 &
                                             Ha8 & Ha9 & Hrest0_first & Hprog_done)".
          iApply (big_sepL2_app with "Hprog_done [-]").
          iFrame "Hrest0_first Ha9 Ha8". 
          iApply (big_sepL2_app with "Hpop3 [-]").
          iApply (big_sepL2_app with "Hpop2 [-]").
          iApply (big_sepL2_app with "Hpop1 [-]").
          iFrame "Ha19".
          iApply (big_sepL2_app with "push1 [-]").
          iApply (big_sepL2_app with "Hpush2 [-]").
          rewrite Hrest_app1. 
          iApply (big_sepL2_app with "Hscall [-]"). iFrame.
        }

        (* we separate the points to chunk from the persistent parts of the leftovers l'' *)
        iDestruct (temp_resources_split with "Hrest'") as (pws') "[#Hrest_valid' [#Hrev Hrest']]".
        iDestruct "Hrev" as %Hrev'.

        (* Allocate a static region to hold our frame *)

        (* first, put together again the resources for the frame *)

        iDestruct (region_mapsto_cons with "[$Ha3 $Hstack_own]") as "Hstack_own";
          [iContiguous_next Hcont1 1|..]. admit. 
        iDestruct (region_mapsto_cons with "[$Hb_r $Hstack_own]") as "Hstack_own";
          [iContiguous_next Hcont1 0|..]. admit. 

        (* we'll need that later to reason on the fact that the [zip] in the definition of
           m_frame indeed fully uses both lists *)
        iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_stack_own2.
        iDestruct (big_sepL2_length with "Hrest'") as %Hlength_rest''.

        match goal with |- context [ [[a2,stack_own_end]]↦ₐ[RWLX][[ ?instrs ]]%I ] =>
          set l_frame2 := instrs
        end.
        set static2_addrs := region_addrs a2 stack_own_end ++ l' ++ l''.
        set static2_instrs := (zip (repeat RWLX (length l_frame2)) l_frame2) ++ pws ++ pws'.
        set m_static2 := lists_to_static_region_perms static2_addrs static2_instrs.

        rewrite std_update_multiple_revoke_commute;auto.
        2: { rewrite /std_sta. cbn [fst]. eapply Forall_impl; [ apply HForall_static1 |].
             intros ? HH. cbn in HH. rewrite HH. intros ?%Some_eq_inj%encode_inj. congruence. }

        (* fact: l', l'', [a2,stack_own_end] and [stack_own_end, e_r] are all
           disjoint. We will need these facts for later. We can derive them now
           from separation logic and the fact that pointsto (with non-O perm)
           are exclusive... *)

        set static_res := (λ a p w, ∃ φ, a ↦ₐ<p> w ∗ ⌜∀Wv, Persistent (φ Wv)⌝ ∗ rel a p φ)%I.

        (* static_res includes a non-O pointsto, therefore it is exclusive *)
        iAssert (⌜∀ a p1 w1 p2 w2, static_res a p1 w1 -∗ static_res a p2 w2 -∗ False⌝)%I as %Hstatic_res_excl.
        { iIntros (? ? ? ? ?) "". iPureIntro. iIntros "H1 H2". iDestruct "H1" as (?) "[[? %] _]".
          iDestruct "H2" as (?) "[[? %] _]". iApply (cap_duplicate_false with "[$]"). split; assumption. }

        iAssert ([∗ list] a;pw ∈ l';pws, static_res a pw.1 pw.2)%I with "[Hl']" as "Hl'".
        { iDestruct (big_sepL2_sep with "[Hrest_valid $Hl']") as "Hl'". by iApply "Hrest_valid".
          iApply (big_sepL2_mono with "Hl'"). cbn. iIntros (k a' pw ? ?) "[H1 H2]".
          iDestruct "H2" as (? ? ?) "(? & ? & ?)". iExists _. iFrame. eauto. }

        iAssert ([∗ list] a;pw ∈ l'';pws', static_res a pw.1 pw.2)%I with "[Hrest']" as "Hrest'".
        { iDestruct (big_sepL2_sep with "[Hrest_valid' $Hrest']") as "Hrest'". by iApply "Hrest_valid'".
          iApply (big_sepL2_mono with "Hrest'"). cbn. iIntros (k a' pw ? ?) "[H1 H2]".
          iDestruct "H2" as (? ? ?) "(? & ? & ?)". iExists _. iFrame. eauto. }

        iAssert ([∗ list] a;w ∈ (region_addrs a2 stack_own_end);l_frame2, static_res a RWLX w)%I
          with "[Hstack_own]" as "Hstack_own".
        { rewrite (region_addrs_split a2 stack_own_end e_r). 2: admit.
          iDestruct (big_sepL_app with "Hstack_val") as "[Hstack_val' _]".
          iDestruct (big_sepL2_sep with "[Hstack_val' $Hstack_own]") as "Hstack_own".
          { iApply big_sepL2_to_big_sepL_l. auto. iApply "Hstack_val'". }
          iApply (big_sepL2_mono with "Hstack_own"). iIntros (? ? ? ? ?) "(? & ?)". unfold static_res.
          iExists _. iFrame. iSplitR; [iPureIntro; congruence|]. iPureIntro. intro; apply interp_persistent. }

        iDestruct (big_sepL2_app with "Hl' Hrest'") as "Hl'_rest'".

        (* we will need that later *)
        iAssert (⌜NoDup (region_addrs a2 e_r ++ l' ++ l'')⌝)%I as %Hstack_l'_l''_NoDup.
        { iAssert ([∗ list] a;w ∈ (region_addrs stack_own_end e_r);region_addrs_zeroes stack_own_end e_r, static_res a RWLX w)%I
            with "[Hstack_adv]" as "Hstack_adv".
          { rewrite (region_addrs_split a2 stack_own_end e_r). 2: admit.
            iDestruct (big_sepL_app with "Hstack_val") as "[_ Hstack_val']".
            iDestruct (big_sepL2_sep with "[Hstack_val' $Hstack_adv]") as "Hstack_adv".
            { iApply big_sepL2_to_big_sepL_l.
              (* TODO: region_addrs_length, region_addrs_zeroes_length *)
              by rewrite /region_addrs !region_addrs_aux_length /region_addrs_zeroes repeat_length //.
              iApply "Hstack_val'". }
            iApply (big_sepL2_mono with "Hstack_adv"). iIntros (? ? ? ? ?) "(? & ?)". unfold static_res.
            iExists _. iFrame. iSplitR; [iPureIntro; congruence|]. iPureIntro. intro; apply interp_persistent. }

          iApply (NoDup_of_sepL2_exclusive with "[] [Hstack_own Hstack_adv Hl'_rest']").
          2: { rewrite (region_addrs_split a2 stack_own_end e_r). 2: admit.
               iDestruct (big_sepL2_app with "Hstack_own Hstack_adv") as "Hstack".
               iDestruct (big_sepL2_zip_repeat with "Hstack") as "Hstack".
               iDestruct (big_sepL2_app with "Hstack Hl'_rest'") as "HH". iApply "HH". }
          iIntros (? [? ?] [? ?]). iApply Hstatic_res_excl. }

        (* Allocate the static region; for that we only need the part of Hstack we own *)
        iAssert ([∗ list] a;pw ∈ static2_addrs;static2_instrs, static_res a pw.1 pw.2)%I
          with "[Hstack_own Hl'_rest']" as "Hstatic".
        { iDestruct (big_sepL2_zip_repeat with "Hstack_own") as "Hstack_own".
          iApply (big_sepL2_app with "Hstack_own Hl'_rest'"). }

        iAssert (⌜NoDup static2_addrs⌝)%I as %Hstatic2_addrs_NoDup.
        { iApply (NoDup_of_sepL2_exclusive with "[] Hstatic").
          iIntros (? [? ?] [? ?]) "". iApply Hstatic_res_excl. }

        iDestruct (region_revoked_to_static _ m_static2 with "[$Hsts $Hr Hstatic]") as ">[Hsts Hr]".
        { iApply (big_sepL2_to_static_region_perms with "[] Hstatic"). assumption.
          iModIntro. iIntros (? ? pw ? ?) "H". iDestruct "H" as (?) "([? ?] & ? & ?)".
          iExists _,_,_. iFrame. iPureIntro. destruct pw; auto. }

        rewrite -std_update_multiple_revoke_commute;auto.
        2: { admit. }

        (* now that we have privately updated our resources, we can close the region invariant for the adv stack *)
        assert (list.last (a2 :: a3 :: a4 :: stack_own_b :: stack_own) = Some stack_own_end) as Hlast.
        { apply contiguous_between_link_last with a2 stack_own_last; [auto|apply gt_Sn_O|].
          revert Hstack_own_bound Hstack_own_bound'; clear. solve_addr. }

        (* To make some of the future proofs easier, let's make certain assertions about addresses in adv frame *)
        assert (∀ a, a ∈ region_addrs stack_own_end e_r -> a ∉ elements (dom (gset Addr) m_static2)) as Hnin2.
        { rewrite lists_to_static_perms_region_dom.
          2: { repeat rewrite app_length. rewrite Hlength_rest Hlength_rest''. auto. }
          intros a' Ha'. 
          rewrite elements_list_to_set;auto.
          assert (a' ∈ region_addrs a2 e_r) as Hin'.
          { rewrite -Hstack_localeq in Ha'. rewrite Hstack_eq.
            apply elem_of_app in Ha' as [Hl | Hr].
            - apply elem_of_list_singleton in Hl. subst.
              apply elem_of_app; left. apply elem_of_list_lookup. exists (11 - 1).
              rewrite -Hlength_own -last_lookup; auto.
            - by apply elem_of_app; right. 
          } 
          apply not_elem_of_app. split.
          - apply region_addrs_xor_elem_of with (c:=stack_own_end) in Hin' as [ [Hin' Hnin] | [Hin' Hnin] ];auto.
            eapply withinBounds_le_addr. apply Hwb3. 
          - rewrite NoDup_app in Hstack_l'_l''_NoDup |- *. intros (_ & HH & _). by apply HH.
        }
        assert (∀ a, a ∈ region_addrs stack_own_last e_r -> a ∉ elements (dom (gset Addr) m_static1)) as Hnin1.
        { rewrite lists_to_static_perms_region_dom.
          2: { repeat rewrite app_length. rewrite Hlength_rest . auto. }
          intros a' Ha'. 
          rewrite elements_list_to_set;auto.
          assert (a' ∈ region_addrs a2 e_r) as Hin'.
          { rewrite Hstack_eq. apply elem_of_app;right. auto. } 
          apply not_elem_of_app. split.
          - apply region_addrs_xor_elem_of with (c:=stack_own_last) in Hin' as [ [Hin' Hnin] | [Hin' Hnin] ];auto.
            eapply withinBounds_le_addr. apply Hwb2.
          - rewrite NoDup_app in Hstack_l'_l''_NoDup |- *. intros (_ & HH & _).
            by eapply (not_elem_of_app l' l''), HH.
        }

        match goal with |- context [ region ?W ] => set W4 := W end.
        
        (* finally we can now close the region: a_last' will be in state revoked in revoke(W3) *)
        assert (∀ x, x ∈ ([stack_own_end] ++ region_addrs stack_own_last e_r) ->
                       W4.1.1 !! encode x = Some (encode Revoked)) as Hlookup_revoked.
        { intros x Hsome.
          rewrite std_sta_update_multiple_lookup_same;auto.
          2: { apply Hnin2. rewrite Hstack_localeq in Hsome. auto. } 
          apply elem_of_app in Hsome as [Hl | Hr]. 
          + apply elem_of_list_singleton in Hl;subst.
            apply std_sta_update_multiple_lookup_in.
            rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;auto].
            rewrite elements_list_to_set;auto.
            apply elem_of_app;left. apply region_addrs_of_contiguous_between in Hcont1 as <-.
            apply elem_of_list_lookup. exists (11 - 1). rewrite -Hlength_own -last_lookup; auto.
          + rewrite std_sta_update_multiple_lookup_same;auto.
            apply elem_of_list_lookup in Hr as [k Hk]. 
            apply revoke_lookup_Temp. 
            eapply HtempW3; eauto. 
        }
        
        iMod (monotone_close _ (region_addrs stack_own_end e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
                with "[$Hsts $Hr Hstack_adv ]") as "[Hsts Hr]".
        { iClear "Hreg' Hfull' full Hf4 Hrel Hinv Hadv_val".
          rewrite Hstack_eq. 
          iDestruct (region_addrs_zeroes_trans with "Hstack_adv") as "Hstack_adv".
          rewrite /region_mapsto -Hstack_localeq.
          iDestruct (big_sepL_app with "Hstack_adv") as "[ [Hs_last' _] Hstack_adv]". 
          iDestruct (big_sepL_app with "Hstack_val") as "[Hstack_last Hstack_val']".
          iDestruct (big_sepL_lookup _ _ (length (a2 :: a3 :: a4 :: stack_own_b :: stack_own) - 1) stack_own_end with "Hstack_last") as "Hs_last_val";[by rewrite -last_lookup|].
          iApply big_sepL_sep. iSplitL.
          - iApply big_sepL_app. iSplitL "Hs_last'". 
            + iSimpl. iSplit;[|auto]. iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
              * iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
              * by repeat (rewrite fixpoint_interp1_eq /=).
            + iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hy".
              iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
              * iAlways. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
              * by repeat (rewrite fixpoint_interp1_eq /=).
          - iApply big_sepL_sep; iFrame "#". iSplit;[auto|]. iApply big_sepL_forall. iPureIntro.
            hnf. intros x a' Hin.
            apply Hlookup_revoked. apply elem_of_list_lookup. eauto. 
        }

        (* The resulting world is a private future world of W3 *)
        iSimpl in "Hsts".
        match goal with |- context [ region ?W ] => set W5 := W end.
        
        assert (related_sts_priv_world W3 W5) as Hrelated5.
        { eapply related_sts_priv_pub_trans_world;[|apply close_list_related_sts_pub;auto].
          eapply related_sts_priv_trans_world;[|apply related_sts_priv_world_static];auto.
          eapply related_sts_priv_trans_world;[|apply related_sts_priv_world_revoked with (m:=m_static1)];auto.
          eapply related_sts_priv_trans_world;[|apply revoke_related_sts_priv];auto.
          apply related_sts_pub_priv_world. destruct HW3lookup as [y Hy].
          split;[apply related_sts_pub_refl|simpl;eapply related_pub_local_1; eauto].
          - apply Forall_forall. intros a' Hin.
            apply revoke_lookup_Static. apply elem_of_elements in Hin. 
            apply Hall_static in Hin. rewrite /static in Hin.
            destruct (std_sta W3 !! encode a') eqn:Hsome;[subst|inversion Hin]. auto.
          - apply std_update_multiple_rel_is_std. auto.
          - apply Forall_forall. intros a' Hin.
            destruct (decide (a' ∈ (elements (dom (gset Addr) m_static1)))). 
            apply std_sta_update_multiple_lookup_in;auto.
            rewrite std_sta_update_multiple_lookup_same;auto.
            apply revoke_lookup_Temp. apply Hiff'. revert Hin n.
            rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest Hlength_rest'';auto]. 
            rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
            repeat rewrite elements_list_to_set;auto. rewrite Hstack_localeq'. clear; set_solver.
            apply withinBounds_le_addr in Hwb3 as [? _]. auto. 
          - repeat apply std_update_multiple_rel_is_std. auto.            
        }

        (* we can now finally monotonically update the region to match the new sts collection *)
        (* iDestruct (region_monotone _ W5 with "[] [] Hex") as "Hr";[rewrite /std_sta /=;auto|auto|..]. *)
        (* iAssert (sts_full_world sts_std W5) with "Hsts" as "Hsts". *)
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hreli.
        (* We choose the r *)
        evar (r2 : gmap RegName Word).
        instantiate (r2 := <[PC    := inl 0%Z]>
                          (<[r_stk := inr (RWLX, Local, stack_own_end, e_r, stack_new)]>
                           (<[r_t0  := inr (E, Local, a2, e_r, a4)]>
                            (<[r_adv := inr (E, Global, b, e, a)]>
                             (create_gmap_default
                                (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
        (* We have all the resources of r *)
        iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r2))
          with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
        { iApply (registers_mapsto_resources with "Hr_gen Hr_stk Hr_t0 Hr_adv HPC"). } 
        (* r contrains all registers *)
        iAssert (full_map r2) as "#Hfull2";[iApply r_full|].
        iSimpl in "Hadv_val".
        iAssert (interp_expression r2 W5 (inr (RX, Global, b, e, a)))
          as "Hvalid". 
        { iApply fundamental. iLeft; auto. iExists RX. iSplit;[iPureIntro;apply PermFlows_refl|]. 
          iApply (adv_monotone with "Hadv_val");[|auto].
          eapply related_sts_priv_trans_world;[|apply Hrelated5].
            by eapply related_sts_priv_pub_trans_world;[|apply Hrelated3]. }
        (* the adversary stack is valid in the W5 *)
        iAssert ([∗ list] a ∈ region_addrs stack_own_end e_r,
                 read_write_cond a RWLX (fixpoint interp1)
                 ∗ ⌜region_state_pwl W5 a⌝ ∧ ⌜region_std W5 a⌝)%I as "#Hstack_adv_val".
        { rewrite Hstack_eq.
          iDestruct (big_sepL_app with "Hstack_val") as "[Hstack_last Hstack_val']".
          iDestruct (big_sepL_lookup _ _ (length (a2 :: a3 :: a4 :: stack_own_b :: stack_own) - 1) stack_own_end with "Hstack_last")
            as "Hs_last_val";[by rewrite -last_lookup|].
          iApply big_sepL_sep. iSplit.
          - rewrite /region_mapsto -Hstack_localeq. 
            iApply big_sepL_app. iFrame "Hs_last_val".
            iSplit;[auto|]. 
            iApply (big_sepL_mono with "Hstack_val'").
            iIntros (g y Hsome) "Hy". iFrame.
          - iApply big_sepL_forall. iPureIntro.
            intros g y Hsome. split. 
            + apply close_list_std_sta_revoked; auto.
              { apply elem_of_list_fmap. exists y. split; auto.
                apply elem_of_list_lookup_2 with g. auto. }
              apply Hlookup_revoked. rewrite Hstack_localeq.
              apply elem_of_list_lookup_2 with g. auto.
            + eapply related_sts_rel_std.
              { apply related_sts_priv_trans_world with W3;auto.
                apply related_sts_priv_pub_trans_world with W'';auto. eauto. }
              rewrite Hstack_eq in Hrevoked.
              apply Forall_app in Hrevoked as [Hrevoked_last Hrevoked].
              revert Hrevoked. rewrite Forall_forall =>Hrevoked.
              apply (Forall_lookup_1 _ _ (length (a2 :: a3 :: a4 :: stack_own_b :: stack_own) - 1) stack_own_end)
                in Hrevoked_last as [Hrel_last Hlookup_last]; [|by rewrite -last_lookup].
              rewrite -Hstack_localeq in Hsome.
              destruct g.
              * simpl in Hsome; inversion Hsome as [Heq]. rewrite -Heq. eauto.
              * simpl in Hsome. apply Hrevoked. apply elem_of_list_lookup; eauto.  
        }
        (* We are now ready to show that all registers point to a valid word *)
        iDestruct (sts_full_world_std with "Hsts") as %Hstd5.
        iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W5 (r2 !r! r1))%I
          with "[-Hsts Hr Hmaps Hvalid Hna]" as "Hreg".
        { iIntros (r1).
          assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
              [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
          { destruct (decide (r1 = PC)); [by left|right].
            destruct (decide (r1 = r_stk)); [by left|right].
            destruct (decide (r1 = r_t0)); [by left|right].
            destruct (decide (r1 = r_adv)); [by left|right;auto].  
          }
          - iIntros "%". contradiction.
          - assert (r2 !! r_stk = Some (inr (RWLX, Local, stack_own_end, e_r, stack_new))) as Hr_stk; auto. 
            rewrite /RegLocate Hr_stk. repeat rewrite fixpoint_interp1_eq. 
            iIntros (_). iExists RWLX. iSplitR; [auto|].
            iAssert ([∗ list] a ∈ region_addrs stack_own_end e_r, read_write_cond a RWLX (fixpoint interp1)
                                                             ∧ ⌜region_state_pwl W5 a⌝ ∧ ⌜region_std W5 a⌝)%I as "#Hstack_adv_val'". 
            { iApply (big_sepL_mono with "Hstack_adv_val"). iIntros (g y Hsome) "(Hr & Hrev & Hstd)". iFrame. }
            iFrame "Hstack_adv_val'". 
            iAlways.
            rewrite /exec_cond.
            iIntros (y r3 W6 Hay Hrelated6). iNext.
            iApply fundamental.
            + iRight. iRight. done.
            + iExists RWLX. iSplit; auto. simpl.
              iApply (adv_stack_monotone with "Hstack_adv_val'"); auto. 
          - (* continuation *)
            iIntros (_). clear Hr_t0. 
            assert (r2 !! r_t0 = Some (inr (E, Local, a2, e_r, a4))) as Hr_t0; auto. 
            rewrite /RegLocate Hr_t0. repeat rewrite fixpoint_interp1_eq. iSimpl. 
            (* prove continuation *)
            iAlways.
            iIntros (r3 W6 Hrelated6).
            iNext.

            (* We start by asserting that the adversary stack is still temporary *)
            iAssert ([∗ list] a ∈ (region_addrs stack_own_end e_r),
                     ⌜W6.1.1 !! encode a = Some (encode Temporary)⌝
                    ∗ rel a RWLX (λ Wv : prodO STS STS * Word, ((fixpoint interp1) Wv.1) Wv.2)
                )%I as "#Hstack_adv_tmp'".
            { iApply (big_sepL_mono with "Hstack_adv_val"). iIntros (k y Hsome) "(Hrel & Htemp & Hstd)".
              iFrame. iDestruct "Htemp" as %Htemp6; iDestruct "Hstd" as %Hstd6. 
              iPureIntro.
              apply region_state_pwl_monotone with W5; eauto. }
            iDestruct (big_sepL_sep with "Hstack_adv_tmp'") as "[Htemp _]". 
            iDestruct (big_sepL_forall with "Htemp") as %HtempW6. iClear "Htemp". 
            
            (* we want to distinguish between the case where the local stack frame is Static (step through 
               continuation) and where the local stack frame is temporary (apply FTLR) *)
            assert (forall a, a ∈ region_addrs a2 stack_own_end ++ l' ++ l'' ->
                         (std_sta W6) !! (encode a) = Some (encode Temporary) ∨
                         (std_sta W6) !! (encode a) = Some (encode (Static m_static2)))
              as Hcases'.
            { intros a' Hin. apply or_comm,related_sts_pub_world_static with W5;auto.
              - apply std_rel_update_multiple_lookup_std_i. 
                rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                rewrite elements_list_to_set;auto. apply elem_of_list_fmap. repeat eexists. auto. 
              - assert (std_sta W4 !! encode a' = Some (encode (Static m_static2))) as Hlookup.
                { apply std_sta_update_multiple_lookup_in_i.
                  rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                  rewrite elements_list_to_set;auto. apply elem_of_list_fmap. repeat eexists. auto. }
                rewrite -close_list_std_sta_same_alt;auto. rewrite Hlookup. intros Hcontr;inversion Hcontr as [heq].
                apply encode_inj in heq. done.
            }
            assert (a2 ∈ region_addrs a2 stack_own_end ++ l' ++ l'') as Ha2in.
            { apply elem_of_app. left. apply elem_of_list_lookup. exists 0.
              apply region_addrs_first. assert ((a2 + 2)%a = Some a4) as Hincr.
              eapply (contiguous_between_incr_addr _ 2 a2 a4);[apply Hcont1|auto].
              revert Hstack_own_bound1 Hincr. clear. solve_addr. }
            pose proof (Hcases' _ Ha2in) as [Hm_temp' | Hm_static'].
            { iSimpl. 
              iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)". 
              iSplit; [auto|rewrite /interp_conf].
              (* first we want to assert that if a2 is Temporary, the remaining addresses are also temporary *)
              iAssert (⌜∀ a : Addr, a ∈ dom (gset Addr) m_static2 → temporary W6 a⌝)%I as %Hm_frame_temp_all.
              { iIntros (a'). rewrite /m_static2. 
                rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                iIntros (Hin). apply elem_of_list_to_set in Hin. 
                pose proof (Hcases' a' Hin) as [Htemp' | Hstatic].
                - rewrite /temporary. rewrite Htemp'. auto.
                - iDestruct (full_sts_static_all with "Hsts Hr") as %Hforall;[eauto|]. exfalso.
                  assert (a2 ∈ dom (gset Addr) m_static2) as Hin'.
                  { rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                    apply elem_of_list_to_set. auto. }
                  apply Hforall in Hin'. rewrite /static Hm_temp' in Hin'. apply encode_inj in Hin'. done. 
              }
              iDestruct (fundamental W6 r3 RX Local a2 e_r a4 with "[] [] [-]") as "[_ Hcont]";[by iLeft| |iFrame "∗ #"|..].
              { iSimpl. iExists RWLX. iSplit;[auto|].
                iApply (big_sepL_mono with "Hstack_val").
                iIntros (k y Hk) "Hrel". iFrame. iPureIntro.            
                split;[left|].
                - (* first we assert that the region is all in state temporary *)
                  rewrite (region_addrs_split _ stack_own_end) in Hk. 
                  assert (y ∈ region_addrs a2 stack_own_end ++ region_addrs stack_own_end e_r) as Hk'.
                  { apply elem_of_list_lookup. eauto. }
                  apply elem_of_app in Hk' as [Hframe | Hadv].
                  + assert (y ∈ dom (gset Addr) m_static2) as Hk'.
                    { rewrite lists_to_static_perms_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                      apply elem_of_list_to_set. apply elem_of_app. by left. }
                    apply Hm_frame_temp_all in Hk'. rewrite /temporary in Hk'.
                    destruct (W6.1.1 !! encode y) eqn:Hsome;[subst;auto|inversion Hk'].
                  + apply elem_of_list_lookup in Hadv as [j Hj]. by apply HtempW6 with j. 
                  + apply withinBounds_le_addr in Hwb3 as [Hle1 Hle2]. revert Hle1 Hle2.
                    clear. solve_addr. 
                - apply related_sts_rel_std with W.
                  eapply related_sts_priv_pub_trans_world;[|apply Hrelated6].
                  eapply related_sts_priv_trans_world;[|apply Hrelated5].
                  eapply related_sts_priv_pub_trans_world;[|apply Hrelated3];auto. 
                  revert Htemp. rewrite Forall_forall =>Htemp. apply Htemp. apply elem_of_list_lookup;eauto. 
              }
              iFrame. 
            }
            
            (* Now we are in the case where m_static2 is still static. We will have to open the region and step through
               the continuation as usual. *)
            iSimpl. 
            iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)".
            (* we might need to remember that W3 is standard *)
            iDestruct (sts_full_world_std with "Hsts") as %Hstd6.
            (* since a2 is static, all of dom(m_static1) is static *)
            iDestruct (full_sts_static_all with "Hsts Hr") as %Hall_static';eauto.
            iSplit; [auto|rewrite /interp_conf].
            (* get the PC, currently pointing to the activation record *)
            iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
            iAssert (⌜∃ M, dom_equal W6.1.1 M⌝)%I as %Hdom_equal.
            { rewrite region_eq /region_def. iDestruct "Hr" as (M Mρ) "(_ & #Hdom & _)".
              iDestruct "Hdom" as %Hdom. iPureIntro. exists M. apply Hdom. }
            (* get some registers *)
            iGet_genpur_reg_map r3 r_t1 "Hmreg'" "Hfull3" "[Hr_t1 Hmreg']".
            iGet_genpur_reg_map r3 r_stk "Hmreg'" "Hfull3" "[Hr_stk Hmreg']".
            iGet_genpur_reg_map r3 r_adv "Hmreg'" "Hfull3" "[Hr_adv Hmreg']".
            iGet_genpur_reg_map r3 r_env "Hmreg'" "Hfull3" "[Hr_env Hmreg']".
            iGet_genpur_reg_map r3 r_t0 "Hmreg'" "Hfull3" "[Hr_t0 Hmreg']".
            iGet_genpur_reg_map r3 r_t2 "Hmreg'" "Hfull3" "[Hr_t2 Hmreg']".
            
            (* Open the static region for the local stack frame *)
            iDestruct (region_open_static with "[$Hr $Hsts]") as "(Hr & Hsts & Hstates & Hframe & %)";
              [apply Hm_static'|].
            iAssert ( a2 ↦ₐ[RWLX] inr (RWX, Global, d, d', d)
                    ∗ a3 ↦ₐ[RWLX] inr (E, g_ret, b_ret, e_ret, a_ret)
                    ∗ [[a4,stack_own_end]] ↦ₐ[RWLX] 
                           [[ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                               inr (pc_p, pc_g, pc_b, pc_e, a27); inr (RWLX, Local, a2, e_r, stack_new)] ]]
                    ∗ [∗ list] a;pw ∈ l'++l''; pws++pws', a ↦ₐ[pw.1] pw.2)%I
              with "[Hframe]" as "(Ha2 & Ha3 & Hframe & Hrest)".
            { iDestruct (static_region_perms_to_big_sepL2 _ _ (λ a p v, a ↦ₐ[p] v)%I with "[] Hframe")
                as "Hframe";[auto|..]. 
              { repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto. }
              { iAlways. iIntros (k pw1 pw2 Hlookup1 Hlookup2) "Hr".
                iDestruct "Hr" as (p v Heq) "Hr". inversion Heq. iFrame. 
              }
              iDestruct (big_sepL2_app' with "Hframe") as "[Hframe $]";[auto|].
              iDestruct (big_sepL2_zip_repeat _ _ (λ a p v, a ↦ₐ[p] v)%I with "Hframe") as "Hframe".
              iDestruct (region_mapsto_cons with "Hframe") as "[Ha2 Hframe]"; [iContiguous_next Hcont1 0|..].
              { apply contiguous_between_middle_bounds with (i:=1) (ai:=a3) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iDestruct (region_mapsto_cons with "Hframe") as "[Ha3 Hframe]"; [iContiguous_next Hcont1 1|..].
              { apply contiguous_between_middle_bounds with (i:=2) (ai:=a4) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame. 
            }
            (* prepare the new stack value *)
            assert (∃ stack_new_1, (stack_new_1 + 1)%a = Some stack_new) as [stack_new_1 Hstack_new_1].
            { revert Hstack_own_bound' Hstack_new. clear. intros H. destruct (stack_own_b + 5)%a eqn:Hsome;[|solve_addr].
              exists a. solve_addr. }
            (* step through instructions in activation record *)
            iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
              [|done|iContiguous_next Hcont_rest1 0|apply Hstack_new_1|revert Hstack_own_bound1 Hstack_own_bound1'; clear; solve_addr|..].
            { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb3.
              apply (contiguous_between_middle_bounds _ 2 a4) in Hcont1;[|auto].
              revert Hwb3 Hcont1 Hmid. clear. solve_addr. 
            }
            iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
            iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
            iDestruct "Hr_t1" as (wrt1') "Hr_t1".
            (* we don't want to close the stack invariant yet, as we will now need to pop it *)
            (* go through rest of the program. We will now need to open the invariant and destruct it into its done and prog part *)
            (* sub r_t1 0 7 *)
            iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|]. 
            rewrite Hrest_app1 /=. repeat rewrite app_comm_cons. rewrite app_assoc.
            rewrite /awkward_example /awkward_instrs.
            iDestruct (mapsto_decomposition _ _ _ ([store_z r_env 0] ++
                                                   push_r_instrs r_stk r_env ++
                                                   push_r_instrs r_stk r_t0 ++
                                                   push_r_instrs r_stk r_adv ++
                                                   scall_prologue_instrs 65 r_adv ++
                                                   [jmp r_adv;
                                                    sub_z_z r_t1 0 7;
                                                    lea_r r_stk r_t1] ++
                                                   pop_instrs r_stk r_adv ++
                                                   pop_instrs r_stk r_t0 ++
                                                   pop_instrs r_stk r_env ++
                                                   [store_z r_env 1] ++
                                                   push_r_instrs r_stk r_env ++
                                                   push_r_instrs r_stk r_t0 ++
                                                   scall_prologue_instrs 65 r_adv) with "Hprog")
              as "[Hprog_done [Ha Hprog] ]". 
            { simpl. inversion Hscall_length as [Heq]. inversion Hscall_length1 as [Heq']. rewrite app_length Heq /=. rewrite Heq'. done. }
            (* let's prove some practical lemmas before continuing *)
            (* assert (last (rest1_first :: a27 :: rest1) = Some a_last) as Hlast1. *)
            (* { rewrite Hrest_app in Hlast. repeat rewrite app_comm_cons in Hlast. *)
            (*   rewrite -last_app_eq in Hlast;[|simpl;apply gt_Sn_O]. *)
            (*   rewrite Hrest_app1 in Hlast. repeat rewrite app_comm_cons in Hlast. *)
            (*   by rewrite -last_app_eq in Hlast;[|simpl;apply gt_Sn_O]. } *)
            iCombine "Ha" "Hprog_done" as "Hprog_done".
            (* sub r_t1 0 7 *)
            iPrologue rest1 Hrest_length1 "Hprog".
            iApply (wp_add_sub_lt_success_z_z with "[$HPC Hr_t1 $Hinstr]");
              [apply sub_z_z_i|right;left;eauto|iContiguous_next Hcont_rest1 1|apply PermFlows_refl|iCorrectPC a27 a_last|
               iSimpl;iFrame;eauto|].
            iEpilogue "(HPC & Hinstr & Hr_t1)".
            iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* lea r_stk r_t1 *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            assert ((stack_new_1 + (0 - 7))%a = Some a3) as Hpop1.
            { assert ((a4 + 1)%a = Some stack_own_b) as Hincr;[iContiguous_next Hcont1 2|].
              assert ((a3 + 1)%a = Some a4) as Hincr';[iContiguous_next Hcont1 1|].
              revert Hstack_own_bound1' Hincr Hincr' Hstack_new_1. clear. solve_addr. }
            iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
              [apply lea_r_i|apply PermFlows_refl|iCorrectPC a27 a_last|
               iContiguous_next Hcont_rest1 2|apply Hpop1|auto..].
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* pop r_stk r_t0 *)
            do 3 (destruct rest1; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a30;a31;a32] (a33::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a3 + (0 - 1))%a = Some a2) as Hpop1.
            { rewrite -(addr_add_assoc a2 _ 1);[apply addr_add_0|iContiguous_next Hcont1 0]. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_t0 Ha3"];
              [split;[|split];iCorrectPC a27 a_last|apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|iContiguous_next Hcont_rest1 3|iContiguous_next Hcont_rest1 4|iContiguous_next Hcont_rest1 5|apply Hpop1|].
            iNext. iIntros "(HPC & Hpop & Hr_t0 & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* pop r_stk r_env *)
            do 3 (destruct rest1; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a33;a34;a35] (a36::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a2 + (0 - 1))%a = Some b_r') as Hpop1.
            { revert Hb_r'. clear. solve_addr. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Ha2"];
              [split;[|split];iCorrectPC a27 a_last|apply PermFlows_refl|iContiguous_bounds_withinBounds a2 stack_own_last|auto|iContiguous_next Hcont_rest1 6|iContiguous_next Hcont_rest1 7|iContiguous_next Hcont_rest1 8|apply Hpop1|].
            iNext. iIntros "(HPC & Hpop & Hr_env & Ha2 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* we have now arrived at the final load of the environment. we must here assert that the loaded
               value is indeed 1. We are able to show this since W6 is a public future world of W5, in which 
               invariant i is in state true *)
            (* load r_adv r_env *)
            iPrologue rest1 Hrest_length1 "Hprog".
            iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a37)
                                ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                                ∗ a36 ↦ₐ[pc_p] load_r r_adv r_env
                                ∗ sts_full_world sts_std W6
                                ∗ r_adv ↦ᵣ inl 1%Z
                                -∗ WP Seq (Instr Executable) {{ v, φ v }})
                            -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
              with "[HPC Hinstr Hr_env Hr_adv Hsts]" as "Hload_step".
            { iIntros (φ') "Hφ'".
              iInv ι as (x) "[>Hstate Hb]" "Hcls".
              iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hi.
              assert (x = true) as ->.
              { apply related_pub_lookup_local with W5 W6 i;auto. repeat rewrite std_update_multiple_loc_sta.
                apply lookup_insert. }
              iDestruct "Hb" as ">Hb".
              iAssert (⌜(d =? a36)%a = false⌝)%I as %Hne.
              { destruct (d =? a36)%a eqn:Heq;auto. apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
                iDestruct (cap_duplicate_false with "[$Hinstr $Hb]") as "Hfalse";[|done].
                eapply isCorrectPC_contiguous_range with (a := a0) in Hvpc;[|eauto|];last (by apply elem_of_cons;left). 
                destruct pc_p;auto.
                inversion Hvpc as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
              iApply (wp_load_success with "[$HPC $Hinstr $Hr_adv $Hr_env Hb]");
                [apply load_r_i|apply PermFlows_refl|iCorrectPC a27 a_last
                 |auto|iContiguous_next Hcont_rest1 9|rewrite Hne;iFrame;iPureIntro;apply PermFlows_refl|rewrite Hne].
              iNext. iIntros "(HPC & Hr_adv & Ha36 & Hr_env & Hd)".
              iMod ("Hcls" with "[Hstate Hd]") as "_".
              { iNext. iExists true. iFrame. }
              iModIntro. iApply wp_pure_step_later;auto;iNext.
              iApply "Hφ'". iFrame. 
            }
            iApply "Hload_step".
            iNext. iIntros "(HPC & Hr_env & Ha36 & Hsts & Hr_adv)".
            (* We can now assert that r_adv indeed points to 1 *)
            (* move r_t1 PC *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            iApply (wp_move_success_reg_fromPC with "[$HPC $Hr_t1 $Hinstr]");
              [apply move_r_i|apply PermFlows_refl|iCorrectPC a27 a_last|
               iContiguous_next Hcont_rest1 10|auto|..].
            iEpilogue "(HPC & Hinstr & Hr_t1)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* lea r_t1 5 *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            do 2 (destruct rest1;[inversion Hrest_length1|]).
            assert ((a37 + 62)%a = Some a_last) as Hincr.
            { revert Hcont_rest1 Hrest_length1. clear. intros Hcont_rest1 Hrest_length1.
              assert ((a27 + 10)%a = Some a37);[eapply contiguous_between_incr_addr with (i:=10) (ai:=a37) in Hcont_rest1;auto|].
              apply contiguous_between_length in Hcont_rest1. solve_addr. }
            iApply (wp_lea_success_z with "[$HPC $Hinstr $Hr_t1]");
              [apply lea_z_i|apply PermFlows_refl|iCorrectPC a27 a_last|
               iContiguous_next Hcont_rest1 11|apply Hincr|auto|..].
            { apply isCorrectPC_range_npE in Hvpc; auto. revert Hf2;clear; intros H. apply contiguous_between_length in H. solve_addr. }
            iEpilogue "(HPC & Hinstr & Hr_t1)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* sub r_adv r_adv 1 *)
            iDestruct "Hprog" as "[Hinstr Hprog]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hinstr $Hr_adv]");
              [apply sub_r_z_i|right;left;eauto|iContiguous_next Hcont_rest1 12|apply PermFlows_refl|iCorrectPC a27 a_last|..]. 
            iEpilogue "(HPC & Hinstr & Hr_adv)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* jnz r_self *)
            iDestruct "Hprog" as "[Hinstr Hprog]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_jnz_success_next with "[$HPC $Hinstr $Hr_t1 $Hr_adv]");
              [apply jnz_i|apply PermFlows_refl|iCorrectPC a27 a_last|iContiguous_next Hcont_rest1 13|..].
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_adv)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".  
            (* Since the assertion succeeded, we are now ready to jump back to the adv who called us *)
            (* Before we can return to the adversary, we must clear the local stack frame and registers. This will 
               allow us to release the local frame, and show we are in a public future world by reinstating 
               the full stack invariant *)
            (* we must prepare the stack capability so that we only clear the local stack frame *)
            (* getb r_t1 r_stk *)
            iPrologue rest1 Hrest_length1 "Hprog". 
            iApply (wp_Get_success with "[$HPC $Hinstr $Hr_stk $Hr_t1]");
              [apply getb_i|auto|apply PermFlows_refl|iCorrectPC a27 a_last|iContiguous_next Hcont_rest1 14|auto..].
            iEpilogue "(HPC & Hinstr & Hr_stk & Hr_t1)"; iSimpl in "Hr_t1"; iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* add_r_z r_t2 r_t1 8 *)
            iPrologue rest1 Hrest_length1 "Hprog".
            iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hinstr $Hr_t2 $Hr_t1]");
              [apply add_r_z_i|by left|iContiguous_next Hcont_rest1 15|apply PermFlows_refl|iCorrectPC a27 a_last|..].
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_t2)"; iSimpl in "Hr_t2"; iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* subseg r_stk r_t1 r_t2 *)
            assert (z_to_addr a2 = Some a2) as Ha2.
            { rewrite /z_to_addr. revert Hlink. rewrite Hlength_own. clear; intros.
              destruct (Z_le_dec a2 MemNum);destruct a2;[f_equiv;by apply z_of_eq|]. solve_addr. }
            assert ((a2 + 10)%a = Some stack_own_end) as Ha2_stack_own_end.
            { assert ((a2 + 3)%a = Some stack_own_b) as Ha2_stack_own_b.
              { apply (contiguous_between_incr_addr _ 3 _ stack_own_b) in Hcont1; auto. }
              revert Ha2_stack_own_b Hstack_own_bound'. 
              clear; intros. solve_addr. }
            iPrologue rest1 Hrest_length1 "Hprog".
            iApply (wp_subseg_success with "[$HPC $Hinstr $Hr_stk $Hr_t1 $Hr_t2]");
              [apply subseg_r_r_i|apply PermFlows_refl|iCorrectPC a27 a_last|
               split;[apply Ha2|revert Ha2_stack_own_end;clear;done]|
               auto|auto| |iContiguous_next Hcont_rest1 16|..].
            { rewrite !andb_true_iff !Z.leb_le. apply withinBounds_le_addr in Hwb2.
              assert ((a2 + 3)%a = Some stack_own_b) as Ha2_stack_own_b.
              { apply (contiguous_between_incr_addr _ 3 _ stack_own_b) in Hcont1; auto. }
              revert Hbounds Hstack_own_bound Hwb2 Ha2_stack_own_end Ha2_stack_own_b.
              clear. repeat split; try lia; try solve_addr. }
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_t2 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            iAssert (∃ ws : list Word, [[a2,stack_own_end]]↦ₐ[RWLX][[ws]])%I with "[Hframe Ha2 Ha3]" as "Hstack".
            { iExists l_frame2. 
              iApply region_mapsto_cons;[iContiguous_next Hcont1 0|..].
              { apply contiguous_between_middle_bounds with (i:=1) (ai:=a3) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame.
              iApply region_mapsto_cons;[iContiguous_next Hcont1 1|..].
              { apply contiguous_between_middle_bounds with (i:=2) (ai:=a4) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame. 
            }
            (* We are now ready to clear the stack *)
            assert (contiguous_between (a44 :: rest1) a44 a_last) as Hcont_weak.
            { repeat (inversion Hcont_rest1 as [|????? Hf2']; subst; auto; clear Hcont_rest1; rename Hf2' into Hcont_rest1). }
            iDestruct (contiguous_between_program_split with "Hprog") as (mclear_addrs rclear_addrs rclear_first)
                                                                           "(Hmclear & Hrclear & #Hcont)"; [eauto|].
            iDestruct "Hcont" as %(Hcont_mclear & Hcont_rest2 & Hstack_eq2 & Hlink2).
            iDestruct (big_sepL2_length with "Hmclear") as %Hmclear_length.
            assert (7 < (length mclear_addrs)) as Hlt7;[rewrite Hmclear_length /=;clear;lia|].
            assert (17 < (length mclear_addrs)) as Hlt17;[rewrite Hmclear_length /=;clear;lia|].
            apply lookup_lt_is_Some_2 in Hlt7 as [ai Hai].
            apply lookup_lt_is_Some_2 in Hlt17 as [aj Haj].
            assert (ai + 10 = Some aj)%a.
            { rewrite (_: 10%Z = Z.of_nat (10 : nat)).
              eapply contiguous_between_incr_addr_middle; [eapply Hcont_mclear|..]. all: eauto. }
            assert (a44 < rclear_first)%a as Hcontlt2.
            { revert Hmclear_length Hlink2. clear. solve_addr. }
            assert (a27 <= a44)%a as Hcontge2.
            { apply region_addrs_of_contiguous_between in Hcont_scall1. subst.
              revert Hscall_length1 Hcont_rest1 Hcontlt1 Hcontlt2. clear =>Hscall_length Hf2 Hcontlt Hcontlt2.
              apply contiguous_between_middle_bounds with (i := 17) (ai := a44) in Hf2;[solve_addr|auto].
            }
            iApply (mclear_spec with "[-]"); last (rewrite /region_mapsto; iFrame "HPC Hr_stk Hstack");
              [ apply Hcont_mclear | ..]; eauto.
            { assert (rclear_first <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest2|].
              intros mid Hmid. apply isCorrectPC_inrange with a0 a_last; auto.
              revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid Hcontlt2 Hcontge2. clear; intros. split; try solve_addr.
            }
            { apply PermFlows_refl. }
            { apply PermFlows_refl. } 
            { apply withinBounds_le_addr in Hwb3 as [? _]. auto. }
            rewrite /mclear.
            destruct (strings.length mclear_addrs =? strings.length (mclear_instrs r_stk 10 2))%nat eqn:Hcontr;
              [|rewrite Hmclear_length in Hcontr;inversion Hcontr].
            iFrame "Hmclear".
            iGet_genpur_reg_map r3 r_t3 "Hmreg'" "Hfull3" "[Hr_t3 Hmreg']".
            iGet_genpur_reg_map r3 r_t4 "Hmreg'" "Hfull3" "[Hr_t4 Hmreg']".
            iGet_genpur_reg_map r3 r_t5 "Hmreg'" "Hfull3" "[Hr_t5 Hmreg']".
            iGet_genpur_reg_map r3 r_t6 "Hmreg'" "Hfull3" "[Hr_t6 Hmreg']".
            iSplitL "Hr_t4". iNext; eauto.
            iSplitL "Hr_t1". iNext; eauto.
            iSplitL "Hr_t2". iNext; eauto. 
            iSplitL "Hr_t3". iNext; eauto.
            iSplitL "Hr_t5". iNext; eauto.
            iSplitL "Hr_t6". iNext; eauto.
            iNext. iIntros "(HPC & Hr_t1 & Hr_t2' & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6 & Hr_stk & Hstack & Hmclear)".
            (* insert general purpose registers back into map *)
            repeat (rewrite -(delete_commute _ r_t2)). 
            iClose_genpur_reg_map r_t2 "[Hr_t2' $Hmreg']" "Hmreg'".
            rewrite delete_insert_delete. 
            repeat (rewrite -(delete_insert_ne _ _ r_t2); [|auto]).
            iClose_genpur_reg_map r_t6 "[Hr_t6 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t6); [|auto]).
            iClose_genpur_reg_map r_t5 "[Hr_t5 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t5); [|auto]).
            iClose_genpur_reg_map r_t4 "[Hr_t4 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t4); [|auto]).
            iClose_genpur_reg_map r_t3 "[Hr_t3 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t3); [|auto]).
            repeat (rewrite -(delete_commute _ r_t1)). 
            iClose_genpur_reg_map r_t1 "[Hr_t1 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t1); [|auto]).
            repeat (rewrite -(delete_commute _ r_env)). 
            iClose_genpur_reg_map r_env "[Hr_env $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_env); [|auto]).
            repeat (rewrite -(delete_commute _ r_adv)). 
            iClose_genpur_reg_map r_adv "[Hr_adv $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_adv); [|auto]).
            repeat (rewrite -(delete_commute _ r_stk)). 
            iClose_genpur_reg_map r_stk "[Hr_stk $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_stk); [|auto]).
            
            (* We are now ready to clear the registers *)
            iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length. 
            destruct rclear_addrs;[inversion Hrclear_length|].
            apply contiguous_between_cons_inv_first in Hcont_rest2 as Heq. subst rclear_first.
            iDestruct (contiguous_between_program_split with "Hrclear") as (rclear jmp_addrs jmp_addr)
                                                                           "(Hrclear & Hjmp & #Hcont)"; [eauto|].
            iDestruct "Hcont" as %(Hcont_rclear & Hcont_rest3 & Hstack_eq3 & Hlink3).
            clear Hrclear_length. iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
            assert (a45 < jmp_addr)%a as Hcontlt3.
            { revert Hrclear_length Hlink3. clear. rewrite /all_registers /=. solve_addr. }
            iApply (rclear_spec with "[-]"); last (iFrame "HPC Hrclear").
            { eauto. }
            { apply not_elem_of_list; apply elem_of_cons; by left. }
            { destruct rclear; inversion Hcont_rclear; eauto. inversion Hrclear_length. }
            { assert (jmp_addr <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest3|].
              intros mid Hmid. apply isCorrectPC_inrange with a0 a_last; auto.
              revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid Hcontlt2 Hcontge2 Hcontlt3. clear; intros. split; solve_addr.
            }
            { apply PermFlows_refl. }
            iSplitL "Hmreg'". 
            { iNext. iApply region_addrs_exists. iDestruct "Hfull3" as %Hfull3. 
              iApply (big_sepM_to_big_sepL with "Hmreg'");
                [apply NoDup_ListNoDup,NoDup_list_difference,all_registers_NoDup|].
              intros r0 Hin. assert (r0 ≠ PC ∧ r0 ≠ r_t0) as [Hne1 Hne2].
              { split; intros Hcontreq; subst r0. apply (not_elem_of_list PC all_registers [PC;r_t0]);auto. apply elem_of_cons; left; auto.
                apply (not_elem_of_list r_t0 all_registers [PC;r_t0]);auto. apply elem_of_cons; right; apply elem_of_cons; auto.
              }
              repeat (rewrite lookup_delete_ne;auto).
              destruct (decide (r_stk = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto]. 
              destruct (decide (r_adv = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto]. 
              destruct (decide (r_env = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto]. 
              destruct (decide (r_t1 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t3 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t4 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t5 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t6 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              destruct (decide (r_t2 = r0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              apply Hfull3. 
            }
            iNext. iIntros "(HPC & Hmreg' & Hrclear)".

            (* we must now invoke the callback validity of the adversary. This means we must show we 
               are currently in a public future world of W *)
            assert (related_sts_pub_world W (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary))
              as Hrelated7.
            { eapply related_pub_local_3 with (b:=a2) (l1:=l') (l2:=l'');
                [..|apply Hrelated3|apply Hrelated6]; eauto; simpl; auto.
              - revert Hwb2 Hwb3. clear. intros Hwb2 Hwb3.
                apply withinBounds_le_addr in Hwb2.
                apply withinBounds_le_addr in Hwb3. solve_addr.
              - repeat split;auto.
                rewrite lists_to_static_perms_region_dom. rewrite elements_list_to_set;auto. apply Permutation_app_comm. 
                repeat rewrite app_length. rewrite Hlength_rest;auto.
                rewrite lists_to_static_perms_region_dom. rewrite elements_list_to_set;auto.
                rewrite /static2_addrs Permutation_app_comm app_assoc. auto.
                repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto.
            }
            (* in order to handle the leftovers from the revocation of W3, we must also show that the final world 
               is a public future world of W3 *)
            assert (related_sts_pub_world W3 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary))
              as Hrelated8.
            { eapply related_pub_local_4 with (b:=a2) (l1:=l') (l2:=l'');
                [..|apply Hrelated3|apply Hrelated6]; eauto; simpl; auto.
              - revert Hwb2 Hwb3. clear. intros Hwb2 Hwb3.
                apply withinBounds_le_addr in Hwb2.
                apply withinBounds_le_addr in Hwb3. solve_addr.
              - repeat split;auto.
                rewrite lists_to_static_perms_region_dom. rewrite elements_list_to_set;auto. apply Permutation_app_comm. 
                repeat rewrite app_length. rewrite Hlength_rest;auto.
                rewrite lists_to_static_perms_region_dom. rewrite elements_list_to_set;auto.
                rewrite /static2_addrs Permutation_app_comm app_assoc. auto.
                repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto.
            } 

            (* We use the fact that the final world is public to W and W3 to close the full static frame *)
            iMod (region_close_static_to_temporary_alt m_static2 with "[$Hr $Hsts Hstack Hrest $Hstates]") as "[Hsts Hr]". 
            { set ψ := ((λ a p v, ∃ (p' : Perm) (_v : Word) (φ0 : prodO STS STS * Word → iPropI Σ),
                                ⌜∀ Wv : prodO STS STS * Word, Persistent (φ0 Wv)⌝
                                ∗ ⌜(p,v) = (p', _v)⌝
                                  ∗ temp_resources
                                      (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary) φ0 a p'
                                      ∗ rel a p' φ0))%I.
              iApply (big_sepL2_to_static_region_perms _ _ ψ)%I;[auto|..]. 
              { iAlways. iIntros (k a' pw Hpw1 Hpw2) "Hr". destruct pw. iFrame "Hr". }
              iApply (big_sepL2_app with "[Hstack]").
              - iApply (big_sepL2_zip_repeat _ _ ψ).
                iDestruct (region_addrs_zeroes_trans with "Hstack") as "Hstack".
                rewrite (region_addrs_split _ stack_own_end).
                iDestruct (big_sepL_app with "Hstack_val") as "[Hstack_val_frame _]".
                iDestruct (big_sepL_sep with "[Hstack_val_frame Hstack]") as "Hstack".
                iSplitL;[iFrame "Hstack"|iFrame "Hstack_val_frame"]. 
                iDestruct (big_sepL2_to_big_sepL_l _ _ l_frame2 with "Hstack") as "Hstack";[auto|].
                iApply (big_sepL2_mono with "Hstack"). 
                iIntros (k a' _v Hy1 Yy2) "[Ha' Hrel]".
                iExists RWLX,_v,(λ Wv : prodO STS STS * Word, ((fixpoint interp1) Wv.1) Wv.2).
                iSplit;[iPureIntro;apply _|]. iSplit;[auto|]. iFrame. iExists (inl 0%Z). iSimpl.
                iSplit;[auto|]. iFrame. iSplit.
                { iAlways. iIntros (W0 W'). iApply interp_monotone. }
                rewrite fixpoint_interp1_eq /=. auto.
                apply withinBounds_le_addr in Hwb3 as [Hb1 Hb2].
                revert Hb1 Hb2;clear. solve_addr.
              - iDestruct (big_sepL2_app' with "Hrest") as "[Hrest Hrest']";[auto|].
                iDestruct (big_sepL2_sep with "[Hrest]") as "Hrest".
                { iSplitL;[iFrame "Hrest"|iFrame "Hrest_valid"]. }
                iDestruct (big_sepL2_sep with "[Hrest']") as "Hrest'".
                { iSplitL;[iFrame "Hrest'"|iFrame "Hrest_valid'"]. }
                iApply (big_sepL2_app with "[Hrest]").
                + iApply (big_sepL2_mono with "Hrest").
                  iIntros (k a' pw Ha' Hpw) "[Ha' Hr]".
                  iDestruct "Hr" as (φ0 Hpers Hne) "(Hφ & Hrel & mono)".
                  rewrite /ψ. destruct pw. simpl. iExists p,w17,φ0.
                  repeat iSplit;auto. iExists w17. destruct (pwl p).
                  { iDestruct "mono" as "#mono".
                    iAssert (φ0 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary, w17))
                      with "[Hφ]" as "Hφ".
                    { iApply ("mono" with "[] Hφ"). auto. }
                    iFrame "∗ #". auto. }
                  { iDestruct "mono" as "#mono".
                    iAssert (φ0 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary, w17))
                      with "[Hφ]" as "Hφ".
                    { iApply ("mono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto. }
                    iFrame "∗ #". auto. }
                + iApply (big_sepL2_mono with "Hrest'").
                  iIntros (k a' pw Ha' Hpw) "[Ha' Hr]".
                  iDestruct "Hr" as (φ0 Hpers Hne) "(Hφ & Hrel & mono)".
                  rewrite /ψ. destruct pw. simpl. iExists p,w17,φ0.
                  repeat iSplit;auto. iExists w17. destruct (pwl p).
                  { iDestruct "mono" as "#mono".
                    iAssert (φ0 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary, w17))
                      with "[Hφ]" as "Hφ".
                    { iApply ("mono" with "[] Hφ"). auto. }
                    iFrame "∗ #". auto. }
                  { iDestruct "mono" as "#mono".
                    iAssert (φ0 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary, w17))
                      with "[Hφ]" as "Hφ".
                    { iApply ("mono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto. }
                    iFrame "∗ #". auto. }
            }

            (* we can finish reasoning about the program *)
            rewrite /enter_cond /interp_expr /interp_conf. iSimpl in "Hcallback".
            iAssert (future_world g_ret W (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary))%I
              as "#Hfuture". 
            { destruct g_ret; iSimpl.
              - iPureIntro. apply related_sts_pub_priv_world. apply Hrelated7.
              - iPureIntro. apply Hrelated7.
            } 
            evar (r4 : gmap RegName Word).
            instantiate (r4 := <[PC := inl 0%Z]>
                              (<[r_t0 := inr (E, g_ret, b_ret, e_ret, a_ret)]>
                               (create_gmap_default
                                  (list_difference all_registers [PC; r_t0]) (inl 0%Z)))).
            iDestruct ("Hcallback" $! r4 with "Hfuture") as "Hcallback_now".

            (* We can now finally jump to the return capability *)
            (* jmp r_t0 *)
            iDestruct (big_sepL2_length with "Hjmp") as %Hjmp_length.
            destruct jmp_addrs; [inversion Hjmp_length|].
            destruct jmp_addrs; [|inversion Hjmp_length].
            apply contiguous_between_cons_inv_first in Hcont_rest3 as Heq; subst jmp_addr.
            iDestruct "Hjmp" as "[Hinstr _]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_t0]");
              [apply jmp_i|apply PermFlows_refl|..].
            { (* apply contiguous_between_bounds in Hcont_rest3 as Hle. *)
              inversion Hcont_rest3 as [| a' b' c' l3 Hnext Hcont_rest4 Heq Hnil Heq'].
              inversion Hcont_rest4; subst. 
              apply Hvpc2. revert Hcontge2 Hcontlt2 Hcontlt3 Hnext. clear. solve_addr. }
            iEpilogue "(HPC & Hinstr & Hrt0)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 

            
            (* We close the program Iris invariant *)
            iMod ("Hcls'" with "[$Hna Hprog_done Hmclear Hrclear Ha36]") as "Hna". 
            { iNext. iDestruct "Hprog_done" as "(Ha46 & Ha43 & Ha42 & Ha41 & Ha40 & Ha39 & Ha38 & Ha37 & 
                                                 Hpop2 & Hpop1 & Ha29 & Ha28 & Ha27 & Hprog_done)".
              iApply (big_sepL2_app with "Hprog_done [-]").
              iFrame "Ha27 Ha28 Ha29". 
              iApply (big_sepL2_app with "Hpop1 [-]").
              iApply (big_sepL2_app with "Hpop2 [-]").
              iFrame "Ha37 Ha38 Ha39 Ha40 Ha36". rewrite Hstack_eq2 Hstack_eq3.
              iFrame "Ha41 Ha42 Ha43". 
              iApply (big_sepL2_app with "Hmclear [-]").
              iApply (big_sepL2_app with "Hrclear [-]").
              iFrame. done.
            } 
            iClear "Hf4 full Hfull' Hfull2 Hreg'".
            iSimpl in "HPC".

            (* we apply the callback to the current configuration *)
            iSpecialize ("Hcallback_now" with "[Hsts Hr Hmreg' HPC Hrt0 Hna]"). 
            { iFrame "Hna Hr Hsts". iSplitR;[iSplit|].
              - iPureIntro. clear. 
                intros x. rewrite /= /r4.
                destruct (decide (PC = x));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                destruct (decide (r_t0 = x));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                exists (inl 0%Z). apply create_gmap_default_lookup.
                apply elem_of_list_difference. split;[apply all_registers_correct|].
                repeat (apply not_elem_of_cons; split;[auto|try apply not_elem_of_nil]).
              - iIntros (r0 Hne). rewrite /RegLocate.
                rewrite /r4 lookup_insert_ne;auto.
                destruct (decide (r_t0 = r0));[subst;rewrite lookup_insert|].
                + iApply (interp_monotone $! Hrelated7).
                  rewrite /interp /= fixpoint_interp1_eq /=. iFrame "Hcallback". 
                + rewrite lookup_insert_ne;[|auto]. 
                  assert (r0 ∈ (list_difference all_registers [PC; r_t0])) as Hin.
                  { apply elem_of_list_difference. split;[apply all_registers_correct|].
                    repeat (apply not_elem_of_cons; split;[auto|try apply not_elem_of_nil]). }
                  rewrite fixpoint_interp1_eq. iRevert (Hin).
                  rewrite (create_gmap_default_lookup _ (inl 0%Z : Word) r0).
                  iIntros (Hin). rewrite Hin. iSimpl. done. 
              - rewrite /registers_mapsto (insert_insert _ PC).
                iApply (big_sepM_insert_2 with "[HPC]"); first iFrame.
                iApply (big_sepM_insert_2 with "[Hrt0]"); first iFrame.
                assert ((list_difference all_registers [PC;r_t0]) =
                        [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12;
                         r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24;
                         r_t25; r_t26; r_t27; r_t28; r_t29; r_t30; r_t31]) as ->; first auto. 
                rewrite /create_gmap_default. iSimpl in "Hmreg'". 
                repeat (iDestruct "Hmreg'" as "[Hr Hmreg']";
                        iApply (big_sepM_insert_2 with "[Hr]"); first iFrame).
                iApply big_sepM_empty. done. 
            }  
            iDestruct "Hcallback_now" as "[_ Hcallback_now]".
            iApply wp_wand_l. iFrame "Hcallback_now". 
            iIntros (v) "Hv". 
            iIntros (halted). 
            iDestruct ("Hv" $! halted) as (r0 W0) "(#Hfull & Hmreg' & #Hrelated & Hna & Hsts & Hr)". 
            iDestruct ("Hrelated") as %Hrelated10.
            iExists r0,W0. iFrame "Hfull Hmreg' Hsts Hr Hna".
            iPureIntro. 
            eapply related_sts_priv_trans_world;[|apply Hrelated10].
            apply related_sts_pub_priv_world. 
            apply related_sts_pub_world_static_to_temporary with (m:=m_static2);auto.
            apply Forall_forall. intros a' Hin. apply elem_of_elements in Hin. apply Hall_static' in Hin.
            rewrite /static in Hin. destruct (std_sta W6 !! encode a') eqn:Hsome;[|inversion Hin].
            subst. auto. 
          - rewrite Hr_t30. 
            assert (r2 !! r_adv = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
            rewrite /RegLocate Hr_t30_some. repeat rewrite fixpoint_interp1_eq. iSimpl. 
            iIntros (_). 
            iAlways. rewrite /enter_cond.
            iIntros (r0 W2 Hrelated2). 
            iNext. iApply fundamental.
            iLeft. done.
            iExists RX. iSplit; auto.
            iApply (adv_monotone with "Hadv_val"); auto.
            apply related_sts_priv_trans_world with W''; auto.
            eapply related_sts_priv_trans_world;[apply related_sts_pub_priv_world;apply Hrelated3|].
            apply related_sts_priv_trans_world with W5; auto.
          - rewrite r_zero; auto.
            repeat rewrite fixpoint_interp1_eq. iPureIntro. auto.
        }
        iDestruct ("Hvalid" with "[$Hsts $Hr $Hna $Hfull2 $Hmaps $Hreg]")
          as "[_ Ho]". 
        iApply wp_wand_r. iFrame.
        iIntros (v) "Hhalted".
        iIntros (->).
        iSpecialize ("Hhalted" with "[]");[auto|]. 
        iDestruct "Hhalted" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
        iExists _,_. iFrame. 
        iPureIntro. eapply related_sts_priv_trans_world;[apply Hrelated5|auto]. 
      - rewrite Hr_t30. 
        assert (r !! r_adv = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some fixpoint_interp1_eq. iSimpl. 
        iIntros (_). 
        iAlways. iIntros (r' W3 Hrelated3). 
        iNext. iApply fundamental.
        iLeft. done.
        iExists RX. iSplit; simpl; auto.
        iApply (adv_monotone with "Hadv_val");auto.
        eapply related_sts_priv_trans_world;[apply HWW''|auto].          
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        iIntros (Hne). 
        assert (r !r! r1 = inl 0%Z) as Hr1.
        { rewrite /RegLocate.
          destruct (r !! r1) eqn:Hsome; rewrite Hsome; last done. rewrite /r in Hsome. 
          do 4 (rewrite lookup_insert_ne in Hsome;auto). 
          assert (Some w2 = Some (inl 0%Z)) as Heq.
          { rewrite -Hsome. apply create_gmap_default_lookup.
            apply elem_of_list_difference. split; first apply all_registers_correct.
            repeat (apply not_elem_of_cons;split;auto).
            apply not_elem_of_nil. 
          }
            by inversion Heq. 
        }
        rewrite Hr1 fixpoint_interp1_eq. iPureIntro. eauto.         
    }
    iAssert (((interp_reg interp) W'' r))%I as "#HvalR";[iSimpl;auto|]. 
    iSpecialize ("Hvalid" with "[$HvalR $Hmaps Hsts $Hna $Hr]"); iFrame. 
    iDestruct "Hvalid" as "[_ Ho]". 
    rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros (->). 
    iSpecialize ("Htest" with "[]");[auto|]. 
    iDestruct "Htest" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
    iExists _,_. iFrame.
    iPureIntro. eapply related_sts_priv_trans_world;[apply HWW''|auto].
  Admitted.

End awkward_example.
