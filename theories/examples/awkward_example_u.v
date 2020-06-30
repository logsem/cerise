From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static region_invariants_uninitialized.
From cap_machine.examples Require Import region_macros stack_macros stack_macros_u stack_macros_helpers scall_u malloc awkward_example_helpers.
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

Lemma region_mapsto_cons {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
      `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
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

Definition lists_to_static_region (l1: list Addr) (l2: list Word): gmap Addr Word :=
  list_to_map (zip l1 l2).

Definition lists_to_uninitialised_region (l1 : list Addr) (l2 : list Word) : gmap Addr Word :=
  list_to_map (zip l1 l2). 

Lemma lists_to_static_region_cons a w l1 l2 :
  lists_to_static_region (a :: l1) (w :: l2) =
  <[ a := w ]> (lists_to_static_region l1 l2).
Proof. reflexivity. Qed.


Lemma lists_to_static_region_lookup_None l1 l2 a :
  a ∉ l1 → lists_to_static_region l1 l2 !! a = None.
Proof.
  revert l2. induction l1; eauto; []. intros l2 [? ?]%not_elem_of_cons.
  destruct l2.
  { cbn. eauto. }
  { rewrite lists_to_static_region_cons. rewrite lookup_insert_None. eauto. }
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

(* Lemma zip_elem_of {A B} (l1 : list A) (l2 : list B) k : *)
(*   is_Some (l1 !! k) -> (is_Some (l2 !! k)) ->  *)
    
Lemma lists_to_static_region_dom l1 l2 :
  length l1 = length l2 →
  dom (gset Addr) (lists_to_static_region l1 l2) = list_to_set l1.
Proof.
  intros Hlen. apply elem_of_equiv_L. intros x.
  rewrite /lists_to_static_region elem_of_dom elem_of_list_to_set.
  split. by intros [? ?%elem_of_list_to_map_2%elem_of_zip_l].
  intros Hx.
  destruct (elem_of_list_lookup_1 _ _ Hx) as [xi Hxi].
  pose proof (lookup_lt_Some _ _ _ Hxi).
  rewrite list_to_map_lookup_is_Some fst_zip //. lia.
Qed.

Lemma lists_to_static_region_size l1 l2 :
  length l1 = length l2 → NoDup l1 ->
  size (lists_to_static_region l1 l2) = length l1.
Proof.
  revert l2. 
  induction l1;intros l2 Hlen Hdup.
  - simpl. auto.
  - simpl. destruct l2;inversion Hlen. apply NoDup_cons in Hdup as [Hnin Hdup]. 
    rewrite -(IHl1 l2);auto.
    rewrite /lists_to_static_region /=. rewrite map_size_insert;auto. 
    apply not_elem_of_list_to_map_1. rewrite fst_zip;[auto|lia].
Qed. 

Lemma lists_to_uninitialised_region_dom l1 l2 :
  length l1 = length l2 →
  dom (gset Addr) (lists_to_uninitialised_region l1 l2) = list_to_set l1.
Proof.
  intros Hlen. apply elem_of_equiv_L. intros x.
  rewrite /lists_to_static_region elem_of_dom elem_of_list_to_set.
  split. by intros [? ?%elem_of_list_to_map_2%elem_of_zip_l].
  intros Hx.
  destruct (elem_of_list_lookup_1 _ _ Hx) as [xi Hxi].
  pose proof (lookup_lt_Some _ _ _ Hxi).
  rewrite list_to_map_lookup_is_Some. rewrite fst_zip //. lia. 
Qed.

Lemma big_sepL2_to_static_region {Σ: gFunctors} l1 l2 (Φ : _ → _ → iProp Σ) Ψ :
  NoDup l1 →
  □ (∀ k a w, ⌜l1 !! k = Some a⌝ -∗ ⌜l2 !! k = Some w⌝ -∗ Φ a w -∗ Ψ a w) -∗
  ([∗ list] a;w ∈ l1;l2, Φ a w) -∗
  ([∗ map] a↦pv ∈ lists_to_static_region l1 l2, Ψ a pv).
Proof.
  revert l2. induction l1; intros l2 ND.
  { cbn in *. iIntros "_ _". by iApply big_sepM_empty. }
  { iIntros "#Ha H". iDestruct (big_sepL2_cons_inv_l with "H") as (w l2' ->) "[HΦ H]".
    rewrite lists_to_static_region_cons. iApply big_sepM_insert.
      by apply lists_to_static_region_lookup_None, NoDup_cons_11.
    iSplitL "HΦ". { iApply ("Ha" $! 0); try (iPureIntro; apply cons_lookup); eauto. }
    iApply IHl1; auto.
    by eauto using NoDup_cons_12.
    iModIntro. iIntros. iApply ("Ha" $! (S k)); auto. }
Qed.

Lemma static_region_to_big_sepL2 {Σ: gFunctors} l1 l2 (Φ : _ → _ -> iProp Σ) Ψ :
  NoDup l1 → length l1 = length l2 ->
  □ (∀ k a w, ⌜l1 !! k = Some a⌝ -∗ ⌜l2 !! k = Some w⌝ -∗ Ψ a w -∗ Φ a w) -∗
  ([∗ map] a↦pv ∈ lists_to_static_region l1 l2, Ψ a pv) -∗
  ([∗ list] a;w ∈ l1;l2, Φ a w).
Proof.
  revert l2. induction l1; intros l2 ND Hlen.
  { cbn in *. iIntros "_ _". destruct l2;[|inversion Hlen]. done. }
  { iIntros "#Ha H". destruct l2;[inversion Hlen|]. iDestruct (big_sepM_delete with "H") as "[Hψ H]".
    rewrite lists_to_static_region_cons. apply lookup_insert.
    iSplitL "Hψ". { iApply ("Ha" $! 0); try (iPureIntro; constructor). auto. }
    iApply IHl1; auto.
    by eauto using NoDup_cons_12.
    iModIntro. iIntros. iApply ("Ha" $! (S k)); auto; iPureIntro.
    rewrite lists_to_static_region_cons.
    rewrite delete_insert. auto. by apply lists_to_static_region_lookup_None, NoDup_cons_11. }
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
    
Lemma length_zip_l {A B} (l1: list A) (l2: list B) :
  length l1 ≤ length l2 → length (zip l1 l2) = length l1.
Proof.
  revert l2. induction l1; intros l2 Hl2; auto.
  destruct l2; cbn in Hl2. exfalso; lia.
  cbn. rewrite IHl1; auto. lia.
Qed.

Section awkward_example.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  (* choose a special register for the environment and adv pointer *)
  (* note that we are here simplifying the environment to simply point to one location *)      
   Definition r_env : RegName := r_t30.
   Definition r_adv : RegName := r_t28.

   (* Lemma which splits a list of temp resources into its persistent and non persistent parts *)
   Lemma temp_resources_split l W : 
     ([∗ list] a ∈ l, (∃ (p : Perm) (φ : WORLD * Word → iPropI Σ),
                          ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ temp_resources W φ a p ∗ rel a p φ)
                        ∗ ⌜std (revoke W) !! a = Some Revoked⌝) -∗
     ∃ (ws : list Word), □ ([∗ list] a;w ∈ l;ws, ∃ p φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                                             ∗ ⌜p ≠ O⌝
                                                             ∗ φ (W,w)
                                                             ∗ rel a p φ
                                                             ∗ (if pwl p then future_pub_mono φ w
                                                                else future_priv_mono φ w))
                          ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l⌝
                          ∗ ([∗ list] a;w ∈ l;ws, ∃ p φ, a ↦ₐ[p] w ∗ rel a p φ).
   Proof.
     rewrite /temp_resources. 
     iIntros "Hl".
     iAssert ([∗ list] a ∈ l, ∃ (v : Word), (∃ (p : Perm) (φ : WORLD * Word → iPropI Σ), 
                            ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                            ∗ ⌜p ≠ O⌝
                            ∗ a ↦ₐ[p] v ∗ (if pwl p then future_pub_mono φ v else future_priv_mono φ v) ∗ φ (W, v)
                            ∗ rel a p φ ∗ ⌜std (revoke W) !! a = Some Revoked⌝))%I
       with "[Hl]" as "Hl".
     { iApply (big_sepL_mono with "Hl").
       iIntros (k y Hy) "Hy".
       iDestruct "Hy" as "[Hy Hy']".
       iDestruct "Hy" as (p φ) "(Hpers & Hv & Hrel)".
       iDestruct "Hv" as (v) "(Hne & Hy & Hmono & Hφ)".
       iExists v,p,φ. iFrame. 
     }
     iDestruct (region_addrs_exists with "Hl") as (wps) "Hl".
     iExists wps. iSplit. 
     - iAssert ([∗ list] a;w ∈ l;wps, ∃ p φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                                             ∗ ⌜p ≠ O⌝
                                                             ∗ φ (W,w)
                                                             ∗ rel a p φ
                                                             ∗ (if pwl p then future_pub_mono φ w
                                                                else future_priv_mono φ w))%I
         with "[Hl]" as "Hl". 
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as (p φ) "(Hpers & Hne & Hy & Hmono & Hφ & Hrel & Hrev)".
         iExists p,φ. iFrame. 
       }
       iDestruct (region_addrs_exists2 with "Hl") as (ps Hlen) "Hl".
       iDestruct (region_addrs_exists2 with "Hl") as (φs Hlen') "Hl".
       iDestruct (big_sepL2_sep with "Hl") as "[Hpers Hl]".
       iDestruct (big_sepL2_length with "Hl") as %Hlength. 
       iDestruct (big_sepL2_to_big_sepL_r with "Hpers") as "Hpers";auto. 
       iDestruct (big_sepL_forall with "Hpers") as %Hpers.
       iAssert ([∗ list] y1;y2 ∈ l;zip (zip wps ps) φs, □ (⌜y2.1.2 ≠ O⌝
                                                 ∗ y2.2 (W, y2.1.1)
                                                   ∗ rel y1 y2.1.2 y2.2
                                                     ∗ (if pwl y2.1.2
                                                        then future_pub_mono y2.2 y2.1.1
                                                        else future_priv_mono y2.2 y2.1.1)))%I
         with "[Hl]" as "Hl".
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         apply Hpers with (Wv:=(W,y2.1.1)) in Hy2.
         destruct (pwl y2.1.2) eqn:Hpwl.
         - iDestruct "Hy" as "#(Hne & Hy & Hrel & Hmono)".
           iAlways. iFrame "#".
         - iDestruct "Hy" as "#(Hne & Hy & Hrel & Hmono)".
           iAlways. iFrame "#".
       }
       iDestruct "Hl" as "#Hl". 
       iAlways. iApply region_addrs_exists2.
       iExists ps. iSplit;auto. iApply region_addrs_exists2.
       iExists φs. iSplit;auto.
       iApply big_sepL2_sep. iSplit.
       + iApply big_sepL2_to_big_sepL_r;auto. iApply big_sepL_forall. auto.
       + iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as "#(Hne & Hy & Hrel & Hmono)".
         iFrame "#".
     - iAssert ([∗ list] a0;c0 ∈ l;wps, (∃ p (φ : WORLD * Word → iPropI Σ),
                                    ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                    ∗ ⌜p ≠ O⌝
                                      ∗ a0 ↦ₐ[p] c0
                                        ∗ (if pwl p then future_pub_mono φ c0 else future_priv_mono φ c0)
                                          ∗ φ (W, c0)
                                            ∗ rel a0 p φ)
                                              ∗ ⌜std (revoke W) !! a0 = Some Revoked⌝)%I
         with "[Hl]" as "Hl".
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as (p φ) "(?&?&?&?&?&?&?)".
         iFrame. iExists _,_. iFrame. 
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
         iDestruct "Hy" as (p φ) "(?&?&?&?&?&?)". iExists _,_. 
         iFrame.
   Qed. 
         

   (* TODO: move to region_invariants_static *)
   Lemma region_has_static_addr_Forall (W:WORLD) (a:Addr) (m: gmap Addr Word):
     std W !! a = Some (Static m) →
     region W ∗ sts_full_world W
            -∗ ⌜Forall (λ a':Addr, std W !! a' = Some (Static m))
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

(*  Lemma push_z_instrs_extract a i j z prog p' :
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
    last iRename "Hprog" into prog.*)
  
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
  Definition awkward_instrs f_a (r1 : RegName) epilogue_off :=
     reqglob_instrs r1 ++
     prepstackU_instrs r_stk 10 (* 11 *) ++ (* Are those hardcoded numbers correct ?? *)
     [store_z r_env 0] ++
     [pushU_r_instr r_stk r_env] ++
     [pushU_r_instr r_stk r_t0] ++
     [pushU_r_instr r_stk r1] ++
     scallU_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     storeU_z_z r_stk 0 0; (* we clear the part of the stack which is different from next stack frame *)
     sub_z_z r_t1 0 7 (* 7 since we have increased the bound by one with the above store *);
     lea_r r_stk r_t1] ++
     popU_instrs r_stk r1 ++
     popU_instrs r_stk r_t0 ++
     popU_instrs r_stk r_env ++
     [store_z r_env 1] ++
     [pushU_r_instr r_stk r_env] ++
     [pushU_r_instr r_stk r_t0] ++ 
     scallU_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 6 (* 7 *);
     lea_r r_stk r_t1] ++
     popU_instrs r_stk r_t0 ++
     popU_instrs r_stk r_env ++
     (* assert that the cap in r_env points to 1 *)
     [load_r r1 r_env] ++ 
     assert_r_z_instrs f_a r1 1 ++
     (* in this version, we clear only the local stack frame before returning *)
     (* first we prepare the stack to only point to the local stack frame *)
     [getb r_t1 r_stk;
     add_r_z r_t2 r_t1 9 (* 10 *);
     subseg_r_r r_stk r_t1 r_t2] ++ 
     mclearU_instrs r_stk ++
     rclear_instrs (list_difference all_registers [PC;r_t0]) ++
     [jmp r_t0].

   (* TODO: possibly add fail subroutine to awkward example? *)
  
   (* Definition awkward_preamble a p r1 offset_to_awkward := *)
   (*   ([∗ list] a_i;w_i ∈ a;(awkward_preamble_instrs r1 offset_to_awkward), a_i ↦ₐ[p] w_i)%I. *)
   
   Definition awkward_example (a : list Addr) (p : Perm) f_a (r1 : RegName) epilogue_off : iProp Σ :=
     ([∗ list] a_i;w_i ∈ a;(awkward_instrs f_a r1 epilogue_off), a_i ↦ₐ[p] w_i)%I.

   
   Definition awk_inv i a :=
     (∃ x:bool, sts_state_loc (A:=Addr) i x
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
     rewrite Heq in H. 
     inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ].
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
     rewrite Heq in H. 
     inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]. subst. 
     destruct b;apply encode_inj in Heq1;auto;subst. 
     left. eapply rtc_rel_pub; eauto. 
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
     split;[apply related_sts_std_priv_refl|simpl].
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

   (* Shorthand definition for an adress being currently temporary/revoked *)
   Definition region_type_revoked W (a : Addr) :=
     (std W) !! a = Some Revoked.
   Definition region_type_temporary W (a : Addr) :=
     (std W) !! a = Some Temporary.
   Definition region_type_uninitialized W (a : Addr) :=
     exists w, (std W) !! a = Some (Static {[a:=w]}).
   
   Lemma region_type_temporary_dec W a: Decision (region_type_temporary W a).
   Proof.
     rewrite /region_type_temporary. solve_decision.
   Qed.
   
   Lemma region_type_uninitialized_dec W a: Decision (region_type_uninitialized W a).
   Proof.
     rewrite /region_type_uninitialized. destruct (std W !! a); [|right; red; intros (w & A); discriminate].
     destruct r; try (right; red; intros (w & A); discriminate).
     destruct (g !! a) eqn:Hsome;[|right];[|intros [? ?];simplify_map_eq].
     destruct (decide (g = {[a:=w]}));[left|right];subst;eauto. intros [? ?]. simplify_map_eq. 
   Qed.
   
   (* Instead we must use static regions all the way through *)
   Notation "m1 >> W" := (override_uninitializedW m1 W) (at level 40, left associativity).   
   
   Lemma related_pub_local_3 W W3 W6 b e l l' l1 l2 l_uninit1 l_temps1 l_temps2 m1 m2
         (m_uninit1 m_uninit2 : gmap Addr Word) i c c' :
     l_uninit1 = list_filter (region_type_uninitialized W) (region_type_uninitialized_dec W) (region_addrs b c)
     -> l_temps1 = list_filter (region_type_temporary W) (region_type_temporary_dec W) (region_addrs b e)
     -> l_temps2 = list_filter (region_type_temporary W3) (region_type_temporary_dec W3) (region_addrs c e)
     -> (b <= c < e)%a ∧ (b <= c' < e)%a
     (* l is the list of all revoked resources in W *)
     -> (forall a : Addr, W.1 !! a = Some Temporary <-> a ∈ l)
     (* the stack is either temporary or uninitialized *)
     -> Forall (λ a, region_type_temporary W a ∨ region_type_uninitialized W a) (region_addrs b e)
     (* l' is the list of all addition revoked resources in W3 (other than [c,e)) *)
     -> (forall a : Addr, W3.1 !! a = Some Temporary <-> a ∈ l')
     (* m1 and m2 are the maps containing the local frame and the rest of the temporary resources *)
     -> (l ≡ₚl1 ++ l_temps1 ∧ l' ≡ₚl2 ++ l_temps2 ∧
        elements (dom (gset Addr) m1) ≡ₚl1 ++ (region_addrs b c)
        ∧ elements (dom (gset Addr) m2) ≡ₚl1 ++ l2 ++ (region_addrs b (min c c')))
     (* facts about m_uninit *)
     → elements (dom (gset Addr) m_uninit1) ≡ₚ
       list_filter (region_type_temporary W) (region_type_temporary_dec W) (region_addrs c e)
     → elements (dom (gset Addr) m_uninit2) ≡ₚ (region_addrs c' c) ++ l_temps2
     (* i is the awkward invariant *)
     → W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)
     -> (∃ (b : bool), W.2.1 !! i = Some (encode b))
     (* relations between intermediary worlds *)
     -> related_sts_pub_world
                (m_uninit1 >>
                 revoke 
                  (std_update_multiple
                   (std (std_update_multiple W l_uninit1 Revoked), (<[i:=encode false]> W.2.1, W.2.2))
                   (elements (dom (gset Addr) m1)) (Static m1))) W3
     -> related_sts_pub_world
                (m_uninit2 >>
                 revoke
                   (std_update_multiple
                      (std_update_multiple (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2))
                         (elements (dom (gset Addr) m1)) Revoked) (elements (dom (gset Addr) m2))
                      (Static m2))) W6
     
     → related_sts_pub_world W (std_update_temp_multiple W6 (elements (dom (gset Addr) m2) ++
                                                             elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1)))).
   Proof.
     intros Hluninit1 Hltemp1 Hltemp2 [Hbounds1 Hbounds2] Hiff1 Hstack Hiff2 Happ Hm_uninit1_dom Hm_uninit2_dom
            Hawk [x Hawki] Hrelated1 Hrelated2.
     assert ((std_update_temp_multiple W6 (elements (dom (gset Addr) m2) ++
                                           elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1)))) =
            (std_update_temp_multiple W6 (elements (dom (gset Addr) m2) ++
                                          elements (dom (gset Addr) m_uninit1) ++
                                          elements (dom (gset Addr) m_uninit2)))) as ->.
     { rewrite /std_update_temp_multiple std_update_multiple_app std_update_elements_app_union
               std_update_multiple_app_commute -std_update_multiple_app. auto.  }
     (* get some useful facts about m_uninits *)
     assert (∀ a : Addr, W.1 !! a = Some Temporary ∧ a ∈ region_addrs c e <-> a ∈ dom (gset Addr) m_uninit1) as Hm_uninit1.
     { intros a. split.
       - intros [Htemp Hce].
         apply elem_of_elements. 
         rewrite Hm_uninit1_dom. apply elem_of_list_filter. split;auto.
       - intros Hin%elem_of_elements. revert Hin; rewrite Hm_uninit1_dom =>Hin.
         apply elem_of_list_filter in Hin. auto. 
     }
     assert (∀ a : Addr, (W3.1 !! a = Some Temporary ∧ a ∈ region_addrs c e) ∨ a ∈ region_addrs c' c <->
                         a ∈ dom (gset Addr) m_uninit2) as Hm_uninit2.
     { intros a. split.
       - intros [ [Htemp Hce] | Hc'c].
         + apply elem_of_elements. 
           rewrite Hm_uninit2_dom Hltemp2. apply elem_of_app. right.
           apply elem_of_list_filter. split;auto.
         + apply elem_of_elements. 
           rewrite Hm_uninit2_dom Hltemp2. apply elem_of_app. left. 
           auto. 
       - intros Hin%elem_of_elements. revert Hin; rewrite Hm_uninit2_dom =>Hin.
         apply elem_of_app in Hin as [Hin | Hin]. 
         + right. auto.
         + rewrite Hltemp2 in Hin. apply elem_of_list_filter in Hin. auto. 
     }
       
     simpl in *.
     split; simpl. 
     - (* standard resources *)
       destruct Hrelated1 as [Hstd_related1 _]. 
       destruct Hrelated2 as [Hstd_related2 _]. (* simpl in *.  *)
       destruct Hstd_related2 as [Hstd_sta_dom2 Hstd_related2].
       destruct Hstd_related1 as [Hstd_sta_dom1 Hstd_related1].
       assert (dom (gset Addr) (std W) ⊆ dom (gset Addr) (std W6)) as Hsub.
       { trans (dom (gset Addr) (std W3)).
         - etrans;[|apply Hstd_sta_dom1]. 
           etrans;[|apply (override_uninitializedW_dom _ m_uninit1)].
           rewrite -revoke_dom_eq.           
           etrans;[|apply std_update_multiple_sta_dom_subseteq].
           etrans;[|apply std_update_multiple_sta_dom_subseteq].
            done.
         - etrans;[|apply Hstd_sta_dom2].
           etrans;[|apply override_uninitializedW_dom].
           rewrite -revoke_dom_eq. 
           repeat (etrans;[|apply std_update_multiple_sta_dom_subseteq]).
           done. 
       }
       (* simpl in *.  *)
       split.
       + etrans;[|apply std_update_multiple_sta_dom_subseteq]. auto. 
       + intros k x0 y Hx0 Hy.
         destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ].
         destruct W3 as [ Wstd_sta3 [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ Wstd_sta6 [Wloc_sta6 Wloc_rel6] ].
         (* simpl in *. *)
         destruct (decide (k ∈ l1 ++ l2 ++ (region_addrs b (min c c')))).
         * (* k is a revoked element, which is updated to static at the end *)
           destruct Happ as (Heq1' & Heq2' & Heq3' & Heq4'). 
           rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
           2: { apply elem_of_app. left. rewrite elem_of_elements. rewrite -elem_of_elements. rewrite Heq4'. auto. }
           inversion Hy; subst.
           (* apply elem_of_list_fmap in e0 as [a [Heqa e0] ]. subst. *)
           apply elem_of_app in e0 as [Hl1 | Hl']. 
           ** (* k is a revoked element in l1 *)
             assert (Wstd_sta !! k = Some Temporary) as Htemp. 
             { apply Hiff1. rewrite Heq1'. apply elem_of_app. by left. }
             rewrite Htemp in Hx0; inversion Hx0; subst. left.
           ** (* k is a either revoked element in l2 or [b,c'] *)
             apply elem_of_app in Hl' as [Hl2 | Hbc']. 
             *** (* k is a revoked element in l2 *)
               assert (Wstd_sta3 !! k = Some Temporary) as Htemp.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. by left. }
               (* if x0 is temp we are done *)
               destruct (decide (x0 = Temporary));[subst;left|].
               (* o/w it cannot be an element of either l1 or m_uninit1, which means it will not get set to static *)
               assert (k ∉ l1 ++ list_filter (region_type_temporary (Wstd_sta, (Wloc_sta, Wloc_rel)))
               (region_type_temporary_dec (Wstd_sta, (Wloc_sta, Wloc_rel))) (region_addrs b e)) as Hnin.
               { rewrite -Heq1'. intros Hin. apply Hiff1 in Hin. rewrite Hx0 in Hin. inversion Hin. contradiction. }
               (* k can be an elements of the uninitialized part of the stack *)
               destruct (decide (k ∈ region_addrs b e)).
               **** (* in this case x0 must be uninitialized: done *)
                 apply Forall_forall with (x1:=k) in Hstack;auto.
                 destruct Hstack as [Hcontr | [w Huninit] ];[rewrite Hcontr in Hx0;congruence|].
                 rewrite Huninit in Hx0. inversion Hx0.
                 eright;[|left]. constructor. 
               **** (* in this case x0 does not change *)
                 apply Hstd_related1 with k; auto. 
                 apply not_elem_of_app in Hnin as [Hl1 Hfilter1].
                 assert (k ∉ dom (gset Addr) m_uninit1) as Huninit1.
                 { intros Hcontr%Hm_uninit1. destruct Hcontr as [_ Hcontr].
                   rewrite (region_addrs_split _ c) in n0;[|revert Hbounds1;clear;solve_addr].
                   apply not_elem_of_app in n0 as [_ n0]. done. 
                 }
                 rewrite override_uninitializedW_lookup_nin;[|auto].
                 simpl in *. 
                 rewrite (region_addrs_split _ c) in n0;[|revert Hbounds1;clear;solve_addr].
                 apply not_elem_of_app in n0 as [Hbc Hce]. rewrite /std /=. 
                 rewrite revoke_monotone_lookup_same;auto;
                 [repeat rewrite std_sta_update_multiple_lookup_same_i|].
                 rewrite Hx0;auto. intros Hcontr%elem_of_list_filter. destruct Hcontr as [_ Hcontr]. done.
                 rewrite Heq3'. apply not_elem_of_app. split;auto.
                 repeat rewrite std_sta_update_multiple_lookup_same_i;auto.
                 rewrite Hx0. congruence.
                 intros Hcontr%elem_of_list_filter. destruct Hcontr as [_ Hcontr]. done.
                 rewrite Heq3'. apply not_elem_of_app. split;auto.
             *** (* k is in [b,c']. it will either be temporary or uninitialized *)
               assert (k ∈ region_addrs b e) as Hbe.
               { rewrite (region_addrs_split _ (min c c'));[|revert Hbounds1 Hbounds2;clear;solve_addr].
                 apply elem_of_app. by left. }
               apply Forall_forall with (x1:=k) in Hstack as [Htemp | [w Huninit] ];auto.
               { (* x0 is temp *) rewrite Htemp in Hx0. inversion Hx0. left. }
               { (* x0 is uninit *) rewrite Huninit in Hx0; inversion Hx0. eright;[|left]. constructor. }
         * destruct Happ as [Heq1' [Heq2' [Heq3' Heq4'] ] ]. repeat rewrite fmap_app in n.
           apply not_elem_of_app in n as [Hl1 Hn1].
           apply not_elem_of_app in Hn1 as [Hl2 Hbc'].
           subst. 
           (* we have two more cases, either k is an element of the stack passed on to adv call 2, 
              or k was never a revoked element *)
           destruct (decide (k ∈ region_addrs (min c c') e)). 
           ** (* k is an element of the stack and was either revoked in W or uninitialized *)
             assert (k ∈ region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ (min c c'));[|revert Hbounds1 Hbounds2;clear;solve_addr].
               apply elem_of_app. by right. }
             apply Forall_forall with (x1:=k) in Hstack;auto.
             destruct (decide (k ∈ dom (gset Addr) m_uninit2)) as [Hin | Hin]. 
             *** (* if k is in m_uninit2, we know its now temporary *)
               rewrite std_sta_update_multiple_lookup_in_i in Hy.
               2: { repeat rewrite elem_of_app. right. right. apply elem_of_elements. auto. }
               inversion Hy. destruct Hstack as [Htemp | [w Huninit] ].
               { (* x0 is temp *) rewrite Htemp in Hx0. inversion Hx0. left. }
               { (* x0 is uninit *) rewrite Huninit in Hx0; inversion Hx0. eright;[|left]. constructor. }
             *** (* otherwise we must assert that k is either temporary in W1, in which case it is reinstated
                    or uninitialized at the same value all the way through *)
               destruct Hstack as [Htemp | [w Huninit] ].
               { (* if x0 is temp it must be in m_uninit1 or [c' c] *)
                 rewrite Htemp in Hx0. inversion Hx0;subst.
                 assert (k ∈ dom (gset Addr) m_uninit1) as Hin1.
                 { destruct (decide (c <= c')%Z).
                   - assert (min c c' = c) as Heq;[revert l0;clear;solve_addr|].
                     rewrite Heq in e0,Hbc'. apply Hm_uninit1.
                     split;auto. 
                   - assert (min c c' = c') as Heq;[revert n;clear;solve_addr|].
                     rewrite Heq in Hbc',e0. rewrite (region_addrs_split _ c) in e0;[|revert n Hbounds1;clear;solve_addr].
                     apply elem_of_app in e0 as [e0 | e0];[|apply Hm_uninit1;split;auto]. 
                     exfalso. apply Hin. apply elem_of_elements. rewrite Hm_uninit2_dom.
                     apply elem_of_app. by left. 
                 }
                 rewrite std_sta_update_multiple_lookup_in_i in Hy;[inversion Hy;left|]. 
                 repeat rewrite elem_of_app. rewrite Heq4'. right. left. apply elem_of_elements. auto.
               }
               { (* otherwise we must infer that the uninitialized value is the same all the way through *)
                 rewrite Huninit in Hx0. inversion Hx0;subst.
                 assert (k ∉ dom (gset Addr) m_uninit1) as Hin1.
                 { destruct (decide (c <= c')%Z).
                   - assert (min c c' = c) as Heq;[revert l0;clear;solve_addr|].
                     rewrite Heq in e0,Hbc'. intros Hcontr%Hm_uninit1. destruct Hcontr as [Hcontr _].
                     rewrite Huninit in Hcontr. done.
                   - assert (min c c' = c') as Heq;[revert n;clear;solve_addr|].
                     rewrite Heq in Hbc'. intros Hcontr%Hm_uninit1. destruct Hcontr as [Hcontr _].
                     rewrite Huninit in Hcontr. done.
                 }
                 assert (k ∈ dom (gset Addr) Wstd_sta3) as Hin3.
                 { apply Hstd_sta_dom1.
                   apply override_uninitializedW_elem_of.
                   apply elem_of_gmap_dom.
                   rewrite -revoke_std_sta_lookup_Some. 
                   repeat apply std_sta_update_multiple_is_Some. eauto. }
                 apply elem_of_gmap_dom in Hin3 as [y3 Hy3].
                 (* now we must still distinguish whether the value gets to be static *)
                 destruct (decide (k ∈ region_addrs c e)). 
                 - (* if a is in [c,e] and [c',e],it cannot also be in [b,c] *)
                   assert (k ∉ region_addrs b c) as Hbc.
                   { destruct (decide (c < c')%a). 
                     - rewrite (region_addrs_split _ c) in Hbc';[|revert Hbounds1 l0;clear;solve_addr].
                       revert Hbc'; clear; set_solver.
                     - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                       assert (min c c' = c') as Heq;[solve_addr|]. rewrite Heq in Hbc',e0.
                       apply region_addrs_xor_elem_of with (c:=c) in Hbe;auto.
                       destruct Hbe as [ [Hbc Hce] | [Hbc Hce] ];auto. 
                   }
                   specialize (Hstd_related1 k).
                   rewrite override_uninitializedW_lookup_nin in Hstd_related1;auto.
                   rewrite revoke_monotone_lookup_same in Hstd_related1;eauto.
                   2: { repeat rewrite std_sta_update_multiple_lookup_same_i.
                        rewrite Huninit. auto.
                        intros Hcontr%elem_of_list_filter. destruct Hcontr as [_ Hcontr]. done.
                        rewrite Heq3'. revert Hl1 Hbc. clear. set_solver. }
                   rewrite std_sta_update_multiple_lookup_same_i in Hstd_related1;auto.
                   2: { rewrite Heq3'. revert Hl1 Hbc. clear. set_solver. }
                   rewrite std_sta_update_multiple_lookup_same_i in Hstd_related1;auto.
                   2: { intros Hcontr%elem_of_list_filter. destruct Hcontr as [_ Hcontr]. done. }
                   eapply Hstd_related1 in Hy3 as Hrel1.
                   2: { rewrite Huninit. auto. }
                   apply std_rel_pub_rtc_Static with (g:={[k:=w]}) in Hrel1 as [Htemp | Huninit3];subst;auto.
                   + (* k cannot be temporary in W3 *)
                     apply Hiff2 in Hy3. exfalso.
                     revert Hy3. rewrite Heq2' elem_of_app. intros [Hl2' | Hin']; try done.
                     apply elem_of_list_filter in Hin' as [Htemp _]. apply Hin. apply Hm_uninit2. left. split;auto.
                   + apply Hstd_related2 with k;auto.
                     2: { rewrite std_sta_update_multiple_lookup_same_i in Hy;auto.
                          rewrite Heq4'. repeat (rewrite not_elem_of_app;split;auto);intros Hcontr%elem_of_elements;done. }
                     rewrite override_uninitializedW_lookup_nin;auto;
                     rewrite revoke_monotone_lookup_same;auto;
                     (rewrite std_sta_update_multiple_lookup_same_i;auto;
                       [|rewrite Heq4';revert Hl1 Hbc' Hl2;clear;set_solver]);
                     (rewrite std_sta_update_multiple_lookup_same_i;auto);
                       try (rewrite Heq3';revert Hl1 Hbc;clear;set_solver).
                     rewrite Hy3. auto.
                 - (* c' must be smaller than c *)
                   assert (c' <= c)%Z as Hle.
                   { destruct (decide (c' ≤ c)%Z);auto.
                     assert (min c c' = c) as Heq;[revert n0;clear;solve_addr|].
                     rewrite Heq in Hbc',e0. 
                     rewrite (region_addrs_split _ c) in Hbe;[|revert Hbounds1;clear;solve_addr].
                     apply elem_of_app in Hbe as [Hcontr | Hcontr]; done. 
                   }
                   assert (min c c' = c') as Heq;[revert Hle;clear;solve_addr|].
                   rewrite Heq in Hbc',e0.
                   rewrite std_sta_update_multiple_lookup_same_i in Hy;auto.
                   2: { rewrite Heq4' Heq. repeat (rewrite not_elem_of_app).
                        repeat split;auto;intros Hcontr%elem_of_elements;done. }
                   inversion Hy.
                   eapply Hstd_related1 in Hy3 as Hrel1. 
                   2: { rewrite override_uninitializedW_lookup_nin;auto.
                        assert (k ∉ region_addrs b c) as Hbc.
                        { rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                          apply not_elem_of_app. split;auto. intros Hcontr. apply Hin.
                          apply Hm_uninit2. right. auto. 
                        }
                        rewrite revoke_monotone_lookup_same;eauto;
                        (rewrite std_sta_update_multiple_lookup_same_i;auto;
                          [|rewrite Heq3';revert Hl1 Hbc Hl2;clear;set_solver]);
                        rewrite std_sta_update_multiple_lookup_same_i;auto;
                        try (intros Hcontr%elem_of_list_filter;destruct Hcontr as [_ Hcontr];
                             revert Hbc Hcontr;clear;set_solver); rewrite Huninit;auto. 
                   }
                   apply std_rel_pub_rtc_Static with (g:={[k:=w]}) in Hrel1 as [Htemp | Huninit3];subst;auto.
                   + (* k cannot be temporary in W3 *)
                     apply Hiff2 in Hy3.
                     rewrite (region_addrs_split _ c) in e0;[|revert Hbounds1 Hle;clear;solve_addr].
                     apply elem_of_app in e0 as [e0 | e0];[|done].
                     exfalso. apply Hin. apply Hm_uninit2. right;auto. 
                   + apply Hstd_related2 with k;auto.
                     rewrite override_uninitializedW_lookup_nin;auto.
                     assert (k ∉ region_addrs b c) as Hbc. 
                     { rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                       apply not_elem_of_app. split;auto. intros Hcontr. apply Hin.
                       apply Hm_uninit2. right;auto. 
                     }
                     rewrite revoke_monotone_lookup_same;
                     (rewrite std_sta_update_multiple_lookup_same_i;auto;
                       [|rewrite Heq4' Heq;revert Hl1 Hbc' Hl2;clear;set_solver]);
                     rewrite std_sta_update_multiple_lookup_same_i;auto;
                     (* try (rewrite (region_addrs_split _ c') in Hbc; *)
                     (*      [|revert Hbounds2 Hle;clear;try solve_addr]); *)
                     try (rewrite Heq3';revert Hl1 Hbc;clear;set_solver).
                     rewrite Hy3. auto.
               }
           ** (* if k is never a revoked element, we can apply its transitions during the two future world relations *)
             assert (k ∈ dom (gset Addr) Wstd_sta3) as Hin3.
             { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1.
               apply override_uninitializedW_elem_of.
               apply elem_of_gmap_dom.
               rewrite -revoke_std_sta_lookup_Some.
               repeat apply std_sta_update_multiple_is_Some. eauto. }
             apply elem_of_gmap_dom in Hin3 as [y3 Hy3].
             assert (k ∉ region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ (min c c')). revert Hbc' n. clear. set_solver.
               revert Hbounds1 Hbounds2. clear. solve_addr. }
             assert (k ∉ region_addrs b c) as Hbc.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             assert (k ∉ region_addrs c e) as Hce.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             assert (k ∉ elements (dom (gset Addr) m_uninit1)) as Huninit1.
             { intros Hcontr%elem_of_elements. apply Hm_uninit1 in Hcontr as [_ Hcontr]. done. }
             assert (k ∉ elements (dom (gset Addr) m_uninit2)) as Huninit2.
             { intros Hcontr%elem_of_elements. apply Hm_uninit2 in Hcontr as [ [_ Hcontr] | Hcontr]; try done.
               destruct (decide (c <= c'))%Z.
               - assert (max c c' = c') as Heq;[revert l0;clear;solve_addr|].
                 rewrite interp_weakening.region_addrs_empty in Hcontr;auto. inversion Hcontr. 
               - rewrite (region_addrs_split _ c') in Hbc;[|revert Hbounds2 Hbounds1 n0;clear;solve_addr].
                 apply not_elem_of_app in Hbc as [_ Hc'c]. done.  
             }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. revert Hl1 Hl2 Hbc' Huninit1 Huninit2. clear. set_solver. }
             trans y3. 
             *** apply Hstd_related1 with k; auto.
                 rewrite override_uninitializedW_lookup_nin; [|intros Hcontr%elem_of_elements;done].
                 rewrite -std_update_multiple_revoke_commute;auto.
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver].
                 rewrite revoke_monotone_lookup_same;auto;
                 (rewrite std_sta_update_multiple_lookup_same_i;[|intros Hcontr%elem_of_list_filter;destruct Hcontr;done]).
                 auto. 
                 intros Hcontr. subst. apply Hiff1 in Hcontr. revert Hcontr. rewrite Heq1' =>Hcontr.
                 apply elem_of_app in Hcontr. revert Hcontr; rewrite elem_of_list_filter =>Hcontr.
                 revert Hcontr Hl1 Hbe;clear; set_solver.
             *** apply Hstd_related2 with k;auto. 
                 rewrite override_uninitializedW_lookup_nin; [|intros Hcontr%elem_of_elements;done].
                 rewrite -std_update_multiple_revoke_commute;auto.
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
                 rewrite revoke_monotone_lookup_same;auto;
                 (rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver]).
                 auto. 
                 intros Hcontr. apply Hiff2 in Hcontr. revert Hcontr. rewrite Heq2' =>Hcontr.
                 apply elem_of_app in Hcontr. revert Hcontr; rewrite elem_of_list_filter =>Hcontr.
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
         (* rewrite std_update_multiple_loc_sta /=. *)
         rewrite dom_insert_L;clear;set_solver. 
       + rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom2]. 
         repeat rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom1].
         by rewrite std_update_multiple_loc_rel /=.
         (* by rewrite std_update_multiple_loc_rel /=. *)
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
           repeat rewrite std_update_multiple_loc_rel. auto. }
         edestruct Hloc_related1 with (i0:=k) as [Heq1 [Heq2 Hrelated] ];[eauto|eauto|subst]. 
         edestruct Hloc_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated'] ];[eauto|eauto|subst]. 
         repeat split;auto. intros x0 y Hx0 Hy. 
         assert (is_Some (Wloc_sta3 !! k)) as [y3 Hy3].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hloc_sta_dom1; apply Hloc_sta_dom1.
           assert (k ∈ dom (gset positive) Wloc_sta) as Hin;[apply elem_of_gmap_dom;eauto|].
           repeat rewrite std_update_multiple_loc_sta. 
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

    Lemma related_pub_local_4 W W3 W6 b e l l' l1 l2 l_uninit1 l_temps1 l_temps2 m1 m2
         (m_uninit1 m_uninit2 : gmap Addr Word) i c c' :
     l_uninit1 = list_filter (region_type_uninitialized W) (region_type_uninitialized_dec W) (region_addrs b c)
     -> l_temps1 = list_filter (region_type_temporary W) (region_type_temporary_dec W) (region_addrs b e)
     -> l_temps2 = list_filter (region_type_temporary W3) (region_type_temporary_dec W3) (region_addrs c e)
     -> (b <= c < e)%a ∧ (b <= c' < e)%a
     (* l is the list of all revoked resources in W *)
     -> (forall a : Addr, W.1 !! a = Some Temporary <-> a ∈ l) ∧ NoDup l 
     (* the stack is either temporary or uninitialized *)
     -> Forall (λ a, region_type_temporary W a ∨ region_type_uninitialized W a) (region_addrs b e)
     (* l' is the list of all addition revoked resources in W3 (other than [c,e)) *)
     -> (forall a : Addr, W3.1 !! a = Some Temporary <-> a ∈ l')
     (* m1 and m2 are the maps containing the local frame and the rest of the temporary resources *)
     -> (l ≡ₚl1 ++ l_temps1 ∧ l' ≡ₚl2 ++ l_temps2 ∧
        elements (dom (gset Addr) m1) ≡ₚl1 ++ (region_addrs b c)
        ∧ elements (dom (gset Addr) m2) ≡ₚl1 ++ l2 ++ (region_addrs b (min c c')))
     (* facts about m_uninit *)
     → elements (dom (gset Addr) m_uninit1) ≡ₚ
       list_filter (region_type_temporary W) (region_type_temporary_dec W) (region_addrs c e)
     → elements (dom (gset Addr) m_uninit2) ≡ₚ (region_addrs c' c) ++ l_temps2
     (* i is the awkward invariant *)
     → W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)
     -> (∃ (b : bool), W.2.1 !! i = Some (encode b))
     (* relations between intermediary worlds *)
     -> related_sts_pub_world
                (m_uninit1 >>
                 revoke 
                  (std_update_multiple
                   (std (std_update_multiple W l_uninit1 Revoked), (<[i:=encode false]> W.2.1, W.2.2))
                   (elements (dom (gset Addr) m1)) (Static m1))) W3
     -> related_sts_pub_world
                (m_uninit2 >>
                 revoke
                   (std_update_multiple
                      (std_update_multiple (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2))
                         (elements (dom (gset Addr) m1)) Revoked) (elements (dom (gset Addr) m2))
                      (Static m2))) W6
     
     → related_sts_pub_world W3 (std_update_temp_multiple W6 (elements (dom (gset Addr) m2) ++
                                                             elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1)))).
   Proof.
     intros Hluninit1 Hltemp1 Hltemp2 [Hbounds1 Hbounds2] [Hiff1 Hdup] Hstack Hiff2 Happ Hm_uninit1_dom Hm_uninit2_dom
            Hawk [x Hawki] Hrelated1 Hrelated2.
     assert ((std_update_temp_multiple W6 (elements (dom (gset Addr) m2) ++
                                           elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1)))) =
            (std_update_temp_multiple W6 (elements (dom (gset Addr) m2) ++
                                          elements (dom (gset Addr) m_uninit1) ++
                                          elements (dom (gset Addr) m_uninit2)))) as ->.
     { rewrite /std_update_temp_multiple std_update_multiple_app std_update_elements_app_union
               std_update_multiple_app_commute -std_update_multiple_app. auto. }
     (* get some useful facts about m_uninits *)
     assert (∀ a : Addr, W.1 !! a = Some Temporary ∧ a ∈ region_addrs c e <-> a ∈ dom (gset Addr) m_uninit1) as Hm_uninit1.
     { intros a. split.
       - intros [Htemp Hce].
         apply elem_of_elements. 
         rewrite Hm_uninit1_dom. apply elem_of_list_filter. split;auto.
       - intros Hin%elem_of_elements. revert Hin; rewrite Hm_uninit1_dom =>Hin.
         apply elem_of_list_filter in Hin. auto. 
     }
     assert (∀ a : Addr, (W3.1 !! a = Some Temporary ∧ a ∈ region_addrs c e) ∨ a ∈ region_addrs c' c <->
                         a ∈ dom (gset Addr) m_uninit2) as Hm_uninit2.
     { intros a. split.
       - intros [ [Htemp Hce] | Hc'c].
         + apply elem_of_elements. 
           rewrite Hm_uninit2_dom Hltemp2. apply elem_of_app. right.
           apply elem_of_list_filter. split;auto.
         + apply elem_of_elements. 
           rewrite Hm_uninit2_dom Hltemp2. apply elem_of_app. left. 
           auto. 
       - intros Hin%elem_of_elements. revert Hin; rewrite Hm_uninit2_dom =>Hin.
         apply elem_of_app in Hin as [Hin | Hin]. 
         + right. auto.
         + rewrite Hltemp2 in Hin. apply elem_of_list_filter in Hin. auto. 
     }
       
     simpl in *.
     split; simpl. 
     - (* standard resources *)
       destruct Hrelated1 as [Hstd_related1 _]. 
       destruct Hrelated2 as [Hstd_related2 _]. 
       destruct Hstd_related2 as [Hstd_sta_dom2 Hstd_related2].
       destruct Hstd_related1 as [Hstd_sta_dom1 Hstd_related1].
       assert (dom (gset Addr) (std W3) ⊆ dom (gset Addr) (std W6)) as Hsub.
       { etrans;[|apply Hstd_sta_dom2].
         etrans;[|apply override_uninitializedW_dom].
         rewrite -revoke_dom_eq. 
         repeat (etrans;[|apply std_update_multiple_sta_dom_subseteq]).
         done.
       }
       split.
       + etrans;[|apply std_update_multiple_sta_dom_subseteq]. auto. 
       + intros a x0 y Hx0 Hy.
         destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ].
         destruct W3 as [ Wstd_sta3 [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ Wstd_sta6 [Wloc_sta6 Wloc_rel6] ].
         (* simpl in *. *)
         destruct (decide (a ∈ l1 ++ l2 ++ (region_addrs b (min c c')))).
         * (* k is a revoked element, which is updated to static at the end *)
           destruct Happ as (Heq1' & Heq2' & Heq3' & Heq4'). 
           rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
           2: { rewrite Heq4'. apply elem_of_app. left; auto. }
           inversion Hy; subst.
           (* apply elem_of_list_fmap in e0 as [a [Heqa e0] ]. subst. *)
           apply elem_of_app in e0 as [Hl1 | Hl']. 
           ** (* k is a revoked element in l1 *)
             assert (Wstd_sta !! a = Some Temporary) as Htemp.
             { apply Hiff1. rewrite Heq1'. apply elem_of_app. by left. }
             (* in this case x0 is either Temporary or Static *)
             assert (rtc std_rel_pub (Static m1) x0) as Hrtc.
             { apply Hstd_related1 with a;auto.
               assert (a ∉ dom (gset Addr) m_uninit1) as Hin.
               { intros Hcontr%Hm_uninit1. revert Hdup; rewrite Heq1' =>Hdup. apply NoDup_app in Hdup as (_ & Hdup & _).
                 apply Hdup in Hl1. apply Hl1. apply elem_of_list_filter. split;auto.
                 rewrite (region_addrs_split _ c);[|revert Hbounds1;clear;solve_addr].
                 apply elem_of_app. destruct Hcontr as [_ Hcontr]. right; auto. 
               }
               rewrite override_uninitializedW_lookup_nin;auto.
               rewrite revoke_monotone_lookup_same. 
               - apply std_sta_update_multiple_lookup_in_i. rewrite Heq3'. revert Hl1;clear;set_solver.
               - rewrite std_sta_update_multiple_lookup_in_i;[|rewrite Heq3';revert Hl1;clear;set_solver].
                 intros Hcontr. inversion Hcontr as [Heq]. 
             }
             apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->]. 
             left. right with Temporary;[|left]. constructor. auto. 
           ** (* k is a either revoked element in l2 or [b,c'] *)
             apply elem_of_app in Hl' as [Hl2 | Hbc']. 
             *** (* k is a revoked element in l2 *)
               assert (Wstd_sta3 !! a = Some Temporary) as Htemp.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. by left. }
               (* if x0 is temp we are done *)
               rewrite Htemp in Hx0. inversion Hx0. left. 
             *** (* k is a revoked element in [b,c'] *)
               assert (a ∈ region_addrs b e) as Hbe.
               { rewrite (region_addrs_split _ (min c c'));[|revert Hbounds2 Hbounds1;clear;solve_addr].
                 apply elem_of_app. by left. }
               (* assert (Wstd_sta !! a = Some Temporary) as Htemp. *)
               (* { apply Hiff1. rewrite Heq1'. apply elem_of_app. right. apply elem_of_list_filter. *)
               (*   split;auto.  *)
               (* } *)
               destruct (decide (a ∈ dom (gset Addr) m_uninit2)). 
               **** (* a was temporary, and set to uninitialised/static *)
                 apply Hm_uninit2 in e0 as [ [Htemp _] | Hcc'].
                 { rewrite Htemp in Hx0; inversion Hx0. left. }
                 assert (min c c' = c') as Heq.
                 { destruct (decide (c <= c'))%Z.
                   - rewrite interp_weakening.region_addrs_empty in Hcc';[inversion Hcc'|auto]. 
                   - revert n;clear;solve_addr. }
                 assert (a ∉ dom (gset Addr) m_uninit1) as Hin.
                 { intros Hcontr%Hm_uninit1. destruct Hcontr as [Htemp Hcontr].
                   rewrite Heq in Hbc'. 
                   apply region_addrs_xor_elem_of with (c:=c') in Hbe;auto.
                   destruct Hbe as [ [? ?] | [? ?] ]; try done.
                   rewrite (region_addrs_split _ c) in H0 ;[|revert Hbounds1 Heq;clear;solve_addr].
                   apply not_elem_of_app in H0 as [? ?]. done. 
                 }
                 assert (a ∈ elements (dom (gset Addr) m1)) as Hnin.
                 { rewrite Heq3'. rewrite (region_addrs_split _ c');[|revert Hbounds2 Heq;clear;solve_addr].
                   repeat rewrite elem_of_app. right. right. auto. }
                 (* apply elem_of_gmap_dom in Hin1 as [w Hw].  *)
                 assert (rtc std_rel_pub (Static m1) x0) as Hrtc.
                 { apply Hstd_related1 with a;auto.
                   rewrite override_uninitializedW_lookup_nin;auto.
                   rewrite revoke_monotone_lookup_same.
                   apply std_sta_update_multiple_lookup_in_i. auto.
                   rewrite std_sta_update_multiple_lookup_in_i; auto.
                 }
                 revert Hstack. rewrite Forall_forall =>Hstack. pose proof (Hstack _ Hbe) as [Htemp | Huninit]. 
                 { apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->].
                   left. right with Temporary;[|left]. constructor; auto. auto.
                 }
                 { apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->]. 
                   left. right with Temporary;[|left]. constructor. auto.
                 }
               ****
                 assert (a ∉ region_addrs c' c) as Hc'c.
                 { intros Hcontr. apply n. apply Hm_uninit2. right. auto. }
                 destruct (decide (a ∈ dom (gset Addr) m_uninit1)).
                 { (* a is uninitialized in the first call. *)
                   apply elem_of_gmap_dom in e0 as [w Hw]. 
                   assert (rtc std_rel_pub (Static {[a:=w]}) x0) as Hrtc.
                   { apply Hstd_related1 with a;auto.
                     apply override_uninitializedW_lookup_some;auto.
                   }
                   apply (std_rel_pub_rtc_Static _ _ {[a:=w]}) in Hrtc as [-> | ->];auto;[left|]. 
                   eright;[|left]. constructor. 
                 }
                 { destruct (decide (a ∈ l1 ++ region_addrs b c)). 
                   - (* a is static in the first call *)
                     assert (rtc std_rel_pub (Static m1) x0) as Hrtc.
                     { apply Hstd_related1 with a;auto.
                       rewrite override_uninitializedW_lookup_nin;auto.
                       rewrite -std_update_multiple_revoke_commute.
                       apply std_sta_update_multiple_lookup_in_i.
                      rewrite Heq3'. auto. auto. 
                     }
                     apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->]. 
                     left. right with Temporary;[|left]. constructor. auto.
                   - revert Hstack. rewrite Forall_forall =>Hstack. pose proof (Hstack _ Hbe) as [Htemp | [w Huninit] ]. 
                     + (* contradiction: if a was temp, and not in the local stack frame, 
                          it would have been uninitialised *)
                       exfalso. apply n0. apply Hm_uninit1. split;auto.
                       apply not_elem_of_app in n1 as [Hl1 Hbc]. 
                       apply region_addrs_xor_elem_of with (c:=c) in Hbe;auto.
                       destruct Hbe as [ [? ?] | [? ?] ];done. 
                     + (* a was uninit from the beginning *)
                       assert (a ∉ elements (dom (gset Addr) m1)) as Hm1.
                       { rewrite Heq3'. auto. }
                       assert (rtc std_rel_pub (Static {[a:=w]}) x0) as Hrtc.
                       { apply Hstd_related1 with a;auto.
                         rewrite override_uninitializedW_lookup_nin;auto.
                         rewrite -std_update_multiple_revoke_commute;auto.
                         rewrite std_sta_update_multiple_lookup_same_i;auto.
                         rewrite revoke_monotone_lookup_same;
                           rewrite std_sta_update_multiple_lookup_same_i;auto.
                         - intros Hcontr%elem_of_list_filter.
                           apply not_elem_of_app in n1 as [Hl1 Hbc].
                           destruct Hcontr as [_ Hcontr]. done.
                         - rewrite Huninit. auto.
                         - intros Hcontr%elem_of_list_filter.
                           apply not_elem_of_app in n1 as [Hl1 Hbc].
                           destruct Hcontr as [_ Hcontr]. done.
                       }
                       apply (std_rel_pub_rtc_Static _ _ {[a:=w]}) in Hrtc as [-> | ->];auto;[left|]. 
                       eright;[|left]. constructor.                      
                 }
         * destruct Happ as [Heq1' [Heq2' [Heq3' Heq4'] ] ]. 
           apply not_elem_of_app in n as [Hl1 Hn1].
           apply not_elem_of_app in Hn1 as [Hl2 Hbc'].
           (* we have two more cases, either k is an element of the stack passed on to adv call 2, 
              or k was never a revoked element *)
           destruct (decide (a ∈ region_addrs (min c c') e)). 
           ** (* k is an element of the stack and was revoked in W *)
             assert (a ∈ region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ (min c c'));[|revert Hbounds1 Hbounds2;clear;solve_addr].
               apply elem_of_app. by right. }
             destruct (decide (a ∈ dom (gset Addr) m_uninit1)). 
             { rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
               2: { rewrite Heq4'. repeat (rewrite elem_of_app). right. left. apply elem_of_elements;auto. }
               inversion Hy.
               apply elem_of_gmap_dom in e1 as [w Hw]. 
               assert (rtc std_rel_pub (Static {[a:=w]}) x0) as Hrtc.
               { apply Hstd_related1 with a;auto.
                 apply override_uninitializedW_lookup_some;auto.
               }
               apply (std_rel_pub_rtc_Static _ _ {[a:=w]}) in Hrtc as [-> | ->];auto;[left|]. 
               eright;[|left]. constructor. 
             }
             destruct (decide (a ∈ dom (gset Addr) m_uninit2)). 
             { rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
               2: { rewrite Heq4'. repeat (rewrite elem_of_app). right. right. apply elem_of_elements;auto. }
               inversion Hy.
               assert (a ∉ elements (dom (gset Addr) m2)) as Hin.
               { rewrite Heq4'. repeat (rewrite not_elem_of_app;split;auto). }
               apply Hm_uninit2 in e1 as [ [Htemp _] | Hc'c].
               { rewrite Htemp in Hx0. inversion Hx0. left. }
               assert (c' <= c)%Z as Hle.
               { destruct (decide (c' <= c)%Z);auto. rewrite interp_weakening.region_addrs_empty in Hc'c;auto.
                 inversion Hc'c. revert n0. clear. solve_addr. }
               assert (min c c' = c') as Heq;[revert Hle;clear;solve_addr|]. 
               assert (a ∈ elements (dom (gset Addr) m1)) as Hin1.
               { rewrite Heq3'. rewrite Heq in Hbc'. apply elem_of_app. right.
                 rewrite (region_addrs_split _ c');[|revert Hle Hbounds2;clear;solve_addr].
                 apply elem_of_app. by right. 
               }
               assert (rtc std_rel_pub (Static m1) x0) as Hrtc.
               { apply Hstd_related1 with a;auto.
                 rewrite override_uninitializedW_lookup_nin;auto.
                 rewrite -std_update_multiple_revoke_commute;auto.
                 apply std_sta_update_multiple_lookup_in_i. auto. 
               }
               apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->]. 
               left. right with Temporary;[|left]. constructor. auto.
             }
             { assert (a ∉ region_addrs c' c) as Hc'c.
               { intros Hcontr. apply n0. apply Hm_uninit2. right;auto. } 
               rewrite std_sta_update_multiple_lookup_same_i in Hy;auto.
               2: { repeat (rewrite not_elem_of_app;split;auto).
                    rewrite Heq4'. repeat (rewrite not_elem_of_app;split;auto).
                    rewrite elem_of_elements. auto. rewrite elem_of_elements. auto. }
               revert Hstack. rewrite Forall_forall =>Hstack. pose proof (Hstack _ Hbe) as [Htemp | [w Huninit] ]. 
               - (* this case leads to a contradiction, since we would need to have a in uninit *)
                 exfalso. apply n. apply Hm_uninit1. split;auto.
                 destruct (decide (c <= c'))%Z.
                 + assert (min c c' = c) as Heq;[revert l0;clear;solve_addr|]. rewrite Heq in Hbc'.
                   apply region_addrs_xor_elem_of with (c:=c) in Hbe;[|revert Hbounds1 Hbounds2;clear;solve_addr].
                   destruct Hbe as [ [? ?] | [? ?] ];try done.
                 + assert (min c c' = c') as Heq;[revert n1;clear;solve_addr|].
                   rewrite Heq in Hbc' e0.
                   rewrite (region_addrs_split _ c) in e0;[|revert Heq n1 Hbounds1;clear;solve_addr].
                   apply elem_of_app in e0 as [e0 | e0];auto. done. 
               - (* a was uninit from the beginning *)
                 assert (a ∉ region_addrs b c) as Hbc.
                 { destruct (decide (c <= c'))%Z.
                   - assert (min c c' = c) as Heq;[revert l0;clear;solve_addr|]. rewrite Heq in Hbc'. auto.
                   - assert (min c c' = c') as Heq;[revert n1;clear;solve_addr|].
                     rewrite Heq in Hbc'.
                     rewrite (region_addrs_split _ c');[|revert Heq Hbounds2;clear;solve_addr].
                     apply not_elem_of_app. split;auto.
                 }
                 assert (a ∉ elements (dom (gset Addr) m1)) as Hm1.
                 { rewrite Heq3'. apply not_elem_of_app. split;auto. }
                 assert (rtc std_rel_pub (Static {[a:=w]}) x0) as Hrtc.
                 { apply Hstd_related1 with a;auto.
                   rewrite override_uninitializedW_lookup_nin;auto.
                   rewrite -std_update_multiple_revoke_commute;auto.
                   rewrite std_sta_update_multiple_lookup_same_i;auto.
                   rewrite revoke_monotone_lookup_same;
                           rewrite std_sta_update_multiple_lookup_same_i;auto.
                   - rewrite Hluninit1. intros Hcontr%elem_of_list_filter.
                     destruct Hcontr as [_ Hcontr]. done.
                   - rewrite Huninit. auto.
                   - rewrite Hluninit1. intros Hcontr%elem_of_list_filter.
                     destruct Hcontr as [_ Hcontr]. done.
                 }
                 apply (std_rel_pub_rtc_Static _ _ {[a:=w]}) in Hrtc as [-> | ->];auto.
                 + assert (a ∉ elements (dom (gset Addr) m2)).
                   { rewrite Heq4'. repeat (rewrite not_elem_of_app;split;auto). }
                   (* this case leads to a contradiction, since we would need to have a in uninit *)
                   exfalso. apply n0. apply Hm_uninit2. left. split;auto.
                   destruct (decide (c <= c'))%Z.
                   { assert (min c c' = c) as Heq;[revert l0;clear;solve_addr|]. rewrite Heq in Hbc'.
                     apply region_addrs_xor_elem_of with (c:=c) in Hbe;[|revert Hbounds1 Hbounds2;clear;solve_addr].
                     destruct Hbe as [ [? ?] | [? ?] ];try done. }
                   { assert (min c c' = c') as Heq;[revert n1;clear;solve_addr|].
                     rewrite Heq in Hbc' e0.
                     rewrite (region_addrs_split _ c) in e0;[|revert Heq n1 Hbounds1;clear;solve_addr].
                     apply elem_of_app in e0 as [e0 | e0];auto. done. }
                 + assert (a ∉ elements (dom (gset Addr) m2)).
                   { rewrite Heq4'. repeat (rewrite not_elem_of_app;split;auto). }
                   assert (a ∉ elements (dom (gset Addr) m1)).
                   { rewrite Heq3'. repeat (rewrite not_elem_of_app;split;auto). }
                   apply Hstd_related2 with a;auto.
                   rewrite override_uninitializedW_lookup_nin;auto.
                   rewrite -std_update_multiple_revoke_commute;auto.
                   rewrite std_sta_update_multiple_lookup_same_i;auto.
                   rewrite revoke_monotone_lookup_same;rewrite std_sta_update_multiple_lookup_same_i;auto.
                   rewrite Hx0. auto.
             } 
           ** (* if k is never a revoked element, we can apply its transitions during the second future world relations *)
             assert (a ∉ region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ (min c c')). revert Hbc' n. clear. set_solver.
               revert Hbounds2 Hbounds1. clear. solve_addr. }
             assert (a ∉ region_addrs b c) as Hbc.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             assert (a ∉ region_addrs c e) as Hce.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             assert (a ∉ elements (dom (gset Addr) m_uninit1)) as Huninit1.
             { intros Hcontr%elem_of_elements. apply Hm_uninit1 in Hcontr as [_ Hcontr]. done. }
             assert (a ∉ elements (dom (gset Addr) m_uninit2)) as Huninit2.
             { intros Hcontr%elem_of_elements. apply Hm_uninit2 in Hcontr as [ [_ Hcontr] | Hcontr]; try done.
               destruct (decide (c <= c'))%Z.
               - assert (max c c' = c') as Heq;[revert l0;clear;solve_addr|].
                 rewrite interp_weakening.region_addrs_empty in Hcontr;auto. inversion Hcontr. 
               - rewrite (region_addrs_split _ c') in Hbc;[|revert Hbounds2 Hbounds1 n0;clear;solve_addr].
                 apply not_elem_of_app in Hbc as [_ Hc'c]. done.  
             }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. revert Hl1 Hl2 Hbc' Huninit1 Huninit2. clear. set_solver. }
             apply Hstd_related2 with a;auto. 
             rewrite override_uninitializedW_lookup_nin; [|intros Hcontr%elem_of_elements;done].
             rewrite -std_update_multiple_revoke_commute;auto.
             rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
             rewrite revoke_monotone_lookup_same;auto;
               (rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver]).
             auto. 
             intros Hcontr. apply Hiff2 in Hcontr. revert Hcontr. rewrite Heq2' =>Hcontr.
             apply elem_of_app in Hcontr. revert Hcontr; rewrite Hltemp2 elem_of_list_filter =>Hcontr.
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

   Lemma related_pub_local_lookup W W3 W6 m_uninit1 m_uninit2 m_static1 m_static2 i luninitsplit
         ltemprest ltempadv3 wsrest wsadv3 l1 l2 l l' b c c' e wsrs l_temps1 : 
     (l ≡ₚl1 ++ l_temps1 ∧ l' ≡ₚl2 ++ ltempadv3 ∧
      elements (dom (gset Addr) m_static1) ≡ₚl1 ++ (region_addrs b c)
      ∧ elements (dom (gset Addr) m_static2) ≡ₚl1 ++ l2 ++ (region_addrs b (min c c')))
     -> region_size c' c = length wsrs
     -> length ltempadv3 = length wsadv3
     -> length ltemprest = length wsrest
     -> m_uninit1 = list_to_map (zip ltemprest wsrest)
     -> ltemprest = list_filter (region_type_temporary W) (region_type_temporary_dec W) (region_addrs c e)
     -> m_uninit2 = list_to_map (zip (region_addrs c' c ++ ltempadv3) (wsrs ++ wsadv3))
     -> ltempadv3 = list_filter (region_type_temporary W3) (region_type_temporary_dec W3) (region_addrs c e)
     -> l_temps1 = list_filter (region_type_temporary W) (region_type_temporary_dec W) (region_addrs b e)
     -> (b <= c < e)%a ∧ (b <= c' < e)%a
     (* l is the list of all revoked resources in W *)
     -> (forall a : Addr, W.1 !! a = Some Temporary <-> a ∈ l) ∧ NoDup l
     (* l' is the list of all addition revoked resources in W3 (other than [c,e)) *)
     -> (forall a : Addr, W3.1 !! a = Some Temporary <-> a ∈ l')
     -> NoDup (region_addrs c' c ++ ltempadv3)
     -> Forall (λ a, region_type_temporary W a ∨ region_type_uninitialized W a) (region_addrs b e)
     -> related_sts_pub_world
         (m_uninit1 >>
            revoke
            (std_update_multiple (std (std_update_multiple W luninitsplit Revoked), (<[i:=encode false]> W.2.1, W.2.2))
                                 (elements (dom (gset Addr) m_static1)) (Static m_static1))) W3
     → related_sts_pub_world
         (m_uninit2 >>
            revoke
            (std_update_multiple
               (std_update_multiple (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2)) (elements (dom (gset Addr) m_static1))
                                    Revoked) (elements (dom (gset Addr) m_static2)) (Static m_static2))) W6
     → ∀ (a : Addr) (w : Word),
         (m_uninit2 ∪ m_uninit1) !! a = Some w → std W6 !! a = Some Temporary ∨ std W6 !! a = Some (Static {[a:=w]}).
   Proof.
     intros Heq Hlen Hlen' Hlen'' Hm_uninit1 Hltemprest Hm_uninit2 Hltempadv3 Hl_temps Hbounds Hiff Hiff' Hdup Hstack
            Hrelated1 Hrelated2.
     destruct Hrelated1 as [Hstd_related1 _]. 
     destruct Hrelated2 as [Hstd_related2 _]. (* simpl in *.  *)
     destruct Hstd_related2 as [Hstd_dom2 Hstd_related2].
     destruct Hstd_related1 as [Hstd_dom1 Hstd_related1].
     intros a w Hin%lookup_union_Some_raw. 
     destruct Hin as [Huninit2 | [Hnuninit2 Huninit1] ]. 
     - assert (a ∈ dom (gset Addr) m_uninit2) as Hin;[apply elem_of_gmap_dom;eauto|].
       assert (m_uninit2 !! a = Some w) as Hlookup;auto. 
       rewrite Hm_uninit2 Hltempadv3 in Huninit2.
       apply elem_of_list_to_map_2,elem_of_zip_l in Huninit2.
       apply elem_of_app in Huninit2 as [Hc'c | Hce].
       + assert (is_Some (W.1 !! a)) as [x Ha].
         { revert Hstack; rewrite Forall_forall =>Hstack.
           destruct (decide (c <= c'))%Z;[rewrite interp_weakening.region_addrs_empty in Hc'c;auto;inversion Hc'c|]. 
           assert (a ∈ region_addrs b e) as Hbe.
           { rewrite (region_addrs_split _ c');[|revert Hbounds n;clear;solve_addr].
             rewrite (region_addrs_split c' c);[|revert Hbounds n;clear;solve_addr].
             repeat rewrite elem_of_app. right;left. auto. }
           apply Hstack in Hbe as [Htemp | [w' Huninit] ];eauto. 
         }
         assert (is_Some (W3.1 !! a)) as [w3 Hw3].
         { apply elem_of_gmap_dom. apply Hstd_dom1.
           apply override_uninitializedW_elem_of.
           rewrite -revoke_dom_eq. repeat apply std_update_multiple_sta_dom_subseteq.
           apply elem_of_gmap_dom. eauto. }
         assert (is_Some (W6.1 !! a)) as [w6 Hw6].
         { apply elem_of_gmap_dom. apply Hstd_dom2.
           apply override_uninitializedW_elem_of_overwritten;auto. }
         eapply Hstd_related2 in Hw6 as Hrel;[|apply override_uninitializedW_lookup_some;eauto]. 
         eapply std_rel_pub_rtc_Static in Hrel as [Heq' | Heq'];eauto; 
           rewrite Heq' in Hw6; auto. 
       + apply elem_of_list_filter in Hce as [Htemp Hce].
         assert (is_Some (W6.1 !! a)) as [w6 Hw6].
         { apply elem_of_gmap_dom. apply Hstd_dom2.
           apply override_uninitializedW_elem_of_overwritten;auto. }
         eapply Hstd_related2 in Hw6 as Hrel;[|apply override_uninitializedW_lookup_some;eauto]. 
         eapply std_rel_pub_rtc_Static in Hrel as [Heq' | Heq'];eauto; 
           rewrite Heq' in Hw6; auto.
     - assert (a ∈ dom (gset Addr) m_uninit1) as Hin;[apply elem_of_gmap_dom;eauto|].
       assert (a ∉ dom (gset Addr) m_uninit2) as Hnin;[apply not_elem_of_dom;eauto|].
       assert (m_uninit1 !! a = Some w) as Hlookup;auto. 
       rewrite Hm_uninit1 Hltemprest in Huninit1.
       apply elem_of_list_to_map_2,elem_of_zip_l,elem_of_list_filter in Huninit1 as [Htemp Hce]. 
       assert (is_Some (W3.1 !! a)) as [w3 Hw3].
       { apply elem_of_gmap_dom. apply Hstd_dom1. 
         apply override_uninitializedW_elem_of_overwritten;auto. }
       eapply Hstd_related1 in Hw3 as Hrel;[|apply override_uninitializedW_lookup_some;eauto]. 
       eapply std_rel_pub_rtc_Static in Hrel;eauto. 
       assert (is_Some (W6.1 !! a)) as [w6 Hw6].
       { apply elem_of_gmap_dom. apply Hstd_dom2.
         apply override_uninitializedW_elem_of.
         rewrite -revoke_dom_eq. repeat apply std_update_multiple_sta_dom_subseteq.
         apply elem_of_gmap_dom. eauto.
       }
       destruct Hrel as [-> | ->].
       + (* if a is Temporary in W3, it must be in m_uninit2: contradiction *)
         assert (is_Some (m_uninit2 !! a)) as [w' Hin'].
         { rewrite Hm_uninit2. apply list_to_map_lookup_is_Some. 
           rewrite fst_zip;[auto|repeat rewrite app_length;rewrite region_addrs_length Hlen Hlen';auto].
           apply elem_of_app. right. rewrite Hltempadv3.
           apply elem_of_list_filter. split;auto. 
         }
         rewrite Hin' in Hnuninit2;done. 
       + (* otherwise we want to reason that the value stays the same *)
         destruct Heq as (Heq1 & Heq2 & Heq3 & Heq4). 
         assert (a ∉ elements (dom (gset Addr) m_static1)) as Hstatic1.
         { rewrite Heq3. apply not_elem_of_app.
           destruct Hiff as [Hiff Hdup']. revert Hdup';rewrite Heq1 Hl_temps =>Hdup'.
           assert (a ∈ list_filter (region_type_temporary W) (region_type_temporary_dec W) (region_addrs b e)) as Ha.
           { apply elem_of_list_filter. split;auto.
             rewrite (region_addrs_split _ c);[|revert Hbounds;clear;solve_addr].
             apply elem_of_app. right. auto. }
           assert (a ∉ l1) as Ha'.
           { apply NoDup_app in Hdup' as (_ & Hdup' & _). intros Hcontr%Hdup'. done. }
           assert (a ∈ region_addrs b e) as Hbe. 
           { rewrite (region_addrs_split _ c);[|revert Hbounds;clear;solve_addr].
             apply elem_of_app. right. auto. }
           apply (region_addrs_xor_elem_of _ _ c) in Hbe;[|revert Hbounds;clear;solve_addr].
           destruct Hbe as [ [? ?] | [? ?] ];try done.
         }
         assert (a ∉ elements (dom (gset Addr) m_static2)) as Hstatic2.
         { rewrite Heq4. repeat rewrite not_elem_of_app.
           destruct Hiff as [Hiff Hdup']. revert Hdup';rewrite Heq1 Hl_temps =>Hdup'.
           assert (a ∈ list_filter (region_type_temporary W) (region_type_temporary_dec W) (region_addrs b e)) as Ha.
           { apply elem_of_list_filter. split;auto.
             rewrite (region_addrs_split _ c);[|revert Hbounds;clear;solve_addr].
             apply elem_of_app. right. auto. }
           assert (a ∉ l1) as Ha'.
           { apply NoDup_app in Hdup' as (_ & Hdup' & _). intros Hcontr%Hdup'. done. }
           assert (a ∉ l2) as Ha''.
           { intros Hcontr.
             assert (a ∈ l') as Hl'.
             { rewrite Heq2. apply elem_of_app. by left. }
             apply Hiff' in Hl'. rewrite Hl' in Hw3. inversion Hw3. }           
           assert (a ∈ region_addrs b e) as Hbe. 
           { rewrite (region_addrs_split _ c);[|revert Hbounds;clear;solve_addr].
             apply elem_of_app. right. auto. }
           apply (region_addrs_xor_elem_of _ _ (min c c')) in Hbe as Hbe';[|revert Hbounds;clear;solve_addr].
           destruct Hbe' as [ [? ?] | [? ?] ];try done.
           apply (region_addrs_xor_elem_of _ _ c) in Hbe;[|revert Hbounds;clear;solve_addr].
           destruct Hbe as [ [? ?] | [? ?] ];try done.
           destruct (decide (c <= c'))%Z. 
           * assert (min c c' = c) as Hceq;[revert l0;clear;solve_addr|]. 
             rewrite Hceq in H,H0. done.
           * assert (min c c' = c') as Hceq;[revert n;clear;solve_addr|].
             rewrite Hceq in H,H0.
             rewrite (region_addrs_split _ c) in H0;[|revert Hbounds n;clear;solve_addr].
             apply not_elem_of_app in H0 as [_ ?]. done.
         }
         eapply Hstd_related2 in Hw6 as Hrel.
         2: { rewrite override_uninitializedW_lookup_nin;auto.
              rewrite -std_update_multiple_revoke_commute;auto.
              rewrite std_sta_update_multiple_lookup_same_i;auto. 
              rewrite -std_update_multiple_revoke_commute;auto.
              rewrite std_sta_update_multiple_lookup_same_i;auto.
              rewrite revoke_monotone_lookup_same;eauto. rewrite Hw3. auto.
         }
         eapply std_rel_pub_rtc_Static in Hrel;eauto.
         destruct Hrel as [-> | ->];auto. 
   Qed. 
         

  Lemma create_gmap_default_lookup_is_Some {K V} `{EqDecision K, Countable K} (l: list K) (d: V) x v:
    create_gmap_default l d !! x = Some v → x ∈ l ∧ v = d.
  Proof.
    revert x v d. induction l as [| a l]; cbn.
    - done.
    - intros x v d. destruct (decide (a = x)) as [->|].
      + rewrite lookup_insert. intros; simplify_eq. repeat constructor.
      + rewrite lookup_insert_ne //. intros [? ?]%IHl. subst. repeat constructor; auto.
  Qed.

  Lemma create_gmap_default_dom {K V} `{EqDecision K, Countable K} (l: list K) (d: V):
    dom (gset K) (create_gmap_default l d) = list_to_set l.
  Proof.
    induction l as [| a l].
    - cbn. rewrite dom_empty_L //.
    - cbn [create_gmap_default list_to_set]. rewrite dom_insert_L // IHl //.
  Qed.

  Lemma registers_mapsto_resources pc_w stk_w rt0_w adv_w pc_w' (rmap: gmap RegName Word) :
    dom (gset RegName) rmap = all_registers_s ∖ {[PC; r_stk; r_t0; r_adv]} →
    ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ inl 0%Z)
    -∗ r_stk ↦ᵣ stk_w
    -∗ r_t0 ↦ᵣ rt0_w
    -∗ r_adv ↦ᵣ adv_w
    -∗ PC ↦ᵣ pc_w'
    -∗
    registers_mapsto (<[PC:=pc_w']> (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
      (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z))))))).
  Proof.
    iIntros (Hdom) "Hregs Hr_stk Hr_t0 Hr_adv HPC".
    rewrite /registers_mapsto insert_insert.
    do 4 (rewrite big_sepM_insert; [iFrame|done]).
    iDestruct (big_sepM_dom with "Hregs") as "Hregs".
    iApply (big_sepM_mono (λ k _, k ↦ᵣ inl 0%Z))%I.
    { intros * [? ->]%create_gmap_default_lookup_is_Some. auto. }
    iApply big_sepM_dom. rewrite big_opS_proper'. iFrame. done.
    rewrite Hdom.
    rewrite create_gmap_default_dom list_to_set_difference -/all_registers_s.
    f_equal. clear. set_solver.
  Qed.

  Lemma r_full (pc_w stk_w rt0_w adv_w : Word) :
    full_map (Σ:=Σ) (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
  Proof.
    rewrite /full_map. iPureIntro. intros rr. cbn beta.
    rewrite elem_of_gmap_dom 4!dom_insert_L create_gmap_default_dom list_to_set_difference.
    rewrite -/all_registers_s. generalize (all_registers_s_correct rr). clear. set_solver.
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
    (([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std W !! a = Some Permanent⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std W' !! a = Some Permanent⌝))%I.
  Proof.
    iIntros (Hrelated) "Hr".
    iApply (big_sepL_mono with "Hr").
    iIntros (k y Hsome) "(Hy & Hperm)". 
    iFrame.
    iDestruct "Hperm" as %Hperm.
    iPureIntro. 
    apply (region_state_nwl_monotone_nl _ W') in Hperm; auto.
  Qed.

  Lemma adv_stack_monotone W W' b e :
    related_sts_pub_world W W' ->
    (([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                     ∧ ⌜region_state_pwl W a⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                       ∧ ⌜region_state_pwl W' a⌝))%I.
  Proof.
    iIntros (Hrelated) "Hstack_adv". 
    iApply (big_sepL_mono with "Hstack_adv").
    iIntros (k y Hsome) "(Hr & Htemp)".
    iDestruct "Htemp" as %Htemp. 
    iFrame. iPureIntro. 
    apply (region_state_pwl_monotone _ W') in Htemp; auto.
  Qed. 

  (* Helper lemma about private future worlds *)
  (* TODO: move this in sts? *)
  Lemma related_sts_priv_world_std_sta_is_Some W W' i :
    related_sts_priv_world W W' -> is_Some ((std W) !! i) -> is_Some ((std W') !! i).
  Proof.
    intros [ [Hdom1 _ ] _] Hsome.
    apply elem_of_gmap_dom in Hsome.
    apply elem_of_gmap_dom.
    apply elem_of_subseteq in Hdom1. auto.
  Qed.

  Lemma related_sts_priv_world_std_sta_region_type W W' (i : Addr) (ρ : region_type) :
    related_sts_priv_world W W' ->
    (std W) !! i = Some ρ ->
    ∃ (ρ' : region_type), (std W') !! i = Some ρ'.
  Proof.
    intros Hrelated Hρ.
    assert (is_Some ((std W') !! i)) as [x Hx].
    { apply related_sts_priv_world_std_sta_is_Some with W; eauto. }
    destruct Hrelated as [ [Hdom1 Hrevoked ] _].
    specialize (Hrevoked _ _ _ Hρ Hx). simplify_eq. 
    eauto. 
  Qed.
  
  (* TODO: move to region_invariants ? *)
  Lemma region_type_uninitialized_revoke W (a : Addr):
    region_type_uninitialized W a ->
    region_type_uninitialized (revoke W) a.
  Proof.
    rewrite /region_type_uninitialized /revoke /revoke_std_sta /=.
    intros [w H]. rewrite lookup_fmap H /=. eauto.
  Qed.

  (* TODO: move to region_addrs *)
  Lemma region_addrs_split2 b e a:
    region_addrs b e = region_addrs b (min a e) ++ region_addrs (max b a) e.
  Proof.
    destruct (addr_eq_dec (min a e) (max b a)).
    - rewrite e0 -region_addrs_split; auto.
      split; solve_addr.
    - destruct (Addr_le_dec (min a e) b).
      + rewrite (interp_weakening.region_addrs_empty b (min a e)); auto.
        destruct (Addr_le_dec a b).
        * replace (max b a) with b by solve_addr. auto.
        * replace (max b a) with a in n by solve_addr.
          assert (e <= b)%a by solve_addr.
          rewrite (interp_weakening.region_addrs_empty b e); auto.
          rewrite interp_weakening.region_addrs_empty; auto. solve_addr.
      + replace (max b a) with a by solve_addr.
        destruct (Addr_le_dec e a).
        * rewrite (interp_weakening.region_addrs_empty a e); auto.
          replace (min a e) with e by solve_addr; auto.
          rewrite app_nil_r. auto.
        * replace (min a e) with a by solve_addr.
          rewrite -region_addrs_split; auto. solve_addr.
  Qed.

  (* TODO: move to region_addrs *)
  Lemma region_addrs_split3 b e n:
    region_size b e > n ->
    exists a, region_addrs b e = region_addrs b a ++ region_addrs a e /\ region_size b a = n.
  Proof.
    intros Hsize. rewrite /region_size in Hsize.
    assert (exists a, (b + n)%a = Some a) as [a Ha].
    { rewrite /incr_addr. destruct (Z_le_dec (b + n)%Z MemNum); [|solve_addr].
      destruct (Z_le_dec 0 (b + n)%Z); [eauto|solve_addr]. }
    exists a. split; [|rewrite /region_size; solve_addr].
    eapply region_addrs_split. split; solve_addr.
  Qed.

  (* TODO: move to region_addrs *)
  Lemma region_addrs_submseteq b b' e e':
    (b' <= b)%a ->
    (e <= e')%a ->
    region_addrs b e ⊆+ region_addrs b' e'.
  Proof.
    intros. destruct (Addr_le_dec b e).
    - rewrite (region_addrs_split b' b e'); [|solve_addr].
      rewrite (region_addrs_split b e e'); [|solve_addr].
      eapply submseteq_middle.
    - rewrite interp_weakening.region_addrs_empty; [|solve_addr].
      eapply submseteq_nil_l.
  Qed.

  (* Need to update stdpp :'( *)
  Lemma list_filter_app { A: Type } (P: A -> Prop) `{ forall x, Decision (P x) } l1 l2:
    @list_filter _ P _ (l1 ++ l2) = @list_filter _ P _ l1 ++ @list_filter _ P _ l2.
  Proof.
    induction l1; simpl; auto.
    destruct (decide (P a)); auto.
    unfold filter. rewrite IHl1. auto.
  Qed.

  Lemma list_filter_forall { A: Type } (P: A -> Prop) `{ forall x, Decision (P x) } l:
    Forall P l ->
    @list_filter _ P _ l = l.
  Proof.
    induction 1; auto.
    simpl. destruct (decide (P x)); rewrite /filter; try congruence.
  Qed.

  Lemma big_sepL_delete' {PROP: bi} {A: Type} (φ: A -> PROP) (l: list A):
        forall k, (([∗ list] k0↦y ∈ l, if decide (k0 = k) then emp else φ y) -∗
             ([∗ list] k0↦x0 ∈ delete k l, (λ (_ : nat) (x1 : A), φ x1) k0 x0))%I.
  Proof.
    iInduction (l) as [|x l] "IH"; simpl; auto; iIntros (k) "H".
    iDestruct "H" as "[H1 H2]".
    rewrite /delete /=. destruct k.
    - iApply (big_sepL_impl with "H2").
      iClear "H1". iModIntro. iIntros. destruct (decide (S k = 0)); auto. lia.
    - simpl. iFrame. iApply ("IH" with "[H2]").
      iApply (big_sepL_impl with "H2").
      iModIntro; iIntros. destruct (decide (k0 = k)); destruct (decide (S k0 = S k)); auto; lia.
  Qed.

  (* TODO: move to iris ? *)
  Lemma big_sepL_merge {PROP: bi} {A: Type} (l: list A) (HNoDup: NoDup l) (φ: A -> PROP) {Haffine: forall a, Affine (φ a)}:
    forall l1 l2, (forall a, a ∈ l -> a ∈ l1 \/ a ∈ l2) ->
             (([∗ list] a ∈ l1, φ a) -∗
              ([∗ list] a ∈ l2, φ a) -∗
              ([∗ list] a ∈ l, φ a))%I.
  Proof.
    iInduction (l) as [|x l] "IH"; iIntros (l1 l2 H) "Hl1 Hl2".
    - iApply big_sepL_nil; auto.
    - iApply big_sepL_cons. destruct (H x ltac:(eapply elem_of_list_here)) as [H'|H']; eapply elem_of_list_lookup in H'; destruct H' as [k H'].
      + iDestruct (big_sepL_delete with "Hl1") as "[$ Hl1]"; eauto.
        iAssert ([∗ list] a ∈ delete k l1, φ a)%I with "[Hl1]" as "Hl1".
        { iApply (big_sepL_impl with "[Hl1]"); auto.
          iApply (big_sepL_delete' with "Hl1"). }
        assert (Hincl: ∀ a : A, a ∈ l → a ∈ delete k l1 ∨ a ∈ l2).
        { intros. destruct (H a ltac:(eapply elem_of_list_further; eauto)).
          - left. eapply elem_of_list_lookup in H1. destruct H1.
            eapply elem_of_list_lookup. assert (x0 <> k).
            + red; intros; subst x0. rewrite H1 in H'; inv H'.
              inv HNoDup. eapply H4. auto.
            + assert  (x0 < k \/ k <= x0) by lia. destruct H3.
              * exists x0. rewrite lookup_delete_lt; auto.
              * exists (x0 - 1). rewrite lookup_delete_ge; auto; try lia.
                replace (S (x0 - 1)) with x0; auto. lia.
          - right. auto. }
        inv HNoDup. iApply ("IH" $! H3 (delete k l1) l2 Hincl with "[$Hl1] [$Hl2]").
      + iDestruct (big_sepL_delete with "Hl2") as "[$ Hl2]"; eauto.
        iAssert ([∗ list] a ∈ delete k l2, φ a)%I with "[Hl2]" as "Hl2".
        { iApply (big_sepL_impl with "[Hl2]"); auto.
          iApply (big_sepL_delete' with "Hl2"). }
        assert (Hincl: ∀ a : A, a ∈ l → a ∈ l1 ∨ a ∈ delete k l2).
        { intros. destruct (H a ltac:(eapply elem_of_list_further; eauto)).
          - left. auto.
          - right. eapply elem_of_list_lookup in H1. destruct H1.
            eapply elem_of_list_lookup. assert (x0 <> k).
            + red; intros; subst x0. rewrite H1 in H'; inv H'.
              inv HNoDup. eapply H4. auto.
            + assert  (x0 < k \/ k <= x0) by lia. destruct H3.
              * exists x0. rewrite lookup_delete_lt; auto.
              * exists (x0 - 1). rewrite lookup_delete_ge; auto; try lia.
                replace (S (x0 - 1)) with x0; auto. lia. }
        inv HNoDup. iApply ("IH" $! H3 l1 (delete k l2) Hincl with "[$Hl1] [$Hl2]").
  Qed.

  (* TODO: move *)
  Lemma contiguous_between_inj l:
    forall a1 b1 b2,
      contiguous_between l a1 b1 ->
      contiguous_between l a1 b2 ->
      b1 = b2.
  Proof.
    induction l; intros.
    - inv H; inv H0; auto.
    - inv H; inv H0. rewrite H2 in H3; inv H3.
      eapply IHl; eauto.
  Qed.

  (* TODO: upstream to iris *)
  Lemma big_sepL2_to_big_sepM (PROP : bi) (A B : Type) `{EqDecision A} `{Countable A}
        (φ: A -> B -> PROP) (l1: list A) (l2: list B):
        NoDup l1 ->
        (([∗ list] y1;y2 ∈ l1;l2, φ y1 y2) -∗
        ([∗ map] y1↦y2 ∈ list_to_map (zip l1 l2), φ y1 y2))%I.
  Proof.
    revert l2. iInduction (l1) as [|x l1] "IH"; iIntros (l2 Hnd) "H".
    - iSimpl. iDestruct (big_sepL2_length with "H") as "%".
      destruct l2; simpl in H0; inv H0.
      iApply big_sepM_empty. auto.
    - iDestruct (big_sepL2_length with "H") as "%".
      destruct l2; simpl in H0; inv H0.
      simpl. inv Hnd. iDestruct "H" as "[A B]".
      iApply (big_sepM_insert with "[A B]").
      + eapply not_elem_of_list_to_map.
        rewrite fst_zip; auto. lia.
      + iFrame. iApply ("IH" $! l2 H4 with "B"); auto.
  Qed.

  (* TODO: move to sts.v ?*)
  Lemma rtc_rel_priv x y:
    x <> Permanent ->
    rtc (λ x y : region_type, Rpub x y ∨ Rpriv x y) x y.
  Proof.
    intros; destruct x, y; try congruence;
      repeat
        (match goal with
         | |- rtc (λ x y : region_type, Rpub x y ∨ Rpriv x y) ?X ?X => left
         | |- rtc (λ x y : region_type, Rpub x y ∨ Rpriv x y) Temporary ?X => eright; [try (left; constructor); right; constructor|left]
         | |- rtc (λ x y : region_type, Rpub x y ∨ Rpriv x y) ?X ?Y => right with Temporary; [try (left; constructor); right; constructor|]
         | _ => idtac
         end).
  Qed.

  (* TODO: move to multiple_update.v ? *)
  Lemma related_sts_priv_world_std_update_multiple W l ρ :
    Forall (λ a : Addr, ∃ ρ, (std W) !! a = Some ρ /\ ρ <> Permanent) l →
    related_sts_priv_world W (std_update_multiple W l ρ).
  Proof.
    intros Hforall.
    induction l. 
    - apply related_sts_priv_refl_world. 
    - eapply related_sts_priv_trans_world;[apply IHl|].
      + apply Forall_cons_1 in Hforall as [_ Hforall]. auto. 
      + split;[|rewrite std_update_multiple_loc_rel;apply related_sts_priv_refl].
        split. 
        ++ rewrite /std_update dom_insert_L. set_solver.
        ++ intros j x0 y Hx0 Hy.
           destruct (decide (a = j)).
           +++ subst. rewrite lookup_insert in Hy. inversion Hy; subst.
               apply Forall_cons_1 in Hforall as [Hi _].
               destruct (decide (j ∈ l)).
               { rewrite std_sta_update_multiple_lookup_in_i in Hx0; auto. inversion Hx0. left. }
               rewrite std_sta_update_multiple_lookup_same_i in Hx0; auto.
               rewrite /revoke /std /= in Hi.
               destruct Hi as [ρ [Hi Hi'] ].
               rewrite Hi in Hx0. inversion Hx0; subst.
               eapply rtc_rel_priv; auto.
           +++ rewrite /= lookup_insert_ne in Hy;auto. rewrite Hx0 in Hy; inversion Hy; subst; left.
  Qed.

  (* TODO: move? *)
  Definition mapsto_nO (a: Addr) (p: Perm) (w: Word) := (a ↦ₐ[p] w ∗ ⌜p ≠ O⌝)%I.
  Notation "a ↦ₐ < p > w" := (mapsto_nO a p w)
    (at level 20, p at level 50, format "a  ↦ₐ < p >  w") : bi_scope.

   (* the following spec is for the f4 subroutine of the awkward example, jumped to after dynamically allocating into r_env *)
  Lemma f4_spec W pc_p pc_p' pc_g pc_b pc_e (* PC *)
        wadv (* b e a *) (* adv *)
        wret (* g_ret b_ret e_ret a_ret *) (* return cap *)
        f4_addrs (* f2 *)
        d d' i (* dynamically allocated memory given by preamble, connected to invariant i *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        wstk (* stack *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' -> 

    (* Program adresses assumptions *)
    contiguous_between f4_addrs a_first a_last ->
    
    (* Linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* malloc'ed memory assumption *)
    (d + 1)%a = Some d' ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_adv;r_t0;r_env]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    {{{ r_stk ↦ᵣ wstk
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_adv ↦ᵣ wadv
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (awk_inv i d))
      ∗ sts_rel_loc (A:=Addr) i awk_rel_pub awk_rel_priv
      (* stack *)
      ∗ interp W wstk
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv code *)
      ∗ interp W wadv
      (* callback validity *)
      ∗ interp W wret
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (awkward_example f4_addrs pc_p' f_a r_adv 40)
      (* linking table *)
      ∗ na_inv logrel_nais ι2 (pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ[RW] fail_cap)
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r W', full_map r ∧ registers_mapsto r
                         ∗ ⌜related_sts_priv_world W W'⌝
                         ∗ na_own logrel_nais ⊤                           
                         ∗ sts_full_world W'
                         ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hfl Hcont Hwb_table Hlink_table Hd Hrmap_dom Hne φ)
            "(Hr_stk & HPC & Hr_t0 & Hr_adv & Hr_env & Hgen_reg & #Hι & #Hrel & #Hstack_val & Hna & #Hadv_val & #Hcallback & #Hf4 & #Htable & Hsts & Hr) Hφ".
    iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls)";[auto..|]. 
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct (f4_addrs);[inversion Hprog_length|].
    iDestruct "Hι" as (ι) "Hinv".
    (* We get some general purpose registers *)
    iAssert ((∃ w1, r_t1 ↦ᵣ w1) ∗ (∃ w2, r_t2 ↦ᵣ w2) ∗ [∗ map] r_i↦w_i ∈ delete r_t2 (delete r_t1 rmap), r_i ↦ᵣ w_i)%I
      with "[Hgen_reg]" as "(Hr_t1 & Hr_t2 & Hgen_reg)".
    { assert (is_Some (rmap !! r_t1)) as [w1 Hrt1].
      { apply elem_of_gmap_dom. rewrite Hrmap_dom. apply elem_of_difference.
        split;[apply all_registers_s_correct|clear;set_solver]. }
      assert (is_Some (delete r_t1 rmap !! r_t2)) as [w2 Hrt2].
      { apply elem_of_gmap_dom. rewrite dom_delete_L Hrmap_dom. apply elem_of_difference.
        split;[|clear;set_solver]. apply elem_of_difference.
        split;[apply all_registers_s_correct|clear;set_solver]. }
      iDestruct (big_sepM_delete _ _ r_t1 with "Hgen_reg") as "[Hr_t1 Hgen_reg]";[eauto|].
      iDestruct (big_sepM_delete _ _ r_t2 with "Hgen_reg") as "[Hr_t2 Hgen_reg]";[eauto|].
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iFrame. 
    }
    (* First we require wadv to be global *)
    iDestruct (contiguous_between_program_split with "Hprog") as (reqperm_prog rest link)
                                                                   "(Hreqglob & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_reqglob & Hcont_rest & Heqapp & Hlink).
    iDestruct (big_sepL2_length with "Hreqglob") as %Hreqglob_length. simpl in Hreqglob_length. 
    iApply (reqglob_spec with "[-]");
      [|apply Hfl|apply Hcont_reqglob|iFrame "HPC Hreqglob Hr_adv Hr_t1 Hr_t2"]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hmid Hcont_rest;clear;solve_addr. }
    iNext. destruct (isGlobalWord wadv) eqn:Hglob;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    (* If the macro is successful, we can infer that it is a Global capability *)
    destruct wadv as [z | [ [ [ [p g] b] e] a'] ];[inversion Hglob|].
    destruct g;[|inversion Hglob]. iExists _,_,_,_. iSplit;[eauto|]. iIntros "(HPC & Hreqglob & Hr_adv & Hr_t1 & Hr_t2)".
    (* Next we prepare the stack *)
    iDestruct (contiguous_between_program_split with "Hprog") as (preptack_prog rest0 link0)
                                                                   "(Hprepstack & Hprog & #Hcont)";[apply Hcont_rest|].
    iDestruct "Hcont" as %(Hcont_prepstack & Hcont_rest0 & Heqapp0 & Hlink0).
    iDestruct (big_sepL2_length with "Hprepstack") as %Hprepstack_length. simpl in Hprepstack_length.
    iApply (prepstackU_spec with "[-]");
      [|apply Hfl|apply Hcont_prepstack|iFrame "HPC Hprepstack Hr_stk"].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest0. revert Hmid Hcont_rest0 Hlink;clear. solve_addr. }
    iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_t2";[iNext;eauto|].
    iNext. destruct (isPermWord wstk URWLX) eqn:Hperm;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct (isPermWord_cap_isPerm _ _ Hperm) as [pstk [gstk [bstk [estk [astk [-> HX] ] ] ] ] ].
    eapply bool_decide_eq_true_1 in HX. subst pstk.
    iExists _, _, _, _. iSplitR; auto.
    destruct (10 <? estk - bstk)%Z eqn:Hsize';[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct (bstk <=? astk)%Z;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iIntros "Hcont".
    iDestruct "Hcont" as "(HPC & Hprestack & Hr_stk & Hr_t1 & Hr_t2)".
    (* We cleanup our definitions *)
    simplify_eq.
    assert (region_size bstk estk > 10) as Hsize; [|clear Hperm Hsize'].
    { apply Zlt_is_lt_bool in Hsize'. revert Hsize'. clear. rewrite /region_size /=. lia. }
    (* If the stack is Global, validity is false *)
    destruct gstk;[by rewrite fixpoint_interp1_eq;iSimpl in "Hstack_val"|].
    rewrite fixpoint_interp1_eq;iSimpl in "Hstack_val".
    iAssert ([∗ list] a'0 ∈ region_addrs bstk (min astk estk), read_write_cond a'0 RWLX (fixpoint interp1)
                                                               ∧ ⌜region_state_pwl W a'0⌝)%I as "#Hstack_region".
    { iDestruct "Hstack_val" as "[Hstack_region _]".
      iApply (big_sepL_mono with "Hstack_region").
      iIntros (k y Hk) "H". iDestruct "H" as (p0 Hperm) "Hw". destruct p0;inversion Hperm. iFrame. }
    iAssert ([∗ list] a'0 ∈ region_addrs (max bstk astk) estk, read_write_cond a'0 RWLX (fixpoint interp1)
                                                               ∧ ⌜region_state_U_pwl W a'0⌝)%I as "#Hstack_end".
    { iDestruct "Hstack_val" as "[_ Hstack_end]".
      iApply (big_sepL_mono with "Hstack_end").
      iIntros (k y Hk) "H". iDestruct "H" as (p0 Hperm) "Hw". destruct p0;inversion Hperm. iFrame. }
    destruct (region_addrs_split3 _ _ _ Hsize) as [asplit [Hstksplit Hspliteq] ].
    set (ltempsplit := (@list_filter Addr (region_type_temporary W) (region_type_temporary_dec W) (region_addrs bstk asplit))).
    set (ltemp := (@list_filter Addr (region_type_temporary W) (region_type_temporary_dec W) (region_addrs bstk estk))).
    set (ltemprest := (@list_filter Addr (region_type_temporary W) (region_type_temporary_dec W) (region_addrs asplit estk))).
    assert (Hltempspliteq: ltemp = ltempsplit ++ ltemprest).
    { rewrite /ltemp /ltempsplit /ltemprest.
      rewrite Hstksplit list_filter_app. auto. }
    iAssert (⌜Forall (λ a, region_type_temporary W a) ltemp⌝)%I as %Htemp.
    { iPureIntro. eapply List.Forall_forall.
      intros. eapply elem_of_list_filter.
      eapply elem_of_list_In; eauto. }
    remember Htemp as Htemp'. clear HeqHtemp'.
    rewrite Hltempspliteq in Htemp. eapply Forall_app in Htemp.
    destruct Htemp as [Htemp Htemprest].
    set (luninitsplit := (@list_filter Addr (region_type_uninitialized W) (region_type_uninitialized_dec W) (region_addrs bstk asplit))).
    (* set (luninit := (@list_filter Addr (region_type_uninitialized W) (region_type_uninitialized_dec W) (region_addrs bstk estk))). *)
    iAssert (⌜Forall (λ a, region_type_uninitialized W a) luninitsplit⌝)%I as %Huninit.
    { iPureIntro. eapply List.Forall_forall.
      intros. eapply elem_of_list_filter.
      eapply elem_of_list_In; eauto. }
    assert (Hdupuninit: NoDup luninitsplit).
    { eapply NoDup_filter, NoDup_ListNoDup, region_addrs_NoDup. }
    (* iAssert (⌜Forall (λ a, region_type_temporary W a) (region_addrs bstk (min astk estk))⌝)%I as %Htempforall. *)
    (* { iDestruct (big_sepL_and with "Hstack_region") as "[Hstack_rel Hstack_pwl]". *)
    (*   iDestruct (big_sepL_forall with "Hstack_pwl") as %Hforall. *)
    (*   iPureIntro. rewrite Forall_forall. intros x Hin. apply elem_of_list_lookup_1 in Hin as [k Hin]. *)
    (*   apply Hforall in Hin. auto. } *)
    (* assert (Hltempeq: ltemp = region_addrs bstk (min astk estk) ++ @list_filter Addr (region_type_temporary W) (region_type_temporary_dec W) (region_addrs (max bstk astk) estk)). *)
    (* { rewrite /ltemp (region_addrs_split2 bstk estk astk) list_filter_app. *)
    (*   f_equal; auto. eapply list_filter_forall. auto. } *)
    (* assert (Hluniniteq: luninit = (@list_filter Addr (region_type_uninitialized W) (region_type_uninitialized_dec W) (region_addrs (max bstk astk) estk))). *)
    (* { rewrite /luninit (region_addrs_split2 bstk estk astk) list_filter_app. *)
    (*   replace (list_filter (region_type_uninitialized W) (region_type_uninitialized_dec W) (region_addrs bstk (min astk estk))) with (@nil Addr); simpl; auto. *)
    (*   case_eq (list_filter (region_type_uninitialized W) (region_type_uninitialized_dec W) (region_addrs bstk (min astk estk))); intros; auto. *)
    (*   generalize (proj1 (@elem_of_list_filter _ (region_type_uninitialized W) (region_type_uninitialized_dec W) (region_addrs bstk (min astk estk)) a0)). rewrite /filter H. *)
    (*   destruct 1. eapply elem_of_list_here. *)
    (*   eapply Forall_forall in Htempforall; eauto. *)
    (*   rewrite /region_type_uninitialized in H0. *)
    (*   rewrite /region_type_temporary in Htempforall. *)
    (*   destruct H0; congruence. } *)
    (* We will now need to open the invariant for d. 
       We do not know which state d is in, and may need to 
       do a private transition from 1 to 0! For that reason 
       we will first revoke region, so that we can do private 
       updates to it. We do not care about the stack resources, 
       as it currently in the revoked state. 
     *)
    pose proof (extract_temps_split W ltemp) as [l' [Hdup Hiff] ];
      [apply NoDup_filter,NoDup_ListNoDup,region_addrs_NoDup|apply Htemp'|].
    iMod (monotone_revoke_keep_some W _ ltemp with "[$Hsts $Hr]") as "[Hsts [Hr [Hrest Hstack] ] ]";[apply Hdup|..].
    { iSplit.
      - iApply big_sepL_forall. iPureIntro. intros n. simpl. intros x Hsome. apply Hiff. apply elem_of_app; left.
        apply elem_of_list_lookup. eauto. 
      - iApply big_sepL_forall. iIntros. iSplit.
        + iPureIntro. eapply Hiff, elem_of_app; right.
          eapply elem_of_list_lookup; eauto.
        + generalize (proj2 (elem_of_list_lookup ltemp x) ltac:(eauto)); intro Hx.
          eapply elem_of_list_filter in Hx. destruct Hx as [Hx1 Hx2].
          rewrite (region_addrs_split2 _ _ astk) in Hx2.
          eapply elem_of_app in Hx2. destruct Hx2 as [Hx2|Hx2].
          * iDestruct (big_sepL_elem_of with "Hstack_region") as "[H _]"; eauto.
            rewrite /read_write_cond /=. iApply "H".
          * iDestruct (big_sepL_elem_of with "Hstack_end") as "[H _]"; eauto. }
    rewrite Hltempspliteq. iDestruct (big_sepL_app with "Hstack") as "[Hstack Hstackrest]".
    (* Revoke some uninitialized to get their points to *)
    iMod (region_uninitialized_to_revoked W _ _ _ Hdupuninit with "[$Hsts $Hr]") as "HHH".
    { iApply big_sepL_forall. iIntros. iSplit.
      - iPureIntro. eapply (proj1 (elem_of_list_filter (region_type_uninitialized W) _ _)).
        eapply elem_of_list_lookup. exists k. eauto.
      - generalize (proj2 (elem_of_list_lookup luninitsplit x) ltac:(eauto)); intro Hx.
        eapply elem_of_list_filter in Hx. destruct Hx as [Hx1 Hx2].
        eapply elem_of_submseteq in Hx2; [|eapply (submseteq_inserts_r (region_addrs asplit estk) (region_addrs bstk asplit) (region_addrs bstk asplit)); auto].
        rewrite -Hstksplit in Hx2. rewrite (region_addrs_split2 _ _ astk) in Hx2.
        eapply elem_of_app in Hx2. destruct Hx2 as [Hx2|Hx2].
        * iDestruct (big_sepL_elem_of with "Hstack_region") as "[H _]"; eauto.
          rewrite /read_write_cond /=. iApply "H".
        * iDestruct (big_sepL_elem_of with "Hstack_end") as "[H _]"; eauto. }
    iDestruct "HHH" as "[Hsts [Hr Huninitstack]]".
    set (W' := (std_update_multiple (revoke W) luninitsplit Revoked)).
    iAssert ((▷ ∃ ws, ([∗ list] a;w ∈ region_addrs bstk asplit;ws, a ↦ₐ[RWLX] w))
               ∗ ⌜Forall (λ a : Addr, region_type_revoked W' a) ltempsplit⌝
               ∗ ⌜Forall (λ a : Addr, region_type_revoked W' a) luninitsplit⌝)%I
    (* iAssert ((▷ ∃ ws, ([∗ list] a;w ∈ ltemp;ws, a ↦ₐ[RWLX] w)) *)
    (*            ∗ ⌜Forall (λ a : Addr, region_type_revoked (revoke W) a) ltemp⌝)%I *)
      with "[Hstack Huninitstack]" as "[>Hstack [#Hrevoked1 #Hrevoked2]]".
    { iDestruct (big_sepL_sep with "Hstack") as "[Hstack #Hrevoked]".
      iDestruct (big_sepL_forall with "Hrevoked") as %Hrevoked.
      rename Hrevoked into Hrevoked'.
      assert (Hrevoked: ∀ (x : nat) (x0 : Addr), ltempsplit !! x = Some x0 → std (revoke W) !! x0 = Some Revoked).
      { intros. eapply Hrevoked'. rewrite Hltempspliteq. eauto. }
      iSplit;[|iPureIntro].
      - iDestruct (big_sepL_sep with "Hstack") as "[Hstack _]". iNext.
        iApply region_addrs_exists.
        iDestruct (region_addrs_exists with "Hstack") as (ws) "Hstack".
        iDestruct (big_sepL2_sep with "Hstack") as "[_ Hstack]".
        iDestruct (big_sepL2_sep with "Hstack") as "[Hstack _]".
        iDestruct (region_addrs_exists with "[Hstack]") as "Hstack".
        { iExists ws; auto. }
        iAssert (∀ x : Addr, ⌜x ∈ region_addrs bstk asplit⌝ → ⌜region_type_temporary W x ∨ region_type_uninitialized W x⌝)%I as %HHH.
        { iIntros. eapply elem_of_submseteq in a0; [|eapply (submseteq_inserts_r (region_addrs asplit estk) (region_addrs bstk asplit) (region_addrs bstk asplit)); auto].
          rewrite -Hstksplit in a0. rewrite (region_addrs_split2 _ _ astk) in a0.
          eapply elem_of_app in a0. destruct a0 as [a0|a0].
          * iDestruct (big_sepL_elem_of with "Hstack_region") as "[_ %]"; eauto.
          * iDestruct (big_sepL_elem_of with "Hstack_end") as "[_ %]"; eauto. }
        iApply (big_sepL_merge with "[$Hstack] [$Huninitstack]").
        { eapply NoDup_ListNoDup,region_addrs_NoDup. }
        { intros. destruct (HHH _ H) as [HH|HH].
          - left. eapply elem_of_list_filter; auto.
          - right. eapply elem_of_list_filter; auto. }
      - split.
        + revert Htemp; repeat (rewrite Forall_forall). 
          intros Htemp x Hx. eapply elem_of_list_lookup in Hx.
          destruct Hx. rewrite /W' /region_type_revoked std_sta_update_multiple_lookup_same_i.
          eapply Hrevoked; eauto.
          red; intro. eapply elem_of_list_filter in H0. destruct H0.
          eapply Hrevoked in H. destruct H0.
          rewrite /revoke /revoke_std_sta lookup_fmap H0 /= in H.
          discriminate.
        + eapply Forall_forall. intros. rewrite /W' /region_type_revoked.
          eapply std_sta_update_multiple_lookup_in_i; auto. }
    iDestruct "Hrevoked1" as %Hrevoked1.
    iDestruct "Hrevoked2" as %Hrevoked2.
    (* For later use it will be useful to know that W contains i *)
    (* Now we may do any private transitions to our local invariants.
       since we don't know which case we are in, we can generalize and 
       say that there exists some private future world such that   
       the store succeeded, after which the state at i is false
     *)
    iDestruct (big_sepL2_length with "Hprog") as %Hrest0_length.
    destruct rest0;[inversion Hrest0_length|]. 
    iPrologue rest0 Hrest0_length "Hprog".
    apply contiguous_between_cons_inv_first in Hcont_rest0 as Heq. subst a0.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link0 a_last) as Hvpc'.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      revert Hlink Hlink0 Hmid. clear. solve_addr. }
    assert (withinBounds (RWX, Global, d, d', d) = true) as Hwb.
    { isWithinBounds;[lia|]. revert Hd; clear. solve_addr. }
    iAssert (▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a1)
              ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
              ∗ link0 ↦ₐ[pc_p'] store_z r_env 0
              ∗ (∃ W'',⌜(∃ b : bool, W.2.1 !! i = Some (encode b))
                        ∧ W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝ ∧ 
                    ⌜W'' = (W'.1,(<[i:=encode false]> W.2.1,W.2.2))⌝ ∧
                    ⌜related_sts_priv_world W' W''⌝ ∧
                    ⌜W''.2.1 !! i = Some (encode false)⌝ ∧
                    region W'' ∗ sts_full_world W'' ∗
                    ⌜Forall (λ a : Addr, region_type_revoked W'' a) ltempsplit⌝ ∗
                    ⌜Forall (λ a : Addr, region_type_revoked W'' a) luninitsplit⌝)
              -∗ WP Seq (Instr Executable) {{ v, φ v }})
        -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
      with "[HPC Hinstr Hr_env Hr Hsts]" as "Hstore_step".
    { iIntros "Hcont". 
      (* store r_env 0 *)
      iInv ι as (x) "[>Hstate Hb]" "Hcls".
      destruct x; iDestruct "Hb" as ">Hb".
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC link0 a_last|iContiguous_next Hcont_rest0 0|auto|auto|..].
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* we assert that updating the local state d to 0 is a private transition *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.
        assert (related_sts_priv_world (std_update_multiple W luninitsplit Revoked) ((std_update_multiple W luninitsplit Revoked).1, (<[i:=encode false]> (std_update_multiple W luninitsplit Revoked).2.1, (std_update_multiple W luninitsplit Revoked).2.2)))
          as Hrelated;[apply related_priv_local_1; auto|].
        rewrite /std_update_multiple_loc_sta.
        rewrite /W' std_update_multiple_revoke_commute /std_update_multiple_loc_sta in Hlookup; auto.
        rewrite /std_update_multiple_loc_rel.
        rewrite /W' std_update_multiple_revoke_commute /std_update_multiple_loc_rel in Hrel; auto.
        (* first we can update region privately since it is revoked *)
        iAssert (sts_full_world W'
               ∗ region (W'.1, (<[i:=encode false]> W'.2.1, W'.2.2)))%I with "[Hsts Hr]" as "[Hsts Hr]".
        { rewrite /W' std_update_multiple_revoke_commute; auto.
          rewrite region_eq /region_def.
          iDestruct "Hr" as (M Mρ) "(HM & % & % & Hr)".
          iDestruct (monotone_revoke_list_region_def_mono_same $! Hrelated with "Hsts Hr") as "[Hsts Hr]".
          iFrame. iExists M, Mρ. iFrame. iPureIntro. auto.
        }
        rewrite /W' std_update_multiple_loc_sta in Hlookup; auto.
        rewrite /W' std_update_multiple_loc_rel in Hrel; auto.
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
        split; [auto|]. f_equal. f_equal.
        rewrite /W' std_update_multiple_loc_sta.
        rewrite /revoke /=. reflexivity.
        rewrite /W' std_update_multiple_loc_rel.
        rewrite /revoke /=. reflexivity.
        split;[apply revoke_monotone in Hrelated; auto|split;[apply lookup_insert|] ].
        rewrite /W' std_update_multiple_revoke_commute; auto.
        split. eapply Forall_impl;[apply Hrevoked1|].
        intros a2 Ha0_rev; auto.
        eapply Forall_impl;[apply Hrevoked2|].
        intros a2 Ha0_rev; auto.
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC link0 a_last|iContiguous_next Hcont_rest0 0|auto|auto|..].
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* use sts_state to assert that the current state of i is false *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.
        rewrite /W' std_update_multiple_revoke_commute in Hlookup; auto.
        rewrite /W' std_update_multiple_revoke_commute in Hrel; auto.
        (* No need to update the world, since we did not change state *)
        iMod ("Hcls" with "[Hstate Hd]") as "_". 
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        iExists _. iFrame. iPureIntro. rewrite /revoke /loc /= in Hlookup.
        rewrite std_update_multiple_loc_sta in Hlookup.
        rewrite /revoke /loc /= in Hrel.
        rewrite std_update_multiple_loc_rel in Hrel.
        apply insert_id in Hlookup as Heq. rewrite Heq. split;[eauto|]. split.
        { destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ]. simpl.
          rewrite /W' std_update_multiple_revoke_commute; auto.
          rewrite /revoke /loc std_update_multiple_loc /=. auto. }
        split;[apply related_sts_priv_refl_world|split;auto].
        rewrite /W' std_update_multiple_revoke_commute; auto.
        rewrite /revoke /loc std_update_multiple_loc_sta /=. auto.
    }
    iApply "Hstore_step".
    iNext. iIntros "(HPC & Hr_env & Hprog_done & HW')".
    iDestruct "HW'" as (W'' [Hawki Hawk] HeqW' Hrelated Hfalse) "(Hr & Hsts & #Hforall1 & #Hforall2)".
    clear Hrevoked1. clear Hrevoked2.
    iDestruct "Hforall1" as %Hrevoked1.
    iDestruct "Hforall2" as %Hrevoked2.
    (* we prepare the stack for storing local state *)
    (* Splitting the stack into own and adv parts *)
    assert (contiguous (region_addrs bstk estk)) as Hcont_stack;[apply region_addrs_contiguous|].
    assert (contiguous_between (region_addrs bstk estk) bstk estk) as Hcontiguous.
    { apply contiguous_between_of_region_addrs; auto. revert Hsize. rewrite /region_size. clear. solve_addr. }
    iDestruct "Hstack" as (ws) "Hstack".
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 10)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { exists ws, []. split; auto. rewrite app_nil_r. auto.
      rewrite -Hlength. rewrite region_addrs_length; auto. }
      (* rewrite region_addrs_length in Hlength; auto. rewrite Hlength in Hsize. *)
      (* do 11 (destruct ws as [|? ws]; [simpl in Hsize; lia|]). *)
      (*      by exists [w;w0;w1;w2;w3;w4;w5;w6;w7;w8;w9],ws. } *)
    rewrite Happ. assert (Hcontiguous': contiguous_between (region_addrs bstk asplit) bstk asplit).
    { eapply contiguous_between_of_region_addrs; auto.
      rewrite /region_size in Hspliteq. revert Hspliteq; clear; solve_addr. }
    iDestruct (contiguous_between_program_split with "Hstack") as (stack_own stack_adv stack_own_last) "(Hstack_own & Hstack_adv & #Hcont)"; [eauto|].
    iDestruct "Hcont" as %(Hcont1 & Hcont2 & Hstack_eq1 & Hlink1).
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_own. rewrite Hlength' in Hlength_own.
    rewrite Hstack_eq1 in Hcontiguous'.
    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_f2.
    iDestruct (big_sepL2_length with "Hstack_adv") as %Hlength_adv.
    (* Getting the three top adress on the stack *)
    do 4 (destruct stack_own; [inversion Hlength_own|]; destruct ws_own;[inversion Hlength'|]).
    assert ((region_addrs bstk asplit) !! 0 = Some bstk) as Hfirst_stack.
    { apply region_addrs_first. revert Hspliteq; clear. rewrite /region_size. solve_addr. }
    rewrite Hstack_eq1 /= in Hfirst_stack. inversion Hfirst_stack as [Heq]. subst bstk.
    (* assert that the stack bounds are within bounds *)
    assert (withinBounds (RWLX,Local,a0,estk,a0) = true ∧ withinBounds (RWLX,Local,a0,estk,stack_own_last) = true) as [Hwb1 Hwb2].
    { split; isWithinBounds; first lia.
      - revert Hsize. rewrite /region_size. clear. solve_addr.
      - by eapply contiguous_between_bounds.
      - apply contiguous_between_bounds in Hcont2. simplify_eq.
        revert Hlength' Hlength Hlink1 Hsize Hlength_adv Hlength_own Hcont2. rewrite -region_addrs_length app_length. clear.
        rewrite !region_addrs_length /region_size. solve_addr.
    }
    (* push r_stk r_env *)
    iDestruct "Hstack_own" as "[Ha Hstack_own]".
    do 2 (destruct rest0;[inversion Hrest0_length|]).
    iDestruct (big_sepL2_app_inv _ [a1] (a5::a6::rest0) with "Hprog") as "[Hpush Hprog]"; [simpl;auto|].
    iDestruct "Hpush" as "[Hpush _]".
    iApply (pushU_r_spec); [..|iFrame "HPC Hpush Hr_stk Hr_env Ha"];
      [|apply Hfl|auto|iContiguous_next Hcont_rest0 1|iContiguous_next Hcont_rest0 1|auto|..].
    { iCorrectPC link0 a_last. }
    { iContiguous_next Hcont1 0. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_self *)
    (destruct rest0;[inversion Hrest0_length|]).
    iDestruct (big_sepL2_app_inv _ [a5] (a6::a7::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iDestruct "Hstack_own" as "[Ha2 Hstack_own]".
    iDestruct "Hpush" as "[Hpush _]".
    iApply (pushU_r_spec);[..|iFrame "HPC Hpush Hr_stk Hr_t0 Ha2"];
      [|apply Hfl|auto| |
       iContiguous_next Hcont_rest0 2|iContiguous_next Hcont1 1|..].
    { iCorrectPC link0 a_last. }
    { iContiguous_bounds_withinBounds a0 stack_own_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha2)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_adv *)
    (* do 2 (destruct rest0;[inversion Hrest0_length|]). *)
    iDestruct (big_sepL2_app_inv _ [a6] (a7::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|].
    iDestruct "Hstack_own" as "[Ha3 Hstack_own]".
    iDestruct "Hpush" as "[Hpush _]".
    iApply (pushU_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_adv Ha3"];
      [|apply Hfl| auto| |
       iContiguous_next Hcont_rest0 3|iContiguous_next Hcont1 2|..].
    { iCorrectPC link0 a_last. }
    { iContiguous_bounds_withinBounds a0 stack_own_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_adv & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* prepare for scall *)
    (* Prepare the scall prologue macro *)
    rename a4 into stack_own_b.
    (* destruct stack_own as [|stack_own_b stack_own];[inversion Hlength_own|]. *)
    assert ((stack_own_b :: stack_own) = region_addrs stack_own_b stack_own_last) as ->.
    { apply region_addrs_of_contiguous_between; auto.
      repeat (inversion Hcont1 as [|????? Hcont1']; subst; auto; clear Hcont1; rename Hcont1' into Hcont1). }
    (* assert (stack_adv = region_addrs stack_own_last e_r) as ->. *)
    (* { apply region_addrs_of_contiguous_between; auto. } *)
    assert (contiguous_between (a7 :: rest0) a7 a_last) as Hcont_weak.
    { repeat (inversion Hcont_rest0 as [|????? Hcont_rest0']; subst; auto; clear Hcont_rest0; rename Hcont_rest0' into Hcont_rest0). }
    iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue rest1 s_last)
                                                                   "(Hscall & Hf2 & #Hcont)"; [eauto|..].
    clear Hfirst_stack Hcont_weak.
    iDestruct "Hcont" as %(Hcont_scall & Hcont_rest1 & Hrest_app & Hlink').
    iDestruct (big_sepL2_length with "Hscall") as %Hscall_length. simpl in Hscall_length, Hlength_f2.
    assert ((stack_own_b + 7)%a = Some stack_own_last) as Hstack_own_bound.
    { rewrite -(addr_add_assoc a0 _ 3). assert ((3 + 7) = 10)%Z as ->;[done|].
      rewrite Hlength_own in Hlink1. revert Hlink1; clear; solve_addr.
      apply contiguous_between_incr_addr with (i:=3) (ai:=stack_own_b) in Hcont1; auto. }
    assert (∃ a, (stack_own_b + 6)%a = Some a) as [stack_own_end Hstack_own_bound'].
    { revert Hstack_own_bound. clear. intros H. destruct (stack_own_b + 6)%a eqn:Hnone; eauto. solve_addr. }
    assert (a7 < s_last)%a as Hcontlt.
    { revert Hscall_length Hlink'. clear. solve_addr. }
    assert (link0 <= a7)%a as Hcontge.
    { apply region_addrs_of_contiguous_between in Hcont_scall. simplify_eq. revert Hscall_length Hcont_rest0 Hcontlt. clear =>Hscall_length Hf2 Hcontlt.
      apply contiguous_between_middle_bounds with (i := 4) (ai := a7) in Hf2;[solve_addr|auto]. 
    }
    (* scall *)
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hgen_reg $Hr_t1]") as "Hgen_reg".
    { rewrite lookup_delete_ne;auto. apply lookup_delete. }
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hgen_reg $Hr_t2]") as "Hgen_reg".
    { rewrite lookup_insert_ne;auto. apply lookup_delete. }
    iDestruct (big_sepM_insert _ _ r_env with "[$Hgen_reg $Hr_env]") as "Hgen_reg".
    { repeat (try rewrite lookup_insert_ne;auto; try rewrite lookup_delete_ne;auto). 
      enough (r_env ∉ dom (gset RegName) rmap) as HH by rewrite not_elem_of_dom // in HH.
      rewrite Hrmap_dom. rewrite not_elem_of_difference; right. set_solver. }
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hgen_reg $Hr_self]") as "Hgen_reg".
    { repeat (try rewrite lookup_insert_ne;auto; try rewrite lookup_delete_ne;auto). 
      enough (r_t0 ∉ dom (gset RegName) rmap) as HH by rewrite not_elem_of_dom // in HH.
      rewrite Hrmap_dom. rewrite not_elem_of_difference; right. set_solver. }
    iApply (scallU_prologue_spec with "[- $HPC $Hr_stk $Hscall $Hstack_own $Hgen_reg]");
      [ | |apply Hwb2| |apply Hcont_scall|apply Hfl|iNotElemOfList|
        iContiguous_next Hcont1 2|apply Hstack_own_bound'|apply Hstack_own_bound| |done|..].
    { assert (s_last <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest1|].
      intros mid Hmid. apply isCorrectPC_inrange with link0 a_last; auto.
      revert Hle Hcontlt Hcontge Hmid. clear. intros. split; solve_addr. }
    { simplify_eq. iContiguous_bounds_withinBounds a0 stack_own_last. }
    { clear; split; solve_addr. }
    { rewrite !dom_insert_L !dom_delete_L !Hrmap_dom !singleton_union_difference_L
              !difference_diag_L !all_registers_union_l !difference_difference_L.
      f_equal. clear. set_solver. }
    { assert (5 + 40 = 45)%Z as ->;[done|]. rewrite Hscall_length in Hlink'. done. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hscall)".
    iDestruct (big_sepL2_length with "Hf2") as %Hf2_length. simpl in Hf2_length.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last a_last) as Hvpc1.
    { intros mid Hmid. assert (link0 <= s_last)%a as Hle;[apply contiguous_between_bounds in Hcont_scall; revert Hcont_scall Hcontge;clear; solve_addr|].
      apply isCorrectPC_inrange with link0 a_last; auto.
      revert Hmid Hle. clear. solve_addr. }
    
    (* We now want to reason about unknown code. For this we invoke validity of wadv *)
    (* Before we can show the validity of the continuation, we need to set up the invariants 
       for local state, as well as the invariant for the stack *)

    (* We set the local stack frame and all the leftover Temporary resources to static *)

    (* first, put together again the resources for the frame *)
    iDestruct (region_mapsto_cons with "[Ha3 Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 2| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=3) (ai:=stack_own_b) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    iDestruct (region_mapsto_cons with "[Ha2 Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 1| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=2) (ai:=a3) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    iDestruct (region_mapsto_cons with "[Hb_r Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 0| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=1) (ai:=a2) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    
    (* Next we want to define the map which will keep track of each word and permission *)
    iDestruct (temp_resources_split with "Hrest") as (pws) "[#Hrest_valid [#Hrev Hrest]]".
    iDestruct "Hrev" as %Hrev.
    match goal with |- context [ [[a0,stack_own_last]]↦ₐ[RWLX][[ ?instrs ]]%I ] =>
                    set l_frame := instrs
    end.
    set m_static1 := lists_to_static_region (region_addrs a0 stack_own_last ++ l')
                                                  (l_frame ++ pws).

    (* we'll need that later to reason on the fact that the [zip] in the definition of
       l_frame indeed fully uses both lists *)
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_stack_own1.

    assert (Heqq: region_addrs a0 asplit = (a0 :: a2 :: a3 :: stack_own_b :: stack_own)).
    { rewrite -region_addrs_length Hstack_eq1 app_length Hlength_own in Hspliteq.
      rewrite Hstack_eq1. destruct stack_adv; [rewrite app_nil_r; auto|].
      simpl in Hspliteq; lia. }
    assert (Hxx: stack_own_last = asplit).
    { assert (a0 <= asplit)%a.
      { revert Hspliteq. clear. intros.
        rewrite /region_size in Hspliteq. solve_addr. }
      revert Hstack_own_bound Hspliteq H Heqq.
      rewrite -region_addrs_length. clear.
      simpl. intros. symmetry in Heqq.
      generalize (contiguous_between_of_region_addrs _ _ _ H Heqq).
      intro. inversion H0; subst. inv H6. inv H9. inv H10.
      assert ((a0 + 10)%a = Some stack_own_last) by solve_addr.
      rewrite region_addrs_length in Hspliteq.
      generalize (contiguous_between_of_region_addrs_aux _ _ stack_own_last _ Heqq).
      rewrite Hspliteq. rewrite H1. intro.
      generalize (H2 eq_refl); clear H2; intro.
      revert H0 H2; clear; intros. eapply contiguous_between_inj; eauto. }
    subst asplit.
    iAssert (⌜forall a, a ∈ region_addrs a0 stack_own_last -> region_state_U_pwl W a⌝)%I as %HXYZ.
    { iIntros (xa Hxa). assert (xa ∈ region_addrs a0 estk) by (rewrite Hstksplit; eapply elem_of_app; eauto).
      rewrite (region_addrs_split2 a0 estk astk) in H. eapply elem_of_app in H. destruct H.
      - iDestruct (big_sepL_elem_of with "Hstack_region") as "[_ %]"; eauto. iPureIntro.
        left; auto.
      - iDestruct (big_sepL_elem_of with "Hstack_end") as "[_ $]"; eauto. }
    (* Allocate the static region containing the local stack frame and leftovers *)
    assert (NoDup (region_addrs a0 stack_own_last ++ l')) as Hdup1.
    { rewrite Permutation_app_comm.
      eapply NoDup_app. repeat split.
      - eapply NoDup_app in Hdup; destruct Hdup; auto.
      - intros. red; intros. destruct (HXYZ _ H0).
        + assert (x ∈ ltempsplit) by (eapply elem_of_list_filter; eauto).
          assert (x ∈ ltemp) by (rewrite Hltempspliteq; eapply elem_of_app; auto).
          eapply NoDup_app in Hdup. destruct Hdup as [A [B C] ].
          eapply B; eauto.
        + assert (std W !! x = Some Temporary) by (eapply Hiff, elem_of_app; auto).
          destruct H1; congruence.
      - eapply NoDup_ListNoDup, region_addrs_NoDup. }

    iAssert (([∗ list] a'0 ∈ region_addrs a0 estk, read_write_cond a'0 RWLX (fixpoint interp1)) ∗ ⌜Forall (λ a : Addr, region_type_temporary W a \/ region_type_uninitialized W a) (region_addrs a0 estk)⌝)%I as "[#Hstackallrel %]".
    { rewrite (region_addrs_split2 a0 estk astk). rewrite big_sepL_app. iSplit.
      - iSplit.
        + iApply (big_sepL_impl with "Hstack_region").
          iAlways. iIntros (k x) "% [$ _]".
        + iApply (big_sepL_impl with "Hstack_end").
          iAlways. iIntros (k x) "% [$ _]".
      - rewrite Forall_app !Forall_forall. iSplit.
        + iIntros (x Hxin). iDestruct (big_sepL_elem_of with "Hstack_region") as "[HHH %]"; eauto.
        + iIntros (x Hxin). iDestruct (big_sepL_elem_of with "Hstack_end") as "[HHH %]"; eauto. }
    
    iDestruct (region_revoked_to_static ((std (std_update_multiple W luninitsplit Revoked)), (<[i:=encode false]> W.2.1, W.2.2)) m_static1
                 with "[Hsts Hr Hstack_own Hrest]") as ">[Hsts Hr]".
    { rewrite /W' std_update_multiple_revoke_commute in HeqW'; auto.
      rewrite HeqW' /revoke /=. iFrame. rewrite /region_mapsto.
      iApply (big_sepL2_to_static_region _ _ (λ a w, ∃ p φ, a ↦ₐ[p] w ∗ rel a p φ)%I with "[] [Hstack_own Hrest]").
      - auto.
      - iAlways.
        iIntros (k y wy Hin1 Hin2) "Hy /=".
        iDestruct "Hy" as (p' φ') "[Hy #Hrely]". 
        destruct (decide (k < length (l_frame))). 
        + rewrite lookup_app_l in Hin1;[|rewrite Hlength_stack_own1;auto].
          rewrite lookup_app_l in Hin2;[|auto].
          iExists RWLX,(λ Wv, interp Wv.1 Wv.2). iFrame. 
          iSplit;[iPureIntro;apply _|]. iSplit;auto.
          apply withinBounds_le_addr in Hwb2.
          rewrite (region_addrs_split a0 stack_own_last estk);[|revert Hwb2;clear;solve_addr].
          iDestruct (big_sepL_app with "Hstackallrel") as "[Hframe _]".
          iDestruct (big_sepL_elem_of with "Hstackallrel") as "Htest'";
            [apply elem_of_app;left;apply elem_of_list_lookup;eauto|auto].
          iDestruct (rel_agree y p' RWLX with "[$Hrely $Htest']") as "[% _]". subst p'.
          iFrame "Hy Htest'". 
        + assert (length l_frame <= k);[revert n;clear;lia|]. 
          rewrite lookup_app_r in Hin1;[|rewrite Hlength_stack_own1;auto].
          rewrite lookup_app_r in Hin2;[|auto].
          rewrite Hlength_stack_own1 in Hin1. simpl in Hin1,Hin2.
          iDestruct (big_sepL2_lookup with "Hrest_valid") as "Hyv";[apply Hin1|apply Hin2|].
          iDestruct "Hyv" as (p0 φ0) "(Hpers & Hne & Hφ & Hrely' & Hmono)".
          iDestruct (rel_agree y p' p0 with "[$Hrely $Hrely']") as "[% Heq]". subst p0.
          iExists _,_. iFrame "Hrely' Hy". auto. 
      - iFrame.
        apply withinBounds_le_addr in Hwb2.
        rewrite (region_addrs_split a0 stack_own_last estk);[|revert Hwb2;clear;solve_addr].
        iDestruct (big_sepL_app with "Hstackallrel") as "[Hframe _]".
        iDestruct (big_sepL2_sep with "[Hframe $Hstack_own]") as "Hstack_own".
        { iApply big_sepL2_to_big_sepL_l;auto. }
        iApply (big_sepL2_mono with "Hstack_own").
        iIntros (k y1 ? Hin1 Hin2) "Hrel".
        iExists RWLX,(λ Wv, interp Wv.1 Wv.2). iFrame. 
    }

    (* Next we close the adversary stack region so that it is Temporary *)
    iDestruct (big_sepL2_length with "Hrest_valid") as %Hlength_rest.
    rewrite std_update_multiple_revoke_commute; auto.
    iDestruct (big_sepL_sep with "Hstackrest") as "[Hstackrest _]".
    iDestruct (big_sepL_sep with "Hstackrest") as "[Hstackrest Hstackrest']".
    iDestruct (region_addrs_exists with "Hstackrest") as (wsrest) "Hstackrest".
    iDestruct (big_sepL2_length with "Hstackrest") as %Hlengthstackrest.
    iDestruct (big_sepL2_to_big_sepL_l with "Hstackrest'") as "Hstackrest'"; [eapply Hlengthstackrest|].
    (* We need to first remember that all words in m_uninit1 are valid *)
    iSimpl in "Hstackrest". 
    iDestruct (big_sepL2_mono with "Hstackrest") as "Hstackrest".
    { iIntros (k y1 y2 Hy1 Hy2) "H". repeat rewrite bi.sep_assoc. iExact "H". }
    iDestruct (big_sepL2_sep with "Hstackrest") as "[Hstackrest #Hold_temps_valid]". 
    iDestruct (big_sepL2_sep with "[$Hstackrest $Hstackrest']") as "Hstackrest".
    set m_uninit1 : gmap Addr Word := list_to_map (zip ltemprest wsrest).    
    iMod (region_revoked_to_uninitialized _ m_uninit1 with "[$Hsts $Hr Hstackrest]") as "[Hsts Hr]".
    { iDestruct (big_sepL2_to_big_sepM with "Hstackrest") as "HH".
      - eapply NoDup_filter, NoDup_ListNoDup, region_addrs_NoDup.
      - rewrite /m_uninit1. iApply (big_sepM_mono with "HH").
        simpl; intros. iIntros "[[[A B] C] D]".
        iExists _, _. iFrame. iPureIntro. intros; eapply interp_persistent. }

    (* Resulting world *)
    set W''' := (override_uninitializedW m_uninit1
              (revoke
                 (std_update_multiple (std (std_update_multiple W luninitsplit Revoked), (<[i:=encode false]> W.2.1, W.2.2))
                    (elements (dom (gset Addr) m_static1)) (Static m_static1)))).
    
    assert (related_sts_priv_world W'' W''') as HW'W''.
    { rewrite HeqW' /W''' /W' /= std_update_multiple_revoke_commute /=; auto.
      rewrite -std_update_multiple_revoke_commute /=; auto.
      eapply related_sts_priv_trans_world with (std_update_multiple
       (revoke (std (std_update_multiple W luninitsplit Revoked), (<[i:=encode false]> W.2.1, W.2.2)))
       (elements (dom (gset Addr) m_static1)) (Static m_static1)).
      - eapply related_sts_priv_world_static. simpl.
        rewrite lists_to_static_region_dom.
        + eapply Forall_forall. intros.
          assert (x ∈ region_addrs a0 stack_own_last ++ l').
          { eapply elem_of_list_permutation_proper; [| exact H0].
            symmetry; eapply elements_list_to_set. auto. }
          apply elem_of_app in H1. destruct H1 as [Hin | Hin].
          * generalize (HXYZ _ Hin). intros Hin'; destruct Hin'.
            { destruct W; simpl. eapply revoke_lookup_Temp.
              rewrite std_sta_update_multiple_lookup_same_i; auto.
              red; intro. eapply Forall_forall in Huninit; eauto.
              destruct Huninit. rewrite H1 in H3. inv H3. }
            { eapply revoke_lookup_Revoked.
              eapply std_sta_update_multiple_lookup_in_i.
              eapply (proj2 (elem_of_list_filter _ _ _)). 
              split; eauto. }
          * generalize (proj2 (Hiff x) ltac:(eapply elem_of_app; left; auto)). intros.
            eapply revoke_lookup_Temp. rewrite std_sta_update_multiple_lookup_same_i; auto.
            red; intro. eapply Forall_forall in Huninit; eauto.
            destruct Huninit. rewrite H1 in H3. inv H3.
        + rewrite !app_length. f_equal; auto.
      - eapply related_sts_priv_world_override_uninitializedW.
        eapply Forall_forall. intros.
        eapply (proj1 (elem_of_elements _ _)) in H0.
        eapply elem_of_dom in H0. destruct H0.
        eapply elem_of_list_to_map_2, elem_of_zip_l in H0.
        destruct (decide (x ∈ (elements (dom (gset Addr) m_static1)))).
        + exists (Static m_static1). split; auto.
          rewrite std_sta_update_multiple_lookup_in_i; auto.
        + exists Revoked. rewrite std_sta_update_multiple_lookup_same_i; auto.
          simpl. destruct (decide (x ∈ luninitsplit)).
          * rewrite revoke_lookup_Revoked; auto.
            rewrite std_sta_update_multiple_lookup_in_i; auto.
          * rewrite revoke_lookup_Temp; auto.
            rewrite std_sta_update_multiple_lookup_same_i; auto.
            eapply Forall_forall in Htemprest; eauto. }
    assert (related_sts_priv_world W W''') as HWW''.
    { eapply related_sts_priv_trans_world with W''; auto.
      eapply related_sts_priv_trans_world with W'; auto.
      eapply related_sts_priv_trans_world;[apply revoke_related_sts_priv;auto|].
      rewrite /W'. eapply related_sts_priv_world_std_update_multiple.
      eapply Forall_forall. intros.
      eapply Forall_forall in Huninit; eauto.
      destruct Huninit. exists (Static {[x:=x0]}).
      split; auto. rewrite revoke_monotone_lookup_same'; auto.
      rewrite H1; auto. }
    
    (* We choose the r *)
    set r : gmap RegName Word :=
      <[PC     := inl 0%Z]>
      (<[r_stk := inr (URWLX, Local, stack_own_last, estk, stack_own_last)]>
      (<[r_t0  := inr (E, Local, a0, stack_own_last, stack_own_b)]>
      (<[r_adv := inr (p, Global, b, e, a')]>
       (create_gmap_default (list_difference all_registers [PC;r_stk;r_t0;r_adv]) (inl 0%Z))))).

    (* Now that the world has been set up, we want to apply the jmp or fail pattern of wadv *)
    iDestruct (jmp_or_fail_spec _ _ φ with "Hadv_val") as "Hadv_cont".
    
    (* jmp r_adv *)
    iDestruct (big_sepL2_length with "Hf2") as %Hrest_length; simpl in Hrest_length. 
    destruct rest0;[inversion Hrest0_length|].
    iPrologue rest1 Hrest_length "Hf2".
    apply contiguous_between_cons_inv_first in Hcont_rest1 as Heq. subst a8. 
    iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
      [apply jmp_i|apply Hfl|iCorrectPC s_last a_last|..].
    (* before applying the epilogue, we want to distinguish between a correct or incorrect resulting PC *)
    destruct (decide (isCorrectPC (updatePcPerm (inr (p, Global, b, e, a')))));
      [rewrite decide_True;auto|rewrite decide_False;auto]. 
    2: { iEpilogue "(HPC & _ & _)". iApply ("Hadv_cont" with "[Hφ $HPC]").
         iApply "Hφ". iIntros (Hcontr). done. }
    iDestruct "Hadv_cont" as (p0 g b0 e0 a11 Heq) "Hadv_cont". symmetry in Heq. simplify_eq.
    iDestruct ("Hadv_cont" $! r _ HWW'') as "Hadv_contW''". 
    iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".
    
    (* We close the invariant for the program *)
    iMod ("Hcls" with "[Hprog_done Hinstr Hprog $Hna Hscall Hreqglob Hprestack]") as "Hna". 
    { iNext. iDestruct "Hprog_done" as "(Hpush3 & Hpush2 & Hpush1 & Ha_first)".
      rewrite Heqapp. 
      iApply (big_sepL2_app with "Hreqglob [-]").
      iApply (big_sepL2_app with "Hprestack [-]").
      iFrame "Ha_first". rewrite Hrest_app.
      iFrame "Hpush1". iFrame "Hpush2". iFrame "Hpush3".
      iApply (big_sepL2_app with "Hscall [-]").
      iFrame.
    }

    assert (forall x, x ∈ region_addrs stack_own_last estk -> region_type_uninitialized W''' x) as HrestpwlU.
    { intros. rewrite /W'''. red.
      generalize (proj1 (Forall_forall _ _) H x ltac:(rewrite Hstksplit; eapply elem_of_app; eauto)); intros.
      destruct H1.
      - assert (x ∈ ltemprest) by (eapply elem_of_list_filter; split; auto).
        rewrite -(fst_zip ltemprest wsrest) in H2; [|revert Hlengthstackrest; clear; lia].
        eapply list_to_map_lookup_is_Some in H2. destruct H2.
        erewrite override_uninitializedW_lookup_some; eauto.
      - rewrite override_uninitializedW_lookup_nin.
        + assert (∃ w3 : Word, std (std_update_multiple (std (std_update_multiple W luninitsplit Revoked), (<[i:=encode false]> W.2.1, W.2.2)) (elements (dom (gset Addr) m_static1)) (Static m_static1)) !! x =  Some (Static {[x:=w3]})).
          { repeat rewrite std_sta_update_multiple_lookup_same_i; eauto.
            { red; intro. eapply elem_of_list_filter in H2. destruct H2.
              destruct (region_addrs_xor_elem_of x a0 stack_own_last estk).
              - revert Hspliteq Hsize. clear.
                rewrite /region_size; solve_addr.
              - rewrite Hstksplit. eapply elem_of_app; auto.
              - destruct H4; auto.
              - destruct H4; auto. }
            { rewrite lists_to_static_region_dom; auto.
              - generalize (elements_list_to_set _ Hdup1). intros.
                red; intros. eapply (elem_of_list_permutation_proper _ _ _ H2) in H3.
                eapply elem_of_app in H3. destruct H3.
                + destruct (region_addrs_xor_elem_of x a0 stack_own_last estk).
                  * revert Hspliteq Hsize. clear.
                    rewrite /region_size; solve_addr.
                  * rewrite Hstksplit. eapply elem_of_app; auto.
                  * destruct H4; auto.
                  * destruct H4; auto.
                + specialize (proj2 (Hiff x) ltac:(eapply elem_of_app; left; auto)) as HH.
                  destruct H1; congruence.
              - rewrite !app_length. f_equal; auto. } }
          rewrite revoke_monotone_lookup_same; auto.
          destruct H2; rewrite H2. auto.
        + red; intro. eapply elem_of_dom in H2. eapply list_to_map_lookup_is_Some in H2.
          rewrite fst_zip in H2; [|revert Hlengthstackrest; clear; lia].
          eapply elem_of_list_filter in H2. destruct H2.
          destruct H1; congruence. }

    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:= (match p with
                | E => inr (RX, Global, b, e, a')
                | _ => inr (p, Global, b, e, a')
                end)]> r))
      with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
    { iApply (registers_mapsto_resources with "[$Hr_gen] [$Hr_stk] [$Hr_t0] [$Hr_adv] [$HPC]").
      rewrite !dom_delete_L !dom_insert_L !dom_delete_L Hrmap_dom.
      rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
      f_equal. clear. set_solver. }
    (* r contrains all registers *)
    iAssert (full_map r) as "#full";[iApply r_full|].
    iSimpl in "Hadv_val".
    (* We are now ready to show that all registers point to a valid word *)
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W''' (r !r! r1))%I
      with "[-Hsts Hr Hmaps Hna Hφ]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
          [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_adv)); [by left|right;auto].  
      }
      - iIntros "%". contradiction.
      - assert (r !! r_stk = Some (inr (URWLX, Local, stack_own_last, estk, stack_own_last))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk !fixpoint_interp1_eq. 
        iIntros (_). 
        assert (Hmin1: min stack_own_last estk = stack_own_last).
        { revert Hsize Hspliteq. clear. rewrite /region_size; solve_addr. }
        iSimpl. rewrite !Hmin1. replace (max stack_own_last stack_own_last) with stack_own_last by (clear; solve_addr).
        rewrite (interp_weakening.region_addrs_empty stack_own_last stack_own_last); [|clear; solve_addr].
        rewrite big_sepL_nil.
        rewrite Hstksplit. iDestruct (big_sepL_app with "Hstackallrel") as "[Hstackallrel1 Hstackallrel2]". iSplitR; auto.
        iApply (big_sepL_impl with "Hstackallrel2").
        iAlways. iIntros. iExists RWLX. iSplit;auto. iSplit; auto. iPureIntro.
        rewrite /region_state_U_pwl. right.
        eapply HrestpwlU. eapply elem_of_list_lookup. eauto.
      - (* continuation *)
        iIntros (_).
        assert (r !! r_t0 = Some (inr (E, Local, a0, stack_own_last, stack_own_b))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 !fixpoint_interp1_eq. iSimpl. 
        (* prove continuation *)
        iAlways.
        iIntros (r' W3 Hrelated3).
        iNext.

        (* We start by asserting that the adversary stack is still temporary or uninitialized *)
        iAssert ([∗ list] a ∈ (region_addrs stack_own_last estk),
                 ⌜region_type_temporary W3 a \/ region_type_uninitialized W3 a⌝
                    ∗ rel a RWLX (λ Wv : WORLD * Word, ((fixpoint interp1) Wv.1) Wv.2)
                )%I as "#Hstack_adv_tmp".
        { iApply big_sepL_sep. iSplit.
          - (* W3 is a public future world of W''' and we know that everything is uninitialized in the range in W''' *)
            iApply big_sepL_forall. iPureIntro. simpl; intros.
            generalize (HrestpwlU x0 ltac:(eapply elem_of_list_lookup; eauto)).
            rewrite /region_type_uninitialized. intros [xx Hx0uninit].
            eapply region_state_U_pwl_monotone_same in Hx0uninit; eauto.
            destruct Hx0uninit; [left; auto|right; eauto].
          - rewrite Hstksplit. iDestruct (big_sepL_app with "Hstackallrel") as "[_ $]". }

        iDestruct (big_sepL_sep with "Hstack_adv_tmp") as "[Htemp _]". 
        iDestruct (big_sepL_forall with "Htemp") as %HtempW3. iClear "Htemp".
        
        (* we want to distinguish between the case where the local stack frame is Static (step through 
           continuation) and where the local stack frame is temporary (apply FTLR) *)
        assert (forall a, a ∈ region_addrs a0 stack_own_last ++ l' ->
                  (std W3) !! a = Some Temporary ∨
                  (std W3) !! a = Some (Static m_static1))
          as Hcases.
        { intros a'' Hin. apply or_comm,related_sts_pub_world_static with W''';auto.
          rewrite /W'''. rewrite override_uninitializedW_lookup_nin.
          - rewrite -std_update_multiple_revoke_commute; auto.
            eapply std_sta_update_multiple_lookup_in_i.
            rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
             rewrite elements_list_to_set;auto.
          - red; intro. eapply elem_of_dom in H0. eapply list_to_map_lookup_is_Some in H0.
            rewrite fst_zip in H0; [|revert Hlengthstackrest; clear; lia].
            eapply elem_of_app in Hin. destruct Hin.
            + eapply elem_of_list_filter in H0. destruct H0.
              destruct (region_addrs_xor_elem_of a'' a0 stack_own_last estk).
              * revert Hspliteq Hsize. clear.
                rewrite /region_size; solve_addr.
              * rewrite Hstksplit. eapply elem_of_app; auto.
              * destruct H3; auto.
              * destruct H3; auto.
            + eapply NoDup_app in Hdup. destruct Hdup as [A [B C] ].
              eapply B in H1. eapply H1.
              rewrite Hltempspliteq. eapply elem_of_app; auto. }
        assert (a0 ∈ region_addrs a0 stack_own_last ++ l') as Ha2in.
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
            iIntros (a''). rewrite /m_static1. 
            rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
            iIntros (Hin). apply elem_of_list_to_set in Hin. 
            pose proof (Hcases a'' Hin) as [Htemp'' | Hstatic].
            - rewrite /temporary. rewrite Htemp''. auto.
            - iDestruct (full_sts_static_all with "Hsts Hr") as %Hforall;[eauto|]. exfalso.
              assert (a0 ∈ dom (gset Addr) m_static1) as Hin'.
              { rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                apply elem_of_list_to_set. apply elem_of_app. left. apply elem_of_list_lookup. exists 0.
                apply region_addrs_of_contiguous_between in Hcont1 as <-. auto. }
              apply Hforall in Hin'. rewrite /static Hm_temp in Hin'. done. 
          }
          iDestruct (fundamental W3 r' RX Local a0 stack_own_last stack_own_b with "[] [] [-]") as "[_ Hcont]";[by iLeft| |iFrame "∗ #"|..].
          { iSimpl. 
            rewrite Hstksplit. iDestruct (big_sepL_app with "Hstackallrel") as "[H1 H2]".
            iApply (big_sepL_impl with "H1").
            iAlways. iIntros. iExists RWLX. iSplit;auto. iSplit; auto.
            iPureIntro. left.
            (* we assert that the region is all in state temporary *)
            assert (x ∈ dom (gset Addr) m_static1) as Hk'.
            { rewrite lists_to_static_region_dom; [|repeat rewrite app_length;rewrite Hlength_rest;auto].
              apply elem_of_list_to_set. apply elem_of_app.
              left. eapply elem_of_list_lookup; eauto. }
            apply Hm_frame_temp_all in Hk'. rewrite /temporary in Hk'.
            destruct (W3.1 !! x) eqn:Hsome;[subst;auto|inversion Hk']. }
          iFrame. 
        }
        
        (* Now we are in the case where m_static1 is still static. We will have to open the region and step through
           the continuation as usual. *)
        iSimpl. 
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hr & Hsts & Hna)". 
        iSplit; [auto|rewrite /interp_conf].
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

        iDestruct (region_has_static_addr_Forall with "[$Hr $Hsts]") as %HForall_static1; eauto.
        set ltempadv3 := (list_filter (region_type_temporary W3) (region_type_temporary_dec W3) (region_addrs stack_own_last estk)).
        iAssert (⌜Forall (λ a, W3.1 !! a = Some Temporary) ltempadv3⌝)%I as %Hstack_adv_tmp.
        { iPureIntro. eapply Forall_forall. intros. eapply elem_of_list_filter in H0.
          destruct H0; exact H0. }
        pose proof (extract_temps_split W3 ltempadv3) as [l'' [Hdup' Hiff'] ].
        { eapply NoDup_filter, NoDup_ListNoDup, region_addrs_NoDup. }
        { apply Hstack_adv_tmp. }
        
        (* we revoke W3, and keep a list of leftovers l'' *)
        iMod (monotone_revoke_keep_some _ l'' ltempadv3
                with "[Hstack_adv_tmp $Hr $Hsts]") as "(Hsts & Hr & Hrest' & Hstack_adv)".
        assumption. iSplit.
        { (* TODO: lemma for that? *)
          iApply big_sepL_forall. iPureIntro. intros n. simpl. intros x Hsome. apply Hiff'. apply elem_of_app; left.
          apply elem_of_list_lookup. eauto. }
        { iDestruct (big_sepL_submseteq with "Hstack_adv_tmp") as "Hstack_adv_tmp'".
          - instantiate (1 := ltempadv3).
            eapply NoDup_submseteq.
            + eapply NoDup_filter, NoDup_ListNoDup, region_addrs_NoDup.
            + eapply elem_of_list_filter.
          - iApply (big_sepL_impl with "Hstack_adv_tmp'").
            iAlways. iIntros (k x Hxin) "[_ $]". iPureIntro.
            assert (x ∈ ltempadv3) by (eapply elem_of_list_lookup; eauto).
            eapply elem_of_list_filter in H0. destruct H0; auto. }

        iDestruct (region_static_to_revoked with "[$Hr $Hsts]") as ">(Hsts & Hr & Hm_static1_resources & _)". eauto.

        (* finally we split up the static resources into the local stack frame and l' *)
        iAssert ([[a0,stack_own_last]] ↦ₐ[RWLX] [[l_frame]]
                ∗ [∗ list] a;w ∈ l';pws, ∃ p φ, rel a p φ ∗ a ↦ₐ[p] w)%I with "[Hm_static1_resources]" as "[Hframe Hl']".
         { rewrite /m_static1 /region_mapsto /static_resources.
          iAssert (([∗ list] y1;y2 ∈ region_addrs a0 stack_own_last;l_frame, y1 ↦ₐ[RWLX] y2)
                     ∗ ([∗ list] a11;w ∈ l';pws, ∃ p φ, rel a11 p φ ∗ a11 ↦ₐ[p] w))%I with "[-]" as "[H $]".
          { iDestruct (static_region_to_big_sepL2 _ _ (λ a w, ∃ p φ, rel a p φ ∗ a ↦ₐ[p] w)
                         with "[] Hm_static1_resources")%I as "Hm_static1_resources";
              [auto|repeat rewrite app_length;auto|auto|].
            iDestruct (big_sepL2_app' with "Hm_static1_resources") as "[Hframe $]";auto.
            (* rewrite Hstack_eq1. apply region_addrs_of_contiguous_between in Hcont1. rewrite Hcont1. *)
            apply withinBounds_le_addr in Hwb2.
            rewrite (region_addrs_split a0 stack_own_last estk);[|revert Hwb2;clear;solve_addr].
            iDestruct (big_sepL_app with "Hstackallrel") as "[Hframe' _]".
            iDestruct (big_sepL2_to_big_sepL_l with "Hframe'") as "Hframe+";eauto.
            iDestruct (big_sepL2_sep with "[$Hframe $Hframe+]") as "Hframe".
            iApply (big_sepL2_mono with "Hframe").
            iIntros (? ? ? ? ?) "HH". iDestruct "HH" as "[H1 H2]". iDestruct "H1" as (? ?) "[Hrel Hy]".
            iDestruct (rel_agree with "[$Hrel $H2]") as "[% _]". subst H2. iFrame.
          }
          iFrame.
        }

        (* we isolate the activation record from the frame *)
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha2 Hframe]"; [iContiguous_next Hcont1 0|..].
        { apply contiguous_between_middle_bounds with (i:=1) (ai:=a2) in Hcont1;auto. revert Hcont1;clear;solve_addr. }
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha3 Hframe]"; [iContiguous_next Hcont1 1|..].
        { apply contiguous_between_middle_bounds with (i:=2) (ai:=a3) in Hcont1;auto. revert Hcont1;clear;solve_addr. }
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha4 Hframe]"; [iContiguous_next Hcont1 2|..].
        { apply contiguous_between_middle_bounds with (i:=3) (ai:=stack_own_b) in Hcont1;auto.
          revert Hcont1;clear;solve_addr. }

        (* prepare the new stack value *)
        assert (exists stack_new, (stack_new + 1)%a = Some stack_own_end) as [stack_new Hstack_new].
        { revert Hstack_own_bound'. clear. intros H. destruct (stack_own_b + 5)%a eqn:Hsome;[|solve_addr].
          exists a. solve_addr. }

        (* step through instructions in activation record *)
        destruct rest1;[by inversion Hrest_length|].
        iApply (scallU_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
          [| |auto|auto|auto|iContiguous_next Hcont_rest1 0|apply Hstack_new|revert Hstack_own_bound Hstack_own_bound'; clear; solve_addr|..].
        { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb2.
          apply (contiguous_between_middle_bounds _ 3 stack_own_b) in Hcont1;[|auto]. revert Hwb2 Hcont1 Hmid. clear. solve_addr.
        }
        { simpl. revert Hsize Hspliteq Hstack_own_bound Hstack_own_bound'. clear. rewrite /region_size.
          rewrite andb_true_iff. 
          intros. assert ((stack_own_end + 1)%a = Some stack_own_last) by solve_addr.
          assert ((a0 + 9)%a = Some stack_own_end) by solve_addr.
          split.
          - revert H4; clear. intros. eapply (reflect_iff _ _ (leb_addr_spec _ _)). solve_addr.
          (* TODO: add reflect_iff trick to solve_addr *)
          - revert H4 H; clear. intros.
            (* TODO: move this *)
            assert (ltb_addr_spec: ∀ a1 a2 : Addr, reflect (a1 < a2)%a (a1 <? a2)%a).
            { intros. rewrite /ltb_addr /lt_addr.
              apply Z.ltb_spec0. }
            eapply (reflect_iff _ _ (ltb_addr_spec _ _)). solve_addr. }
        iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|].
        iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
        iDestruct "Hr_t1" as (wrt1) "Hr_t1".
        
        (* we can now step through the rest of the program *)
        (* to do that wee need to open the non atomic invariant of the program *)
        iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|]. 
        rewrite Heqapp Hrest_app. repeat rewrite app_assoc. repeat rewrite app_comm_cons. rewrite app_assoc.
        
        iDestruct (mapsto_decomposition _ _ pc_p' (take 85 (awkward_instrs f_a r_adv 40)) with "Hprog")
          as "[Hprog_done [Ha Hprog] ]".
        { simpl. repeat rewrite app_length /=.
          rewrite Hscall_length Hprepstack_length Hreqglob_length. auto. }
        iCombine "Ha" "Hprog_done" as "Hprog_done".
        (* Ustore r_stk 0 0 *)
        iApply (wp_bind (fill [SeqCtx])).
        destruct rest1 as [|astore rest1];[inversion Hf2_length|].
        (* we will need to split off the last element to adv *)
        assert (forall stack_own_b : Addr, (stack_own_b <= stack_own_end)%Z -> region_addrs stack_own_b stack_own_last = region_addrs stack_own_b stack_own_end ++ [stack_own_end]) as Hstack_localeq'.
        { intros stack_own_b' Hle. rewrite (region_addrs_decomposition _ stack_own_end).
          - repeat f_equiv. assert( (stack_own_end + 1)%a = Some stack_own_last) as ->;[|by rewrite /region_addrs /region_size Z.sub_diag /=].
            revert Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. 
          - revert Hle Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. 
        }
        
        rewrite /region_mapsto (Hstack_localeq' stack_own_b);[|revert Hstack_own_bound';clear;solve_addr].
        iDestruct (mapsto_decomposition _ _ _ [inl w_1; inl w_2_U; inl w_3; inl w_4a; inl w_4b_U;
                                               inr (pc_p, pc_g, pc_b, pc_e, s_last)] with "Hframe") as "[Hframe Hlast']".
        { rewrite region_addrs_length /=. rewrite /region_size. revert Hstack_own_bound'; clear. solve_addr. }
        assert ([stack_own_end] ++ region_addrs stack_own_last estk = region_addrs stack_own_end estk) as Hstack_localeq.
        { rewrite /region_addrs. apply withinBounds_le_addr in Hwb2 as [_ Hwb2].
          assert ((stack_own_end + 1)%a = Some stack_own_last) as Hincr;[revert Hstack_own_bound Hstack_own_bound';clear;solve_addr|].
          assert (region_size stack_own_end estk = S (region_size stack_own_last estk)) as ->.
          { revert Hstack_own_bound Hstack_own_bound' Hwb2; clear. rewrite /region_size. solve_addr. }
          simpl. f_equiv. rewrite Hincr /=. done.
        }
         assert (withinBounds (URWLX, Local, a0, estk, stack_own_end) = true) as Hwb3.
        { isWithinBounds. 
          - assert ((a0 + 3)%a = Some stack_own_b) as Hincr;[apply contiguous_between_incr_addr with (i := 3) (ai := stack_own_b) in Hcont1; auto|].
            revert Hstack_own_bound' Hincr. clear. solve_addr. 
          - apply withinBounds_le_addr in Hwb2 as [_ Hwb2]. revert Hstack_own_bound Hstack_own_bound' Hwb2. clear. solve_addr. 
        }
        iDestruct "Hprog" as "[Hi Hprog]".
        iDestruct "Hlast'" as "[Hstack_own_end _]".
        assert (stack_own_end + 1 = Some stack_own_last)%a as Hstack_own_end_incr.
        { revert Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. }         
        iApply (rules_StoreU_derived.wp_storeU_success_0_z with "[$HPC $Hi $Hr_stk $Hstack_own_end]");
          [apply storeU_z_z_i|apply Hfl|auto|iCorrectPC s_last a_last|iContiguous_next Hcont_rest1 1|
           auto|auto|apply Hstack_own_end_incr|..]. 
        iEpilogue "(HPC & Hinstr & Hr_stk & Hstack_own_end)".
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* sub r_t1 0 7 *)
        iPrologue rest1 Hrest_length "Hprog".
        iApply (wp_add_sub_lt_success_z_z with "[$HPC $Hr_t1 $Hinstr]");
          [apply sub_z_z_i|right;left;eauto|iContiguous_next Hcont_rest1 2|apply Hfl|iCorrectPC s_last a_last|..]. 
        iEpilogue "(HPC & Hinstr & Hr_t1)".
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* lea r_stk r_t1 *)
        iPrologue rest1 Hrest_length "Hprog".
        assert ((stack_own_last + (-8))%a = Some a3) as Hpop.
        { assert ((a3 + 1)%a = Some stack_own_b) as Ha0;[iContiguous_next Hcont1 2|].
          revert Ha0 Hstack_own_bound' Hstack_own_end_incr. clear. solve_addr. } 
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
          [apply lea_r_i|apply Hfl|iCorrectPC s_last a_last|iContiguous_next Hcont_rest1 3| |auto..].
        { simpl. assert ((a3 + 1)%a = Some stack_own_b) as Ha0;[iContiguous_next Hcont1 2|].
          revert Ha0 Hstack_own_bound' Hstack_new. clear.
          revert Hpop. instantiate (1 := stack_own_b). clear. intros. solve_addr. }
        { simpl; auto. revert Hstack_own_bound. clear. solve_addr. }
        iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_adv *)
        do 3 (destruct rest1; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a10;a11;a12] (a13::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a3 + (-1))%a = Some a2) as Hpop.
        { rewrite -(addr_add_assoc a2 _ 1);[apply addr_add_0|iContiguous_next Hcont1 1]. }
        assert (Hcont_rest2: contiguous_between (a0 :: a2 :: a3 :: stack_own_b :: stack_own) a0 stack_own_last).
        { eapply contiguous_between_of_region_addrs; eauto.
          revert Hspliteq. clear. rewrite /region_size. solve_addr. }
        iApply (popU_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_adv Ha4"];
          [split;[|split];iCorrectPC s_last a_last| apply Hfl| econstructor|iContiguous_bounds_withinBounds a0 stack_own_last|auto|
           iContiguous_next Hcont_rest1 4|iContiguous_next Hcont_rest1 5|iContiguous_next Hcont_rest1 6| |].
        { iContiguous_next Hcont_rest2 2. }
        iNext. iIntros "(HPC & Hpop & Hr_adv & Ha4 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_self *)
        do 3 (destruct rest1; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a13;a14;a15] (a16::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        iApply (popU_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_t0 Ha3"];
          [split;[|split];iCorrectPC s_last a_last| apply Hfl| econstructor|iContiguous_bounds_withinBounds a0 stack_own_last|auto|
           iContiguous_next Hcont_rest1 7|iContiguous_next Hcont_rest1 8|iContiguous_next Hcont_rest1 9|iContiguous_next Hcont_rest2 1|].
        iNext. iIntros "(HPC & Hpop & Hr_t0 & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_env *)
        do 3 (destruct rest1; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a16;a17;a18] (a19::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        iApply (popU_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Ha2"];
          [split;[|split];iCorrectPC s_last a_last| apply Hfl|econstructor|iContiguous_bounds_withinBounds a0 stack_own_last|auto|
           iContiguous_next Hcont_rest1 10|iContiguous_next Hcont_rest1 11|iContiguous_next Hcont_rest1 12|iContiguous_next Hcont_rest2 0|].
        iNext. iIntros "(HPC & Hpop & Hr_env & Hb_r & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* store r_env 1 *)
        iPrologue rest1 Hrest_length "Hprog".
        (* Storing 1 will always constitute a public future world of 
           std_update_multiple (revoke W3) dom(m_static1) Revoked *)
        iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, (* a23*) a20)
                       ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                       ∗ a19 (*a22*) ↦ₐ[pc_p'] store_z r_env 1
                       ∗ region (std_update_multiple (revoke (W3.1,(<[i:=encode true]> W3.2.1,W3.2.2)))
                                                     (elements (dom (gset Addr) m_static1)) Revoked)
                       ∗ sts_full_world (std_update_multiple (revoke (W3.1,(<[i:=encode true]> W3.2.1,W3.2.2)))
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
              [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC s_last a_last|
               iContiguous_next Hcont_rest1 13|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ". iFrame.            
            rewrite (insert_id _ i);[|auto].
            destruct W3 as [W3_std [W3_loc_pub W3_lo_priv] ]. iFrame.
            eauto. 
          - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
              [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC s_last a_last|
               iContiguous_next Hcont_rest1 13|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod (sts_update_loc _ _ _ true with "Hsts Hstate") as "[Hsts Hstate]".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ".
            rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel std_update_multiple_proj_eq.
            iFrame. 
            iSplitL;[|eauto]. iApply (region_monotone with "[] [] Hr").
            + iPureIntro. rewrite /revoke /std /loc /=. erewrite std_update_multiple_std_sta_eq. eauto. 
            + iPureIntro. apply std_update_mutiple_related_monotone.
              split;[apply related_sts_std_pub_refl|].
              rewrite /= /loc. apply related_pub_local_1 with false; auto.
        }
        iApply "Hstore_step". iNext. iIntros "(HPC & Hr_env & Hinstr & Hr & Hsts & #HW3lookup)".
        iDestruct "HW3lookup" as %[HW3lookup Hw3rel]. 
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* push r_stk r_env *)
        (destruct rest1;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a20] (a21::rest1) with "Hprog") as "[Hpush Hprog]";[simpl;auto|].
        iDestruct "Hpush" as "[Hpush _]".
        iApply (pushU_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Hb_r"];
          [iCorrectPC s_last a_last|apply Hfl|econstructor|auto|iContiguous_next Hcont_rest1 14|iContiguous_next Hcont_rest2 0|auto|..].
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
        (* push r_stk r_self *)
        (destruct rest1;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a21] (a22::rest1) with "Hprog") as "[Hpush Hprog]";[simpl;auto|].
        iDestruct "Hpush" as "[Hpush _]".
        iApply (pushU_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_t0 Ha3"];
          [iCorrectPC s_last a_last|apply Hfl|econstructor|iContiguous_bounds_withinBounds a0 stack_own_last|iContiguous_next Hcont_rest1 15|..]. iContiguous_next Hcont_rest2 1.
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done". 
        (* SECOND SCALL *)

        (* we now want to extract the final element of the local stack, which will now be handed off to the adversary *)
        (iDestruct (big_sepL_sep with "Hstack_adv") as "[Hstack_adv Hstack_adv_revoked]").
        (iDestruct (big_sepL_sep with "Hstack_adv") as "[Hstack_adv _]").
        iAssert (∃ ws_own : list Word, [[a3,stack_own_end]]↦ₐ[RWLX][[ws_own]])%I with "[Hframe Ha4]" as (ws_own'') "Hstack_own".
        { iExists ((inr (p, Global, b, e, a')) :: _). rewrite /region_mapsto.
          assert ([a3] ++ region_addrs stack_own_b stack_own_end = region_addrs a3 stack_own_end) as <-.
          { rewrite /region_addrs.
            assert ((a3 + 1)%a = Some stack_own_b) as Hincr;[iContiguous_next Hcont1 2|].
            assert (region_size a3 stack_own_end = S (region_size stack_own_b stack_own_end)) as ->.
            { revert Hstack_own_bound' Hincr; clear. rewrite /region_size. solve_addr. }
            simpl. f_equiv. rewrite Hincr /=. done. 
          }
          iApply (mapsto_decomposition [a3] _ _ [inr (p, Global, b, e, a')]); [auto|]. iFrame. done.
        }
        (* prepare for scall *)
        (* split the program into the scall_prologue and the rest *)
        assert (contiguous_between (a22 :: rest1) a22 a_last) as Hcont_weak.
        { repeat (inversion Hcont_rest1 as [|????? Hcont_rest1']; subst; auto; clear Hcont_rest1; rename Hcont_rest1' into Hcont_rest1). }

        iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue1 rest2 s_last1)
                                                                       "(Hscall & Hprog & #Hcont)"; [eauto|..].
        clear Hcont_weak.
        rename Hcont_rest2 into Hcont_rest2'.
        iDestruct "Hcont" as %(Hcont_scall1 & Hcont_rest2 & Hrest_app1 & Hlink2). subst.
        iDestruct (big_sepL2_length with "Hscall") as %Hscall_length1. simpl in Hscall_length1.
        destruct scall_prologue1 as [|scall_prologue_first1 scall_prologue1];[inversion Hscall_length1|].
        assert (scall_prologue_first1 = a22) as <-;[inversion Hrest_app1;auto|].
        (* some important element of the stack *)
        assert ((a3 + 7)%a = Some stack_own_end) as Hstack_own_bound1.
        { assert ((a3 + 1)%a = Some stack_own_b) as Ha4;[iContiguous_next Hcont1 2|].
          revert Hstack_own_bound Hstack_own_bound' Ha4. clear. solve_addr. }
        assert ((a3 + 6)%a = Some stack_new) as Hstack_own_bound1'.
        { revert Hstack_own_bound1 Hstack_new. clear. solve_addr. }
        assert (scall_prologue_first1 < s_last1)%a as Hcontlt1.
        { revert Hscall_length1 Hlink2. clear. solve_addr. }
        assert (s_last <= scall_prologue_first1)%a as Hcontge1.
        { apply region_addrs_of_contiguous_between in Hcont_scall. subst. revert Hscall_length1 Hcont_rest1 Hcontlt1.  clear =>Hscall_length Hf2 Hcontlt.
          apply contiguous_between_middle_bounds with (i := 16) (ai := scall_prologue_first1) in Hf2;[solve_addr|auto].
        }
       
        (* we can now invoke the stack call prologue *)
        iDestruct (big_sepM_insert _ _ r_t1 with "[$Hmreg' $Hr_t1]") as "Hmreg'".
          repeat (rewrite lookup_delete_ne;[|done]). by rewrite lookup_delete.
          repeat (rewrite -(delete_insert_ne _ _ r_t1);[|done]).
          rewrite insert_delete.
        iDestruct (big_sepM_insert _ _ r_t0 with "[$Hmreg' $Hr_self]") as "Hmreg'".
          rewrite lookup_delete_ne; [|done]. by rewrite lookup_delete.
          rewrite -delete_insert_ne;[|done]. rewrite insert_delete.
        iDestruct (big_sepM_insert _ _ r_env with "[$Hmreg' $Hr_env]") as "Hmreg'".
          by rewrite lookup_delete. rewrite insert_delete.
        iAssert (⌜dom (gset RegName) r' = all_registers_s⌝)%I as %Hdom_r'.
        { iDestruct "Hfull'" as %Hfull'. iPureIntro.
          apply (anti_symm _); [apply all_registers_subseteq|]. rewrite elem_of_subseteq.
          intros x _. rewrite -elem_of_gmap_dom. apply Hfull'. }
        iApply (scallU_prologue_spec with "[- $HPC $Hr_stk $Hmreg' $Hscall $Hstack_own]");
          [| |apply Hwb3| |apply Hcont_scall1|apply Hfl|
           iNotElemOfList| iContiguous_next Hcont1 2|apply Hstack_own_bound1'|apply Hstack_own_bound1|
           | done |..].
        { assert (s_last1 <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest2|].
          intros mid Hmid. apply isCorrectPC_inrange with link0 a_last; auto.
          revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid. clear; intros. split; solve_addr. }
        { iContiguous_bounds_withinBounds a0 stack_own_last. }
        { clear. solve_addr. }
        { repeat rewrite ?dom_insert_L ?dom_delete_L. rewrite Hdom_r'.
          rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
          f_equal. clear. set_solver. }
        { assert (5 + 40 = 45)%Z as ->;[done|]. rewrite Hscall_length1 in Hlink2. done. }
        iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hscall)".
        iDestruct (big_sepL2_length with "Hprog") as %Hrest_length1. simpl in Hrest_length1.
        assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last1 a_last) as Hvpc2.
        { intros mid Hmid. assert (link0 <= s_last1)%a as Hle.
          { apply contiguous_between_bounds in Hcont_scall1.
            apply contiguous_between_bounds in Hcont_scall.
            revert Hcont_scall Hcont_scall1 Hcontge1 Hcontge;clear. solve_addr.
          } 
          apply isCorrectPC_inrange with link0 a_last; auto.
          revert Hmid Hle. clear. solve_addr. }
        (* jmp r_adv *)
        destruct rest2;[inversion Hrest_length1|]. 
        iPrologue rest2 Hrest_length1 "Hprog". apply contiguous_between_cons_inv_first in Hcont_rest2 as Heq. subst s_last1.
        (* we separate the points to chunk from the persistent parts of the leftovers l'' *)
        iDestruct (temp_resources_split with "Hrest'") as (pws') "[#Hrest_valid' [#Hrev Hrest']]".
        iDestruct "Hrev" as %Hrev'.
        
        (* Allocate a static region to hold our frame *)

        (* first, put together again the resources for the frame *)

        iDestruct (region_mapsto_cons with "[$Ha3 $Hstack_own]") as "Hstack_own";
          [iContiguous_next Hcont1 1|..].
        { revert Hstack_own_bound1. clear; solve_addr. }
        iDestruct (region_mapsto_cons with "[$Hb_r $Hstack_own]") as "Hstack_own";
          [iContiguous_next Hcont1 0|..].
        { have: (a2 + 1 = Some a3)%a. by iContiguous_next Hcont1 1. revert Hstack_own_bound1.
          clear; solve_addr. }

        (* we'll need that later to reason on the fact that the [zip] in the definition of
           m_frame indeed fully uses both lists *)
        iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_stack_own2.
        iDestruct (big_sepL2_length with "Hrest'") as %Hlength_rest''.

        match goal with |- context [ [[a0,stack_own_end]]↦ₐ[RWLX][[ ?instrs ]]%I ] =>
          set l_frame2 := instrs
        end.
        set static2_addrs := region_addrs a0 stack_own_end ++ l' ++ l''.
        set static2_instrs := l_frame2 ++ pws ++ pws'.
        set m_static2 := lists_to_static_region static2_addrs static2_instrs.

        rewrite std_update_multiple_revoke_commute;auto.

        (* fact: l', l'', [a2,stack_own_end] and [stack_own_end, e_r] are all
           disjoint. We will need these facts for later. We can derive them now
           from separation logic and the fact that pointsto (with non-O perm)
           are exclusive... *)

        set static_res := (λ a w, ∃ p φ, a ↦ₐ<p> w ∗ ⌜∀Wv, Persistent (φ Wv)⌝ ∗ rel a p φ)%I.

        (* static_res includes a non-O pointsto, therefore it is exclusive *)
        iAssert (⌜∀ a w1 w2, static_res a w1 -∗ static_res a w2 -∗ False⌝)%I as %Hstatic_res_excl.
        { iIntros (? ? ?) "". iPureIntro. iIntros "H1 H2". iDestruct "H1" as (? ?) "[[? %] _]".
          iDestruct "H2" as (? ?) "[[? %] _]". iApply (cap_duplicate_false with "[$]"). split; assumption. }
        
        iAssert ([∗ list] a;w ∈ l';pws, static_res a w)%I with "[Hl']" as "Hl'".
        { iDestruct (big_sepL2_sep with "[Hrest_valid $Hl']") as "Hl'". by iApply "Hrest_valid".
          iApply (big_sepL2_mono with "Hl'"). cbn. iIntros (k a'' pw ? ?) "[H1 H2]".
          iDestruct "H2" as (? ? ?) "(? & ? & #Hrel' & ?)".
          iDestruct "H1" as (? ?) "[#Hrel ?]".
          iDestruct (rel_agree _ H2 H5 with "[$Hrel $Hrel']") as "[% _]";subst H2. 
          iExists _,_. iFrame. eauto. }
        
        iAssert ([∗ list] a;w ∈ l'';pws', static_res a w)%I with "[Hrest']" as "Hrest'".
        { iDestruct (big_sepL2_sep with "[Hrest_valid' $Hrest']") as "Hrest'". by iApply "Hrest_valid'".
          iApply (big_sepL2_mono with "Hrest'"). cbn. iIntros (k a'' pw ? ?) "[H1 H2]".
          iDestruct "H2" as (? ? ?) "(? & ? & #Hrel' & ?)".
          iDestruct "H1" as (? ?) "[? #Hrel]".
          iDestruct (rel_agree _ H2 H5 with "[$Hrel $Hrel']") as "[% _]";subst H2.
          iExists _. iFrame. eauto. }

        assert (a0 <= stack_own_end ∧ stack_own_end <= estk)%a.
        { move: (withinBounds_le_addr _ _ _ _ _ Hwb3). clear; solve_addr. }

        iAssert ([∗ list] a;w ∈ (region_addrs a0 stack_own_end);l_frame2, static_res a w)%I
          with "[Hstack_own]" as "Hstack_own".
        { rewrite (region_addrs_split a0 stack_own_end estk) //.
          iDestruct (big_sepL_app with "Hstackallrel") as "[Hstack_val' _]".
          iDestruct (big_sepL2_sep with "[Hstack_val' $Hstack_own]") as "Hstack_own".
          { iApply big_sepL2_to_big_sepL_l. auto. iApply "Hstack_val'". }
          iApply (big_sepL2_mono with "Hstack_own"). iIntros (? ? ? ? ?) "(? & ?)". unfold static_res.
          iExists _,_. rewrite /read_write_cond. iFrame. iSplitR; [iPureIntro; congruence|]. iPureIntro.
          intro; apply interp_persistent. }

        iDestruct (big_sepL2_app with "Hl' Hrest'") as "Hl'_rest'".

        (* now that we have privately updated our resources, we can close the region invariant for the adv stack *)
        assert (list.last (a0 :: a2 :: a3 :: stack_own_b :: stack_own) = Some stack_own_end) as Hlast.
        { apply contiguous_between_link_last with a0 stack_own_last; [auto|apply gt_Sn_O|].
          revert Hstack_own_bound Hstack_own_bound'; clear. solve_addr. }
        
        (* we will need that later *)
        iAssert (⌜NoDup (region_addrs a0 estk ++ l' ++ l'')⌝)%I as %Hstack_l'_l''_NoDup.
        { rewrite NoDup_app. repeat iSplit.
          - iPureIntro. eapply NoDup_ListNoDup, region_addrs_NoDup.
          - rewrite (region_addrs_split a0 stack_own_end estk); auto.
            iIntros (x Hin1 Hin2). eapply elem_of_app in Hin1.
            destruct Hin1 as [Hin1|Hin1].
            + eapply elem_of_list_lookup_1 in Hin1. destruct Hin1 as [i1 Hin1].
              eapply elem_of_list_lookup_1 in Hin2. destruct Hin2 as [i2 Hin2].
              specialize (lookup_lt_is_Some_1 _ i1 ltac:(eauto)) as Hli1.
              specialize (lookup_lt_is_Some_1 _ i2 ltac:(eauto)) as Hli2.
              rewrite app_length Hlength_rest'' Hlength_rest -app_length in Hli2.
              eapply lookup_lt_is_Some_2 in Hli2. destruct Hli2 as [x2 Hin2'].
              iDestruct (big_sepL2_lookup with "Hl'_rest'") as "H2"; eauto.
              assert (length (region_addrs a0 stack_own_end) = 9).
              { revert Hspliteq Hstack_own_bound Hstack_own_bound'; clear.
                rewrite region_addrs_length /region_size. 
                solve_addr. }
              replace 9 with (length l_frame2) in H1 by reflexivity.
              rewrite H1 in Hli1.
              eapply lookup_lt_is_Some_2 in Hli1. destruct Hli1 as [x1 Hin1'].
              iDestruct (big_sepL2_lookup with "Hstack_own") as "H1"; eauto.
              iApply (Hstatic_res_excl with "H1 H2").
            + iPureIntro. eapply elem_of_app in Hin2. destruct Hin2 as [Hin2|Hin2].
              * erewrite Forall_forall in H. specialize (H x ltac:(rewrite (region_addrs_split a0 stack_own_end estk); auto; eapply elem_of_app; auto)) as [HH | HH].
                { eapply NoDup_app in Hdup. destruct Hdup as [_ [Hdup _] ].
                  eapply Hdup in Hin2. eapply Hin2.
                  eapply elem_of_list_filter. split; auto.
                  rewrite (region_addrs_split a0 stack_own_end estk); auto.
                  eapply elem_of_app; auto. }
                { generalize (proj2 (Hiff x) ltac:(eapply elem_of_app; auto)).
                  destruct HH; congruence. }
              * rewrite -Hstack_localeq in Hin1. eapply elem_of_app in Hin1.
                destruct Hin1 as [Hin1 | Hin1].
                { eapply elem_of_list_singleton in Hin1. subst x.
                  generalize (proj2 (Hiff' stack_own_end) ltac:(eapply elem_of_app; auto)).
                  intros. assert (std W3 !! stack_own_end = Some (Static m_static1)).
                  { eapply (proj1 (Forall_forall _ _) HForall_static1).
                    rewrite /m_static1 lists_to_static_region_dom.
                    - generalize (elements_list_to_set _ Hdup1). intros.
                      eapply (elem_of_list_permutation_proper _ _ _ H2).
                      eapply elem_of_app. left.
                      rewrite Heqq. rewrite last_lookup in Hlast.
                      eapply elem_of_list_lookup_2. eauto.
                    - rewrite !app_length. f_equal; auto. }
                  congruence. }
                { specialize (elem_of_list_lookup_1 _ _ Hin1) as Hin1'. destruct Hin1' as [i1 Hin1'].
                  eapply HtempW3 in Hin1'. destruct Hin1'.
                  - eapply NoDup_app in Hdup'. destruct Hdup' as [_ [Hdup' _] ].
                    eapply Hdup' in Hin2. eapply Hin2.
                    eapply elem_of_list_filter. split; auto.
                  - generalize (proj2 (Hiff' x) ltac:(eapply elem_of_app; auto)).
                    destruct H1; congruence. }
          - iApply (NoDup_of_sepL2_exclusive with "[] [Hstack_own Hstack_adv Hl'_rest']").
            2: { eauto. }
            iIntros (? ? ?). iApply Hstatic_res_excl. }
        
        (* Allocate the static region; for that we only need the part of Hstack we own *)
        iAssert ([∗ list] a;w ∈ static2_addrs;static2_instrs, static_res a w)%I
          with "[Hstack_own Hl'_rest']" as "Hstatic".
        { iApply (big_sepL2_app with "Hstack_own Hl'_rest'"). }

        iAssert (⌜NoDup static2_addrs⌝)%I as %Hstatic2_addrs_NoDup.
        { iApply (NoDup_of_sepL2_exclusive with "[] Hstatic").
          iIntros (? ? ?) "". iApply Hstatic_res_excl. }

        iDestruct (region_revoked_to_static _ m_static2 with "[$Hsts $Hr Hstatic]") as ">[Hsts Hr]".
        { iApply (big_sepL2_to_static_region with "[] Hstatic"). assumption.
          iModIntro. iIntros (? ? pw ? ?) "H". iDestruct "H" as (? ?) "([? ?] & ? & ?)".
          iExists _,_. iFrame. }

        rewrite -std_update_multiple_revoke_commute;auto.

        (* To make some of the future proofs easier, let's make certain assertions about addresses in adv frame *)
        assert (∀ a, a ∈ region_addrs stack_own_end estk -> a ∉ elements (dom (gset Addr) m_static2)) as Hnin2.
        { rewrite lists_to_static_region_dom.
          2: { repeat rewrite app_length. rewrite Hlength_rest Hlength_rest''. auto. }
          intros a'' Ha'. 
          rewrite elements_list_to_set;auto.
          assert (a'' ∈ region_addrs a0 estk) as Hin'.
          { rewrite -Hstack_localeq in Ha'. rewrite Hstksplit.
            apply elem_of_app in Ha' as [Hl | Hr].
            - apply elem_of_list_singleton in Hl. subst.
              apply elem_of_app; left. apply elem_of_list_lookup. exists (10 - 1).
              rewrite -(region_addrs_of_contiguous_between _ _ _ Hcont_rest2').
              rewrite -Hlength_own -last_lookup; auto.
            - by apply elem_of_app; right. 
          }
          apply not_elem_of_app. split.
          - apply region_addrs_xor_elem_of with (c:=stack_own_end) in Hin' as [ [Hin' Hnin] | [Hin' Hnin] ];auto.
            eapply withinBounds_le_addr. apply Hwb3. 
          - rewrite NoDup_app in Hstack_l'_l''_NoDup |- *. intros (_ & HH & _). by apply HH.
        }
        assert (∀ a, a ∈ region_addrs stack_own_last estk -> a ∉ elements (dom (gset Addr) m_static1)) as Hnin1.
        { rewrite lists_to_static_region_dom.
          2: { repeat rewrite app_length. rewrite Hlength_rest . auto. }
          intros a'' Ha'. 
          rewrite elements_list_to_set;auto.
          assert (a'' ∈ region_addrs a0 estk) as Hin'.
          { rewrite Hstksplit. apply elem_of_app;right. auto. } 
          apply not_elem_of_app. split.
          - apply region_addrs_xor_elem_of with (c:=stack_own_last) in Hin' as [ [Hin' Hnin] | [Hin' Hnin] ];auto.
            eapply withinBounds_le_addr. apply Hwb2.
          - rewrite NoDup_app in Hstack_l'_l''_NoDup |- *. intros (_ & HH & _).
            by eapply (not_elem_of_app l' l''), HH.
        }
        
        match goal with |- context [ region ?W ] => set W4 := W end.

        (* finally we can now close the region: a_last' will be in state revoked in revoke(W3) *)
        assert (∀ x, x ∈ ([stack_own_end] ++ ltempadv3) ->
                       W4.1 !! x = Some Revoked) as Hlookup_revoked.
        { intros x Hsome.
          rewrite std_sta_update_multiple_lookup_same_i;auto.
          2: { apply Hnin2. rewrite -Hstack_localeq. eapply elem_of_app in Hsome.
               eapply elem_of_app. destruct Hsome; [left; auto| right].
               eapply elem_of_list_filter. eauto. }
          apply elem_of_app in Hsome as [Hl | Hr].
          + apply elem_of_list_singleton in Hl;subst.
            apply std_sta_update_multiple_lookup_in_i.
            rewrite lists_to_static_region_dom;[|repeat rewrite app_length;auto].
            rewrite elements_list_to_set;auto. 
            apply elem_of_app;left. apply region_addrs_of_contiguous_between in Hcont1 as <-. 
            apply elem_of_list_lookup. exists (10 - 1). rewrite -Hlength_own -last_lookup; auto.
          + rewrite std_sta_update_multiple_lookup_same_i;auto. 
            apply elem_of_list_lookup in Hr as [k Hk].
            apply revoke_lookup_Temp. simpl.
            assert (x ∈ ltempadv3) as Hin%elem_of_list_filter;[apply elem_of_list_lookup;eauto|].
            destruct Hin as [Htemp3 _];auto.  
            apply Hnin1. eapply elem_of_list_filter. eauto.
        }
        
        iDestruct (region_addrs_exists with "Hstack_adv") as (wsadv3) "Hstack_adv".
        iDestruct (big_sepL2_length with "Hstack_adv") as %Hlengthstackadv.
        (* We remember the fact that the words in m_uninit2 are valid *)
        iDestruct (big_sepL2_mono with "Hstack_adv") as "Hstack_adv".
        { iIntros (k y1 y2 Hy1 Hy2) "H". repeat rewrite bi.sep_assoc. iExact "H". }
        iDestruct (big_sepL2_sep with "Hstack_adv") as "[Hstack_adv #Hold_temps_valid3]". 
        
        set m_uninit2 : gmap Addr Word := list_to_map (zip ([stack_own_end] ++ ltempadv3) ([inl 0%Z] ++ wsadv3)).

        (* a useful lemma about m_uninit2 *)
        assert (forall a, a ∈ dom (gset Addr) m_uninit2 -> a ∈ region_addrs stack_own_end estk) as Hm_uninit2_in.
        { intros x Hx%elem_of_gmap_dom%list_to_map_lookup_is_Some.
          rewrite fst_zip in Hx;[|rewrite /= Hlengthstackadv;clear;lia].
          apply withinBounds_le_addr in Hwb3.
          apply elem_of_cons in Hx as [-> | Hx%elem_of_list_filter].
          - apply elem_of_list_lookup. exists 0. apply region_addrs_first. revert Hwb3;clear;solve_addr.
          - destruct Hx as [_ Hx].
            rewrite (region_addrs_split _ stack_own_last);
              [apply elem_of_app;by right|revert Hstack_own_end_incr Hwb3;clear;solve_addr]. 
        }

        iMod (region_revoked_to_uninitialized _ m_uninit2 with "[Hsts Hr Hstack_adv Hstack_own_end]") as "[Hsts Hr]".
        { rewrite /W4 !std_update_multiple_revoke_commute; auto.
          iFrame "Hsts Hr".
          iApply big_sepL2_to_big_sepM.
          { apply NoDup_app in Hdup' as (_ & _ & Hdup'). apply NoDup_app.
            split;[constructor;[apply not_elem_of_nil|apply NoDup_nil;auto]|].
            split;[|auto]. intros x Hx%elem_of_list_singleton. rewrite Hx.
            intros Hcontr%elem_of_list_filter. destruct Hcontr as [_ Hcontr].
            assert (stack_own_end ∉ region_addrs stack_own_last estk);[|done]. 
            apply region_addrs_not_elem_of. revert Hstack_own_end_incr;clear;solve_addr. 
          }
          iApply (big_sepL2_app with "[Hstack_own_end]").
          - iSimpl. iSplit;[|auto]. iExists RWLX,(λ Wv, interp Wv.1 Wv.2). iFrame.
            iSplit;[iPureIntro;intros [? ?];apply interp_persistent|]. iSplit;[auto|].
            assert (stack_own_end ∈ region_addrs a0 estk) as Hin.
            { apply withinBounds_le_addr in Hwb3.
              rewrite (region_addrs_split _ stack_own_end);[|revert Hwb3;clear;solve_addr].
              apply elem_of_app;right. apply elem_of_list_lookup. exists 0.
              apply region_addrs_first. revert Hwb3;clear;solve_addr. }
            iDestruct (big_sepL_elem_of with "Hstackallrel") as "Hstack_own_end_rel";[apply Hin|].
            iFrame "Hstack_own_end_rel".
          - iAssert ([∗ list] y1;y2 ∈ ltempadv3;wsadv3, ((⌜RWLX ≠ O⌝ ∗ y1 ↦ₐ[RWLX] y2)
                                     ∗ future_pub_mono (λ Wv : WORLD * Word, ((fixpoint interp1) Wv.1) Wv.2) y2)
                                     ∗ rel y1 RWLX (λ Wv, interp Wv.1 Wv.2))%I with "[Hstack_adv]" as "Hstack_adv".
            { iApply big_sepL2_sep. iSplitL. iFrame.
              iApply big_sepL2_to_big_sepL_l;auto.
              iApply big_sepL_forall. iIntros (k x Hx).
              assert (x ∈ region_addrs stack_own_last estk) as Hin.
              { assert (x ∈ ltempadv3) as Hin%elem_of_list_filter;[apply elem_of_list_lookup;eauto|].
                destruct Hin as [_ Hin]. auto. }
              iDestruct (big_sepL_elem_of with "Hstack_adv_tmp") as "[_ $]";apply Hin. 
            }
            iApply (big_sepL2_mono with "Hstack_adv").
            iIntros (k y1 y2 Hy1 Hy2) "(((? & ?) & ?) & ?)". 
            iExists _,_. iFrame. iPureIntro; intros [? ?]; apply interp_persistent. 
        }
        
        (* The resulting world is a private future world of W3 *)
        iSimpl in "Hsts".
        match goal with |- context [ region ?W ] => set W5 := W end.

        assert (Forall (λ a : Addr, ∃ ρ, (std W4) !! a = Some ρ /\ ρ <> Permanent) (elements (dom (gset Addr) m_uninit2)))
          as Hm_uninit2_state.
        { apply Forall_forall. intros x Hx%elem_of_elements%Hm_uninit2_in. 
          apply withinBounds_le_addr in Hwb3.
          rewrite (region_addrs_split _ stack_own_last) in Hx;[|revert Hstack_own_end_incr Hwb3;clear;solve_addr].
          apply elem_of_app in Hx as [Hx | Hx].
          - rewrite std_sta_update_multiple_lookup_same_i;[eauto|].
            2: { apply Hnin2. rewrite (region_addrs_split _ stack_own_last);
                                [apply elem_of_app;by left|revert Hstack_own_end_incr Hwb3;clear;solve_addr]. }
            rewrite std_sta_update_multiple_lookup_in_i;[eauto|].
            rewrite lists_to_static_region_dom;
              [|repeat rewrite app_length;by rewrite Hlength_stack_own1 Hlength_rest /=]. 
            rewrite elements_list_to_set;auto. apply elem_of_app. left.
            rewrite (region_addrs_split _ stack_own_end);[|revert Hstack_own_end_incr Hwb3;clear;solve_addr].
            apply elem_of_app;by right.
          - rewrite std_sta_update_multiple_lookup_same_i;[eauto|].
            2: { apply Hnin2. rewrite (region_addrs_split _ stack_own_last);
                                [apply elem_of_app;by right|revert Hstack_own_end_incr Hwb3;clear;solve_addr]. }
            rewrite std_sta_update_multiple_lookup_same_i;[eauto|].
            2: { apply Hnin1. auto. }
            apply elem_of_list_lookup in Hx as [k Hx].
            apply HtempW3 in Hx as [Htempx | [? Huninitx] ].
            + exists Revoked. rewrite revoke_lookup_Temp;auto.
            + exists (Static {[x:=x0]}). rewrite revoke_monotone_lookup_same;auto. rewrite Huninitx. auto. 
        }

        assert (forall x, x ∈ elements (dom (gset Addr) m_static2) -> x ∉ elements (dom (gset Addr) m_static1) -> x ∈ l'')
          as Hl''.
        { intros x Hx n.
          rewrite /m_static1 in n. rewrite /m_static2 /static2_addrs in Hx.
          rewrite lists_to_static_region_dom in Hx;
            [|repeat rewrite app_length;by rewrite Hlength_stack_own2 Hlength_rest Hlength_rest'' /=].
          revert Hx; rewrite elements_list_to_set;[intros Hx|auto].
          revert Hx; repeat rewrite elem_of_app; intros Hx.
          rewrite lists_to_static_region_dom in n;
            [|repeat rewrite app_length;by rewrite Hlength_stack_own1 Hlength_rest /=].
          revert n; rewrite elements_list_to_set;[intros n|auto].
          apply not_elem_of_app in n as [Hn1 Hn2].
          apply withinBounds_le_addr in Hwb3.
          rewrite (region_addrs_split _ stack_own_end) in Hn1;[|revert Hstack_own_end_incr Hwb3;clear;solve_addr]. 
          apply not_elem_of_app in Hn1 as [Hn1 Hn1']. 
          destruct Hx as [? | [? | ?] ];done. 
        }
        
        assert (related_sts_priv_world W3 W5) as Hrelated5.
        { apply related_sts_priv_trans_world with W4;
            [|rewrite /W5;repeat rewrite -std_update_multiple_revoke_commute;auto;
              apply related_sts_priv_world_override_uninitializedW;auto].
          
          eapply related_sts_priv_trans_world;[|apply related_sts_priv_world_static2].
          2: { apply Forall_forall. intros x Hx.
               destruct (decide (x ∈ elements (dom (gset Addr) m_static1))). 
               - rewrite std_sta_update_multiple_lookup_in_i;eauto.
               - rewrite std_sta_update_multiple_lookup_same_i;eauto.
                 assert (x ∈ l'' ++ ltempadv3);[apply elem_of_app;left;apply Hl'';auto|].
                 apply Hiff' in H1. rewrite revoke_lookup_Temp;eauto.
          }

          eapply related_sts_priv_trans_world;[|apply related_sts_priv_world_std_update_multiple];auto.
          2: { apply Forall_forall. intros x Hx%elem_of_elements.
               apply Hall_static in Hx. rewrite /static in Hx.
               destruct (W3.1 !! x) eqn:Hsome;[rewrite Hx in Hsome|done]. 
               rewrite revoke_monotone_lookup_same;eauto. rewrite Hsome. auto.
          }

          eapply related_sts_priv_trans_world;[|apply revoke_related_sts_priv];auto.
          apply related_sts_pub_priv_world. destruct HW3lookup as [y Hy].
          split;[apply related_sts_std_pub_refl|simpl;eapply related_pub_local_1; eauto].
        }

        (* we can now finally monotonically update the region to match the new sts collection *)
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hreli.
        (* We choose the r *)
        set r2 : gmap RegName Word :=
          <[PC    := inl 0%Z]>
          (<[r_stk := inr (URWLX, Local, stack_own_end, estk, stack_own_end)]>
          (<[r_t0  := inr (E, Local, a0, stack_own_end, a3)]>
          (<[r_adv := inr (p, Global, b, e, a')]>
          (create_gmap_default
             (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z))))).

        (* we set up the expression relation of the jump *)
        assert (related_sts_priv_world W W5) as Hrelated5'.
        { eapply related_sts_priv_trans_world;[|apply Hrelated5]. 
            by eapply related_sts_priv_pub_trans_world;[|apply Hrelated3]. }
        iDestruct ("Hadv_cont" $! r2 W5 Hrelated5') as "Hadv_contW5".     
        (* we do the actual jump *)
        iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
          [apply jmp_i|apply Hfl|iCorrectPC a22 a_last|..].
        iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".

        (* We have all the resources of r *)
        iAssert (registers_mapsto (<[PC:=match p with
                | E => inr (RX, Global, b, e, a')
                | _ => inr (p, Global, b, e, a')
                end]> r2))
          with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
        { iApply (registers_mapsto_resources with "[$Hr_gen] [$Hr_stk] [$Hr_t0] [$Hr_adv] [$HPC]").
          repeat rewrite ?dom_delete_L ?dom_insert_L. rewrite Hdom_r'.
          rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
          f_equal. clear. set_solver. }
        (* r contrains all registers *)
        iAssert (full_map r2) as "#Hfull2";[iApply r_full|].
        (* again we are jumping to unknown code. We will now need to close all our invariants so we can 
           reestablish the FTLR on the new state *)
        (* we close the invariant for our program *)
        iMod ("Hcls'" with "[Hprog_done Hprog Hinstr Hscall $Hna]") as "Hna".
        { iNext. iDestruct "Hprog_done" as "(Hpush2 & push1 & Ha19 & Hpop1 & Hpop2 & Hpop3 &
                                             Ha8 & Ha9 & Hastore & Hrest0_first & Hprog_done)".
          iApply (big_sepL2_app with "Hprog_done [-]"). 
          iFrame "Hrest0_first Ha9 Ha8 Hastore". 
          iApply (big_sepL2_app with "Hpop3 [-]").
          iApply (big_sepL2_app with "Hpop2 [-]").
          iApply (big_sepL2_app with "Hpop1 [-]").
          iFrame "Ha19". iFrame "push1". iFrame "Hpush2".
          rewrite Hrest_app1. 
          iApply (big_sepL2_app with "Hscall [-]"). iFrame.
        }

        (* the adversary stack is valid in the W5 *)
        iAssert ([∗ list] a ∈ region_addrs stack_own_end estk,
                 read_write_cond a RWLX (fixpoint interp1)
                 ∗ ⌜region_type_uninitialized W5 a⌝)%I as "#Hstack_adv_val".
                 (* ∗ ⌜region_state_pwl W5 a⌝)%I as "#Hstack_adv_val". *)
        { rewrite Hstksplit -Hstack_localeq.
          iDestruct (big_sepL_app with "Hstackallrel") as "[Hstackallrel1 Hstackallrel2]".
          iApply big_sepL_app. iSplit.
          - iApply big_sepL_sep. iSimpl.
            (* Use Hstackallrel and the fact that stack_own_end ∈ region_addrs a0 estk *)
            (* stack_own_end is uninitialized in W5 by definition of W5 *)
            assert (stack_own_end ∈ region_addrs a0 stack_own_last) as Hin.
            { apply withinBounds_le_addr in Hwb3.
              rewrite (region_addrs_split _ stack_own_end);[|revert Hwb3 Hstack_own_end_incr;clear;solve_addr].
              apply elem_of_app;right. apply elem_of_list_lookup. exists 0.
              apply region_addrs_first. revert Hwb3 Hstack_own_end_incr;clear;solve_addr. }
            iDestruct (big_sepL_elem_of with "Hstackallrel") as "Hstack_own_end_rel";[apply elem_of_app;left;apply Hin|]. 
            iFrame "Hstack_own_end_rel". iPureIntro.
            split;auto.
            assert (is_Some (m_uninit2 !! stack_own_end)) as [? Hin'].
            { apply list_to_map_lookup_is_Some. rewrite fst_zip;[|rewrite /= Hlengthstackadv;clear;lia].
              apply elem_of_app;left;constructor. }
            exists x. apply override_uninitializedW_lookup_some. auto. 
          - iApply big_sepL_sep. iFrame "Hstackallrel2".
            iApply big_sepL_forall. iPureIntro.
            intros x y Hin.
            pose proof (HtempW3 x y Hin) as [Htempy | [? Huninity] ]. 
            + assert (is_Some (m_uninit2 !! y)) as [wy Hwy].
              { apply list_to_map_lookup_is_Some. rewrite fst_zip;[|rewrite /= Hlengthstackadv;clear;lia].
                apply elem_of_app. right. apply elem_of_list_filter. split;auto. apply elem_of_list_lookup. eauto. 
              }
              eapply override_uninitializedW_lookup_some in Hwy. exists wy. eauto.
            + assert (y ∈ region_addrs stack_own_last estk) as Hin';[apply elem_of_list_lookup;eauto|].
              apply withinBounds_le_addr in Hwb3.
              apply withinBounds_le_addr in Hwb2.
              assert (y ∈ region_addrs stack_own_end estk) as Hin''.
              { rewrite (region_addrs_split _ stack_own_last);[|revert Hwb3 Hstack_own_end_incr;clear;solve_addr].
                apply elem_of_app;right;auto. }
              apply (region_addrs_xor_elem_of _ _ stack_own_last) in Hin'' as test;
                [|revert Hwb2 Hstack_own_end_incr;clear;solve_addr].
              destruct test as [ [? ?] | [? ?] ];try done.
              rewrite /region_addrs in H1.
              assert (region_size stack_own_end stack_own_last = 1) as Heqsize;
                [revert Hstack_own_end_incr;clear;rewrite /region_size;solve_addr|].
              rewrite Heqsize /= in H1.
              apply Hnin1 in Hin'. apply Hnin2 in Hin''. 
              assert (y ∉ dom (gset Addr) m_uninit2) as Hnin.
              { intros Hcontr%elem_of_gmap_dom%list_to_map_lookup_is_Some.
                rewrite fst_zip in Hcontr;[|rewrite /= Hlengthstackadv;clear;lia].
                apply elem_of_app in Hcontr as [Hcontr | Hcontr];[done|].
                apply elem_of_list_filter in Hcontr as [Hcontr _].
                rewrite Hcontr in Huninity. inversion Huninity.  
              }
              exists x0. rewrite override_uninitializedW_lookup_nin;auto.
              rewrite -std_update_multiple_revoke_commute;auto.
              rewrite std_sta_update_multiple_lookup_same_i;auto.
              rewrite -std_update_multiple_revoke_commute;auto.
              rewrite std_sta_update_multiple_lookup_same_i;auto.
              rewrite revoke_monotone_lookup_same;auto. rewrite Huninity. auto. 
        }
  
        (* We are now ready to show that all registers point to a valid word *)
        iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W5 (r2 !r! r1))%I
          with "[-Hsts Hr Hmaps Hna]" as "Hreg".
        { iIntros (r1).
          assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
              [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
          { destruct (decide (r1 = PC)); [by left|right].
            destruct (decide (r1 = r_stk)); [by left|right].
            destruct (decide (r1 = r_t0)); [by left|right].
            destruct (decide (r1 = r_adv)); [by left|right;auto].  
          }
          - iIntros "%". contradiction.
          - assert (r2 !! r_stk = Some (inr (URWLX, Local, stack_own_end, estk, stack_own_end))) as Hr_stk; auto. 
            rewrite /RegLocate Hr_stk. repeat rewrite fixpoint_interp1_eq.
            iIntros (_). iSimpl. 
            replace (min stack_own_end estk) with stack_own_end by (revert H0; clear; solve_addr).
            replace (max stack_own_end stack_own_end) with stack_own_end by (clear; solve_addr).
            rewrite (interp_weakening.region_addrs_empty stack_own_end stack_own_end); [|clear; solve_addr].
            rewrite big_sepL_nil. iSplitR; auto.
            iApply (big_sepL_mono with "Hstack_adv_val").
            simpl. iIntros (k y Hky) "[H %]". iExists RWLX. iFrame. iSplit;[auto|]. 
            iPureIntro. right. auto.
          - (* continuation *)
            iIntros (_). clear Hr_t0. 
            assert (r2 !! r_t0 = Some (inr (E, Local, a0, stack_own_end, a3))) as Hr_t0; auto. 
            rewrite /RegLocate Hr_t0. repeat rewrite fixpoint_interp1_eq. iSimpl.
            (* prove continuation *)
            iAlways.
            iIntros (r3 W6 Hrelated6).
            iNext.

            (* We start by asserting that the adversary stack is still temporary *)
            iAssert ([∗ list] a ∈ (region_addrs stack_own_end estk),
                     ⌜region_type_temporary W6 a \/ region_type_uninitialized W6 a⌝
                     (* ⌜W6.1 !! a = Some Temporary⌝ *)
                    ∗ rel a RWLX (λ Wv : WORLD * Word, ((fixpoint interp1) Wv.1) Wv.2)
                )%I as "#Hstack_adv_tmp'".
            { (* WARNING: the lemma can be made stronger by asserting that the uninitialized word is the same as in W5 *)
              (* need to see if that's important later (probably is...) *)
              iApply (big_sepL_mono with "Hstack_adv_val"). iIntros (k y Hsome) "(Hrel & %)".
              iFrame. iPureIntro. destruct H1.
              eapply region_state_U_pwl_monotone_same in H1; eauto.
              destruct H1; [left; auto|right; eauto].
              exists x. exact H1. }

            iDestruct (big_sepL_sep with "Hstack_adv_tmp'") as "[Htemp _]". 
            iDestruct (big_sepL_forall with "Htemp") as %HtempW6. iClear "Htemp".
            
            (* we want to distinguish between the case where the local stack frame is Static (step through 
               continuation) and where the local stack frame is temporary (apply FTLR) *)
            assert (forall a, a ∈ region_addrs a0 stack_own_end ++ l' ++ l'' ->
                         (std W6) !! a = Some Temporary ∨
                         (std W6) !! a = Some (Static m_static2))
              as Hcases'.
            { intros a'' Hin. apply or_comm,related_sts_pub_world_static with W5;auto.
              assert (std W4 !! a'' = Some (Static m_static2)) as Hlookup.
                { apply std_sta_update_multiple_lookup_in_i.
                  rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                  rewrite elements_list_to_set;auto. }
                rewrite /W5. rewrite /W4 in Hlookup.
                assert (a'' ∉ dom (gset Addr) m_uninit2) as Hnin.
                { intros Hcontr%elem_of_gmap_dom%list_to_map_lookup_is_Some.
                  rewrite fst_zip in Hcontr;[|rewrite /= Hlengthstackadv;clear;lia].
                  assert (a'' ∈ region_addrs stack_own_end estk) as Hin'.
                  { apply withinBounds_le_addr in Hwb3. 
                    apply elem_of_cons in Hcontr as [-> | Hcontr%elem_of_list_filter].
                    - apply elem_of_list_lookup. exists 0. apply region_addrs_first.
                      revert Hwb3. clear;solve_addr.
                    - rewrite (region_addrs_split _ stack_own_last);[|revert Hstack_own_end_incr Hwb3;clear;solve_addr].
                      apply elem_of_app;right;destruct Hcontr as [_ Hcontr];auto. 
                  }
                  apply Hnin2 in Hin'. apply Hin'.
                  rewrite /m_static2. rewrite /static2_addrs /static2_instrs. 
                  rewrite lists_to_static_region_dom;
                    [|repeat rewrite app_length; by rewrite Hlength_rest Hlength_rest'' Hlength_stack_own2 /l_frame2 /=].
                  rewrite elements_list_to_set;auto. 
                }
                rewrite override_uninitializedW_lookup_nin;auto.
                rewrite -std_update_multiple_revoke_commute;auto.
                rewrite -std_update_multiple_revoke_commute;auto. 
            }
            assert (a0 ∈ region_addrs a0 stack_own_end ++ l' ++ l'') as Ha2in.
            { apply elem_of_app. left. apply elem_of_list_lookup. exists 0.
              apply region_addrs_first. assert ((a0 + 2)%a = Some a3) as Hincr.
              eapply (contiguous_between_incr_addr _ 2 a0 a3);[apply Hcont1|auto].
              revert Hstack_own_bound1 Hincr. clear. solve_addr. }
            pose proof (Hcases' _ Ha2in) as [Hm_temp' | Hm_static'].
            { iSimpl. iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)".
              iSplit; [auto|rewrite /interp_conf].
              (* first we want to assert that if a2 is Temporary, the remaining addresses are also temporary *)
              iAssert (⌜∀ a : Addr, a ∈ dom (gset Addr) m_static2 → temporary W6 a⌝)%I as %Hm_frame_temp_all.
              { iIntros (a''). rewrite /m_static2. 
                rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                iIntros (Hin). apply elem_of_list_to_set in Hin. 
                pose proof (Hcases' a'' Hin) as [Htemp'' | Hstatic].
                - rewrite /temporary. rewrite Htemp''. auto.
                - iDestruct (full_sts_static_all with "Hsts Hr") as %Hforall;[eauto|]. exfalso.
                  assert (a0 ∈ dom (gset Addr) m_static2) as Hin'.
                  { rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                    apply elem_of_list_to_set. auto. }
                  apply Hforall in Hin'. rewrite /static Hm_temp' in Hin'. done. 
              }
              iDestruct (fundamental W6 r3 RX Local a0 stack_own_end a3 with "[] [] [-]") as "[_ Hcont]";[by iLeft| |iFrame "∗ #"|..].
              (* iDestruct (fundamental W6 r3 RX Local a0 estk a3 with "[] [] [-]") as "[_ Hcont]";[by iLeft| |iFrame "∗ #"|..]. *)
              { iSimpl. 
                rewrite Hstksplit. iDestruct (big_sepL_app with "Hstackallrel") as "[A _]".
                assert (region_addrs a0 stack_own_last = region_addrs a0 stack_own_end ++ [stack_own_end]) as ->.
                { apply withinBounds_le_addr in Hwb3.
                  rewrite (region_addrs_split _ stack_own_end);[|revert Hstack_own_end_incr Hwb3;clear;solve_addr]. 
                  f_equal. rewrite /region_addrs.
                  assert (region_size stack_own_end stack_own_last = 1) as ->;
                      [revert Hstack_own_end_incr;clear;rewrite /region_size; solve_addr|auto].
                }
                iDestruct (big_sepL_app with "A") as "[B _]".
                iApply (big_sepL_mono with "B").
                iIntros (k y Hky) "Hrel". iExists RWLX. iSplit;[auto|]. iFrame. iPureIntro.            
                left. 
                (* we assert that the region is all in state temporary *)
                assert (y ∈ region_addrs a0 stack_own_end) as Hk'.
                { apply elem_of_list_lookup. eauto. }
                assert (y ∈ dom (gset Addr) m_static2) as Hk''.
                { rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                  apply elem_of_list_to_set. apply elem_of_app. by left. }
                apply Hm_frame_temp_all in Hk''. rewrite /temporary in Hk''.
                destruct (W6.1 !! y) eqn:Hsome;[subst;auto|done].
              }
              iFrame. 
            }
            
            (* Now we are in the case where m_static2 is still static. We will have to open the region and step through
               the continuation as usual. *)
            iSimpl.
            iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)".
            (* since a2 is static, all of dom(m_static1) is static *)
            iDestruct (full_sts_static_all with "Hsts Hr") as %Hall_static';eauto.
            iSplit; [auto|rewrite /interp_conf].
            (* get the PC, currently pointing to the activation record *)
            iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
            (* get some registers *)
            iGet_genpur_reg_map r3 r_t1 "Hmreg'" "Hfull3" "[Hr_t1 Hmreg']".
            iGet_genpur_reg_map r3 r_stk "Hmreg'" "Hfull3" "[Hr_stk Hmreg']".
            iGet_genpur_reg_map r3 r_adv "Hmreg'" "Hfull3" "[Hr_adv Hmreg']".
            iGet_genpur_reg_map r3 r_env "Hmreg'" "Hfull3" "[Hr_env Hmreg']".
            iGet_genpur_reg_map r3 r_t0 "Hmreg'" "Hfull3" "[Hr_t0 Hmreg']".
            iGet_genpur_reg_map r3 r_t2 "Hmreg'" "Hfull3" "[Hr_t2 Hmreg']".

            (* works here?! *)
            
            (* Open the static region for the local stack frame *)
            iMod (region_open_static with "[$Hr $Hsts]") as "(Hr & Hsts & Hstates & Hframe & %)";
              [apply Hm_static'|].
            iAssert ( a0 ↦ₐ[RWLX] inr (RWX, Global, d, d', d)
                    ∗ a2 ↦ₐ[RWLX] wret
                    ∗ [[a3,stack_own_end]] ↦ₐ[RWLX] 
                           [[ [inl w_1; inl w_2_U; inl w_3; inl w_4a; inl w_4b_U;
                               inr (pc_p, pc_g, pc_b, pc_e, a22); inr (URWLX, Local, a0, estk, stack_new)] ]]
                    ∗ [∗ list] a;w ∈ l'++l''; pws++pws', ∃ p φ, rel a p φ ∗ a ↦ₐ[p] w)%I
              with "[Hframe]" as "(Ha2 & Ha3 & Hframe & Hrest)".
            { iDestruct (static_region_to_big_sepL2 _ _ (λ a v, ∃ p φ, rel a p φ ∗ a ↦ₐ[p] v)%I with "[] Hframe")
                as "Hframe";[auto|..]. 
              { repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto. }
              { iAlways. auto. }
              iDestruct (big_sepL2_app' with "Hframe") as "[Hframe $]";[auto|].
              iAssert ([∗ list] y1;y2 ∈ region_addrs a0 stack_own_end;l_frame2, y1 ↦ₐ[RWLX] y2)%I
                with "[Hframe]" as "Hframe".
              { rewrite (region_addrs_split a0 stack_own_end estk).
                iDestruct (big_sepL_app with "Hstackallrel") as "[Hframe' _]".
                iDestruct (big_sepL2_to_big_sepL_l _ _ l_frame2 with "Hframe'") as "Hframe+";eauto.
                iDestruct (big_sepL2_sep with "[Hframe+ Hframe]") as "Hframe";
                  [iSplitL "Hframe";[iFrame "Hframe"|iFrame "Hframe+"]|].
                iApply (big_sepL2_mono with "Hframe").
                iIntros (k y1 y2 Hin1 Hin2) "[H1 Hrel2]".
                iDestruct "H1" as (? ?) "[Hrel1 ?]".
                iDestruct (rel_agree with "[$Hrel1 $Hrel2]") as "[% _]". subst H2. iFrame.
                auto. }                
              iDestruct (region_mapsto_cons with "Hframe") as "[Ha2 Hframe]"; [iContiguous_next Hcont1 0|..].
              { apply contiguous_between_middle_bounds with (i:=1) (ai:=a2) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iDestruct (region_mapsto_cons with "Hframe") as "[Ha3 Hframe]"; [iContiguous_next Hcont1 1|..].
              { apply contiguous_between_middle_bounds with (i:=2) (ai:=a3) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame. 
            }
            (* prepare the new stack value *)
            assert (∃ stack_new_1, (stack_new_1 + 1)%a = Some stack_new) as [stack_new_1 Hstack_new_1].
            { revert Hstack_own_bound' Hstack_new. clear. intros H. destruct (stack_own_b + 4)%a eqn:Hsome;[|solve_addr].
              exists a. solve_addr. }
            (* step through instructions in activation record *)
            iApply (scallU_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
              [| |auto|auto|auto|iContiguous_next Hcont_rest2 0|apply Hstack_new_1|revert Hstack_own_bound1 Hstack_own_bound1'; clear; solve_addr|..].
            { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb3.
              apply (contiguous_between_middle_bounds _ 2 a3) in Hcont1;[|auto].
              revert Hwb3 Hcont1 Hmid. clear. solve_addr. 
            }
            { simpl. revert Hcont_rest2' Hsize Hspliteq Hstack_own_bound Hstack_own_bound' Hstack_own_bound1 Hstack_own_bound1'. clear. rewrite /region_size.
              rewrite andb_true_iff. intros.
              rewrite Z.leb_le Z.ltb_lt. solve_addr. 
            }
            iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
            iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
            iDestruct "Hr_t1" as (wrt1') "Hr_t1".
            (* we don't want to close the stack invariant yet, as we will now need to pop it *)
            (* go through rest of the program. We will now need to open the invariant and destruct it into its done and prog part *)
            (* sub r_t1 0 7 *)
            (* works here *)
            iMod (na_inv_open with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|].
            iClear "Hadv_val". 
            rewrite Hrest_app1. repeat rewrite app_comm_cons. rewrite app_assoc.
            rewrite /awkward_example.
            iAssert ([∗ list] a_i;w_i ∈ ((((reqperm_prog ++ preptack_prog) ++ link0 :: a1 :: a5 :: a6 :: scall_prologue) ++
                                 s_last :: a8 :: astore :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19
                                 :: a20 :: a21 :: scall_prologue_first1 :: scall_prologue1) ++ (a22 :: a23 :: rest2));
                     (take 146 (awkward_instrs f_a r_adv 40)) ++ (drop 146 (awkward_instrs f_a r_adv 40)), a_i ↦ₐ[pc_p'] w_i)%I
              with "[Hprog]" as "Hprog".
            { rewrite take_drop. iApply "Hprog". }
            iDestruct (mapsto_decomposition with "Hprog") as "[Hprog_done Hprog]".
            { simpl. inversion Hscall_length as [Heq]. inversion Hscall_length1 as [Heq']. rewrite app_length Heq /=. rewrite Heq'. repeat rewrite app_length. rewrite Hreqglob_length Hprepstack_length. simpl. repeat f_equiv. rewrite Heq. simpl. done. }
            assert (drop 146 (awkward_instrs f_a r_adv 40) = [jmp r_adv;
                                                          sub_z_z r_t1 0 6;
                                                          lea_r r_stk r_t1] ++
                                                          popU_instrs r_stk r_t0 ++
                                                          popU_instrs r_stk r_env ++
                                                          [load_r r_adv r_env] ++
                                                          assert_r_z_instrs f_a r_adv 1 ++
                                                          [getb r_t1 r_stk;
                                                           add_r_z r_t2 r_t1 9;
                                                           subseg_r_r r_stk r_t1 r_t2] ++ 
                                                          mclearU_instrs r_stk ++
                                                          rclear_instrs (list_difference all_registers [PC;r_t0]) ++
                                                          [jmp r_t0]) as ->;[auto|].
            iDestruct "Hprog" as "[Ha Hprog]".
            iCombine "Ha" "Hprog_done" as "Hprog_done".
            (* sub r_t1 0 6 *)
            iPrologue rest2 Hrest_length1 "Hprog".
            iApply (wp_add_sub_lt_success_z_z with "[$HPC Hr_t1 $Hinstr]");
              [apply sub_z_z_i|right;left;eauto|iContiguous_next Hcont_rest2 1|apply Hfl|iCorrectPC a22 a_last|
               iSimpl;iFrame;eauto|].
            iEpilogue "(HPC & Hinstr & Hr_t1)".
            iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* lea r_stk r_t1 *)
            iPrologue rest2 Hrest_length1 "Hprog".
            assert ((stack_new + (0 - 6))%a = Some a3) as Hpop1.
            { assert ((a3 + 1)%a = Some stack_own_b) as Hincr;[iContiguous_next Hcont1 2|].
              assert ((a2 + 1)%a = Some a3) as Hincr';[iContiguous_next Hcont1 1|].
              revert Hstack_own_bound1' Hincr Hincr' Hstack_new_1. clear. solve_addr. }
            iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
              [apply lea_r_i|apply Hfl|iCorrectPC a22 a_last|
               iContiguous_next Hcont_rest2 2|apply Hpop1|auto..].
            { simpl; auto. revert Hpop1; clear; solve_addr. }
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* pop r_stk r_t0 *)
            do 3 (destruct rest2; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a25;a26;a27] (a28::rest2) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a2 + (-1))%a = Some a0) as Hpop1.
            { rewrite -(addr_add_assoc a0 _ 1);[apply addr_add_0|iContiguous_next Hcont1 0]. }
            iApply (popU_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_t0 Ha3"];
              [split;[|split];iCorrectPC a22 a_last|apply Hfl|econstructor|iContiguous_bounds_withinBounds a0 stack_own_last|auto|iContiguous_next Hcont_rest2 3|iContiguous_next Hcont_rest2 4|iContiguous_next Hcont_rest2 5| |].
            { iContiguous_next Hcont_rest2' 1. }
            iNext. iIntros "(HPC & Hpop & Hr_t0 & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* pop r_stk r_env *)
            do 3 (destruct rest2; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a28;a29;a30] (a31::rest2) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            iApply (popU_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Ha2"];
              [split;[|split];iCorrectPC a22 a_last|apply Hfl|econstructor|iContiguous_bounds_withinBounds a0 stack_own_last|auto|iContiguous_next Hcont_rest2 6|iContiguous_next Hcont_rest2 7|iContiguous_next Hcont_rest2 8|iContiguous_next Hcont_rest2' 0|].
            iNext. iIntros "(HPC & Hpop & Hr_env & Ha2 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* we have now arrived at the final load of the environment. we must here assert that the loaded
               value is indeed 1. We are able to show this since W6 is a public future world of W5, in which 
               invariant i is in state true *)
            (* load r_adv r_env *)
            (* does not work here *)

            iPrologue rest2 Hrest_length1 "Hprog".
            iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a32 (* a37 *))
                                ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                                ∗ a31 (* a36 *) ↦ₐ[pc_p'] load_r r_adv r_env
                                ∗ sts_full_world W6
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
              iAssert (⌜(d =? a31)%a = false⌝)%I as %Hne'.
              { destruct (d =? a31)%a eqn:Heq;auto. apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
                iDestruct (cap_duplicate_false with "[$Hinstr $Hb]") as "Hfalse";[|done].
                eapply isCorrectPC_contiguous_range with (a := a) in Hvpc;[|eauto|];last (by apply elem_of_cons;left).
                destruct pc_p';auto.
                destruct pc_p;inversion Hfl. 
                inversion Hvpc as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
              iApply (wp_load_success with "[$HPC $Hinstr $Hr_adv $Hr_env Hb]");
                [apply load_r_i|apply Hfl|iCorrectPC a22 a_last
                 |auto|iContiguous_next Hcont_rest2 9|rewrite Hne';iFrame;iPureIntro;apply PermFlows_refl|rewrite Hne'].
              iNext. iIntros "(HPC & Hr_adv & Ha36 & Hr_env & Hd)".
              iMod ("Hcls" with "[Hstate Hd]") as "_".
              { iNext. iExists true. iFrame. }
              iModIntro. iApply wp_pure_step_later;auto;iNext.
              iApply "Hφ'". iFrame. 
            }
            iApply "Hload_step".
            iNext. iIntros "(HPC & Hr_env & Ha36 & Hsts & Hr_adv)".
            (* We can now assert that r_adv indeed points to 1 *)
            assert (contiguous_between (a32 :: rest2) a32 a_last) as Hcont_rest2_weak.
            { apply contiguous_between_incr_addr with (i:=10) (ai:=a32) in Hcont_rest2 as Hincr;auto. 
              eapply (contiguous_between_app _ [a22;a23;a24;a25;a26;a27;a28;a29;a30;a31] (a32 :: rest2) _ _ a32)
                in Hcont_rest2 as [_ Hcont_rest2];eauto. }
            iDestruct (contiguous_between_program_split with "Hprog") as (assert_prog rest3' link3')
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont_rest2_weak|].
            iDestruct "Hcont" as %(Hcont_assert & Hcont_rest3' & Heqapp3' & Hlink3').
            iGet_genpur_reg_map r3 r_t3 "Hmreg'" "Hfull3" "[Hr_t3 Hmreg']".
            iMod (na_inv_open with "Htable Hna") as "[ [>Hpc_b >Ha_entry] [Hna Hcls] ]";[revert Hne;clear;solve_ndisj..|].
            iApply (assert_r_z_success with "[-]");[..|iFrame "HPC Hpc_b Ha_entry Hfetch Hr_adv"];
              [|apply Hfl|apply Hcont_assert|auto|auto|auto|..].
            { intros mid Hmid. apply isCorrectPC_inrange with a22 a_last; auto.
              apply contiguous_between_bounds in Hcont_rest2_weak.
              apply contiguous_between_incr_addr with (i:=10) (ai:=a32) in Hcont_rest2 as Hincr;auto. 
              apply contiguous_between_bounds in Hcont_rest3'.
              revert Hincr Hcont_rest3' Hcont_rest2_weak Hmid; clear. intros. solve_addr. }
            iSplitL "Hr_t1";[iExists _;iFrame|].
            iSplitL "Hr_t2";[iExists _;iFrame|].
            iSplitL "Hr_t3";[iExists _;iFrame|].
            iNext. iIntros "(Hr_t1 & Hr_t2 & Hr_t3 & Hr_adv & HPC & Hassert & Hpc_b & Ha_entry)".
            iMod ("Hcls" with "[$Hna $Hpc_b $Ha_entry]") as "Hna". 
            iDestruct (big_sepL2_length with "Hprog") as %Hrest_length2.
            iDestruct (big_sepL2_length with "Hassert") as %Hassert_length.
            assert (isCorrectPC_range pc_p pc_g pc_b pc_e link3' a_last) as Hvpc3.
            { intros mid Hmid. apply isCorrectPC_inrange with a22 a_last; auto.
              apply contiguous_between_incr_addr with (i:=10) (ai:=a32) in Hcont_rest2 as Hincr;auto.
              revert Hincr Hassert_length Hlink3' Hmid; clear. intros. solve_addr. }
            
            (* Since the assertion succeeded, we are now ready to jump back to the adv who called us *)
            (* Before we can return to the adversary, we must clear the local stack frame and registers. This will 
               allow us to release the local frame, and show we are in a public future world by reinstating 
               the full stack invariant *)
            (* we must prepare the stack capability so that we only clear the local stack frame *)
            (* getb r_t1 r_stk *)
            destruct rest3';[inversion Hrest_length2|].
            apply contiguous_between_cons_inv_first in Hcont_rest3' as Heq. subst link3'. 
            iPrologue rest3' Hrest_length2 "Hprog".
            iApply (wp_Get_success with "[$HPC $Hinstr $Hr_stk $Hr_t1]");
              [apply getb_i|auto|apply Hfl|iCorrectPC a33 a_last|iContiguous_next Hcont_rest3' 0|auto..].
            iEpilogue "(HPC & Hinstr & Hr_stk & Hr_t1)"; iSimpl in "Hr_t1"; iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* add_r_z r_t2 r_t1 8 *)
            iPrologue rest3' Hrest_length2 "Hprog".
            iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hinstr $Hr_t1 $Hr_t2]");
              [apply add_r_z_i|by left|iContiguous_next Hcont_rest3' 1|apply Hfl|iCorrectPC a33 a_last|..].
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_t2)"; iSimpl in "Hr_t2"; iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* subseg r_stk r_t1 r_t2 *)
            assert (z_to_addr a0 = Some a0) as Ha2.
            { clear. rewrite /z_to_addr /=.
              destruct (Z_le_dec a0 MemNum),(Z_le_dec 0 a0);destruct a0;
                [f_equiv;by apply z_of_eq|zify_addr;apply Zle_bool_imp_le in pos..]. 
              lia. apply Zle_bool_imp_le in fin. lia. lia.               
            }
            assert ((a0 + 9)%a = Some stack_own_end) as Ha2_stack_own_end.
            { assert ((a0 + 3)%a = Some stack_own_b) as Ha2_stack_own_b.
              { apply (contiguous_between_incr_addr _ 3 _ stack_own_b) in Hcont1; auto. }
              revert Ha2_stack_own_b Hstack_own_bound'. 
              clear; intros. solve_addr. }
            assert (z_to_addr (a0 + 9)%Z = Some stack_own_end) as Ha2_stack_own_end'.
            { (* fixme: very tedious *)
              revert Ha2_stack_own_end;clear. intros.
              destruct stack_own_end;simpl.
              rewrite /z_to_addr.
              zify_addr; subst;
              try solve_addr_close_proof. 
              destruct (Z_le_dec (z1 + 9)%Z MemNum);try lia. 
              destruct (Z_le_dec 0 (z1 + 9)%Z); try lia.
              destruct (Z.leb_le (z1 + 9) MemNum); try lia. 
              destruct (Z.leb_le 0 (z1 + 9)); try lia.
              f_equal. eapply z_of_eq. reflexivity. }
            iPrologue rest3' Hrest_length2 "Hprog".
            iApply (wp_subseg_success with "[$HPC $Hinstr $Hr_stk $Hr_t1 $Hr_t2]");
              [apply subseg_r_r_i|apply Hfl|iCorrectPC a33 a_last|
               split;[apply Ha2|apply Ha2_stack_own_end']|
               auto|auto| |iContiguous_next Hcont_rest3' 2|..].
            { rewrite !andb_true_iff !Z.leb_le. apply withinBounds_le_addr in Hwb2.
              assert ((a0 + 3)%a = Some stack_own_b) as Ha2_stack_own_b.
              { apply (contiguous_between_incr_addr _ 3 _ stack_own_b) in Hcont1; auto. }
              revert Hstack_own_bound Hwb2 Ha2_stack_own_end Ha2_stack_own_b.
              clear. repeat split; try lia; try solve_addr. }
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_t2 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            iAssert ([[a0,stack_own_end]]↦ₐ[RWLX][[l_frame2]])%I with "[Hframe Ha2 Ha3]" as "Hstack".
            { iApply region_mapsto_cons;[iContiguous_next Hcont1 0|..].
              { apply contiguous_between_middle_bounds with (i:=1) (ai:=a2) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame.
              iApply region_mapsto_cons;[iContiguous_next Hcont1 1|..].
              { apply contiguous_between_middle_bounds with (i:=2) (ai:=a3) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame. 
            }
            (* We are now ready to clear the stack *)
            assert (contiguous_between (a36 :: rest3') a36 a_last) as Hcont_weak.
            { repeat (inversion Hcont_rest3' as [|????? Hcont_rest2'']; subst; auto; clear Hcont_rest3'; rename Hcont_rest2'' into Hcont_rest3'). }
            iDestruct (contiguous_between_program_split with "Hprog") as (mclear_addrs rclear_addrs rclear_first)
                                                                           "(Hmclear & Hrclear & #Hcont)"; [eauto|].
            iDestruct "Hcont" as %(Hcont_mclear & Hcont_rest3 & Hstack_eq2 & Hlink3).
            iDestruct (big_sepL2_length with "Hmclear") as %Hmclear_length.
            assert (7 < (length mclear_addrs)) as Hlt7;[rewrite Hmclear_length /=;clear;lia|].
            assert (16 < (length mclear_addrs)) as Hlt17;[rewrite Hmclear_length /=;clear;lia|].
            apply lookup_lt_is_Some_2 in Hlt7 as [ai Hai].
            apply lookup_lt_is_Some_2 in Hlt17 as [aj Haj].
            assert (ai + 9 = Some aj)%a.
            { rewrite (_: 9%Z = Z.of_nat (9 : nat)).
              eapply contiguous_between_incr_addr_middle; [eapply Hcont_mclear|..]. all: eauto. }
            assert (a36 < rclear_first)%a as Hcontlt2.
            { revert Hmclear_length Hlink3. clear. solve_addr. }
            assert (a22 <= a36)%a as Hcontge2.
            { apply region_addrs_of_contiguous_between in Hcont_scall1. subst. 
              revert Hscall_length1 Hcont_rest2 Hcontlt1 Hcontlt2 Hassert_length. rewrite Heqapp3'.
              clear =>Hscall_length Hf2 Hcontlt Hcontlt2 Hassert_length.
              apply contiguous_between_middle_bounds with (i := 26) (ai := a36) in Hf2;[solve_addr|auto].
              simpl in *. assert (16 = 13 + 3) as ->;[lia|]. rewrite lookup_app_r;[|lia].
                by rewrite Hassert_length /=.
            }

            iGet_genpur_reg_map r3 r_t4 "Hmreg'" "Hfull3" "[Hr_t4 Hmreg']".
            iGet_genpur_reg_map r3 r_t5 "Hmreg'" "Hfull3" "[Hr_t5 Hmreg']".
            iGet_genpur_reg_map r3 r_t6 "Hmreg'" "Hfull3" "[Hr_t6 Hmreg']".
            iAssert (▷ (∃ w18 : Word, r_t4 ↦ᵣ w18) ∗ ▷ (∃ w18 : Word, r_t1 ↦ᵣ w18) ∗ ▷ (∃ w18 : Word, r_t2 ↦ᵣ w18) ∗ ▷ (∃ w18 : Word, r_t3 ↦ᵣ w18) ∗ ▷ (∃ w18 : Word, r_t5 ↦ᵣ w18) ∗ ▷ (∃ w18 : Word, r_t6 ↦ᵣ w18) ∗ ▷ (∃ ws : list Word, [[a0,stack_own_end]]↦ₐ[RWLX][[ws]]))%I with "[Hr_t4 Hr_t1 Hr_t2 Hr_t3 Hr_t5 Hr_t6 Hstack]" as "(Hr_t4 & Hr_t1 &Hr_t2 & Hr_t3 & Hr_t5 & Hr_t6 &Hstack)".
            { iSplitL "Hr_t4"; [iNext; iExists _; iFrame "Hr_t4"|].
              iSplitL "Hr_t1"; [iNext; iExists _; iFrame "Hr_t1"|].
              iSplitL "Hr_t2"; [iNext; iExists _; iFrame "Hr_t2"|].
              iSplitL "Hr_t3"; [iNext; iExists _; iFrame "Hr_t3"|].
              iSplitL "Hr_t5"; [iNext; iExists _; iFrame "Hr_t5"|].
              iSplitL "Hr_t6"; [iNext; iExists _; iFrame "Hr_t6"|].
              iNext; iExists _; iFrame "Hstack". }
            iApply (mclearU_spec with "[- $HPC $Hr_stk $Hr_t4 $Hr_t1 $Hr_t2 $Hr_t3 $Hr_t5 $Hr_t6 $Hstack]");
              [apply Hcont_mclear|..]; eauto.
            { assert (rclear_first <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest3|].
              intros mid Hmid. apply isCorrectPC_inrange with link0 a_last; auto.
              revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid Hcontlt2 Hcontge2. clear; intros. split; try solve_addr.
            }
            { destruct H0 as [? _]. auto. }
            { clear. solve_addr. }
            rewrite /mclear.
            destruct (strings.length mclear_addrs =? strings.length (mclearU_instrs r_stk))%nat eqn:Hcontr;
              [|rewrite Hmclear_length in Hcontr;inversion Hcontr].
            iFrame "Hmclear". iNext. iIntros "(HPC & Hr_t1 & Hr_t2' & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6 & Hr_stk & Hstack & Hmclear)".
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
            apply contiguous_between_cons_inv_first in Hcont_rest3 as Heq. subst rclear_first.
            iDestruct (contiguous_between_program_split with "Hrclear") as (rclear jmp_addrs jmp_addr)
                                                                           "(Hrclear & Hjmp & #Hcont)"; [eauto|].
            iDestruct "Hcont" as %(Hcont_rclear & Hcont_rest4 & Hstack_eq3 & Hlink4).
            clear Hrclear_length. iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
            assert (a37 < jmp_addr)%a as Hcontlt3.
            { revert Hrclear_length Hlink4. clear. rewrite /all_registers /=. solve_addr. }
            iAssert (⌜dom (gset RegName) r3 = all_registers_s⌝)%I as %Hdom_r3.
            { iDestruct "Hfull3" as %Hfull3. iPureIntro. apply (anti_symm _); [apply all_registers_subseteq|].
              rewrite elem_of_subseteq. intros ? _. rewrite -elem_of_gmap_dom. apply Hfull3. }
            iApply (rclear_spec with "[- $HPC $Hrclear $Hmreg']").
            { eauto. }
            { apply not_elem_of_list; apply elem_of_cons; by left. }
            { destruct rclear; inversion Hcont_rclear; eauto. inversion Hrclear_length. }
            { assert (jmp_addr <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest4|].
              intros mid Hmid. apply isCorrectPC_inrange with link0 a_last; auto.
              revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid Hcontlt2 Hcontge2 Hcontlt3. clear; intros. split; solve_addr.
            }
            { apply Hfl. }
            { rewrite list_to_set_difference -/all_registers_s.
              repeat rewrite ?dom_delete_L ?dom_insert_L. rewrite Hdom_r3.
              rewrite !all_registers_union_l !difference_difference_L. f_equal. clear. set_solver. }
            iNext. iIntros "(HPC & Hmreg' & Hrclear)".
            
    
            (* we must now invoke the callback validity of the adversary. This means we must show we 
               are currently in a public future world of W *)
            assert (related_sts_pub_world W (std_update_temp_multiple W6 (elements (dom (gset Addr) m_static2) ++
                                                             elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1)))))
              as Hrelated7.
            { eapply related_pub_local_3 with (b:=a0) (l1:=l') (l2:=l'') (l_uninit1:=luninitsplit)
                                              (l_temps1:= ltempsplit ++ ltemprest) (l_temps2:=ltempadv3);
                [rewrite /luninitsplit;eauto|rewrite -Hltempspliteq;auto|auto| |apply Hiff|apply H|apply Hiff'| | | |apply Hawk|apply Hawki|..|
                apply Hrelated3|apply Hrelated6].
              - revert Hwb2 Hwb3. clear. intros Hwb2 Hwb3.
                apply withinBounds_le_addr in Hwb2.
                apply withinBounds_le_addr in Hwb3.
                split;[apply Hwb2|apply Hwb3]. 
              - repeat split;auto.
                rewrite Hltempspliteq. auto. 
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto. apply Permutation_app_comm.
                repeat rewrite app_length. rewrite Hlength_rest;auto.
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto.
                rewrite /static2_addrs Permutation_app_comm app_assoc. auto.
                assert (min stack_own_last stack_own_end = stack_own_end) as ->.
                revert Hstack_own_bound Hstack_own_bound'. clear. solve_addr. auto. 
                repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto.
              - rewrite lists_to_uninitialised_region_dom;auto. rewrite elements_list_to_set;auto.
                rewrite Hltempspliteq in Hdup. do 2 apply NoDup_app in Hdup as (_ & _ & Hdup). auto. 
              - pose proof (lists_to_uninitialised_region_dom ([stack_own_end] ++ ltempadv3)
                                                  ([inl 0%Z] ++ wsadv3));auto.
                rewrite /lists_to_uninitialised_region in H3. rewrite H3. rewrite elements_list_to_set;auto.
                + apply Permutation_app_tail. rewrite /region_addrs.
                  assert (region_size stack_own_end stack_own_last = 1)  as ->;
                      [revert Hstack_own_bound Hstack_own_bound';clear;rewrite /region_size;solve_addr|auto]. 
                + apply NoDup_cons. apply NoDup_app in Hdup' as (_ & _ & Hdup'). split;auto.
                  rewrite /ltempadv3. intros Hin%elem_of_list_filter. destruct Hin as [_ Hin].
                  rewrite /region_addrs in Hin. 
                  assert (stack_own_end < stack_own_last)%a as Hlt;
                    [revert Hstack_own_bound Hstack_own_bound';clear;solve_addr|].
                  apply region_addrs_not_elem_of with (n:=region_size stack_own_last estk) in Hlt. done. 
                + simpl. auto. 
            }
            (* in order to handle the leftovers from the revocation of W3, we must also show that the final world 
               is a public future world of W3 *)
            assert (related_sts_pub_world W3 (std_update_temp_multiple W6 (elements (dom (gset Addr) m_static2) ++
                                                             elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1)))))
              as Hrelated8.
            { eapply related_pub_local_4 with (b:=a0) (l1:=l') (l2:=l'') (l_uninit1:=luninitsplit)
                                              (l_temps1:= ltempsplit ++ ltemprest) (l_temps2:=ltempadv3); 
                [rewrite /luninitsplit;eauto|rewrite -Hltempspliteq;auto|auto| |split;[apply Hiff|apply Hdup]|
                 apply H|apply Hiff'| | | |apply Hawk|apply Hawki|..|
                apply Hrelated3|apply Hrelated6].
              - revert Hwb2 Hwb3. clear. intros Hwb2 Hwb3.
                apply withinBounds_le_addr in Hwb2.
                apply withinBounds_le_addr in Hwb3.
                split;[apply Hwb2|apply Hwb3]. 
              - repeat split;auto.
                rewrite Hltempspliteq. auto. 
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto. apply Permutation_app_comm.
                repeat rewrite app_length. rewrite Hlength_rest;auto.
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto.
                rewrite /static2_addrs Permutation_app_comm app_assoc. auto.
                assert (min stack_own_last stack_own_end = stack_own_end) as ->.
                revert Hstack_own_bound Hstack_own_bound'. clear. solve_addr. auto. 
                repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto.
              - rewrite lists_to_uninitialised_region_dom;auto. rewrite elements_list_to_set;auto.
                rewrite Hltempspliteq in Hdup. do 2 apply NoDup_app in Hdup as (_ & _ & Hdup). auto. 
              - pose proof (lists_to_uninitialised_region_dom ([stack_own_end] ++ ltempadv3)
                                                  ([inl 0%Z] ++ wsadv3));auto.
                rewrite /lists_to_uninitialised_region in H3. rewrite H3. rewrite elements_list_to_set;auto.
                + apply Permutation_app_tail. rewrite /region_addrs.
                  assert (region_size stack_own_end stack_own_last = 1)  as ->;
                      [revert Hstack_own_bound Hstack_own_bound';clear;rewrite /region_size;solve_addr|auto]. 
                + apply NoDup_cons. apply NoDup_app in Hdup' as (_ & _ & Hdup'). split;auto.
                  rewrite /ltempadv3. intros Hin%elem_of_list_filter. destruct Hin as [_ Hin].
                  rewrite /region_addrs in Hin. 
                  assert (stack_own_end < stack_own_last)%a as Hlt;
                    [revert Hstack_own_bound Hstack_own_bound';clear;solve_addr|].
                  apply region_addrs_not_elem_of with (n:=region_size stack_own_last estk) in Hlt. done. 
                + simpl. auto. 
            }

            (* We use the fact that the final world is public to W and W3 to close the full static frame + 
               all temporary address from W and W3 that we uninitialised *)
            iMod (region_close_static_and_uninitialized_to_temporary
                    m_static2 (m_uninit2 ∪ m_uninit1) with "[$Hr $Hsts Hstack Hrest $Hstates]") as "[Hsts Hr]";
              [reflexivity|..].
            { rewrite /m_static2 /static2_addrs. rewrite lists_to_static_region_size;auto.
              repeat rewrite app_length. rewrite Hlength_stack_own2 /=. clear. lia. 
              repeat rewrite app_length. by rewrite Hlength_stack_own2 Hlength_rest Hlength_rest'' /=. }
            { assert (region_addrs stack_own_end stack_own_last = [stack_own_end]) as Hendstack.
              { rewrite /region_addrs.
                assert (region_size stack_own_end stack_own_last = 1) as ->;
                  [rewrite /region_size;revert Hstack_own_end_incr;clear;solve_addr|].
                auto. 
              }
              
              eapply related_pub_local_lookup with (c':=stack_own_end) (b:=a0) (wsadv3:=wsadv3) (wsrs:=[inl 0%Z]) (l1:=l') (l2:=l'') (ltemprest:=ltemprest);
                [..|split;[apply Hiff|]|apply Hiff'| | |apply Hrelated3|apply Hrelated6];eauto. 
              - repeat split;auto.
                (* rewrite Hltempspliteq. auto.  *)
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto. apply Permutation_app_comm.
                repeat rewrite app_length. rewrite Hlength_rest;auto.
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto.
                rewrite /static2_addrs Permutation_app_comm app_assoc. auto.
                assert (min stack_own_last stack_own_end = stack_own_end) as ->.
                revert Hstack_own_end_incr. clear. solve_addr. auto. 
                repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto.
              - assert (region_size stack_own_end stack_own_last = 1) as ->;
                  [rewrite /region_size;revert Hstack_own_end_incr;clear;solve_addr|].
                auto. 
              - rewrite /m_uninit2. rewrite Hendstack. auto. 
              - revert Hwb2 Hwb3. clear. intros Hwb2 Hwb3.
                apply withinBounds_le_addr in Hwb2.
                apply withinBounds_le_addr in Hwb3.
                split;[apply Hwb2|apply Hwb3].
              - rewrite Hendstack. apply NoDup_cons. apply NoDup_app in Hdup' as (_ & _ & Hdup'). split;auto.
                  rewrite /ltempadv3. intros Hin%elem_of_list_filter. destruct Hin as [_ Hin].
                  rewrite /region_addrs in Hin. 
                  assert (stack_own_end < stack_own_last)%a as Hlt;
                    [revert Hstack_own_bound Hstack_own_bound';clear;solve_addr|].
                  apply region_addrs_not_elem_of with (n:=region_size stack_own_last estk) in Hlt. done.
            }
            { set ψ := ((λ a v, ∃ (p' : Perm) (φ0 : WORLD * Word → iPropI Σ),
                                ⌜∀ Wv : WORLD * Word, Persistent (φ0 Wv)⌝
                                  ∗ temp_resources
                                      (std_update_temp_multiple W6
                                         (elements (dom (gset Addr) m_static2) ++
                                          elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1)))) φ0 a p'
                                      ∗ rel a p' φ0))%I.
              set Wfinal := std_update_temp_multiple W6
                                       (elements (dom (gset Addr) m_static2) ++
                                        elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1))).
              iSplitL. 
              - iApply (big_sepL2_to_static_region _ _ ψ)%I;[auto|..]. 
                { iAlways. iIntros (k a'' pw Hpw1 Hpw2) "Hr". iFrame "Hr". }
                iApply (big_sepL2_app with "[Hstack]").
                + iDestruct (region_addrs_zeroes_trans with "Hstack") as "Hstack".
                  rewrite (region_addrs_split a0 stack_own_end estk).
                  iDestruct (big_sepL_app with "Hstackallrel") as "[Hstack_val_frame _]".
                  iDestruct (big_sepL_sep with "[Hstack_val_frame Hstack]") as "Hstack".
                  iSplitL;[iFrame "Hstack"|iFrame "Hstack_val_frame"]. 
                  iDestruct (big_sepL2_to_big_sepL_l _ _ l_frame2 with "Hstack") as "Hstack";[auto|].
                  iApply (big_sepL2_mono with "Hstack"). 
                  iIntros (k a'' _v Hy1 Yy2) "[Ha' Hrel]".
                  iExists RWLX,(λ Wv : WORLD * Word, ((fixpoint interp1) Wv.1) Wv.2).
                  iSplit;[iPureIntro;apply _|]. iSplit;[auto|]. iFrame. iExists (inl 0%Z). iSimpl.
                  iSplit;[auto|]. iFrame. iSplit.
                  { iAlways. iIntros (W0 W0'). iApply interp_monotone. }
                  rewrite fixpoint_interp1_eq /=. auto. iFrame. 
                  apply withinBounds_le_addr in Hwb3 as [Hb1 Hb2].
                  revert Hb1 Hb2;clear. solve_addr.
                + iDestruct (big_sepL2_app' with "Hrest") as "[Hrest Hrest']";[auto|].
                  iDestruct (big_sepL2_sep with "[Hrest]") as "Hrest".
                  { iSplitL;[iFrame "Hrest"|iFrame "Hrest_valid"]. }
                  iDestruct (big_sepL2_sep with "[Hrest']") as "Hrest'".
                  { iSplitL;[iFrame "Hrest'"|iFrame "Hrest_valid'"]. }
                  iApply (big_sepL2_app with "[Hrest]").
                  * iApply (big_sepL2_mono with "Hrest").
                    iIntros (k a'' pw Ha' Hpw) "[Ha' Hr]".
                    iDestruct "Hr" as (p0 φ0 Hpers Hne') "(Hφ & #Hrel & mono)".
                    iDestruct "Ha'" as (p1 φ1) "[#Hrel' Ha'']". 
                    rewrite /ψ. simpl.
                    iDestruct (rel_agree _ p0 p1 with "[$Hrel $Hrel']") as "[% _]". subst p0. 
                    iExists p1,φ0.
                    repeat iSplit;auto. iExists pw. destruct (pwl p1).
                    { iDestruct "mono" as "#mono".
                      iAssert (φ0 (Wfinal, pw))
                      with "[Hφ]" as "Hφ".
                      { iApply ("mono" with "[] Hφ"). auto. }
                      iFrame "∗ #". auto. }
                    { iDestruct "mono" as "#mono".
                      iAssert (φ0 (Wfinal, pw))
                        with "[Hφ]" as "Hφ".
                      { iApply ("mono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto. }
                      iFrame "∗ #". auto. }
                  * iApply (big_sepL2_mono with "Hrest'").
                    iIntros (k a'' pw Ha' Hpw) "[Ha' Hr]".
                    iDestruct "Hr" as (p0 φ0 Hpers Hne') "(Hφ & #Hrel & mono)".
                    iDestruct "Ha'" as (p1 φ1) "[#Hrel' Ha'']".
                    iDestruct (rel_agree _ p0 p1 with "[$Hrel $Hrel']") as "[% _]". subst p1. 
                    rewrite /ψ. simpl. iExists p0,φ0.
                    repeat iSplit;auto. iExists pw. destruct (pwl p0).
                    { iDestruct "mono" as "#mono".
                      iAssert (φ0 (Wfinal, pw))
                        with "[Hφ]" as "Hφ".
                      { iApply ("mono" with "[] Hφ"). auto. }
                      iFrame "∗ #". auto. }
                    { iDestruct "mono" as "#mono".
                      iAssert (φ0 (Wfinal, pw))
                        with "[Hφ]" as "Hφ".
                      { iApply ("mono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto. }
                      iFrame "∗ #". auto. }
              - iAlways.
                iAssert ([∗ map] a↦w ∈ (m_uninit2 ∪ m_uninit1), ▷ interp Wfinal w ∗ read_write_cond a RWLX interp)%I
                  as "#Hvalid".
                { iApply big_sepM_forall. rewrite /m_uninit1 /m_uninit2. 
                  iIntros (k x Hin%lookup_union_Some_raw).
                  assert (k ∈ region_addrs a0 estk) as Hinx.
                  { destruct Hin as [Hin | [Hnin Hin] ].
                    - apply elem_of_list_to_map_2,elem_of_zip_l,elem_of_cons in Hin as [-> | Hin%elem_of_list_filter].
                      + apply withinBounds_le_addr in Hwb3.
                        rewrite (region_addrs_split _ stack_own_end);[|revert Hwb3;simpl;clear;solve_addr].
                        apply elem_of_app;right. apply elem_of_list_lookup. exists 0.
                        apply region_addrs_first. revert Hwb3;simpl;clear;solve_addr.
                      + destruct Hin as [_ Hin].
                        apply withinBounds_le_addr in Hwb2.
                        rewrite (region_addrs_split _ stack_own_last);[|revert Hwb2;simpl;clear;solve_addr].
                        apply elem_of_app;right;auto.
                    - apply elem_of_list_to_map_2,elem_of_zip_l,elem_of_list_filter in Hin as [_ Hin].
                      apply withinBounds_le_addr in Hwb2.
                      rewrite (region_addrs_split _ stack_own_last);[|revert Hwb2;simpl;clear;solve_addr].
                      apply elem_of_app;right;auto.                    
                  }
                  iDestruct (big_sepL_elem_of _ _ k with "Hstackallrel") as "Hk";[auto|]. iFrame "Hk".
                  iNext. (* we want to use the old validity from either W1 or W3 *)
                  destruct Hin as [Hin | [Hnin Hin] ].
                  - apply elem_of_list_to_map_2,elem_of_zip_r,elem_of_cons in Hin as [-> | Hin].
                    + rewrite fixpoint_interp1_eq. auto. 
                    + iDestruct (big_sepL2_to_big_sepL_r with "Hold_temps_valid3") as "Hold_temps_valid3'";[auto|].
                      iDestruct (big_sepL_elem_of _ _ x with "Hold_temps_valid3'") as "Hx";[auto|].
                      iApply interp_monotone;[iPureIntro;apply Hrelated8|]. iApply "Hx". 
                  - (* x is valid in W1 *)
                    apply elem_of_list_to_map_2,elem_of_zip_r in Hin.
                    iDestruct (big_sepL2_to_big_sepL_r with "Hold_temps_valid") as "Hold_temps_valid'";[auto|].
                    iDestruct (big_sepL_elem_of _ _ x with "Hold_temps_valid'") as "Hx";[auto|].
                    iApply interp_monotone;[iPureIntro;apply Hrelated7|]. iApply "Hx". 
                }
                iApply (big_sepM_mono with "Hvalid").
                iIntros (k x Hin) "#[Hinterp Hrel]".
                iExists (λ Wv, interp Wv.1 Wv.2),RWLX. repeat iSplit;auto.
                iPureIntro. intros Wv. apply interp_persistent.
                simpl. iAlways. iIntros (W7 W8) "Hrelated Hinterp'".
                iApply (interp_monotone with "Hrelated Hinterp'").
            }

            (* we can finish reasoning about the program *)
            rewrite /enter_cond /interp_expr /interp_conf. iSimpl in "Hcallback".
            (* again we want to use the jump of fail pattern when jumping to unknown capabilities *)
            iAssert (interp W wret) as "#Hcallback'";[|iClear "Hcallback"].
            { rewrite fixpoint_interp1_eq. iFrame "Hcallback". }
            iDestruct (jmp_or_fail_spec with "Hcallback'") as "Hcallback_now".

            (* We can now finally jump to the return capability *)
            (* jmp r_t0 *)
            iDestruct (big_sepL2_length with "Hjmp") as %Hjmp_length.
            destruct jmp_addrs; [inversion Hjmp_length|].
            destruct jmp_addrs; [|inversion Hjmp_length].
            apply contiguous_between_cons_inv_first in Hcont_rest4 as Heq; subst jmp_addr.
            iDestruct "Hjmp" as "[Hinstr _]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_t0]");
              [apply jmp_i|apply Hfl|..].
            { (* apply contiguous_between_bounds in Hcont_rest3 as Hle. *)
              inversion Hcont_rest4 as [| a'' b' c' l3 Hnext Hcont_rest5 Heq Hnil Heq'].
              inversion Hcont_rest5; subst. 
              apply Hvpc2. revert Hcontge2 Hcontlt2 Hcontlt3 Hnext. clear. solve_addr. }

            destruct (decide (isCorrectPC (updatePcPerm wret))).
            2: { iEpilogue "(HPC & Hinstr & Hrt0)". iApply "Hcallback_now". iFrame. iIntros (Hcontr'). done. }
            
            iDestruct "Hcallback_now" as (p_ret g_ret b_ret e_ret a_ret Heqret) "Hcallback_now". simplify_eq. 
            iAssert (future_world g_ret W (std_update_temp_multiple W6
                   (elements (dom (gset Addr) m_static2) ++ elements (dom (gset Addr) (m_uninit2 ∪ m_uninit1)))))%I
              as "#Hfuture". 
            { destruct g_ret; iSimpl.
              - iPureIntro. apply related_sts_pub_priv_world. apply Hrelated7.
              - iPureIntro. apply Hrelated7.
            }
            set r4 : gmap RegName Word :=
              <[PC := inl 0%Z]>
              (<[r_t0 := inr (p_ret, g_ret, b_ret, e_ret, a_ret)]>
              (create_gmap_default
                 (list_difference all_registers [PC; r_t0]) (inl 0%Z))).
            iDestruct ("Hcallback_now" $! r4 with "Hfuture") as "Hcallback_now'".
            
            iEpilogue "(HPC & Hinstr & Hrt0)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            
            (* We close the program Iris invariant *)
            iMod ("Hcls'" with "[$Hna Hprog_done Hmclear Hrclear Ha36 Hassert]") as "Hna". 
            { iNext. iDestruct "Hprog_done" as "(Ha38 & Ha35 & Ha34 & Ha33 &
                                                 Hpop2 & Hpop1 & Ha24 & Ha23 & Ha22 & Hprog_done)".
              iApply (big_sepL2_app with "Hprog_done [-]").
              iFrame "Ha22 Ha23 Ha24". 
              iApply (big_sepL2_app with "Hpop1 [-]").
              iApply (big_sepL2_app with "Hpop2 [-]").
              iFrame "Ha36".
              rewrite Heqapp3' Hstack_eq2 Hstack_eq3.
              iApply (big_sepL2_app with "Hassert [-]").
              iFrame "Ha33 Ha34 Ha35". 
              iApply (big_sepL2_app with "Hmclear [-]").
              iApply (big_sepL2_app with "Hrclear [-]").
              iFrame. done.
            }
            iClear "Hf4 full Hfull' Hfull2 Hreg'".
            iSimpl in "HPC".
            
            (* we apply the callback to the current configuration *)
            iSpecialize ("Hcallback_now'" with "[Hsts Hr Hmreg' HPC Hrt0 Hna]"). 
            { iFrame "Hna Hr Hsts". iSplitR;[iSplit|].
              - iPureIntro. clear. 
                intros x. rewrite /= /r4.
                destruct (decide (PC = x));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                destruct (decide (r_t0 = x));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                exists (inl 0%Z). apply create_gmap_default_lookup.
                apply elem_of_list_difference. split;[apply all_registers_correct|].
                repeat (apply not_elem_of_cons; split;[auto|try apply not_elem_of_nil]).
              - iIntros (r0 Hne'). rewrite /RegLocate.
                rewrite /r4 lookup_insert_ne;auto.
                destruct (decide (r_t0 = r0));[subst;rewrite lookup_insert|].
                + iApply (interp_monotone $! Hrelated7).
                  rewrite /interp fixpoint_interp1_eq. iFrame "Hcallback'". 
                + rewrite lookup_insert_ne;[|auto]. 
                  assert (r0 ∈ (list_difference all_registers [PC; r_t0])) as Hin.
                  { apply elem_of_list_difference. split;[apply all_registers_correct|].
                    repeat (apply not_elem_of_cons; split;[auto|try apply not_elem_of_nil]). }
                  rewrite !fixpoint_interp1_eq. iRevert (Hin).
                  rewrite (create_gmap_default_lookup _ (inl 0%Z : Word) r0).
                  iIntros (Hin). rewrite Hin. iSimpl. done. 
              - rewrite /registers_mapsto /r4 insert_insert.
                do 2 (rewrite big_sepM_insert; [|done]). iFrame.
                iApply (big_sepM_mono (λ k _, k ↦ᵣ inl 0%Z))%I.
                { intros ? ? [? ->]%create_gmap_default_lookup_is_Some. auto. }
                iDestruct (big_sepM_dom with "Hmreg'") as "Hmreg'". iApply big_sepM_dom.
                rewrite big_opS_proper'. iApply "Hmreg'". done.
                rewrite create_gmap_default_dom list_to_set_difference -/all_registers_s.
                repeat rewrite ?dom_delete_L ?dom_insert_L. rewrite Hdom_r3.
                rewrite !all_registers_union_l !difference_difference_L. f_equal. clear. set_solver.
            }
            iDestruct "Hcallback_now'" as "[_ Hcallback_now']".
            iApply wp_wand_l. iFrame "Hcallback_now'". 
            iIntros (v) "Hv". 
            iIntros (halted). 
            iDestruct ("Hv" $! halted) as (r0 W0) "(#Hfull & Hmreg' & #Hrelated & Hna & Hsts & Hr)". 
            iDestruct ("Hrelated") as %Hrelated10.
            iExists r0,W0. iFrame "Hfull Hmreg' Hsts Hr Hna".
            iPureIntro. 
            eapply related_sts_priv_trans_world;[|apply Hrelated10].
            apply related_sts_pub_priv_world.
            rewrite /std_update_temp_multiple std_update_multiple_app.

            eapply related_sts_pub_trans_world;[apply related_sts_pub_world_static_to_temporary with (m:=m_static2)
                                               (l:=elements (dom (gset Addr) m_static2))|].
            2: { apply related_sts_pub_world_uninit_to_temporary_region. intros k Hin.
                 destruct (decide (k ∈ (elements (dom (gset Addr) m_static2)))).
                 - left. apply std_sta_update_multiple_lookup_in_i. auto.
                 - rewrite std_sta_update_multiple_lookup_same_i;auto.
                   assert (∃ j, region_addrs stack_own_end estk !! j = Some k) as [j Hj].
                   { apply elem_of_list_lookup. rewrite dom_union_L in Hin. 
                     apply elem_of_union in Hin. revert Hin. repeat rewrite -elem_of_gmap_dom.
                     intros [ Hk2%list_to_map_lookup_is_Some | Hk1%list_to_map_lookup_is_Some ]. 
                     - rewrite fst_zip in Hk2;[|rewrite /= Hlengthstackadv;clear;lia].
                       apply elem_of_cons in Hk2 as [-> | Hk2%elem_of_list_filter].
                       + apply withinBounds_le_addr in Hwb3.
                         rewrite (region_addrs_split _ stack_own_end);[|revert Hwb3;simpl;clear;solve_addr].
                         apply elem_of_app;right. apply elem_of_list_lookup. exists 0.
                         apply region_addrs_first. revert Hwb3;simpl;clear;solve_addr.
                       + destruct Hk2 as [_ Hin].
                         apply withinBounds_le_addr in Hwb3.
                         apply withinBounds_le_addr in Hwb2.
                         rewrite (region_addrs_split _ stack_own_last);
                           [|revert Hwb3 Hwb2 Hstack_own_end_incr;simpl;clear;solve_addr].
                         apply elem_of_app;right;auto.
                     - rewrite fst_zip in Hk1;[|rewrite Hlengthstackrest;clear;lia].
                       apply elem_of_list_filter in Hk1 as [_ Hk1].
                       apply withinBounds_le_addr in Hwb2.
                       apply withinBounds_le_addr in Hwb3.
                       rewrite (region_addrs_split _ stack_own_last);
                         [|revert Hwb3 Hwb2 Hstack_own_end_incr;simpl;clear;solve_addr].
                       apply elem_of_app;right;auto.            
                   }
                   apply HtempW6 in Hj. eauto.
            } 
            apply Forall_forall. revert Hall_static';clear;intros Hall_static'.
            intros x Hx%elem_of_elements. apply Hall_static' in Hx. rewrite /static in Hx.
            destruct (W6.1 !! x) eqn:Hsome;subst;done. 
          - iAssert (interp W (inr (p, Global, b, e, a'))) as "#Hadv_val'";[|iClear "Hadv_val"].
            { rewrite fixpoint_interp1_eq. iFrame "Hadv_val". }
            rewrite Hr_t30. 
            assert (r2 !! r_adv = Some (inr (p, Global, b, e, a'))) as Hr_t30_some; auto. 
            rewrite /RegLocate Hr_t30_some. (* repeat rewrite fixpoint_interp1_eq. iSimpl.  *)
            iIntros (_).
            iApply (interp_monotone_nl with "[] [] Hadv_val'");[iPureIntro|auto].
            eapply Hrelated5'.
          - rewrite r_zero; auto.
            repeat rewrite fixpoint_interp1_eq. iPureIntro. auto.
        }
        iDestruct ("Hadv_contW5" with "[$Hsts $Hr $Hna $Hfull2 $Hmaps $Hreg]")
          as "[_ Ho]".
        iApply wp_wand_r. iFrame.
        iIntros (v) "Hhalted".
        iIntros (->).
        iSpecialize ("Hhalted" with "[]");[auto|].
        iDestruct "Hhalted" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)".
        iExists _,_. iFrame.
        iPureIntro. eapply related_sts_priv_trans_world;[apply Hrelated5|auto].
      - rewrite Hr_t30. 
        assert (r !! r_adv = Some (inr (p, Global, b, e, a'))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some. iSimpl. 
        iIntros (_). 
        iApply (interp_monotone_nl with "[] [] Hadv_val");[iPureIntro|auto].
        eapply related_sts_priv_trans_world;[apply HWW''|auto].
        apply related_sts_priv_refl_world. 
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        iIntros (Hne'). 
        assert (r !r! r1 = inl 0%Z) as Hr1.
        { rewrite /RegLocate.
          destruct (r !! r1) eqn:Hsome; rewrite Hsome; last done. rewrite /r in Hsome. 
          do 4 (rewrite lookup_insert_ne in Hsome;auto). 
          assert (Some w3 = Some (inl 0%Z)) as Heq.
          { rewrite -Hsome. apply create_gmap_default_lookup.
            apply elem_of_list_difference. split; first apply all_registers_correct.
            repeat (apply not_elem_of_cons;split;auto).
            apply not_elem_of_nil. 
          }
            by inversion Heq.
        }
        rewrite Hr1 !fixpoint_interp1_eq. auto.
    }
    
    iAssert (((interp_reg interp) W''' r))%I as "#HvalR";[iSimpl;auto|]. 
    iSpecialize ("Hadv_contW''" with "[$HvalR $Hmaps Hsts $Hna $Hr]"); iFrame. 
    iDestruct "Hadv_contW''" as "[_ Ho]". 
    rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros (->). 
    iSpecialize ("Htest" with "[]");[auto|]. 
    iDestruct "Htest" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
    iExists _,_. iFrame.
    iPureIntro. eapply related_sts_priv_trans_world;[apply HWW''|auto].
  Qed.

End awkward_example.
