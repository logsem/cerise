From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine Require Export addr_reg_sample region_invariants_revocation. 

Section region_macros.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.


  (* TODO: move this to folder that will contain all the files about region *)
  (* Currently, this file contains: 
          - supplemental lemmas about big_sepL 
          - splitting a region address (for splitting stack)
          - a definition for updating multiple region states (with some useful lemmas) 
          - allocating a region of multiple addresses (and a definition of default region values)
          - opening a region of multiple addresses 
  *)

  (* --------------------------------------------------------------------------------- *)
  (* -------------------- USEFUL LEMMAS FOR STACK MANIPULATION ----------------------- *)
  (* --------------------------------------------------------------------------------- *)

  (* -------------------- SUPPLEMENTAL LEMMAS ABOUT BIGSEPL -------------------------- *)
   
   Lemma region_addrs_exists {A B: Type} (a : list A) (φ : A → B → iProp Σ) :
     (([∗ list] a0 ∈ a, (∃ b0, φ a0 b0)) ∗-∗
      (∃ (ws : list B), [∗ list] a0;b0 ∈ a;ws, φ a0 b0))%I.
   Proof.
     iSplit. 
     - iIntros "Ha".
       iInduction (a) as [ | a0] "IHn". 
       + iExists []. done.
       + iDestruct "Ha" as "[Ha0 Ha]".
         iDestruct "Ha0" as (w0) "Ha0". 
         iDestruct ("IHn" with "Ha") as (ws) "Ha'".
         iExists (w0 :: ws). iFrame.
     - iIntros "Ha".
       iInduction (a) as [ | a0] "IHn". 
       + done. 
       + iDestruct "Ha" as (ws) "Ha".
         destruct ws;[by iApply bi.False_elim|]. 
         iDestruct "Ha" as "[Ha0 Ha]". 
         iDestruct ("IHn" with "[Ha]") as "Ha'"; eauto. 
         iFrame. eauto.        
   Qed.

   Lemma big_sepL2_to_big_sepL_r {A B : Type} (φ : B → iProp Σ) (l1 : list A) l2 :
     length l1 = length l2 →
     (([∗ list] _;y2 ∈ l1;l2, φ y2) ∗-∗
     ([∗ list] y ∈ l2, φ y))%I. 
   Proof.
     iIntros (Hlen). 
     iSplit. 
     - iIntros "Hl2". iRevert (Hlen). 
       iInduction (l2) as [ | y2] "IHn" forall (l1); iIntros (Hlen). 
       + done.
       + destruct l1;[by iApply bi.False_elim|]. 
         iDestruct "Hl2" as "[$ Hl2]". 
         iApply ("IHn" with "Hl2"). auto. 
     - iIntros "Hl2". 
       iRevert (Hlen). 
       iInduction (l2) as [ | y2] "IHn" forall (l1); iIntros (Hlen). 
       + destruct l1; inversion Hlen. done.
       + iDestruct "Hl2" as "[Hy2 Hl2]".
         destruct l1; inversion Hlen. 
         iDestruct ("IHn" $! l1 with "Hl2") as "Hl2".
         iFrame. iApply "Hl2". auto. 
   Qed.

   Lemma big_sepL2_app'
         (PROP : bi) (A B : Type) (Φ : nat → A → B → PROP) (l1 l2 : list A)
         (l1' l2' : list B) :
     (length l1) = (length l1') →
    (([∗ list] k↦y1;y2 ∈ l1;l1', Φ k y1 y2)
       ∗ ([∗ list] k↦y1;y2 ∈ l2;l2', Φ (strings.length l1 + k) y1 y2))%I
    ≡ ([∗ list] k↦y1;y2 ∈ (l1 ++ l2);(l1' ++ l2'), Φ k y1 y2)%I.
   Proof.
     intros Hlenl1.
     iSplit.
     - iIntros "[Hl1 Hl2]". iApply (big_sepL2_app with "Hl1 Hl2").
     - iIntros "Happ".
       iAssert (∃ l0' l0'' : list A,
         ⌜(l1 ++ l2) = l0' ++ l0''⌝
         ∧ ([∗ list] k↦y1;y2 ∈ l0';l1', Φ k y1 y2)
             ∗ ([∗ list] k↦y1;y2 ∈ l0'';l2', Φ (strings.length l1' + k) y1 y2))%I
                       with "[Happ]" as (l0' l0'') "(% & Happl0' & Happl0'')".
       { by iApply (big_sepL2_app_inv_r with "Happ"). }
       iDestruct (big_sepL2_length with "Happl0'") as %Hlen1.
       iDestruct (big_sepL2_length with "Happl0''") as %Hlen2.
       rewrite -Hlenl1 in Hlen1.
       assert (l1 = l0' ∧ l2 = l0'') as [Heq1 Heq2]; first by apply app_inj_1.
       simplify_eq; rewrite Hlenl1.
       iFrame.
   Qed.

   (* --------------------------------------------------------------------------------- *)
  
   Lemma stack_split (b e a a' : Addr) (p : Perm) (w1 w2 : list Word) :
     (b ≤ a < e)%Z →
     (a + 1)%a = Some a' →
     (length w1) = (region_size b a) →
     ([[b,e]]↦ₐ[p][[w1 ++ w2]] ⊣⊢ [[b,a]]↦ₐ[p][[w1]] ∗ [[a',e]]↦ₐ[p][[w2]])%I.
   Proof.
     intros [Hba Hae] Ha' Hsize.
     assert (b ≤ e)%Z; first lia.
     assert (a < a')%Z; first by apply next_lt.
     assert (a' ≤ e)%Z; first apply addr_next_lt_le with a; auto.
     assert ((a + 1)%Z = a').
     { rewrite /incr_addr in Ha'.
         by destruct (Z_le_dec (a + 1)%Z MemNum); inversion Ha'. }
     iSplit.
     - iIntros "Hbe".
       rewrite /region_mapsto /region_addrs.
       destruct (Z_le_dec b e); try contradiction. 
       rewrite (region_addrs_aux_decomposition _ _ (region_size b a)).      
       iDestruct (big_sepL2_app' with "Hbe") as "[Hba Ha'b]".
       + by rewrite region_addrs_aux_length. 
       + destruct (Z_le_dec b a); try contradiction.
         iFrame.         
         destruct (Z_le_dec a' e); try contradiction.        
         rewrite (region_size_split _ _ _ a'); auto. 
         rewrite (get_addr_from_option_addr_next _ _ a'); auto.
       + rewrite /region_size. lia. 
     - iIntros "[Hba Ha'e]".
       rewrite /region_mapsto /region_addrs.
       destruct (Z_le_dec b a),(Z_le_dec a' e),(Z_le_dec b e); try contradiction. 
       iDestruct (big_sepL2_app with "Hba Ha'e") as "Hbe".
       (* assert (region_size a' e = (region_size b e) - (region_size b a')). *)
       (* { rewrite (region_size_split a b e a'). rewrite /region_size. simpl.  } *)
       rewrite -(region_size_split a b e a'); auto. 
       rewrite -(get_addr_from_option_addr_next a b a'); auto.
       rewrite -(region_addrs_aux_decomposition (region_size b e) b (region_size b a)).
       iFrame.
       rewrite /region_size. lia.
   Qed.

   (* --------------------------------------------------------------------------------- *)
   (* ----------------------- UPDATING MULTIPLE REGION STATES ------------------------- *)
   
   Fixpoint std_update_multiple W l ρ :=
     match l with
     | [] => W
     | a :: l => std_update (std_update_multiple W l ρ) a ρ std_rel_pub std_rel_priv
     end.
   
   (* Fixpoint std_update_temp_multiple W l := *)
   (*   match l with *)
   (*   | [] => W *)
   (*   | a :: l => std_update (std_update_temp_multiple W l) a Temporary std_rel_pub std_rel_priv *)
   (*   end. *)
   Definition std_update_temp_multiple W l := std_update_multiple W l Temporary. 

   Lemma std_update_multiple_loc_sta W l ρ :
     (std_update_multiple W l ρ).2.1 = W.2.1.
   Proof.
     induction l; auto.
   Qed.      

   Lemma std_update_multiple_loc_rel W l ρ :
     (std_update_multiple W l ρ).2.2 = W.2.2.
   Proof.
     induction l; auto.
   Qed.

   Lemma std_update_multiple_swap_head W l a1 a2 ρ :
     std_update_multiple W (a1 :: a2 :: l) ρ = std_update_multiple W (a2 :: a1 :: l) ρ.
   Proof.
     induction l.
     - simpl. destruct (decide (a1 = a2)); subst.
       + done.
       + rewrite /std_update.
         assert (countable.encode a1 ≠ countable.encode a2).
         { intro Hcontr. apply encode_inj in Hcontr. subst; done. }
         repeat rewrite (insert_commute _ (countable.encode a1) (countable.encode a2)) ; auto. 
     - destruct (decide (a1 = a2)); subst;[done|].
       assert (countable.encode a1 ≠ countable.encode a2).
       { intro Hcontr. apply encode_inj in Hcontr. subst; done. }
       simpl. rewrite /std_update. 
       repeat rewrite (insert_commute _ (countable.encode a1) (countable.encode a2)) ; auto. 
   Qed. 
       
   Lemma std_update_multiple_swap W l1 a l2 ρ :
     std_update_multiple W (l1 ++ a :: l2) ρ = std_update_multiple W (a :: l1 ++ l2) ρ.
   Proof.
     induction l1; auto.
     rewrite app_comm_cons std_update_multiple_swap_head /=. 
     f_equal. auto.
   Qed.

   Lemma remove_dups_swap_head {A : Type} `{EqDecision A} (a1 a2 : A) (l : list A) :
     remove_dups (a1 :: a2 :: l) ≡ₚ remove_dups (a2 :: a1 :: l).
   Proof. 
     destruct (decide (a1 = a2)); subst; auto.
     simpl. destruct (decide_rel elem_of a1 (a2 :: l)), (decide_rel elem_of a2 (a1 :: l)).
     - apply elem_of_cons in e as [Hcontr | Hl];[subst;contradiction|].
       apply elem_of_cons in e0 as [Hcontr | Hl0];[subst;contradiction|].
       destruct (decide_rel elem_of a2 l);[|contradiction].
       destruct (decide_rel elem_of a1 l);[|contradiction].
       done.
     - apply elem_of_cons in e as [Hcontr | Hl];[subst;contradiction|].
       apply not_elem_of_cons in n0 as [Hcontr Hl0]. 
       destruct (decide_rel elem_of a2 l);[contradiction|].
       destruct (decide_rel elem_of a1 l);[|contradiction].
       done.
     - apply elem_of_cons in e as [Hcontr | Hl];[subst;contradiction|].
       apply not_elem_of_cons in n0 as [Hcontr Hl0]. 
       destruct (decide_rel elem_of a2 l);[|contradiction].
       destruct (decide_rel elem_of a1 l);[contradiction|].
       done.
     - apply not_elem_of_cons in n1 as [Hcontr Hl]. 
       apply not_elem_of_cons in n0 as [Hcontr0 Hl0]. 
       destruct (decide_rel elem_of a2 l); [contradiction|]. 
       destruct (decide_rel elem_of a1 l);[contradiction|].
       rewrite (Permutation_swap a1 a2 (remove_dups l)). done. 
   Qed. 
     
   Lemma remove_dups_swap {A : Type} `{EqDecision A} (l1 : list A) (a : A) (l2 : list A) :
     remove_dups (l1 ++ a :: l2) ≡ₚremove_dups (a :: l1 ++ l2).
   Proof.
     induction l1; auto.
     rewrite app_comm_cons remove_dups_swap_head (app_comm_cons l1 l2 a) /=.
     destruct (decide_rel elem_of a0 (l1 ++ a :: l2)).
     - rewrite decide_True;[|by rewrite Permutation_middle].
       destruct (decide_rel elem_of a (l1 ++ l2)). 
       + rewrite IHl1. simpl. rewrite decide_True; auto. 
       + rewrite IHl1. simpl. rewrite decide_False; auto.
     - rewrite decide_False;[|by rewrite Permutation_middle]. f_equiv. 
       destruct (decide_rel elem_of a (l1 ++ l2)). 
       + rewrite IHl1. simpl. rewrite decide_True; auto. 
       + rewrite IHl1. simpl. rewrite decide_False; auto.
   Qed.

   Lemma std_sta_update_multiple_lookup_same W l ρ (a : Addr) :
     a ∉ l -> (std_sta (std_update_multiple W l ρ)) !! (countable.encode a) =
             (std_sta W) !! (countable.encode a).
   Proof.
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hne Hnin].
     rewrite lookup_insert_ne; auto.
     intros Hcontr. apply encode_inj in Hcontr. subst; contradiction.
   Qed.

   Lemma std_rel_update_multiple_lookup_same W l ρ (a : Addr) :
     a ∉ l -> (std_rel (std_update_multiple W l ρ)) !! (countable.encode a) =
             (std_rel W) !! (countable.encode a).
   Proof.
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hne Hnin].
     rewrite lookup_insert_ne; auto.
     intros Hcontr. apply encode_inj in Hcontr. subst; contradiction.
   Qed. 
   
   Lemma std_update_multiple_not_in_sta W l ρ (a : Addr) :
     a ∉ l → (countable.encode a) ∈ dom (gset positive) (std_sta W) ↔
             (countable.encode a) ∈ dom (gset positive) (std_sta (std_update_multiple W l ρ)). 
   Proof. 
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hneq Hnin]. 
     split.
     - intros Hin. simpl. rewrite dom_insert.
       apply elem_of_union. right. apply IHl; auto. 
     - simpl. rewrite dom_insert. intros Hin.
       apply elem_of_union in Hin as [Hcontr | Hin].
       + apply elem_of_singleton in Hcontr. apply encode_inj in Hcontr. subst; contradiction.
       + apply IHl; auto.
   Qed. 
       
   Lemma std_update_multiple_not_in_rel W l ρ (a : Addr) :
     a ∉ l → (countable.encode a) ∈ dom (gset positive) (std_rel W) ↔
             (countable.encode a) ∈ dom (gset positive) (std_rel (std_update_multiple W l ρ)). 
   Proof. 
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hneq Hnin]. 
     split.
     - intros Hin. simpl. rewrite dom_insert.
       apply elem_of_union. right. apply IHl; auto. 
     - simpl. rewrite dom_insert. intros Hin.
       apply elem_of_union in Hin as [Hcontr | Hin].
       + apply elem_of_singleton in Hcontr. apply encode_inj in Hcontr. subst; contradiction.
       + apply IHl; auto.
   Qed. 
     
   Lemma related_sts_pub_update_multiple W l ρ :
     NoDup l →
     Forall (λ a, (countable.encode a) ∉ dom (gset positive) (std_sta W) ∧
                  (countable.encode a) ∉ dom (gset positive) (std_rel W)) l →
     related_sts_pub_world W (std_update_multiple W l ρ).
   Proof.
     intros Hdup Hforall. induction l.
     - split; apply related_sts_pub_refl. 
     - simpl. apply NoDup_cons_iff in Hdup as [Ha Hdup].
       apply list.Forall_cons in Hforall as [ [Ha_std Ha_rel] Hforall].
       eapply related_sts_pub_trans_world;[apply IHl; auto|].
       apply related_sts_pub_world_fresh; auto. 
       + intros Hcontr. apply std_update_multiple_not_in_sta in Hcontr; auto. 
         intros Hcontr'; apply elem_of_list_In in Hcontr'; contradiction.
       + intros Hcontr. apply std_update_multiple_not_in_rel in Hcontr; auto. 
         intros Hcontr'; apply elem_of_list_In in Hcontr'; contradiction.
   Qed.

   Lemma std_update_multiple_lookup W l ρ k y :
     l !! k = Some y ->
     std_sta (std_update_multiple W l ρ) !! countable.encode y = Some (countable.encode ρ)
     ∧ region_std (std_update_multiple W l ρ) y.
   Proof.
     intros Helem.
     apply elem_of_list_lookup_2 in Helem.
     apply elem_of_list_split in Helem as [l1 [l2 Heq] ].
     rewrite Heq std_update_multiple_swap /= /std_update. split. 
     - rewrite /std_sta /=. apply lookup_insert.
     - rewrite /region_std /rel_is_std_i /std_rel /=. apply lookup_insert.
   Qed. 
   
   Lemma std_update_temp_multiple_lookup W l k y :
     l !! k = Some y →
     region_state_pwl (std_update_temp_multiple W l) y ∧ region_std (std_update_temp_multiple W l) y.
   Proof.
     apply std_update_multiple_lookup. 
   Qed. 
     
   Lemma std_update_multiple_dom_top_sta W n ρ a :
     a ≠ top ->
     countable.encode a ∉ dom (gset positive) (std_sta W) →
     countable.encode a ∉ dom (gset positive) (std_sta (std_update_multiple W (repeat top n) ρ)).
   Proof.
     intros Hne Hnin.
     induction n; auto.
     simpl. rewrite dom_insert. apply not_elem_of_union.
     split.
     + apply not_elem_of_singleton.
       intros Hcontr. apply encode_inj in Hcontr.
       subst. done.
     + apply IHn.
   Qed.

   Lemma std_update_multiple_dom_top_rel W n ρ a :
     a ≠ top ->
     countable.encode a ∉ dom (gset positive) (std_rel W) →
     countable.encode a ∉ dom (gset positive) (std_rel (std_update_multiple W (repeat top n) ρ)).
   Proof.
     intros Hne Hnin.
     induction n; auto.
     simpl. rewrite dom_insert. apply not_elem_of_union.
     split.
     + apply not_elem_of_singleton.
       intros Hcontr. apply encode_inj in Hcontr.
       subst. done.
     + apply IHn.
   Qed.

   Lemma region_addrs_aux_top n :
     region_addrs_aux top n = repeat top n.
   Proof.
     induction n; auto.
     simpl. f_equiv. done.
   Qed. 

   Lemma std_update_multiple_dom_sta_i W n ρ a i :
     a ≠ top → (i > 0)%Z →
     countable.encode a ∉ dom (gset positive) (std_sta W) →
     countable.encode a ∉ dom (gset positive) (std_sta (std_update_multiple W (region_addrs_aux (get_addr_from_option_addr (a + i)%a) n) ρ)).
   Proof.
     intros Hneq Hgt. 
     destruct (a + i)%a eqn:Hsome.
     - simpl.
       assert (a < a0)%a as Hlt;[apply next_lt_i with i; auto|].
       intros Hnin.
       revert Hlt Hsome. generalize i a0. induction n; auto; intros j a1 Hlt Hsome. 
       simpl. rewrite dom_insert. apply not_elem_of_union.
       split.
       + apply not_elem_of_singleton.
         intros Hcontr. apply encode_inj in Hcontr.
         subst. rewrite /lt_addr in Hlt. lia.  
       + destruct (a1 + 1)%a eqn:Ha2; simpl. 
         ++ apply IHn with (j + 1)%Z. 
            +++ apply next_lt in Ha2. rewrite /lt_addr in Hlt. rewrite /lt_addr. lia.
            +++ apply (incr_addr_trans a a1 a2 j 1) in Hsome; auto.
         ++ rewrite region_addrs_aux_top. apply std_update_multiple_dom_top_sta; auto.
     - simpl. rewrite region_addrs_aux_top. apply std_update_multiple_dom_top_sta; auto.
   Qed.

   Lemma std_update_multiple_dom_rel_i W n ρ a i :
     a ≠ top → (i > 0)%Z →
     countable.encode a ∉ dom (gset positive) (std_rel W) →
     countable.encode a ∉ dom (gset positive) (std_rel (std_update_multiple W (region_addrs_aux (get_addr_from_option_addr (a + i)%a) n) ρ)).
   Proof.
      intros Hneq Hgt. 
     destruct (a + i)%a eqn:Hsome.
     - simpl.
       assert (a < a0)%a as Hlt;[by apply next_lt_i with i|].
       intros Hnin.
       revert Hlt Hsome. generalize i a0. induction n; auto; intros j a1 Hlt Hsome. 
       simpl. rewrite dom_insert. apply not_elem_of_union.
       split.
       + apply not_elem_of_singleton.
         intros Hcontr. apply encode_inj in Hcontr.
         subst. rewrite /lt_addr in Hlt. lia.  
       + destruct (a1 + 1)%a eqn:Ha2; simpl. 
         ++ apply IHn with (j + 1)%Z. 
            +++ apply next_lt in Ha2. rewrite /lt_addr in Hlt. rewrite /lt_addr. lia.
            +++ apply (incr_addr_trans a a1 a2 j 1) in Hsome; auto.
         ++ rewrite region_addrs_aux_top. apply std_update_multiple_dom_top_rel; auto.
     - simpl. rewrite region_addrs_aux_top. apply std_update_multiple_dom_top_rel; auto.
   Qed.

   Lemma incr_addr_is_Some_weak a n :
     is_Some (a + S (S n))%a → is_Some (a + (S n))%a.
   Proof.
     intros Hsome.
     rewrite /incr_addr in Hsome. rewrite /incr_addr.
     destruct (Z_le_dec (a + S (S n))%Z MemNum); inversion Hsome; try discriminate.
     destruct (Z_le_dec (a + S n)%Z MemNum); eauto.
     clear H3 x Hsome. lia. 
   Qed.

   Lemma std_sta_update_multiple_insert W (a b a' l : Addr) ρ i r r' :
     (a' < a)%a →
     std_sta (std_update_multiple (std_update W a' i r r') (region_addrs a b) ρ) !! (countable.encode l) =
     std_sta (std_update (std_update_multiple W (region_addrs a b) ρ) a' i r r') !! (countable.encode l).
   Proof.
     intros Hlt. 
     destruct (decide (l ∈ region_addrs a b)).
     - assert (l ≠ a') as Hne.
       { intros Hcontr. apply region_addrs_not_elem_of with _ (region_size a b) _ in Hlt.
         subst. rewrite /region_addrs in e. destruct (Z_le_dec a b); first contradiction.
         apply elem_of_nil in e. done. }
       apply elem_of_list_lookup in e as [n Hsome].
       assert (std_sta (std_update_multiple W (region_addrs a b) ρ) !! countable.encode l = Some (countable.encode ρ)
               ∧ region_std (std_update_multiple W (region_addrs a b) ρ) l) as [Hpwl _].
       { apply std_update_multiple_lookup with n. auto. }
       assert (std_sta (std_update_multiple (std_update W a' i r r') (region_addrs a b) ρ) !! countable.encode l = Some (countable.encode ρ)
               ∧ region_std (std_update_multiple (std_update W a' i r r') (region_addrs a b) ρ) l) as [Hpwl' _].
       { apply std_update_multiple_lookup with n. auto. }
       rewrite /region_state_pwl /= in Hpwl. rewrite /region_state_pwl /= in Hpwl'.
       rewrite -Hpwl in Hpwl'. rewrite Hpwl'. 
       rewrite lookup_insert_ne; auto. 
       intros Hcontr. apply encode_inj in Hcontr. subst. contradiction.
     - rewrite std_sta_update_multiple_lookup_same; auto. 
       destruct (decide (countable.encode a' = countable.encode l)).
       + rewrite /std_update /std_sta /= e. do 2 rewrite lookup_insert. done.
       + rewrite /std_update /std_sta /=. rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne; auto.
         rewrite std_sta_update_multiple_lookup_same; auto.
   Qed.

   Lemma std_rel_update_multiple_insert W (a b a' l : Addr) ρ i r r' :
     (a' < a)%a →
     std_rel (std_update_multiple (std_update W a' i r r') (region_addrs a b) ρ) !! (countable.encode l) =
     std_rel (std_update (std_update_multiple W (region_addrs a b) ρ) a' i r r') !! (countable.encode l).
   Proof.
     intros Hlt. 
     destruct (decide (l ∈ region_addrs a b)).
     - assert (l ≠ a') as Hne.
       { intros Hcontr. apply region_addrs_not_elem_of with _ (region_size a b) _ in Hlt.
         subst. rewrite /region_addrs in e. destruct (Z_le_dec a b); first contradiction.
         apply elem_of_nil in e. done. }
       apply elem_of_list_lookup in e as [n Hsome].
       assert (std_sta (std_update_multiple W (region_addrs a b) ρ) !! countable.encode l = Some (countable.encode ρ)
               ∧ region_std (std_update_multiple W (region_addrs a b) ρ) l) as [_ Hstd].
       { apply std_update_multiple_lookup with n. auto. }
       assert (std_sta (std_update_multiple (std_update W a' i r r') (region_addrs a b) ρ) !! countable.encode l = Some (countable.encode ρ)
               ∧ region_std (std_update_multiple (std_update W a' i r r') (region_addrs a b) ρ) l) as [_ Hstd'].
       { apply std_update_multiple_lookup with n. auto. }
       rewrite /region_std /rel_is_std_i /= in Hstd. rewrite /region_std /rel_is_std_i /= in Hstd'.
       rewrite -Hstd in Hstd'. rewrite Hstd'. 
       rewrite lookup_insert_ne; auto. 
       intros Hcontr. apply encode_inj in Hcontr. subst. contradiction.
     - rewrite std_rel_update_multiple_lookup_same; auto. 
       destruct (decide (countable.encode a' = countable.encode l)).
       + rewrite /std_update /std_rel /= e. do 2 rewrite lookup_insert. done.
       + rewrite /std_update /std_rel /=. rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne; auto.
         rewrite std_rel_update_multiple_lookup_same; auto.
   Qed. 
       
   Lemma std_update_multiple_dom_insert W (a b a' : Addr) i r :
     (a' < a)%a →
     Forall (λ a : Addr,
                   (countable.encode a ∉ dom (gset positive) (std_sta W))
                   ∧ countable.encode a ∉ dom (gset positive) (std_rel W)) (region_addrs a b) →
     Forall (λ a : Addr,
                   (countable.encode a ∉ dom (gset positive) (<[countable.encode a' := i]> W.1.1))
                   ∧ countable.encode a ∉ dom (gset positive) (<[countable.encode a' := r]> W.1.2)) (region_addrs a b).
   Proof.
     intros Hlt. 
     do 2 (rewrite list.Forall_forall). intros Hforall.  
     intros x Hin.
     assert (x ≠ a') as Hne.
     { intros Hcontr; subst.
       apply region_addrs_not_elem_of with _ (region_size a b) _ in Hlt.
       rewrite /region_addrs in Hin.
       destruct (Z_le_dec a b);[contradiction|apply elem_of_nil in Hin; auto].
     }
     destruct Hforall with x as [Hsta Hrel];auto. split.
     - rewrite dom_insert. apply not_elem_of_union.
       split;auto. apply not_elem_of_singleton.
       intros Hcontr. apply encode_inj in Hcontr. contradiction. 
     - rewrite dom_insert. apply not_elem_of_union.
       split;auto. apply not_elem_of_singleton.
       intros Hcontr. apply encode_inj in Hcontr. contradiction.
   Qed. 
  
   (* -------------------- ALLOCATING A NEW REGION OF ZEROES ------------------ *)
   
   Lemma region_addrs_zeroes_alloc_aux E a W p (n : nat) :
     p ≠ O → is_Some (a + (Z.of_nat n - 1))%a →
     Forall (λ a, (countable.encode a) ∉ dom (gset positive) (std_sta W) ∧
                  (countable.encode a) ∉ dom (gset positive) (std_rel W)) (region_addrs_aux a n) →
     ([∗ list] a0 ∈ region_addrs_aux a n, a0 ↦ₐ[p] inl 0%Z)
       -∗ region W
       -∗ sts_full_world sts_std W
     ={E}=∗ ([∗ list] x ∈ region_addrs_aux a n, read_write_cond x p (fixpoint interp1))
         ∗ region (std_update_temp_multiple W (region_addrs_aux a n))
         ∗ sts_full_world sts_std (std_update_temp_multiple W (region_addrs_aux a n)).
   Proof.
     iInduction (n) as [n | n] "IHn" forall (a W).
     - simpl. iIntros (_ _ _) "_ Hr Hsts". iFrame. done. 
     - iIntros (Hne Hnext Hforall) "Hlist Hr Hsts".
       iDestruct "Hlist" as "[Ha Hlist]".
       simpl in Hforall.
       apply list.Forall_cons in Hforall as [ [Hasta Harel] Hforall].
       destruct (pwl p) eqn:Hpwl. 
       + iAssert (∀ W, interp W (inl 0%Z))%I as "#Hav".
         { iIntros (W'). rewrite fixpoint_interp1_eq. eauto. }
         (* if n is 0 we do not need to use IH *)
         destruct n.
         { simpl. iFrame. 
           iMod (extend_region_temp_pwl E _ a p (inl 0%Z) (λ Wv, interp Wv.1 Wv.2)
                 with "[] Hsts Hr Ha Hav") as "(Hr & Ha & Hsts)"; auto.
           { iAlways. iIntros (W1 W2 Hrelated) "Hv /=". do 2 (rewrite fixpoint_interp1_eq /=). done. }
           iFrame. done.
         }         
         iMod ("IHn" with "[] [] [] Hlist Hr Hsts") as "(Hlist & Hr & Hsts)"; auto.
         { iPureIntro.
           rewrite Nat2Z.inj_succ -Z.add_1_l in Hnext.
           destruct (a + 1)%a eqn:Hsome.
           - rewrite Nat2Z.inj_succ -Z.add_1_r Z.add_simpl_r. 
             rewrite Z.add_simpl_l Nat2Z.inj_succ -Z.add_1_r Z.add_comm (addr_add_assoc a a0) in Hnext; auto. 
           - apply incr_addr_one_none in Hsome. subst.
             rewrite /incr_addr Z.add_simpl_l Nat2Z.inj_succ -Z.add_1_r in Hnext.
             destruct (Z_le_dec (top + (n + 1))%Z MemNum); inversion Hnext; try discriminate.
             exfalso. clear Hnext x H3. rewrite /top /= in l. lia. }
         iFrame. rewrite Nat2Z.inj_succ -Z.add_1_r Z.add_simpl_r in Hnext.
         iMod (extend_region_temp_pwl E _ a p (inl 0%Z) (λ Wv, interp Wv.1 Wv.2)
                 with "[] Hsts Hr Ha Hav") as "(Hr & Ha & Hsts)"; auto.
         { apply (std_update_multiple_dom_sta_i _ (S n) _ _ 1); auto;[|lia]. apply next_lt_top with (S n); auto. lia. }
         { apply (std_update_multiple_dom_rel_i _ (S n) _ _ 1); auto;[|lia]. apply next_lt_top with (S n); auto. lia. }
         { iAlways. iIntros (W1 W2 Hrelated) "Hv /=". do 2 (rewrite fixpoint_interp1_eq /=). done. }
         iFrame. done.
       + iAssert (∀ W, interp W (inl 0%Z))%I as "#Hav".
         { iIntros (W'). rewrite fixpoint_interp1_eq. eauto. }
         (* if n is 0 we do not need to use IH *)
         destruct n.
         { simpl. iFrame. 
           iMod (extend_region_temp_nwl E _ a p (inl 0%Z) (λ Wv, interp Wv.1 Wv.2)
                 with "[] Hsts Hr Ha Hav") as "(Hr & Ha & Hsts)"; auto.
           { iAlways. iIntros (W1 W2 Hrelated) "Hv /=". do 2 (rewrite fixpoint_interp1_eq /=). done. }
           iFrame. done.
         }         
         iMod ("IHn" with "[] [] [] Hlist Hr Hsts") as "(Hlist & Hr & Hsts)"; auto.
         { iPureIntro.
           rewrite Nat2Z.inj_succ -Z.add_1_l in Hnext.
           destruct (a + 1)%a eqn:Hsome.
           - rewrite Nat2Z.inj_succ -Z.add_1_r Z.add_simpl_r. 
             rewrite Z.add_simpl_l Nat2Z.inj_succ -Z.add_1_r Z.add_comm (addr_add_assoc a a0) in Hnext; auto. 
           - apply incr_addr_one_none in Hsome. subst.
             rewrite /incr_addr Z.add_simpl_l Nat2Z.inj_succ -Z.add_1_r in Hnext.
             destruct (Z_le_dec (top + (n + 1))%Z MemNum); inversion Hnext; try discriminate.
             exfalso. clear Hnext x H3. rewrite /top /= in l. lia. }
         iFrame. rewrite Nat2Z.inj_succ -Z.add_1_r Z.add_simpl_r in Hnext.
         iMod (extend_region_temp_nwl E _ a p (inl 0%Z) (λ Wv, interp Wv.1 Wv.2)
                 with "[] Hsts Hr Ha Hav") as "(Hr & Ha & Hsts)"; auto.
         { apply (std_update_multiple_dom_sta_i _ (S n) _ _ 1); auto;[|lia]. apply next_lt_top with (S n); auto. lia. }
         { apply (std_update_multiple_dom_rel_i _ (S n) _ _ 1); auto;[|lia]. apply next_lt_top with (S n); auto. lia. }
         { iAlways. iIntros (W1 W2 Hrelated) "Hv /=". do 2 (rewrite fixpoint_interp1_eq /=). done. }
         iFrame. done.
   Qed.

   (* creates a gmap with domain from the list, all pointing to a default value *)
   Fixpoint create_gmap_default {K V : Type} `{Countable K}
            (l : list K) (d : V) : gmap K V :=
     match l with 
     | [] => ∅
     | k :: tl => <[k:=d]> (create_gmap_default tl d)
     end.

   Lemma create_gmap_default_lookup {K V : Type} `{Countable K}
         (l : list K) (d : V) (k : K) :
     k ∈ l ↔ (create_gmap_default l d) !! k = Some d.
   Proof.
     split.
     - intros Hk.
       induction l; inversion Hk.
       + by rewrite lookup_insert.
       + destruct (decide (a = k)); [subst; by rewrite lookup_insert|]. 
         rewrite lookup_insert_ne; auto. 
     - intros Hl.
       induction l; inversion Hl.
       destruct (decide (a = k)); [subst;apply elem_of_list_here|]. 
       apply elem_of_cons. right.
       apply IHl. rewrite lookup_insert_ne in H5; auto.
   Qed.

   Lemma region_addrs_zeroes_valid_aux n W : 
     ([∗ list] y ∈ repeat (inl 0%Z) n, ▷ (fixpoint interp1) W y)%I.
   Proof. 
     iInduction (n) as [n | n] "IHn".
     - done.
     - simpl. iSplit; last iFrame "#".
       rewrite fixpoint_interp1_eq. iNext.
       eauto.
   Qed. 
     
   Lemma region_addrs_zeroes_valid (a b : Addr) W :
     ([∗ list] _;y2 ∈ region_addrs a b; region_addrs_zeroes a b,
                                        ▷ (fixpoint interp1) W y2)%I.
   Proof.
     rewrite /region_addrs /region_addrs_zeroes.
     destruct (Z_le_dec a b); last done. 
     iApply (big_sepL2_to_big_sepL_r _ _ (repeat (inl 0%Z) (region_size a b))).
     - rewrite region_addrs_aux_length.
       rewrite repeat_length. done.
     - iApply region_addrs_zeroes_valid_aux.
   Qed. 
     
   Lemma region_addrs_zeroes_trans_aux (a b : Addr) p n :
     ([∗ list] y1;y2 ∈ region_addrs_aux a n;repeat (inl 0%Z) n, y1 ↦ₐ[p] y2)
       -∗ [∗ list] y1 ∈ region_addrs_aux a n, y1 ↦ₐ[p] inl 0%Z.
   Proof.
     iInduction (n) as [n | n] "IHn" forall (a); first auto. 
     iIntros "Hlist". 
     iDestruct "Hlist" as "[Ha Hlist]".
     iFrame.
     iApply "IHn". iFrame.
   Qed.

   Lemma region_addrs_zeroes_trans (a b : Addr) p :
     ([∗ list] y1;y2 ∈ region_addrs a b;region_addrs_zeroes a b, y1 ↦ₐ[p] y2)
       -∗ [∗ list] a0 ∈ region_addrs a b, a0 ↦ₐ[p] (inl 0%Z).
   Proof.
     iIntros "Hlist".
     rewrite /region_addrs /region_addrs_zeroes.
     destruct (Z_le_dec a b); last done. 
     iApply region_addrs_zeroes_trans_aux; auto.
   Qed.

   Lemma region_addrs_zeroes_alloc E W (a b : Addr) p :
     p ≠ O → 
     Forall (λ a0 : Addr, (countable.encode a0 ∉ dom (gset positive) (std_sta W))
                          ∧ countable.encode a0 ∉ dom (gset positive) (std_rel W))
            (region_addrs a b) →
     ([∗ list] y1;y2 ∈ region_addrs a b;region_addrs_zeroes a b, y1 ↦ₐ[p] y2)
       ∗ region W ∗ sts_full_world sts_std W
     ={E}=∗ ([∗ list] a0 ∈ region_addrs a b, read_write_cond a0 p (fixpoint interp1))
         ∗ region (std_update_temp_multiple W (region_addrs a b))
         ∗ sts_full_world sts_std (std_update_temp_multiple W (region_addrs a b)).
   Proof.
     iIntros (Hne Hforall) "[Hlist [Hr Hsts] ]".
     iDestruct (region_addrs_zeroes_trans with "Hlist") as "Hlist".
     rewrite /region_addrs. rewrite /region_addrs in Hforall.
     destruct (Z_le_dec a b); last iFrame; auto.
     iMod (region_addrs_zeroes_alloc_aux with "[$Hlist] [$Hr] [$Hsts]") as "H"; auto.
     apply incr_addr_region_size in l; auto. eauto. 
   Qed.


   (* ------------------------------ OPENING A REGION ----------------------------------- *)

   Lemma disjoint_nil_l {A : Type} `{EqDecision A} (a : A) (l2 : list A) :
     [] ## l2.
   Proof.
     apply elem_of_disjoint. intros x Hcontr. inversion Hcontr.
   Qed.

   Lemma disjoint_nil_r {A : Type} `{EqDecision A} (a : A) (l2 : list A) :
     l2 ## [].
   Proof.
     apply elem_of_disjoint. intros x Hl Hcontr. inversion Hcontr.
   Qed.
   
   Lemma disjoint_cons {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
     a :: l1 ## l2 → a ∉ l2.
   Proof.
     rewrite elem_of_disjoint =>Ha.
     assert (a ∈ a :: l1) as Hs; [apply elem_of_cons;auto;apply elem_of_nil|].
     specialize (Ha a Hs). done.
   Qed.

   Lemma disjoint_weak {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
     a :: l1 ## l2 → l1 ## l2.
   Proof.
     rewrite elem_of_disjoint =>Ha a' Hl1 Hl2.
     assert (a' ∈ a :: l1) as Hs; [apply elem_of_cons;auto;apply elem_of_nil|].
     specialize (Ha a' Hs Hl2). done.
   Qed.

   Lemma disjoint_swap {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
     a ∉ l1 →
     a :: l1 ## l2 -> l1 ## a :: l2.
   Proof.
     rewrite elem_of_disjoint =>Hnin Ha a' Hl1 Hl2.
     destruct (decide (a' = a)).
     - subst. contradiction.
     - apply Ha with a'.
       + apply elem_of_cons; by right.
       + by apply elem_of_cons in Hl2 as [Hcontr | Hl2]; [contradiction|].
   Qed.

   Lemma delete_list_swap {A B : Type} `{EqDecision A, Countable A}
         (a a' : A) (l1 l2 : list A) (M : gmap A B) :
     delete a' (delete_list (l1 ++ a :: l2) M) =
     delete a (delete a' (delete_list (l1 ++ l2) M)).
   Proof.
     induction l1.
     - apply delete_commute.
     - simpl. repeat rewrite (delete_commute _ _ a0).
       f_equiv. apply IHl1.
   Qed. 
   
   Lemma open_region_many_swap a l1 l2 W :
     open_region_many (l1 ++ a :: l2) W ≡ open_region_many (a :: l1 ++ l2) W.
   Proof. 
     iInduction (l1) as [l | a' l'] "IHl"; simpl.
     - iSplit; auto.
     - iSplit.
       + iIntros "Hr /=".
         rewrite open_region_many_eq /open_region_many_def /=.
         iDestruct "Hr" as (M) "Hr".
         rewrite (delete_list_swap a a' l' l2 M).
         iExists _; iFrame.
       + iIntros "Hr /=".
         rewrite open_region_many_eq /open_region_many_def /=.
         iDestruct "Hr" as (M) "Hr".
         rewrite -(delete_list_swap a a' l' l2 M).
         iExists _; iFrame.
   Qed. 
       
   Lemma region_addrs_open_aux W l a n p :
     (∃ a', (a + (Z.of_nat n))%a = Some a') →
     region_addrs_aux a n ## l ->
     pwl p = true ->
     (Forall (λ a, (std_sta W) !! countable.encode a = Some (countable.encode Temporary)) (region_addrs_aux a n)) ->
     open_region_many l W
     -∗ sts_full_world sts_std W
     -∗ ([∗ list] a0 ∈ region_addrs_aux a n, read_write_cond a0 p (fixpoint interp1))
     -∗ ([∗ list] a0 ∈ region_addrs_aux a n,
         (∃ w : Word, a0 ↦ₐ[p] w
                         ∗ ▷ (fixpoint interp1) W w
                         ∗ ⌜p ≠ O⌝
                         ∗ ▷ future_pub_mono (λ Wv, (fixpoint interp1) Wv.1 Wv.2) w
                         ∗ sts_state_std (countable.encode a0) Temporary))
     ∗ open_region_many (region_addrs_aux a n ++ l) W
     ∗ sts_full_world sts_std W.
   Proof.
     iInduction (n) as [n | n] "IHn" forall (a l).
     - iIntros (Hne Hdisj Hpwl Hforall) "Hr Hsts #Hinv /=".
       iFrame. 
     - iIntros (Hne Hdisj Hpwl Hforall) "Hr Hsts #Hinv /=".
       iDestruct "Hinv" as "[Ha Hinv]".
       simpl in *.       
       iDestruct (region_open_next_temp_pwl with "[$Ha $Hr $Hsts]") as (v) "(Hr & Hsts & Hstate & Ha0 & #Hp & #Hmono & Hav)"; auto.
       { by apply disjoint_cons with (region_addrs_aux (get_addr_from_option_addr (a + 1)%a) n). }
       { apply Forall_inv in Hforall. done. }
       (* apply subseteq_difference_r with _ _ (↑logN.@a) in HleE; auto.  *)
       assert ((∃ a' : Addr, (get_addr_from_option_addr (a + 1) + n)%a = Some a')
               ∨ n = 0) as [Hnen | Hn0].
       { destruct Hne as [an Hne].
         assert (∃ a', (a + 1)%a = Some a') as [a' Ha'].
         { rewrite /incr_addr.
           destruct (Z_le_dec (a + 1)%Z MemNum); first eauto.
           rewrite /incr_addr in Hne.
           destruct (Z_le_dec (a + S n)%Z MemNum),an; inversion Hne.
           subst.
           assert (a + 1 ≤ MemNum)%Z; last contradiction.
           clear Hne n0 fin Hdisj Hforall.
           induction n; auto. apply IHn. lia.
         }
         destruct n.
         - by right.
         - left.
           rewrite Ha' /=. exists an.
           apply incr_addr_of_z in Ha'.
           rewrite /incr_addr in Hne.
           destruct (Z_le_dec (a + S (S n))%Z MemNum),an; inversion Hne.
           rewrite /incr_addr.
           destruct (Z_le_dec (a' + S n)%Z MemNum).
           + f_equal. apply addr_unique. lia.
           + rewrite -Ha' /= in n0. clear Hne. lia.
       }
       + apply Forall_cons_1 in Hforall as [Ha Hforall]. 
         iDestruct ("IHn" $! _ _ Hnen _ Hpwl Hforall with "Hr Hsts Hinv") as "(Hreg & Hr & Hsts)".
         iFrame "Hreg Hsts". 
         iDestruct (open_region_many_swap with "Hr") as "$".
         iExists _; iFrame "∗ #". 
       + rewrite Hn0 /=. iFrame.
         iExists _; iFrame "∗ #". 
         Unshelve.
         apply disjoint_swap; auto.
         apply not_elem_of_region_addrs_aux; [done|].
         intros Hcontr.
         rewrite Hcontr in Hne.
         destruct Hne as [a' Ha'].
         rewrite /incr_addr /= in Ha'.
         destruct (Z_le_dec (MemNum + S n)%Z MemNum),a'; inversion Ha'.
         clear fin Ha' H4. lia. 
   Qed.

   Lemma region_state_pwl_forall_temp W (l : list Addr) (φ : Addr → iProp Σ) :
     (([∗ list] a ∈ l, φ a ∧ ⌜region_state_pwl W a⌝) -∗
     ⌜Forall (λ a, (std_sta W) !! countable.encode a = Some (countable.encode Temporary)) l⌝)%I.
   Proof.
     iIntros "Hl".
     iInduction (l) as [|x l] "IH".
     - done.
     - iDestruct "Hl" as "[ [_ Ha] Hl]". iDestruct "Ha" as %Ha. 
       iDestruct ("IH" with "Hl") as %Hforall. 
       iPureIntro. apply list.Forall_cons.
       split;auto.
   Qed. 

   Lemma region_addrs_open W l a b p :
     (∃ a', (a + region_size a b)%a = Some a') →
     region_addrs a b ## l →
     pwl p = true ->
     open_region_many l W
     -∗ sts_full_world sts_std W
     -∗ ([∗ list] a0 ∈ region_addrs a b, read_write_cond a0 p (fixpoint interp1)
                                         ∧ ⌜region_state_pwl W a0⌝)
     -∗ ([∗ list] a0 ∈ region_addrs a b,
             (∃ w : Word, a0 ↦ₐ[p] w
                         ∗ ▷ (fixpoint interp1) W w
                         ∗ ⌜p ≠ O⌝
                         ∗ ▷ future_pub_mono (λ Wv, (fixpoint interp1) Wv.1 Wv.2) w
                         ∗ sts_state_std (countable.encode a0) Temporary))
     ∗ open_region_many (region_addrs a b ++ l) W
     ∗ sts_full_world sts_std W.
   Proof.
     rewrite /region_addrs.
     iIntros (Ha' Hdiff Hpwl) "Hr Hsts #Hinv".
     iDestruct (region_state_pwl_forall_temp W with "Hinv") as %Hforall. 
     destruct (Z_le_dec a b).
     - iApply (region_addrs_open_aux with "Hr Hsts"); auto.
       iApply (big_sepL_mono with "Hinv"). iIntros (n y Hlookup) "[$ _]". 
     - simpl. iFrame.
   Qed.
   
End region_macros.
