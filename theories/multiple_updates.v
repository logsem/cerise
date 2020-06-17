From iris.proofmode Require Import tactics.
From cap_machine Require Export region_invariants_revocation.
From cap_machine Require Import logrel. 
Require Import Eqdep_dec List.
From stdpp Require Import countable.

Section std_updates. 

  (* --------------------------------------------------------------------------------- *)
  (* ----------------------- UPDATING MULTIPLE REGION STATES ------------------------- *)

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.
  
  Fixpoint std_update_multiple W l ρ :=
    match l with
    | [] => W
    | a :: l => std_update (std_update_multiple W l ρ) a ρ
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

   Lemma std_update_multiple_loc W l ρ :
     (std_update_multiple W l ρ).2 = W.2. 
   Proof.
     induction l; auto. 
   Qed.

   Lemma std_update_multiple_proj_eq W Wloc l ρ :
     ((std_update_multiple W l ρ).1, Wloc) = std_update_multiple (W.1,Wloc) l ρ.
   Proof.
     destruct W as [Wsta Wloc']. simpl. induction l; auto. 
     simpl. rewrite -IHl. auto.
   Qed.

   Lemma std_update_multiple_std_sta_eq W Wloc l ρ :
     (std_update_multiple W l ρ).1 = (std_update_multiple (W.1, Wloc) l ρ).1.
   Proof.
     destruct W as [Wsta Wloc']. simpl. induction l; auto. 
     simpl. rewrite -IHl. auto.
   Qed.
   
   Lemma std_update_multiple_swap_head W l a1 a2 ρ :
     std_update_multiple W (a1 :: a2 :: l) ρ = std_update_multiple W (a2 :: a1 :: l) ρ.
   Proof.
     induction l.
     - simpl. destruct (decide (a1 = a2)); subst.
       + done.
       + rewrite /std_update.
         repeat rewrite (insert_commute _ a1 a2); auto.
     - destruct (decide (a1 = a2)); subst;[done|].
       simpl. rewrite /std_update.
       repeat rewrite (insert_commute _ a1 a2) ; auto.
   Qed. 
       
   Lemma std_update_multiple_swap W l1 a l2 ρ :
     std_update_multiple W (l1 ++ a :: l2) ρ = std_update_multiple W (a :: l1 ++ l2) ρ.
   Proof.
     induction l1; auto.
     rewrite app_comm_cons std_update_multiple_swap_head /=. 
     f_equal;auto.
   Qed.


   Lemma std_update_multiple_permutation W l1 l2 ρ :
     l1 ≡ₚ l2 →
     std_update_multiple W l1 ρ = std_update_multiple W l2 ρ.
   Proof.
     intros Hperm. 
     induction Hperm using Permutation_ind.
     - done.
     - simpl. rewrite IHHperm. done. 
     - apply (std_update_multiple_swap_head W l y x).
     - by rewrite IHHperm1 IHHperm2.
   Qed.

   Global Instance std_update_multiple_Permutation W ρ :
     Proper (Permutation ==> eq) (λ l, std_update_multiple W l ρ).
   Proof. intros y1 y2 Hperm. simpl. by apply std_update_multiple_permutation. Defined.

   
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

   (* --------------------------------------------------------------------------------------------------------- *)
   (* Lookup Lemmas: for each lookup lemma, we will have a version with addresses, and a version with positives *)
   (* --------------------------------------------------------------------------------------------------------- *)

   (* If an element is not in the update list, the state lookup is the same *)
   Lemma std_sta_update_multiple_lookup_same_i W l ρ i :
     i ∉ l -> (std (std_update_multiple W l ρ)) !! i =
             (std W) !! i.
   Proof.
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hne Hnin].
     rewrite lookup_insert_ne; auto.
   Qed.

   (* ------------------------------------------------------------ *)

   (* If an element is in the update list, the state lookup corresponds to the update value *)
   Lemma std_sta_update_multiple_lookup_in_i W l ρ i :
     i ∈ l -> (std (std_update_multiple W l ρ)) !! i = Some ρ.
   Proof.
     intros Hnin.
     induction l; auto; first inversion Hnin.
     apply elem_of_cons in Hnin as [Hne | Hnin].
     - subst i. rewrite lookup_insert; auto.
     - destruct (decide (a = i));[subst i; rewrite lookup_insert; auto|].
       rewrite lookup_insert_ne;auto. 
   Qed.

   (* ------------------------------------------------------------ *)

   (* if W at a is_Some, the the updated W at a is_Some *)
   Lemma std_sta_update_multiple_is_Some W l ρ i :
     is_Some (std W !! i) -> is_Some (std (std_update_multiple W l ρ) !! i).
   Proof.
     intros Hsome.
     destruct (decide (i ∈ l)).
     - exists ρ. by apply std_sta_update_multiple_lookup_in_i.
     - rewrite std_sta_update_multiple_lookup_same_i;auto.
   Qed. 

   (* ------------------------------------------------------------ *)
   
   (* domains *)
   Lemma std_update_multiple_not_in_sta_i W l ρ i :
     i ∉ l → i ∈ dom (gset Addr) (std W) ↔
               i ∈ dom (gset Addr) (std (std_update_multiple W l ρ)). 
   Proof.
     intros Hnin. induction l; auto.
     apply not_elem_of_cons in Hnin as [Hneq Hnin].
     rewrite /= dom_insert. set_solver.
   Qed.
   Lemma std_update_multiple_in_sta_i W (l: list Addr) ρ i :
     Forall (λ (a:Addr), is_Some (std W !! a)) l →
     i ∈ dom (gset Addr) (std W) ↔ i ∈ dom (gset Addr) (std (std_update_multiple W l ρ)).
   Proof.
     intros Hl.
     induction l; auto.
     apply Forall_cons_1 in Hl as [Ha Hll].
     cbn. rewrite dom_insert. split; [ set_solver |].
     rewrite elem_of_union elem_of_singleton. intros [-> | Hi]; [| set_solver].
     rewrite -elem_of_gmap_dom //.
   Qed.
   Lemma std_update_multiple_not_in_sta W l ρ (a : Addr) :
     a ∉ l → a ∈ dom (gset Addr) (std W) ↔
             a ∈ dom (gset Addr) (std (std_update_multiple W l ρ)).
   Proof. 
     intros Hnin.
     apply std_update_multiple_not_in_sta_i. 
     intros Hcontr. contradiction.
   Qed.
   
   (* ---------------------------------------------------------------------------- *)
   (* Some helper lemmas for various lemmas about using multiple updates in region *)

   Lemma related_sts_pub_update_multiple W l ρ :
     Forall (λ a, a ∉ dom (gset Addr) (std W)) l →
     related_sts_pub_world W (std_update_multiple W l ρ).
   Proof.
     intros Hforall. induction l.
     - apply related_sts_pub_refl_world. 
     - simpl.
       apply list.Forall_cons in Hforall as [ Ha_std Hforall].
       eapply related_sts_pub_trans_world;[apply IHl; auto|].
       destruct (decide (a ∈ l)).
       { rewrite (_: <s[a:=ρ]s>(std_update_multiple W l ρ) = std_update_multiple W l ρ) /=.
         by apply related_sts_pub_refl_world.
         rewrite /std_update insert_id /=. by destruct (std_update_multiple W l ρ).
         by apply std_sta_update_multiple_lookup_in_i. }
       apply related_sts_pub_world_fresh; auto.
       intros Hcontr. apply std_update_multiple_not_in_sta in Hcontr; auto.
   Qed.

   Lemma std_update_multiple_lookup W l ρ k y :
     l !! k = Some y ->
     std (std_update_multiple W l ρ) !! y = Some ρ.
   Proof.
     intros Helem.
     apply elem_of_list_lookup_2 in Helem.
     apply elem_of_list_split in Helem as [l1 [l2 Heq] ].
     rewrite Heq std_update_multiple_swap /= /std_update. 
     rewrite /std /=. rewrite lookup_insert. auto. 
   Qed. 
   
   Lemma std_update_temp_multiple_lookup W l k y :
     l !! k = Some y →
     region_state_pwl (std_update_temp_multiple W l) y.
   Proof.
     apply std_update_multiple_lookup. 
   Qed.
   

   (* Multiple updates does not change dom, as long as the updated elements are a subset of original dom *)
   Lemma std_update_multiple_dom_equal W l ρ :
     (∀ i : Addr, i ∈ l → i ∈ dom (gset Addr) (std W)) ->
     dom (gset Addr) (std W) = dom (gset Addr) (std (std_update_multiple W l ρ)). 
   Proof.
     intros Hsub.
     induction l; auto. 
     rewrite /= /std_update.
     rewrite dom_insert_L.
     assert (a ∈ a :: l) as Hin.
     { apply elem_of_cons. by left. }
     pose proof (Hsub _ Hin) as Hain. etrans;[apply IHl|].
     - intros i Hi. apply Hsub. apply elem_of_cons. by right. 
     - set_solver.
   Qed.

   (* In general, the domain is a subset of the updated domain *)
   Lemma std_update_multiple_sta_dom_subseteq W l ρ :
     dom (gset Addr) (std W) ⊆ dom (gset Addr) (std (std_update_multiple W l ρ)).
   Proof.
     apply elem_of_subseteq. intros x Hx.
     destruct (decide (x ∈ l)).
     - apply elem_of_gmap_dom. exists ρ.
       apply std_sta_update_multiple_lookup_in_i; auto.
     - apply std_update_multiple_not_in_sta_i; auto.
   Qed.

   Lemma std_update_multiple_std_sta_dom_monotone W W' l ρ :
     dom (gset Addr) (std W) ⊆ dom (gset Addr) (std W') ->
     dom (gset Addr) (std (std_update_multiple W l ρ)) ⊆ dom (gset Addr) (std (std_update_multiple W' l ρ)).
   Proof.
     induction l;auto. 
     simpl. repeat rewrite dom_insert_L. set_solver.
   Qed.
     
   Lemma std_update_mutiple_related_monotone W W' l ρ :
     related_sts_pub_world W W' ->
     related_sts_pub_world (std_update_multiple W l ρ) (std_update_multiple W' l ρ).
   Proof.
     intros Hrelated.
     destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ].
     destruct W' as [ Wstd_sta' [Wloc_sta' Wloc_rel'] ]. 
     destruct Hrelated as [ [Hstd_dom1 Hstd_related ] Hloc_related].
     simpl in *.
     split;[clear Hloc_related|by repeat rewrite std_update_multiple_loc_rel std_update_multiple_loc_sta].
     split. 
     - apply std_update_multiple_std_sta_dom_monotone. auto.
     - intros i x y Hx Hy.
       destruct (decide (i ∈ l)).
       + rewrite std_sta_update_multiple_lookup_in_i in Hx;auto.
         rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
         inversion Hx; inversion Hy; subst. left.
       + rewrite std_sta_update_multiple_lookup_same_i /std /= in Hx;auto.
         rewrite std_sta_update_multiple_lookup_same_i /std /= in Hy;auto.
         apply Hstd_related with i; auto. 
   Qed. 
 
   (* lemmas for updating a repetition of top *)
   Lemma std_update_multiple_dom_top_sta W n ρ a :
     a ≠ top ->
     a ∉ dom (gset Addr) (std W) →
     a ∉ dom (gset Addr) (std (std_update_multiple W (repeat top n) ρ)).
   Proof.
     intros Hne Hnin.
     induction n; auto.
     simpl. rewrite dom_insert. apply not_elem_of_union.
     split.
     + apply not_elem_of_singleton.
       intros Hcontr. done. 
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
     a ∉ dom (gset Addr) (std W) →
     a ∉ dom (gset Addr) (std (std_update_multiple W (region_addrs_aux (get_addr_from_option_addr (a + i)%a) n) ρ)).
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
         intros Hcontr. subst. rewrite /lt_addr in Hlt. lia.  
       + destruct (a1 + 1)%a eqn:Ha2; simpl. 
         ++ apply IHn with (j + 1)%Z. 
            +++ apply next_lt in Ha2. rewrite /lt_addr in Hlt. rewrite /lt_addr. lia.
            +++ apply (incr_addr_trans a a1 a2 j 1) in Hsome; auto.
         ++ rewrite region_addrs_aux_top. apply std_update_multiple_dom_top_sta; auto.
     - simpl. rewrite region_addrs_aux_top. apply std_update_multiple_dom_top_sta; auto.
   Qed.

   Lemma incr_addr_is_Some_weak a n :
     is_Some (a + S (S n))%a → is_Some (a + (S n))%a.
   Proof.
     intros Hsome.
     rewrite /incr_addr in Hsome. rewrite /incr_addr.
     destruct (Z_le_dec (a + S (S n))%Z MemNum),(Z_le_dec 0 (a + S (S n)))%Z; inversion Hsome; try discriminate.
     - destruct (Z_le_dec (a + S n)%Z MemNum),(Z_le_dec 0 (a + S n)%Z); eauto;
         clear H x Hsome;zify_addr;lia.
     - destruct (Z_le_dec (a + S n)%Z MemNum),(Z_le_dec 0 (a + S n)%Z); eauto;
         clear H x Hsome;zify_addr;lia.
   Qed.

   Lemma std_sta_update_multiple_insert W (a b a' l : Addr) ρ i :
     (a' < a)%a →
     std (std_update_multiple (std_update W a' i) (region_addrs a b) ρ) !! l =
     std (std_update (std_update_multiple W (region_addrs a b) ρ) a' i) !! l.
   Proof.
     intros Hlt. 
     destruct (decide (l ∈ region_addrs a b)).
     - assert (l ≠ a') as Hne.
       { intros ->. apply region_addrs_not_elem_of with _ (region_size a b) _ in Hlt.
         rewrite /region_addrs // in e. }
       apply elem_of_list_lookup in e as [n Hsome].
       assert (std (std_update_multiple W (region_addrs a b) ρ) !! l = Some ρ) as Hpwl.
       { apply std_update_multiple_lookup with n. auto. }
       assert (std (std_update_multiple (std_update W a' i) (region_addrs a b) ρ) !! l = Some ρ) as Hpwl'.
       { apply std_update_multiple_lookup with n. auto. }
       rewrite /region_state_pwl /= in Hpwl. rewrite /region_state_pwl /= in Hpwl'.
       rewrite -Hpwl in Hpwl'. rewrite Hpwl'. 
       rewrite lookup_insert_ne; auto. 
     - rewrite std_sta_update_multiple_lookup_same_i; auto. 
       destruct (decide ( a' =  l)).
       + rewrite /std_update /std /= e. do 2 rewrite lookup_insert. done.
       + rewrite /std_update /std /=. rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne; auto.
         rewrite std_sta_update_multiple_lookup_same_i; auto.
   Qed.
       
   Lemma std_update_multiple_dom_insert W (a b a' : Addr) i :
     (a' < a)%a →
     Forall (λ a : Addr,
                   (a ∉ dom (gset Addr) (std W))) (region_addrs a b) →
     Forall (λ a : Addr,
                   (a ∉ dom (gset Addr) (<[ a' := i]> W.1))) (region_addrs a b).
   Proof.
     intros Hlt. 
     do 2 (rewrite list.Forall_forall). intros Hforall.  
     intros x Hin.
     assert (x ≠ a') as Hne.
     { intros Hcontr; subst.
       apply region_addrs_not_elem_of with _ (region_size a b) _ in Hlt.
       rewrite /region_addrs // in Hin. }
     apply Hforall with x in Hin.
     rewrite dom_insert. apply not_elem_of_union.
     split;auto. apply not_elem_of_singleton.
     intros Hcontr. contradiction. 
   Qed. 

   (* commuting updates and revoke *)

   Lemma std_update_multiple_revoke_commute W (l: list Addr) ρ :
     ρ ≠ Temporary →
     std_update_multiple (revoke W) l ρ = revoke (std_update_multiple W l ρ).
   Proof.
     intros Hne.
     induction l; auto; simpl.
     rewrite IHl. 
     rewrite /std_update /revoke /loc /std /=. repeat f_equiv.
     eapply (map_leibniz (M:=gmap Addr) (A:=region_type)). intros i. apply leibniz_equiv_iff.
     destruct (decide (a = i)).
     - subst. rewrite lookup_insert revoke_monotone_lookup_same;rewrite lookup_insert; auto.
       intros Hcontr; inversion Hcontr as [Hcontr']. done. 
     - rewrite lookup_insert_ne;auto.
       apply revoke_monotone_lookup. rewrite lookup_insert_ne;auto. Unshelve. apply _. 
   Qed.

   (* std_update_multiple and app *)

   Lemma std_update_multiple_app W (l1 l2 : list Addr) ρ :
     std_update_multiple W (l1 ++ l2) ρ = std_update_multiple (std_update_multiple W l1 ρ) l2 ρ.
   Proof.
     induction l2; auto.
     - by rewrite app_nil_r /=. 
     - rewrite std_update_multiple_swap /=. f_equal. auto. 
   Qed.

   Lemma std_update_multiple_app_commute W (l1 l2 : list Addr) ρ :
     std_update_multiple W (l1 ++ l2) ρ = std_update_multiple W (l2 ++ l1) ρ.
   Proof.
     induction l2.
     - by rewrite app_nil_r /=.
     - rewrite std_update_multiple_swap /=. by rewrite IHl2. 
   Qed.

   (* Helper lemmas about permutation *)

   Lemma elements_permutation A C `{Empty C, Union C, Singleton A C, Elements A C,ElemOf A C, EqDecision A, FinSet A C} (l: list A) :
     NoDup l ->
     elements (list_to_set l) ≡ₚl.
   Proof. 
     intros Hdup.
     induction l. 
     - by rewrite /= elements_empty. 
     - apply NoDup_cons_iff in Hdup as [Hnin Hdup].
       rewrite /= elements_union_singleton; auto. 
       apply not_elem_of_list_to_set.
       intros Hcontr. apply elem_of_list_In in Hcontr.
       done.
   Qed.        
     
End std_updates.
