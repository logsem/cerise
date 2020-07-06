From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine Require Export addr_reg_sample region_invariants_revocation
     region_invariants_allocation multiple_updates.
From cap_machine.examples Require Export iris_extra.

Section region_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* Tthis file contains: 
          - splitting a region address (for splitting stack)
          - a definition for updating multiple region states (with some useful lemmas) 
          - allocating a region of multiple addresses (and a definition of default region values)
          - opening a region of multiple addresses 
  *)

  (* --------------------------------------------------------------------------------- *)
  (* -------------------- USEFUL LEMMA FOR STACK MANIPULATION ------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  
   Lemma stack_split (b e a : Addr) (p : Perm) (w1 w2 : list Word) :
     (b ≤ a ≤ e)%Z →
     (length w1) = (region_size b a) →
     ([[b,e]]↦ₐ[p][[w1 ++ w2]] ⊣⊢ [[b,a]]↦ₐ[p][[w1]] ∗ [[a,e]]↦ₐ[p][[w2]])%I.
   Proof with try (rewrite /region_size; solve_addr).
     intros [Hba Hae] Hsize.
     iSplit.
     - iIntros "Hbe".
       rewrite /region_mapsto /region_addrs.
       rewrite (region_addrs_aux_decomposition _ _ (region_size b a))...
       iDestruct (big_sepL2_app' with "Hbe") as "[Hba Ha'b]".
       + by rewrite region_addrs_aux_length. 
       + iFrame.
         rewrite (_: ^(b + region_size b a)%a = a)...
         rewrite (_: region_size a e = region_size b e - region_size b a)...
         (* todo: turn these two into lemmas *)
     - iIntros "[Hba Hae]".
       rewrite /region_mapsto /region_addrs. (* todo: use a proper region splitting lemma *)
       rewrite (region_addrs_aux_decomposition (region_size b e) _ (region_size b a))...
       iApply (big_sepL2_app with "Hba [Hae]"); cbn.
       rewrite (_: ^(b + region_size b a)%a = a)...
       rewrite (_: region_size b e - region_size b a = region_size a e)...
   Qed.

  
   (* -------------------- ALLOCATING A NEW REGION OF ZEROES ------------------ *)
   
   Lemma region_addrs_zeroes_alloc_aux E a W p (n : nat) :
     p ≠ O → is_Some (a + (Z.of_nat n))%a →
     Forall (λ a, a ∉ dom (gset Addr) (std W)) (region_addrs_aux a n) →
     ([∗ list] a0 ∈ region_addrs_aux a n, a0 ↦ₐ[p] inl 0%Z)
       -∗ region W
       -∗ sts_full_world W
     ={E}=∗ ([∗ list] x ∈ region_addrs_aux a n, read_write_cond x p interp)
         ∗ region (std_update_temp_multiple W (region_addrs_aux a n))
         ∗ sts_full_world (std_update_temp_multiple W (region_addrs_aux a n)).
   Proof.
     iInduction (n) as [| n] "IHn" forall (a W).
     - simpl. iIntros (_ _ _) "_ Hr Hsts". iFrame. done. 
     - iIntros (Hne Hnext Hforall) "Hlist Hr Hsts".
       iDestruct "Hlist" as "[Ha Hlist]".
       simpl in Hforall.
       apply list.Forall_cons in Hforall as [ Hasta Hforall].
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
         { iPureIntro. destruct Hnext as [? ?]. zify_addr; solve [ eauto | lia ]. }
         iFrame. destruct Hnext as [e He]. assert (a ≠ top) by (intros ->; solve_addr).
         iMod (extend_region_temp_pwl E _ a p (inl 0%Z) (λ Wv, interp Wv.1 Wv.2)
                 with "[] Hsts Hr Ha Hav") as "(Hr & Ha & Hsts)"; auto.
         { apply (std_update_multiple_dom_sta_i _ (S n) _ _ 1); auto; lia. }
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
         { iPureIntro. destruct Hnext as [? ?]. zify_addr; solve [ eauto | lia ]. }
         iFrame. destruct Hnext as [e He]. assert (a ≠ top) by (intros ->; solve_addr).
         iMod (extend_region_temp_nwl E _ a p (inl 0%Z) (λ Wv, interp Wv.1 Wv.2)
                 with "[] Hsts Hr Ha Hav") as "(Hr & Ha & Hsts)"; auto.
         { apply (std_update_multiple_dom_sta_i _ (S n) _ _ 1); auto; lia. }
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
       apply IHl. simplify_map_eq. auto. 
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

   Lemma region_addrs_zeroes_valid_aux n W : 
     ([∗ list] y ∈ replicate n (inl 0%Z), ▷ (fixpoint interp1) W y)%I.
   Proof. 
     iInduction (n) as [| n] "IHn".
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
     iApply (big_sepL2_to_big_sepL_r _ _ (region_addrs_zeroes a b)).
     - rewrite region_addrs_aux_length replicate_length //.
     - iApply region_addrs_zeroes_valid_aux.
   Qed. 
     
   Lemma region_addrs_zeroes_trans_aux (a b : Addr) p n :
     ([∗ list] y1;y2 ∈ region_addrs_aux a n;replicate n (inl 0%Z), y1 ↦ₐ[p] y2)
       -∗ [∗ list] y1 ∈ region_addrs_aux a n, y1 ↦ₐ[p] inl 0%Z.
   Proof.
     iInduction (n) as [| n] "IHn" forall (a); first auto.
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
     iApply region_addrs_zeroes_trans_aux; auto.
   Qed.

   Lemma region_addrs_zeroes_alloc E W (a b : Addr) p :
     p ≠ O → 
     Forall (λ a0 : Addr, (a0 ∉ dom (gset Addr) (std W))) (region_addrs a b) →
     ([∗ list] y1;y2 ∈ region_addrs a b;region_addrs_zeroes a b, y1 ↦ₐ[p] y2)
       ∗ region W ∗ sts_full_world W
     ={E}=∗ ([∗ list] a0 ∈ region_addrs a b, read_write_cond a0 p interp)
         ∗ region (std_update_temp_multiple W (region_addrs a b))
         ∗ sts_full_world (std_update_temp_multiple W (region_addrs a b)).
   Proof.
     iIntros (Hne Hforall) "[Hlist [Hr Hsts] ]".
     iDestruct (region_addrs_zeroes_trans with "Hlist") as "Hlist". 
     rewrite /region_addrs. rewrite /region_addrs in Hforall. 
     iMod (region_addrs_zeroes_alloc_aux with "[$Hlist] [$Hr] [$Hsts]") as "H"; auto.
     rewrite /region_size. zify_addr; eauto; lia. 
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
     iInduction (l1) as [| a' l'] "IHl"; simpl.
     - iSplit; auto.
     - iSplit.
       + iIntros "Hr /=".
         rewrite open_region_many_eq /open_region_many_def /=.
         iDestruct "Hr" as (M Mρ) "Hr".
         rewrite (delete_list_swap a a' l' l2 M).
         rewrite (delete_list_swap a a' l' l2 Mρ).
         iExists M,Mρ. iFrame.
       + iIntros "Hr /=".
         rewrite open_region_many_eq /open_region_many_def /=.
         iDestruct "Hr" as (M Mρ) "Hr".
         rewrite -(delete_list_swap a a' l' l2 M).
         rewrite -(delete_list_swap a a' l' l2 Mρ).         
         iExists M,Mρ; iFrame.
   Qed. 
       
   Lemma region_addrs_open_aux W l a n p :
     (∃ a', (a + (Z.of_nat n))%a = Some a') →
     region_addrs_aux a n ## l ->
     pwl p = true ->
     (Forall (λ a, (std W) !! a = Some Temporary) (region_addrs_aux a n)) ->
     open_region_many l W
     -∗ sts_full_world W
     -∗ ([∗ list] a0 ∈ region_addrs_aux a n, read_write_cond a0 p (fixpoint interp1))
     -∗ ([∗ list] a0 ∈ region_addrs_aux a n,
         (∃ w : Word, a0 ↦ₐ[p] w
                         ∗ ▷ (fixpoint interp1) W w
                         ∗ ⌜p ≠ O⌝
                         ∗ ▷ future_pub_mono (λ Wv, (fixpoint interp1) Wv.1 Wv.2) w
                         ∗ sts_state_std a0 Temporary))
     ∗ open_region_many (region_addrs_aux a n ++ l) W
     ∗ sts_full_world W.
   Proof.
     iInduction (n) as [| n] "IHn" forall (a l).
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
       { destruct Hne as [an Hne]. zify_addr; solve [ eauto | lia ]. }
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
         destruct Hne as [a' Ha']. solve_addr. 
   Qed.

   Lemma region_state_pwl_forall_temp W (l : list Addr) (φ : Addr → iProp Σ) :
     (([∗ list] a ∈ l, φ a ∧ ⌜region_state_pwl W a⌝) -∗
     ⌜Forall (λ a, (std W) !! a = Some Temporary) l⌝)%I.
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
     -∗ sts_full_world W
     -∗ ([∗ list] a0 ∈ region_addrs a b, read_write_cond a0 p (fixpoint interp1)
                                         ∧ ⌜region_state_pwl W a0⌝)
     -∗ ([∗ list] a0 ∈ region_addrs a b,
             (∃ w : Word, a0 ↦ₐ[p] w
                         ∗ ▷ (fixpoint interp1) W w
                         ∗ ⌜p ≠ O⌝
                         ∗ ▷ future_pub_mono (λ Wv, (fixpoint interp1) Wv.1 Wv.2) w
                         ∗ sts_state_std a0 Temporary))
     ∗ open_region_many (region_addrs a b ++ l) W
     ∗ sts_full_world W.
   Proof.
     rewrite /region_addrs.
     iIntros (Ha' Hdiff Hpwl) "Hr Hsts #Hinv".
     iDestruct (region_state_pwl_forall_temp W with "Hinv") as %Hforall. 
     iApply (region_addrs_open_aux with "Hr Hsts"); auto.
     iApply (big_sepL_mono with "Hinv"). iIntros (n y Hlookup) "[$ _]". 
   Qed.
   
End region_macros.
