From iris.proofmode Require Import tactics.
From cap_machine Require Import addr_reg_sample. 


(* This file contains definition and lemmas for contiguous address regions *)
(* It is used mainly in specs of programs where it is necessary to assume  *)
(* that some program lies in memory in a contiguous region                 *)

Section Contiguous.

  Definition contiguous : list Addr -> Prop :=
    λ a, (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj).

  (* The first element of the contiguous list is less than or equal to the last *)
   Lemma incr_list_lt (a : list Addr) (a0 an : Addr) :
    contiguous a →
    a !! 0 = Some a0 → list.last a = Some an → (a0 ≤ an)%Z.
  Proof.
    generalize a0 an. induction a as [_ | a al IHa ]; intros a0' an' Hcond Hfirst Hlast;
     first inversion Hfirst.  
    simpl in Hfirst. inversion Hfirst. subst.
    destruct al as [_ | hd tl ].
    - inversion Hlast. omega.
    - assert ((a0' :: hd :: tl) !! 0 = Some a0') as Ha0; auto.
      assert ((a0' :: hd :: tl) !! 1 = Some hd) as Ha; auto.
      rewrite /contiguous in Hcond. 
      apply Hcond with 0 a0' hd in Ha0 as Hnext; auto. 
      assert ((hd :: tl) !! 0 = Some hd) as Ha'; auto.
      assert (list.last (hd :: tl) = Some an').
      { simpl. destruct tl; auto. }
      apply IHa with hd an' in Ha'; auto.
      + assert (a0' ≤ hd)%Z.
        {  rewrite /incr_addr in Hnext.
           destruct (Z_le_dec (a0' + 1)%Z MemNum); inversion Hnext. simpl. omega. }
        apply Z.le_trans with hd; auto. 
      + intros i ai aj Hai Haj. 
        apply Hcond with (i + 1); by rewrite Nat.add_1_r.
  Qed. 

  (* The last element of a list is the same as a list where we drop fewer elements than the list *)
  Lemma last_drop_lt {A : Type} (l : list A) (i : nat) (a : A) :
    i < (length l) → list.last l = Some a → list.last (drop i l) = Some a.
  Proof.
    generalize i. induction l.
    - intros i' Hlen Hlast. inversion Hlast. 
    - intros i' Hlen Hlast. destruct i'.
      + simpl. apply Hlast.
      + simpl; simpl in Hlen. apply IHl; first omega.
        assert (0 < length l) as Hl; first lia.
        destruct l; simpl in Hl; first by apply Nat.lt_irrefl in Hl. auto.
  Qed. 

  (* The i'th element of the contiguous list is less than or equal to the last *)
  Lemma incr_list_le_middle (a : list Addr) i (ai an : Addr) :
    contiguous a →
    a !! i = Some ai → list.last a = Some an → (ai ≤ an)%Z.
  Proof.
    generalize ai. destruct i;
                     intros ai' Hcond Hi' Hlast.
    - apply incr_list_lt with a; auto. 
    - rewrite -Nat.add_1_r in Hi'.
      assert ((drop (i + 1) a) !! 0 = Some ai') as Ha.
      { rewrite -(Nat.add_0_r (i + 1)) in Hi'.
        rewrite -Hi'. apply (lookup_drop a (i + 1) 0). }
      apply incr_list_lt with _ _ an in Ha; auto.
      + intros i0 ai0 aj Hd Hd'. 
        rewrite (lookup_drop) /= in Hd. rewrite (lookup_drop) /= in Hd'.
        apply Hcond with (i + 1 + i0); auto.
        rewrite Nat.add_assoc in Hd'. done.
      + assert (is_Some (a !! (i + 1))) as Hsome; eauto. 
        apply lookup_lt_is_Some_1 in Hsome as Hlength. 
        apply last_drop_lt; auto. 
  Qed.
  
  (* If the i'th element is not the last, it is less than the last *)
  Lemma incr_list_lt_middle (a : list Addr) i (ai an : Addr) :
    contiguous a →
    a !! i = Some ai → list.last a = Some an → (ai ≠ an)%Z → (ai < an)%Z.
  Proof.
    intros Hreg Ha Hj Hne.
    assert (ai ≤ an)%Z as Hinc; first (apply incr_list_le_middle with a i; auto).
    apply Z.lt_eq_cases in Hinc as [Hlt | Heq]; auto.
    apply neq_z_of in Hne. congruence. 
  Qed.

  (* The i'th element is less than the i+1'th element *)
  Lemma incr_list_lt_succ (a : list Addr) (a0 a1 : Addr) (i : nat) :
    contiguous a →
    a !! i = Some a0 → a !! (S i) = Some a1 → (a0 < a1)%Z.
  Proof.
    intros Hcond Hi Hsi. rewrite /contiguous in Hcond. 
    specialize Hcond with i a0 a1; simpl in Hcond. 
    apply Hcond in Hi; try rewrite Nat.add_1_r; auto.
    rewrite /incr_addr in Hi.
    destruct (Z_le_dec (a0 + 1)%Z MemNum); inversion Hi. simpl. omega.
  Qed.

  (* A region_addrs_aux is contiguous *)
  Lemma region_addrs_aux_contiguous (a : Addr) (n : nat) :
    (a + n - 1 ≤ MemNum)%Z
    → contiguous (region_addrs_aux a n). 
  Proof.
    intros Hle i ai aj Hai Haj.
    apply (region_addrs_aux_next a n i ai aj) in Hai as Hnext; auto.
    destruct (ai + 1)%a eqn:Hnone; simpl in Hnext.
    - congruence.
    - assert (i + 1 < n).
      { rewrite -(region_addrs_aux_length n a).
        apply lookup_lt_is_Some_1. eauto. }
      apply incr_addr_one_none in Hnone. subst.
      assert (a + i < MemNum)%Z as Hlt;[lia|].
      apply region_addrs_lt_top with _ n _ top in Hlt; auto. 
      congruence. 
  Qed.

  Lemma region_addrs_contiguous (a b : Addr) :
    contiguous (region_addrs a b).
  Proof.
    rewrite /region_addrs.
    destruct (Z_le_dec a b).
    - apply region_addrs_aux_contiguous.
      apply incr_addr_region_size in l.
      rewrite /incr_addr in l.
      destruct (Z_le_dec (a + (region_size a b - 1))%Z MemNum);[lia|].
      inversion l. 
    - done. 
  Qed.

  Lemma contiguous_nil : contiguous [].
  Proof. done. Qed. 
  
  Lemma contiguous_weak hd a :
    contiguous (hd :: a) → contiguous a.
  Proof.
    intros Ha.
    destruct a.
    - done.
    - intros i ai aj Hai Haj.
      rewrite /contiguous in Ha. apply Ha with (S i); auto.
  Qed. 

  (* the following lemma assumes that a1 and a2 are non empty.
     if either are empty, the lemma holds trivially *)
  Lemma contiguous_app a1 a2 a1_last a2_first :
    ∀ a, a = a1 ++ a2 ->
         list.last a1 = Some a1_last →
         a2 !! 0 = Some a2_first →
         contiguous a →
         contiguous a1 ∧ contiguous a2 ∧ (a1_last + 1)%a = Some a2_first.
  Proof.
    induction a1 as [|a_first a1]; intros a Happ Hlast Hfirst Ha. 
    - split; [apply contiguous_nil|].
      rewrite app_nil_l in Happ. subst. done. 
    - destruct a as [|a_first' a];[inversion Happ|].
      split.
      + inversion Happ.
        destruct a1.
        { intros i ai aj Hai Haj. rewrite PeanoNat.Nat.add_1_r /= in Haj. done. }
        assert (last (a_first :: a0 :: a1) = last (a0 :: a1)) as Heq;[auto|].
        rewrite Heq in Hlast.         
        intros i ai aj Hai Haj.
        destruct i.
        { rewrite /contiguous in Ha.
          simpl in *; subst; inversion Hai; inversion Haj; subst. 
          apply Ha with 0; auto. }
        apply contiguous_weak in Ha as Ha'.
        specialize (IHa1 _ H1 Hlast Hfirst Ha') as [Ha1 _]. 
        by specialize (Ha1 i ai aj Hai Haj).         
      + inversion Happ as [Heq].
        apply contiguous_weak in Ha as Ha'.
        destruct a1.
        { simpl in Hlast. subst. rewrite app_nil_l in Ha. split; auto.
          inversion Hlast; subst. rewrite /contiguous in Ha. apply Ha with 0; auto. }
        assert (last (a_first :: a0 :: a1) = last (a0 :: a1)) as Heq';[auto|].
        rewrite Heq' in Hlast.     
        by specialize (IHa1 a H Hlast Hfirst Ha') as [_ Ha2].
  Qed.

  (* the following lemmas lets us split a list of length at least n + 1 into two parts *)
  Lemma take_n_last {A : Type} (a : list A) n :
    0 < n < length a -> ∃ a_last, list.last (take n a) = Some a_last.
  Proof.
    intros Hlt. 
    rewrite -head_reverse.
    assert (length (reverse (take n a)) > 0).
    { rewrite reverse_length take_length. lia. }
    destruct (reverse (take n a)); simpl; [|eauto]. 
    inversion H. 
  Qed.

  Lemma drop_n_first {A : Type} (a : list A) n :
    n < length a -> ∃ a_first, (drop n a) !! 0 = Some a_first.
  Proof.
    intros Hlt. 
    rewrite lookup_drop PeanoNat.Nat.add_0_r. 
    apply lookup_lt_is_Some_2. done. 
  Qed. 
    
  Lemma app_split {A : Type} (a : list A) n :
    0 < n < length a → ∃ a1 a2 a1_last a2_first, a = a1 ++ a2
                                             ∧ length a1 = n
                                             ∧ list.last a1 = Some a1_last
                                             ∧ a2 !! 0 = Some a2_first.
  Proof.
    intros [Hlt Hgt].
    exists (take n a),(drop n a). 
    destruct (take_n_last a n) as [a_last Ha_last]; auto. 
    destruct (drop_n_first a n) as [a_first Ha_first]; auto. 
    exists a_last, a_first. repeat (split;auto). 
    - by rewrite take_drop. 
    - rewrite take_length. lia. 
  Qed.


  (* The following lemma splits a contiguous program into two parts *)
  Context `{memG Σ, regG Σ, STSG Σ, 
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  (* Note that we are assuming that both prog1 and prog2 are nonempty *)
  Lemma contiguous_program_split prog1 prog2 (φ : Addr → Word → iProp Σ) a :
    contiguous a → 0 < length prog1 → 0 < length prog2 →
    (([∗ list] a_i;w_i ∈ a;prog1 ++ prog2, φ a_i w_i) -∗
    ∃ (a1 a2 : list Addr) (a1_last a2_first : Addr),
      ([∗ list] a_i;w_i ∈ a1;prog1, φ a_i w_i)
        ∗ ([∗ list] a_i;w_i ∈ a2;prog2, φ a_i w_i)
        ∗ ⌜contiguous a1
           ∧ contiguous a2
           ∧ a = a1 ++ a2
           ∧ list.last a1 = Some a1_last
           ∧ a2 !! 0 = Some a2_first⌝)%I. 
  Proof.
    iIntros (Ha Hprog1 Hprog2) "Hprog".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. 
    destruct (app_split a (length prog1)) as (a1 & a2 & a1_last & a2_first & Happ & Ha1 & Hlast & Hfirst). 
    { split; auto. rewrite Hlength app_length. lia. }
    iExists a1,a2,a1_last,a2_first.
    rewrite Happ.
    iDestruct (big_sepL2_app' with "Hprog") as "[Hprog1 Hprog2]"; auto.
    iFrame.
    iPureIntro.
    destruct (contiguous_app a1 a2 a1_last a2_first a) as (Hca1 & Hca2 & Heq); auto.  
  Qed. 
        
    
End Contiguous.
    
Opaque contiguous. 
