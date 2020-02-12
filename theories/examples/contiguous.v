From iris.proofmode Require Import tactics.
From cap_machine Require Import region_macros.
From cap_machine Require Import addr_reg_sample.


(* This file contains definition and lemmas for contiguous address regions *)
(* It is used mainly in specs of programs where it is necessary to assume  *)
(* that some program lies in memory in a contiguous region                 *)

Section Contiguous.

  Definition contiguous (l: list Addr): Prop :=
    ∃ a b, l = region_addrs a b.

  Inductive contiguous_between : list Addr -> Addr -> Addr -> Prop :=
    | contiguous_between_nil : ∀ a,
        contiguous_between [] a a
    | contiguous_between_cons : ∀ a a' b l,
        (a + 1)%a = Some a' ->
        contiguous_between l a' b ->
        contiguous_between (a :: l) a b.

  Lemma contiguous_between_vacuous l a b :
    contiguous_between l a b →
    (b < a)%a →
    False.
  Proof. induction 1; intros; solve_addr. Qed.

  Lemma contiguous_between_bounds l a b :
    contiguous_between l a b →
    (a <= b)%a.
  Proof.
    intros HH. generalize (contiguous_between_vacuous _ _ _ HH).
    solve_addr.
  Qed.

  Lemma contiguous_between_nil_inv l a b :
    contiguous_between l a b →
    (b <= a)%a →
    l = [].
  Proof.
    induction 1; eauto.
    destruct (Z_eq_dec a b).
    { intros. exfalso.
      eapply (contiguous_between_vacuous l a' b). 2: solve_addr. eauto. }
    { intros. exfalso. eapply contiguous_between_vacuous; eauto. solve_addr. }
  Qed.

  Lemma contiguous_between_cons_inv_first l a a' b :
    contiguous_between (a' :: l) a b →
    a' = a.
  Proof. inversion 1; eauto. Qed.

  Lemma contiguous_between_last (a : list Addr) a0 an ai :
    contiguous_between a a0 an →
    list.last a = Some ai →
    (ai + 1)%a = Some an.
  Proof.
    revert ai. induction 1 as [| * X Y].
    { inversion 1. }
    { destruct l.
      - cbn. inversion 1. inversion Y; subst. auto.
      - eauto. }
  Qed.

  Lemma contiguous_between_of_region_addrs_aux l a b n :
    l = region_addrs_aux a n →
    (a + n)%a = Some b →
    contiguous_between l a b.
  Proof.
    revert a b l. induction n.
    { intros. cbn in *. subst l. assert (a = b) as -> by solve_addr.
      constructor. }
    { intros * -> ?. cbn. eapply (contiguous_between_cons _ (^(a+1)%a)). solve_addr.
      apply IHn; auto. solve_addr. }
  Qed.

  Lemma region_addrs_aux_of_contiguous_between l a b (n:nat) :
    contiguous_between l a b →
    (a + n)%a = Some b →
    l = region_addrs_aux a n.
  Proof.
    revert a b l. induction n.
    { intros. cbn in *.
      apply (contiguous_between_nil_inv l a b); eauto; solve_addr. }
    { intros * Hl Hn. cbn.
      destruct l as [| a' l].
      { inversion Hl; subst. exfalso. solve_addr. }
      { inversion Hl; subst. f_equal. eapply (IHn _ b). 2: solve_addr.
        assert (^(a+1)%a = a'0) as -> by solve_addr. auto. } }
  Qed.

  Lemma contiguous_between_of_region_addrs l a b :
    (a <= b)%a →
    l = region_addrs a b →
    contiguous_between l a b.
  Proof.
    intros ? ->. eapply contiguous_between_of_region_addrs_aux; eauto.
    rewrite /region_size. solve_addr.
  Qed.

  Lemma region_addrs_of_contiguous_between l a b :
    contiguous_between l a b →
    l = region_addrs a b.
  Proof.
    intros.
    destruct (Z_le_dec a b).
    { eapply region_addrs_aux_of_contiguous_between; eauto.
      rewrite /region_size. solve_addr. }
    { rewrite /region_addrs (_: region_size a b = 0) /=.
      2: unfold region_size; solve_addr.
      eapply contiguous_between_nil_inv; eauto. solve_addr. }
  Qed.

  Lemma contiguous_iff_contiguous_between l :
    contiguous l ↔
    ∃ a b, contiguous_between l a b.
  Proof.
    split.
    { intros (a & b & H).
      destruct (Z_le_dec a b).
      { apply contiguous_between_of_region_addrs in H; eauto. }
      { rewrite /region_addrs (_: region_size a b = 0) in H.
        2: unfold region_size; solve_addr. cbn in *. subst l.
        exists a, a. constructor. } }
    { intros (a & b & H).
      apply region_addrs_of_contiguous_between in H. unfold contiguous.
      eauto. }
  Qed.

  Lemma contiguous_of_contiguous_between l a b :
    contiguous_between l a b →
    contiguous l.
  Proof.
    intros. rewrite contiguous_iff_contiguous_between. eauto.
  Qed.

  Lemma contiguous_spec (l: list Addr) :
      contiguous l →
      (∀ i ai aj,
       l !! i = Some ai →
       l !! (i + 1) = Some aj →
       (ai + 1)%a = Some aj).
  Proof.
    intros Hl%contiguous_iff_contiguous_between.
    destruct Hl as (a & b & H).
    induction H as [| * Ha' Hl Hind].
    { intros *. inversion 1. }
    { intros * Hi Hi'. destruct i as [| i].
      { cbn in *. inversion Hi; subst ai; clear Hi.
        destruct Hl; inversion Hi'; [ subst aj; clear Hi' ]. auto. }
      { cbn in *. eauto. } }
  Qed.

  Lemma contiguous_nil : contiguous [].
  Proof.
    rewrite contiguous_iff_contiguous_between. exists top, top. constructor.
  Qed.

  Lemma contiguous_weak hd a :
    contiguous (hd :: a) → contiguous a.
  Proof.
    rewrite !contiguous_iff_contiguous_between.
    intros (?&?&H). inversion H; eauto.
  Qed.

  Lemma contiguous_drop (a : list Addr) :
    ∀ i, contiguous a -> contiguous (drop i a).
  Proof.
    induction a; intros i Ha.
    - rewrite drop_nil. apply contiguous_nil.
    - destruct i; auto. simpl.
      apply IHa. by apply contiguous_weak with a.
  Qed.

  Lemma contiguous_between_length a i j :
    contiguous_between a i j →
    (i + length a = Some j)%a.
  Proof. induction 1; cbn; solve_addr. Qed.

  (* The first element of the contiguous list is less than or equal to the last *)
   Lemma incr_list_le (a : list Addr) (a0 an : Addr) :
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
      apply (contiguous_spec _ Hcond) with 0 a0' hd in Ha0 as Hnext; auto.
      assert ((hd :: tl) !! 0 = Some hd) as Ha'; auto.
      assert (list.last (hd :: tl) = Some an').
      { simpl. destruct tl; auto. }
      apply IHa with hd an' in Ha'; auto.
      + assert (a0' ≤ hd)%Z.
        {  rewrite /incr_addr in Hnext.
           destruct (Z_le_dec (a0' + 1)%Z MemNum); inversion Hnext. simpl. omega. }
        apply Z.le_trans with hd; auto.
      + eauto using contiguous_weak.
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

  Lemma last_lookup {A : Type} (l : list A) :
    list.last l = l !! (length l - 1).
  Proof.
    induction l.
    - done.
    - simpl. destruct l; auto.
      rewrite IHl. simpl. rewrite PeanoNat.Nat.sub_0_r. done.
  Qed.

  Lemma last_app_iff {A : Type} (l1 l2 : list A) a :
    list.last l2 = Some a <-> length l2 > 0 ∧ list.last (l1 ++ l2) = Some a.
  Proof.
    split.
    - intros Hl2.
      induction l1.
      + destruct l2; inversion Hl2. simpl. split; auto. lia.
      + destruct IHl1 as [Hlt Hlast]. split; auto. simpl. rewrite Hlast.
        destruct (l1 ++ l2); auto.
        inversion Hlast.
    - generalize l1. induction l2; intros l1' [Hlen Hl].
      + inversion Hlen.
      + destruct l2;[rewrite last_snoc in Hl; inversion Hl; done|].
        rewrite -(IHl2 (l1' ++ [a0])); auto.
        simpl. split;[lia|]. rewrite -app_assoc -cons_middle. done.
  Qed.

  Lemma last_app_eq {A : Type} (l1 l2 : list A) :
    length l2 > 0 ->
    list.last l2 = list.last (l1 ++ l2).
  Proof.
    revert l1. induction l2;intros l1 Hlen.
    - inversion Hlen.
    - destruct l2.
      + rewrite last_snoc. done.
      + rewrite cons_middle app_assoc -(IHl2 (l1 ++ [a]));[auto|simpl;lia].
  Qed.

  Lemma contiguous_between_middle_bounds (a : list Addr) i (ai a0 an : Addr) :
    contiguous_between a a0 an →
    a !! i = Some ai →
    (a0 <= ai ∧ ai < an)%a.
  Proof.
    intro HH. revert ai i. induction HH as [| * Ha Hc Hi]; [ by inversion 1 |].
    intros * Hi'. destruct i as [| i].
    { cbn in Hi'. inversion Hi'; subst; clear Hi'. split; [ solve_addr |].
      destruct (decide (a' = b)).
      { subst a'. inversion Hc; subst; solve_addr. }
      { apply contiguous_between_length in Hc. solve_addr. } }
    { cbn in Hi'. split. enough (a' <= ai)%a by solve_addr.
      all: eapply Hi; eauto. }
  Qed.

  Lemma contiguous_between_middle_bounds' (a : list Addr) (ai a0 an : Addr) :
    contiguous_between a a0 an →
    ai ∈ a →
    (a0 <= ai ∧ ai < an)%a.
  Proof.
    intros Hc Hin.
    apply elem_of_list_lookup_1 in Hin as [? ?].
    eapply contiguous_between_middle_bounds; eauto.
  Qed.

  (* The i'th element of the contiguous list is less than or equal to the last *)
  Lemma incr_list_le_middle (a : list Addr) i (ai an : Addr) :
    contiguous a →
    a !! i = Some ai → list.last a = Some an → (ai ≤ an)%Z.
  Proof.
    generalize ai. destruct i;
                     intros ai' Hcond Hi' Hlast.
    - apply incr_list_le with a; auto.
    - rewrite -Nat.add_1_r in Hi'.
      assert ((drop (i + 1) a) !! 0 = Some ai') as Ha.
      { rewrite -(Nat.add_0_r (i + 1)) in Hi'.
        rewrite -Hi'. apply (lookup_drop a (i + 1) 0). }
      apply incr_list_le with _ _ an in Ha; auto.
      + apply contiguous_drop; auto.
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
    intros Hcond Hi Hsi.
    pose proof (contiguous_spec _ Hcond i a0 a1) as Hcond'; simpl in Hcond'.
    apply Hcond' in Hi; try rewrite Nat.add_1_r; auto.
    rewrite /incr_addr in Hi.
    destruct (Z_le_dec (a0 + 1)%Z MemNum); inversion Hi. simpl. omega.
  Qed.

  Lemma contiguous_between_incr_addr (a: list Addr) (i : nat) a0 ai an :
    contiguous_between a a0 an →
    a !! i = Some ai →
    (a0 + i)%a = Some ai.
  Proof.
    intros Hc. revert i ai. induction Hc.
    - inversion 1.
    - intros i ai. destruct i as [| i].
      { cbn. inversion 1; subst. solve_addr. }
      { cbn. intros Hi. specialize (IHHc _ _ Hi). solve_addr. }
  Qed.

  (* the i'th element is the same as adding i to the first element *)
  Lemma contiguous_incr_addr (a : list Addr) (i : nat) a0 ai :
    contiguous a ->
    a !! 0 = Some a0 → a !! i = Some ai -> (a0 + i)%a = Some ai.
  Proof.
    revert ai. induction i; intros ai Ha Ha0 Hai.
    - rewrite Ha0 in Hai. inversion Hai.
      apply addr_add_0.
    - assert (∃ aj, a !! i = Some aj) as [aj Haj].
      { apply lookup_lt_is_Some.
        apply Nat.lt_succ_l.
        apply lookup_lt_is_Some. eauto. }
      specialize (IHi aj Ha Ha0 Haj).
      rewrite -Nat.add_1_r in Hai. rewrite -Nat.add_1_r.
      pose proof (contiguous_spec _ Ha i _ _ Haj Hai).
      rewrite -(incr_addr_trans a0 aj ai i 1); auto.
      rewrite Nat.add_1_r Z.add_1_r Nat2Z.inj_succ.
      done.
  Qed.

  (* the i'th element is greater or equal to the first *)
  Lemma incr_list_ge_middle (a : list Addr) i (a0 ai : Addr) :
    contiguous a ->
    a !! 0 = Some a0 -> a !! i = Some ai -> (a0 <= ai)%Z.
  Proof.
    intros Ha H0 Hi. generalize (contiguous_incr_addr _ _ _ _ Ha H0 Hi).
    solve_addr.
  Qed.

  (* the i + j element is the same as adding j to the ith element *)
  Lemma contiguous_incr_addr_middle (a : list Addr) (i j : nat) ai aj :
    contiguous a ->
    a !! i = Some ai -> a !! (i + j) = Some aj -> (ai + j)%a = Some aj.
  Proof.
    intros Ha Hai Haij.
    rewrite -(PeanoNat.Nat.add_0_r i) in Hai.
    rewrite -lookup_drop in Hai.
    rewrite -lookup_drop in Haij.
    apply contiguous_drop with _ i in Ha.
    apply contiguous_incr_addr with (drop i a); auto.
  Qed.

  Lemma contiguous_between_incr_addr_middle (a : list Addr) a0 an (i j : nat) ai aj :
    contiguous_between a a0 an ->
    a !! i = Some ai -> a !! (i + j) = Some aj -> (ai + j)%a = Some aj.
  Proof.
    intros HH%contiguous_of_contiguous_between.
    apply contiguous_incr_addr_middle; auto.
  Qed.

  (* an alternative version of proving that an element in the middle of the list is < than the last *)
  Lemma incr_list_lt_middle_alt (a : list Addr) i (ai an : Addr) :
    contiguous a ->
    a !! i = Some ai -> list.last a = Some an -> i < length a - 1 -> (ai < an)%Z.
  Proof.
    intros Hreg Ha Hj Hlt.
    assert (ai ≤ an)%Z as Hinc; first (apply incr_list_le_middle with a i; auto).
    rewrite last_lookup in Hj.
    apply Zle_lt_or_eq in Hinc as [Hlt' | Heq];[auto|].
    apply z_of_eq in Heq. subst.
    assert ((an + (length a - 1 - i))%a = Some an) as Hcontr.
    { apply (contiguous_incr_addr_middle a i (length a - 1 - i)%nat an an) in Ha;auto.
      - solve_addr.
      - rewrite -Hj. f_equiv. lia. 
    } 
    apply next_lt_i in Hcontr; [done|lia]. 
  Qed. 

  Lemma contiguous_incr_addr_middle' (a : list Addr) (i : nat) (j: Z) ai aj :
    contiguous a →
    (0 <= i + j < length a)%Z →
    a !! i = Some ai -> a !! (Z.to_nat (i + j)%Z) = Some aj -> (ai + j)%a = Some aj.
  Proof.
    intros Ha Hij Hai Haj.
    destruct (decide (0 <= j)%Z).
    { assert (j = Z.to_nat j) as -> by lia.
      eapply contiguous_incr_addr_middle; eauto.
      assert (i + Z.to_nat j = Z.to_nat (i + j)) as -> by lia. auto. }
    { assert (i = Z.to_nat (i + j) + Z.to_nat (-j)) as Hi by lia.
      generalize (contiguous_incr_addr_middle a (Z.to_nat (i + j)) (Z.to_nat (-j)) aj ai Ha Haj).
      rewrite -Hi => /(_ Hai). solve_addr. }
  Qed.

  Lemma contiguous_between_incr_addr_middle' (a : list Addr) a0 an (i : nat) (j: Z) ai aj :
    contiguous_between a a0 an →
    (0 <= i + j < length a)%Z →
    a !! i = Some ai -> a !! (Z.to_nat (i + j)%Z) = Some aj -> (ai + j)%a = Some aj.
  Proof.
    intros HH%contiguous_of_contiguous_between.
    apply contiguous_incr_addr_middle'; auto.
  Qed.

  (* A region_addrs_aux is contiguous *)
  Lemma region_addrs_aux_contiguous (a : Addr) (n : nat) :
    is_Some (a + n)%a →
    contiguous (region_addrs_aux a n).
  Proof.
    intros [? ?]. rewrite /contiguous /region_addrs.
    exists a, (^(a + n)%a). f_equal. unfold region_size. solve_addr.
  Qed.

  Lemma region_addrs_contiguous (a b : Addr) :
    contiguous (region_addrs a b).
  Proof.
    rewrite /region_addrs. apply region_addrs_aux_contiguous.
    rewrite /region_size. zify_addr; try lia; eauto.
  Qed.

  Lemma contiguous_between_app a a1 a2 (i j k: Addr) :
    a = a1 ++ a2 →
    contiguous_between a i j →
    (i + length a1 = Some k)%a →
    contiguous_between a1 i k ∧ contiguous_between a2 k j.
  Proof.
    revert a a2 i j k. induction a1 as [| aa a1].
    { intros * ->.  simpl. intros. assert (i = k) by solve_addr. subst i. split; auto.
      apply contiguous_between_nil. }
    { intros * ->. cbn. inversion 1. subst. intros.
      unshelve epose proof (IHa1 (a1 ++ a2) a2 _ _ _ eq_refl _ _) as [IH1 IH2];
        [ shelve | shelve | shelve | ..]; eauto; cycle 1.
      split; [| eapply IH2]. 2: by solve_addr.
      eapply contiguous_between_cons; eauto. }
  Qed.

(*
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
*)

(*
  Lemma last_app_region_addrs l1 a b :
    length (region_addrs a b) > 0 ->
    list.last (l1 ++ region_addrs a b) = Some b.
  Proof.
    intros Hlen (* Hcont *).
    assert (a ≤ b)%Z.
    { rewrite /region_addrs in Hlen. destruct (Z_le_dec a b); auto. simpl in Hlen; lia. }
    rewrite -last_app_eq; auto. apply region_addrs_last; auto.
  Qed.
*)

(*
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
*)

(*
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
           ∧ a2 !! 0 = Some a2_first
           ∧ (a1_last + 1)%a = Some a2_first⌝)%I.
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
    repeat split;auto.
  Qed.
*)

  Context `{memG Σ, regG Σ, STSG Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  (* Note that we are assuming that both prog1 and prog2 are nonempty *)
  Lemma contiguous_between_program_split prog1 prog2 (φ : Addr → Word → iProp Σ) a i j :
    contiguous_between a i j →
    (([∗ list] a_i;w_i ∈ a;prog1 ++ prog2, φ a_i w_i) -∗
    ∃ (a1 a2 : list Addr) (k: Addr),
      ([∗ list] a_i;w_i ∈ a1;prog1, φ a_i w_i)
        ∗ ([∗ list] a_i;w_i ∈ a2;prog2, φ a_i w_i)
        ∗ ⌜contiguous_between a1 i k
           ∧ contiguous_between a2 k j
           ∧ a = a1 ++ a2
           ∧ (i + length a1 = Some k)%a⌝)%I.
  Proof.
    iIntros (Ha) "Hprog".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    rewrite app_length in Hlength.
    set (n1 := length prog1) in *.
    set (n2 := length prog2) in *.
    rewrite -(take_drop n1 a). set (k := ^(i + n1)%a).
    iExists (take n1 a), (drop n1 a), k.
    iDestruct (big_sepL2_app' with "Hprog") as "[Hprog1 Hprog2]".
    { subst n1. rewrite take_length. lia. }
    iFrame. iPureIntro.
    pose proof (contiguous_between_length _ _ _ Ha).
    destruct (contiguous_between_app a (take n1 a) (drop n1 a) i j k); auto.
    by rewrite take_drop.
    { rewrite take_length Hlength. subst k. solve_addr. }
    rewrite take_length. repeat split; eauto. rewrite Nat.min_l; solve_addr.
  Qed.

(*
  Lemma contiguous_region_addrs a a_first a_last :
    contiguous a -> a !! 0 = Some a_first -> list.last a = Some a_last ->
    a = region_addrs a_first a_last.
  Proof.
    generalize a_first. induction a; intros a_first' Ha Hfirst Hlast.
    - inversion Hfirst.
    - simpl in Hfirst. inversion Hfirst; subst.
      rewrite /region_addrs.
      assert (a_first' <= a_last)%Z as Hle.
      { apply incr_list_le with (a_first' :: a0); auto. }
      destruct (Z_le_dec a_first' a_last);[|contradiction].
      simpl. f_equiv.
      destruct a0.
      + inversion Hlast; subst.
        rewrite Z.sub_diag /=. done.
      + rewrite (Ha 0 _ a); auto. simpl.
        specialize (IHa a).
        rewrite /region_addrs in IHa.
        assert (a <= a_last)%Z as Hle'.
        { apply contiguous_weak in Ha. apply incr_list_le with (a :: a0); auto. }
        destruct (Z_le_dec a a_last);[|contradiction].
        assert (region_size a a_last = Z.abs_nat (a_last - a_first')) as <-.
        { rewrite /region_size.
          assert ((a_first' + 1)%a = Some a) as Hnext;[apply Ha with 0; auto|].
          apply incr_addr_of_z_i in Hnext. rewrite -Hnext. lia.
        }
        apply contiguous_weak in Ha.
        apply IHa; auto.
  Qed.
*)

  (* Helper lemma for contiguous lists of size 2: useful for the push macro *)
  Lemma contiguous_2 a :
    length a = 2 → contiguous a → ∃ a1 a2, a = [a1; a2] ∧ (a1 + 1)%a = Some a2.
  Proof.
    intros Hlength Ha.
    destruct a as [|a1 a]; inversion Hlength.
    destruct a as [|a2 a]; inversion Hlength.
    destruct a; inversion Hlength.
    exists a1,a2.
    pose proof (contiguous_spec _ Ha) as Ha'.
    split; [| apply Ha' with 0]; auto.
  Qed.

  (* Helper lemma for contiguous lists of size 3: useful for the pop macro *)
  Lemma contiguous_3 a :
    length a = 3 → contiguous a → ∃ a1 a2 a3, a = [a1; a2; a3] ∧ (a1 + 1)%a = Some a2 ∧ (a2 + 1)%a = Some a3.
  Proof.
    intros Hlength Ha.
    destruct a as [|a1 a]; inversion Hlength.
    destruct a as [|a2 a]; inversion Hlength.
    destruct a as [|a3 a]; inversion Hlength.
    destruct a; inversion Hlength.
    exists a1,a2,a3.
    pose proof (contiguous_spec _ Ha) as Ha'.
    split; [|split;[apply Ha' with 0|apply Ha' with 1] ];auto.
  Qed.


End Contiguous.

Opaque contiguous.
