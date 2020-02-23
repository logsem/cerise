From stdpp Require Import gmap fin_maps list.
From cap_machine Require Export addr_reg lang region.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.

(* Some addresses *)
  Notation "a- z" := (A z eq_refl) (at level 10, format "a- z").

  (* Some general purpuse registers *)
  Definition r_t0 : RegName := R 0 eq_refl.
  Definition r_t1 : RegName := R 1 eq_refl.
  Definition r_t2 : RegName := R 2 eq_refl.
  Definition r_t3 : RegName := R 3 eq_refl.
  Definition r_t4 : RegName := R 4 eq_refl.
  Definition r_t5 : RegName := R 5 eq_refl.
  Definition r_t6 : RegName := R 6 eq_refl.
  Definition r_t7 : RegName := R 7 eq_refl.
  Definition r_t8 : RegName := R 8 eq_refl.
  Definition r_t9 : RegName := R 9 eq_refl.
  Definition r_t10 : RegName := R 10 eq_refl.
  Definition r_t11 : RegName := R 11 eq_refl.
  Definition r_t12 : RegName := R 12 eq_refl.
  Definition r_t13 : RegName := R 13 eq_refl.
  Definition r_t14 : RegName := R 14 eq_refl.
  Definition r_t15 : RegName := R 15 eq_refl.
  Definition r_t16 : RegName := R 16 eq_refl.
  Definition r_t17 : RegName := R 17 eq_refl.
  Definition r_t18 : RegName := R 18 eq_refl.
  Definition r_t19 : RegName := R 19 eq_refl.
  Definition r_t20 : RegName := R 20 eq_refl.
  Definition r_t21 : RegName := R 21 eq_refl.
  Definition r_t22 : RegName := R 22 eq_refl.
  Definition r_t23 : RegName := R 23 eq_refl.
  Definition r_t24 : RegName := R 24 eq_refl.
  Definition r_t25 : RegName := R 25 eq_refl.
  Definition r_t26 : RegName := R 26 eq_refl.
  Definition r_t27 : RegName := R 27 eq_refl.
  Definition r_t28 : RegName := R 28 eq_refl.
  Definition r_t29 : RegName := R 29 eq_refl.
  Definition r_t30 : RegName := R 30 eq_refl.
  Definition r_t31 : RegName := R 31 eq_refl.

  (* A list of all general purpuse registers (if regnum=31) *)
  Definition all_registers : list RegName :=
    [r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6;r_t7;r_t8;r_t9;r_t10;r_t11;r_t12;r_t13;
       r_t14;r_t15;r_t16;r_t17;r_t18;r_t19;r_t20;r_t21;r_t22;r_t23;r_t24;r_t25;r_t26;
         r_t27;r_t28;r_t29;r_t30;r_t31;PC].


  (* Instructions and their decodings *)
  (* A special register for the stack pointer, different from PC *)
  Definition r_stk : RegName := r_t31.
  Lemma r_stk_ne : r_stk ≠ PC. Proof. done. Qed.

  (* Restore code encodings *)
  Parameter w_1 : Z.
  Parameter w_2 : Z.
  Parameter w_3 : Z.
  Parameter w_4a : Z.
  Parameter w_4b : Z.
  Parameter w_4c : Z.
  Parameter local_e : Z.
  (* Instruction encodings *)
  Parameter lea_z : RegName → Z → Word.
  Parameter lea_r : RegName → RegName → Word.
  Parameter store_z : RegName → Z → Word.
  Parameter store_r : RegName → RegName → Word.
  Parameter load_r : RegName → RegName → Word.
  Parameter move_z : RegName → Z → Word.
  Parameter move_r : RegName → RegName → Word.
  Parameter restrict_r : RegName → RegName → Word.
  Parameter restrict_z : RegName → Z → Word.
  Parameter geta : RegName → RegName → Word.
  Parameter getb : RegName → RegName → Word.
  Parameter gete : RegName → RegName → Word.
  Parameter add_r_z : RegName → RegName → Z → Word.
  Parameter sub_r_r : RegName → RegName → RegName → Word.
  Parameter sub_r_z : RegName → RegName → Z → Word.
  Parameter sub_z_z : RegName → Z → Z → Word.
  Parameter subseg_r_r : RegName → RegName → RegName → Word.
  Parameter jnz : RegName → RegName → Word.
  Parameter lt_r_r : RegName → RegName → RegName → Word.
  Parameter jmp : RegName → Word.
  Parameter halt : Word.
  Parameter fail_end : Word.
  (* Encoding decodings *)
  Axiom halt_i : cap_lang.decode (halt) = Halt.
  Axiom fail_end_i : cap_lang.decode (fail_end) = Fail.
  Axiom jnz_i : ∀ r1 r2, cap_lang.decode (jnz r1 r2) = Jnz r1 r2.
  Axiom lt_i : ∀ dst r1 r2, cap_lang.decode (lt_r_r dst r1 r2) = Lt dst (inr r1) (inr r2).
  Axiom jmp_i : ∀ r, cap_lang.decode (jmp r) = Jmp r.
  Axiom lea_z_i : ∀ r z, cap_lang.decode (lea_z r z) = Lea r (inl z).
  Axiom lea_r_i : ∀ r1 r2, cap_lang.decode (lea_r r1 r2) = Lea r1 (inr r2).
  Axiom store_z_i : ∀ r z, cap_lang.decode (store_z r z) = Store r (inl z).
  Axiom store_r_i : ∀ r1 r2, cap_lang.decode (store_r r1 r2) = Store r1 (inr r2).
  Axiom load_r_i : ∀ r1 r2, cap_lang.decode (load_r r1 r2) = Load r1 r2.
  Axiom move_z_i : ∀ r z, cap_lang.decode (move_z r z) = Mov r (inl z).
  Axiom move_r_i : ∀ r1 r2, cap_lang.decode (move_r r1 r2) = Mov r1 (inr r2).
  Axiom restrict_r_i : ∀ r1 r2, cap_lang.decode (restrict_r r1 r2) = Restrict r1 (inr r2).
  Axiom restrict_r_z : ∀ r1 z, cap_lang.decode (restrict_z r1 z) = Restrict r1 (inl z).
  Axiom geta_i : ∀ r1 r2, cap_lang.decode (geta r1 r2) = GetA r1 r2.
  Axiom getb_i : ∀ r1 r2, cap_lang.decode (getb r1 r2) = GetB r1 r2.
  Axiom gete_i : ∀ r1 r2, cap_lang.decode (gete r1 r2) = GetE r1 r2.
  Axiom add_r_z_i : ∀ r1 r2 z, cap_lang.decode (add_r_z r1 r2 z) = cap_lang.Add r1 (inr r2) (inl z).
  Axiom sub_r_r_i : ∀ r1 r2 r3, cap_lang.decode (sub_r_r r1 r2 r3) = cap_lang.Sub r1 (inr r2) (inr r3).
  Axiom sub_z_z_i : ∀ r1 z1 z2, cap_lang.decode (sub_z_z r1 z1 z2) = cap_lang.Sub r1 (inl z1) (inl z2).
  Axiom sub_r_z_i : ∀ r1 r2 z1, cap_lang.decode (sub_r_z r1 r2 z1) = cap_lang.Sub r1 (inr r2) (inl z1).
  Axiom subseg_r_r_i : ∀ r1 r2 r3, cap_lang.decode (subseg_r_r r1 r2 r3) = Subseg r1 (inr r2) (inr r3).
  (* encodings of restore code *)
  Axiom i_1 : cap_lang.encode (Mov r_t1 (inr PC)) = inl w_1.
  Axiom i_2 : cap_lang.encode (Lea r_t1 (inl 7%Z)) = inl w_2.
  Axiom i_3 : cap_lang.encode (Load r_stk r_t1) = inl w_3.
  Axiom i_4a : cap_lang.encode (Sub (r_t1) (inl 0%Z) (inl 1%Z)) = inl w_4a.
  Axiom i_4b : cap_lang.encode (Lea r_stk (inr r_t1)) = inl w_4b.
  Axiom i_4c : cap_lang.encode (Load PC r_stk) = inl w_4c.

  (* encodings of return pointer permission pair *)
  Axiom epp_local_e : cap_lang.decodePermPair local_e = (E,Local).


  (* Helper lemmas on list differences *)

   Lemma not_elem_of_list {A : Type} `{EqDecision A} (a : A) (l x : list A) :
     a ∈ x → a ∉ list_difference l x.
   Proof.
     intros Hax.
     rewrite /not.
     intros Hal.
     by apply elem_of_list_difference in Hal as [Ha' Hax_not].
   Qed.

   Lemma list_difference_nil {A : Type} `{EqDecision A} (l : list A) :
     list_difference l [] = l.
   Proof.
     induction l; auto.
     simpl. f_equal.
     apply IHl.
   Qed.

   Lemma list_difference_length_cons {A : Type} `{EqDecision A}
         (l2 : list A) (a : A) :
     list_difference [a] (a :: l2) = [].
   Proof.
     simpl.
     assert (a ∈ a :: l2); first apply elem_of_list_here.
     destruct (decide_rel elem_of a (a :: l2)); auto; last contradiction.
   Qed.

   Lemma list_difference_skip {A : Type} `{EqDecision A}
         (l1 l2 : list A) (b : A) :
     ¬ (b ∈ l1) →
     list_difference l1 (b :: l2) = list_difference l1 l2.
   Proof.
     intros Hnin.
     induction l1; auto.
     apply not_elem_of_cons in Hnin.
     destruct Hnin as [Hne Hl1].
     simpl.
     destruct (decide_rel elem_of a (b :: l2)).
     - apply elem_of_cons in e.
       destruct e as [Hcontr | Hl2]; first congruence.
       destruct (decide_rel elem_of a l2); last contradiction.
         by apply IHl1.
     - apply not_elem_of_cons in n.
       destruct n as [Hne' Hl2].
       destruct (decide_rel elem_of a l2); first contradiction.
       f_equal.
         by apply IHl1.
   Qed.

   Lemma list_difference_nested {A : Type} `{EqDecision A}
         (l1 l1' l2 : list A) (b : A) :
     ¬ (b ∈ (l1 ++ l1')) →
     list_difference (l1 ++ b :: l1') (b :: l2) = list_difference (l1 ++ l1') l2.
   Proof.
     intros Hnotin.
     induction l1.
     - simpl.
       assert (b ∈ (b :: l2)); first apply elem_of_list_here.
       destruct (decide_rel elem_of b (b :: l2)); last contradiction.
       rewrite list_difference_skip; auto.
     - simpl in *.
       apply not_elem_of_cons in Hnotin.
       destruct Hnotin as [Hne Hnotin].
       destruct (decide_rel elem_of a (b :: l2)).
       + apply elem_of_cons in e.
         destruct e as [Hcontr | Hl2]; first congruence.
         destruct (decide_rel elem_of a l2); last contradiction.
           by apply IHl1.
       + apply not_elem_of_cons in n.
         destruct n as [Hne' Hnotin'].
         destruct (decide_rel elem_of a l2); first contradiction.
         f_equal.
           by apply IHl1.
   Qed.

   Lemma list_difference_length_ni  {A : Type} `{EqDecision A}
         (l1 : list A) (b : A) :
     ¬ (b ∈ l1) →
     length (list_difference l1 [b]) = length l1.
   Proof.
     intros Hna.
     destruct l1; auto.
     simpl.
     apply not_elem_of_cons in Hna.
     destruct Hna as [Hne Hna].
     destruct (decide_rel elem_of a [b]).
     - apply elem_of_list_singleton in e. congruence.
     - simpl. rewrite list_difference_skip; auto.
         by rewrite list_difference_nil.
   Qed.

   Lemma list_difference_length {A : Type} `{EqDecision A}
         (l1 : list A) (b : A) :
     b ∈ l1 →
     NoDup l1 →
     length (list_difference l1 [b]) =
     length l1 - 1.
   Proof.
     intros Ha Hndup.
     induction l1; auto.
     destruct (decide (b = a)).
     - subst.
       assert (a ∈ a :: l1); first apply elem_of_list_here.
       apply NoDup_cons_iff in Hndup.
       destruct Hndup as [Hni Hndup].
       assert (¬ (a ∈ l1)) as Hni'.
       { rewrite /not. intros Hin. apply elem_of_list_In in Hin. contradiction. }
       simpl.
       assert (a ∈ [a]); first apply elem_of_list_here.
       destruct (decide_rel elem_of a [a]); last contradiction.
       rewrite -minus_n_O.
       apply list_difference_length_ni; auto.
     - simpl.
       assert (¬ (a ∈ [b])).
       { rewrite /not. intros Hin. apply elem_of_list_singleton in Hin. congruence. }
       destruct (decide_rel elem_of a [b]); first contradiction.
       rewrite -minus_n_O /=.
       inversion Hndup; subst.
       apply elem_of_cons in Ha.
       destruct Ha as [Hcontr | Ha]; first congruence.
       apply IHl1 in Ha as Heq; auto.
       rewrite Heq.
       destruct l1; first inversion Ha.
       simpl. lia.
   Qed.

   Lemma list_difference_app {A : Type} `{EqDecision A}
         (l1 l2 l2' : list A) :
     list_difference l1 (l2 ++ l2') = list_difference (list_difference l1 l2) l2'.
   Proof.
     induction l1; auto.
     simpl. destruct (decide_rel elem_of a (l2 ++ l2')).
     - apply elem_of_app in e as [Hl2 | Hl2'].
       + destruct (decide_rel elem_of a l2); last contradiction.
         apply IHl1.
       + destruct (decide_rel elem_of a l2); first by apply IHl1.
         simpl.
         destruct (decide_rel elem_of a l2'); last contradiction.
         apply IHl1.
     - apply not_elem_of_app in n as [Hl2 Hl2'].
       destruct (decide_rel elem_of a l2); first contradiction.
       simpl.
       destruct (decide_rel elem_of a l2'); first contradiction.
       f_equal. apply IHl1.
   Qed.


   (* helper lemmas for the list of all registers *)

   Ltac discharge_not_or :=
     rewrite /not; intros Hor;
       by repeat (destruct Hor as [Hcontr | Hor]; first inversion Hcontr).

   (* a typical helper lemma for stack calls *)
  Lemma helper1 r1 :
     r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 →
     r1 ∈ all_registers →
     length (list_difference all_registers [PC; r_stk; r_t0; r1]) = 29.
   Proof.
     intros (Hne1 & Hne2 & Hne3) Hr1.
     assert ([PC; r_stk; r_t0; r1] = [PC; r_stk; r_t0] ++ [r1]); first done.
     rewrite H.
     rewrite list_difference_app.
     assert (r1 ∈ (list_difference all_registers [PC; r_stk; r_t0])).
     { simpl.
       rewrite /all_registers in Hr1.
       apply elem_of_cons in Hr1 as [Hcontr | Hr1]; first contradiction.
       assert
       ([r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11;
          r_t12; r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22;
          r_t23; r_t24; r_t25; r_t26; r_t27; r_t28; r_t29; r_t30; r_t31; PC] =
       [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11;
          r_t12; r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22;
          r_t23; r_t24; r_t25; r_t26; r_t27; r_t28; r_t29; r_t30] ++ [r_t31; PC]); auto.
       rewrite H0 in Hr1. clear H0.
       apply elem_of_app in Hr1 as [Hr1 | Hcontr]; auto.
       apply elem_of_cons in Hcontr as [? | Hcontr]; first contradiction.
       apply elem_of_list_singleton in Hcontr; contradiction.
     }
     rewrite list_difference_length; auto.
     simpl.
     repeat (apply NoDup_cons; first discharge_not_or).
     apply NoDup_nil.
   Qed.

   (* Spec for all_registers *)

   Lemma all_registers_correct r1 :
     r1 ∈ all_registers.
   Proof.
     rewrite /all_registers.
     destruct r1.
     - do 32 (apply elem_of_cons; right).
         by apply elem_of_list_singleton.
     - induction n.
       + apply elem_of_cons; left. (* rewrite /r_t0. *)
         apply f_equal. apply eq_proofs_unicity. decide equality.
       + apply elem_of_list_lookup_2 with (S n).
         repeat (destruct n;
                   first (simpl;do 2 f_equal;apply eq_proofs_unicity;decide equality)).
         simpl in *. inversion fin.
   Qed.

   Lemma all_registers_NoDup :
     NoDup all_registers.
   Proof.
     rewrite /all_registers.
     repeat (
     apply NoDup_cons;
      first (rewrite /not; intros Hcontr; apply elem_of_list_In in Hcontr;
         repeat (apply elem_of_cons in Hcontr as [Hcontr | Hcontr];[inversion Hcontr|]);
         inversion Hcontr)).
     apply NoDup_nil.
   Qed.

   Lemma NoDup_list_difference {A : Type} `{EqDecision A} (l1 l2 : list A) :
     NoDup l1 → NoDup (list_difference l1 l2).
   Proof.
     intros Hdup.
     revert l2. induction l1; intros l2.
     - apply NoDup_nil.
     - simpl. destruct (decide_rel elem_of a l2).
       + apply IHl1.
           by apply NoDup_cons_iff in Hdup as [Ha Hdup].
       + apply NoDup_cons_iff in Hdup as [Ha Hdup].
         apply NoDup_cons.
         * rewrite /not. rewrite /not in Ha. intros Hcontr.
           apply elem_of_list_In in Hcontr.
           apply elem_of_list_difference in Hcontr as [Hal1 _].
           apply elem_of_list_In in Hal1.
             by apply Ha in Hal1.
         * by apply IHl1.
   Qed.

   Lemma list_difference_Permutation {A : Type} `{EqDecision A} (l l1 l2 : list A) :
     l1 ≡ₚl2 -> list_difference l l1 = list_difference l l2.
   Proof.
     intros Hl.
     induction l; auto.
     simpl. rewrite IHl.
     destruct (decide_rel elem_of a l1).
     - apply elem_of_list_In in e.
       apply Permutation_in with _ _ _ a in Hl; auto.
       apply elem_of_list_In in Hl.
       destruct (decide_rel elem_of a l2);[|contradiction].
       done.
     - revert n; rewrite elem_of_list_In; intros n.
       assert (¬ In a l2) as Hnin.
       { intros Hcontr. apply Permutation_sym in Hl.
         apply Permutation_in with _ _ _ a in Hl; auto. }
       revert Hnin; rewrite -elem_of_list_In; intro Hnin.
       destruct (decide_rel elem_of a l2);[contradiction|].
       done.
   Qed.

  (* Some additional helper lemmas about region_addrs *)

  Lemma not_elem_of_region_addrs_aux a n (i : Z) :
     (i > 0)%Z →
     a ≠ addr_reg.top →
     a ∉ region_addrs_aux (^(a + i)%a) n.
   Proof. 
     intros Hi Hne.
     revert i Hi; induction n; intros i Hi.
     - apply not_elem_of_nil.
     - simpl. apply not_elem_of_cons; split. 
       + intro. apply Hne. solve_addr. 
       + rewrite get_addrs_from_option_addr_comm.
         apply IHn; omega. done. 
   Qed.

  Lemma region_addrs_first a b :
    (a < b)%a ->
    (region_addrs a b) !! 0 = Some a.
  Proof.
    intros Hle.
    rewrite /region_addrs.
    rewrite (_: region_size a b = S (region_size a b - 1)).
    2: by (unfold region_size; solve_addr). done.
  Qed.

  Lemma region_addrs_aux_next_head a (a0 a1 : Addr) n :
    ((region_addrs_aux (^a)%a n) !! 0) = Some a0 →
    ((region_addrs_aux (^a)%a n) !! (1)) = Some a1 →
    (^(a0 + 1)%a = a1).
  Proof.
    rewrite /region_addrs_aux.
    intros Ha0 Ha1.
    destruct n; inversion Ha0.
    destruct n; inversion Ha1.
    simpl in *.
    rewrite H0 in Ha1.
    rewrite -H1 in Ha1.
    inversion Ha1.
    destruct (a0 + 1)%a; simpl; auto; inversion Ha1.
  Qed.

  Lemma region_addrs_aux_next a n i ai aj :
    ((region_addrs_aux a n) !! i) = Some ai → ((region_addrs_aux a n) !! (i + 1)) = Some aj →
    ^(ai + 1)%a = aj.
  Proof.
    intros Hai Haj.
    assert (i + 1 < n).
    { rewrite -(region_addrs_aux_length n a).
      apply lookup_lt_is_Some_1. eauto. }
    assert (i < n).
    { rewrite -(region_addrs_aux_length n a).
      apply lookup_lt_is_Some_1. eauto. }
    assert (strings.length (region_addrs_aux a i) = i).
    { apply region_addrs_aux_length. }
    assert (strings.length (region_addrs_aux a (i + 1)) = (i + 1)).
    { apply region_addrs_aux_length. }
    rewrite (region_addrs_aux_decomposition n a i) in Hai; last lia.
    rewrite lookup_app_r in Hai; last lia.
    rewrite H1 in Hai. rewrite Nat.sub_diag in Hai.
    rewrite (region_addrs_aux_decomposition n a i) in Haj; last lia.
    rewrite lookup_app_r in Haj; last lia.
    rewrite H1 in Haj. rewrite minus_plus in Haj.
    apply (region_addrs_aux_next_head (a + i)%a ai aj (n - i)); auto.
  Qed.

  Lemma region_addrs_lt_top a n i ai :
    ((z_of a) + (Z.of_nat i) < MemNum)%Z → region_addrs_aux a n !! i = Some ai → ai ≠ top.
  Proof.
    intros Ha Hai.
    assert (length (region_addrs_aux a n) = n) as Hlen.
    { apply region_addrs_aux_length. }
    assert (length (region_addrs_aux a i) = i) as Hleni.
    { apply region_addrs_aux_length. }
    assert (i < n) as Hi.
    { rewrite -Hlen. by apply lookup_lt_Some with ai. }
    rewrite (region_addrs_aux_decomposition n a i) in Hai; last lia.
    rewrite lookup_app_r in Hai; last lia.
    rewrite Hleni Nat.sub_diag in Hai.
    destruct (a + i)%a eqn:Hai'.
    - rewrite /= /region_addrs_aux in Hai.
      destruct (n - i); inversion Hai.
      rewrite H0 in Hai'.
      rewrite /incr_addr in Hai'.
      destruct (Z_le_dec (a + i)%Z MemNum); inversion Hai'.
      rewrite /top /not. intros Hcontr. inversion Hcontr. lia.
    - rewrite /incr_addr in Hai'.
      destruct (Z_le_dec (a + i)%Z MemNum); inversion Hai'; lia.
  Qed.

  Definition region_addrs_aux_singleton (a : Addr) :
    [a] = region_addrs_aux a 1. Proof. done. Qed.

  Definition region_addrs_zeroes (b e : Addr) : list Word :=
    repeat (inl 0%Z) (region_size b e).

  Lemma region_addrs_zeroes_lookup (b e : Addr) i y :
    region_addrs_zeroes b e !! i = Some y → y = inl 0%Z.
  Proof.
    rewrite /region_addrs_zeroes. intros Hlookup.
    apply repeat_spec with (region_size b e).
    apply elem_of_list_In.
    by apply elem_of_list_lookup_2 with i.
  Qed.

  Lemma region_size_split (a b e : Addr) :
     (b ≤ a < e)%Z →
     region_size b e = region_size b a + region_size a e.
   Proof. intros [? ?]. rewrite /region_size. solve_addr. Qed.

   Lemma get_addr_from_option_addr_region_size (a b : Addr) :
     (b ≤ a)%Z →
     (^(b + region_size b a) = a)%a.
   Proof. intros Hle. rewrite /region_size. solve_addr. Qed.

   Lemma incr_addr_region_size (a b : Addr) :
     (b <= a)%a →
     (b + region_size b a)%a = Some a.
   Proof. intros. unfold region_size. solve_addr. Qed.

   Lemma incr_addr_region_size_iff (a b : Addr) (i : nat) :
     (a + i)%a = Some b ↔ (a <= b)%a ∧ region_size a b = i.
   Proof.
     rewrite /region_size. split; [ intros | intros [? ?] ]; solve_addr.
   Qed.

   Lemma region_addrs_not_elem_of a n :
     forall a', (a < a')%a -> a ∉ (region_addrs_aux a' n).
   Proof.
     induction n.
     - intros a' Ha'. apply not_elem_of_nil.
     - intros a' Ha'. apply not_elem_of_cons.
       split.
       + intros Hcontr; subst. rewrite /lt_addr in Ha'. lia.
       + apply IHn. rewrite /lt_addr in Ha'. rewrite /lt_addr.
         destruct (a' + 1)%a eqn:Hsome; simpl.
         ++ apply next_lt in Hsome. lia.
         ++ destruct a,a'. simpl in *. apply Z.leb_le in fin0 as Hle. lia.
   Qed.

   Lemma region_addrs_aux_NoDup (a: Addr) (n: nat) :
     is_Some (a + n)%a →
     NoDup (region_addrs_aux a n).
   Proof.
     generalize a. clear a. induction n; intros a Hsome.
     - apply NoDup_nil.
     - apply NoDup_cons.
       + intros Hin. apply elem_of_list_In in Hin.
         destruct n. { inversion Hin. }
         assert (a < top)%a as Hlt.
         { destruct Hsome as [x Hx]. apply next_lt_i in Hx;[|lia].
           rewrite /lt_addr. destruct a,x; simpl in *. apply Z.leb_le in fin0 as Hle. lia.
         }
         assert (a < (get_addr_from_option_addr (a + 1)%a))%a as Hlt2.
         { destruct (a + 1)%a eqn:Hnext.
           - apply next_lt in Hnext. simpl. auto.
           - simpl. done.
         }
         apply region_addrs_not_elem_of with _ (S n) _ in Hlt2. contradiction.
       + destruct n; [apply NoDup_nil|].
         apply IHn.
         destruct Hsome as [x Hx].
         rewrite Nat2Z.inj_succ -Z.add_1_r in Hx.
         unfold is_Some. zify_addr; eauto; lia.
   Qed.

   Lemma region_addrs_NoDup a b :
     NoDup (region_addrs a b).
   Proof.
     rewrite /region_addrs. destruct (Z_le_dec a b).
     - apply region_addrs_aux_NoDup.
       rewrite incr_addr_region_size; eauto.
     - rewrite /region_size Z_to_nat_nonpos; [| lia]. apply NoDup_nil.
   Qed.
