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


   (* Helper lemmas for doing arithmetic on adresses. TODO: move this to addr_reg *)

  Lemma next_lt (a a' : Addr) :
    (a + 1)%a = Some a' → (a < a')%Z.
  Proof.
    rewrite /incr_addr. intros Ha'.
    destruct (Z_le_dec (a + 1)%Z MemNum); inversion Ha'.
    simpl. lia.
  Qed.

  Lemma next_lt_i (a a' : Addr) (i : Z) :
    (i > 0)%Z →
    (a + i)%a = Some a' → (a < a')%Z.
  Proof.
    rewrite /incr_addr. intros Hgt Ha'.
    destruct (Z_le_dec (a + i)%Z MemNum); inversion Ha'.
    simpl. lia.
  Qed.

  Lemma next_le_i (a a' : Addr) (i : Z) :
    (i >= 0)%Z →
    (a + i)%a = Some a' → (a <= a')%Z.
  Proof.
    rewrite /incr_addr. intros Hgt Ha'.
    destruct (Z_le_dec (a + i)%Z MemNum); inversion Ha'.
    simpl. lia.
  Qed.

  Lemma next_lt_top (a : Addr) i :
    (i > 0)%Z →
    is_Some (a + i)%a → a ≠ top.
  Proof.
    intros Hlt Hsome.
    intros Heq. subst. destruct Hsome as [x Hcontr].
    rewrite /incr_addr in Hcontr.
    destruct ( Z_le_dec (top + i)%Z MemNum); inversion Hcontr.
    clear Hcontr H0. rewrite /top /= in l. lia.
  Qed. 
  
  Lemma addr_next_le (a e e' : Addr) :
    (a ≤ e)%Z → (e + 1)%a = Some e' → ∃ a', (a + 1)%a = Some a'.
  Proof.
    intros Ha He.
    assert (e < e')%Z as Hlt.
    { rewrite /incr_addr in He.
      destruct (Z_le_dec (e + 1)%Z MemNum); inversion He. simpl. omega. }
    assert (a < e')%a; [apply Z.le_lt_trans with e; auto|].
    assert (a < MemNum)%Z.
    { apply Z.lt_le_trans with e'; destruct e'; auto. simpl.
        by apply Z.leb_le. }
    destruct (a + 1)%a eqn:Hnone.
    - exists a0; done.
    - apply incr_addr_one_none in Hnone.
      rewrite Hnone in H0. inversion H0.
  Qed.
    
  Lemma addr_next_lt_gt_contr (a e a' : Addr) :
    (a < e)%Z → (a + 1)%a = Some a' → (e < a')%Z → False.
  Proof.
    intros Hlta Ha' Hlta'.
    rewrite /incr_addr in Ha'.
    destruct (Z_le_dec (a + 1)%Z MemNum); inversion Ha'.
    rewrite -H0 in Hlta'. 
    simpl in *. lia.
  Qed.

  Lemma addr_next_lt (a e a' : Addr) :
    (a < e)%Z → (a + 1)%a = Some a' → (a' ≤ e)%Z.
  Proof.
    intros Ha Ha'.
    apply Znot_gt_le. rewrite /not.
    intros Hlt. apply Z.gt_lt in Hlt. 
    apply addr_next_lt_gt_contr with a e a'; auto.
  Qed. 
    
  Lemma addr_abs_next (a e a' : Addr) :
    (a + 1)%a = Some a' → (a < e)%Z → (Z.abs_nat (e - a) - 1) = (Z.abs_nat (e - a')).
  Proof.
    intros Ha' Hlt.
    rewrite /incr_addr in Ha'.
    destruct (Z_le_dec (a + 1)%Z MemNum); inversion Ha'.
    destruct a'. inversion H0; simpl.
    rewrite Z.sub_add_distr. lia.
  Qed.

  Lemma addr_unique a a' fin fin' :
    a = a' → A a fin = A a' fin'.
  Proof.
    intros ->. f_equal. apply eq_proofs_unicity. decide equality.
  Qed.

  Lemma incr_addr_trans (a1 a2 a3 : Addr) (z1 z2 : Z) :
    (a1 + z1)%a = Some a2 → (a2 + z2)%a = Some a3 →
    (a1 + (z1 + z2))%a = Some a3.
  Proof.
    rewrite /incr_addr. 
    intros Ha1 Ha2. 
    destruct (Z_le_dec (a1 + z1)%Z MemNum); inversion Ha1.
    destruct (Z_le_dec (a2 + z2)%Z MemNum); inversion Ha2.
    destruct a2,a3. simpl in *.
    inversion H0. inversion H1.  
    rewrite -H2 in H3. subst.
    destruct (Z_le_dec (a1 + (z1 + z2))%Z MemNum).
    - f_equal. apply addr_unique. lia.
    - exfalso. clear fin l l0 H0 H1 Ha2 Ha1.
      apply Z.leb_nle in n. 
      rewrite Z.add_assoc in n.
      congruence.
  Qed. 

  Lemma addr_add_assoc (a a' : Addr) (z1 z2 : Z) :
    (a + z1)%a = Some a' →
    (a + (z1 + z2))%a = (a' + z2)%a.
  Proof.
    intros Ha'.
    assert ((z_of a) + z1 = z_of a')%Z as Haz'.
    { rewrite /incr_addr in Ha'.
      by destruct (Z_le_dec (a + z1)%Z MemNum); inversion Ha'. } 
    rewrite /incr_addr.
    destruct (Z_le_dec (a + (z1 + z2))%Z MemNum),(Z_le_dec (a' + z2)%Z MemNum); auto. 
    - f_equal. apply addr_unique. lia. 
    - rewrite -Haz' in n.
      exfalso.  
      by rewrite Z.add_assoc in l.
    - exfalso. 
      rewrite -Haz' in l.
        by rewrite Z.add_assoc in n.
  Qed. 

  Lemma addr_add_0 (a : Addr) :
    (a + 0)%a = Some a.
  Proof.
    rewrite /incr_addr.
    destruct a; simpl.
    destruct (Z_le_dec (z + 0)%Z MemNum).
    - f_equal. apply addr_unique. lia.
    - rewrite Z.add_0_r in n.
      exfalso. 
      apply (Z.leb_le z MemNum) in fin.
      contradiction.
  Qed.

  (* Some additional helper lemmas about region_addrs *)

  Lemma region_addrs_aux_next_head a (a0 a1 : Addr) n :
    ((region_addrs_aux (get_addr_from_option_addr a) n) !! 0) = Some a0 →
    ((region_addrs_aux (get_addr_from_option_addr a) n) !! (1)) = Some a1 →
    (get_addr_from_option_addr (a0 + 1)%a = a1).
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
    get_addr_from_option_addr (ai + 1)%a = aj.
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
    if Z_le_dec b e then (repeat (inl 0%Z) (region_size b e)) else nil.

  Lemma region_addrs_zeroes_lookup (b e : Addr) i y :
    region_addrs_zeroes b e !! i = Some y → y = inl 0%Z.
  Proof.
    rewrite /region_addrs_zeroes.
    destruct (Z_le_dec b e).
    - intros Hlookup. apply repeat_spec with (region_size b e).
      apply elem_of_list_In.
      by apply elem_of_list_lookup_2 with i.
    - intro Hcontr; inversion Hcontr.
  Qed.

  Lemma region_size_split (a b e a' : Addr) :
     (b ≤ a < e)%Z →
     (a + 1)%Z = a' →
     region_size b e - region_size b a = region_size a' e.
   Proof.
     intros Hbe Ha'.
     rewrite /region_size.
     rewrite -Ha' /=.
     lia.
   Qed.

   Lemma incr_addr_of_z (a a' : Addr) :
     (a + 1)%a = Some a' →
     (a + 1)%Z = a'.
   Proof. 
     intros Ha'. rewrite /incr_addr in Ha'.
       by destruct (Z_le_dec (a + 1)%Z MemNum); inversion Ha'.
   Qed.

   Lemma incr_addr_of_z_i (a a' : Addr) i :
     (a + i)%a = Some a' →
     (a + i)%Z = a'.
   Proof. 
     intros Ha'. rewrite /incr_addr in Ha'.
       by destruct (Z_le_dec (a + i)%Z MemNum); inversion Ha'.
   Qed. 

   (* a + (region_size a b) = a + 1 *)
   Lemma get_addr_from_option_addr_next (a b a' : Addr) :
     (a + 1)%a = Some a' →
     (b ≤ a)%Z →
     (get_addr_from_option_addr (b + region_size b a)%a = a')%a.
   Proof.
     intros Hasome' Hle.
     apply incr_addr_of_z in Hasome' as Ha'.
     rewrite /region_size.
     assert (b ≤ a')%Z.
     { assert (a < a')%Z; first by apply next_lt. lia. }     
     assert (b + S (Z.abs_nat (a - b)) = a')%Z; first lia.
     (* assert ((b + S (Z.abs_nat (a - b)))%a = Some a'). *)
     destruct a'. rewrite /incr_addr.
     destruct (Z_le_dec (b + S (Z.abs_nat (a - b)))%Z MemNum).
     - f_equal. by apply addr_unique.
     - rewrite H0 /= in n.
       apply Z.leb_nle in n. congruence.
   Qed.

   Lemma get_addr_from_option_addr_region_size (a b : Addr) :
     (b ≤ a)%Z →
     (get_addr_from_option_addr (b + (region_size b a - 1))%a = a)%a.
   Proof.
     intros Hle.
     rewrite /region_size /= Nat2Z.inj_succ -Z.add_1_r Z.add_simpl_r.
     destruct (b + Z.abs_nat (a - b))%a eqn:Hsome.
     - rewrite /incr_addr in Hsome.
       destruct (Z_le_dec (b + Z.abs_nat (a - b))%Z MemNum); inversion Hsome.
       destruct a; simpl. apply z_of_eq. simpl in *. clear H0 Hsome l a0.
       lia.
     - rewrite /incr_addr in Hsome.
       destruct (Z_le_dec (b + Z.abs_nat (a - b))%Z MemNum); inversion Hsome. exfalso.
       clear Hsome. destruct a,b; simpl in *. apply Z.leb_le in fin0. apply Z.leb_le in fin.
       lia. 
   Qed. 

   Lemma incr_addr_region_size_next (a b b': Addr) :
     (b + 1)%a = Some b' →
     (a <= b)%a →
     (a + (region_size a b))%a = Some b'.
   Proof.
     intros Hb' Hle.
     assert (b ≠ top) as Hb.
     { intros Htop. subst.
       rewrite /incr_addr in Hb'.
       destruct (Z_le_dec (top + 1)%Z MemNum); try discriminate. clear Hb'.
       rewrite /top /= in l. lia. 
     }
     apply get_addr_from_option_addr_next with b a b' in Hb' as Hsome; auto.
     rewrite -Hsome.
     apply incr_addr_of_z in Hb'. subst.
     rewrite /incr_addr.
     destruct (Z_le_dec (a + region_size a b)%Z MemNum).
     - f_equiv.
     - exfalso. rewrite /incr_addr in Hb'.
       destruct (Z_le_dec (a + region_size a b)%Z MemNum); inversion Hb'.
       + contradiction.
       + rewrite /region_size/=  in n.
         rewrite /le_addr in Hle. 
         rewrite -Zabs2Nat.inj_succ in n;[|lia]. 
         rewrite Zminus_succ_l -Z.add_1_r H0 in n.
         lia.
   Qed.

   Lemma incr_addr_region_size (a b : Addr) :
     (a <= b)%a →
     (a + (region_size a b - 1))%a = Some b.
   Proof.
     intros Hle.
     apply get_addr_from_option_addr_region_size in Hle.
     rewrite /incr_addr. rewrite /incr_addr in Hle. 
     destruct (Z_le_dec (a + (region_size a b - 1))%Z MemNum).
     - simpl in *. f_equiv. done. 
     - exfalso.
       destruct a,b; simpl in *.
       rewrite /top in Hle. inversion Hle; subst.
       apply Z.leb_le in fin as Hle'. rewrite /region_size /= in n.
       lia. 
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

   Lemma region_addrs_aux_NoDup a n :
     is_Some (a + (Z.of_nat n - 1))%a →
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
         assert (n + 1 > 0)%Z as Hgt;[lia|].
         rewrite Z.add_simpl_r Nat2Z.inj_succ -Z.add_1_r in Hx.
         apply (next_lt_i a x (n + 1) Hgt) in Hx as Hlt.
         exists x. destruct (a + 1)%a eqn:some.
         ++ simpl.
            apply incr_addr_of_z in some.
            apply incr_addr_of_z_i in Hx as Ha.
            rewrite /incr_addr.
            destruct x; simpl in *. apply Z.leb_le in fin as Hle.
            assert (a0 + n <= MemNum)%Z as Hle0;[lia|].
            assert (S n - 1 = n)%Z as ->;[lia|].
            destruct (Z_le_dec (a0 + n)%Z MemNum);[|contradiction].
            assert (a0 + n = z)%Z as Heq;[lia|].
            subst. f_equiv. apply z_of_eq. done.
         ++ exfalso. apply incr_addr_one_none in some.
            rewrite /top /= in some.
            destruct x; simpl in *. apply Z.leb_le in fin as Hle.
            subst. simpl in *. lia.
   Qed.

   Lemma region_addrs_NoDup a b :
     NoDup (region_addrs a b).
   Proof.
     rewrite /region_addrs. destruct (Z_le_dec a b).
     - apply region_addrs_aux_NoDup.
       rewrite incr_addr_region_size; eauto.
     - apply NoDup_nil.
   Qed.


   (* Helper lemma for big separation conjuction of two lists, with appends of the same size *)
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
