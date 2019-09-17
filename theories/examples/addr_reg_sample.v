From stdpp Require Import gmap fin_maps list.
From cap_machine Require Export addr_reg lang region.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.

  (* Some addresses *)
  Definition a0 : Addr := A 0 eq_refl.
  Definition a1 : Addr := A 1 eq_refl.
  Definition a2 : Addr := A 2 eq_refl.
  Definition a3 : Addr := A 3 eq_refl.
  Definition a4 : Addr := A 4 eq_refl.
  Definition a5 : Addr := A 5 eq_refl.
  Definition a6 : Addr := A 6 eq_refl.
  Definition a7 : Addr := A 7 eq_refl.
  Definition a8 : Addr := A 8 eq_refl.
  Definition a9 : Addr := A 9 eq_refl.
  Definition a10 : Addr := A 10 eq_refl.
  Definition a11 : Addr := A 11 eq_refl.
  Definition a12 : Addr := A 12 eq_refl.
  Definition a13 : Addr := A 13 eq_refl.
  Definition a14 : Addr := A 14 eq_refl.
  Definition a15 : Addr := A 15 eq_refl.
  Definition a16 : Addr := A 16 eq_refl.
  Definition a17 : Addr := A 17 eq_refl.
  Definition a18 : Addr := A 18 eq_refl.
  Definition a19 : Addr := A 19 eq_refl.
  Definition a20 : Addr := A 20 eq_refl.
  Definition a21 : Addr := A 21 eq_refl.
  Definition a22 : Addr := A 22 eq_refl.
  Definition a23 : Addr := A 23 eq_refl.
  Definition a24 : Addr := A 24 eq_refl.
  Definition a25 : Addr := A 25 eq_refl.
  Definition a26 : Addr := A 26 eq_refl.
  Definition a27 : Addr := A 27 eq_refl.
  Definition a28 : Addr := A 28 eq_refl.
  Definition a29 : Addr := A 29 eq_refl.
  Definition a30 : Addr := A 30 eq_refl.
  Definition a31 : Addr := A 31 eq_refl.
  Definition a32 : Addr := A 32 eq_refl.
  Definition a33 : Addr := A 33 eq_refl.
  Definition a34 : Addr := A 34 eq_refl.
  Definition a35 : Addr := A 35 eq_refl.
  Definition a36 : Addr := A 36 eq_refl.
  Definition a37 : Addr := A 37 eq_refl.
  Definition a38 : Addr := A 38 eq_refl.
  Definition a39 : Addr := A 39 eq_refl.
  Definition a40 : Addr := A 40 eq_refl.
  Definition a41 : Addr := A 41 eq_refl.
  Definition a42 : Addr := A 42 eq_refl.
  Definition a43 : Addr := A 43 eq_refl.
  Definition a44 : Addr := A 44 eq_refl.
  Definition a45 : Addr := A 45 eq_refl.
  Definition a46 : Addr := A 46 eq_refl.
  Definition a47 : Addr := A 47 eq_refl.
  Definition a48 : Addr := A 48 eq_refl.
  Definition a49 : Addr := A 49 eq_refl.
  Definition a50 : Addr := A 50 eq_refl.
  Definition a51 : Addr := A 51 eq_refl.
  Definition a52 : Addr := A 52 eq_refl.
  Definition a53 : Addr := A 53 eq_refl.
  Definition a54 : Addr := A 54 eq_refl.
  Definition a55 : Addr := A 55 eq_refl.
  Definition a56 : Addr := A 56 eq_refl.
  Definition a57 : Addr := A 57 eq_refl.
  Definition a58 : Addr := A 58 eq_refl.
  Definition a59 : Addr := A 59 eq_refl.
  Definition a60 : Addr := A 60 eq_refl.
  Definition a61 : Addr := A 61 eq_refl.
  Definition a62 : Addr := A 62 eq_refl.
  Definition a63 : Addr := A 63 eq_refl.
  Definition a64 : Addr := A 64 eq_refl.
  Definition a65 : Addr := A 65 eq_refl.
  Definition a66 : Addr := A 66 eq_refl.
  Definition a67 : Addr := A 67 eq_refl.
  Definition a68 : Addr := A 68 eq_refl.
  Definition a69 : Addr := A 69 eq_refl.
  Definition a70 : Addr := A 70 eq_refl.
  Definition a71 : Addr := A 71 eq_refl.
  Definition a72 : Addr := A 72 eq_refl.
  Definition a73 : Addr := A 73 eq_refl.
  Definition a74 : Addr := A 74 eq_refl.
  Definition a75 : Addr := A 75 eq_refl.
  Definition a76 : Addr := A 76 eq_refl.
  Definition a77 : Addr := A 77 eq_refl.
  Definition a78 : Addr := A 78 eq_refl.
  Definition a79 : Addr := A 79 eq_refl.
  Definition a80 : Addr := A 80 eq_refl.
  Definition a81 : Addr := A 81 eq_refl.
  Definition a82 : Addr := A 82 eq_refl.
  Definition a83 : Addr := A 83 eq_refl.
  Definition a84 : Addr := A 84 eq_refl.
  Definition a85 : Addr := A 85 eq_refl.
  Definition a86 : Addr := A 86 eq_refl.
  Definition a87 : Addr := A 87 eq_refl.
  Definition a88 : Addr := A 88 eq_refl.
  Definition a89 : Addr := A 89 eq_refl.
  Definition a90 : Addr := A 90 eq_refl.
  Definition a91 : Addr := A 91 eq_refl.
  Definition a92 : Addr := A 92 eq_refl.
  Definition a93 : Addr := A 93 eq_refl.
  Definition a94 : Addr := A 94 eq_refl.
  Definition a95 : Addr := A 95 eq_refl.
  Definition a96 : Addr := A 96 eq_refl.
  Definition a97 : Addr := A 97 eq_refl.
  Definition a98 : Addr := A 98 eq_refl.
  Definition a99 : Addr := A 99 eq_refl.
  Definition a100 : Addr := A 100 eq_refl.
  Definition a101 : Addr := A 101 eq_refl.
  Definition a102 : Addr := A 102 eq_refl.
  Definition a103 : Addr := A 103 eq_refl.
  Definition a104 : Addr := A 104 eq_refl.
  Definition a105 : Addr := A 105 eq_refl.
  Definition a106 : Addr := A 106 eq_refl.
  Definition a107 : Addr := A 107 eq_refl.
  Definition a108 : Addr := A 108 eq_refl.
  Definition a109 : Addr := A 109 eq_refl.
  Definition a110 : Addr := A 110 eq_refl.
  Definition a111 : Addr := A 111 eq_refl.
  Definition a112 : Addr := A 112 eq_refl.
  Definition a113 : Addr := A 113 eq_refl.
  Definition a114 : Addr := A 114 eq_refl.
  Definition a115 : Addr := A 115 eq_refl.
  Definition a116 : Addr := A 116 eq_refl.
  Definition a117 : Addr := A 117 eq_refl.
  Definition a118 : Addr := A 118 eq_refl.
  Definition a119 : Addr := A 119 eq_refl.
  Definition a120 : Addr := A 120 eq_refl.
  Definition a121 : Addr := A 121 eq_refl.
  Definition a122 : Addr := A 122 eq_refl.
  Definition a123 : Addr := A 123 eq_refl.
  Definition a124 : Addr := A 124 eq_refl.
  Definition a125 : Addr := A 125 eq_refl.
  Definition a126 : Addr := A 126 eq_refl.
  Definition a127 : Addr := A 127 eq_refl.
  Definition a128 : Addr := A 128 eq_refl.
  Definition a129 : Addr := A 129 eq_refl.
  Definition a130 : Addr := A 130 eq_refl.
  Definition a131 : Addr := A 131 eq_refl.
  Definition a132 : Addr := A 132 eq_refl.
  Definition a133 : Addr := A 133 eq_refl.
  Definition a134 : Addr := A 134 eq_refl.
  Definition a135 : Addr := A 135 eq_refl.
  Definition a136 : Addr := A 136 eq_refl.
  Definition a137 : Addr := A 137 eq_refl.
  Definition a138 : Addr := A 138 eq_refl.
  Definition a139 : Addr := A 139 eq_refl.
  Definition a140 : Addr := A 140 eq_refl.
  Definition a141 : Addr := A 141 eq_refl.
  Definition a142 : Addr := A 142 eq_refl.
  Definition a143 : Addr := A 143 eq_refl.
  Definition a144 : Addr := A 144 eq_refl.
  Definition a145 : Addr := A 145 eq_refl.
  Definition a146 : Addr := A 146 eq_refl.
  Definition a147 : Addr := A 147 eq_refl.
  Definition a148 : Addr := A 148 eq_refl.
  Definition a149 : Addr := A 149 eq_refl.
  Definition a150 : Addr := A 150 eq_refl.
  Definition a151 : Addr := A 151 eq_refl.
  Definition a152 : Addr := A 152 eq_refl.
  Definition a153 : Addr := A 153 eq_refl.
  Definition a154 : Addr := A 154 eq_refl.
  Definition a155 : Addr := A 155 eq_refl.
  Definition a156 : Addr := A 156 eq_refl.
  Definition a157 : Addr := A 157 eq_refl.
  Definition a158 : Addr := A 158 eq_refl.
  Definition a159 : Addr := A 159 eq_refl.
  Definition a160 : Addr := A 160 eq_refl.

  Lemma a0a1 : (a0 + 1)%a = Some a1.
  Proof.
    unfold incr_addr. simpl. do 2 f_equal. apply eq_proofs_unicity. decide equality.
  Qed.
  
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


   Ltac discharge_not_or :=
     rewrite /not; intros Hor;
       by repeat (destruct Hor as [Hcontr | Hor]; first inversion Hcontr).
  
  (* helper lemmas *)
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


   (* Lemmas for dealing with increasing list of addresses *)
   Lemma incr_list_lt (a : list Addr) (a0 an : Addr) :
    (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj) →
    a !! 0 = Some a0 → list.last a = Some an → (a0 ≤ an)%Z.
  Proof.
    generalize a0 an. induction a as [_ | a al IHa ]; intros a0' an' Hcond Hfirst Hlast;
     first inversion Hfirst.  
    simpl in Hfirst. inversion Hfirst. subst.
    destruct al as [_ | hd tl ].
    - inversion Hlast. omega.
    - assert ((a0' :: hd :: tl) !! 0 = Some a0') as Ha0; auto.
      assert ((a0' :: hd :: tl) !! 1 = Some hd) as Ha; auto.
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
  
  Lemma incr_list_le_middle (a : list Addr) i (ai an : Addr) :
    (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj) →
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

   Lemma incr_list_lt_middle (a : list Addr) i (ai an : Addr) :
    (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj) →
    a !! i = Some ai → list.last a = Some an → (ai ≠ an)%Z → (ai < an)%Z.
   Proof.
     intros Hreg Ha Hj Hne.
     assert (ai ≤ an)%Z as Hinc; first (apply incr_list_le_middle with a i; auto).
     apply Z.lt_eq_cases in Hinc as [Hlt | Heq]; auto.
     apply neq_z_of in Hne. congruence. 
  Qed.

  Lemma incr_list_lt_succ (a : list Addr) (a0 a1 : Addr) (i : nat) :
    (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj) →
    a !! i = Some a0 → a !! (S i) = Some a1 → (a0 < a1)%Z.
  Proof.
    intros Hcond Hi Hsi.
    specialize Hcond with i a0 a1; simpl in Hcond. 
    apply Hcond in Hi; try rewrite Nat.add_1_r; auto.
    rewrite /incr_addr in Hi.
    destruct (Z_le_dec (a0 + 1)%Z MemNum); inversion Hi. simpl. omega.
  Qed.

  Lemma next_lt (a a' : Addr) : 
    (a + 1)%a = Some a' → (a < a')%Z.
  Proof.
    rewrite /incr_addr. intros Ha'.
    destruct (Z_le_dec (a + 1)%Z MemNum); inversion Ha'.
    simpl. lia.
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
    - exists a161; done.
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
     
   Lemma region_addrs_aux_contiguous a n i ai aj :
     region_addrs_aux a n !! i = Some ai
     → (a + n + 1 < MemNum)%Z
     → region_addrs_aux a n !! (i + 1) = Some aj → (ai + 1)%a = Some aj.
   Proof.
     intros Hai Haj Hlast.
     apply (region_addrs_aux_next a n i ai aj) in Hai as Hnext; auto.
      destruct (ai + 1)%a; simpl in Hnext.
     - congruence.
     - assert (i < n).
       { rewrite -(region_addrs_aux_length n a).
         apply lookup_lt_is_Some_1. eauto. }
       assert (aj ≠ top)%a.
       { apply (region_addrs_lt_top a n (i + 1) aj); [|done].
         rewrite Nat.add_comm /=.
         apply Z.lt_trans with (a + n + 1)%Z; [lia|done].          
       } congruence.
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