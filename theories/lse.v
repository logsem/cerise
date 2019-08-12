From cap_machine Require Import rules logrel fundamental addr_reg_sample.
From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.

Section lse.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ}.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- STACK MACROS AND THEIR SPECS -------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition push_r (a1 a2 : Addr) (r_stk r : RegName) : iProp Σ :=
    (a1 ↦ₐ lea_z r_stk 1
   ∗ a2 ↦ₐ store_r r_stk r)%I.
  
  Lemma push_r_spec a1 a2 a3 w w' r p g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) →
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a') = true →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ push_r a1 a2 r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ stk_a' ↦ₐ w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a3) ∗ push_r a1 a2 r_stk r ∗
            r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a') ∗ r ↦ᵣ w' ∗ stk_a' ↦ₐ w'
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof. 
    iIntros ([Hvpc1 Hvpc2] Hwb Hsuc Hlea Hstk)
            "([Ha1 Ha2] & HPC & Hr_stk & Hr & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a1 a2 _ r_stk RWLX with "[HPC Ha1 Hr_stk]");
      eauto; try apply lea_z_i; iFrame. 
    iNext. iIntros "(HPC & Ha1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_reg _ _ _ _ _ a2 a3 _ r_stk r _ RWLX Local
              with "[HPC Ha2 Hr_stk Hr Hstk_a']"); eauto; try apply store_r_i; iFrame.
    iNext. iIntros "(HPC & Ha2 & Hr & Hr_stk & Hstk_a') /=".
    iApply wp_pure_step_later; auto. iNext. iApply "Hφ". iFrame.
  Qed.

  
  Definition push_z (a1 a2 : Addr) (r_stk : RegName) (z : Z) : iProp Σ :=
    (a1 ↦ₐ lea_z r_stk 1
   ∗ a2 ↦ₐ store_z r_stk z)%I.
  
  Lemma push_z_spec a1 a2 a3 w z p g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) →
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a') = true →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ push_z a1 a2 r_stk z
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a' ↦ₐ w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a3) ∗ push_z a1 a2 r_stk z ∗
            r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a') ∗ stk_a' ↦ₐ inl z
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof. 
    iIntros ([Hvpc1 Hvpc2] Hwb Hsuc Hlea Hstk)
            "([Ha1 Ha2] & HPC & Hr_stk & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a1 a2 _ r_stk RWLX with "[HPC Ha1 Hr_stk]");
      eauto; first apply lea_z_i; iFrame. 
    iNext. iIntros "(HPC & Ha1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_z _ _ _ _ _ a2 a3 _ r_stk _ _ RWLX
              with "[HPC Ha2 Hr_stk Hstk_a']"); eauto; first apply store_z_i; iFrame.
    iNext. iIntros "(HPC & Ha2 & Hr & Hr_stk & Hstk_a') /=".
    iApply wp_pure_step_later; auto. iNext. iApply "Hφ". iFrame.
  Qed.


  Definition pop (a1 a2 a3 : Addr) (r_stk r : RegName) : iProp Σ :=
    (a1 ↦ₐ load_r r r_stk
   ∗ a2 ↦ₐ sub_z_z r_t1 0 1
   ∗ a3 ↦ₐ lea_r r_stk r_t1)%I.

  Lemma pop_spec a1 a2 a3 a4 r w w' wt1 p g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) ∧
    isCorrectPC (inr ((p,g),b,e,a3)) →
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a) = true →
    r ≠ PC →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (a3 + 1)%a = Some a4 →
    (stk_a + (-1))%a = Some stk_a' →

      ▷ pop a1 a2 a3 r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a ↦ₐ w
    ∗ ▷ r_t1 ↦ᵣ wt1
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a4) ∗ pop a1 a2 a3 r_stk r ∗ r ↦ᵣ w ∗ stk_a ↦ₐ w ∗
            r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a') ∗ r_t1 ↦ᵣ (inl (-1)%Z)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ((Hvpc1 & Hvpc2 & Hvpc3) Hwb Hne Ha1' Ha2' Ha3' Hstk_a')
            "((>Ha1 & >Ha2 & >Ha3) & >HPC & >Hr_stk & >Hstk_a & >Hr_t1 & Hr & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_load_success _ _ _ _ _ _ _ a1 _ _ _ RWLX
              with "[HPC Ha1 Hr_stk Hr Hstk_a]"); eauto; first apply load_r_i; iFrame.
    iNext. iIntros "(HPC & Hr & Ha1 & Hr_stk & Hstk_a) /=".
    iApply wp_pure_step_later; auto; iNext. 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_sub_success_z_z _ r_t1 _ _ _ _ _ _ a2 with "[HPC Ha2 Hr_t1]");
      eauto; first apply sub_z_z_i; iFrame.
    iNext. iIntros "(HPC & Hr_t1 & Ha2) /=".
    iApply wp_pure_step_later; auto; iNext. 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_reg _ _ _ _ _ a3 a4 _ r_stk _ RWLX
              with "[HPC Ha3 Hr_stk Hr_t1]"); eauto; first apply lea_r_i; iFrame.
    iNext. iIntros "(HPC & Ha3 & Hr_t1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto; iNext.
    iApply "Hφ". iFrame. 
  Qed.

  (* Lemmas for dealing with increasing list of addresses *)
   Lemma incr_list_lt (a : list Addr) (a0 an : Addr) :
    (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj) →
    a !! 0 = Some a0 → list.last a = Some an → (a0 ≤ an)%Z.
  Proof.
    generalize a0 an. induction a; intros a0' an' Hcond Hfirst Hlast;
     first inversion Hfirst.  
    simpl in Hfirst. inversion Hfirst. subst.
    destruct a1.
    - inversion Hlast. omega.
    - assert ((a0' :: a :: a1) !! 0 = Some a0') as Ha0; auto.
      assert ((a0' :: a :: a1) !! 1 = Some a) as Ha; auto.
      apply Hcond with 0 a0' a in Ha0 as Hnext; auto. 
      assert ((a :: a1) !! 0 = Some a) as Ha'; auto.
      assert (list.last (a :: a1) = Some an').
      { simpl. destruct a1; auto. }
      apply IHa with a an' in Ha'; auto.
      + assert (a0' ≤ a)%Z.
        {  rewrite /incr_addr in Hnext.
           destruct (Z_le_dec (a0' + 1)%Z MemNum); inversion Hnext. simpl. omega. }
        apply Z.le_trans with a; auto. 
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
      assert ((drop (i + 1) a) !! 0 = Some ai').
      { rewrite -(Nat.add_0_r (i + 1)) in Hi'.
        rewrite -Hi'. apply (lookup_drop a (i + 1) 0). }
      apply incr_list_lt with _ _ an in H3; auto.
      + intros. 
        rewrite (lookup_drop) /= in H4. rewrite (lookup_drop) /= in H5.
        apply Hcond with (i + 1 + i0); auto.
        rewrite Nat.add_assoc in H5. done.
      + assert (is_Some (a !! (i + 1))) as Hsome; eauto. 
        apply lookup_lt_is_Some_1 in Hsome as Hlength. 
        apply last_drop_lt; auto. 
  Qed.

   Lemma incr_list_lt_middle (a : list Addr) i (ai an : Addr) :
    (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj) →
    a !! i = Some ai → list.last a = Some an → (ai ≠ an)%Z → (ai < an)%Z.
   Proof.
     intros.
     assert (ai ≤ an)%Z; first (apply incr_list_le_middle with a i; auto).
     apply Z.lt_eq_cases in H7 as [Hlt | Heq]; auto.
     apply neq_z_of in H6. congruence. 
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
  
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
  Definition rclear (a : list Addr) (r : list RegName) : iProp Σ :=
    if ((length a) =? (length r))%nat then
      ([∗ list] k↦a_i;r_i ∈ a;r, a_i ↦ₐ move_z r_i 0)%I
    else
      False%I.

  (* the following macro clears the region of memory a capability govers over. a denotes
     the list of adresses containing the instructions for the clear. |a| = 21 *)

  (* first we will define the list of Words making up the mclear macro *)
  Definition mclear_prog r_stk off_end off_iter :=
    [ move_r r_t4 r_stk;
      getb r_t1 r_t4; 
      geta r_t2 r_t4; 
      sub_r_r r_t2 r_t1 r_t2; 
      lea_r r_t4 r_t2;
      gete r_t5 r_t4;
      move_r r_t2 PC;
      lea_z r_t2 off_end; (* offset to "end" *)
      move_r r_t3 PC;
      lea_z r_t3 off_iter; (* offset to "iter" *)
    (* iter: *)
      lt_r_r r_t6 r_t5 r_t1; 
      jnz r_t2 r_t6;
      store_z r_t4 0; 
      lea_z r_t4 1;
      add_r_z r_t1 r_t1 1; 
      jmp r_t3; 
    (* end: *)
      move_z r_t4 0;
      move_z r_t1 0;
      move_z r_t2 0;
      move_z r_t3 0;
      move_z r_t5 0;
      move_z r_t6 0].

  (* Next we define mclear in memory, using a list of addresses of size 21 *)
  Definition mclear (a : list Addr) (r : RegName) (off_end off_iter : Z) : iProp Σ :=
    if ((length a) =? (length (mclear_prog r off_end off_iter)))%nat then
      ([∗ list] k↦a_i;w_i ∈ a;(mclear_prog r off_end off_iter), a_i ↦ₐ w_i)%I
    else
      False%I.

  Lemma isCorrectPC_bounds_alt p g b e (a0 a1 a2 : Addr) :
    isCorrectPC (inr (p, g, b, e, a0))
    → isCorrectPC (inr (p, g, b, e, a2))
    → (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z
    → isCorrectPC (inr (p, g, b, e, a1)). 
  Proof.
    intros Hvpc0 Hvpc2 [Hle0 Hle2].
    apply Z.lt_eq_cases in Hle2 as [Hlt2 | Heq2].
    - apply isCorrectPC_bounds with a0 a2; auto.
    - apply z_of_eq in Heq2. rewrite Heq2. auto.
  Qed.


  Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [_ | a' a]; inversion Hlen; simpl
    end.
  
  Ltac iPrologue prog :=
    (try iPrologue_pre);
    iDestruct prog as "[Hi Hprog]"; 
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _ 
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end. 

  Ltac iCorrectPC index :=
    match goal with
    | [ Hnext : ∀ (i : nat) (ai aj : Addr), ?a !! i = Some ai
                                          → ?a !! (i + 1) = Some aj
                                          → (ai + 1)%a = Some aj,
          Ha_first : ?a !! 0 = Some ?a_first,
          Ha_last : list.last ?a = Some ?a_last |- _ ]
      => apply isCorrectPC_bounds_alt with a_first a_last; eauto; split ;
         [ apply Z.lt_le_incl;auto |
           apply incr_list_le_middle with a index; auto ]
    end.

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
      rewrite Hnone in H4. inversion H4.
  Qed.
    
  Lemma addr_next_lt_gt_contr (a e a' : Addr) :
    (a < e)%Z → (a + 1)%a = Some a' → (e < a')%Z → False.
  Proof.
    intros Hlta Ha' Hlta'.
    rewrite /incr_addr in Ha'.
    destruct (Z_le_dec (a + 1)%Z MemNum); inversion Ha'.
    rewrite -H4 in Hlta'. 
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
    destruct a'. inversion H4; simpl.
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
    inversion H4. inversion H5.  
    rewrite -H6 in H7. subst.
    destruct (Z_le_dec (a1 + (z1 + z2))%Z MemNum).
    - f_equal. apply addr_unique. lia.
    - exfalso. clear fin l l0 H5 H4 Ha2 Ha1.
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
    rewrite H4 in Ha1.
    rewrite -H5 in Ha1.
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
    rewrite H5 in Hai. rewrite Nat.sub_diag in Hai.
    rewrite (region_addrs_aux_decomposition n a i) in Haj; last lia.
    rewrite lookup_app_r in Haj; last lia.
    rewrite H5 in Haj. rewrite minus_plus in Haj.
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
      rewrite H4 in Hai'.
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
             
  Lemma mclear_iter_spec (a1 a2 a3 a4 a5 a6 b_r e_r a_r e_r' : Addr) ws z
        p g b e rt rt1 rt2 rt3 rt4 rt5 a_end (p_r : Perm) (g_r : Locality) φ :
        isCorrectPC (inr ((p,g),b,e,a1))
      ∧ isCorrectPC (inr ((p,g),b,e,a2))
      ∧ isCorrectPC (inr ((p,g),b,e,a3))
      ∧ isCorrectPC (inr ((p,g),b,e,a4))
      ∧ isCorrectPC (inr ((p,g),b,e,a5))
      ∧ isCorrectPC (inr ((p,g),b,e,a6)) →
        (a1 + 1)%a = Some a2
      ∧ (a2 + 1)%a = Some a3
      ∧ (a3 + 1)%a = Some a4
      ∧ (a4 + 1)%a = Some a5
      ∧ (a5 + 1)%a = Some a6 →
        ((b_r + z ≤ e_r)%Z → withinBounds ((p_r,g_r),b_r,e_r,a_r) = true) →
        rt3 ≠ PC ∧ rt ≠ PC ∧ rt1 ≠ PC →
        writeAllowed p_r = true →
        (e_r + 1)%a = Some e_r' →
        (b_r + z)%a = Some a_r →
 
      ([[a_r,e_r]]↦ₐ[[ws]]
     ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
     ∗ ▷ rt ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
     ∗ ▷ rt1 ↦ᵣ inl (b_r + z)%Z
     ∗ ▷ rt2 ↦ᵣ inl (z_of e_r)
     ∗ ▷ (∃ w, rt3 ↦ᵣ w)
     ∗ ▷ rt4 ↦ᵣ inr (p, g, b, e, a_end)
     ∗ ▷ rt5 ↦ᵣ inr (p, g, b, e, a1)
     ∗ ▷ ([∗ list] a_i;w_i ∈ [a1;a2;a3;a4;a5;a6];[lt_r_r rt3 rt2 rt1;
                                                  jnz rt4 rt3;
                                                  store_z rt 0;
                                                  lea_z rt 1;
                                                  add_r_z rt1 rt1 1;
                                                  jmp rt5], a_i ↦ₐ w_i)
     ∗ ▷ (PC ↦ᵣ updatePcPerm (inr ((p,g),b,e,a_end))
             ∗ [[ a_r , e_r ]] ↦ₐ [[ region_addrs_zeroes a_r e_r ]]
             ∗ (∃ a_r, rt ↦ᵣ inr (p_r, g_r, b_r, e_r, a_r))
             ∗ rt5 ↦ᵣ inr (p, g, b, e, a1)
             ∗ a3 ↦ₐ store_z rt 0
             ∗ a4 ↦ₐ lea_z rt 1
             ∗ a5 ↦ₐ add_r_z rt1 rt1 1
             ∗ a6 ↦ₐ jmp rt5
             ∗ a1 ↦ₐ lt_r_r rt3 rt2 rt1
             ∗ rt2 ↦ᵣ inl (z_of e_r)
             ∗ (∃ z, rt1 ↦ᵣ inl (b_r + z)%Z)
             ∗ a2 ↦ₐ jnz rt4 rt3
             ∗ rt4 ↦ᵣ inr (p, g, b, e, a_end)
             ∗ rt3 ↦ᵣ inl 1%Z
              -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hnext Hwb Hne Hwa Her' Hprogress)
            "(Hbe & >HPC & >Hrt & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & >Hprog & Hφ)".
    iRevert (Hwb Hprogress). 
    iLöb as "IH" forall (a_r ws z).
    iIntros (Hwb Hprogress).
    iDestruct "Hr_t3" as (w) "Hr_t3". 
    destruct Hvpc as (Hvpc1 & Hvpc2 & Hvpc3 & Hvpc4 & Hvpc5 & Hvpc6).
    destruct Hnext as (Hnext1 & Hnext2 & Hnext3 & Hnext4 & Hnext5).
    destruct Hne as (Hne1 & Hne2 & Hne3). 
    (* lt rt3 rt2 rt1 *)
    iDestruct "Hprog" as "[Hi Hprog]". 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lt_success _ rt3 rt2 _ rt1 _ _ _ _ _ a1 a2 with "[Hi HPC Hr_t3 Hr_t1 Hr_t2]"); eauto; first apply lt_i. 
    iFrame. iEpilogue "(HPC & Ha1 & Hr_t3 & Hr_t2 & Hr_t1)".
    rewrite /region_mapsto /region_addrs. 
    destruct (Z_le_dec (b_r + z) e_r)%Z; simpl. 
    - assert (Z.b2z (e_r <? b_r + z)%Z = 0%Z) as Heq0.
      { rewrite /Z.b2z. assert (e_r <? b_r + z = false)%Z as Heq; [apply Z.ltb_nlt; omega|].
          by rewrite Heq. }
      rewrite Heq0. 
      (* jnz rt4 rt3 *)
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_jnz_success_next _ rt4 rt3 _ _ _ _ a2 a3 with "[HPC Hi Hr_t3]");
        eauto; first apply jnz_i. 
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t3)". 
      (* store rt 0 *)
      apply Hwb in l as Hwb'.
      rewrite/ withinBounds in Hwb'.
      apply andb_prop in Hwb' as [Hwb_b Hwb_e]. 
      apply (Z.leb_le a_r e_r) in Hwb_e. 
      destruct (Z_le_dec a_r e_r); try contradiction.
      destruct ws as [_ | w1 ws]; [simpl; by iApply bi.False_elim|simpl]. 
      iDestruct "Hbe" as "[Ha_r Hbe]".
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_store_success_z _ _ _ _ _ a3 a4 _ rt 0 _ p_r g_r b_r e_r a_r with "[HPC Hi Hrt Ha_r]"); eauto; first apply store_z_i. 
      iFrame. iEpilogue "(HPC & Ha3 & Hrt & Ha_r)".
      (* lea rt 1 *)
      assert (∃ a_r', (a_r + 1)%a = Some a_r') as [a_r' Ha_r']; [apply addr_next_le with e_r e_r'; auto|].
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_lea_success_z _ _ _ _ _ a4 a5 _ rt p_r _ _ _ a_r 1 a_r' with "[HPC Hi Hrt]"); eauto; first apply lea_z_i. 
      { destruct p_r; auto. }
      iFrame. iEpilogue "(HPC & Ha4 & Hrt)".
      (* add rt1 rt1 1 *)
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_add_success_r_z_same _ rt1 _ 1 _ _ _ _ a5 a6 with "[HPC Hi Hr_t1]"); eauto; first apply add_r_z_i. 
      iFrame. iEpilogue "(HPC & Hr_t1 & Ha5)".
      (* jmp rt5 *)
      iDestruct "Hprog" as "[Hi _]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_jmp_success _ _ _ _ _ a6 with "[HPC Hi Hr_t5]"); eauto; first apply jmp_i. 
      iFrame. iEpilogue "(HPC & Ha6 & Hr_t5)".
      iApply ("IH" $! a_r' ws (z + 1)%Z with
                  "[Hbe] [HPC] [Hrt] [Hr_t1] [Hr_t2] [Hr_t3] [Hr_t4] [Hr_t5] [Ha1 Ha2 Ha3 Ha4 Ha5 Ha6] [Hφ Ha_r]")
      ; iFrame. 
      + rewrite Ha_r'; simpl.
        destruct (Z_le_dec a_r' e_r).
        { assert (∀ {A : Type} (x : A) (l : list A), x :: l = [x] ++ l) as Hl; auto.
          assert ((a_r < e_r)%Z).
          { apply Z.lt_le_trans with a_r'; eauto.
            rewrite /incr_addr in Ha_r'.
            destruct (Z_le_dec (a_r + 1)%Z MemNum); inversion Ha_r'. simpl. omega.
          }
          rewrite Hl region_addrs_aux_singleton (region_addrs_aux_decomposition _ _ 1); last lia. 
          destruct ws; simpl; first by iApply bi.False_elim.
          iDestruct "Hbe" as "[$ Hbe]".
          rewrite (addr_abs_next _ _ a_r'); auto. 
        }
        { apply Znot_le_gt in n.
          apply Zle_lt_or_eq in Hwb_e as [Hlt | ->]. 
          - apply (addr_next_lt_gt_contr a_r e_r a_r') in Hlt; auto; lia.
          - rewrite Z.sub_diag. iFrame.
        }
      + assert (updatePcPerm (inr (p, g, b, e, a1)) = (inr (p, g, b, e, a1))).
        { rewrite /updatePcPerm. destruct p; auto.
          inversion Hvpc1; destruct H9 as [Hc | [Hc | Hc] ]; inversion Hc. }
        rewrite H3. iFrame.
      + rewrite Z.add_assoc. iFrame.
      + iExists (inl 0%Z). iFrame.
      + iNext.
        iIntros "(HPC & Hregion & Hrt & Hrt5 & Ha3 & Ha4 & Ha5 & Ha6 & Ha1 & Hrt2 & Hrt1 & Ha2 & Hrt4 & Hrt3)".
        iApply "Hφ".
        iFrame.
        rewrite /region_addrs_zeroes.
        destruct (Z_le_dec a_r' e_r).
        { destruct (Z_le_dec a_r e_r); last by iApply bi.False_elim.
          simpl. iFrame.
          assert ((z_of a_r) + 1 = z_of a_r')%Z.
          { rewrite /incr_addr in Ha_r'.
              by destruct (Z_le_dec (a_r + 1)%Z MemNum); inversion Ha_r'. }
          assert ((e_r - a_r) = (Z.succ (e_r - a_r')))%Z; first lia. 
          rewrite H4 Ha_r' /=.
          rewrite Zabs2Nat.inj_succ; last lia.
          rewrite /=. iFrame. }
        { apply Znot_le_gt in n.
          apply Zle_lt_or_eq in Hwb_e as [Hlt | Heq]. 
          - apply (addr_next_lt_gt_contr a_r e_r a_r') in Hlt; auto; lia.
          - rewrite Heq.
            apply z_of_eq in Heq. 
            rewrite Heq. 
            rewrite /region_size Z.sub_diag. simpl.
            destruct (Z_le_dec e_r e_r); last lia. 
            simpl. iFrame. } 
      + iPureIntro.
        intros Hle.
        apply andb_true_intro.
        apply Z.leb_le in Hwb_b. 
        split; apply Z.leb_le.
        * apply Z.le_trans with a_r; auto.
          rewrite /incr_addr in Ha_r'.
          destruct (Z_le_dec (a_r + 1)%Z MemNum); inversion Ha_r'; simpl; omega.  
        * rewrite Z.add_assoc in Hle.
          assert ((z_of b_r) + z = z_of a_r)%Z as Heq_brz.
          { rewrite /incr_addr in Hprogress.
              by destruct (Z_le_dec (b_r + z)%Z MemNum); inversion Hprogress. }
          rewrite Heq_brz in Hle.
          assert ((z_of a_r) + 1 = z_of a_r')%Z as Ha_rz.
          { rewrite /incr_addr in Ha_r'.
              by destruct (Z_le_dec (a_r + 1)%Z MemNum); inversion Ha_r'. }
          rewrite Ha_rz in Hle.
          done. 
      + iPureIntro.
        rewrite -Ha_r'.
        by rewrite (addr_add_assoc _ a_r). 
    - (* b_r + z > e_r case *)
      (* in this case we immediately jump to a_end *)
      (* jnz rt4 rt3 *)
      assert (Z.b2z (e_r <? b_r + z)%Z = 1%Z) as Heq0.
      { rewrite /Z.b2z. assert (e_r <? b_r + z = true)%Z as Heq; [apply Z.ltb_lt; omega|].
          by rewrite Heq. }
      rewrite Heq0. 
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_jnz_success_jmp _ rt4 rt3 _ _ _ _ a2 _ _ (inl 1%Z) with "[HPC Hi Hr_t3 Hr_t4]"); eauto; first apply jnz_i. 
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)". 
      iApply "Hφ". iFrame.
      assert (a_r > e_r)%Z.
      { assert ((z_of b_r) + z = a_r)%Z; 
          first (rewrite /incr_addr in Hprogress;
                   by destruct (Z_le_dec (b_r + z)%Z MemNum); inversion Hprogress).
        rewrite -H3. lia. 
      }
      rewrite /region_addrs_zeroes.
      iDestruct "Hprog" as "(Ha3 & Ha4 & Ha5 & Ha6 & _)".
      destruct (Z_le_dec a_r e_r); try contradiction. iFrame.
      iSplitR; auto. iSplitL "Hrt". iExists (a_r). iFrame. iExists z. iFrame. 
  Qed. 

    
  Lemma mclear_spec (a : list Addr) (r : RegName) 
        (a_last a_first a6' a_end : Addr) p g b e p_r g_r (b_r e_r a_r e_r' : Addr) a' φ :
    (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj) →
    a !! 0 = Some a_first → list.last a = Some a_last →
    (* We will assume that we are not trying to clear memory in a *)
   
    r ≠ PC ∧ writeAllowed p_r = true →
    
    (* (a_r + (b_r - a_r)%Z)%a = Some a_r' → *)
    
    (a !! 6 = Some a6' ∧ (a6' + 10)%a = Some a_end ∧ a !! 16 = Some a_end) →
    (* (a !! 9 = Some a9' ∧ (a9' + 1)%a = a !! 10) → *)
    
    isCorrectPC (inr ((p,g),b,e,a_first)) → isCorrectPC (inr ((p,g),b,e,a_last)) →
    
    (a_last + 1)%a = Some a' →
    (e_r + 1)%a = Some e_r' →

     (mclear a r 10 2
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a_first)
    ∗ ▷ r ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
    ∗ ▷ (∃ w4, r_t4 ↦ᵣ w4)
    ∗ ▷ (∃ w1, r_t1 ↦ᵣ w1)
    ∗ ▷ (∃ w2, r_t2 ↦ᵣ w2)
    ∗ ▷ (∃ w3, r_t3 ↦ᵣ w3)
    ∗ ▷ (∃ w5, r_t5 ↦ᵣ w5)
    ∗ ▷ (∃ w6, r_t6 ↦ᵣ w6)
    ∗ ▷ (∃ ws, [[ b_r , e_r ]] ↦ₐ [[ ws ]])
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a')
            ∗ r_t1 ↦ᵣ inl 0%Z
            ∗ r_t2 ↦ᵣ inl 0%Z
            ∗ r_t3 ↦ᵣ inl 0%Z
            ∗ r_t4 ↦ᵣ inl 0%Z
            ∗ r_t5 ↦ᵣ inl 0%Z
            ∗ r_t6 ↦ᵣ inl 0%Z
            ∗ r ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
            ∗ [[ b_r , e_r ]] ↦ₐ [[region_addrs_zeroes b_r e_r]]
            ∗ mclear a r 10 2 -∗ 
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }})%I.  
  Proof.
    iIntros (Hnext Ha_first Ha_last [Hne Hwa] Hjnz_off Hvpc1 Hvpc2 Ha_last' He_r')
            "(Hmclear & >HPC & >Hr & >Hr_t4 & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t5 & >Hr_t6 & >Hregion & Hφ)".
    iDestruct "Hr_t4" as (w4) "Hr_t4".
    iDestruct "Hr_t1" as (w1) "Hr_t1".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t6" as (w6) "Hr_t6".
    (* destruct Hne as (Hne1 & Hne2 & Hne3 & Hwa). *)
    iAssert (⌜((length a) =? (length (mclear_prog r _ _)) = true)%nat⌝)%I as %Hlen.
    { destruct (((length a) =? (length (mclear_prog r _ _)))%nat) eqn:Hlen; auto.
      rewrite /mclear Hlen. by iApply bi.False_elim. }
    rewrite /mclear Hlen /mclear_prog; simpl in Hlen. apply beq_nat_true in Hlen.
    destruct a as [_ | a1 a]; inversion Hlen; simpl; inversion Ha_first; simplify_eq. 
    iPrologue "Hmclear". 
    iApply (wp_move_success_reg _ _ _ _ _ a_first _ _ r_t4 _ r with "[HPC Hr Hr_t4 Hi]"); eauto; first apply move_r_i. 
    iFrame. iEpilogue "(HPC & Ha_first & Hr_t4 & Hr)". 
    (* getb r_t1 r_t4 *)
    iPrologue "Hprog". 
    assert (a_first < a0)%Z as Hlt0; first (apply incr_list_lt_succ with (a_first :: a0 :: a1 :: a) 0; auto). 
    iApply (wp_getb_success _ _ _ _ _ a0 a1 _ r_t1 _ r_t4 with "[HPC Hi Hr_t1 Hr_t4]");
      eauto; first apply getb_i; first iCorrectPC 1. 
    { apply Hnext with 1; auto. }
    iFrame. iEpilogue "(HPC & Ha0 & Hr_t1 & Hr_t4)".
    iCombine "Ha0 Ha_first" as "Hprog_done". 
    (* geta r_t2 r_t4 *)
    iPrologue "Hprog". 
    assert (a_first < a1)%Z as Hlt1; first middle_lt a0 1. 
    iApply (wp_geta_success _ _ _ _ _ a1 a2 _ r_t2 _ r_t4 with "[HPC Hi Hr_t2 Hr_t4]");
       eauto; first apply geta_i; first iCorrectPC 2. 
    { apply Hnext with 2; auto. }
    iFrame. iEpilogue "(HPC & Ha1 & Hr_t2 & Hr_t4)".
    iCombine "Ha1 Hprog_done" as "Hprog_done". 
    (* sub r_t2 r_t1 r_t2 *)
    iPrologue "Hprog".
    assert (a_first < a2)%Z as Hlt2; first middle_lt a1 2.
    iApply (wp_sub_success_r_r_src_same _ r_t2 r_t1 _ _ _ _ a2 a3 with "[HPC Hi Hr_t1 Hr_t2]"); 
      eauto; first apply sub_r_r_i; first iCorrectPC 3.
    { apply Hnext with 3; auto. }
    iFrame. iEpilogue "(HPC & Hr_t2 & Hr_t1 & Ha2)".
    iCombine "Ha2 Hprog_done" as "Hprog_done". 
    (* lea r_t4 r_t2 *)
    iPrologue "Hprog".
    assert (a_first < a3)%Z as Hlt3; first middle_lt a2 3.
    assert (a_r + (b_r - a_r) = b_r)%Z as Haddmin; first lia.
    assert ((a_r + (b_r - a_r))%a = Some b_r) as Ha_rb_r.
    { rewrite /incr_addr.
      destruct (Z_le_dec (a_r + (b_r - a_r))%Z MemNum).
      - f_equal. destruct b_r. apply addr_unique. done.
      - exfalso. destruct b_r. rewrite Haddmin /= in n.
        destruct Haddmin. 
        apply Z.leb_nle in n. congruence. 
    }
    iApply (wp_lea_success_reg _ _ _ _ _ a3 a4 _ r_t4 r_t2 p_r _ _ _ a_r (b_r - a_r) with "[HPC Hi Hr_t4 Hr_t2]");
      eauto; first apply lea_r_i; first iCorrectPC 4.
    { apply Hnext with 4; auto. }
    { destruct p_r; inversion Hwa; auto. }
    iFrame. iEpilogue "(HPC & Ha3 & Hr_t2 & Hr_t4)".
    iCombine "Ha3 Hprog_done" as "Hprog_done". 
    (* gete r_t2 r_t4 *)
    iPrologue "Hprog".
    assert (a_first < a4)%Z as Hlt4; first middle_lt a3 4.
    iApply (wp_gete_success _ _ _ _ _ a4 a5 _ r_t5 with "[HPC Hi Hr_t5 Hr_t4]");
      eauto; first apply gete_i; first iCorrectPC 5. 
    { apply Hnext with 5; auto. }
    iFrame. iEpilogue "(HPC & Ha4 & Hr_t5 & Hr_t4)".
    iCombine "Ha4 Hprog_done" as "Hprog_done". 
    (* move r_t2 PC *)
    iPrologue "Hprog".
    assert (a_first < a5)%Z as Hlt5; first middle_lt a4 5.
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a5 a6 _ r_t2 with "[HPC Hi Hr_t2]");
      eauto; first apply move_r_i; first iCorrectPC 6.
    { apply Hnext with 6; auto. }
    iFrame. iEpilogue "(HPC & Ha5 & Hr_t2)".
    iCombine "Ha5 Hprog_done" as "Hprog_done". 
    (* lea r_t2 off_end *)
    iPrologue "Hprog".
    assert (a_first < a6)%Z as Hlt6; first middle_lt a5 6.
    assert (p ≠ E) as Hpne.
    { inversion Hvpc1; destruct H18 as [? | [? | ?] ]; subst; auto. }
    iApply (wp_lea_success_z _ _ _ _ _ a6 a7 _ r_t2 p _ _ _ a5 10 a_end with "[HPC Hi Hr_t2]");
      eauto; first apply lea_z_i; first iCorrectPC 7.
    { apply Hnext with 7; auto. }
    { destruct Hjnz_off as (Ha7' & Hoff_end & Ha_end). simpl in Ha7'. congruence. }
    iFrame. iEpilogue "(HPC & Ha6 & Hr_t2)".
    iCombine "Ha6 Hprog_done" as "Hprog_done". 
    (* move r_t3 PC *)
    iPrologue "Hprog".
    assert (a_first < a7)%Z as Hlt7; first middle_lt a6 7.
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a7 a8 _ r_t3 with "[HPC Hi Hr_t3]");
      eauto; first apply move_r_i; first iCorrectPC 8.
    { apply Hnext with 8; auto. }
    iFrame. iEpilogue "(HPC & Ha7 & Hr_t3)".
    iCombine "Ha7 Hprog_done" as "Hprog_done". 
    (* lea r_t3 off_iter *)
    iPrologue "Hprog".
    assert (a_first < a8)%Z as Hlt8; first middle_lt a7 8.
    iApply (wp_lea_success_z _ _ _ _ _ a8 a9 _ r_t3 p _ _ _ a7 2 a9 with "[HPC Hi Hr_t3]");
      eauto; first apply lea_z_i; first iCorrectPC 9.
    { apply Hnext with 9; auto. }
    { assert (2 = 1 + 1)%Z as ->; auto. 
      apply incr_addr_trans with a8. 
      apply Hnext with 8; auto. apply Hnext with 9; auto. }
    iFrame. iEpilogue "(HPC & Ha8 & Hr_t3)".
    iCombine "Ha8 Hprog_done" as "Hprog_done". 
    (* iter *)
    clear H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 Hlt0 Hlt1 Hlt2 Hlt3 Hlt4 Hlt5 Hlt6 Hlt7.
    do 5 iPrologue_pre. clear H4 H5 H6 H7.
    iDestruct "Hprog" as "[Hi1 Hprog]".
    iDestruct "Hprog" as "[Hi2 Hprog]".
    iDestruct "Hprog" as "[Hi3 Hprog]".
    iDestruct "Hprog" as "[Hi4 Hprog]".
    iDestruct "Hprog" as "[Hi5 Hprog]".
    iDestruct "Hprog" as "[Hi6 Hprog]".
    iDestruct "Hregion" as (ws) "Hregion".
    assert (a_first < a9)%Z as Hlt9; first middle_lt a8 9.
    assert (a_first < a10)%Z as Hlt10; first middle_lt a9 10.
    assert (a_first < a11)%Z as Hlt11; first middle_lt a10 11.
    assert (a_first < a12)%Z as Hlt12; first middle_lt a11 12.
    assert (a_first < a13)%Z as Hlt13; first middle_lt a12 13.
    assert (a_first < a14)%Z as Hlt14; first middle_lt a13 14.
    iApply (mclear_iter_spec a9 a10 a11 a12 a13 a14 b_r e_r b_r e_r' _
                             0 p g b e r_t4 r_t1 r_t5 r_t6 r_t2 r_t3 _ p_r g_r
              with "[-]"); auto.
    - repeat split;[iCorrectPC 10|iCorrectPC 11|iCorrectPC 12|iCorrectPC 13|iCorrectPC 14|iCorrectPC 15].
    - repeat split;[apply Hnext with 10; auto|apply Hnext with 11; auto|apply Hnext with 12; auto|
                    apply Hnext with 13; auto|apply Hnext with 14; auto].
    - rewrite Z.add_0_r. intros Hle.
      rewrite /withinBounds.
      apply andb_true_intro.
      split; apply Z.leb_le; lia.
    - apply addr_add_0.
    - rewrite Z.add_0_r.
      iFrame.
      iSplitL "Hr_t6". iNext. iExists w6. iFrame. 
      iSplitR; auto.
      iNext.
      iIntros "(HPC & Hbe & Hr_t4 & Hr_t3 & Ha11 & Ha12 & Ha13 & Ha14 & 
      Ha9 & Hr_t5 & Hr_t1 & Ha10 & Hr_t2 & Hr_t6)".
      iCombine "Ha9 Ha10 Ha11 Ha12 Ha13 Ha14 Hprog_done" as "Hprog_done". 
      iDestruct "Hr_t4" as (a_r0) "Hr_t4".
      iDestruct "Hr_t1" as (z) "Hr_t1".
      assert (updatePcPerm (inr (p, g, b, e, a_end)) = inr (p, g, b, e, a_end)) as ->.
      { rewrite /updatePcPerm.
        destruct p; auto; contradiction. }
      (* move r_t4 0 *)
      iPrologue "Hprog".
      assert (a15 = a_end)%a as Ha15.
      { simpl in Hjnz_off. 
        destruct Hjnz_off as (Ha15 & Ha15' & Hend).
        by inversion Hend. 
      } 
      destruct a as [_ | a16 a]; inversion Hlen. 
      assert (a_first < a15)%Z as Hlt15; first middle_lt a14 15. 
      iApply (wp_move_success_z _ _ _ _ _ a15 a16 _ r_t4 _ 0 with "[HPC Hi Hr_t4]");
        eauto; first apply move_z_i; first iCorrectPC 16.
      { apply Hnext with 16; auto. }
      rewrite Ha15. iFrame. iEpilogue "(HPC & Ha15 & Hr_t4)".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      assert (a_first < a16)%Z as Hlt16; first middle_lt a15 16. 
      iApply (wp_move_success_z _ _ _ _ _ a16 a17 _ r_t1 _ 0 with "[HPC Hi Hr_t1]");
        eauto; first apply move_z_i; first iCorrectPC 17.
      { apply Hnext with 17; auto. }
      iFrame. iEpilogue "(HPC & Ha16 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      assert (a_first < a17)%Z as Hlt17; first middle_lt a16 17. 
      iApply (wp_move_success_z _ _ _ _ _ a17 a18 _ r_t2 _ 0 with "[HPC Hi Hr_t2]");
        eauto; first apply move_z_i; first iCorrectPC 18.
      { apply Hnext with 18; auto. }
      iFrame. iEpilogue "(HPC & Ha17 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      assert (a_first < a18)%Z as Hlt18; first middle_lt a17 18. 
      iApply (wp_move_success_z _ _ _ _ _ a18 a19 _ r_t3 _ 0 with "[HPC Hi Hr_t3]");
        eauto; first apply move_z_i; first iCorrectPC 19.
      { apply Hnext with 19; auto. }
      iFrame. iEpilogue "(HPC & Ha18 & Hr_t3)".
      (* move r_t5 0 *)
      iPrologue "Hprog".
      assert (a_first < a19)%Z as Hlt19; first middle_lt a18 19. 
      iApply (wp_move_success_z _ _ _ _ _ a19 a20 _ r_t5 _ 0 with "[HPC Hi Hr_t5]");
        eauto; first apply move_z_i; first iCorrectPC 20.
      { apply Hnext with 20; auto. }
      iFrame. iEpilogue "(HPC & Ha19 & Hr_t5)".
      (* move r_t6 0 *)
      iPrologue "Hprog".
      assert (a_first < a20)%Z as Hlt20; first middle_lt a19 20. 
      iApply (wp_move_success_z _ _ _ _ _ a20 a' _ r_t6 _ 0 with "[HPC Hi Hr_t6]");
        eauto; first apply move_z_i; first iCorrectPC 21.
      { inversion Ha_last. auto. }
      iFrame. iEpilogue "(HPC & Ha20 & Hr_t6)".
      iApply "Hφ".
      iDestruct "Hprog_done" as "(Ha_iter & Ha10 & Ha11 & Ha12 & Ha13 & Ha14 & Ha8 & Ha7
      & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha1 & Ha0 & Ha_first)".
      iFrame. Unshelve. exact 0. exact 0. 
  Qed.        (* ??? *)
      
    
  Lemma rclear_spec (a : list Addr) (r : list RegName) p g b e a1 an a' φ :
    (∀ i ai aj, a !! i = Some ai → a !! (i + 1) = Some aj → (ai + 1)%a = Some aj) →
    list.last a = Some an → (an + 1)%a = Some a' →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a')) →
    (length a) = (length r) →
    
      ▷ (∃ ws, ([∗ list] k↦r_i;w_i ∈ r;ws, r_i ↦ᵣ w_i))
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ rclear a r    
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a') ∗ ([∗ list] k↦r_i ∈ r, r_i ↦ᵣ inl 0%Z)
            ∗ rclear a r -∗
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hsuc Hend Ha' Hne Hhd [Hvpchd Hvpcend] Har) "(>Hreg & >HPC & Hrclear & Hφ)".
    iRevert (Hne Har Hhd Hvpchd). 
    iInduction (a) as [_ | a1'] "IH" forall (r a1). iIntros (Hne Har Hhd Hvpchd).
    inversion Hhd; simplify_eq.
    iDestruct "Hreg" as (ws) "Hreg". 
    iIntros (Hne Har Hhd Hvpchd).
    iApply (wp_bind (fill [SeqCtx])). rewrite /rclear Har /=.
    rewrite -(beq_nat_refl (length r)). destruct r; inversion Har. 
    iDestruct "Hrclear" as ">Hrclear".
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    iDestruct (big_sepL2_length with "Hreg") as %rws.
    destruct ws; inversion rws. 
    iDestruct (big_sepL2_cons with "Hreg") as "[Hr Hreg]".
    destruct a. 
    - inversion H4; symmetry in H6; apply (nil_length_inv r0) in H6. 
      inversion Hend. inversion Hhd. subst.                                      
      iApply (wp_move_success_z _ _ _ _ _ a1 with "[HPC Ha1 Hr]");
        eauto;first apply move_z_i.
      { apply (not_elem_of_cons) in Hne as [Hne _]. apply Hne. }
      iFrame. iNext. iIntros "(HPC & Han & Hr) /=".
      iApply wp_pure_step_later; auto; iNext. 
      iApply "Hφ". iFrame. 
    - destruct r0; inversion H4.
      iApply (wp_move_success_z _ _ _ _ _ a1 a _ r with "[HPC Ha1 Hr]")
      ; eauto; first apply move_z_i. 
      { apply Hsuc with 0; simpl; auto. }
      { by apply not_elem_of_cons in Hne as [Hne _]. }
      inversion Hhd. subst. 
      iFrame. iNext. iIntros "(HPC & Ha1 & Hr) /=".
      iApply wp_pure_step_later; auto. iNext.
      inversion Hhd; subst.
      iApply ("IH" with "[] [] [Hreg] [HPC] [Hrclear] [Hφ Ha1 Hr]"); iFrame. 
      + iPureIntro. intros i ai aj Hai Haj.
        apply Hsuc with (S i); simpl; eauto.
      + auto.
      + iExists (ws). iFrame. 
        (* iApply big_sepL2_cons. iFrame.  *)
      + simpl. rewrite H6. rewrite -beq_nat_refl. iFrame. 
      + simpl. rewrite H6. rewrite -beq_nat_refl.
        iNext. iIntros "(HPC & Hreg & Hrclear)".
        iApply "Hφ". iFrame. 
      + iPureIntro. by apply not_elem_of_cons in Hne as [_ Hne]. 
      + iPureIntro. simpl. congruence.
      + auto.
      + iPureIntro.
        assert (a1 ≤ a)%Z as Hlow.
        { apply Z.lt_le_incl. apply incr_list_lt_succ with (a1 :: a :: a0) 0; auto. }
      assert (a ≤ an)%Z.
      { apply incr_list_le_middle with (a1 :: a :: a0) 1; auto. }
      assert (a < a')%Z as Hi.
      { apply Z.le_lt_trans with an; auto. rewrite /incr_addr in Ha'.
        destruct (Z_le_dec (an + 1)%Z MemNum); inversion Ha'. simpl. omega. }
        apply isCorrectPC_bounds with a1 a'; eauto. 
  Qed. 
        
  (* encapsulation of local state using local capabilities and scall *)
  (* assume r1 contains an executable pointer to adversarial code 
     (no linking table yet) *)
  Definition f2 (r1 : RegName) : iProp Σ :=
    (    (* push 1 *)
           push_z a0 a1 r_stk 1
    (* scall r1([],[]) *)
         (* push private state *)
         (* push activation code *)
         ∗ push_z a2 a3 r_stk w_1
         ∗ push_z a4 a5 r_stk w_2
         ∗ push_z a6 a7 r_stk w_3
         ∗ push_z a8 a9 r_stk w_4a
         ∗ push_z a10 a11 r_stk w_4b
         ∗ push_z a12 a13 r_stk w_4c
         (* push old pc *)
         ∗ a14 ↦ₐ move_r r_t1 PC
         ∗ a15 ↦ₐ lea_z r_t1 64 (* offset to "after" *)
         ∗ push_r a16 a17 r_stk r_t1
         (* push stack pointer *)
         ∗ a18 ↦ₐ lea_z r_stk 1
         ∗ a19 ↦ₐ store_r r_stk r_stk
         (* set up protected return pointer *)
         ∗ a20 ↦ₐ move_r r_t0 r_stk
         ∗ a21 ↦ₐ lea_z r_t0 (-7)%Z
         ∗ a22 ↦ₐ restrict_z r_t0 (local_e)
         (* restrict stack capability *)
         ∗ a23 ↦ₐ geta r_t1 r_stk
         ∗ a24 ↦ₐ add_r_z r_t1 r_t1 1
         ∗ a25 ↦ₐ gete r_t2 r_stk
         ∗ a26 ↦ₐ subseg_r_r r_stk r_t1 r_t2
         (* clear the unused part of the stack *)
         (* mclear r_stk: *)
         ∗ mclear (region_addrs_aux a27 22) r_stk 10 2 (* contiguous *)
         (* clear non-argument registers *)
         ∗ rclear (region_addrs_aux a49 29)
                  (list_difference all_registers [PC;r_stk;r_t0;r1])
         (* jump to unknown code *)
         ∗ a78 ↦ₐ jmp r1
    (* after: *)
         (* pop the restore code *)
         (* to shorten the program we will do it all at once *)
         ∗ a79 ↦ₐ sub_z_z r_t1 0 7
         ∗ a80 ↦ₐ lea_r r_stk r_t1
         (* pop the private state into appropriate registers *)
    (* END OF SCALL *)
         ∗ a81 ↦ₐ load_r r1 r_stk
         ∗ a82 ↦ₐ sub_z_z r_t1 0 1
         ∗ a83 ↦ₐ lea_r r_stk r_t1
         (* assert r1 points to 1. For "simplicity" I am not using the assert macro ! 
            but rather a hardcoded version for f2. TODO: change this to actual assert *)
         ∗ a84 ↦ₐ move_r r_t1 PC
         ∗ a85 ↦ₐ lea_z r_t1 5(* offset to fail *)
         ∗ a86 ↦ₐ sub_r_z r1 r1 1
         ∗ a87 ↦ₐ jnz r_t1 r1
         ∗ a88 ↦ₐ halt
         (* set the flag to 1 to indicate failure. flag is set to be the address after 
            the program *)
         ∗ a89 ↦ₐ move_r r_t1 PC
         ∗ a90 ↦ₐ lea_z r_t1 4(* offset to flag *)
         ∗ a91 ↦ₐ store_z r_t1 1
         ∗ a92 ↦ₐ halt
    )%I.



  Ltac addr_succ :=
    match goal with
    | H : _ |- (?a1 + ?z)%a = Some ?a2 =>
      rewrite /incr_addr /=; do 2 f_equal; apply eq_proofs_unicity; decide equality
    end.

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
     - rewrite H4 /= in n.
       apply Z.leb_nle in n. congruence.
   Qed. 
     
   Lemma stack_split (b e a a' : Addr) (w1 w2 : list Word) :
     (b ≤ a < e)%Z →
     (a + 1)%a = Some a' →
     (length w1) = (region_size b a) →
     ([[b,e]]↦ₐ[[w1 ++ w2]] ⊣⊢ [[b,a]]↦ₐ[[w1]] ∗ [[a',e]]↦ₐ[[w2]])%I.
   Proof.
     intros [Hba Hae] Ha' Hsize.
     assert (b ≤ e)%Z; first lia.
     assert (a < a')%Z; first by apply next_lt.
     assert (a' ≤ e)%Z; first by apply addr_next_lt with a; auto.
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

   
   Lemma region_addrs_zeroes_valid (a b : Addr) stsf E :
     ([∗ list] w ∈ region_addrs_zeroes a b, ▷ ⟦ w ⟧ stsf E)%I.
   Proof.
     simpl. rewrite /region_addrs_zeroes.
     destruct (Z_le_dec a b); last done. 
     iInduction (region_size a b) as [_ | n] "IHn"; first done.  
     simpl. iSplit; auto. iNext.
     rewrite fixpoint_interp1_eq /=.
     iPureIntro. eauto.
   Qed. 
   
       
  Ltac wp_push_z Hstack a_lo a_hi b e a_cur a_next φ push1 push2 push3 ws prog ptrn :=
    match goal with
    | H : length _ = _ |- _ =>
      let wa := fresh "wa" in
      let Ha := fresh "w"a_next in
      let Ha_next := fresh "H"a_next in
      iDestruct prog as "[Hi Hf2]";
      destruct ws as [_ | wa ws]; first inversion H;
      iDestruct Hstack as "[Ha Hstack]"; 
      iApply (push_z_spec push1 push2 push3 _ _ _ _ _ _ b e a_cur a_next φ);
      eauto; try addr_succ;
      [split; eauto; apply isCorrectPC_bounds with a_lo a_hi; eauto; split; done|];
      iFrame; iNext; iIntros ptrn
    end.

   Ltac wp_push_r Hstack a_lo a_hi b e a_cur a_next φ push1 push2 push3 ws prog ptrn :=
    match goal with
    | H : length _ = _ |- _ =>
      let wa := fresh "wa" in
      let Ha := fresh "w"a_next in
      iDestruct prog as "[Hi Hf2]";
      destruct ws as [_ | wa ws]; first inversion H;
      iDestruct Hstack as "[Ha Hstack]"; 
      iApply (push_r_spec push1 push2 push3 _ _ _ _ _ _ _ b e a_cur a_next φ);
      eauto; try addr_succ;
      [split; eauto; apply isCorrectPC_bounds with a_lo a_hi; eauto; split; done|];
      iFrame; iNext; iIntros ptrn
    end.

   (* The following ltac gets out the next general purpuse register *)
   Ltac get_genpur_reg Hr_gen wsr ptr :=
     let w := fresh "wr" in 
       destruct wsr as [? | w wsr]; first (by iApply bi.False_elim);
       iDestruct Hr_gen as ptr. 

   Lemma subseteq_trans (E1 E2 E3 : coPset) :
     E1 ⊆ E2 → E2 ⊆ E3 → E1 ⊆ E3.
   Proof.
     intros He1 He2.
     apply elem_of_subseteq. intros x Hx.
     assert (∀ x, x ∈ E1 → x ∈ E2) as He1'; first by rewrite -elem_of_subseteq.
     assert (∀ x, x ∈ E2 → x ∈ E3) as He2'; first by rewrite -elem_of_subseteq.
     specialize He1' with x.
     specialize He2' with x. 
     apply He2'. apply He1'. done.
   Qed. 
     

  (* We want to show encapsulation of local state, by showing that an arbitrary adv 
     cannot change what lies on top of the stack after return, i.e. we want to show
     that the last pop indeed loads the value 1 into register r1 *)
  (* to make the proof simpler, we are assuming WLOG the r1 registers is r_t30 *)
  Lemma f2_spec stsf b e a pc_p pc_g pc_b pc_e :
    (* r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 → *)
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a0)) ∧
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,a110)) →
    {{{ r_stk ↦ᵣ inr ((RWLX,Local),a120,a150,a119)
      ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_stk;r_t30]; wsr,
           r_i ↦ᵣ w_i)
      ∗ (∃ ws, [[a120, a150]]↦ₐ[[ws]])
      (* flag *)
      ∗ a93 ↦ₐ inl 0%Z
      (* token which states all invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv *)
      ∗ r_t30 ↦ᵣ inr ((E,Global),b,e,a)
      ∗ (∃ ws : list Word, na_inv logrel_nais
                             (logN.@(b, e)) (read_only_cond b e ws interp))
      (* trusted *)
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a0)
      ∗ f2 r_t30
      (* we start out with arbitrary sts *)
      ∗ sts_full stsf.1 stsf.2.1 stsf.2.2
    }}}
      Seq (Instr Executable)
    {{{ v, RET v; ⌜v = HaltedV⌝ → a93 ↦ₐ inl 0%Z }}}.
  Proof.
    iIntros ([Hvpc0 Hvpc93] φ)
        "(Hr_stk & Hr_gen & Hstack & Hflag & Hna & Hr1 & #Hadv & HPC & Hf2 & Hs) Hφ /=".
    iDestruct "Hr_gen" as (wsr) "Hr_gen". 
    get_genpur_reg "Hr_gen" wsr "[Hrt0 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt1 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt2 Hr_gen]". 
    iDestruct "Hstack" as (ws) "Hstack". 
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 9)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { simpl in Hlength.
      do 9 (destruct ws as [|? ws]; inversion Hlength).
        by exists [w;w0;w1;w2;w3;w4;w5;w6;w7],ws. }
    assert ((a100 ≤ a108)%Z ∧ (a108 < a150)%Z); first (simpl; lia).  
    rewrite Happ (stack_split a120 a150 a128 a129); auto; try addr_succ.
    simpl in Hlength. 
    iDestruct "Hstack" as "[Hstack_own Hstack_adv]".
    rewrite /region_mapsto.
    assert (region_addrs a120 a128 = [a120;a121;a122;a123;a124;a125;a126;a127;a128])
      as ->.
    { rewrite /region_addrs. 
      simpl. repeat f_equal; (apply eq_proofs_unicity; decide equality). }
    wp_push_z "Hstack_own" a0 a110 a120 a150 a119 a120 φ a0 a1 a2 ws_own "Hf2"
              "(HPC & _ & Hr_stk & Ha120)".
    wp_push_z "Hstack" a0 a110 a120 a150 a120 a121 φ a2 a3 a4 ws_own "Hf2"
              "(HPC & _ & Hr_stk & Ha121)".
    wp_push_z "Hstack" a0 a110 a120 a150 a121 a122 φ a4 a5 a6 ws_own "Hf2"
              "(HPC & _ & Hr_stk & Ha122)".
    wp_push_z "Hstack" a0 a110 a120 a150 a122 a123 φ a6 a7 a8 ws_own "Hf2"
              "(HPC & _ & Hr_stk & Ha123)".
    wp_push_z "Hstack" a0 a110 a120 a150 a123 a124 φ a8 a9 a10 ws_own "Hf2"
              "(HPC & _ & Hr_stk & Ha124)".
    wp_push_z "Hstack" a0 a110 a120 a150 a124 a125 φ a10 a11 a12 ws_own "Hf2"
              "(HPC & _ & Hr_stk & Ha125)".
    wp_push_z "Hstack" a0 a110 a120 a150 a125 a126 φ a12 a13 a14 ws_own "Hf2"
              "(HPC & _ & Hr_stk & Ha126)".
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a14 a15 _ r_t1
              with "[Hi Hrt1 HPC]"); eauto; try addr_succ;
      first apply move_r_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hr_t1)". iSimpl.
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply wp_pure_step_later;auto;iNext. 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a15 a16 _ r_t1 pc_p _ _ _ a14 64 a78
              with "[Hi Hr_t1 HPC]"); eauto; try addr_succ;
      first apply lea_z_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    { inversion Hvpc0 as [?????? Hpc_p | ????? Hpc_p];
        destruct Hpc_p as [Hpc_p | [Hpc_p | Hpc_p] ]; congruence. }
    iFrame. iNext. iIntros "(HPC & _ & Hrt_1)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext. 
    wp_push_r "Hstack" a0 a110 a120 a150 a126 a127 φ a16 a17 a18 ws_own "Hf2"
              "(HPC & _ & Hr_stk & Hr_t1 & Ha127)".
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a18 a19 _ r_stk RWLX _ _ _ a127 1 a128
              with "[Hi Hr_stk HPC]"); eauto; try addr_succ;
      first apply lea_z_i; 
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hr_stk)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    destruct ws_own as [_ | wa129 ws_own]; first inversion Hlength';
      iDestruct "Hstack" as "[Ha128 Hstack]".
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_reg_same _ _ _ _ _ a19 a20 _ r_stk _ RWLX
                                 Local a120 a150 a128
              with "[HPC Hi Hr_stk Ha128]"); eauto; try addr_succ;
      first apply store_r_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hr_stk & Ha128)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext. 
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_move_success_reg _ _ _ _ _ a20 a21 _ r_t0 _ r_stk
              with "[HPC Hi Hrt0 Hr_stk]"); eauto; try addr_succ;
      first apply move_r_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hrt0 & Hr_stk)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a21 a22 _ r_t0 RWLX _ _ _ a128 (-7)%Z a121 
              with "[Hi Hrt0 HPC]"); eauto; try addr_succ;
      first apply lea_z_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hrt0)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_restrict_success_z _ _ _ _ _ a22 a23 _ r_t0 RWLX Local a120 a150 a121
        local_e with "[Hi HPC Hrt0]"); eauto; try addr_succ;
      [apply restrict_r_z| | | |];
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    { rewrite epp_local_e /=. auto. }
    iFrame. iNext. iIntros "(HPC & _ & Hrt0)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_geta_success _ _ _ _ _ a23 a24 _ r_t1
              with "[Hi HPC Hr_t1 Hr_stk]"); eauto;try addr_succ;
      first apply geta_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hr_t1 & Hr_stk)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_success_r_z_same _ r_t1 (z_of a128) 1 _ _ _ _ a24 a25
           with "[Hi HPC Hr_t1]"); try addr_succ; eauto; 
      first apply add_r_z_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    iFrame. iNext. iIntros "(HPC & Hr_t1 & _)";iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_gete_success _ _ _ _ _ a25 a26 _ r_t2
              with "[Hi HPC Hrt2 Hr_stk]"); eauto;try addr_succ;
      first apply gete_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    iFrame. iNext. iIntros "(HPC & _ & Hr_t2 & Hr_stk)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_subseg_success _ _ _ _ _ a26 a27 _ r_stk r_t1 r_t2
                              RWLX Local a120 a150 a128 129 150 a129 a150
              with "[Hi HPC Hr_stk Hr_t1 Hr_t2]");eauto;try addr_succ;
      first apply subseg_r_r_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
    { assert (110 ≤ MemNum)%Z; [done|].
      assert (100 ≤ MemNum)%Z; [done|].
      rewrite /z_to_addr.
      destruct ( Z_le_dec 109%Z MemNum),(Z_le_dec 100%Z MemNum); try contradiction.
      split;[rewrite /a109|rewrite /a100];
        do 2 f_equal; apply eq_proofs_unicity; decide equality. 
    }
    iFrame.
    assert ((a150 =? -42)%a = false) as Ha10042;[done|]; rewrite Ha10042.  
    iNext. iIntros "(HPC & _ & Hr_t1 & Hr_t2 & Hr_stk)"; iSimpl.
    iApply wp_pure_step_later; auto;iNext. 
    (* mclear r_stk *)
    assert (list.last (region_addrs_aux a27 22) = Some a48).
    { cbn. cbv. do 2 f_equal. apply eq_proofs_unicity. decide equality. }
    get_genpur_reg "Hr_gen" wsr "[Hrt3 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt4 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt5 Hr_gen]".
    get_genpur_reg "Hr_gen" wsr "[Hrt6 Hr_gen]".
    iDestruct "Hf2" as "[Hi Hf2]".
    iApply (mclear_spec (region_addrs_aux a27 22) r_stk a48 a27 a33 a43
                        pc_p pc_g pc_b pc_e RWLX Local a129 a150 a128 a151 a49 
              with "[-Hstack]");
      try addr_succ; try assumption;[|auto|auto| | | |].  
    { intros j ai aj Hai Haj.
      apply (region_addrs_aux_contiguous a27 22 j ai aj); auto.
      done. }
    { split; [cbn; f_equal; by apply addr_unique|].
      split; [addr_succ|cbn; f_equal; by apply addr_unique].  
    }
    { apply isCorrectPC_bounds with a0 a110; eauto; split; done. }
    { apply isCorrectPC_bounds with a0 a110; eauto; split; done. }
    iFrame.
    iSplitL "Hrt4"; [iNext;iExists _;iFrame|].
    iSplitL "Hr_t1"; [iNext;iExists _;iFrame|].
    iSplitL "Hr_t2"; [iNext;iExists _;iFrame|].
    iSplitL "Hrt3"; [iNext;iExists _;iFrame|].
    iSplitL "Hrt5"; [iNext;iExists _;iFrame|].
    iSplitL "Hrt6"; [iNext;iExists _;iFrame|].
    iSplitL "Hstack_adv"; [iNext;iExists _;iFrame|]. 
    iNext. iIntros "(HPC & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6
                   & Hr_stk & Hstack_adv & _)".
    iDestruct "Hf2" as "[Hi Hf2]".
    clear H3 Hlength'.
    assert (list.last (region_addrs_aux a49 29) = Some a77).
    { cbn. cbv. do 2 f_equal. apply eq_proofs_unicity. decide equality. }
    iApply (rclear_spec (region_addrs_aux a49 29)
                        (list_difference all_registers [PC; r_stk; r_t0; r_t30])
                        _ _ _ _ a49 a77 a78 with "[-]");
      try addr_succ; try assumption; auto. 
    { intros j ai aj Hai Haj.
      apply (region_addrs_aux_contiguous a49 29 j ai aj); eauto.
      done. }
    { apply not_elem_of_list, elem_of_list_here. }
    { split; (apply isCorrectPC_bounds with a0 a110; eauto; split; done). }
    iSplitL "Hr_t1 Hr_t2 Hr_t3 Hr_t4 Hr_t5 Hr_t6 Hr_gen". 
    { iNext. iExists ((repeat (inl 0%Z) 6) ++ wsr); iSimpl. iFrame. }
    iSplitL "HPC";[iFrame|].
    iSplitL "Hi";[iExact "Hi"|].
    iNext. iIntros "(HPC & Hr_gen & _)".
    iPrologue "Hf2".
    iApply (wp_jmp_success _ _ _ _ _ a78 with "[Hi HPC Hr1]");
      first apply jmp_i;
      first (apply isCorrectPC_bounds with a0 a110; eauto; split; done). 
    iFrame. iEpilogue "(HPC & _ & Hr1)"; iSimpl in "HPC".
    (* We have now arrived at the interesting part of the proof: namely the unknown 
       adversary code. In order to reason about unknown code, we must apply the 
       fundamental theorem. To this purpose, we must first define the stsf that will 
       describe the behavior of the memory. *)
    evar (r : gmap RegName Word).
    instantiate (r := <[PC    := inl 0%Z]>
                     (<[r_stk := inr (RWLX, Local, a129, a150, a128)]>
                     (<[r_t0  := inr (E, Local, a120, a150, a121)]>
                     (<[r_t30 := inr (E, Global, b, e, a)]>
                     (create_gmap_default
                (list_difference all_registers [PC; r_stk; r_t0; r_t30]) (inl 0%Z)))))).
    iAssert (interp_expression ⊤ r stsf (inr (RX, Global, b, e, a)))
      as (fs' fr_pub' fr_priv') "(-> & -> & -> & Hvalid)". 
    { iApply fundamental. iLeft. iSplit; auto. }
    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:=inr (RX, Global, b, e, a)]> r))
                          with "[Hr_gen Hr_stk Hrt0 Hr1 HPC]" as "Hmaps".
    { rewrite /r /registers_mapsto (insert_insert _ PC).
      iApply (big_sepM_insert_2 with "[HPC]"); first iFrame.
      iApply (big_sepM_insert_2 with "[Hr_stk]"); first iFrame.
      iApply (big_sepM_insert_2 with "[Hrt0]"); first (rewrite epp_local_e;iFrame).
      iApply (big_sepM_insert_2 with "[Hr1]"); first iFrame.
      assert ((list_difference all_registers [PC; r_stk; r_t0; r_t30]) =
              [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11; r_t12;
               r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22; r_t23; r_t24;
               r_t25; r_t26; r_t27; r_t28; r_t29]) as ->; first auto. 
      rewrite /create_gmap_default. iSimpl in "Hr_gen". 
      repeat (iDestruct "Hr_gen" as "[Hr Hr_gen]";
              iApply (big_sepM_insert_2 with "[Hr]"); first iFrame).
      done. 
    }
    (* r contrains all registers *)
    iAssert (full_map r) as "#full".
    { iIntros (r0).
      iPureIntro.
      assert (r0 ∈ all_registers); [apply all_registers_correct|].
      destruct (decide (r0 = PC)); [subst;rewrite lookup_insert; eauto|]. 
      rewrite lookup_insert_ne;auto.
      destruct (decide (r0 = r_stk)); [subst;rewrite lookup_insert; eauto|]. 
      rewrite lookup_insert_ne;auto.
      destruct (decide (r0 = r_t0)); [subst;rewrite lookup_insert; eauto|]. 
      rewrite lookup_insert_ne;auto.
      destruct (decide (r0 = r_t30)); [subst;rewrite lookup_insert; eauto|].
      rewrite lookup_insert_ne;auto.
      assert (¬ r0 ∈ [PC; r_stk; r_t0; r_t30]).
      { repeat (apply not_elem_of_cons; split; auto). apply not_elem_of_nil. }
      exists (inl 0%Z).
      apply create_gmap_default_lookup. apply elem_of_list_difference. auto.
    }
    (* Need to prove the validity of the continuation, the stack, as well as put
       local memory into invariant. *)
    iMod (inv_alloc
            (nroot.@"Hprog")
            _
            (a79 ↦ₐ sub_z_z r_t1 0 7
            ∗ a80 ↦ₐ lea_r r_stk r_t1
              ∗ a81 ↦ₐ load_r r_t30 r_stk
                ∗ a82 ↦ₐ sub_z_z r_t1 0 1
                  ∗ a83 ↦ₐ lea_r r_stk r_t1
                    ∗ a84 ↦ₐ move_r r_t1 PC
                      ∗ a85 ↦ₐ lea_z r_t1 5
                        ∗ a86 ↦ₐ sub_r_z r_t30 r_t30 1
                          ∗ a87 ↦ₐ jnz r_t1 r_t30
                            ∗ a88 ↦ₐ halt
                              ∗ a89 ↦ₐ move_r r_t1 PC ∗ a90 ↦ₐ lea_z r_t1 4 ∗ a91 ↦ₐ store_z r_t1 1 ∗ a92 ↦ₐ halt)
            with "[Hprog]")%I as "#Hprog".
    { iNext; iFrame. }
    iMod (na_inv_alloc logrel_nais ⊤ (logN.@(a120, a150))
                        (a120 ↦ₐ inl 1%Z
                       ∗ a121 ↦ₐ inl w_1
                       ∗ a122 ↦ₐ inl w_2
                       ∗ a123 ↦ₐ inl w_3
                       ∗ a124 ↦ₐ inl w_4a
                       ∗ a125 ↦ₐ inl w_4b
                       ∗ a126 ↦ₐ inl w_4c
                       ∗ a127 ↦ₐ inr (pc_p, pc_g, pc_b, pc_e, a78)
                       ∗ a128 ↦ₐ inr (RWLX, Local, a120, a150, a128))%I with "[-Hφ Hs Hstack_adv Hvalid Hmaps Hna Hflag]")
      as "#Hlocal".
    { iNext. iFrame. }
    iMod (na_inv_alloc logrel_nais ⊤ (logN.@(a129, a150))
     (∃ ws0 : list Word,
       [[a129,a150]]↦ₐ[[ws0]]
       ∗ (∀ (stsf0 : prodC (leibnizC STS_states)
                       (prodC (leibnizC STS_rels) (leibnizC STS_rels))) 
            (E0 : leibnizC coPset),
            [∗ list] w ∈ ws0, ▷ (((fixpoint interp1) E0) stsf0) w))%I
                                      with "[Hstack_adv]")
      as "#Hstack_adv".
    { iNext. iExists _. iFrame. iIntros (stsf' E'). 
      iApply region_addrs_zeroes_valid. }
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (((fixpoint interp1) ⊤) stsf) (r !r! r1))%I
      with "[-Hs Hmaps Hvalid Hna Hφ Hflag]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_t30 ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_t30)).
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_t30)); [by left|right;auto].  
      }
      destruct H5 as [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      - iIntros "%". contradiction.
      - (* invariant for the stack of the adversary *)
        assert (r !! r_stk = Some (inr (RWLX, Local, a129, a150, a128))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk fixpoint_interp1_eq /=.
        iIntros (_). iExists _,_,_,_,_. do 2 (iSplitR; [eauto|]).
        iFrame "#". 
        iIntros (E' r').
        rewrite /exec_cond.          
        iAlways.
        iIntros (a' stsf') "#Ha #Hfuture".
        iNext. iApply fundamental.
        iRight. iRight. iSplit; auto. 
      - (* continuation *)
        iIntros (_). 
        assert (r !! r_t0 = Some (inr (E, Local, a120, a150, a121))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 fixpoint_interp1_eq /=.
        (* prove continuation *)
        iExists _,_,_,_,_. iSplit;[eauto|].
        iIntros (E' r'). iAlways.
        rewrite /enter_cond. 
        iIntros (stsf') "Hrelated".
        destruct stsf' as [fs' [fr_pub' fr_priv'] ].
        iNext. simpl.
        iExists _,_,_. do 3 (iSplit; [eauto|]).
        iClear "Hrelated". 
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hs & Hna & %)". rename H5 into Hns. 
        iExists _,_,_,_,_. iSplit; [eauto|rewrite /interp_conf].
        (* get the PC, currently pointing to the activation record *)
        iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']".
        { rewrite lookup_insert; eauto. }
        (* get a general purpose register *)
        iAssert (⌜∃ wr_t1, r' !! r_t1 = Some wr_t1⌝)%I as %[rt1w Hrt1];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t1 with "Hmreg'") as "[Hr_t1 Hmreg']".
        { rewrite lookup_delete_ne; auto.
          rewrite lookup_insert_ne; eauto. }
        (* get r_stk *)
        iAssert (⌜∃ wr_stk, r' !! r_stk = Some wr_stk⌝)%I as %[rstkw Hrstk];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_stk with "Hmreg'") as "[Hr_stk Hmreg']".
        { do 2 (rewrite lookup_delete_ne; auto).
          rewrite lookup_insert_ne; eauto. }
        (* get r_t30 *)
        iAssert (⌜∃ wr30, r' !! r_t30 = Some wr30⌝)%I as %[wr30 Hr30];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t30 with "Hmreg'") as "[Hr_t30 Hmreg']".
        { do 3 (rewrite lookup_delete_ne; auto).
          rewrite lookup_insert_ne; eauto. }
        (* open the na invariant for the local stack content *)
        assert (↑logN.@(a120,a150) ⊆ E'); [by apply Hns|].
        
        iMod (na_inv_open logrel_nais ⊤ E' (logN.@(a120,a150)) with "Hlocal Hna")
          as "(>(Ha120 & Ha121 & Ha122 & Ha123 & Ha124 & Ha125 & Ha126 & Ha127 & Ha128) 
          & Hna & Hcls)"; auto.
        (* step through instructions in activation record *)
        (* move rt_1 PC *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_move_success_reg_fromPC _ RX Local a120 a150 a121 a122 (inl w_1)
               with "[HPC Ha121 Hr_t1]");
          [rewrite -i_1; apply decode_encode_inv|
           constructor; auto; split; done|
           addr_succ|
           auto| |].
        iFrame. iEpilogue "(HPC & Ha121 & Hr_t1)".
        (* lea r_t1 7 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_z _ RX Local a120 a150 a122 a123 (inl w_2)
                                 _ RX _ _ _ a121 7 a128 with "[HPC Ha122 Hr_t1]");
          try addr_succ;
          first (rewrite -i_2; apply decode_encode_inv);
          first (constructor; auto; split; done); auto. 
        iFrame. iEpilogue "(HPC & Ha122 & Hr_t1)".
        (* load r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_load_success _ _ _ RX Local a120 a150 a123 (inl w_3) _ _ RX Local a120 a150 a128 a124
                  with "[HPC Ha128 Hr_t1 Hr_stk Ha123]");
         try addr_succ;
         first (rewrite -i_3; apply decode_encode_inv);
         first (constructor; auto; split; done); auto. 
        iFrame. iEpilogue "(HPC & Hr_stk & Ha123 & Hr_t1 & Ha128)".
        (* sub r_t1 0 1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_sub_success_z_z _ _ 0 1 RX Local a120 a150 a124 a125 (inl w_4a)
                  with "[HPC Hr_t1 Ha124]");
          try addr_succ;
          first (rewrite -i_4a; apply decode_encode_inv);
          first (constructor; auto; split; done); auto.
        iFrame. iEpilogue "(HPC & Hr_t1 & Ha124)". 
        (* Lea r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_lea_success_reg _ RX Local a120 a150 a125 a126 (inl w_4b) _ _ RWLX Local a120 a150 a128 (-1) a127
                  with "[HPC Hr_t1 Hr_stk Ha125]");
          try addr_succ;
          first (rewrite -i_4b; apply decode_encode_inv);
          first (constructor; auto; split; done); auto.
        iFrame. iEpilogue "(HPC & Ha125 & Hr_t1 & Hr_stk)".
        (* Load PC r_t1 *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_load_success_PC _ r_stk RX Local a120 a150 a126 (inl w_4c) RWLX Local a120 a150 a127
                                   _ _ _ _ a78 a79
                  with "[HPC Hr_stk Ha126 Ha127]");
          try addr_succ;
          first (rewrite -i_4c; apply decode_encode_inv);
          first (constructor; auto; split; done); auto.
        iFrame. iEpilogue "(HPC & Ha126 & Hr_stk & Ha127)".
        (* we don't want to close the stack invariant yet, as we will now need to pop it *)
        (* iMod ("Hcls" with "[$Ha120 $Ha121 $Ha122 $Ha123 $Ha124 $Ha125 $Ha126 $Ha127 $Ha128 $Hna]") as "Hna". *)
        (* go through rest of the program. We will now need to open the invariant one instruction at a time *)
        (* sub r_t1 0 7 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "[>Ha79 Hprog_rest]" "Hcls'".
        iApply (wp_sub_success_z_z _ r_t1 0 7 _ _ _ _ a79 a80
                  with "[HPC Hr_t1 Ha79]");
          try addr_succ;
          first apply sub_z_z_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Hr_t1 & Ha79)".
        iMod ("Hcls'" with "[$Ha79 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & >Ha80 & Hprog_rest)" "Hcls'".
        iApply (wp_lea_success_reg _ _ _ _ _ a80 a81 _ r_stk r_t1 RWLX _ _ _ a127 (-7)%Z a120
                  with "[HPC Hr_t1 Hr_stk Ha80]");
          try addr_succ;
          first apply lea_r_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Ha80 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* load r_t30 r_stk *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & >Ha81 & Hprog_rest)" "Hcls'".
        iApply (wp_load_success _ r_t30 _ _ _ _ _ a81 _ _ _ RWLX Local a120 a150 a120 a82
                  with "[HPC Ha81 Ha120 Hr_t30 Hr_stk]");
          try addr_succ;
          first apply load_r_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done); auto.
        iFrame. iNext. iIntros "(HPC & Hr_t30 & Ha81 & Hr_stk & Ha120)"; iSimpl.  
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* we will not use the local stack anymore, so we may close the na_inv *)
        iMod ("Hcls" with "[$Ha120 $Ha121 $Ha122 $Ha123 $Ha124 $Ha125 $Ha126 $Ha127 $Ha128 $Hna]") as "Hna".
        (* we will now make the assertion that r_t30 points to 1 *)
        (* sub r_t1 0 1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & >Ha82 & Hprog_rest)" "Hcls'".
        iApply (wp_sub_success_z_z _ r_t1 0 1 _ _ _ _ a82 a83
                  with "[HPC Hr_t1 Ha82]");
          try addr_succ;
          first apply sub_z_z_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Hr_t1 & Ha82)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & >Ha83 & Hprog_rest)" "Hcls'".
        iApply (wp_lea_success_reg _ _ _ _ _ a83 a84 _ r_stk r_t1 RWLX _ _ _ a120 (-1)%Z a119
                  with "[HPC Hr_t1 Hr_stk Ha83]");
          try addr_succ;
          first apply lea_r_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Ha83 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* move r_t1 PC *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & >Ha84 & Hprog_rest)" "Hcls'".
        iApply (wp_move_success_reg_fromPC _ _ _ _ _ a84 a85 _ r_t1
                  with "[HPC Hr_t1 Ha84]");
          try addr_succ;
          first apply move_r_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Ha84 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* lea r_t1 5 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & >Ha85 & Hprog_rest)" "Hcls'".
        iApply (wp_lea_success_z _ _ _ _ _ a85 a86 _ r_t1 pc_p _ _ _ a84 5 a89
               with "[HPC Ha85 Hr_t1]");
          try addr_succ;
          first apply lea_z_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done); first auto. 
        { inversion Hvpc0 as [?????? Hpc_p | ????? Hpc_p];
            destruct Hpc_p as [Hpc_p | [Hpc_p | Hpc_p] ]; congruence. }
        iFrame. iNext. iIntros "(HPC & Ha85 & Hr_t1)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* sub r_t30 r_t30 1 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & >Ha86 & Hprog_rest)" "Hcls'".
        iApply (wp_sub_success_r_z_dst_same _ r_t30 _ _ _ _ a86 a87 _ 1 1
                  with "[HPC Ha86 Hr_t30]");
          try addr_succ;
          first apply sub_r_z_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done); auto. 
        iFrame. iNext. iIntros "(HPC & Hr_t30 & Ha86)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $ Ha86 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* jnz r_t1 r_t30 *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & Ha86 & >Ha87 
        & Hprog_rest)" "Hcls'".
        iApply (wp_jnz_success_next _ r_t1 r_t30 _ _ _ _ a87 a88
                  with "[HPC Ha87 Hr_t30]");
          try addr_succ;
          first apply jnz_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
        iFrame. iNext. iIntros "(HPC & Ha87 & Hr_t30)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Ha86 $Ha87 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* halt *)
        iApply (wp_bind (fill [SeqCtx])). 
        iInv (nroot.@"Hprog") as "(Ha79 & Ha80 & Ha81 & Ha82 & Ha83 & Ha84 & Ha85 & Ha86 & Ha87 & >Ha88
        & Hprog_rest)" "Hcls'".
        iApply (wp_halt _ _ _ _ _ a88 with "[HPC Ha88]");
          first apply halt_i;
          first (apply isCorrectPC_bounds with a0 a110; eauto; split; done).
        iFrame. iNext. iIntros "(HPC & Ha88)".
        iMod ("Hcls'" with "[$Ha79 $Ha80 $Ha81 $Ha82 $Ha83 $Ha84 $Ha85 $Ha86 $Ha87 $Ha88 $Hprog_rest]") as "_".
        iModIntro;iApply wp_pure_step_later;auto;iNext.
        (* halted: need to show post condition *)
        iApply wp_value. iIntros "_".
        evar (r'' : gmap RegName Word).
        instantiate (r'' := <[PC    := inr (pc_p, pc_g, pc_b, pc_e, a88)]>
                           (<[r_t1  := inr (pc_p, pc_g, pc_b, pc_e, a89)]>
                           (<[r_t30 := inl 0%Z]>
                           (<[r_stk := inr (RWLX, Local, a120, a150, a119)]> r')))). 
        iExists r'',fs',fr_pub',fr_priv'.
        iFrame. iSplit;[|iSplit].
        + iDestruct "Hfull'" as %Hfull'.
          iPureIntro.
          intros r0. rewrite /r''.
          destruct (decide (PC = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_t1 = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_t30 = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_stk = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto.
        + rewrite /r''.
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I r'' PC
                       with "[-]") as "Hmreg'"; auto.
          { by rewrite lookup_insert. }
          iFrame. do 2 rewrite delete_insert_delete.
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I
                        (delete PC (<[r_t1:=inr (pc_p, pc_g, pc_b, pc_e, a89)]>
                         (<[r_t30:=inl 0%Z]>
                          (<[r_stk:=inr (RWLX, Local, a120, a150, a119)]> r')))) r_t1
                       with "[-]") as "Hmreg'"; auto.
          { rewrite lookup_delete_ne; auto. by rewrite lookup_insert. }
          iFrame. do 2 rewrite (delete_commute _ r_t1 PC).
          rewrite delete_insert_delete.
          do 2 rewrite (delete_commute _ PC r_t1).
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I
                        (delete r_t1 (delete PC
                            (<[r_t30:=inl 0%Z]>
                             (<[r_stk:=inr (RWLX, Local, a120, a150, a119)]> r')))) r_stk
                       with "[-]") as "Hmreg'"; auto.
          { repeat (rewrite lookup_delete_ne; auto).
            rewrite lookup_insert_ne; auto. by rewrite lookup_insert. }
          iFrame. repeat rewrite (delete_commute _ r_stk _).
          rewrite insert_commute; auto. 
          rewrite delete_insert_delete; auto. 
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I
                  (delete r_t1 (delete PC (delete r_stk (<[r_t30:=inl 0%Z]> r')))) r_t30
                       with "[-]") as "Hmreg'"; auto.
          { repeat (rewrite lookup_delete_ne; auto). by rewrite lookup_insert. }
          iFrame. repeat rewrite (delete_commute _ r_t30 _).  
          rewrite delete_insert_delete. iFrame. 
        + iPureIntro. apply related_sts_refl. 
      - rewrite Hr_t30. 
        assert (r !! r_t30 = Some (inr (E, Global, b, e, a))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some fixpoint_interp1_eq /=.
        iIntros (_). 
        iExists _,_,_,_,_. iSplit; [eauto|].
        iIntros (E' r').
        iAlways. rewrite /enter_cond.
        iIntros (stsf') "_".
        destruct stsf' as [fs' [fr_pub' fr_priv'] ].
        iNext. iApply fundamental.
        iLeft. iSplit; auto. 
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        assert (r !r! r1 = inl 0%Z) as Hr1.
        { rewrite /RegLocate.
          destruct (r !! r1) eqn:Hsome; rewrite Hsome; last done.
          do 4 (rewrite lookup_insert_ne in Hsome;auto).
          assert (Some w = Some (inl 0%Z)) as Heq.
          { rewrite -Hsome. apply create_gmap_default_lookup.
            apply elem_of_list_difference. split; first apply all_registers_correct.
            repeat (apply not_elem_of_cons;split;auto).
            apply not_elem_of_nil. 
          }
          by inversion Heq. 
        }
        rewrite Hr1 fixpoint_interp1_eq /=. iPureIntro. eauto.         
    }
    iAssert (((interp_reg interp stsf ⊤) r))%I as "#HvalR";[iSimpl;auto|].
    iSpecialize ("Hvalid" with "[HvalR Hmaps Hs Hna]").
    { iFrame. iFrame "#".
      iPureIntro. intros ns Hns. auto. }
    iDestruct "Hvalid" as (p' g b0 e0 a0 Heq) "Ho". 
    inversion Heq; subst. rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros "_"; iFrame. 
  Qed. 


End lse.

 