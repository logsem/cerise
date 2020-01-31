From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental monotone. 
From cap_machine Require Export addr_reg_sample contiguous.

Section stack_macros.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  (* ---------------------------- Helper Lemmas --------------------------------------- *)
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

  (* -------------------------------- LTACS ------------------------------------------- *)
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
    | [ Hnext : contiguous ?a,
          Ha_first : ?a !! 0 = Some ?a_first,
          Ha_last : list.last ?a = Some ?a_last |- _ ]
      => apply isCorrectPC_bounds_alt with a_first a_last; eauto; split ;
         [ apply Z.lt_le_incl;auto |
           apply incr_list_le_middle with a index; auto ]
    end.

  Ltac addr_succ :=
    match goal with
    | H : _ |- (?a1 + ?z)%a = Some ?a2 =>
      rewrite /incr_addr /=; do 2 f_equal; apply eq_proofs_unicity; decide equality
    end.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- STACK MACROS AND THEIR SPECS -------------------------- *)
  (* --------------------------------------------------------------------------------- *)
  
  (* -------------------------------------- PUSH ------------------------------------- *)

  Definition push_r_instrs r_stk r := [lea_z r_stk 1 ; store_r r_stk r]. 
                                
  Definition push_r (a1 a2 : Addr) (p : Perm) (r_stk r : RegName) : iProp Σ :=
    ([∗ list] i;a ∈ (push_r_instrs r_stk r);[a1;a2], a ↦ₐ[p] i)%I. 
  
  Lemma push_r_spec a1 a2 a3 w w' r p p' g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) →
    PermFlows p p' -> 
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a') = true →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ push_r a1 a2 p' r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ stk_a' ↦ₐ[RWLX] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a3) ∗ push_r a1 a2 p' r_stk r ∗
            r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a') ∗ r ↦ᵣ w' ∗ stk_a' ↦ₐ[RWLX] w'
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof. 
    iIntros ([Hvpc1 Hvpc2] Hfl Hwb Hsuc Hlea Hstk)
            "([Ha1 [Ha2 _] ] & HPC & Hr_stk & Hr & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a1 a2 _ r_stk RWLX with "[HPC Ha1 Hr_stk]");
      eauto; try apply lea_z_i; iFrame. 
    iNext. iIntros "(HPC & Ha1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_reg _ _ _ _ _ a2 a3 _ r_stk r _ RWLX Local
              with "[HPC Ha2 Hr_stk Hr Hstk_a']"); eauto; try apply store_r_i;
      first apply PermFlows_refl; iFrame.
    iNext. iIntros "(HPC & Ha2 & Hr & Hr_stk & Hstk_a') /=".
    iApply wp_pure_step_later; auto. iNext. iApply "Hφ". iFrame. done. 
  Qed.

  
  Definition push_z_instrs r_stk z := [lea_z r_stk 1; store_z r_stk z]. 
  
  Definition push_z (a1 a2 : Addr) (p : Perm) (r_stk : RegName) (z : Z) : iProp Σ :=
    ([∗ list] i;a ∈ (push_z_instrs r_stk z);[a1;a2], a ↦ₐ[p] i)%I.
  
  Lemma push_z_spec a1 a2 a3 w z p p' g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) →
    PermFlows p p' -> 
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a') = true →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ push_z a1 a2 p' r_stk z
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a' ↦ₐ[RWLX] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a3) ∗ push_z a1 a2 p' r_stk z ∗
            r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a') ∗ stk_a' ↦ₐ[RWLX] inl z
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof. 
    iIntros ([Hvpc1 Hvpc2] Hfl Hwb Hsuc Hlea Hstk)
            "([Ha1 [Ha2 _] ] & HPC & Hr_stk & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a1 a2 _ r_stk RWLX with "[HPC Ha1 Hr_stk]");
      eauto; first apply lea_z_i; iFrame. 
    iNext. iIntros "(HPC & Ha1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_z _ _ _ _ _ a2 a3 _ r_stk _ _ RWLX
              with "[HPC Ha2 Hr_stk Hstk_a']"); eauto; first apply store_z_i;
      first apply PermFlows_refl; iFrame.
    iNext. iIntros "(HPC & Ha2 & Hr_stk & Hstk_a') /=".
    iApply wp_pure_step_later; auto. iNext. iApply "Hφ". iFrame. done. 
  Qed.

  
  (* -------------------------------------- POP -------------------------------------- *)
  Definition pop_instrs r_stk r := [load_r r r_stk; sub_z_z r_t1 0 1; lea_r r_stk r_t1].
  
  Definition pop (a1 a2 a3 : Addr) (p : Perm) (r_stk r : RegName) : iProp Σ :=
    ([∗ list] i;a ∈ (pop_instrs r_stk r);[a1;a2;a3], a ↦ₐ[p] i)%I.

  Lemma pop_spec a1 a2 a3 a4 r w w' wt1 p p' g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) ∧
    isCorrectPC (inr ((p,g),b,e,a3)) →
    PermFlows p p' -> 
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a) = true →
    r ≠ PC →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (a3 + 1)%a = Some a4 →
    (stk_a + (-1))%a = Some stk_a' →

      ▷ pop a1 a2 a3 p' r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ (if (stk_a =? a1)%a then emp else ▷ stk_a ↦ₐ[RWLX] w)
    ∗ ▷ r_t1 ↦ᵣ wt1
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a4)
            ∗ pop a1 a2 a3 p' r_stk r
            ∗ r ↦ᵣ (if (stk_a =? a1)%a then load_r r r_stk else w)
            ∗ (if (stk_a =? a1)%a then emp else stk_a ↦ₐ[RWLX] w)
            ∗ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a')
            ∗ r_t1 ↦ᵣ (inl (-1)%Z)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ((Hvpc1 & Hvpc2 & Hvpc3) Hfl Hwb Hne Ha1' Ha2' Ha3' Hstk_a')
            "((>Ha1 & >Ha2 & >Ha3 & _) & >HPC & >Hr_stk & Hstk_a & >Hr_t1 & Hr & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_load_success _ _ _ _ _ _ _ a1 _ _ _ RWLX
              with "[HPC Ha1 Hr_stk Hr Hstk_a]"); eauto; first apply load_r_i;
      first apply PermFlows_refl;iFrame.
    iNext. iIntros "(HPC & Hr & Ha1 & Hr_stk & Hstk_a) /=".
    iApply wp_pure_step_later; auto; iNext. 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success _ r_t1 _ _ _ _ a2 with "[HPC Ha2 Hr_t1]");
      first (right;left;apply sub_z_z_i); eauto; iFrame; simpl.
    { iSplit; iPureIntro; reflexivity. }
    iNext.
    rewrite sub_z_z_i Ha2'. 
    iIntros "(HPC & Ha2 & _ & _ & Hr_t1) /=".
    iApply wp_pure_step_later; auto; iNext. 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_reg _ _ _ _ _ a3 a4 _ r_stk _ RWLX
              with "[HPC Ha3 Hr_stk Hr_t1]"); eauto; first apply lea_r_i; iFrame.
    iNext. iIntros "(HPC & Ha3 & Hr_t1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto; iNext.
    iApply "Hφ". iFrame. done. 
  Qed.

  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
  Definition rclear_instrs (r : list RegName) := map (λ r_i, move_z r_i 0) r. 
  
  Definition rclear (a : list Addr) (p : Perm) (r : list RegName) : iProp Σ :=
      ([∗ list] k↦a_i;w_i ∈ a;(rclear_instrs r), a_i ↦ₐ[p] w_i)%I.

  Lemma rclear_spec (a : list Addr) (r : list RegName) p p' g b e a1 an a' φ :
    contiguous a →
    list.last a = Some an → (an + 1)%a = Some a' →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a')) →
    PermFlows p p' →
    
      ▷ (∃ ws, ([∗ list] k↦r_i;w_i ∈ r;ws, r_i ↦ᵣ w_i))
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ rclear a p' r    
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a') ∗ ([∗ list] k↦r_i ∈ r, r_i ↦ᵣ inl 0%Z)
            ∗ rclear a p' r -∗
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hsuc Hend Ha' Hne Hhd [Hvpchd Hvpcend] Hfl) "(>Hreg & >HPC & >Hrclear & Hφ)".
    iDestruct (big_sepL2_length with "Hrclear") as %Har. 
    iRevert (Hne Har Hhd Hvpchd). 
    iInduction (a) as [_ | a1'] "IH" forall (r a1). iIntros (Hne Har Hhd Hvpchd).
    inversion Hhd; simplify_eq.
    iDestruct "Hreg" as (ws) "Hreg". 
    iIntros (Hne Har Hhd Hvpchd).
    iApply (wp_bind (fill [SeqCtx])). rewrite /rclear /=.
    (* rewrite -(beq_nat_refl (length r)).  *)destruct r; inversion Har. 
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    iDestruct (big_sepL2_length with "Hreg") as %rws.
    destruct ws; inversion rws. 
    iDestruct (big_sepL2_cons with "Hreg") as "[Hr Hreg]".
    destruct a. 
    - inversion H4; symmetry in H6; apply (nil_length_inv) in H6. 
      inversion Hend. inversion Hhd. subst.                                      
      iApply (wp_move_success_z _ _ _ _ _ a1 with "[HPC Ha1 Hr]");
        eauto;first apply move_z_i.
      { apply (not_elem_of_cons) in Hne as [Hne _]. apply Hne. }
      iFrame. iNext. iIntros "(HPC & Han & Hr) /=".
      iApply wp_pure_step_later; auto; iNext. 
      iApply "Hφ". iFrame. destruct r0; inversion H6. done. 
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
      + simpl. rewrite H6. iFrame. 
      + simpl. rewrite H6. 
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
  
  (* -------------------------------------- MCLEAR ----------------------------------- *)
   (* the following macro clears the region of memory a capability govers over. a denotes
     the list of adresses containing the instructions for the clear. |a| = 21 *)

  (* first we will define the list of Words making up the mclear macro *)
  Definition mclear_instrs r_stk off_end off_iter :=
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
  Definition mclear (a : list Addr) (p : Perm) (r : RegName) (off_end off_iter : Z) : iProp Σ :=
    if ((length a) =? (length (mclear_instrs r off_end off_iter)))%nat then
      ([∗ list] k↦a_i;w_i ∈ a;(mclear_instrs r off_end off_iter), a_i ↦ₐ[p] w_i)%I
    else
      False%I.

  Lemma regname_dupl_false r w1 w2 :
    r ↦ᵣ w1 -∗ r ↦ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %?.
    contradiction. 
  Qed. 
             
  Lemma mclear_iter_spec (a1 a2 a3 a4 a5 a6 b_r e_r a_r e_r' : Addr) ws z
        p p' g b e rt rt1 rt2 rt3 rt4 rt5 a_end (p_r p_r' : Perm) (g_r : Locality) φ :
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
        writeAllowed p_r = true →
        (e_r + 1)%a = Some e_r' →
        (b_r + z)%a = Some a_r →
        PermFlows p p' ->
        PermFlows p_r p_r' -> 
 
      ([[a_r,e_r]] ↦ₐ[p_r'] [[ws]]
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
                                                  jmp rt5], a_i ↦ₐ[p'] w_i)
     ∗ ▷ (PC ↦ᵣ updatePcPerm (inr ((p,g),b,e,a_end))
             ∗ [[ a_r , e_r ]] ↦ₐ[p_r'] [[ region_addrs_zeroes a_r e_r ]]
             ∗ (∃ a_r, rt ↦ᵣ inr (p_r, g_r, b_r, e_r, a_r))
             ∗ rt5 ↦ᵣ inr (p, g, b, e, a1)
             ∗ a3 ↦ₐ[p'] store_z rt 0
             ∗ a4 ↦ₐ[p'] lea_z rt 1
             ∗ a5 ↦ₐ[p'] add_r_z rt1 rt1 1
             ∗ a6 ↦ₐ[p'] jmp rt5
             ∗ a1 ↦ₐ[p'] lt_r_r rt3 rt2 rt1
             ∗ rt2 ↦ᵣ inl (z_of e_r)
             ∗ (∃ z, rt1 ↦ᵣ inl (b_r + z)%Z)
             ∗ a2 ↦ₐ[p'] jnz rt4 rt3
             ∗ rt4 ↦ᵣ inr (p, g, b, e, a_end)
             ∗ rt3 ↦ᵣ inl 1%Z
              -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hnext Hwb Hwa Her' Hprogress Hfl1 Hfl2)
            "(Hbe & >HPC & >Hrt & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & >Hprog & Hφ)".
    iRevert (Hwb Hprogress). 
    iLöb as "IH" forall (a_r ws z).
    iIntros (Hwb Hprogress).
    iDestruct "Hr_t3" as (w) "Hr_t3". 
    destruct Hvpc as (Hvpc1 & Hvpc2 & Hvpc3 & Hvpc4 & Hvpc5 & Hvpc6).
    destruct Hnext as (Hnext1 & Hnext2 & Hnext3 & Hnext4 & Hnext5).
    iAssert (⌜rt1 ≠ PC⌝)%I as %Hne1.
    { destruct (reg_eq_dec rt1 PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t1 HPC") as "Hfalse". }
    iAssert (⌜rt3 ≠ PC⌝)%I as %Hne2.
    { destruct (reg_eq_dec rt3 PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t3 HPC") as "Hfalse". }
    iAssert (⌜rt ≠ PC⌝)%I as %Hne3.
    { destruct (reg_eq_dec rt PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hrt HPC") as "Hfalse". }
    iAssert (⌜rt2 ≠ rt3⌝)%I as %Hne4.
    { destruct (reg_eq_dec rt2 rt3); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t2 Hr_t3") as "Hfalse". }
    iAssert (⌜rt1 ≠ rt3⌝)%I as %Hne5.
    { destruct (reg_eq_dec rt1 rt3); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t1 Hr_t3") as "Hfalse". }
    (* lt rt3 rt2 rt1 *)
    iDestruct "Hprog" as "[Hi Hprog]". 
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success _ rt3 _ _ _ _ a1 _ _ (inr rt2) (inr rt1) _ _
              with "[Hi HPC Hr_t3 Hr_t1 Hr_t2]"); first (right;right;apply lt_i);
      first apply Hfl1; eauto. 
    destruct (reg_eq_dec rt2 rt3),(reg_eq_dec rt1 rt3),(reg_eq_dec rt3 PC);iFrame.
    destruct (reg_eq_dec rt3 PC); try contradiction.
    rewrite Hnext1 lt_i. 
    iEpilogue "(HPC & Ha1 & Hr_t2 & Hr_t1 & Hr_t3)".
    destruct (reg_eq_dec rt2 rt3),(reg_eq_dec rt1 rt3); try contradiction. 
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
        first apply jnz_i; first apply Hfl1;eauto. 
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
      iApply (wp_store_success_z _ _ _ _ _ a3 a4 _ rt 0 _ p_r g_r b_r e_r a_r with "[HPC Hi Hrt Ha_r]"); first apply store_z_i; first apply Hfl1; eauto. 
      iFrame. iEpilogue "(HPC & Ha3 & Hrt & Ha_r)".
      (* lea rt 1 *)
      assert (∃ a_r', (a_r + 1)%a = Some a_r') as [a_r' Ha_r']; [apply addr_next_le with e_r e_r'; auto|].
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_lea_success_z _ _ _ _ _ a4 a5 _ rt p_r _ _ _ a_r 1 a_r' with "[HPC Hi Hrt]"); first apply lea_z_i; first apply Hfl1; eauto. 
      { destruct p_r; auto. }
      iFrame. iEpilogue "(HPC & Ha4 & Hrt)".
      (* add rt1 rt1 1 *)
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_add_sub_lt_success _ rt1 _ _ _ _ a5 _ _ (inr rt1) with "[HPC Hi Hr_t1]");
        first (left;apply add_r_z_i); first apply Hfl1; eauto. 
      { iFrame. iSplit; eauto. by destruct (reg_eq_dec rt1 rt1); try contradiction. }
      destruct (reg_eq_dec rt1 PC),(reg_eq_dec rt1 rt1); try contradiction.
      rewrite Hnext5 add_r_z_i. 
      iEpilogue "(HPC & Ha5 & _ & _ & Hr_t1)".
      (* jmp rt5 *)
      iDestruct "Hprog" as "[Hi _]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_jmp_success _ _ _ _ _ a6 with "[HPC Hi Hr_t5]");
        first apply jmp_i; first apply Hfl1; eauto. 
      iFrame. iEpilogue "(HPC & Ha6 & Hr_t5)".
      iApply ("IH" $! a_r' ws (z + 1)%Z with
                  "[Hbe] [HPC] [Hrt] [Hr_t1] [Hr_t2] [Hr_t3] [Hr_t4] [Hr_t5] [Ha1 Ha2 Ha3 Ha4 Ha5 Ha6] [Hφ Ha_r]")
      ; iFrame. 
      + rewrite Ha_r'; simpl.
        destruct (Z_le_dec a_r' e_r) as [Hle | Hle].
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
        { apply Znot_le_gt in Hle.
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
        destruct (Z_le_dec a_r' e_r) as [Hle | Hle].
        { destruct (Z_le_dec a_r e_r); last by iApply bi.False_elim.
          simpl. iFrame.
          assert ((z_of a_r) + 1 = z_of a_r')%Z.
          { rewrite /incr_addr in Ha_r'.
              by destruct (Z_le_dec (a_r + 1)%Z MemNum); inversion Ha_r'. }
          assert ((e_r - a_r) = (Z.succ (e_r - a_r')))%Z; first lia. 
          rewrite H4 Ha_r' /=.
          rewrite Zabs2Nat.inj_succ; last lia.
          rewrite /=. iFrame. }
        { apply Znot_le_gt in Hle.
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
      iApply (wp_jnz_success_jmp _ rt4 rt3 _ _ _ _ a2 _ _ (inl 1%Z) with "[HPC Hi Hr_t3 Hr_t4]"); first apply jnz_i; first apply Hfl1; eauto. 
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
      Unshelve. apply w1. 
  Qed. 

    
  Lemma mclear_spec (a : list Addr) (r : RegName) 
        (a_last a_first a6' a_end : Addr) p p' g b e p_r p_r' g_r (b_r e_r a_r e_r' : Addr) a' φ :
    contiguous a →
    a !! 0 = Some a_first → list.last a = Some a_last →
    (* We will assume that we are not trying to clear memory in a *)
    r ≠ PC ∧ writeAllowed p_r = true →
    (a !! 6 = Some a6' ∧ (a6' + 10)%a = Some a_end ∧ a !! 16 = Some a_end) →
    
    isCorrectPC (inr ((p,g),b,e,a_first)) → isCorrectPC (inr ((p,g),b,e,a_last)) →
    PermFlows p p' → PermFlows p_r p_r' -> 
    
    (a_last + 1)%a = Some a' →
    (e_r + 1)%a = Some e_r' →

     (mclear a p' r 10 2
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a_first)
    ∗ ▷ r ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
    ∗ ▷ (∃ w4, r_t4 ↦ᵣ w4)
    ∗ ▷ (∃ w1, r_t1 ↦ᵣ w1)
    ∗ ▷ (∃ w2, r_t2 ↦ᵣ w2)
    ∗ ▷ (∃ w3, r_t3 ↦ᵣ w3)
    ∗ ▷ (∃ w5, r_t5 ↦ᵣ w5)
    ∗ ▷ (∃ w6, r_t6 ↦ᵣ w6)
    ∗ ▷ (∃ ws, [[ b_r , e_r ]] ↦ₐ[p_r'] [[ ws ]])
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a')
            ∗ r_t1 ↦ᵣ inl 0%Z
            ∗ r_t2 ↦ᵣ inl 0%Z
            ∗ r_t3 ↦ᵣ inl 0%Z
            ∗ r_t4 ↦ᵣ inl 0%Z
            ∗ r_t5 ↦ᵣ inl 0%Z
            ∗ r_t6 ↦ᵣ inl 0%Z
            ∗ r ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
            ∗ [[ b_r , e_r ]] ↦ₐ[p_r'] [[region_addrs_zeroes b_r e_r]]
            ∗ mclear a p' r 10 2 -∗ 
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }})%I.  
  Proof.
    iIntros (Hnext Ha_first Ha_last [Hne Hwa] Hjnz_off Hvpc1 Hvpc2 Hfl1 Hfl2 Ha_last' He_r')
            "(Hmclear & >HPC & >Hr & >Hr_t4 & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t5 & >Hr_t6 & >Hregion & Hφ)".
    iDestruct "Hr_t4" as (w4) "Hr_t4".
    iDestruct "Hr_t1" as (w1) "Hr_t1".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t6" as (w6) "Hr_t6".
    (* destruct Hne as (Hne1 & Hne2 & Hne3 & Hwa). *)
    iAssert (⌜((length a) =? (length (mclear_instrs r _ _)) = true)%nat⌝)%I as %Hlen.
    { destruct (((length a) =? (length (mclear_instrs r _ _)))%nat) eqn:Hlen; auto.
      rewrite /mclear Hlen. by iApply bi.False_elim. }
    rewrite /mclear Hlen /mclear_instrs; simpl in Hlen. apply beq_nat_true in Hlen.
    destruct a as [_ | a1 a]; inversion Hlen; simpl; inversion Ha_first; simplify_eq. 
    iPrologue "Hmclear". 
    iApply (wp_move_success_reg _ _ _ _ _ a_first _ _ r_t4 _ r with "[HPC Hr Hr_t4 Hi]");
      first apply move_r_i; first apply Hfl1; eauto. 
    iFrame. iEpilogue "(HPC & Ha_first & Hr_t4 & Hr)". 
    (* getb r_t1 r_t4 *)
    iPrologue "Hprog". 
    assert (a_first < a0)%Z as Hlt0; first (apply incr_list_lt_succ with (a_first :: a0 :: a1 :: a) 0; auto). 
    iApply (wp_GetB_success _ r_t1 r_t4 _ _ _ _ a0 _ _ _ a1 with "[HPC Hi Hr_t1 Hr_t4]");
      first apply getb_i; first apply Hfl1; first iCorrectPC 1; eauto. 
    { apply Hnext with 1; auto. }
    iFrame. iEpilogue "(HPC & Ha0 & Hr_t4 & Hr_t1)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|]. 
    iCombine "Ha0 Ha_first" as "Hprog_done". 
    (* geta r_t2 r_t4 *)
    iPrologue "Hprog". 
    assert (a_first < a1)%Z as Hlt1; first middle_lt a0 1. 
    iApply (wp_GetA_success _ r_t2 r_t4 _ _ _ _ a1 _ _ _ a2 with "[HPC Hi Hr_t2 Hr_t4]");
       first apply geta_i; first apply Hfl1; first iCorrectPC 2; auto. 
    { apply Hnext with 2; auto. }
    iFrame. iEpilogue "(HPC & Ha1 & Hr_t4 & Hr_t2)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|]. 
    iCombine "Ha1 Hprog_done" as "Hprog_done". 
    (* sub r_t2 r_t1 r_t2 *)
    iPrologue "Hprog".
    assert (a_first < a2)%Z as Hlt2; first middle_lt a1 2.
    destruct b_r eqn:Hb_r. 
    iApply (wp_add_sub_lt_success _ r_t2 _ _ _ _ a2 _ _ (inr r_t1) (inr r_t2)
              with "[HPC Hi Hr_t1 Hr_t2]"); 
      first (right; left; apply sub_r_r_i); first apply Hfl1; first iCorrectPC 3; eauto. 
    iFrame.
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t2 PC) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t1 r_t2) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t2 r_t2); try contradiction.
    assert ((a2 + 1) = Some a3)%a as ->.
    { apply Hnext with 3; auto. }
    rewrite sub_r_r_i. 
    iEpilogue "(HPC & Ha2 & Hr_t1 & _ & Hr_t2)".
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
      first apply lea_r_i; first apply Hfl1; first iCorrectPC 4; eauto.
    { apply Hnext with 4; auto. }
    { destruct p_r; inversion Hwa; auto. }
    rewrite /z_of Hb_r; iFrame. iEpilogue "(HPC & Ha3 & Hr_t2 & Hr_t4)".
    iCombine "Ha3 Hprog_done" as "Hprog_done". 
    (* gete r_t2 r_t4 *)
    iPrologue "Hprog".
    assert (a_first < a4)%Z as Hlt4; first middle_lt a3 4.
    iApply (wp_GetE_success _ r_t5 _ _ _ _ _ a4 _ _ _ a5 with "[HPC Hi Hr_t5 Hr_t4]");
      first apply gete_i; first apply Hfl1; first iCorrectPC 5; eauto. 
    { apply Hnext with 5; auto. }
    do 2 iFrame.
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t4 r_t5) as [Hcontr | _]; [inversion Hcontr|].
    iEpilogue "(HPC & Ha4 & Hr_t4 & Hr_t5)".
    iCombine "Ha4 Hprog_done" as "Hprog_done". 
    (* move r_t2 PC *)
    iPrologue "Hprog".
    assert (a_first < a5)%Z as Hlt5; first middle_lt a4 5.
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a5 a6 _ r_t2 with "[HPC Hi Hr_t2]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC 6; eauto. 
    { apply Hnext with 6; auto. }
    iFrame. iEpilogue "(HPC & Ha5 & Hr_t2)".
    iCombine "Ha5 Hprog_done" as "Hprog_done". 
    (* lea r_t2 off_end *)
    iPrologue "Hprog".
    assert (a_first < a6)%Z as Hlt6; first middle_lt a5 6.
    assert (p ≠ E) as Hpne.
    { inversion Hvpc1; destruct H18 as [? | [? | ?] ]; subst; auto. }
    iApply (wp_lea_success_z _ _ _ _ _ a6 a7 _ r_t2 p _ _ _ a5 10 a_end with "[HPC Hi Hr_t2]");
      first apply lea_z_i; first apply Hfl1; first iCorrectPC 7; auto.
    { apply Hnext with 7; auto. }
    { destruct Hjnz_off as (Ha7' & Hoff_end & Ha_end). simpl in Ha7'. congruence. }
    iFrame. iEpilogue "(HPC & Ha6 & Hr_t2)".
    iCombine "Ha6 Hprog_done" as "Hprog_done". 
    (* move r_t3 PC *)
    iPrologue "Hprog".
    assert (a_first < a7)%Z as Hlt7; first middle_lt a6 7.
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a7 a8 _ r_t3 with "[HPC Hi Hr_t3]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC 8; auto.
    { apply Hnext with 8; auto. }
    iFrame. iEpilogue "(HPC & Ha7 & Hr_t3)".
    iCombine "Ha7 Hprog_done" as "Hprog_done". 
    (* lea r_t3 off_iter *)
    iPrologue "Hprog".
    assert (a_first < a8)%Z as Hlt8; first middle_lt a7 8.
    iApply (wp_lea_success_z _ _ _ _ _ a8 a9 _ r_t3 p _ _ _ a7 2 a9 with "[HPC Hi Hr_t3]");
      first apply lea_z_i; first apply Hfl1; first iCorrectPC 9; auto.
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
                        0 p p' g b e r_t4 r_t1 r_t5 r_t6 r_t2 r_t3 _ p_r p_r' g_r
              with "[-]"); auto.
    - split; [|(split; [|(split; [|(split; [|split])])])]; [iCorrectPC 10|iCorrectPC 11|iCorrectPC 12|iCorrectPC 13|iCorrectPC 14|iCorrectPC 15].
    - repeat split;[apply Hnext with 10; auto|apply Hnext with 11; auto|apply Hnext with 12; auto|
                    apply Hnext with 13; auto|apply Hnext with 14; auto].
    - rewrite Z.add_0_r. intros Hle.
      rewrite /withinBounds.
      apply andb_true_intro.
      split; apply Z.leb_le; lia.
    - apply addr_add_0.
    - rewrite Z.add_0_r -Hb_r.
      iFrame. rewrite Hb_r /=; iFrame. 
      iSplitL "Hr_t6". iNext. iExists w6. iFrame. 
      iSplitR; auto.
      iNext. rewrite -Hb_r. 
      iIntros "(HPC & Hbe & Hr_t4 & Hr_t3 & Ha11 & Ha12 & Ha13 & Ha14 & 
      Ha9 & Hr_t5 & Hr_t1 & Ha10 & Hr_t2 & Hr_t6)".
      iCombine "Ha9 Ha10 Ha11 Ha12 Ha13 Ha14 Hprog_done" as "Hprog_done". 
      iDestruct "Hr_t4" as (a_r0) "Hr_t4".
      iDestruct "Hr_t1" as (z0) "Hr_t1".
      (* assert (match p with *)
      (*        | E => inr (RX, g, b, e, a_end) *)
      (*        | _ => inr (p, g, b, e, a_end) *)
      (*        end = inr (p, g, b, e, a_end)) as ->. *)
      (* { rewrite /updatePcPerm. *)
      (*   destruct p; auto; contradiction. } *)
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
        first apply move_z_i; first apply Hfl1; first iCorrectPC 16; auto. 
      { apply Hnext with 16; auto. }
      { rewrite Ha15. destruct p; iFrame. contradiction. }
      iEpilogue "(HPC & Ha15 & Hr_t4)".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      assert (a_first < a16)%Z as Hlt16; first middle_lt a15 16. 
      iApply (wp_move_success_z _ _ _ _ _ a16 a17 _ r_t1 _ 0 with "[HPC Hi Hr_t1]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 17; auto.
      { apply Hnext with 17; auto. }
      iFrame. iEpilogue "(HPC & Ha16 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      assert (a_first < a17)%Z as Hlt17; first middle_lt a16 17. 
      iApply (wp_move_success_z _ _ _ _ _ a17 a18 _ r_t2 _ 0 with "[HPC Hi Hr_t2]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 18; auto.
      { apply Hnext with 18; auto. }
      iFrame. iEpilogue "(HPC & Ha17 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      assert (a_first < a18)%Z as Hlt18; first middle_lt a17 18. 
      iApply (wp_move_success_z _ _ _ _ _ a18 a19 _ r_t3 _ 0 with "[HPC Hi Hr_t3]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 19; auto.
      { apply Hnext with 19; auto. }
      iFrame. iEpilogue "(HPC & Ha18 & Hr_t3)".
      (* move r_t5 0 *)
      iPrologue "Hprog".
      assert (a_first < a19)%Z as Hlt19; first middle_lt a18 19. 
      iApply (wp_move_success_z _ _ _ _ _ a19 a20 _ r_t5 _ 0 with "[HPC Hi Hr_t5]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 20; auto.
      { apply Hnext with 20; auto. }
      iFrame. iEpilogue "(HPC & Ha19 & Hr_t5)".
      (* move r_t6 0 *)
      iPrologue "Hprog".
      assert (a_first < a20)%Z as Hlt20; first middle_lt a19 20. 
      iApply (wp_move_success_z _ _ _ _ _ a20 a' _ r_t6 _ 0 with "[HPC Hi Hr_t6]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 21; auto.
      { inversion Ha_last. auto. }
      iFrame. iEpilogue "(HPC & Ha20 & Hr_t6)".
      iApply "Hφ".
      iDestruct "Hprog_done" as "(Ha_iter & Ha10 & Ha11 & Ha12 & Ha13 & Ha14 & Ha8 & Ha7
      & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha1 & Ha0 & Ha_first)".
      iFrame. Unshelve. exact 0. exact 0. apply w1. 
  Qed.        (* ??? *)


  (* --------------------------------------------------------------------------------- *)
  (* -------------------- USEFUL LEMMAS FOR STACK MANIPULATION ----------------------- *)
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

   (* TODO: move this to folder that will contain all the files about region *)
  
   Fixpoint std_update_temp_multiple W l :=
     match l with
     | [] => W
     | a :: l => std_update (std_update_temp_multiple W l) a Temporary std_rel_pub std_rel_priv
     end.

   Lemma std_update_temp_multiple_loc_sta W l :
     (std_update_temp_multiple W l).2.1 = W.2.1.
   Proof.
     induction l; auto.
   Qed.      

   Lemma std_update_temp_multiple_loc_rel W l :
     (std_update_temp_multiple W l).2.2 = W.2.2.
   Proof.
     induction l; auto.
   Qed.

   Lemma std_update_temp_multiple_swap_head W l a1 a2 :
     std_update_temp_multiple W (a1 :: a2 :: l) = std_update_temp_multiple W (a2 :: a1 :: l).
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
       
   Lemma std_update_temp_multiple_swap W l1 a l2 :
     std_update_temp_multiple W (l1 ++ a :: l2) = std_update_temp_multiple W (a :: l1 ++ l2).
   Proof.
     induction l1; auto.
     rewrite app_comm_cons std_update_temp_multiple_swap_head /=. 
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

   Lemma std_sta_update_temp_multiple_lookup_same W l (a : Addr) :
     a ∉ l -> (std_sta (std_update_temp_multiple W l)) !! (countable.encode a) =
             (std_sta W) !! (countable.encode a).
   Proof.
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hne Hnin].
     rewrite lookup_insert_ne; auto.
     intros Hcontr. apply encode_inj in Hcontr. subst; contradiction.
   Qed.

   Lemma std_rel_update_temp_multiple_lookup_same W l (a : Addr) :
     a ∉ l -> (std_rel (std_update_temp_multiple W l)) !! (countable.encode a) =
             (std_rel W) !! (countable.encode a).
   Proof.
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hne Hnin].
     rewrite lookup_insert_ne; auto.
     intros Hcontr. apply encode_inj in Hcontr. subst; contradiction.
   Qed. 
   
   Lemma std_update_temp_multiple_not_in_sta W l (a : Addr) :
     a ∉ l → (countable.encode a) ∈ dom (gset positive) (std_sta W) ↔
             (countable.encode a) ∈ dom (gset positive) (std_sta (std_update_temp_multiple W l)). 
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
       
   Lemma std_update_temp_multiple_not_in_rel W l (a : Addr) :
     a ∉ l → (countable.encode a) ∈ dom (gset positive) (std_rel W) ↔
             (countable.encode a) ∈ dom (gset positive) (std_rel (std_update_temp_multiple W l)). 
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
     
   Lemma related_sts_pub_update_temp_multiple W l :
     NoDup l →
     Forall (λ a, (countable.encode a) ∉ dom (gset positive) (std_sta W) ∧
                  (countable.encode a) ∉ dom (gset positive) (std_rel W)) l →
     related_sts_pub_world W (std_update_temp_multiple W l).
   Proof.
     intros Hdup Hforall. induction l.
     - split; apply related_sts_pub_refl. 
     - simpl. apply NoDup_cons_iff in Hdup as [Ha Hdup].
       apply list.Forall_cons in Hforall as [ [Ha_std Ha_rel] Hforall].
       eapply related_sts_pub_trans_world;[apply IHl; auto|].
       apply related_sts_pub_world_fresh; auto. 
       + intros Hcontr. apply std_update_temp_multiple_not_in_sta in Hcontr; auto. 
         intros Hcontr'; apply elem_of_list_In in Hcontr'; contradiction.
       + intros Hcontr. apply std_update_temp_multiple_not_in_rel in Hcontr; auto. 
         intros Hcontr'; apply elem_of_list_In in Hcontr'; contradiction.
   Qed.

   Lemma std_update_temp_multiple_lookup W l k y :
     l !! k = Some y →
     region_state_pwl (std_update_temp_multiple W l) y ∧ region_std (std_update_temp_multiple W l) y.
   Proof.
     intros Helem.
     apply elem_of_list_lookup_2 in Helem.
     apply elem_of_list_split in Helem as [l1 [l2 Heq] ].
     rewrite Heq std_update_temp_multiple_swap /= /std_update. split. 
     - rewrite /region_state_pwl /std_sta /=. apply lookup_insert.
     - rewrite /region_std /rel_is_std_i /std_rel /=. apply lookup_insert.
   Qed. 
     
   Lemma std_update_multiple_dom_top_sta W n a :
     a ≠ top ->
     countable.encode a ∉ dom (gset positive) (std_sta W) →
     countable.encode a ∉ dom (gset positive) (std_sta (std_update_temp_multiple W (repeat top n))).
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

   Lemma std_update_multiple_dom_top_rel W n a :
     a ≠ top ->
     countable.encode a ∉ dom (gset positive) (std_rel W) →
     countable.encode a ∉ dom (gset positive) (std_rel (std_update_temp_multiple W (repeat top n))).
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

   Lemma std_update_multiple_dom_sta_i W n a i :
     a ≠ top → (i > 0)%Z →
     countable.encode a ∉ dom (gset positive) (std_sta W) →
     countable.encode a ∉ dom (gset positive) (std_sta (std_update_temp_multiple W (region_addrs_aux (get_addr_from_option_addr (a + i)%a) n))).
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

   Lemma std_update_multiple_dom_rel_i W n a i :
     a ≠ top → (i > 0)%Z →
     countable.encode a ∉ dom (gset positive) (std_rel W) →
     countable.encode a ∉ dom (gset positive) (std_rel (std_update_temp_multiple W (region_addrs_aux (get_addr_from_option_addr (a + i)%a) n))).
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

   Lemma std_sta_update_multiple_insert W (a b a' l : Addr) i r r' :
     (a' < a)%a →
     std_sta (std_update_temp_multiple (std_update W a' i r r') (region_addrs a b)) !! (countable.encode l) =
     std_sta (std_update (std_update_temp_multiple W (region_addrs a b)) a' i r r') !! (countable.encode l).
   Proof.
     intros Hlt. 
     destruct (decide (l ∈ region_addrs a b)).
     - assert (l ≠ a') as Hne.
       { intros Hcontr. apply region_addrs_not_elem_of with _ (region_size a b) _ in Hlt.
         subst. rewrite /region_addrs in e. destruct (Z_le_dec a b); first contradiction.
         apply elem_of_nil in e. done. }
       apply elem_of_list_lookup in e as [n Hsome].
       assert (region_state_pwl (std_update_temp_multiple W (region_addrs a b)) l
               ∧ region_std (std_update_temp_multiple W (region_addrs a b)) l) as [Hpwl _].
       { apply std_update_temp_multiple_lookup with n. auto. }
       assert (region_state_pwl (std_update_temp_multiple (std_update W a' i r r') (region_addrs a b)) l
               ∧ region_std (std_update_temp_multiple (std_update W a' i r r') (region_addrs a b)) l) as [Hpwl' _].
       { apply std_update_temp_multiple_lookup with n. auto. }
       rewrite /region_state_pwl /= in Hpwl. rewrite /region_state_pwl /= in Hpwl'.
       rewrite -Hpwl in Hpwl'. rewrite Hpwl'. 
       rewrite lookup_insert_ne; auto. 
       intros Hcontr. apply encode_inj in Hcontr. subst. contradiction.
     - rewrite std_sta_update_temp_multiple_lookup_same; auto. 
       destruct (decide (countable.encode a' = countable.encode l)).
       + rewrite /std_update /std_sta /= e. do 2 rewrite lookup_insert. done.
       + rewrite /std_update /std_sta /=. rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne; auto.
         rewrite std_sta_update_temp_multiple_lookup_same; auto.
   Qed.

   Lemma std_rel_update_multiple_insert W (a b a' l : Addr) i r r' :
     (a' < a)%a →
     std_rel (std_update_temp_multiple (std_update W a' i r r') (region_addrs a b)) !! (countable.encode l) =
     std_rel (std_update (std_update_temp_multiple W (region_addrs a b)) a' i r r') !! (countable.encode l).
   Proof.
     intros Hlt. 
     destruct (decide (l ∈ region_addrs a b)).
     - assert (l ≠ a') as Hne.
       { intros Hcontr. apply region_addrs_not_elem_of with _ (region_size a b) _ in Hlt.
         subst. rewrite /region_addrs in e. destruct (Z_le_dec a b); first contradiction.
         apply elem_of_nil in e. done. }
       apply elem_of_list_lookup in e as [n Hsome].
       assert (region_state_pwl (std_update_temp_multiple W (region_addrs a b)) l
               ∧ region_std (std_update_temp_multiple W (region_addrs a b)) l) as [_ Hstd].
       { apply std_update_temp_multiple_lookup with n. auto. }
       assert (region_state_pwl (std_update_temp_multiple (std_update W a' i r r') (region_addrs a b)) l
               ∧ region_std (std_update_temp_multiple (std_update W a' i r r') (region_addrs a b)) l) as [_ Hstd'].
       { apply std_update_temp_multiple_lookup with n. auto. }
       rewrite /region_std /rel_is_std_i /= in Hstd. rewrite /region_std /rel_is_std_i /= in Hstd'.
       rewrite -Hstd in Hstd'. rewrite Hstd'. 
       rewrite lookup_insert_ne; auto. 
       intros Hcontr. apply encode_inj in Hcontr. subst. contradiction.
     - rewrite std_rel_update_temp_multiple_lookup_same; auto. 
       destruct (decide (countable.encode a' = countable.encode l)).
       + rewrite /std_update /std_rel /= e. do 2 rewrite lookup_insert. done.
       + rewrite /std_update /std_rel /=. rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne; auto.
         rewrite std_rel_update_temp_multiple_lookup_same; auto.
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
         { apply (std_update_multiple_dom_sta_i _ (S n) _ 1); auto;[|lia]. apply next_lt_top with (S n); auto. lia. }
         { apply (std_update_multiple_dom_rel_i _ (S n) _ 1); auto;[|lia]. apply next_lt_top with (S n); auto. lia. }
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
         { apply (std_update_multiple_dom_sta_i _ (S n) _ 1); auto;[|lia]. apply next_lt_top with (S n); auto. lia. }
         { apply (std_update_multiple_dom_rel_i _ (S n) _ 1); auto;[|lia]. apply next_lt_top with (S n); auto. lia. }
         { iAlways. iIntros (W1 W2 Hrelated) "Hv /=". do 2 (rewrite fixpoint_interp1_eq /=). done. }
         iFrame. done.
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

   (* opening a list of invariants all at once *)
   Fixpoint list_names (a : list Addr) : coPset :=
     match a with
     | [] => ∅
     | a0 :: a' => ↑(logN.@a0) ∪ (list_names a')
     end.

   Lemma addr_top_region n :
     (region_addrs_aux addr_reg.top n) = repeat (addr_reg.top) n.
   Proof.
     induction n.
     - done.
     - simpl. f_equal. apply IHn.
   Qed.

   Lemma list_names_repeat_disj a a' n :
     a ≠ a' →
     list_names (repeat a' n) ## ↑logN.@a.
   Proof.
     induction n.
     - intros. apply disjoint_empty_l.
     - intros. simpl. apply disjoint_union_l.
       split.
       + apply ndot_ne_disjoint; auto. 
       + apply IHn; auto.
   Qed. 

   Lemma incr_addr_ne a i :
     i ≠ 0%Z → a ≠ addr_reg.top →
     get_addr_from_option_addr (a + i)%a ≠ a.
   Proof.
     intros Hne0 Hnetop. destruct (a + i)%a eqn:Hai; auto. 
     simpl. destruct a,a0.
     rewrite /not. intros Hcontr.
     inversion Hcontr.
     subst. rewrite /incr_addr in Hai.
     destruct (Z_le_dec (A z fin + i)%Z MemNum); inversion Hai. 
     destruct i; try contradiction; omega.
   Qed.
   
   Lemma list_names_disj a i n :
     a ≠ addr_reg.top → (i > 0)%Z →
    (list_names (region_addrs_aux (get_addr_from_option_addr (a + i)%a) n)) ## (↑logN.@a).
   Proof.
     intros Hnetop. revert i. induction n; simpl; intros i Hne0. 
     - apply disjoint_empty_l.
     - apply disjoint_union_l.
       split.
       + apply ndot_ne_disjoint.
         apply incr_addr_ne; auto. omega. 
       + assert ((get_addr_from_option_addr (get_addr_from_option_addr (a + i) + 1)%a) =
                 (get_addr_from_option_addr (a + (i + 1))%a)) as Heq.
         { rewrite /get_addr_from_option_addr.
           destruct (a + (i + 1))%a eqn:Hai.
           - destruct (a + i)%a eqn:Hcontr.
             + assert ((a1 + 1)%a = Some a0) as ->; last done.
               destruct a,a1.
               rewrite /incr_addr in Hcontr,Hai.
               destruct (Z_le_dec (A z fin + i)%Z MemNum); inversion Hcontr.
               destruct (Z_le_dec (A z fin + (i + 1))%Z MemNum); inversion Hai. 
               subst. rewrite /incr_addr.
               destruct (Z_le_dec (A (z + i) fin0 + 1)%Z MemNum); simpl in *;
                 last omega. f_equal. apply addr_unique. omega. 
             + destruct a,a0.
               rewrite /incr_addr in Hai,Hcontr.
               destruct (Z_le_dec (A z fin + (i + 1))%Z MemNum); inversion Hai.
               destruct (Z_le_dec (A z fin + i)%Z MemNum); inversion Hcontr.
               omega. 
           - destruct (a + i)%a eqn:Hcontr.
             + assert ((a0 + 1)%a = None) as ->; last done.
               destruct a,a0.
               rewrite /incr_addr in Hai,Hcontr.
               destruct (Z_le_dec (A z fin + (i + 1))%Z MemNum); inversion Hai.
               destruct (Z_le_dec (A z fin + i)%Z MemNum); inversion Hcontr.
               subst.
               rewrite /incr_addr.
               destruct (Z_le_dec (A (z + i) fin0 + 1)%Z MemNum); auto.
               simpl in *. omega.                
             + done. 
         }
         destruct (a + i)%a eqn:Hai; simpl.
         * apply addr_add_assoc with a a0 i 1%Z in Hai. rewrite -Hai.
           apply IHn. omega. 
         * rewrite addr_top_region.
           apply list_names_repeat_disj; auto.
      
   Qed.

   (* TODO: move to reg_addr file *)
   Lemma incr_addr_ne_top a z a' :
     (z > 0)%Z → (a + z)%a = Some a' →
     a ≠ addr_reg.top.
   Proof.
     intros Hz Ha.
     rewrite /not. intros Hat.
     rewrite Hat in Ha.
     rewrite /incr_addr in Ha.
     destruct (Z_le_dec (addr_reg.top + z)%Z MemNum); inversion Ha.
     clear Ha H4. 
     rewrite /addr_reg.top /= in l. omega. 
   Qed.

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

   Lemma get_addrs_from_option_addr_comm a i k :
     (k >= 0)%Z -> 
     (get_addr_from_option_addr (get_addr_from_option_addr (a + i) + k)%a) =
     (get_addr_from_option_addr (a + (i + k)%Z)%a).
   Proof.
     intros Hne. 
     destruct (a + i)%a eqn:Hsome; simpl. 
     - f_equal. rewrite /incr_addr in Hsome.
       rewrite /incr_addr.
       destruct (Z_le_dec (a + i)%Z MemNum); inversion Hsome as [Heq]. 
       destruct a0; simpl. inversion Heq as [Ha].
       destruct (Z_le_dec (a + i + k)%Z MemNum); simpl.
       + destruct (Z_le_dec (a + (i + k))%Z MemNum); [simpl |omega].
         f_equal. apply z_of_eq. simpl. omega.
       + by destruct (Z_le_dec (a + (i + k))%Z MemNum); [omega|].
     - rewrite /incr_addr in Hsome.
       destruct (Z_le_dec (a + i)%Z MemNum); inversion Hsome.
       rewrite /incr_addr. 
       destruct (Z_le_dec (addr_reg.top + k)%Z MemNum).
       + assert (k = 0) as ->; [destruct k; simpl in *; lia|].
         destruct (Z_le_dec (a + (i + 0%nat))%Z MemNum); [omega|].
         simpl. apply z_of_eq. simpl. lia.
       + by destruct (Z_le_dec (a + (i + k))%Z MemNum); [omega|].
   Qed. 
     
   Lemma not_elem_of_region_addrs_aux a n (i : Z) :
     (i > 0)%Z →
     a ≠ addr_reg.top →
     a ∉ region_addrs_aux (get_addr_from_option_addr (a + i)%a) n.
   Proof. 
     intros Hi Hne.
     revert i Hi; induction n; intros i Hi.
     - apply not_elem_of_nil.
     - simpl. apply not_elem_of_cons; split.
       + rewrite /incr_addr.
         destruct (Z_le_dec (a + i)%Z MemNum); simpl; auto. 
         destruct a. intros Hcontr. inversion Hcontr. omega.
       + rewrite get_addrs_from_option_addr_comm.
         apply IHn; omega. done. 
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

   (* -------------------- SUPPLEMENTAL LEMMAS ABOUT REGIONS -------------------------- *)
   
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
         
         
End stack_macros. 
