From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental monotone. 
From cap_machine Require Export contiguous region_macros.

Section stack_macros.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  (* ---------------------------- Helper Lemmas --------------------------------------- *)
  (* TODO: move to lang *)
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

  Lemma isWithinBounds_bounds_alt p g b e (a0 a1 a2 : Addr) :
    withinBounds (p,g,b,e,a0) = true ->
    withinBounds (p,g,b,e,a2) = true ->
    (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z ->
    withinBounds (p,g,b,e,a1) = true.
  Proof.
    intros Hwb0 Hwb2 [Hle0 Hle2].
    rewrite /withinBounds.
    apply andb_true_iff.
    apply andb_true_iff in Hwb0 as [Hleb0 Hlea0].
    apply andb_true_iff in Hwb2 as [Hleb2 Hlea2].  
    split; rewrite /leb_addr; apply Z.leb_le.
    - apply Z.leb_le in Hleb0. apply Z.leb_le in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.leb_le in Hlea2. lia.
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
    ([∗ list] a;i ∈ [a1;a2];(push_r_instrs r_stk r), a ↦ₐ[p] i)%I. 
  
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
    ([∗ list] a;i ∈ [a1;a2];(push_z_instrs r_stk z), a ↦ₐ[p] i)%I.
  
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
      eauto; first apply lea_z_i;iFrame.
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
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,an)) →
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
      apply isCorrectPC_bounds_alt with a1 an; auto. 
  Qed. 
  
  (* -------------------------------------- MCLEAR ----------------------------------- *)
   (* the following macro clears the region of memory a capability govers over. a denotes
     the list of adresses containing the instructions for the clear. |a| = 23 *)

  (* first we will define the list of Words making up the mclear macro *)
  Definition mclear_instrs r_stk off_end off_iter :=
    [ move_r r_t4 r_stk;
      getb r_t1 r_t4; 
      geta r_t2 r_t4; 
      sub_r_r r_t2 r_t1 r_t2; 
      lea_r r_t4 r_t2;
      gete r_t5 r_t4;
      sub_r_z r_t5 r_t5 1; (* we subtract the bound by one so that the lt check becomes a le check *)
      move_r r_t2 PC;
      lea_z r_t2 off_end; (* offset to "end" *)
      move_r r_t3 PC;
      lea_z r_t3 off_iter; (* offset to "iter" *)
    (* iter: *)
      lt_r_r r_t6 r_t5 r_t1;
      store_z r_t4 0; 
      jnz r_t2 r_t6;
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

  (* Next we define mclear in memory, using a list of addresses of size 23 *)
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
             
  Lemma mclear_iter_spec (a1 a2 a3 a4 a5 a6 b_r e_r a_r (* e_r' *) : Addr) ws (z : nat)
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
        withinBounds ((p_r,g_r),b_r,e_r,a_r) = true → (* This should now always hold! since we are jumping once a_r and e_r are equal *)
        writeAllowed p_r = true →
        (* (e_r + 1)%a = Some e_r' → *)
        (b_r + z)%a = Some a_r →
        PermFlows p p' ->
        PermFlows p_r p_r' -> 
 
      ([[a_r,e_r]] ↦ₐ[p_r'] [[ws]]
     ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
     ∗ ▷ rt ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
     ∗ ▷ rt1 ↦ᵣ inl (b_r + z)%Z
     ∗ ▷ rt2 ↦ᵣ inl ((z_of e_r) - 1)%Z
     ∗ ▷ (∃ w, rt3 ↦ᵣ w)
     ∗ ▷ rt4 ↦ᵣ inr (p, g, b, e, a_end)
     ∗ ▷ rt5 ↦ᵣ inr (p, g, b, e, a1)
     ∗ ▷ ([∗ list] a_i;w_i ∈ [a1;a2;a3;a4;a5;a6];[lt_r_r rt3 rt2 rt1;
                                                  store_z rt 0;
                                                  jnz rt4 rt3;
                                                  lea_z rt 1;
                                                  add_r_z rt1 rt1 1;
                                                  jmp rt5], a_i ↦ₐ[p'] w_i)
     ∗ ▷ (PC ↦ᵣ updatePcPerm (inr ((p,g),b,e,a_end))
             ∗ [[ a_r , e_r ]] ↦ₐ[p_r'] [[ region_addrs_zeroes a_r e_r ]]
             ∗ (∃ a_r, rt ↦ᵣ inr (p_r, g_r, b_r, e_r, a_r))
             ∗ rt5 ↦ᵣ inr (p, g, b, e, a1)
             ∗ a2 ↦ₐ[p'] store_z rt 0
             ∗ a4 ↦ₐ[p'] lea_z rt 1
             ∗ a5 ↦ₐ[p'] add_r_z rt1 rt1 1
             ∗ a6 ↦ₐ[p'] jmp rt5
             ∗ a1 ↦ₐ[p'] lt_r_r rt3 rt2 rt1
             ∗ rt2 ↦ᵣ inl ((z_of e_r) - 1)%Z
             ∗ (∃ z, rt1 ↦ᵣ inl (b_r + z)%Z)
             ∗ a3 ↦ₐ[p'] jnz rt4 rt3
             ∗ rt4 ↦ᵣ inr (p, g, b, e, a_end)
             ∗ rt3 ↦ᵣ inl 1%Z
              -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hnext Hwb Hwa (* Her' *) Hprogress Hfl1 Hfl2)
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
    destruct (Z_le_dec (b_r + z) (e_r - 1))%Z; simpl. 
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 0%Z) as Heq0.
      { rewrite /Z.b2z. assert (e_r - 1 <? b_r + z = false)%Z as Heq; [apply Z.ltb_nlt; omega|].
          by rewrite Heq. }
      rewrite Heq0. 
      (* store rt 0 *)
      rewrite/ withinBounds in Hwb.
      apply andb_prop in Hwb as [Hwb_b Hwb_e]. 
      apply (Z.leb_le a_r e_r) in Hwb_e. 
      destruct (Z_le_dec a_r e_r); try contradiction.
      destruct ws as [_ | w1 ws]; [simpl; by iApply bi.False_elim|simpl]. 
      iDestruct "Hbe" as "[Ha_r Hbe]".
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_store_success_z _ _ _ _ _ a2 a3 _ rt 0 _ p_r g_r b_r e_r a_r with "[HPC Hi Hrt Ha_r]"); first apply store_z_i; first apply Hfl1; eauto.
      { split;[auto|]. rewrite /withinBounds andb_true_iff; split;[auto|]. by apply Z.leb_le. }
      iFrame. iEpilogue "(HPC & Ha2 & Hrt & Ha_r)".
      (* jnz rt4 rt3 *)
      iDestruct "Hprog" as "[Hi Hprog]". 
      iApply (wp_bind (fill [SeqCtx])). 
      iApply (wp_jnz_success_next _ rt4 rt3 _ _ _ _ a3 a4 with "[HPC Hi Hr_t3]");
        first apply jnz_i; first apply Hfl1;eauto. 
      iFrame. iEpilogue "(HPC & Ha3 & Hr_t3)". 
      (* lea rt 1 *)
      assert (∃ a_r', (a_r + 1)%a = Some a_r') as [a_r' Ha_r'].
      { apply addr_next_lt with e_r. apply incr_addr_of_z_i in Hprogress. lia. }
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
      iApply ("IH" $! a_r' ws (z + 1)%nat with
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
      + assert (b_r + z + 1 = b_r + (z + 1)%nat)%Z as ->;[lia|]. iFrame.
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
        apply andb_true_intro.
        apply Z.leb_le in Hwb_b. 
        split; apply Z.leb_le.
        * apply Z.le_trans with a_r; auto.
          rewrite /incr_addr in Ha_r'.
          destruct (Z_le_dec (a_r + 1)%Z MemNum); inversion Ha_r'; simpl; omega.  
        * assert ((z_of b_r) + z = z_of a_r)%Z as Heq_brz.
          { rewrite /incr_addr in Hprogress.
              by destruct (Z_le_dec (b_r + z)%Z MemNum); inversion Hprogress. }
          assert ((z_of a_r) + 1 = z_of a_r')%Z as Ha_rz.
          { rewrite /incr_addr in Ha_r'.
              by destruct (Z_le_dec (a_r + 1)%Z MemNum); inversion Ha_r'. }
          lia. 
      + iPureIntro.
        rewrite -Ha_r'.
        rewrite PeanoNat.Nat.add_1_r Nat2Z.inj_succ -Z.add_1_r. 
        by rewrite (addr_add_assoc _ a_r). 
    - assert (Z.b2z (e_r -1 <? b_r + z)%Z = 1%Z) as Heq0.
      { rewrite /Z.b2z. assert (e_r - 1 <? b_r + z = true)%Z as Heq; [apply Z.ltb_lt; omega|].
          by rewrite Heq. }
      rewrite Heq0.
      assert (a_r >= e_r)%Z.
      { assert ((z_of b_r) + z = a_r)%Z; 
          first (rewrite /incr_addr in Hprogress;
                   by destruct (Z_le_dec (b_r + z)%Z MemNum); inversion Hprogress).
        rewrite -H3. lia. 
      }
      destruct (Z_le_dec a_r e_r).
      + assert (z_of a_r = z_of e_r) as Heq;[lia|].
        apply z_of_eq in Heq. subst. rewrite Z.sub_diag /=.
        destruct ws;[by iApply bi.False_elim|]. 
        iSimpl in "Hbe". iDestruct "Hbe" as "[He_r _]".
        iDestruct "Hprog" as "[Hi Hprog]". 
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_store_success_z _ _ _ _ _ a2 a3 _ rt 0 _ p_r g_r b_r e_r e_r with "[HPC Hi Hrt He_r]"); first apply store_z_i; first apply Hfl1; eauto.
        iFrame. iEpilogue "(HPC & Ha2 & Hrt & Ha_r)".
        (* jnz *)
        iDestruct "Hprog" as "[Hi Hprog]". 
        iApply (wp_bind (fill [SeqCtx])). 
        iApply (wp_jnz_success_jmp _ rt4 rt3 _ _ _ _ a3 _ _ (inl 1%Z) with "[HPC Hi Hr_t3 Hr_t4]"); first apply jnz_i; first apply Hfl1; eauto. 
        iFrame. iEpilogue "(HPC & Ha3 & Hr_t4 & Hr_t3)". 
        iApply "Hφ". iDestruct "Hprog" as "(Ha4 & Ha5 & Ha6 & _)". iFrame. 
        rewrite /region_addrs_zeroes /= Z.sub_diag /=.
        destruct (Z_le_dec e_r e_r);[|contradiction]. 
        iFrame. iSplitR;[auto|].
        iSplitL "Hrt". iExists (e_r). iFrame. iExists z. iFrame.
      + (* This should lead to a contradiction from within bounds *)
        exfalso. 
        rewrite /withinBounds in Hwb.
        apply andb_true_iff in Hwb as [Hwb1 Hwb2].
        apply Z.leb_le in Hwb2. done. 
        Unshelve. apply w1. 
  Qed. 

    
  Lemma mclear_spec (a : list Addr) (r : RegName) 
        (a_last a_first a6' a_end : Addr) p p' g b e p_r p_r' g_r (b_r e_r a_r : Addr) a' φ :
    contiguous a →
    a !! 0 = Some a_first → list.last a = Some a_last →
    (* We will assume that we are not trying to clear memory in a *)
    r ≠ PC ∧ writeAllowed p_r = true →
    (a !! 7 = Some a6' ∧ (a6' + 10)%a = Some a_end ∧ a !! 17 = Some a_end) →
    
    isCorrectPC (inr ((p,g),b,e,a_first)) → isCorrectPC (inr ((p,g),b,e,a_last)) →
    PermFlows p p' → PermFlows p_r p_r' -> 
    
    (a_last + 1)%a = Some a' →
    (* We will also assume the region to clear is non empty *)
    (b_r ≤ e_r)%Z →

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
    iIntros (Hnext Ha_first Ha_last [Hne Hwa] Hjnz_off Hvpc1 Hvpc2 Hfl1 Hfl2 Ha_last' Hle)
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
    (* sub r_t5 r_t5 1 *)
    iPrologue "Hprog".
    assert (a_first < a5)%Z as Hlt5; first middle_lt a4 5.
    iApply (wp_add_sub_lt_success with "[$HPC $Hi Hr_t5]");
      [right;left;apply sub_r_z_i|apply Hfl1|iCorrectPC 6|auto..].
    destruct (reg_eq_dec r_t5 PC) eqn:Hcontr;[by inversion Hcontr|clear Hcontr].
    assert ((a5 + 1)%a = Some a6) as ->;[apply Hnext with 6; auto|].
    destruct (reg_eq_dec r_t5 r_t5) eqn:Hcontr;[clear Hcontr|by inversion Hcontr].
    rewrite sub_r_z_i.
    iEpilogue "(HPC & Ha5 & _ & _ & Hr_t5)".
    iCombine "Ha5 Hprog_done" as "Hprog_done". 
    (* move r_t2 PC *)
    iPrologue "Hprog".
    assert (a_first < a6)%Z as Hlt6; first middle_lt a5 6.
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a6 a7 _ r_t2 with "[HPC Hi Hr_t2]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC 7; eauto. 
    { apply Hnext with 7; auto. }
    iFrame. iEpilogue "(HPC & Ha6 & Hr_t2)".
    iCombine "Ha6 Hprog_done" as "Hprog_done". 
    (* lea r_t2 off_end *)
    iPrologue "Hprog".
    assert (a_first < a7)%Z as Hlt7; first middle_lt a6 7.
    assert (p ≠ E) as Hpne.
    { inversion Hvpc1; destruct H19 as [? | [? | ?] ]; subst; auto. }
    iApply (wp_lea_success_z _ _ _ _ _ a7 a8 _ r_t2 p _ _ _ a6 10 a_end with "[HPC Hi Hr_t2]");
      first apply lea_z_i; first apply Hfl1; first iCorrectPC 8; auto.
    { apply Hnext with 8; auto. }
    { destruct Hjnz_off as (Ha7' & Hoff_end & Ha_end). simpl in Ha7'. congruence. }
    iFrame. iEpilogue "(HPC & Ha7 & Hr_t2)".
    iCombine "Ha7 Hprog_done" as "Hprog_done". 
    (* move r_t3 PC *)
    iPrologue "Hprog".
    assert (a_first < a8)%Z as Hlt8; first middle_lt a7 8.
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a8 a9 _ r_t3 with "[HPC Hi Hr_t3]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC 9; auto.
    { apply Hnext with 9; auto. }
    iFrame. iEpilogue "(HPC & Ha8 & Hr_t3)".
    iCombine "Ha8 Hprog_done" as "Hprog_done". 
    (* lea r_t3 off_iter *)
    iPrologue "Hprog".
    assert (a_first < a9)%Z as Hlt9; first middle_lt a8 9.
    iApply (wp_lea_success_z _ _ _ _ _ a9 a10 _ r_t3 p _ _ _ a8 2 a10 with "[HPC Hi Hr_t3]");
      first apply lea_z_i; first apply Hfl1; first iCorrectPC 10; auto.
    { apply Hnext with 10; auto. }
    { assert (2 = 1 + 1)%Z as ->; auto. 
      apply incr_addr_trans with a9. 
      apply Hnext with 9; auto. apply Hnext with 10; auto. }
    iFrame. iEpilogue "(HPC & Ha9 & Hr_t3)".
    iCombine "Ha9 Hprog_done" as "Hprog_done".
    (* iter *)
    clear H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 Hlt0 Hlt1 Hlt2 Hlt3 Hlt4 Hlt5 Hlt6 Hlt7 Hlt8.
    do 5 iPrologue_pre. clear H4 H5 H6 H7.
    iDestruct "Hprog" as "[Hi1 Hprog]".
    iDestruct "Hprog" as "[Hi2 Hprog]".
    iDestruct "Hprog" as "[Hi3 Hprog]".
    iDestruct "Hprog" as "[Hi4 Hprog]".
    iDestruct "Hprog" as "[Hi5 Hprog]".
    iDestruct "Hprog" as "[Hi6 Hprog]".
    iDestruct "Hregion" as (ws) "Hregion".
    assert (a_first < a10)%Z as Hlt10;first middle_lt a9 10.
    assert (a_first < a11)%Z as Hlt11; first middle_lt a10 11.
    assert (a_first < a12)%Z as Hlt12; first middle_lt a11 12.
    assert (a_first < a13)%Z as Hlt13; first middle_lt a12 13.
    assert (a_first < a14)%Z as Hlt14; first middle_lt a13 14.
    assert (a_first < a15)%Z as Hlt15; first middle_lt a14 15.
    iApply (mclear_iter_spec a10 a11 a12 a13 a14 a15 b_r e_r b_r _
                        0 p p' g b e r_t4 r_t1 r_t5 r_t6 r_t2 r_t3 _ p_r p_r' g_r
              with "[-]"); auto.
    - split; [|(split; [|(split; [|(split; [|split])])])]; [iCorrectPC 11|iCorrectPC 12|iCorrectPC 13|iCorrectPC 14|iCorrectPC 15|iCorrectPC 16].
    - repeat split;[apply Hnext with 11; auto|apply Hnext with 12; auto|
                    apply Hnext with 13; auto|apply Hnext with 14; auto|apply Hnext with 15; auto].
    - (* rewrite Z.add_0_r. intros Hle. *)
      rewrite /withinBounds.
      apply andb_true_intro.
      split; apply Z.leb_le; [lia|congruence].
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
      iPrologue "Hprog".
      assert (a16 = a_end)%a as Ha16.
      { simpl in Hjnz_off. 
        destruct Hjnz_off as (Ha16 & Ha16' & Hend).
        by inversion Hend. 
      } 
      destruct a as [_ | a17 a]; inversion Hlen. 
      assert (a_first < a16)%Z as Hlt16; first middle_lt a15 16. 
      iApply (wp_move_success_z _ _ _ _ _ a16 a17 _ r_t4 _ 0 with "[HPC Hi Hr_t4]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 17; auto. 
      { apply Hnext with 17; auto. }
      { rewrite Ha16. destruct p; iFrame. contradiction. }
      iEpilogue "(HPC & Ha16 & Hr_t4)".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      assert (a_first < a17)%Z as Hlt17; first middle_lt a16 17. 
      iApply (wp_move_success_z _ _ _ _ _ a17 a18 _ r_t1 _ 0 with "[HPC Hi Hr_t1]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 18; auto.
      { apply Hnext with 18; auto. }
      iFrame. iEpilogue "(HPC & Ha17 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      assert (a_first < a18)%Z as Hlt18; first middle_lt a17 18. 
      iApply (wp_move_success_z _ _ _ _ _ a18 a19 _ r_t2 _ 0 with "[HPC Hi Hr_t2]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 19; auto.
      { apply Hnext with 19; auto. }
      iFrame. iEpilogue "(HPC & Ha18 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      assert (a_first < a19)%Z as Hlt19; first middle_lt a18 19. 
      iApply (wp_move_success_z _ _ _ _ _ a19 a20 _ r_t3 _ 0 with "[HPC Hi Hr_t3]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 20; auto.
      { apply Hnext with 20; auto. }
      iFrame. iEpilogue "(HPC & Ha19 & Hr_t3)".
      (* move r_t5 0 *)
      iPrologue "Hprog".
      assert (a_first < a20)%Z as Hlt20; first middle_lt a19 20. 
      iApply (wp_move_success_z _ _ _ _ _ a20 a21 _ r_t5 _ 0 with "[HPC Hi Hr_t5]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 21; auto.
      { apply Hnext with 21; auto. }
      iFrame. iEpilogue "(HPC & Ha20 & Hr_t5)".
      (* move r_t6 0 *)
      iPrologue "Hprog".
      assert (a_first < a21)%Z as Hlt21; first middle_lt a20 21. 
      iApply (wp_move_success_z _ _ _ _ _ a21 a' _ r_t6 _ 0 with "[HPC Hi Hr_t6]");
        first apply move_z_i; first apply Hfl1; first iCorrectPC 22; auto.
      { inversion Ha_last. auto. }
      iFrame. iEpilogue "(HPC & Ha21 & Hr_t6)".
      iApply "Hφ".
      iDestruct "Hprog_done" as "(Ha_iter & Ha10 & Ha12 & Ha11 & Ha13 & Ha14 & Ha15 & Ha8 & Ha7
      & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha1 & Ha0 & Ha_first)".
      iFrame. Unshelve. exact 0. exact 0. apply w1. apply w1. 
  Qed.        (* ??? *)
            
         
End stack_macros. 
