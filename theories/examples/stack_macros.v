From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental monotone.
From cap_machine Require Export addr_reg_sample region_macros contiguous.

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
    split; rewrite /leb_addr /ltb_addr; first [ apply Z.leb_le | apply Z.ltb_lt ].
    - apply Z.leb_le in Hleb0. apply Z.ltb_lt in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.ltb_lt in Hlea2. lia.
  Qed.

  Lemma isWithinBounds_bounds_alt' p g b e (a0 a1 a2 : Addr) :
    withinBounds (p,g,b,e,a0) = true ->
    withinBounds (p,g,b,e,a2) = true ->
    (a0 ≤ a1)%Z ∧ (a1 < a2)%Z ->
    withinBounds (p,g,b,e,a1) = true.
  Proof.
    intros Hwb0 Hwb2 [Hle0 Hle2].
    rewrite /withinBounds.
    apply andb_true_iff.
    apply andb_true_iff in Hwb0 as [Hleb0 Hlea0].
    apply andb_true_iff in Hwb2 as [Hleb2 Hlea2].
    split; rewrite /leb_addr /ltb_addr; first [ apply Z.leb_le | apply Z.ltb_lt ].
    - apply Z.leb_le in Hleb0. apply Z.ltb_lt in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.ltb_lt in Hlea2. lia.
  Qed.

  Definition isCorrectPC_range p g b e a0 an :=
    ∀ ai, (a0 <= ai)%a ∧ (ai < an)%a → isCorrectPC (inr (p, g, b, e, ai)).

  Lemma isCorrectPC_inrange p g b (e a0 an a: Addr) :
    isCorrectPC_range p g b e a0 an →
    (a0 <= a < an)%Z →
    isCorrectPC (inr (p, g, b, e, a)).
  Proof.
    unfold isCorrectPC_range. move=> /(_ a) HH ?. apply HH. eauto.
  Qed.

  Lemma isCorrectPC_contiguous_range p g b e a0 an a l :
    isCorrectPC_range p g b e a0 an →
    contiguous_between l a0 an →
    a ∈ l →
    isCorrectPC (inr (p, g, b, e, a)).
  Proof.
    intros Hr Hc Hin.
    eapply isCorrectPC_inrange; eauto.
    eapply contiguous_between_middle_bounds'; eauto.
  Qed.

  Lemma isCorrectPC_range_perm p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p = RX ∨ p = RWX ∨ p = RWLX.
  Proof.
    intros Hr H0n.
    assert (isCorrectPC (inr (p, g, b, e, a0))) as HH by (apply Hr; solve_addr).
    inversion HH; auto.
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

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

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
    ([∗ list] a;i ∈ [a1;a2;a3];(pop_instrs r_stk r), a ↦ₐ[p] i)%I.

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
    ∗ ▷ stk_a ↦ₐ[RWLX] w
    ∗ ▷ r_t1 ↦ᵣ wt1
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a4)
            ∗ pop a1 a2 a3 p' r_stk r
            ∗ r ↦ᵣ w
            ∗ stk_a ↦ₐ[RWLX] w
            ∗ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a')
            ∗ r_t1 ↦ᵣ (inl (-1)%Z)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ((Hvpc1 & Hvpc2 & Hvpc3) Hfl Hwb Hne Ha1' Ha2' Ha3' Hstk_a')
            "((>Ha1 & >Ha2 & >Ha3 & _) & >HPC & >Hr_stk & >Hstk_a & >Hr_t1 & >Hr & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iAssert (⌜(stk_a =? a1)%a = false⌝)%I as %Hne'.
    { rewrite Z.eqb_neq. iIntros (Hcontr); apply z_of_eq in Hcontr; subst.
      iApply (cap_duplicate_false with "[$Ha1 $Hstk_a]").
      split; auto. destruct p'; auto. destruct p; inversion Hfl. 
      inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
    iApply (wp_load_success _ _ _ _ _ _ _ a1 _ _ _ RWLX
              with "[HPC Ha1 Hr_stk Hr Hstk_a]"); eauto; first apply load_r_i;
      first apply PermFlows_refl;iFrame. rewrite Hne'. iFrame. 
    iNext. iIntros "(HPC & Hr & Ha1 & Hr_stk & Hstk_a) /=".
    iApply wp_pure_step_later; auto; iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success_z_z _ r_t1 _ _ _ _ a2 with "[HPC Ha2 Hr_t1]");
      first apply sub_z_z_i; eauto; iFrame; simpl.
    iNext.
    (* rewrite sub_z_z_i Ha2'. *)
    iIntros "(HPC & Ha2 & Hr_t1) /=".
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

  Lemma rclear_spec (a : list Addr) (r : list RegName) p p' g b e a1 an φ :
    contiguous_between a a1 an →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC_range p g b e a1 an →
    PermFlows p p' →

      ▷ (∃ ws, ([∗ list] k↦r_i;w_i ∈ r;ws, r_i ↦ᵣ w_i))
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ rclear a p' r
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,an) ∗ ([∗ list] k↦r_i ∈ r, r_i ↦ᵣ inl 0%Z)
            ∗ rclear a p' r -∗
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Ha Hne Hhd Hvpc Hfl) "(>Hreg & >HPC & >Hrclear & Hφ)".
    iDestruct (big_sepL2_length with "Hrclear") as %Har.
    iRevert (Hne Har Hhd Hvpc Ha).
    iInduction (a) as [_ | a1'] "IH" forall (r a1 an). iIntros (Hne Har Hhd Hvpc Ha).
    by inversion Hhd; simplify_eq.
    iDestruct "Hreg" as (ws) "Hreg".
    iIntros (Hne Har Hhd Hvpc Ha).
    iApply (wp_bind (fill [SeqCtx])). rewrite /rclear /=.
    (* rewrite -(beq_nat_refl (length r)).  *)destruct r; inversion Har.
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    iDestruct (big_sepL2_length with "Hreg") as %rws.
    destruct ws; inversion rws.
    iDestruct (big_sepL2_cons with "Hreg") as "[Hr Hreg]".
    destruct a.
    - inversion H4; symmetry in H6; apply (nil_length_inv) in H6.
      inversion Hhd. subst.
      iApply (wp_move_success_z _ _ _ _ _ a1 with "[HPC Ha1 Hr]");
        eauto;first apply move_z_i; first iCorrectPC a1 an.
      { eapply contiguous_between_last; eauto. }
      { apply (not_elem_of_cons) in Hne as [Hne _]. apply Hne. }
      iFrame. iNext. iIntros "(HPC & Han & Hr) /=".
      iApply wp_pure_step_later; auto; iNext.
      iApply "Hφ". iFrame. destruct r0; inversion H6. done.
    - destruct r0; inversion H4. inversion Hhd; subst.
      iApply (wp_move_success_z _ _ _ _ _ a1 a _ r with "[HPC Ha1 Hr]")
      ; eauto; first apply move_z_i; first iCorrectPC a1 an.
      { iContiguous_next Ha 0. }
      { by apply not_elem_of_cons in Hne as [Hne _]. }
      iFrame. iNext. iIntros "(HPC & Ha1 & Hr) /=".
      iApply wp_pure_step_later; auto. iNext.
      rewrite -/(map _ _) -/(rclear_instrs _).
      iApply ("IH" with "[Hreg] [HPC] [Hrclear] [Hφ Ha1 Hr]"); iFrame.
      + iExists (ws). iFrame.
      + simpl. rewrite H6. iFrame.
      + simpl. rewrite H6.
        iNext. iIntros "(HPC & Hreg & Hrclear)".
        iApply "Hφ". iFrame.
      + iPureIntro. by apply not_elem_of_cons in Hne as [_ Hne].
      + iPureIntro. simpl. congruence.
      + auto.
      + iPureIntro.
        intros a' [? Ha'].
        assert (a1 <= a')%a as Hlow.
        { enough (a1 <= a)%a by solve_addr.
          eapply contiguous_between_middle_bounds'; eauto. repeat constructor. }
        by specialize (Hvpc a' (conj Hlow Ha')).
      + iPureIntro. inversion Ha; subst.
        assert (a = a') as ->. eapply contiguous_between_cons_inv_first; eauto.
        auto.
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

  (* Next we define mclear in memory, using a list of addresses of size 23 *)
  Definition mclear (a : list Addr) (p : Perm) (r : RegName) (off_end off_iter : Z) : iProp Σ :=
    if ((length a) =? (length (mclear_instrs r off_end off_iter)))%nat then
      ([∗ list] k↦a_i;w_i ∈ a;(mclear_instrs r off_end off_iter), a_i ↦ₐ[p] w_i)%I
    else
      False%I.

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
        ((b_r + z < e_r)%Z → withinBounds ((p_r,g_r),b_r,e_r,a_r) = true) →
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
             ∗ rt2 ↦ᵣ inl ((z_of e_r) - 1)%Z
             ∗ (∃ z, rt1 ↦ᵣ inl (b_r + z)%Z)
             ∗ a2 ↦ₐ[p'] jnz rt4 rt3
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
    iApply (wp_add_sub_lt_success_r_r _ rt3 _ _ _ _ a1 _ _ _ rt2 _ rt1 _ _
      with "[Hi HPC Hr_t3 Hr_t1 Hr_t2]"); [apply lt_i | | | apply Hfl1 | ..]; eauto.
    iFrame.
    iEpilogue "(HPC & Ha1 & Hr_t2 & Hr_t1 & Hr_t3)".
    rewrite /region_mapsto /region_addrs.
    destruct (Z_le_dec (b_r + z) (e_r - 1))%Z; simpl.
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 0%Z) as Heq0.
      { rewrite /Z.b2z. destruct (e_r - 1 <? b_r + z)%Z eqn:HH; auto.
        apply Z.ltb_lt in HH. lia. }
      rewrite Heq0.
      (* jnz rt4 rt3 *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jnz_success_next _ rt4 rt3 _ _ _ _ a2 a3 with "[HPC Hi Hr_t3]");
        first apply jnz_i; first apply Hfl1;eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t3)".
      (* store rt 0 *)
      rewrite/ withinBounds in Hwb.
      apply andb_prop in Hwb as [Hwb_b%Z.leb_le Hwb_e%Z.ltb_lt].
      rewrite {1}region_size_S /=.
      destruct ws as [| w1 ws]; simpl; [by iApply bi.False_elim|].
      iDestruct "Hbe" as "[Ha_r Hbe]".
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_store_success_z _ _ _ _ _ a3 a4 _ rt 0 _ p_r g_r b_r e_r a_r with "[HPC Hi Hrt Ha_r]"); first apply store_z_i; first apply Hfl1; eauto.
      { split;[auto|]. rewrite /withinBounds andb_true_iff; split;[auto|].
          by apply Z.leb_le. by apply Z.ltb_lt. }
      iFrame. iEpilogue "(HPC & Ha3 & Hrt & Ha_r)".
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
      iApply (wp_add_sub_lt_success_dst_z _ rt1 _ _ _ _ a5 _ _ _ with "[HPC Hi Hr_t1]");
        [ apply add_r_z_i | | | apply Hfl1 | ..]; eauto.
      iFrame. iEpilogue "(HPC & Ha5 & Hr_t1)".
      (* jmp rt5 *)
      iDestruct "Hprog" as "[Hi _]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jmp_success _ _ _ _ _ a6 with "[HPC Hi Hr_t5]");
        first apply jmp_i; first apply Hfl1; eauto.
      iFrame. iEpilogue "(HPC & Ha6 & Hr_t5)".
      iApply ("IH" $! a_r' ws (z + 1)%nat with
                  "[Hbe] [HPC] [Hrt] [Hr_t1] [Hr_t2] [Hr_t3] [Hr_t4] [Hr_t5] [Ha1 Ha2 Ha3 Ha4 Ha5 Ha6] [Hφ Ha_r]")
      ; iFrame. all: auto.
      + by rewrite Ha_r'.
      + assert (updatePcPerm (inr (p, g, b, e, a1)) = (inr (p, g, b, e, a1))).
        { rewrite /updatePcPerm. destruct p; auto.
          inversion Hvpc1; destruct H9 as [Hc | [Hc | Hc] ]; inversion Hc. }
        rewrite H3. iFrame.
      + cbn. assert (b_r + z + 1 = b_r + (z + 1)%nat)%Z as ->;[lia|]. iFrame.
      + iNext.
        iIntros "(HPC & Hregion & Hrt & Hrt5 & Ha3 & Ha4 & Ha5 & Ha6 & Ha1 & Hrt2 & Hrt1 & Ha2 & Hrt4 & Hrt3)".
        iApply "Hφ".
        iFrame.
        rewrite /region_addrs_zeroes.
        rewrite (region_size_S a_r e_r) //= (_: (^(a_r+1))%a = a_r'); [| solve_addr].
        iFrame.
      + iPureIntro. intro.
        rewrite andb_true_iff -Zle_is_le_bool -Zlt_is_lt_bool. solve_addr.
      + iPureIntro. solve_addr.
      + solve_addr.
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 1%Z) as Heq0.
      { rewrite /Z.b2z. destruct (e_r - 1 <? b_r + z)%Z eqn:HH; auto.
        apply Z.ltb_nlt in HH. lia. }
      rewrite Heq0.
      assert (e_r <= a_r)%Z by solve_addr.
      (* destruct (Z_le_dec a_r e_r). *)
      rewrite region_size_0 //=.
      destruct ws;[|by iApply bi.False_elim].
      (* jnz *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jnz_success_jmp _ rt4 rt3 _ _ _ _ a2 _ _ (inl 1%Z) with "[HPC Hi Hr_t3 Hr_t4]"); first apply jnz_i; first apply Hfl1; eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      iApply "Hφ". iDestruct "Hprog" as "(Ha3 & Ha4 & Ha5 & Ha6 & _)".
      rewrite /region_addrs_zeroes region_size_0 //=. iFrame.
      iSplitL "Hrt"; eauto.
  Qed.


  Lemma mclear_spec (a : list Addr) (r : RegName)
        (a_first a6' a_end : Addr) p p' g b e p_r p_r' g_r (b_r e_r a_r : Addr) a' φ :
    contiguous_between a a_first a' →
    (* We will assume that we are not trying to clear memory in a *)
    r ≠ PC ∧ writeAllowed p_r = true →
    (a !! 7 = Some a6' ∧ (a6' + 10)%a = Some a_end ∧ a !! 17 = Some a_end) →

    isCorrectPC_range p g b e a_first a' →
    PermFlows p p' → PermFlows p_r p_r' ->

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
    iIntros (Hnext [Hne Hwa] Hjnz_off Hvpc Hfl1 Hfl2 Hle)
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
    destruct a as [_ | a1 a]; inversion Hlen; simpl.
    move: (contiguous_between_cons_inv_first _ _ _ _ Hnext).
    match goal with |- (?a = _) -> _ => intro; subst a end.
    iPrologue "Hmclear".
    iApply (wp_move_success_reg _ _ _ _ _ a_first _ _ r_t4 _ r with "[HPC Hr Hr_t4 Hi]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 0. }
    iFrame. iEpilogue "(HPC & Ha_first & Hr_t4 & Hr)".
    (* getb r_t1 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t1 r_t4 _ _ _ _ a0 _ _ _ a1 with "[$HPC $Hi $Hr_t1 $Hr_t4]");
      first eapply getb_i; first eauto; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 1. }
    iFrame. iEpilogue "(HPC & Ha0 & Hr_t4 & Hr_t1)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha0 Ha_first" as "Hprog_done".
    (* geta r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t2 r_t4 _ _ _ _ a1 _ _ _ a2 with "[HPC Hi Hr_t2 Hr_t4]");
      first eapply geta_i; first eauto; first eapply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 2. }
    iFrame. iEpilogue "(HPC & Ha1 & Hr_t4 & Hr_t2)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha1 Hprog_done" as "Hprog_done".
    (* sub r_t2 r_t1 r_t2 *)
    iPrologue "Hprog".
    (* destruct b_r eqn:Hb_r. *)
    iApply (wp_add_sub_lt_success_r_dst _ _ _ _ _ _ a2 _ _ r_t1 with "[HPC Hi Hr_t1 Hr_t2]");
      [ apply sub_r_r_i | | | apply Hfl1 | ..]; eauto. 2: by iCorrectPC a_first a'. 
    assert ((a2 + 1) = Some a3)%a as ->. { iContiguous_next Hnext 3. } by eauto. by iFrame.
    iEpilogue "(HPC & Ha2 & Hr_t1 & Hr_t2)".
    iCombine "Ha2 Hprog_done" as "Hprog_done".
    (* lea r_t4 r_t2 *)
    iPrologue "Hprog".
    assert (a_r + (b_r - a_r) = b_r)%Z as Haddmin; first lia.
    assert ((a_r + (b_r - a_r))%a = Some b_r) as Ha_rb_r by solve_addr.
    iApply (wp_lea_success_reg _ _ _ _ _ a3 a4 _ r_t4 r_t2 p_r _ _ _ a_r (b_r - a_r) with "[HPC Hi Hr_t4 Hr_t2]");
      first apply lea_r_i; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 4. }
    { destruct p_r; inversion Hwa; auto. }
    by iFrame. iEpilogue "(HPC & Ha3 & Hr_t2 & Hr_t4)".
    iCombine "Ha3 Hprog_done" as "Hprog_done".
    (* gete r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t5 r_t4 _ _ _ _ a4 _ _ _ a5 with "[HPC Hi Hr_t5 Hr_t4]");
      first apply gete_i; first eauto; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 5. }
    do 2 iFrame.
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t4 r_t5) as [Hcontr | _]; [inversion Hcontr|].
    iEpilogue "(HPC & Ha4 & Hr_t4 & Hr_t5)".
    iCombine "Ha4 Hprog_done" as "Hprog_done".
    (* sub r_t5 r_t5 1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi Hr_t5]");
      [apply sub_r_z_i| | | apply Hfl1|iCorrectPC a_first a'|..]; eauto.
    assert ((a5 + 1)%a = Some a6) as ->. { iContiguous_next Hnext 6. } eauto.
    iEpilogue "(HPC & Ha5 & Hr_t5)".
    iCombine "Ha5 Hprog_done" as "Hprog_done".
    (* move r_t2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a6 a7 _ r_t2 with "[HPC Hi Hr_t2]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 7. }
    iFrame. iEpilogue "(HPC & Ha6 & Hr_t2)".
    iCombine "Ha6 Hprog_done" as "Hprog_done".
    (* lea r_t2 off_end *)
    iPrologue "Hprog".
    assert (p ≠ E) as Hpne.
    { have: (isCorrectPC (inr (p, g, b, e, a_first))).
      { apply Hvpc. eapply contiguous_between_middle_bounds'; eauto. constructor. }
      inversion 1; subst.
      destruct H19 as [? | [? | ?] ]; subst; auto. }
    iApply (wp_lea_success_z _ _ _ _ _ a7 a8 _ r_t2 p _ _ _ a6 10 a_end with "[HPC Hi Hr_t2]");
      first apply lea_z_i; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 8. }
    { destruct Hjnz_off as (Ha7' & Hoff_end & Ha_end). simpl in Ha7'. congruence. }
    iFrame. iEpilogue "(HPC & Ha7 & Hr_t2)".
    iCombine "Ha7 Hprog_done" as "Hprog_done".
    (* move r_t3 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a8 a9 _ r_t3 with "[HPC Hi Hr_t3]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 9. }
    iFrame. iEpilogue "(HPC & Ha8 & Hr_t3)".
    iCombine "Ha8 Hprog_done" as "Hprog_done".
    (* lea r_t3 off_iter *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ a9 a10 _ r_t3 p _ _ _ a8 2 a10 with "[HPC Hi Hr_t3]");
      first apply lea_z_i; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 10. }
    { assert (2 = 1 + 1)%Z as ->; auto.
      apply incr_addr_trans with a9. iContiguous_next Hnext 9.
      iContiguous_next Hnext 10. }
    iFrame. iEpilogue "(HPC & Ha9 & Hr_t3)".
    iCombine "Ha9 Hprog_done" as "Hprog_done".
    (* iter *)
    clear H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
    do 5 iPrologue_pre. clear H4 H5 H6 H7.
    iDestruct "Hprog" as "[Hi1 Hprog]".
    iDestruct "Hprog" as "[Hi2 Hprog]".
    iDestruct "Hprog" as "[Hi3 Hprog]".
    iDestruct "Hprog" as "[Hi4 Hprog]".
    iDestruct "Hprog" as "[Hi5 Hprog]".
    iDestruct "Hprog" as "[Hi6 Hprog]".
    iDestruct "Hregion" as (ws) "Hregion".
    iApply (mclear_iter_spec a10 a11 a12 a13 a14 a15 b_r e_r b_r _
                        0 p p' g b e r_t4 r_t1 r_t5 r_t6 r_t2 r_t3 _ p_r p_r' g_r
              with "[-]"); auto.
    - repeat apply conj; iCorrectPC a_first a'.
    - repeat split; solve [
        iContiguous_next Hnext 11; auto
      | iContiguous_next Hnext 12; auto
      | iContiguous_next Hnext 13; auto
      | iContiguous_next Hnext 14; auto
      | iContiguous_next Hnext 15; auto ].
    - (* rewrite Z.add_0_r. intros Hle. *)
      rewrite /withinBounds. intro.
      rewrite andb_true_iff Z.leb_le Z.ltb_lt. lia.
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
      iDestruct "Hr_t1" as (z0) "Hr_t1".
      iPrologue "Hprog".
      assert (a16 = a_end)%a as Ha16.
      { simpl in Hjnz_off.
        destruct Hjnz_off as (Ha16 & Ha16' & Hend).
        by inversion Hend.
      }
      destruct a as [_ | a17 a]; inversion Hlen.
      iApply (wp_move_success_z _ _ _ _ _ a16 a17 _ r_t4 _ 0 with "[HPC Hi Hr_t4]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 17; auto. }
      { rewrite Ha16. destruct p; iFrame. contradiction. }
      iEpilogue "(HPC & Ha16 & Hr_t4)".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a17 a18 _ r_t1 _ 0 with "[HPC Hi Hr_t1]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 18. }
      iFrame. iEpilogue "(HPC & Ha17 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a18 a19 _ r_t2 _ 0 with "[HPC Hi Hr_t2]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 19. }
      iFrame. iEpilogue "(HPC & Ha18 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a19 a20 _ r_t3 _ 0 with "[HPC Hi Hr_t3]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 20. }
      iFrame. iEpilogue "(HPC & Ha19 & Hr_t3)".
      (* move r_t5 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a20 a21 _ r_t5 _ 0 with "[HPC Hi Hr_t5]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 21. }
      iFrame. iEpilogue "(HPC & Ha20 & Hr_t5)".
      (* move r_t6 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a21 a' _ r_t6 _ 0 with "[HPC Hi Hr_t6]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { eapply contiguous_between_last. eapply Hnext. reflexivity. }
      iFrame. iEpilogue "(HPC & Ha21 & Hr_t6)".
      iApply "Hφ".
      iDestruct "Hprog_done" as "(Ha_iter & Ha10 & Ha12 & Ha11 & Ha13 & Ha14 & Ha15 & Ha8 & Ha7
      & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha1 & Ha0 & Ha_first)".
      iFrame. Unshelve. exact 0. exact 0.
  Qed.        (* ??? *)

End stack_macros.
