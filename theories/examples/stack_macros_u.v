From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental monotone stack_macros_helpers stack_macros.
From cap_machine Require Export addr_reg_sample region_macros contiguous malloc.
From cap_machine.rules Require Import rules_StoreU_derived rules_LoadU_derived.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  (* -------------------------------- LTACS ------------------------------------------- *)
  Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [| a' a]; inversion Hlen; simpl
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

  (* -------------------------------------- PUSHU ------------------------------------- *)
  Definition pushU_r_instr r_stk r := storeU_z_r r_stk 0 r.

  Definition pushU_r a1 p r_stk r : iProp Σ := (a1 ↦ₐ[p] pushU_r_instr r_stk r)%I.

  Lemma pushU_r_spec a1 a2 w w' r p p' p_a g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) →
    PermFlows p p' ->
    PermFlows URWLX p_a ->
    withinBounds ((URWLX,Local),stk_b,stk_e,stk_a) = true →
    (a1 + 1)%a = Some a2 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ pushU_r a1 p' r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ stk_a ↦ₐ[p_a] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a2) ∗ pushU_r a1 p' r_stk r ∗
            r_stk ↦ᵣ inr ((URWLX,Local),stk_b,stk_e,stk_a') ∗ r ↦ᵣ w' ∗ stk_a ↦ₐ[p_a] w'
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc1 Hfl Hfl' Hwb Hsuc Hstk)
            "(Ha1 & HPC & Hr_stk & Hr & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_storeU_success_0_reg with "[$HPC $Ha1 $Hr $Hr_stk $Hstk_a']");
      [apply decode_encode_instrW_inv|auto|auto|auto |apply Hsuc|auto| |eauto..].
    { rewrite /canStoreU. destruct w'; auto. destruct c,p0,p0,p0,l;auto. }
    iFrame.
    iEpilogue "(HPC & Ha1 & Hr & Hr_stk & Hstk_a)".
    iApply "Hφ". iFrame. 
  Qed.

  Lemma pushU_r_spec_same a1 a2 w p p' p_a g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) →
    PermFlows p p' ->
    PermFlows URWLX p_a ->
    withinBounds ((URWLX,Local),stk_b,stk_e,stk_a) = true →
    (a1 + 1)%a = Some a2 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ pushU_r a1 p' r_stk r_stk
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a ↦ₐ[p_a] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a2) ∗ pushU_r a1 p' r_stk r_stk ∗
            r_stk ↦ᵣ inr ((URWLX,Local),stk_b,stk_e,stk_a') ∗ stk_a ↦ₐ[p_a] inr ((URWLX,Local),stk_b,stk_e,stk_a)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc1 Hfl Hfl' Hwb Hsuc Hstk)
            "(Ha1 & HPC & Hr_stk & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_storeU_success_0_reg_same with "[$HPC $Ha1 $Hr_stk $Hstk_a']");
      [apply decode_encode_instrW_inv|auto|auto|auto|apply Hsuc|auto| |eauto..].
    { rewrite /canStoreU. auto. }
    iEpilogue "(HPC & Ha1 & Hr_stk & Hstk_a)".
    iApply "Hφ". iFrame.
  Qed.

  Definition pushU_z_instr r_stk z := storeU_z_z r_stk 0 z.

  Definition pushU_z a1 p r_stk z : iProp Σ := (a1 ↦ₐ[p] pushU_z_instr r_stk z)%I.

  Lemma pushU_z_spec a1 a2 w z p p' p_a g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) →
    PermFlows p p' ->
    PermFlows URWLX p_a ->
    withinBounds ((URWLX,Local),stk_b,stk_e,stk_a) = true →
    (a1 + 1)%a = Some a2 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ pushU_z a1 p' r_stk z
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a ↦ₐ[p_a] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a2) ∗ pushU_z a1 p' r_stk z ∗
            r_stk ↦ᵣ inr ((URWLX,Local),stk_b,stk_e,stk_a') ∗ stk_a ↦ₐ[p_a] inl z
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc1 Hf Hfl' Hwb Hsuc Hstk)
            "(Ha1 & HPC & Hr_stk & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_storeU_success_0_z with "[$HPC $Ha1 $Hr_stk $Hstk_a']");
      [apply decode_encode_instrW_inv|auto| auto |auto|apply Hsuc|eauto..].
    iEpilogue "(HPC & Ha1 & Hr_stk & Hstk_a)".
    iApply "Hφ". iFrame. 
  Qed.
  

  (* -------------------------------------- POPU -------------------------------------- *)
  Definition popU_instrs r_stk r :=
    [loadU_r_z r r_stk (-1); sub_z_z r_t1 0 1; lea_r r_stk r_t1].
  
  Definition popU (a1 a2 a3 : Addr) (p : Perm) (r_stk r : RegName) : iProp Σ :=
    ([∗ list] a;i ∈ [a1;a2;a3];(popU_instrs r_stk r), a ↦ₐ[p] i)%I.

  Lemma popU_spec a1 a2 a3 a4 r w w' wt1 p p' p_a g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) ∧
    isCorrectPC (inr ((p,g),b,e,a3)) →
    PermFlows p p' ->
    PermFlows URWLX p_a ->
    withinBounds ((URWLX,Local),stk_b,stk_e,stk_a') = true →
    r ≠ PC →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (a3 + 1)%a = Some a4 →
    (stk_a' + 1)%a = Some stk_a →

      ▷ popU a1 a2 a3 p' r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a' ↦ₐ[p_a] w
    ∗ ▷ r_t1 ↦ᵣ wt1
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a4)
            ∗ popU a1 a2 a3 p' r_stk r
            ∗ r ↦ᵣ w
            ∗ stk_a' ↦ₐ[p_a] w
            ∗ r_stk ↦ᵣ inr ((URWLX,Local),stk_b,stk_e,stk_a')
            ∗ r_t1 ↦ᵣ (inl (-1)%Z)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ((Hvpc1 & Hvpc2 & Hvpc3) Hfl Hfl' Hwb Hne Ha1' Ha2' Ha3' Hstk_a')
            "((>Ha1 & >Ha2 & >Ha3 & _) & >HPC & >Hr_stk & >Hstk_a & >Hr_t1 & >Hr & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_loadU_success with "[$HPC $Ha1 $Hr $Hr_stk $Hstk_a]");
      [apply decode_encode_instrW_inv|eauto..].
    iEpilogue "(HPC & Hr & Ha1 & Hr_stk & Hstk_a) /=".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success_z_z with "[$HPC $Ha2 $Hr_t1]"); 
      [apply decode_encode_instrW_inv|eauto..].
    iEpilogue "(HPC & Ha2 & Hr_t1) /=".
    iApply (wp_bind (fill [SeqCtx])).
    assert ((stk_a + (-1)%Z)%a = Some stk_a') as Hlea;
      [revert Hstk_a';clear;solve_addr|]. 
    iApply (wp_lea_success_reg with "[$HPC $Ha3 $Hr_stk $Hr_t1]");
      [apply decode_encode_instrW_inv|eauto..].
    { simpl. solve_addr. }  
    iEpilogue "(HPC & Ha3 & Hr_t1 & Hr_stk) /=".
    iApply "Hφ". iFrame. done.
  Qed.

  (* ------------------------------------- MCLEARU ---------------------------------- *)
  (* the following version of mclear works on a U capability *)

  Definition mclearU_off_end := 9%Z.
  Definition mclearU_off_iter := 2%Z.

  Definition mclearU_instrs r_stk :=
    [ move_r r_t4 r_stk;
      getb r_t1 r_t4;
      geta r_t2 r_t4;
      sub_r_r r_t2 r_t1 r_t2;
      lea_r r_t4 r_t2;
      gete r_t5 r_t4;
      sub_r_z r_t5 r_t5 1; (* we subtract the bound by one so that the lt check becomes a le check *)
      move_r r_t2 PC;
      lea_z r_t2 mclearU_off_end; (* offset to "end" *)
      move_r r_t3 PC;
      lea_z r_t3 mclearU_off_iter; (* offset to "iter" *)
    (* iter: *)
      lt_r_r r_t6 r_t5 r_t1;
      jnz r_t2 r_t6;
      storeU_z_z r_t4 0 0;
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
  Definition mclearU (a : list Addr) (p : Perm) (r : RegName) : iProp Σ :=
    ([∗ list] k↦a_i;w_i ∈ a;(mclearU_instrs r), a_i ↦ₐ[p] w_i)%I.

  Lemma mclearU_iter_spec (a1 a2 a3 a4 a5 b_r e_r a_r (* e_r' *) : Addr) ws (z : nat)
        p p' g b e rt rt1 rt2 rt3 rt4 rt5 a_end (p_r p_r' : Perm) (g_r : Locality) φ :
        isCorrectPC (inr ((p,g),b,e,a1))
      ∧ isCorrectPC (inr ((p,g),b,e,a2))
      ∧ isCorrectPC (inr ((p,g),b,e,a3))
      ∧ isCorrectPC (inr ((p,g),b,e,a4))
      ∧ isCorrectPC (inr ((p,g),b,e,a5)) →
        (a1 + 1)%a = Some a2
      ∧ (a2 + 1)%a = Some a3
      ∧ (a3 + 1)%a = Some a4
      ∧ (a4 + 1)%a = Some a5 →
        ((b_r + z < e_r)%Z → withinBounds ((p_r,g_r),b_r,e_r,a_r) = true) →
        isU p_r = true →
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
     ∗ ▷ ([∗ list] a_i;w_i ∈ [a1;a2;a3;a4;a5];[lt_r_r rt3 rt2 rt1;
                                                  jnz rt4 rt3;
                                                  storeU_z_z rt 0 0;
                                                  add_r_z rt1 rt1 1;
                                                  jmp rt5], a_i ↦ₐ[p'] w_i)
     ∗ ▷ (PC ↦ᵣ updatePcPerm (inr ((p,g),b,e,a_end))
             ∗ [[ a_r , e_r ]] ↦ₐ[p_r'] [[ region_addrs_zeroes a_r e_r ]]
             ∗ (∃ a_r, rt ↦ᵣ inr (p_r, g_r, b_r, e_r, a_r))
             ∗ rt5 ↦ᵣ inr (p, g, b, e, a1)
             ∗ a3 ↦ₐ[p'] storeU_z_z rt 0 0
             ∗ a4 ↦ₐ[p'] add_r_z rt1 rt1 1
             ∗ a5 ↦ₐ[p'] jmp rt5
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
    destruct Hvpc as (Hvpc1 & Hvpc2 & Hvpc3 & Hvpc4 & Hvpc5).
    destruct Hnext as (Hnext1 & Hnext2 & Hnext3 & Hnext4).
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
      with "[Hi HPC Hr_t3 Hr_t1 Hr_t2]"); [apply decode_encode_instrW_inv | | | apply Hfl1 | ..]; eauto.
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
      iApply (wp_jnz_success_next _ rt4 rt3 _ _ _ _ a2 a3 with "[HPC Hi Hr_t3 Hr_t4]");
        first apply decode_encode_instrW_inv; first apply Hfl1;eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      (* storeU rt 0 *)
      rewrite/ withinBounds in Hwb.
      apply andb_prop in Hwb as [Hwb_b%Z.leb_le Hwb_e%Z.ltb_lt].
      2: { lia. } 
      rewrite {1}region_size_S /=.
      2: { solve_addr. }
      destruct ws as [| w1 ws]; simpl; [by iApply bi.False_elim|].
      assert (∃ a_r', (a_r + 1)%a = Some a_r') as [a_r' Ha_r'].
      { apply addr_next_lt with e_r. apply incr_addr_of_z_i in Hprogress. lia. }
      iDestruct "Hbe" as "[Ha_r Hbe]".
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_storeU_success_0_z with "[$HPC $Hi $Hrt $Ha_r]");
        [apply decode_encode_instrW_inv|auto|auto|auto|apply Hnext3|auto..].
      { rewrite /withinBounds andb_true_iff; split;[auto|].
          by apply Z.leb_le. by apply Z.ltb_lt. }
      { apply Ha_r'. }
      iEpilogue "(HPC & Ha3 & Hrt & Ha_r)".
      (* add rt1 rt1 1 *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_add_sub_lt_success_dst_z _ rt1 _ _ _ _ a4 _ _ _ with "[HPC Hi Hr_t1]"); try iFrame;
        [ apply decode_encode_instrW_inv | | | apply Hfl1 | ..]; eauto.
      iEpilogue "(HPC & Ha4 & Hr_t1)".
      (* jmp rt5 *)
      iDestruct "Hprog" as "[Hi _]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jmp_success _ _ _ _ _ a5 with "[HPC Hi Hr_t5]");
        first apply decode_encode_instrW_inv; first apply Hfl1; eauto.
      iFrame. iEpilogue "(HPC & Ha5 & Hr_t5)".
      iApply ("IH" $! a_r' ws (z + 1)%nat with
                  "[Hbe] [HPC] [Hrt] [Hr_t1] [Hr_t2] [Hr_t3] [Hr_t4] [Hr_t5] [Ha1 Ha2 Ha3 Ha4 Ha5] [Hφ Ha_r]")
      ; iFrame. 
      + by rewrite Ha_r'.
      + assert (updatePcPerm (inr (p, g, b, e, a1)) = (inr (p, g, b, e, a1))).
        { rewrite /updatePcPerm. destruct p; auto.
          inversion Hvpc1; destruct H5 as [Hc | [Hc | Hc] ]; inversion Hc. }
        rewrite H. iFrame.
      + cbn. assert (b_r + z + 1 = b_r + (z + 1)%nat)%Z as ->;[lia|]. iFrame.
      + eauto.
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
      iApply (wp_jnz_success_jmp _ rt4 rt3 _ _ _ _ a2 _ _ (inl 1%Z) with "[HPC Hi Hr_t3 Hr_t4]");
        first apply decode_encode_instrW_inv; first apply Hfl1; eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      iApply "Hφ". iDestruct "Hprog" as "(Ha3 & Ha4 & Ha5 & _)".
      rewrite /region_addrs_zeroes region_size_0 //=. iFrame.
      iSplitL "Hrt"; eauto.
  Qed.

  Lemma mclearU_spec (a : list Addr) (r : RegName)
        (a_first a6' a_end : Addr) p p' g b e p_r p_r' g_r (b_r e_r a_r : Addr) a' φ :
    contiguous_between a a_first a' →
    (* We will assume that we are not trying to clear memory in a *)
    isU p_r = true →
    (a !! 7 = Some a6' ∧ (a6' + 9)%a = Some a_end ∧ a !! 16 = Some a_end) →

    isCorrectPC_range p g b e a_first a' →
    PermFlows p p' → PermFlows p_r p_r' ->

    (* We will also assume the region to clear is non empty, and that we have write permission on b_r *)
    (b_r ≤ e_r)%Z → (b_r <= a_r)%Z ->

     (mclearU a p' r
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
            ∗ mclearU a p' r -∗
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hnext HU Hjnz_off Hvpc Hfl1 Hfl2 Hle Hle')
            "(Hmclear & >HPC & >Hr & >Hr_t4 & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t5 & >Hr_t6 & >Hregion & Hφ)".
    iDestruct "Hr_t4" as (w4) "Hr_t4".
    iDestruct "Hr_t1" as (w1) "Hr_t1".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t6" as (w6) "Hr_t6".
    (* destruct Hne as (Hne1 & Hne2 & Hne3 & Hwa). *)
    iDestruct (big_sepL2_length with "Hmclear") as %Hlen. 
    rewrite /mclearU /mclearU_instrs; simpl in Hlen. 
    destruct a as [| a1 a]; inversion Hlen; simpl.
    move: (contiguous_between_cons_inv_first _ _ _ _ Hnext).
    match goal with |- (?a = _) -> _ => intro; subst a end.
    iPrologue "Hmclear".
    iApply (wp_move_success_reg _ _ _ _ _ a_first _ _ r_t4 _ r with "[HPC Hr Hr_t4 Hi]");
      first apply decode_encode_instrW_inv; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 0. }
    iFrame. iEpilogue "(HPC & Ha_first & Hr_t4 & Hr)".
    (* getb r_t1 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t1 r_t4 _ _ _ _ a0 _ _ _ a1 with "[$HPC $Hi $Hr_t1 $Hr_t4]");
      first eapply decode_encode_instrW_inv; first eauto; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 1. }
    iFrame. iEpilogue "(HPC & Ha0 & Hr_t4 & Hr_t1)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha0 Ha_first" as "Hprog_done".
    (* geta r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t2 r_t4 _ _ _ _ a1 _ _ _ a2 with "[HPC Hi Hr_t2 Hr_t4]");
      first eapply decode_encode_instrW_inv; first eauto; first eapply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 2. }
    iFrame. iEpilogue "(HPC & Ha1 & Hr_t4 & Hr_t2)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha1 Hprog_done" as "Hprog_done".
    (* sub r_t2 r_t1 r_t2 *)
    iPrologue "Hprog".
    (* destruct b_r eqn:Hb_r. *)
    iApply (wp_add_sub_lt_success_r_dst _ _ _ _ _ _ a2 _ _ r_t1 with "[HPC Hi Hr_t1 Hr_t2]"); try iFrame;
      [ apply decode_encode_instrW_inv | | | apply Hfl1 | ..]; eauto. 2: by iCorrectPC a_first a'.
    assert ((a2 + 1) = Some a3)%a as ->. { iContiguous_next Hnext 3. } by eauto.
    iEpilogue "(HPC & Ha2 & Hr_t1 & Hr_t2)".
    iCombine "Ha2 Hprog_done" as "Hprog_done".
    (* lea r_t4 r_t2 *)
    iPrologue "Hprog".
    assert (a_r + (b_r - a_r) = b_r)%Z as Haddmin; first lia.
    assert ((a_r + (b_r - a_r))%a = Some b_r) as Ha_rb_r by solve_addr.
    iApply (wp_lea_success_reg _ _ _ _ _ a3 a4 _ r_t4 r_t2 p_r _ _ _ a_r (b_r - a_r) with "[HPC Hi Hr_t4 Hr_t2]");
      first apply decode_encode_instrW_inv; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 4. }
    { destruct p_r; inversion HU; auto. }
    { destruct p_r; auto. }
      by iFrame. iEpilogue "(HPC & Ha3 & Hr_t2 & Hr_t4)".
    iCombine "Ha3 Hprog_done" as "Hprog_done".
    (* gete r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t5 r_t4 _ _ _ _ a4 _ _ _ a5 with "[HPC Hi Hr_t5 Hr_t4]"); try iFrame;
      first apply decode_encode_instrW_inv; first eauto; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 5. }
    do 2 iFrame.
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t4 r_t5) as [Hcontr | _]; [inversion Hcontr|].
    iEpilogue "(HPC & Ha4 & Hr_t4 & Hr_t5)".
    iCombine "Ha4 Hprog_done" as "Hprog_done".
    (* sub r_t5 r_t5 1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi Hr_t5]");
      [apply decode_encode_instrW_inv| | | apply Hfl1|iCorrectPC a_first a'|..]; eauto.
    assert ((a5 + 1)%a = Some a6) as ->. { iContiguous_next Hnext 6. } eauto.
    iEpilogue "(HPC & Ha5 & Hr_t5)".
    iCombine "Ha5 Hprog_done" as "Hprog_done".
    (* move r_t2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a6 a7 _ r_t2 with "[HPC Hi Hr_t2]");
      first apply decode_encode_instrW_inv; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 7. }
    iFrame. iEpilogue "(HPC & Ha6 & Hr_t2)".
    iCombine "Ha6 Hprog_done" as "Hprog_done".
    (* lea r_t2 mclearU_off_end *)
    iPrologue "Hprog".
    assert (p ≠ E) as Hpne.
    { have: (isCorrectPC (inr (p, g, b, e, a_first))).
      { apply Hvpc. eapply contiguous_between_middle_bounds'; eauto. constructor. }
      inversion 1; subst.
      destruct H15 as [? | [? | ?] ]; subst; auto. }
    iApply (wp_lea_success_z _ _ _ _ _ a7 a8 _ r_t2 p _ _ _ a6 9 a_end with "[HPC Hi Hr_t2]");
      first apply decode_encode_instrW_inv; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 8. }
    { destruct Hjnz_off as (Ha7' & HmclearU_off_end & Ha_end). simpl in Ha7'. congruence. }
    { have: (isCorrectPC (inr (p, g, b, e, a_first))).
      { apply Hvpc. eapply contiguous_between_middle_bounds'; eauto. constructor. }
      inversion 1; subst.
      destruct H15 as [? | [? | ?] ]; subst; auto.
    }
    iFrame. iEpilogue "(HPC & Ha7 & Hr_t2)".
    iCombine "Ha7 Hprog_done" as "Hprog_done".
    (* move r_t3 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a8 a9 _ r_t3 with "[HPC Hi Hr_t3]");
      first apply decode_encode_instrW_inv; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 9. }
    iFrame. iEpilogue "(HPC & Ha8 & Hr_t3)".
    iCombine "Ha8 Hprog_done" as "Hprog_done".
    (* lea r_t3 mclearU_off_iter *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ a9 a10 _ r_t3 p _ _ _ a8 2 a10 with "[HPC Hi Hr_t3]");
      first apply decode_encode_instrW_inv; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 10. }
    { assert (2 = 1 + 1)%Z as ->; auto.
      apply incr_addr_trans with a9. iContiguous_next Hnext 9.
      iContiguous_next Hnext 10. }
    { have: (isCorrectPC (inr (p, g, b, e, a_first))).
      { apply Hvpc. eapply contiguous_between_middle_bounds'; eauto. constructor. }
      inversion 1; subst.
      destruct H17 as [? | [? | ?] ]; subst; auto. }
    iFrame. iEpilogue "(HPC & Ha9 & Hr_t3)".
    iCombine "Ha9 Hprog_done" as "Hprog_done".
    (* iter *)
    clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    do 5 iPrologue_pre. clear H0 H1 H2 H3.
    iDestruct "Hprog" as "[Hi1 Hprog]".
    iDestruct "Hprog" as "[Hi2 Hprog]".
    iDestruct "Hprog" as "[Hi3 Hprog]".
    iDestruct "Hprog" as "[Hi4 Hprog]".
    iDestruct "Hprog" as "[Hi5 Hprog]".
    iDestruct "Hregion" as (ws) "Hregion".
    iApply (mclearU_iter_spec a10 a11 a12 a13 a14 b_r e_r b_r _
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
      iIntros "(HPC & Hbe & Hr_t4 & Hr_t3 & Ha12 & Ha13 & Ha14 &
      Ha10 & Hr_t5 & Hr_t1 & Ha11 & Hr_t2 & Hr_t6)".
      iCombine "Ha10 Ha11 Ha12 Ha13 Ha14 Hprog_done" as "Hprog_done".
      iDestruct "Hr_t4" as (a_r0) "Hr_t4".
      iDestruct "Hr_t1" as (z0) "Hr_t1".
      iPrologue "Hprog".
      assert (a15 = a_end)%a as Ha16.
      { simpl in Hjnz_off.
        destruct Hjnz_off as (Ha15 & Ha15' & Hend).
        by inversion Hend.
      }
      destruct a as [| a17 a]; inversion Hlen.
      iApply (wp_move_success_z with "[$Hr_t4 HPC $Hi]");
        first apply decode_encode_instrW_inv; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 16; auto. }
      { rewrite Ha16. destruct p; iFrame. contradiction. }
      iEpilogue "(HPC & Ha16 & Hr_t4)".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a16 a17 _ r_t1 _ 0 with "[HPC Hi Hr_t1]");
        first apply decode_encode_instrW_inv; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 17. }
      iFrame. iEpilogue "(HPC & Ha17 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a17 a18 _ r_t2 _ 0 with "[HPC Hi Hr_t2]");
        first apply decode_encode_instrW_inv; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 18. }
      iFrame. iEpilogue "(HPC & Ha18 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a18 a19 _ r_t3 _ 0 with "[HPC Hi Hr_t3]");
        first apply decode_encode_instrW_inv; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 19. }
      iFrame. iEpilogue "(HPC & Ha19 & Hr_t3)".
      (* move r_t5 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a19 a20 _ r_t5 _ 0 with "[HPC Hi Hr_t5]");
        first apply decode_encode_instrW_inv; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 20. }
      iFrame. iEpilogue "(HPC & Ha20 & Hr_t5)".
      (* move r_t6 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a20 a' _ r_t6 _ 0 with "[HPC Hi Hr_t6]");
        first apply decode_encode_instrW_inv; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { eapply contiguous_between_last. eapply Hnext. reflexivity. }
      iFrame. iEpilogue "(HPC & Ha21 & Hr_t6)".
      iApply "Hφ".
      iDestruct "Hprog_done" as "(Ha_iter & Ha10 & Ha12 & Ha11 & Ha13 & Ha14 & Ha15 & Ha8 & Ha7
      & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha1 & Ha0)".
      iFrame. 
  Qed.


  (* -------------------------------------- PREPSTACKU ---------------------------------- *)
  (* The following macro first checks whether r is a capability with permission URWLX. Next
     if it is, it will move the pointer to the bottom of its range *)

  (* TODO: move this to the rules_Lea.v file. small issue with the spec of failure: it does not actually 
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)
  Lemma wp_Lea_fail_U Ep pc_p pc_g pc_b pc_e pc_a w r1 rv p g b e a z a' pc_p' :
    decodeInstrW w = Lea r1 (inr rv) →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (a + z)%a = Some a' ->
     (match p with
      | URW | URWL | URWX | URWLX => (a < a')%a
      | _ => False 
      end) ->
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
     {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hfl Hvpc Hz Hp φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. destruct p0; try done; revert Hp H5;clear;solve_addr. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Definition prepstackU_instrs r (minsize: Z) :=
    reqperm_instrs r (encodePerm URWLX) ++
    reqsize_instrs r minsize ++
    [getb r_t1 r;
    geta r_t2 r;
    sub_r_r r_t1 r_t1 r_t2;
    lea_r r r_t1;
    move_z r_t1 0;
    move_z r_t2 0].

  Definition prepstackU r minsize a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(prepstackU_instrs r minsize), a_i ↦ₐ[p] w_i)%I.

  Lemma prepstackU_spec r minsize a w pc_p pc_p' pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->
    contiguous_between a a_first a_last ->

      ▷ prepstackU r minsize a pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (if isPermWord w URWLX then
           ∃ l b e a', ⌜w = inr (URWLX,l,b,e,a')⌝ ∧
           if (minsize <? e - b)%Z then
             if (b <=? a')%Z then 
               (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ prepstackU r minsize a pc_p' ∗
                   r ↦ᵣ inr (URWLX,l,b,e,b) ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z
                   -∗ WP Seq (Instr Executable) {{ φ }})
             else φ FailedV
           else φ FailedV
         else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    (* reqperm *)
    iDestruct (contiguous_between_program_split with "Hprog") as (reqperm_prog rest link)
                                                                   "(Hreqperm & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_reqperm & Hcont_rest & Heqapp & Hlink).
    iApply (reqperm_spec with "[$HPC $Hreqperm $Hr $Hr_t1 $Hr_t2 Hφ Hprog]"); [|apply Hfl|apply Hcont_reqperm|]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. solve_addr. }
    iNext. destruct (isPermWord w URWLX); auto.
    iDestruct "Hφ" as (l b e a' Heq) "Hφ".
    subst. iExists l,b,e,a'. iSplit; auto.
    iIntros "(HPC & Hprog_done & Hr & Hr_t1 & Hr_t2)".
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. solve_addr. }
    (* reqsize *)
    iDestruct (contiguous_between_program_split with "Hprog")
      as (reqsize_prog rest' link') "(Hreqsize & Hprog & #Hcont)";[apply Hcont_rest|].
    iDestruct "Hcont" as %(Hcont_reqsize & Hcont_rest' & Heqapp' & Hlink').
    iApply (reqsize_spec with "[- $HPC $Hreqsize $Hr $Hr_t1 $Hr_t2]");
      [|apply Hfl|eauto|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest'. solve_addr. }
    iNext. destruct (minsize <? e - b)%Z; auto.
    iIntros "H". iDestruct "H" as (w1 w2) "(Hreqsize & HPC & Hr & Hr_t1 & Hr_t2)".
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link' a_last) as Hvpc_rest'.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. solve_addr. }
    (* getb r_t1 r *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength'.
    do 2 (destruct rest';[inversion Hlength'|]). 
    iPrologue "Hprog".
    apply contiguous_between_cons_inv_first in Hcont_rest' as Heq; subst.
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* geta r_t2 r *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t2]");
      [apply decode_encode_instrW_inv|auto|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 1|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* sub r_t1 r_t1 r_t2 *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont_rest' 2|apply Hfl|iCorrectPC link' a_last|..].
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* we need to distinguish between the case where the capability is stuck, or usable *)
    assert ((a' + (b - a'))%a = Some b) as Hlea;[solve_addr|].
    destruct (decide (b <= a')%a).
    2: { (* lea fail *)
      destruct rest';[inversion Hlength'|].
      iPrologue "Hprog".
      iApply (wp_Lea_fail_U with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link' a_last|apply Hlea|..].
      { simpl. solve_addr. }
      iEpilogue "_ /=". assert (b <=? a' = false)%Z as ->;[apply Z.leb_gt;solve_addr|].
      iApply wp_value. iApply "Hφ". }
    (* lea r r_t1 *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 3|apply Hlea|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* move r_t1 0 *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]"); 
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 4|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* move r_t2 0 *)
    destruct rest';[|inversion Hlength'].
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=a3) in Hcont_rest' as Hlast;[|auto].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]"); 
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link' a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    assert (b <=? a' = true)%Z as ->;[apply Zle_is_le_bool;auto|].
    iApply "Hφ". iFrame.
    repeat (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi"). 
    iFrame "Hprog_done". 
  Qed.


End stack_macros. 
