From cap_machine.ftlr Require Export Jmp Jnz Mov Load Store AddSubLt
  Lea Restrict Subseg Get Seal UnSeal.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine Require Import rules proofmode register_tactics.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma extract_r_ex r (reg : RegName) :
    (∃ w, r !! reg = Some w) →
    ⊢ (([∗ map] r0↦w ∈ r, r0 ↦ᵣ w) → ∃ w, reg ↦ᵣ w)%I.
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w.
    iApply (big_sepM_lookup (λ reg' i, reg' ↦ᵣ i)%I r reg w); eauto.
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    ⊢ (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
     (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap".
    iDestruct (big_sepM_lookup_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto.
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Lemma fundamental_cap r p b e a :
    ⊢ interp (WCap p b e a) →
      interp_expression r (WCap p b e a).
  Proof.
    iIntros "#Hinv_pc /=".
    iIntros (widc) "#Hinv_idc".
    iIntros "[[Hfull Hreg] [Hmreg Hown]]".
    iRevert "Hinv_idc"; iRevert "Hinv_pc".
    iLöb as "IH" forall (r p b e a widc).
    iIntros "#Hinv_pc #Hinv_idc".
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    destruct (decide (isCorrectPC (WCap p b e a))).
    - (* Correct PC *)
      iApply (wp_bind (fill [SeqCtx])).
      assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto. solve_addr. }
      assert (p = RX ∨ p = RWX) as Hp.
      { inversion i. subst. auto. }
      iDestruct (read_allowed_inv_regs with "[] Hinv_pc Hinv_idc") as (P) "(#Hinva & #Hread)";[eauto|destruct Hp as [-> | ->];auto|iFrame "% #"|].
      rewrite /interp_ref_inv /=.
      iInv (logN.@a) as (w) "[>Ha HP]" "Hcls".
      rewrite {2}/registers_mapsto.
      iExtractList "Hmreg" [PC;idc] as ["HPC";"Hidc"].
      destruct (decodeInstrW w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (jmp_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Jnz *)
        iApply (jnz_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Mov *)
        iApply (mov_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Load *)
        iApply (load_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Store *)
        iApply (store_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Lt *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Add *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Sub *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Lea *)
        iApply (lea_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Restrict *)
        iApply (restrict_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Subseg *)
        iApply (subseg_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* GetB *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetB _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* GetE *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetE _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* GetA *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetA _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* GetP *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetP _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* GetWType *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetWType _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* GetOType *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetOType _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* Seal *)
        iApply (seal_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.
      + (* UnSeal *)
        iApply (unseal_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hidc] [Hmreg]");
          try iAssumption; eauto.

      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
        iNext ; iIntros "_".
        iApply wp_value.
        iIntros (Hcontr); inversion Hcontr.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iApply wp_value.
        iInsertList "Hmreg" [PC;idc].
        iIntros (_).
        iExists (<[idc:=widc]> (<[PC:=WCap p b e a]> r)). iFrame.
        iAssert (∀ r0 : RegName, ⌜is_Some ((<[idc:=widc]> (<[PC:=WCap p b e a]> r) !! r0))⌝)%I as "HA".
        { iIntros.
          destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert_ne //= lookup_insert //=.
          - destruct (reg_eq_dec idc r0).
            + subst r0; rewrite lookup_insert //=.
            + rewrite lookup_insert_ne //= lookup_insert_ne //=.
        }
        iFrame "HA".
   - (* Not correct PC *)
      rewrite {2}/registers_mapsto.
      iExtractList "Hmreg" [PC] as ["HPC"].
      iApply interp_expr_invalid_pc; try iFrame; auto.
      iPureIntro; apply regmap_full_dom in H; rewrite -H; set_solver.
  Qed.

  Theorem fundamental w r :
    ⊢ interp w -∗ interp_expression r w.
  Proof.
    iIntros "Hw". destruct w as [| [c | ] | ].
    2: { iApply fundamental_cap. done. }
    all: iClear "Hw"; iIntros (w') "? ([Hfull ?] & Hreg & ?)".
    all: iDestruct "Hfull" as "%".
    all: iApply (wp_wand with "[-]"); [ | iIntros (?) "H"; iApply "H"].
    all: unfold registers_mapsto;iExtract "Hreg" PC as "HPC".
    all: iApply interp_expr_invalid_pc; try iFrame ; [intros Hcontra ; inversion Hcontra |].
    all: iPureIntro; apply regmap_full_dom in H; rewrite -H; set_solver.
  Qed.

  (* The fundamental theorem implies the exec_cond *)

  Definition exec_cond b e p : iProp Σ :=
    (∀ a r, ⌜a ∈ₐ [[ b , e ]]⌝ → ▷ □ interp_expression r (WCap p b e a))%I.

  Lemma interp_exec_cond p b e a :
    p ≠ IE -> p ≠ E -> interp (WCap p b e a) -∗ exec_cond b e p.
  Proof.
    iIntros (Hnp Hnp') "#Hw".
    iIntros (a0 r Hin). iNext. iModIntro.
    iApply fundamental.
    rewrite !fixpoint_interp1_eq /=.
    destruct p; try done.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)

  Lemma exec_wp p b e a :
    isCorrectPC (WCap p b e a) ->
    exec_cond b e p -∗
    ∀ r, ▷ □ (interp_expr interp r) (WCap p b e a).
  Proof.
    iIntros (Hvpc) "#Hexec".
    rewrite /exec_cond.
    iIntros (r).
    assert (a ∈ₐ[[b,e]])%I as Hin.
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    iSpecialize ("Hexec" $! a r Hin). iFrame "#".
  Qed.

  (* updatePcPerm adds a later because of the case of E-capabilities, which
     unfold to ▷ interp_expr *)
  Lemma interp_updatePcPerm w :
    ⊢ interp w -∗ ▷ (∀ r, interp_expression r (updatePcPerm w)).
  Proof.
    iIntros "#Hw".
    assert ((∃ b e a, w = WCap E b e a) ∨ updatePcPerm w = w) as [Hw | ->].
    { destruct w as [ | [ | ] | ]; eauto. unfold updatePcPerm.
      case_match; eauto. }
    { destruct Hw as [b [e [a ->] ] ]. rewrite fixpoint_interp1_eq. cbn -[all_registers_s].
      iNext. iIntros (rmap). iSpecialize ("Hw" $! rmap). iDestruct "Hw" as "#Hw".
      iIntros (w') "#Hinv ([HPC ?] & Hr & ?)". iApply "Hw"; iFrame ; iFrame "#". }
    { iNext. iIntros (rmap). iApply fundamental. eauto. }
  Qed.

  (* Jmp to an unknown word: need specific resources in case the target is an IE-cap *)
  Definition continuation_resources (cont wpc widc : Word) : iProp Σ :=
    match cont with
    | WCap IE b_cont e_cont a_cont =>
        a_cont ↦ₐ wpc ∗ (a_cont ^+ 1)%a ↦ₐ widc
    | _ => emp
    end.

  Definition updatePcCont (cont wpc : Word) :=
    match cont with
    | WCap IE _ _ _ => wpc
    | _ => updatePcPerm cont
    end.

  Definition updateIdcCont (cont widc widc' : Word) :=
    match cont with
    | WCap IE _ _ _ => widc'
    | _ => widc
    end.

  Lemma updatePcCont_cap_non_IE p b e a w :
    p ≠ IE →
    updatePcCont (WCap p b e a) w = updatePcPerm (WCap p b e a).
  Proof.
    intros HnE. cbn. destruct p; auto. contradiction.
  Qed.

  Lemma updateIdcCont_cap_non_IE p b e a w w' :
    p ≠ IE →
    updateIdcCont (WCap p b e a) w w' = w.
  Proof.
    intros HnE. cbn. destruct p; auto. contradiction.
  Qed.

  Lemma continuation_resources_cap_non_IE p b e a w w' :
    p ≠ IE →
    continuation_resources (WCap p b e a) w w' = emp%I.
  Proof.
    intros HnE. cbn. destruct p; auto. contradiction.
  Qed.

  Lemma wp_jmp_general pc_p pc_b pc_e pc_a w cont r w' wpc widc φ :
    decodeInstrW w = Jmp r →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    ( PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ idc ↦ᵣ w'
        ∗ r ↦ᵣ cont
        ∗ continuation_resources cont wpc widc
        ∗ pc_a ↦ₐ w
        ∗ ▷ (
          PC ↦ᵣ updatePcCont cont wpc
            ∗ idc ↦ᵣ updateIdcCont cont w' widc
            ∗ r ↦ᵣ cont
            ∗ continuation_resources cont wpc widc
            ∗ pc_a ↦ₐ w
          -∗ WP Seq (Instr Executable) {{ φ }}))
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.

  Proof.
    iIntros (Hinstr Hvpc)
      "(HPC & Hidc & Hr & Hcont_res & Hpc_a & Hφ)".

    destruct (decide (is_ie_cap cont = true)) as [Hcont|Hcont].
    { (* case is IE *)
      destruct_word cont ; cbn in Hcont ; try congruence.
      destruct c ; try congruence; clear Hcont.
      rewrite /continuation_resources.
      iDestruct "Hcont_res" as "[Hf1 Hf2]".

      destruct (decide (withinBounds f f0 f1 /\ withinBounds f f0 (f1^+1)%a))
        as [ [Hwb Hwb'] | Hwb ].

      { (* case in bounds *)
        wp_instr.
        iApply (@wp_jmp_success_IE with "[-Hφ]")
        ; [| | eapply Hwb | eapply Hwb' | | ]; eauto; iFrame.
        iNext; iIntros "(HPC & Hidc & Hpc_a & Hf1 & Hf2)"; wp_pure.
        iApply (wp_wand _ _ _ φ with "[-]"); last auto.
        iApply "Hφ"; iFrame.
      }
      { (* case not in bounds *)
        wp_instr.
        iApply (@wp_jmp_fail_IE with "[-Hφ]")
        ; [| | eapply Hwb | | ]; eauto; iFrame.
        iNext; iIntros "(HPC & Hidc & Hpc_a & Hf1 & Hf2)"; wp_pure.
        wp_end ; by iRight.
      }
    }
    { (* case is not IE *)
      assert (is_ie_cap cont = false) as Hcont'.
      { destruct_word cont ; [| destruct c | |] ; cbn in * ; congruence. }
      wp_instr.
      iApply (@wp_jmp_success with "[-Hφ Hidc]") ; eauto; iFrame.
      iNext; iIntros "(HPC & Hr & Hpc_a)"; wp_pure.
      iApply (wp_wand _ _ _ φ with "[-]"); last auto.
      iApply "Hφ".
      destruct_word cont ; [| destruct c | |] ; cbn in Hcont ; try congruence ; iFrame.
    }
  Qed.

  Lemma wp_jmp_general_idc pc_p pc_b pc_e pc_a w cont wpc widc φ :
    decodeInstrW w = Jmp idc →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    ( PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ idc ↦ᵣ cont
        ∗ continuation_resources cont wpc widc
        ∗ pc_a ↦ₐ w
        ∗ ▷ (
          PC ↦ᵣ updatePcCont cont wpc
            ∗ idc ↦ᵣ updateIdcCont cont cont widc
            ∗ continuation_resources cont wpc widc
            ∗ pc_a ↦ₐ w
          -∗ WP Seq (Instr Executable) {{ φ }}))
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.

  Proof.
    iIntros (Hinstr Hvpc)
      "(HPC & Hidc & Hcont_res & Hpc_a & Hφ)".

    destruct (decide (is_ie_cap cont = true)) as [Hcont|Hcont].
    { (* case is IE *)
      destruct_word cont ; cbn in Hcont ; try congruence.
      destruct c ; try congruence; clear Hcont.
      rewrite /continuation_resources.
      iDestruct "Hcont_res" as "[Hf1 Hf2]".

      destruct (decide (withinBounds f f0 f1 /\ withinBounds f f0 (f1^+1)%a))
        as [ [Hwb Hwb'] | Hwb ].

      { (* case in bounds *)
        wp_instr.
        iApply (@wp_jmp_success_IE_same_idc with "[-Hφ]")
        ; [| | eapply Hwb | eapply Hwb' | | ]; eauto; iFrame.
        iNext; iIntros "(HPC & Hidc & Hpc_a & Hf1 & Hf2)"; wp_pure.
        iApply (wp_wand _ _ _ φ with "[-]"); last auto.
        iApply "Hφ"; iFrame.
      }
      { (* case not in bounds *)
        wp_instr.
        iApply (@wp_jmp_fail_IE_same_idc with "[-Hφ]")
        ; [| | eapply Hwb | | ]; eauto; iFrame.
        iNext; iIntros "(HPC & Hidc & Hpc_a & Hf1 & Hf2)"; wp_pure.
        wp_end ; by iRight.
      }
    }
    { (* case is not IE *)
      assert (is_ie_cap cont = false) as Hcont'.
      { destruct_word cont ; [| destruct c | |] ; cbn in * ; congruence. }
      wp_instr.
      iApply (@wp_jmp_success with "[-Hφ]") ; eauto; iFrame.
      iNext; iIntros "(HPC & Hidc & Hpc_a)"; wp_pure.
      iApply (wp_wand _ _ _ φ with "[-]"); last auto.
      iApply "Hφ".
      destruct_word cont ; [| destruct c | |] ; cbn in Hcont ; try congruence; iFrame.
    }
  Qed.

  (* Jmp to unknown code is always safe *)
  Lemma jmp_to_unknown w :
    ⊢ interp w
    -∗ ▷ (∀ rmap,
          ⌜dom rmap = all_registers_s ∖ {[ PC ]}⌝ →
            PC ↦ᵣ updatePcPerm w
              ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
              ∗ na_own logrel_nais ⊤
            -∗ WP Seq (Instr Executable)
               {{ λ v, ⌜v = HaltedV⌝ →
                       ∃ r : Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }}).
  Proof.
    iIntros "#Hw". iDestruct (interp_updatePcPerm with "Hw") as "Hw'". iNext.
    iIntros (rmap Hrmap).
    set rmap' := <[ idc := (WInt 0%Z: Word) ]> (<[ PC := (WInt 0%Z: Word) ]> rmap) : gmap RegName Word.
    iSpecialize ("Hw'" $! rmap').
    iIntros "(HPC & Hr & Hna)". unfold interp_expression, interp_expr, interp_conf.
    assert (exists w', rmap !! idc = Some w') as [w' Hw'] by (apply elem_of_dom; set_solver).
    iDestruct (big_sepM_sep with "Hr") as "(Hr & #HrV)".
    iAssert (interp w') as "Hvalid_w'".
    { replace rmap with (<[idc:=w']> rmap) by (by eapply insert_id).
     by iDestruct (big_sepM_delete _ _ idc with "HrV") as "[Hvalid _]"; first by simplify_map_eq.
    }
    iApply "Hw'". iClear "Hw'". iFrame "Hvalid_w'". rewrite /registers_mapsto.
    iSplitL "HrV"; [iSplit| iFrame].
    { unfold full_map. iIntros (r).
      subst rmap'.
      destruct (decide (r = PC)). { subst r. rewrite lookup_insert_ne //= lookup_insert //. }
      destruct (decide (r = idc)). { subst r. rewrite lookup_insert //. }
      rewrite lookup_insert_ne //=. rewrite lookup_insert_ne //=.
      iPureIntro. rewrite -elem_of_dom Hrmap. set_solver. }
    { iIntros (ri v Hri Hri' Hvs).
      rewrite lookup_insert_ne // in Hvs.
      rewrite lookup_insert_ne // in Hvs.
      iDestruct (big_sepM_lookup _ _ ri with "HrV") as "?"; eauto. }
    subst rmap'.
    rewrite (insert_commute _ PC) //= !insert_insert.
    rewrite (insert_commute _ idc _ w') //=.
    iInsert "Hr" PC.
    replace (<[idc:=w']> rmap) with rmap by (symmetry; by eapply insert_id).
    iFrame.
  Qed.

  Lemma jmp_to_unknown' w w' wpc widc:
    ⊢ interp w
    -∗ interp w'
    -∗ ienter_cond wpc widc interp
    -∗ ▷ (∀ rmap,
          ⌜dom rmap = all_registers_s ∖ {[ PC ; idc ]}⌝ →
            PC ↦ᵣ updatePcCont w wpc
              ∗ idc ↦ᵣ updateIdcCont w w' widc
              ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
              ∗ na_own logrel_nais ⊤
            -∗ WP Seq (Instr Executable)
               {{ λ v, ⌜v = HaltedV⌝ →
                       ∃ r : Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }}).
  Proof.
    iIntros "#Hw #Hwidc #Hcont_ie".
    iDestruct (interp_updatePcPerm with "Hw") as "Hw'".
    iNext; iIntros (rmap Hrmap).
    destruct (decide (is_ie_cap w = true)) as [Hcont | Hcont].
    { (* case IE*)
      iClear "Hw'".
      destruct_word w ; [| destruct c | | ]; cbn in Hcont ; try congruence
      ; clear Hcont.
      rewrite fixpoint_interp1_eq //=.
      set rmap' := <[ idc := widc ]> (<[ PC := wpc ]> rmap) : gmap RegName Word.
      iIntros "(HPC & HIDC & Hmap & Hna)".
      iApply ("Hcont_ie" $! rmap').
      iDestruct (big_sepM_sep with "Hmap") as "(Hr & HrV)".
      iSplit.
      iSplit.
      { unfold full_map. iIntros (r).
        destruct (decide (r = PC)). { subst r. rewrite lookup_insert_ne //= lookup_insert //. }
        destruct (decide (r = idc)). { subst r. rewrite lookup_insert //. }
        do 2 rewrite lookup_insert_ne //. iPureIntro. rewrite -elem_of_dom Hrmap. set_solver. }
      { iIntros (ri v Hri Hri' Hvs).
        do 2 rewrite lookup_insert_ne // in Hvs.
        iDestruct (big_sepM_lookup _ _ ri with "HrV") as "HrV"; eauto. }
      { iInsertList "Hr" [PC;idc]. subst rmap'.
        rewrite (insert_commute _ PC) //= !insert_insert.
        iFrame.
      }
    }
    { (* case not IE *)
      set rmap' := <[ idc := (WInt 0%Z: Word) ]> (<[ PC := (WInt 0%Z: Word) ]> rmap) : gmap RegName Word.
      iSpecialize ("Hw'" $! rmap').
      iIntros "(HPC & Hidc & [Hr Hna])". unfold interp_expression, interp_expr, interp_conf. cbn.

      iApply "Hw'". iClear "Hw'". iFrame "#". rewrite /registers_mapsto.
      iAssert (PC ↦ᵣ updatePcPerm w)%I with "[HPC]" as "HPC".
      { destruct_word w ; [ | destruct c | | ] ; cbn in * ; try congruence; iFrame. }
      iAssert (idc ↦ᵣ w')%I with "[Hidc]" as "Hidc".
      { destruct_word w ; [ | destruct c | | ] ; cbn in * ; try congruence; iFrame. }
      iDestruct (big_sepM_sep with "Hr") as "(Hr & HrV)".
      iSplitL "HrV"; [iSplit|].
      { unfold full_map. iIntros (r).
        destruct (decide (r = PC)). { subst r. rewrite lookup_insert_ne //= lookup_insert //. }
        destruct (decide (r = idc)). { subst r. rewrite lookup_insert //. }
        do 2 rewrite lookup_insert_ne //. iPureIntro. rewrite -elem_of_dom Hrmap. set_solver. }
      { iIntros (ri v Hri Hri' Hvs).
        do 2 rewrite lookup_insert_ne // in Hvs.
        iDestruct (big_sepM_lookup _ _ ri with "HrV") as "HrV"; eauto. }
      rewrite (insert_commute _ PC idc) //= !insert_insert //. iFrame.
      iApply big_sepM_insert.
      { rewrite lookup_insert_ne //=. apply not_elem_of_dom. rewrite Hrmap. set_solver. }
      iFrame.
      iApply big_sepM_insert.
      { apply not_elem_of_dom. rewrite Hrmap. set_solver. }
      iFrame.
    }
  Qed.

  Lemma jmp_unknown_safe
    (pc_p : Perm) (pc_b pc_e pc_a : Addr)
    (widc: Word) (r : RegName) :
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->
    r <> PC ->
    ⊢ ∀ rmap,
         ⌜dom rmap = all_registers_s ∖ {[ PC ]}⌝ →
         PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
           ∗ pc_a ↦ₐ jmp r
           ∗ na_own logrel_nais ⊤
         -∗ interp_conf.
  Proof.
    iIntros "%Hpcv %Hr".
    iIntros (rmap) "%Hdom".
    iIntros "(HPC & Hrmap & Hpc_a & Hna)".

    assert (is_Some (rmap !! r)) as [wadv Hwadv].
    {  clear -Hdom Hr. apply elem_of_dom; set_solver. }
    (* iExtract "Hrmap" idc as "[Hidc #Hinterp_widc]". *)
    iExtract "Hrmap" r as "[Hr #Hinterp_wadv]".

    wp_instr.
    destruct ( decide (is_ie_cap wadv = true ) ) as [Hadv|Hadv].
    - (* JMP TO IE-CAP  *)

      destruct_word wadv ; [| destruct c | |] ; cbn in Hadv ; try congruence ; clear Hadv.

      iAssert (interp (WCap IE f f0 f1)) as "Hinterp_wadv'"; first done.
      rewrite {1}(fixpoint_interp1_eq (WCap IE _ _ _)) //=.
      destruct (decide (withinBounds f f0 f1 ∧ withinBounds f f0 (f1 ^+ 1)%a))
        as [ Hbounds | Hbounds] ; cycle 1.
      { (* ill-formed IE, the jump fails *)
        iApply (wp_jmp_fail_IE with "[$HPC $Hr $Hpc_a]")
        ; try solve_pure.
        iNext ; iIntros "(HPC & Hr & Hpc_a)".
        wp_pure; wp_end. by iIntros "%".
      }
      set (Hbounds' := Hbounds).
      destruct Hbounds' as [Hwb Hwb'].
      iDestruct ("Hinterp_wadv" $! Hbounds)
        as (P1 P2) "(%Hpers1 & %Hpers2 & Hinv_f0 & Hinv_f1 & Hcont)".

      assert (Hf1: f1 <> (f1 ^+ 1)%a)
        by (apply Is_true_true_1, withinBounds_true_iff in Hwb; solve_addr).
      iInv (logN.@f1) as (w1) "[>Hf1 #HP1]" "Hcls1".
      iInv (logN.@(f1 ^+1)%a) as (w2) "[>Hf1' #HP2]" "Hcls2".

      destruct (decide (r = idc)) ; simplify_map_eq.
      + iApply (wp_jmp_success_IE_idc with "[$HPC $Hr $Hpc_a $Hf1 $Hf1']")
        ; try solve_pure.
        iNext; iIntros "(HPC& Hr & Hpc_a& Hf0& Hf1) //=".
        iMod ("Hcls2" with "[Hf1 HP2]") as "_"; [iNext ; iExists _ ; iFrame "∗ #"| iModIntro].
        iMod ("Hcls1" with "[Hf0 HP1]") as "_"; [iNext ; iExists _ ; iFrame "∗ #"| iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".

        iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_interp]".
        iInsertList "Hrmap" [idc;PC].

        iApply ("Hcont" $! w1 w2 (<[PC:=w1]> (<[idc:=w2]> rmap))); iFrame "#".
        iSplit; cycle 1.
        { rewrite insert_insert.
          rewrite (insert_commute _ idc PC); [|auto].
          rewrite insert_insert.
          iFrame.
        }
        iSplit.
        { rewrite /full_map.
          iIntros (r') ; iPureIntro.
          apply elem_of_dom.
          rewrite !dom_insert_L Hdom !singleton_union_difference_L; set_solver+.
        }
        {
          iIntros (r0 w Hr0 Hr0' Hregs).
          iClear "Hinterp_wadv Hcont".
          do 2 (rewrite lookup_insert_ne in Hregs ; [|auto]).
          iExtract "Hrmap_interp" r0 as "Hr"; done.
        }

      +
        (* extract idc *)
        assert (∃ widc, ( (delete r rmap) !! idc ) = Some widc) as [widc0 Hidc].
        {  clear -Hdom Hr n. apply elem_of_dom; set_solver. }
        iDestruct (big_sepM_delete _ _ idc with "Hrmap") as "[[Hidc #HVidc] Hrmap]"; eauto.

        iApply (wp_jmp_success_IE with "[$HPC $Hr $Hidc $Hpc_a $Hf1 $Hf1']")
        ; try solve_pure.
        iNext; iIntros "(HPC& Hr & Hidc& Hpc_a& Hf0& Hf1) //=".
        iMod ("Hcls2" with "[Hf1 HP2]") as "_"; [iNext ; iExists _ ; iFrame "∗ #"| iModIntro].
        iMod ("Hcls1" with "[Hf0 HP1]") as "_"; [iNext ; iExists _ ; iFrame "∗ #"| iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iCombine "Hr" "Hinterp_wadv'"  as "Hr".

        iInsert "Hrmap" r.
        replace (<[r:=WCap IE f f0 f1]> (delete idc rmap)) with (delete idc rmap)
          by (rewrite -delete_insert_ne //= insert_id //=).
        iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_interp]".
        iInsertList "Hrmap" [idc;PC].

        iApply ("Hcont" $! w1 w2 (<[PC:=w1]> (<[idc:=w2]> rmap))); iFrame "#".
        iSplit; cycle 1.
        { rewrite insert_insert.
          rewrite (insert_commute _ idc PC); [|auto].
          rewrite insert_insert.
          iFrame.
        }
        iSplit.
        { rewrite /full_map.
          iIntros (r') ; iPureIntro.
          apply elem_of_dom.
          rewrite !dom_insert_L Hdom !singleton_union_difference_L; set_solver+.
        }
        {
          iIntros (r0 w Hr0 Hr0' Hregs).
          iClear "Hinterp_wadv Hcont".
          do 2 (rewrite lookup_insert_ne in Hregs ; [|auto]).
          destruct (decide (r = r0)); simplify_eq; iExtract "Hrmap_interp" r0 as "Hr"; done.
        }

    - (* JMP TO NON IE *)
      apply not_true_is_false in Hadv.
      iDestruct (jmp_to_unknown with "Hinterp_wadv") as "cont".

      (* Jmp adv *)
      iApply (wp_jmp_success with "[$HPC $Hr $Hpc_a]")
      ; [apply decode_encode_instrW_inv| |auto|..]
      ; auto.
      iNext ; iIntros "(HPC & Hi & Hr)".
      wp_pure.

      iCombine "Hr" "Hinterp_wadv"  as "Hr".
      iInsert "Hrmap" r.
      replace (<[r:=wadv]> rmap) with rmap by (rewrite insert_id //=).

      iApply ("cont" $! rmap); auto ; iFrame.
  Qed.


  Lemma region_integers_alloc' E (b e a: Addr) l p :
    Forall (λ w, is_z w = true) l →
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros (Hl) "H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_integers_alloc _ _ _ a _ RX with "H") as ">#H"; auto.
         iModIntro. iIntros (r).
         iDestruct (fundamental _ r with "H") as "H'". eauto. }
    4: { (* IE *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_integers_alloc _ _ _ a _ RX with "H") as ">#H"; auto.
         iModIntro.
         iIntros "%Hbounds".
         iDestruct (read_allowed_inv a a with "H") as (P) "[Hinv [Hpers [Hconds _]] ]"; auto.
         { destruct Hbounds as [ Hbounds%Is_true_true_1%withinBounds_true_iff _ ]; solve_addr. }
         iDestruct (read_allowed_inv (a^+1)%a a with "H") as (P') "[Hinv' [Hpers' [Hconds' _]] ]"; auto.
         { destruct Hbounds as [ _ Hbounds%Is_true_true_1%withinBounds_true_iff ]; solve_addr. }
         iExists P,P'.
         iFrame "#".
         iIntros (w1 w2 r).
         iNext ; iModIntro.
         iIntros "[Hw1 Hw2]".
         iDestruct ("Hconds" with "Hw1") as "#Hinterp1".
         iAssert (interp w2) with "[Hw2]" as "#Hinterp2".
         { iDestruct "Hw2" as "[Hw2 | Hw2]".
           by iDestruct ("Hconds'" with "Hw2") as "#Hinterp2".
           destruct_word w2 ; cbn; try done.
           rewrite !fixpoint_interp1_eq //=.
         }
         iDestruct (fundamental _ r with "Hinterp1") as "H'".
         iApply "H'"; iFrame "#".
    }
    all: iApply region_integers_alloc; eauto.
  Qed.

  Lemma region_valid_alloc' E (b e a: Addr) l p :
    ([∗ list] w ∈ l, interp w) -∗
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros "#Hl H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_valid_alloc _ _ _ a _ RX with "Hl H") as ">#H"; auto.
         iModIntro. iIntros (r).
         iDestruct (fundamental _ r with "H") as "H'". eauto. }
    4: { (* IE *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_valid_alloc _ _ _ a _ RX with "Hl H") as ">#H"; auto.
         iModIntro.
         iIntros "%Hbounds".
         iDestruct (read_allowed_inv a a with "H") as (P) "[Hinv [Hpers [Hconds _]] ]"; auto.
         { destruct Hbounds as [ Hbounds%Is_true_true_1%withinBounds_true_iff _ ]; solve_addr. }
         iDestruct (read_allowed_inv (a^+1)%a a with "H") as (P') "[Hinv' [Hpers' [Hconds' _]] ]"; auto.
         { destruct Hbounds as [ _ Hbounds%Is_true_true_1%withinBounds_true_iff ]; solve_addr. }
         iExists P,P'.
         iFrame "#".
         iIntros (w1 w2 r).
         iNext ; iModIntro.
         iIntros "[Hw1 Hw2]".
         iDestruct ("Hconds" with "Hw1") as "#Hinterp1".
         iAssert (interp w2) with "[Hw2]" as "#Hinterp2".
         { iDestruct "Hw2" as "[Hw2 | Hw2]".
           by iDestruct ("Hconds'" with "Hw2") as "#Hinterp2".
           destruct_word w2 ; cbn; try done.
           rewrite !fixpoint_interp1_eq //=.
         }         iDestruct (fundamental _ r with "Hinterp1") as "H'".
         iApply "H'"; iFrame "#".
    }
    all: iApply (region_valid_alloc with "Hl"); eauto.
  Qed.

  Lemma region_in_region_alloc' E (b e a: Addr) l p :
    Forall (λ a0 : Addr, ↑logN.@a0 ⊆ E) (finz.seq_between b e) ->
    Forall (λ w, is_z w = true \/ in_region w b e) l →
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros (Hmasks Hl) "H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_valid_in_region _ _ _ a _ RX with "H") as ">#H"; auto.
         iModIntro. iIntros (r).
         iDestruct (fundamental _ r with "H") as "H'". eauto. }
    4: { (* IE *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_valid_in_region _ _ _ a _ RX with "H") as ">#H"; auto.
         iModIntro.
         iIntros "%Hbounds".
         iDestruct (read_allowed_inv a a with "H") as (P) "[Hinv [Hpers [Hconds _]] ]"; auto.
         { destruct Hbounds as [ Hbounds%Is_true_true_1%withinBounds_true_iff _ ]; solve_addr. }
         iDestruct (read_allowed_inv (a^+1)%a a with "H") as (P') "[Hinv' [Hpers' [Hconds' _]] ]"; auto.
         { destruct Hbounds as [ _ Hbounds%Is_true_true_1%withinBounds_true_iff ]; solve_addr. }
         iExists P,P'.
         iFrame "#".
         iIntros (w1 w2 r).
         iNext ; iModIntro.
         iIntros "[Hw1 Hw2]".
         iDestruct ("Hconds" with "Hw1") as "#Hinterp1".
         iAssert (interp w2) with "[Hw2]" as "#Hinterp2".
         { iDestruct "Hw2" as "[Hw2 | Hw2]".
           by iDestruct ("Hconds'" with "Hw2") as "#Hinterp2".
           destruct_word w2 ; cbn; try done.
           rewrite !fixpoint_interp1_eq //=.
         }
         iDestruct (fundamental _ r with "Hinterp1") as "H'".
         iApply "H'"; iFrame "#".
    }
    all: iApply (region_valid_in_region with "H"); eauto.
  Qed.

  (* Commonly used property for V(IE, -, -, -) *)
  Program Definition cap_eq p b e a : leibnizO Word -n> iPropO Σ :=
    λne w , ⌜w = WCap p b e a⌝%I.

  Lemma cap_eq_persistent p b e a : ⊢ persistent_cond (cap_eq p b e a).
  Proof.
    iIntros (w). iPureIntro. apply bi.pure_persistent.
  Qed.

  Lemma inv_cap_eq n p b e a:
    inv (logN.@n) (n ↦ₐ WCap p b e a) ⊣⊢
      inv (logN.@n) (∃ w : leibnizO Word, n ↦ₐ w ∗ cap_eq p b e a w).
  Proof.
    iSplit; iIntros "#Hinv"; iApply (inv_iff with "Hinv")
    ; iNext ; iModIntro ; iSplit.
    1,4: iIntros "H" ; iExists _ ; iFrame "H" ; auto.
    all: iIntros "H" ; iDestruct "H" as (w) "[H %cap_eq]" ; simplify_eq ; iFrame.
  Qed.

End fundamental.
