From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.rules Require Import rules_Jnz.
From cap_machine.ftlr Require Import ftlr_base Jmp.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* Derice pure conds =allow_jnz_mmap_or_true= from =cond_jnz= *)
  Lemma mem_map_implies_pure_conds:
    ∀ (regs : Reg) (mem : Mem) (dst src : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr) (wsrc : Word)
      (P1 P2 : D),
      read_reg_inr regs dst p b e a
      -> regs !! src = Some wsrc
      -> allow_jmp_mem (cond_jnz regs src wsrc) regs mem dst pc_a pc_w p b e a P1 P2
        -∗ ⌜mem !! pc_a = Some pc_w⌝
          ∗ ⌜allow_jmp_mmap_or_true (cond_jnz regs src wsrc) dst regs mem⌝.
  Proof.
    iIntros (regs mem dst src pc_a pc_w p b e a wsrc P1 P2 Hrinr Hsrc) "HJmpMem".
    rewrite /allow_jmp_mem.
    case_decide as Hdec ; cycle 1.
    { iDestruct "HJmpMem" as "->".
      iSplitR. by rewrite lookup_insert.
      iPureIntro.
      exists p,b,e,a.
      split; auto.
      rewrite decide_False //=.
    }
    destruct Hdec as (Hdec & Hjnz).

    rewrite /allow_jmp_mem_res.
    assert (a <> (a^+1)%a)
    by (inversion Hdec as (_ & _ & Hwb%Is_true_true_1%withinBounds_true_iff & _); solve_addr).

    case_decide as Ha; simplify_eq.
    { (* pc_a = a *)
      iDestruct "HJmpMem" as (w2) "[%Hmem _]" ; subst.
      iSplitL; iPureIntro.
      by simplify_map_eq.
      exists p,b,e,a.
      split;auto.
      rewrite decide_True //=.
      exists pc_w, w2.
      by split ; simplify_map_eq.
    }

    case_decide as Ha'; simplify_eq.
    { (* pc_a = a+1 *)
      iDestruct "HJmpMem" as (w1) "[%Hmem _]" ; subst.
      iSplitL; iPureIntro.
      by simplify_map_eq.
      exists p,b,e,a.
      split;auto.
      rewrite decide_True //=.
      exists w1, pc_w.
      by split ; simplify_map_eq.
    }

    (* pc_a ≠ a ∧ pc_a ≠ a+1 *)
    iDestruct "HJmpMem" as (w1 w2) "[%Hmem _]" ; subst.
    iSplitL; iPureIntro.
    by simplify_map_eq.
    exists p,b,e,a.
    split;auto.
    rewrite decide_True //=.
    exists w1, w2.
    by split ; simplify_map_eq.
  Qed.

  Lemma jnz_case (regs : Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst src : RegName) (P : D):
    ftlr_instr regs p b e a widc w (Jnz dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread _] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p b e a]> (<[idc:=widc]> regs) !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      destruct (decide (x = idc)).
      rewrite lookup_insert_ne; auto.
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      by rewrite! lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0, read_reg_inr (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) dst p0 b0 e0 a0)
      as [p0 [b0 [e0 [a0 HVdst] ] ] ].
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. rewrite Hsomedst.
      destruct wdst as [|[ p0 b0 e0 a0|] | ]; try done.
      by repeat eexists.
    }

    assert (exists wsrc, (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) !! src = Some wsrc) as [wsrc HVsrc].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      by eexists.
    }

    iAssert (
        ∀ (r' : RegName) (w : Word),
          ⌜r' ≠ PC⌝ → ⌜<[idc:=widc]> regs  !! r' = Some w⌝ → fixpoint interp1 w
      )%I as "Hreg'".
    { iIntros.
      destruct (decide (r' = idc)); simplify_map_eq; auto.
      iApply "Hreg";eauto.
    }

    set (Hcond_jnz := cond_jnz (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) src wsrc).

    (* Step 1: open the region, if necessary, and store all the resources
       obtained from the region in allow_IE_res *)
    iDestruct ((create_jmp_res Hcond_jnz _ _ p)  with "Hreg'") as (P1 P2) "HJmpRes"; eauto.
    { destruct Hp ; destruct p ; auto. }

    (* Step2: derive the concrete map of memory we need, and any spatial
       predicates holding over it *)
    iMod ((jmp_res_implies_mem_map Hcond_jnz)
           with "HJmpRes Ha") as (mem) "[HJmpMem HJmpRest]"; eauto.

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct ((mem_map_implies_pure_conds _ mem dst src a w p0 b0 e0 a0 wsrc P1 P2)
                with "HJmpMem") as %(HReadPC & HAJmpMem); eauto.

    (* Step 3.5:  derive the non-spatial conditions over the registers *)
    assert (allow_jmp_rmap_or_true Hcond_jnz dst (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)))
      as HAJmpReg.
    { rewrite /allow_jmp_rmap_or_true.
      exists p0, b0, e0, a0.
      split; auto.
      (* TODO any way to avoid manual match ? *)
      match goal with
      | H: _ |- (if (decide ?cond) then _ else _) =>
          destruct (decide cond)
      end; auto.
      by eexists _; simplify_map_eq.
    }

    assert (
        regs_of (Jnz dst src) ⊆ dom (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))
      ).
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
    iApply (wp_Jnz _ _ _ _ _ _ _ _ (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))
             with "[Hmap HJmpRest]");eauto.
    { by simplify_map_eq. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".
    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw".
    rewrite /allow_jmp_res /allow_jmp_mem /allow_jmp_mask_reg /allow_jmp_mask.

    destruct HSpec as
      [ Hfail
      | * Hsrc Hdst Hcond Hwb Hwb' Ha Ha' HincrPC (* Success IE true *)
      | * Hsrc Hdst Hcond HnIE HincrPC (* Success true *)
      | * Hsrc Hcond HincrPC (* Success false *)
      ].
    - (* Fail *)
      match goal with
      | H: _ |- context [(if (decide ?cond) then _ else _)] =>
          destruct (decide cond) as [HallowJmp|HallowJmp] ; cycle 1
      end; auto.
      {
        iModIntro.
        iDestruct "HJmpMem" as "->". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto; iIntros; discriminate.
      }
      destruct HallowJmp as (HallowJmp & _).
      assert ((a0 ^+ 1)%a ≠ a0) as Ha0eq
          by (destruct HallowJmp as (_ & _ & Hwb%Is_true_true_1%withinBounds_true_iff & _); solve_addr).
      rewrite /allow_jmp_mem_res /allow_jmp_mask.

      (* Step 4: return all the resources we had *)
      iMod (mem_map_recover_res with "HJmpMem Hmem") as "Ha"; auto.

      iModIntro.
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto; iIntros; discriminate.

    - (* Success IE true*)
      rewrite insert_insert insert_commute //= insert_insert in HincrPC; subst regs'.
      match goal with
      | H: _ |- context [(if (decide ?cond) then _ else _)] =>
          destruct (decide cond) as [HallowJmp|HallowJmp]
      end; auto.
      2: { (* contradiction *)
        rewrite /reg_allows_IE_jmp in HallowJmp.
        rewrite /read_reg_inr in HVdst.
        rewrite Hdst in HVdst; simplify_eq.
        repeat (apply not_and_r in HallowJmp as [HallowJmp|HallowJmp] ; simplify_eq)
        ; try congruence.
        exfalso. apply HallowJmp.
        by rewrite /Hcond_jnz /cond_jnz; intros _.
      }
      destruct HallowJmp as (HallowJmp & _).
      assert (PC <> dst) as Hdst'
          by (destruct (decide (PC = dst)); auto; simplify_map_eq; by destruct Hp).
      assert (p0 = IE /\ b0 = b1 /\ e0 = e1 /\ a0 = a1) as (-> & <- & <- & <-)
          by (by eapply reg_allows_IE_jmp_same)
      ; simplify_map_eq.
      assert ((a0 ^+ 1)%a ≠ a0) as Haeq by (apply Is_true_true_1, withinBounds_true_iff in Hwb ; solve_addr).
      assert (withinBounds b0 e0 a0 ∧ withinBounds b0 e0 (a0 ^+ 1)%a) as Hbounds
          by auto.

      iDestruct "HJmpRes" as "(Hexec&HJmpRes)".

      (* Step 4: return all the resources we had *)
      iMod ((mem_map_recover_res_ie _ _ _ w wpc widc0 P P1 P2) with "HJmpMem Hmem") as "Ha"
      ; auto; iModIntro.


      destruct_decide (decide (a = a0)) as Ha0; simplify_eq.
      { (* a = a0 *)

        iDestruct "Ha" as "[Ha0 ->]".

        iMod ("Hcls" with "[HP Ha0]") as "_"; [iNext;iExists wpc;iFrame|iModIntro].
        iClear "HJmpRes".
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        destruct wpc; cbn in Hi; try done.
        iExtract "Hmap" PC as "HPC".
        iApply interp_expr_invalid_pc; try iFrame ; eauto.
        intro Hcontra; inversion Hcontra.
        iPureIntro; apply regmap_full_dom in Hsome; rewrite -Hsome; set_solver.
      }

      destruct_decide (decide (a = (a0 ^+ 1)%a)) as Ha0'; simplify_eq.
      { (* a = a0+1 *)

        iDestruct "Ha" as "(Ha0 & -> & HP1 & %Hpers1)".
        iDestruct "HP1" as "#HP1".

        iMod ("Hcls" with "[HP Ha0]") as "_"; [iNext;iExists widc0;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iApply ("Hexec" $! _ widc0) ; iFrame "∗ #".
        iRight; destruct widc0; cbn in Hi; try done.
        rewrite insert_commute //=.
        repeat (iSplit ; try done).
      }

      (* a ≠ a0 ∧ a ≠ a0+1 *)
      iDestruct "Ha" as "(Ha & HP1 & HP2 & %Hpers1 & %Hpers2)".
      iDestruct "HP1" as "#HP1"; iDestruct "HP2" as "#HP2".
      iMod ("Hcls" with "[HP Ha]") as "_"; [iNext;iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply "Hexec" ; iFrame "∗ #".
      rewrite insert_commute //=.
      repeat (iSplit ; try done).

    - (* Success true *)
      rewrite insert_insert in HincrPC; subst regs'.
      match goal with
      | H: _ |- context[(if (decide ?cond) then _ else _)]=>
          destruct_decide (decide cond) as HallowJmp
      end; auto.
      { (* contradiction *)
        rewrite /reg_allows_IE_jmp in HallowJmp.
        destruct HallowJmp as ((Hregs0 & -> & Hwb & Hwb') & _).
        rewrite Hregs0 in Hdst.
        simplify_map_eq.
      }
      iModIntro.
      iDestruct "HJmpMem" as "->". rewrite -memMap_resource_1.
      iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.

      set (regs' := <[PC:=updatePcPerm w0]> (<[idc:=widc]> regs)).
      (* Needed because IH disallows non-capability values *)
      destruct w' as [ | [p' b' e' a' | ] | ]; cycle 1.
      {
        rewrite /updatePcPerm.
        set (pc_p' := if decide (p' = E) then RX else p').

        destruct (decide (p' = E)); simplify_map_eq.
        (* Special case if p' is E *)
        - (* p' = E *)
          iAssert (interp (WCap E b' e' a')) as "Hinterp".
          {
          assert ( dst <> PC ).
          { destruct (decide (dst = PC)) ; simplify_map_eq ; destruct Hp; auto. }
          simplify_map_eq.
          destruct (decide (dst = idc)) ; simplify_map_eq; auto.
          iApply "Hreg"; auto.
          }
          rewrite (fixpoint_interp1_eq (WCap E _ _ _)) //=.
          rewrite (insert_commute _ PC _ (WCap RX _ _ _)) //=.
          iDestruct ("Hinterp" with "[$Hinv_idc] [$Hmap $Hown]") as "Hcont"; auto.
        - (* p' ≠ E *)
        iNext ; iIntros "_".
        iApply ("IH" $! regs' pc_p' with "[%] [] [Hmap] [$Hown]"); subst regs'.
        { intro; cbn; by repeat (rewrite lookup_insert_is_Some'; right). }
        { iIntros (ri v Hri Hri' Hvs).
          simplify_map_eq.
          iApply "Hreg"; auto.
        }
        { rewrite
            insert_insert
              (insert_commute _ idc) //=
              insert_insert.
          subst pc_p'; simplify_eq.
          by destruct p'.
        }
        { iModIntro.
          subst pc_p'.
          iClear "HJmpRes IH Hread".
          clear Hsome' HVdst HAJmpMem HAJmpReg.

          destruct (decide (dst = PC)); simplify_map_eq; auto.
          destruct (decide (dst = idc)); simplify_map_eq; auto.
          iApply "Hreg" ; auto.
        }
        { iFrame "Hinv_idc". }
      }

      all: iNext ; iIntros "_".
      all: iExtract "Hmap" PC as "HPC".
      all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
        iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ].
      all: repeat iNext; iIntros "HPC /=".
      all: iApply wp_pure_step_later; auto.
      all: iNext; iIntros "_".
      all: iApply wp_value;iIntros; discriminate.

    - (* Success IE false *)
      apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .
      rewrite insert_insert in Hregs'; subst regs'.
      simplify_map_eq.

      match goal with
      | H: _ |- context [(if (decide ?cond) then _ else _)] =>
          destruct_decide (decide cond) as Heq
      end; simplify_eq.
      { (* contradiction *)
        exfalso.
        destruct Heq as (_ & Hnz) ; simplify_eq.
        apply Hnz in HVsrc.
        rewrite HVsrc in Hcond; congruence.
      }
      iModIntro.
      iDestruct "HJmpMem" as "->"; simplify_eq. rewrite -memMap_resource_1.
      iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.

      set (regs' := <[PC:=WCap p'' b'' e'' x]> (<[idc:=widc]> regs)).
      simplify_map_eq.

      iNext ; iIntros "_".
      iApply ("IH" $! regs' p'' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { intro; cbn; by repeat (rewrite lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        simplify_map_eq.
        iApply "Hreg"; auto.
      }
      { rewrite
          insert_insert
            (insert_commute _ idc) //=
            insert_insert.
        iFrame.
      }
      { iModIntro.
        iClear "HJmpRes IH Hread".
        rewrite !fixpoint_interp1_eq //=; destruct Hp as [-> | ->] ;iFrame "Hinv_pc".
      }
      { iFrame "Hinv_idc". }
  Qed.

End fundamental.
