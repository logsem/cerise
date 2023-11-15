From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_base rules_Mov.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma mov_case (regs : leibnizO Reg)
    (p : Perm) (b e a : Addr)
    (widc w : Word) (dst : RegName) (src : Z + RegName) (P:D):
    ftlr_instr regs p b e a widc w (Mov dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right.
      destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hrarg HincrPC |]; cycle 1.
    - (* Failure *)
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists w; iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - (* Success *)
      incrementPC_inv as (p''&b''&e''&a''& ? & HPC & Z & Hregs') ; simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists w; iFrame|iModIntro].
      iNext; iIntros "_".

      set (widc' := if (decide (dst = idc)) then w0 else widc).
      set (wpc' := if (decide (dst = PC) ) then WCap p b e x else w0).
      set (regs' := <[PC:=wpc']> (<[dst:= w0]> (<[idc:=widc]> regs))).

      destruct (PermFlowsTo RX p'') eqn:Hpft; cycle 1.
      {
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p''; simpl in Hpft; try discriminate; eauto|].
        iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value.
        iIntros; discriminate.
      }

      iAssert (fixpoint interp1 (WCap p'' b'' e'' a''))%I as "Hinterp_wpc".
      { destruct src as [z | src]; cbn in Hrarg; simplify_map_eq.
        + destruct (decide (PC = dst)) as [|Hdst]; simplify_map_eq.
          rewrite !fixpoint_interp1_eq //=; destruct Hp as [-> | ->] ;iFrame "Hinv_pc".
        + destruct (decide (PC = dst)) as [|Hdst]; simplify_map_eq.
          * destruct (decide (src = PC)); simplify_map_eq.
            ** rewrite !fixpoint_interp1_eq //=; destruct Hp as [-> | ->] ;iFrame "Hinv_pc".
            ** destruct (decide (src = idc)); simplify_map_eq; auto.
               iApply ("Hreg" $! src); auto.
          * destruct (decide (src = PC)); simplify_map_eq.
            ** rewrite !fixpoint_interp1_eq //=; destruct Hp as [-> | ->] ;iFrame "Hinv_pc".
            ** destruct (decide (src = idc)); simplify_map_eq; auto.
      }

      iAssert (fixpoint interp1 w0) as "Hinterp_w0".
      { destruct src as [ z | src ]; cbn in Hrarg ; simplify_map_eq.
        rewrite !fixpoint_interp1_eq; auto.
        destruct (decide (src = PC)); simplify_map_eq; auto.
        destruct (decide (src = idc)); simplify_map_eq; auto.
        iApply ("Hreg" $! src); auto.
      }

      iApply ("IH" $! regs' _ _ _ _ widc' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { intro.
        eapply (lookup_insert_is_Some' (<[dst:=w0]> (<[idc:=widc]> regs))); right.
        eapply (lookup_insert_is_Some' (<[idc:=widc]> regs)); right.
        by eapply (lookup_insert_is_Some' regs); right.
      }
      { iIntros (ri v Hri Hri' Hvs).
        iClear "Hwrite".
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        * destruct src as [z | src]; cbn in Hrarg ; simplify_eq.
          { rewrite !fixpoint_interp1_eq; auto. }
          destruct (decide (src = PC)); simplify_map_eq; auto.
        * iApply "Hreg"; auto.
      }
      { iClear "Hwrite".
        subst widc' wpc'.
        case_decide as Hidc; simplify_map_eq.
        - rewrite
            (insert_commute _ idc _ ) //=
              !insert_insert
              (insert_commute _ idc _ ) //=
              !insert_insert
          ; iFrame.
        - case_decide as Hpc; simplify_map_eq.
          * rewrite
              !insert_insert
                (insert_commute _ idc _ ) //=
                !insert_insert
          ; iFrame.
          * rewrite
              !insert_insert
                (insert_commute _ _ PC ) //=
                !insert_insert
                (insert_commute _ idc _ ) //=
                (insert_commute _ idc _ ) //=
                !insert_insert
            ; iFrame.
      }
      { iModIntro.
        destruct p'' ; cbn in Hpft; try congruence
        ; rewrite !fixpoint_interp1_eq //=; iFrame "Hinv_pc".
      }
      { subst widc'; destruct (decide (dst = idc)) ; simplify_map_eq; auto. }
  Qed.

End fundamental.
