From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.rules Require Import rules_Jnz.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma jnz_case (regs : Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst src : RegName) (P : D):
    ftlr_instr regs p b e a widc w (Jnz dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread _] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. repeat (apply lookup_insert_is_Some'; right ; eauto). }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as
      [ * Hsrc Hcond HincrPC (* Fail *)
      | * Hsrc Hcond HincrPC (* Success false *)
      | * Hsrc Hdst Hcond (* Success true *)
      ].

    (* Hfail *)
    {
      iApply wp_pure_step_later;  auto.
      iMod ("Hcls" with "[Hmem HP]");[iExists w;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    }

    (* Hsuccess false *)
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq. rewrite insert_insert.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Hmem HP]");[iExists w;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply ("IH" $! regs _ _ _ x with "[%] [] [Hmap] [$Hown]"); eauto.
      { rewrite insert_commute //=. }
      iModIntro.
      iApply (interp_weakening with "IH"); eauto.
      by destruct Hp as [-> | ->].
      by destruct Hp as [-> | ->].
      solve_addr.
      solve_addr.
      by rewrite PermFlowsToReflexive.
    }

    (* Hsuccess true *)
    { simplify_map_eq. iApply wp_pure_step_later; auto.
      rewrite !insert_insert.

      iMod ("Hcls" with "[HP Hmem]");[iExists w;iFrame|iModIntro].

      (* Needed because IH disallows non-capability values *)
      destruct w' as [ | [p' b' e' a' | ] | ]; cycle 1.
      {
        rewrite /updatePcPerm.
        iAssert (fixpoint interp1 (WCap p' b' e' a')) as "HECap".
        { destruct (decide (dst = PC)) as [-> | Hne]. by simplify_map_eq.
          rewrite lookup_insert_ne // in Hdst.
          { destruct (decide (dst = idc)) as [-> | Hne']. by simplify_map_eq.
            rewrite lookup_insert_ne // in Hdst.
            iApply "Hreg"; eauto.
          }
        }

        (* Special case for E-values*)
        destruct (decide (p' = E)) as [-> | HneE].
        - iEval (rewrite fixpoint_interp1_eq; simpl) in "HECap".
          rewrite insert_commute //=.

          iDestruct ("HECap" with "[$Hinv_idc] [$Hmap $Hown]") as "Hcont"; auto.
        - iAssert ([∗ map] k↦y ∈ <[PC:= WCap p' b' e' a']> (<[idc:=widc]> regs), k ↦ᵣ y)%I  with "[Hmap]" as "Hmap".
          { destruct p'; auto. congruence. }
          iNext; iIntros "_".

          iApply ("IH" $! (<[PC:=WCap p' b' e' a']> (<[idc:=widc]> regs)) with "[%] [] [Hmap] [$Hown]").
          { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
          { iIntros (ri v Hri Hri' Hvs).
            rewrite lookup_insert_ne in Hvs; auto.
            iApply "Hreg"; eauto. by simplify_map_eq. }
          { rewrite insert_insert insert_commute //=.
            rewrite (insert_commute _ PC) //= insert_insert.
            iFrame "Hmap". }
          auto.
          auto.
      }
      (* Non-capability cases *)

      all: iNext; iIntros "_".
      all: iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap] /=";
        [apply lookup_insert|]; simpl.
      all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
        iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ].
      all: repeat iNext; iIntros "HPC /=".
      all: iApply wp_pure_step_later; auto.
      all: iNext; iIntros "_".
      all: iApply wp_value.
      all: iIntros.
      all: discriminate.
    }
  Qed.

End fundamental.
