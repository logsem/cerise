From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Export ftlr_base.
From cap_machine.rules Require Export rules_Get rules_base.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.
  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma get_case (regs : leibnizO Reg)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr)
    (widc w : Word) (dst r : RegName) (ins: instr) (P:D) :
    is_Get ins dst r →
    ftlr_instr regs p_pc b_pc e_pc a_pc widc w ins P.
  Proof.
    intros Hinstr Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].
    rewrite <- Hi in Hinstr. clear Hi.
    iApply (wp_Get with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right.
      destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [* Hsrc Hi HincrPC |]; cycle 1.
    - (* Fail *)
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - (* Success *)
      incrementPC_inv as (p''&b''&e''&a''& ? & HPC & Z & Hregs') ; simplify_map_eq.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      iIntros "_".
      rewrite (insert_commute _ dst PC) //= insert_insert; auto
      ; simplify_map_eq.

      set (widc' := if (decide (dst = idc)) then WInt z else widc).
      set (regs' := <[PC:=WCap p'' b'' e'' a'']> (<[dst:=WInt z]> (<[idc:=widc]> regs))).

      iApply ("IH" $! regs' _ _ _ _ widc' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { intro; cbn; by repeat (rewrite lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        destruct (decide (ri = dst)); simplify_map_eq.
        * by rewrite !fixpoint_interp1_eq.
        * iApply "Hreg"; auto.
      }
      { iClear "Hwrite".
        subst widc'. case_decide as Heq; simplify_map_eq.
        + rewrite
            !insert_insert
              (insert_commute _ idc _) //=
              !insert_insert; iFrame.
        + rewrite
            !insert_insert
              (insert_commute _ idc _) //=
              (insert_commute _ idc _) //=
              insert_insert ; iFrame.
      }
      rewrite !fixpoint_interp1_eq //=; destruct Hp as [-> | ->] ;iFrame "Hinv_pc".
      subst widc'.
      destruct (decide (dst = idc)) ; simplify_map_eq; auto.
      by rewrite !fixpoint_interp1_eq.
  Qed.

End fundamental.
