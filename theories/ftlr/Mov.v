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

  Lemma mov_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst : RegName) (src : Z + RegName) (P : D):
    ftlr_instr r p b e a widc w (Mov dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right.
      destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists w; iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv as (p''&b''&e''&a''& ? & HPC & Z & Hregs'); simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists w; iFrame|iModIntro].
      iNext.
      destruct (reg_eq_dec dst PC).
      { subst dst.
        (* rewrite lookup_insert in H1. *)
        (* inv H1. *)
        simplify_map_eq.
        repeat rewrite insert_insert.
        destruct src; simpl in *; try discriminate.
        destruct (reg_eq_dec PC r0).
        { subst r0.
        rewrite lookup_insert in H0 ; inv H0.
        rewrite (insert_commute _ PC idc); auto.
        iIntros "_".
        iApply ("IH" $! r with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto.
        iModIntro. rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->]; iFrame "Hinv_pc". }
        { simplify_map_eq.
          iDestruct ("Hreg" $! r0 _ _ H0) as "Hr0".
          destruct (PermFlowsTo RX p'') eqn:Hpft; iIntros "_".
          - iApply ("IH" $! r with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto.
            + iModIntro.
              destruct p''; simpl in Hpft; try discriminate; repeat (rewrite fixpoint_interp1_eq); simpl; auto.
          - iApply (wp_bind (fill [SeqCtx])).
            iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p''; simpl in Hpft; try discriminate; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iNext; iIntros "_".
            iApply wp_value.
            iIntros. discriminate. } }
      { simplify_map_eq.
        iIntros "_".
        iApply ("IH" $! (<[dst:=w0]> _) with "[%] [] [Hmap] [$Hown]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec dst x0); auto; right; split; auto.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec PC x0); auto; right; split; auto.
        - iIntros (ri v Hri Hvs).
          destruct (reg_eq_dec ri dst).
          + subst ri. rewrite lookup_insert in Hvs.
            destruct src; simplify_map_eq.
            * repeat rewrite fixpoint_interp1_eq; auto.
            * destruct (reg_eq_dec PC r0).
              { subst r0.
                - simplify_map_eq.
                  rewrite !fixpoint_interp1_eq /=.
                  destruct Hp as [Hp | Hp]; subst p''; try subst g'';
                    (iFrame "Hinv Hexec"). }
              simplify_map_eq.
              iDestruct ("Hreg" $! r0 _ _ H0) as "Hr0". auto.
          + repeat rewrite lookup_insert_ne in Hvs; auto.
            iApply "Hreg"; auto.
        - iModIntro. rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->]; iFrame "Hinv".
      }
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
