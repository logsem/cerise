From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_base rules_Mov.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma mov_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst : RegName) (src : Z + RegName) (P : D):
    ftlr_instr lregs p b e a v lw (Mov dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [lw' Harg Hincr | lw' Harg Hincr]; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementLPC_inv as (p''&b''&e''&a''&v''& ? & HPC & Z & Hregs'); simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro].
      iNext.
      destruct (reg_eq_dec dst PC).
      { subst dst.
        rewrite lookup_insert in HPC; simplify_eq.
        repeat rewrite insert_insert.
        destruct src; simpl in *; simplify_eq; try discriminate.
        destruct (reg_eq_dec PC r).
        { subst r.
          rewrite lookup_insert in Harg; simplify_eq.
          iIntros "_".
          iApply ("IH" $! lregs with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto.
          iModIntro. rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv".
        }
        { rewrite lookup_insert_ne in Harg; auto; simplify_eq.
          iDestruct ("Hreg" $! r _ _ Harg) as "Hr".
          destruct (PermFlowsTo RX p'') eqn:Hpft; iIntros "_".
          - iApply ("IH" $! lregs with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto.
            + iModIntro.
              destruct p''; simpl in Hpft; try discriminate
              ; repeat (rewrite fixpoint_interp1_eq); simpl; auto.
          - iApply (wp_bind (fill [SeqCtx])).
            iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]" ; [apply lookup_insert|].
            iApply (wp_notCorrectPC with "HPC"); auto
            ; [eapply not_isCorrectLPC_perm; destruct p''; simpl in Hpft; try discriminate; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iNext; iIntros "_".
            iApply wp_value.
            iIntros. discriminate.
        }
      }
      { rewrite lookup_insert_ne in HPC ; simplify_eq.
        iIntros "_".
        iApply ("IH" $! (<[dst:=lw']> _) with "[%] [] [Hmap] [$Hown]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec dst x0); auto; right; split; auto.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec PC x0); auto; right; split; auto.
        - iIntros (ri ? Hri Hvs).
          destruct (reg_eq_dec ri dst).
          + subst ri. rewrite lookup_insert in Hvs.
            destruct src; simplify_map_eq.
            * repeat rewrite fixpoint_interp1_eq; auto.
            * destruct (reg_eq_dec PC r).
              { subst r.
                rewrite lookup_insert in Harg; simplify_eq.
                rewrite !fixpoint_interp1_eq /=.
                destruct Hp as [Hp | Hp]; subst p''; try subst g'';
                  (iFrame "Hinv Hexec").
              }
              { rewrite lookup_insert_ne in Harg; auto; simplify_eq.
                iDestruct ("Hreg" $! r _ _ Harg) as "Hr". auto.
              }
          + repeat rewrite lookup_insert_ne in Hvs; auto.
            iApply "Hreg"; auto.
        - iModIntro.
          rewrite lookup_insert in HPC; simplify_eq.
          rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto.
        - auto.
      }
    }
    Unshelve. all: done.
  Qed.

End fundamental.
