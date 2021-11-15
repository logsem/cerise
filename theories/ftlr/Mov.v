From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
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
        (b e a : Addr) (w : Word) (dst : RegName) (src : Z + RegName) (P : D):
    ftlr_instr r p b e a w (Mov dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists w; iFrame|iModIntro]. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { (* TODO: it might be possible to refactor the proof below by using more simplify_map_eq *)
      (* TODO: use incrementPC_inv *)
      match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists w; iFrame|iModIntro].
      iNext.
      destruct (reg_eq_dec dst PC).
      { subst dst. rewrite lookup_insert in HPC. inv HPC.
        repeat rewrite insert_insert.
        destruct src; simpl in *; try discriminate.
        destruct (reg_eq_dec PC r0).
        { subst r0. simplify_map_eq.
          iApply ("IH" $! r with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto.
          iModIntro. rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->]; iFrame "Hinv". }
        { simplify_map_eq.
          iDestruct ("Hreg" $! r0 _ _ H0) as "Hr0".
          destruct (PermFlowsTo RX p'') eqn:Hpft.
          - iApply ("IH" $! r with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto.
            + iModIntro.
              destruct p''; simpl in Hpft; try discriminate; repeat (rewrite fixpoint_interp1_eq); simpl; auto.
          - iApply (wp_bind (fill [SeqCtx])).
            iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p''; simpl in Hpft; try discriminate; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate. } }
      { rewrite lookup_insert_ne in HPC; auto.
        rewrite lookup_insert in HPC. inv HPC.
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
