From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone.
From cap_machine.rules Require Import rules_base rules_Mov.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma mov_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName):
    ftlr_instr W r p p' g b e a w (Mov dst src) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion [Hnotrevoked Hnotstatic] HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { (* TODO: it might be possible to refactor the proof below by using more simplify_map_eq *)
      (* TODO: use incrementPC_inv *)
      match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      destruct (reg_eq_dec dst PC).
      { subst dst. rewrite lookup_insert in HPC. inv HPC.
        repeat rewrite insert_insert.
        destruct src; simpl in *; try discriminate.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        { destruct ρ;auto;[..|specialize (Hnotstatic g0)];contradiction. }
        destruct (reg_eq_dec PC r0).
        { subst r0. simplify_map_eq.
          iApply ("IH" $! _ r with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto. }
        { simplify_map_eq.
          rewrite /RegLocate. iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hr0". rewrite H0.
          destruct (PermFlowsTo RX p'') eqn:Hpft.
          - iApply ("IH" $! _ r with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto.
            + destruct p''; simpl in Hpft; auto.
              repeat rewrite fixpoint_interp1_eq. simpl.
              destruct g''; auto. 
            + iModIntro.
              destruct p''; simpl in Hpft; try discriminate; repeat (rewrite fixpoint_interp1_eq); simpl; auto.
              destruct g''; auto. 
          - iApply (wp_bind (fill [SeqCtx])).
            iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p''; simpl in Hpft; try discriminate; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate. } }
      { rewrite lookup_insert_ne in HPC; auto.
        rewrite lookup_insert in HPC. inv HPC.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        { destruct ρ;auto;[..|specialize (Hnotstatic g)];contradiction. }
        iApply ("IH" $! _ (<[dst:=w0]> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec dst x0); auto; right; split; auto.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec PC x0); auto; right; split; auto.
        - iIntros (ri Hri).
          destruct (reg_eq_dec ri dst).
          + subst ri. rewrite /RegLocate lookup_insert.
            destruct src; simplify_map_eq.
            * repeat rewrite fixpoint_interp1_eq; auto.
            * destruct (reg_eq_dec PC r0).
              { subst r0.
                - simplify_map_eq. 
                  rewrite (fixpoint_interp1_eq _ (inr (_, g'', b'', e'', a''))) /=.
                destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; subst p''; try subst g'';
                  (iFrame "Hinv Hexec"). }
              simplify_map_eq.
              iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hr0". rewrite H0. auto.
          + repeat rewrite /RegLocate lookup_insert_ne; auto.
            iApply "Hreg"; auto.
      }
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
