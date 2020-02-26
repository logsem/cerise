From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_IsPtr.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma isptr_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst r0 : RegName) :
    ftlr_instr W r p p' g b e a w (cap_lang.IsPtr dst r0) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_IsPtr with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { (* todo: tactic *) intro ri. rewrite lookup_insert_is_Some.
      destruct (decide (PC = ri)); eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      assert (dst <> PC) as HdstPC.
      { intro. subst dst. rewrite lookup_insert in HPC.
        destruct (<[PC:=inr (p, g, b, e, a)]> r !! r0) as [wx|] eqn:Hn; rewrite Hn in HPC; try destruct wx; inv HPC. }

      rewrite lookup_insert_ne in HPC; auto.
      rewrite lookup_insert in HPC; inv HPC.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      iApply ("IH" $! _ (<[dst:= _]> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto.
      + intros; simpl.
        rewrite lookup_insert_is_Some.
        destruct (reg_eq_dec dst x0); auto; right; split; auto.
        rewrite lookup_insert_is_Some.
        destruct (reg_eq_dec PC x0); auto; right; split; auto.
      + iIntros (ri Hri).
        destruct (reg_eq_dec ri dst).
        * subst ri. rewrite /RegLocate lookup_insert.
          destruct (<[PC:=inr (p'', g'', b'', e'', a'')]> r !! r0) as [wx|] eqn:Hn; rewrite Hn; try destruct wx; repeat rewrite fixpoint_interp1_eq; auto.
        * repeat rewrite /RegLocate lookup_insert_ne; auto.
          iApply "Hreg"; auto. }
  Qed.

End fundamental.
