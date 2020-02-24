From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base.
From cap_machine Require Import rules_base.

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

  Lemma interp_cap_preserved W p l a2 a1 a0 a3 (Hne: p <> cap_lang.E):
    (fixpoint interp1) W (inr (p, l, a2, a1, a0)) -∗
    (fixpoint interp1) W (inr (p, l, a2, a1, a3)).
  Proof.
    repeat rewrite fixpoint_interp1_eq. simpl. iIntros "HA".
    destruct p; auto; congruence.
  Qed.

  Lemma lookup_insert_is_Some_weaken
    {K : Type} {M : Type → Type} `{FMap M} `{∀ A : Type, Lookup K A (M A)} `{∀ A : Type, Empty (M A)}
               `{∀ A : Type, PartialAlter K A (M A)} `{OMap M} `{Merge M}
               `{∀ A : Type, FinMapToList K A (M A)} `{EqDecision K} `{FinMap K M} :
    ∀ {A : Type} (m : M A) (i j : K) (x : A),
      is_Some (m !! j) → is_Some (<[i:=x]> m !! j).
  Proof.
    intros. rewrite lookup_insert_is_Some. destruct (decide (i = j)); auto.
  Qed.

  Lemma lea_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r0 : Z + RegName):
    ftlr_instr W r p p' g b e a w (cap_lang.Lea dst r0) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. by apply lookup_insert_is_Some_weaken. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * -> Hdst ? Hz Hoffset HincrPC |].
    { apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs').

      assert (p'' = p ∧ g'' = g ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto. iNext.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      iApply ("IH" $! _ regs' with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH".
      { cbn. intros. subst regs'. by repeat apply lookup_insert_is_Some_weaken. }
      { iIntros (ri Hri). subst regs'.
        erewrite locate_ne_reg; [ | | reflexivity]; auto.
        destruct (decide (ri = dst)).
        { subst ri. unshelve iSpecialize ("Hreg" $! dst _); eauto.
          erewrite locate_eq_reg; [ | reflexivity]; auto. simplify_map_eq.
          rewrite /RegLocate Hdst. iApply interp_cap_preserved; auto. }
        { repeat (erewrite locate_ne_reg; [ | | reflexivity]; auto).
          iApply "Hreg"; auto. } }
      { subst regs'. rewrite insert_insert. iApply "Hmap". }
      { iPureIntro. tauto. }
      eauto. }
    { subst retv. iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
