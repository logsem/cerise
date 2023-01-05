From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_base rules_Jnz.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma jnz_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (r1 r2 : RegName) (P : D):
    ftlr_instr r p b e a w (Jnz r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq. rewrite insert_insert.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply ("IH" $! r with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto. iModIntro.
      rewrite !fixpoint_interp1_eq /=.
      destruct Hp as [-> | ->];iFrame "Hinv". }
    { simplify_map_eq. iApply wp_pure_step_later; auto.
      rewrite !insert_insert.

      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].

      (* Needed because IH disallows non-capability values *)
      destruct w' as [ | [p' b' e' a' | ] | ]; cycle 1.
      {
        rewrite /updatePcPerm.
        iAssert (fixpoint interp1 (WCap p' b' e' a')) as "HECap".
        { destruct (decide (r1 = PC)) as [-> | Hne]. by simplify_map_eq.
          rewrite lookup_insert_ne // in H1.
          unshelve iDestruct ("Hreg" $! r1 _ _ H1) as "HPCv"; auto.
        }

        (* Special case for E-values*)
        destruct (decide (p' = E)) as [-> | HneE].
        - iClear "Hinv".
          rewrite fixpoint_interp1_eq; simpl.
          iDestruct ("HECap" with "[$Hmap $Hown]") as "Hcont"; auto.
        - iAssert ([∗ map] k↦y ∈ <[PC:= WCap p' b' e' a']> r, k ↦ᵣ y)%I  with "[Hmap]" as "Hmap".
          { destruct p'; auto. congruence. }
          iNext; iIntros "_".

          iApply ("IH" $! (<[PC:=WCap p' b' e' a']> r) with "[%] [] [Hmap] [$Hown]").
          { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
          { iIntros (ri v Hri Hvs).
            rewrite lookup_insert_ne in Hvs; auto.
              unshelve iSpecialize ("Hreg" $! ri _ _ Hvs); eauto. }
          { rewrite insert_insert. iApply "Hmap". }
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
