From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_base rules_Jnz.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma jnz_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (r1 r2 : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (Jnz r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv).
    iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ lw' Hsrc Hlw' HincrPC | lw' lregs' Hsrc Hlw' HincrPC | lw' lw'' Hsrc Hdst Hlw' ].
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]");[iExists lw;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    {
    { apply incrementLPC_Some_inv in HincrPC as (p''&b''&e''&a''& v''&? & HPC & Z & Hregs') .
      simplify_map_eq. rewrite insert_insert.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[Ha HP]");[iExists lw;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply ("IH" $! lregs with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto. iModIntro.
      rewrite !fixpoint_interp1_eq /=.
      destruct Hp as [-> | ->];iFrame "Hinv". }
    }
    { simplify_map_eq. iApply wp_pure_step_later; auto.
      rewrite !insert_insert.

      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].

      (* Needed because IH disallows non-capability values *)
      destruct lw'' as [ | [p' b' e' a' v' | ] | ]; cycle 1.
      {
        rewrite /updatePcPerm.
        iAssert (fixpoint interp1 (LCap p' b' e' a' v')) as "HECap".
        { destruct (decide (r1 = PC)) as [-> | Hne]; simplify_map_eq; auto.
          unshelve iDestruct ("Hreg" $! r1 _ _ Hdst) as "HPCv"; auto.
        }

        (* Special case for E-values*)
        destruct (decide (p' = E)) as [-> | HneE].
        - iClear "Hinv".
          rewrite fixpoint_interp1_eq; simpl.
          iDestruct ("HECap" with "[$Hmap $Hown]") as "Hcont"; auto.
        - iAssert ([∗ map] k↦y ∈ <[PC:= LCap p' b' e' a' v']> lregs, k ↦ᵣ y)%I  with "[Hmap]" as "Hmap".
          { destruct p'; auto. congruence. }
          iNext; iIntros "_".

          iApply ("IH" $! (<[PC:=LCap p' b' e' a' v']> lregs) with "[%] [] [Hmap] [$Hown]").
          { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
          { iIntros (ri ? Hri Hvs); simplify_map_eq.
              unshelve iSpecialize ("Hreg" $! ri _ _ Hvs); eauto. }
          { rewrite insert_insert. iApply "Hmap". }
          done.
      }
     (* Non-capability cases *)

      all: iNext; iIntros "_".
      all: iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap] /=";
        [apply lookup_insert|]; simpl.
      all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
        iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ] ; cbn in *; simplify_eq.
      all: repeat iNext; iIntros "HPC /=".
      all: iApply wp_pure_step_later; auto.
      all: iNext; iIntros "_".
      all: iApply wp_value.
      all: iIntros.
      all: discriminate.
     }
Qed.

End fundamental.
