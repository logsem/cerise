From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_EStoreId.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma estoreid_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (rd rs : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (EStoreId rd rs) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    specialize Hsome with rd as Hrd.
    specialize Hsome with rs as Hrs.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_estoreid with "[$Ha $Hmap]"); eauto.
    { destruct Hrd as [wrd Hsomerd]. destruct Hrs as [wrs Hsomers].
      rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
    { by simplify_map_eq. }
    iIntros "!>" (regs' tidx retv). iDestruct 1 as (HSpec) "(Hrmap & Ha & Hrs & Hpost)".

    destruct HSpec as [Hincr Hseal|Hincr Hlregs']; cycle 1.
    - (* failure case: increment pc fails *)
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.

    - (* success case *)
      incrementLPC_inv as (p''&b''&e''&a''&v''& ? & HPC & Z & Hregs'); simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro].
      iNext. iIntros.
      iApply ("IH" with "[%] [] Hrmap [$Hown]").

      (* destruct (reg_eq_dec rs PC) as [Heq | Hners]. *)
      (* { simplify_map_eq. } *)
      (* rewrite lookup_insert_ne in HPC; auto. *)
      (* destruct (reg_eq_dec rd PC) as [Heq | Hnerd]. *)
      (* { subst rd. *)
      (* rewrite lookup_insert in HPC. *)
      (* iDestruct "Hpost" as "[%I HPC]". *)
      (* Unshelve. apply I. *)
      (* subst HPC. *)
      (* repeat rewrite insert_insert. *)
      (* (* rewrite insert_insert. *) *)

      (* iApply ("IH" with "[%] [] Hrmap [$Hown]"); auto. *)
      + cbn. intros.  by repeat (apply lookup_insert_is_Some'; right).
      + iIntros. iApply "Hreg"; auto.
        iPureIntro.
        destruct (reg_eq_dec r1 rs).
        { subst rs. admit. }
        { destruct (reg_eq_dec r1 rd).
          - subst. rewrite lookup_insert_ne in H1; auto. admit.
          - repeat rewrite lookup_insert_ne in H1; auto. }

      + iModIntro.
        destruct (reg_eq_dec rs PC).
        { simplify_map_eq. }
        { destruct (reg_eq_dec rd PC).
          - (* rd = PC *)
            subst. admit.
          - (* rd ≠ PC *)
            rewrite lookup_insert_ne in HPC. rewrite lookup_insert_ne in HPC; auto.
            rewrite lookup_insert in HPC. inversion HPC.  subst.
        iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
        { destruct Hp as [HRX | HRW]; by subst p''. }
        { by rewrite PermFlowsToReflexive. }
  Admitted.

End fundamental.
