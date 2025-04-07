From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_EDeInit.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma edeinit_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (r : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (EDeInit r) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_edeinit with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
    { (* where do we get the resource from? It will be registered in an invariant *)
        admit. }
    iNext. iIntros (lregs' etable' retv) "(%HSpec & Hrmap & Hpca)".
    destruct HSpec as [tidx eid Htidx Hetable' Hincr |HFail].
    + (* Success *)
      apply incrementLPC_Some_inv in Hincr as (p''&b''&e''&a''& v''&? & HPC & Z & Hregs') .
      simplify_map_eq.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply ("IH" $! lregs with "[%] [] [Hrmap] [$Hown]"); eauto.

    + destruct HFail as [HNoValidPc|HOther].
      { iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro]. iNext.
        iIntros "_".
        iApply wp_value; auto. iIntros; discriminate. }
      { iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro]. iNext.
        iIntros "_".
        iApply wp_value; auto. iIntros; discriminate. }
    Admitted.

End fundamental.
