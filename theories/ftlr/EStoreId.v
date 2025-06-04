From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_EStoreId.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}
          {contract_enclaves : @CustomEnclavesMap Σ MP}.

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
    iIntros "[Hcontract #Hsystem_inv] #IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    specialize Hsome with rd as Hrd.
    specialize Hsome with rs as Hrs.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_estoreid _ _ _ _ _ _ _ _ _ _ false 0 with "[$Ha $Hmap]"); eauto.
    { destruct Hrd as [wrd Hsomerd]. destruct Hrs as [wrs Hsomers].
      rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
    { by simplify_map_eq. }
    iIntros "!>" (regs' tidx I retv). iDestruct 1 as (HSpec) "(Hrmap & Ha & _ & Henclave)".

    destruct HSpec as [Hincr Hseal | | | | Hincr Hlregs' ]; cycle 1.
    (* failure cases *)
    - (* failure case: increment pc fails *)
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - (* success case *)

      (* get Henclave *)
      destruct (decide (NextIV = NextIV)); last congruence.

      incrementLPC_inv as (p''&b''&e''&a''&v''& ? & HPC & Z & Hregs'); simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]"); [iExists lw; iFrame|iModIntro].
      iNext. iIntros.
      iApply ("IH" with "[%] [] Hrmap [$Hown]").
      { (* full_map lregs' case *)
        intros r.
        rewrite lookup_insert_is_Some.
        destruct (reg_eq_dec rd r); auto; right; split; auto.
        rewrite lookup_insert_is_Some.
        destruct (reg_eq_dec PC r); auto; right; split; auto.
      }
      { (* all registers except PC are safe to share *)
        iIntros (r rlv Hrneq Hlregs').
        destruct (decide (r = rd)).
        - simplify_map_eq. iEval (rewrite fixpoint_interp1_eq). done.
        - rewrite lookup_insert_ne in Hlregs'.
          simplify_map_eq. iApply "Hreg"; eauto. by symmetry. }
      { destruct (decide (rd = PC)).
        + simplify_map_eq.
        + rewrite lookup_insert_ne // in HPC.
          simplify_map_eq.
          iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
          (* { destruct Hp as [HRX | HRW]; by subst p''. } *)
          (* { by rewrite PermFlowsToReflexive. }  *)
      }
  Qed.

End fundamental.
