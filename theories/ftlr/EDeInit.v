From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
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
    destruct (is_seal_range (<[PC:=LCap p b e a v]> lregs !! r)) eqn:Hsealrange.

    + (* we have a seal range in the `r` register *)
      (* we need to get the invariant from the LogRel sealrange case *)
      pose proof Hsealrange as Hsealrange'. (* need a copy of this for later.. *)
      destruct (decide (r = PC)). { simplify_map_eq. }
      rewrite lookup_insert_ne in Hsealrange. 2: by symmetry.

      (* By Hsealrange, there is a sealrange (of the form `SealRange (t,t) b e a`) buried somewhere in lregs !! r *)
      (* let's get it out... *)
      unfold is_seal_range in Hsealrange.
      destruct (lregs !! r) eqn:Hr; rewrite Hr in Hsealrange; last congruence.
      destruct l; try congruence. destruct sb; try congruence.
      destruct s as [allowSeal allowUnseal]; try congruence.
      destruct allowSeal, allowUnseal; try congruence.
      (* lregs now points to a sealrange... *)

      (* The sealrange is safe, since all reg values are safe (by Hreg) *)
      iAssert (interp (LSealRange (true, true) f f0 f1)) as "Hsaferange".
      { iApply "Hreg"; eauto. }
      iEval (rewrite fixpoint_interp1_eq) in "Hsaferange".
      iEval (cbn) in "Hsaferange".

      (* Thus we can obtain the safe_to_attest predicate (needed to obtain the ghost resource for the enclave from the invariant) *)
      iDestruct "Hsaferange" as "(_ & _ & Hattest)".
      unfold safe_to_attest.

      rewrite finz_seq_between_cons. 2: solve_addr.
      rewrite big_sepL_cons.
      (* let's get that enclave ghost resource now *)
      iDestruct "Hattest" as "((%tidx & %Htidx & Hinvtidx) & Hattest)".
      iInv (attestN.@ tidx) as ">Henclave" "Hclstidx".

      (* and consider the two options: either this enclave is still "current" or "live", in which case the invariant stores
         an `enclave_cur` resource,
         or the enclave was already deinitialized, and running edeinit will halt the machine (but we still need to close the invariant)
         and give an `enclave_prev` resource back! *)
      iDestruct "Henclave" as "[Henclave|Henclave]".
      - (* the enclave is current, i.e. not yet deinitialized (this is the interesting path) *)

        iDestruct "Henclave" as "(%I & Henclave)".
        iApply (wp_edeinit _ _ _ _ _ _ _ _ _ _ _ true (* is_cur = true *) with "[$Ha Henclave $Hmap]"); eauto.
        { by simplify_map_eq. }
        { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
          apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
        { rewrite Hsealrange'. iFrame. }

        iNext. iIntros (lregs' retv) "(%HSpec & Henclave & Hrmap & Hpca)".
        destruct HSpec as [Hincr |HFail].
        * (* success when enclave_cur *)
          iApply wp_pure_step_later; auto.
          iMod ("Hclstidx" with "[Henclave]").
          { iNext. by iRight. }
          iModIntro.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro].
          iNext. iIntros "_".
          apply incrementLPC_Some_inv in H2 as (p''&b''&e''&a''& v''&? & HPC & Z & Hregs') .
          simplify_map_eq. rewrite insert_insert.

          iApply ("IH" with "[%] [] [Hrmap] [$Hown]"); eauto.
          iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
          { destruct Hp as [HRX | HRW]; by subst p''. }
          { by rewrite PermFlowsToReflexive. }

        * (* failure case when enclave_cur *)
          iApply wp_pure_step_later; auto.
          iMod ("Hclstidx" with "[Henclave]").
          { iNext. by iRight. }
          iModIntro.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro].
          iNext. iIntros "_".
          iApply wp_value. iIntros. discriminate.

      - (* enclave_prev holds, i.e. the enclave was already deinit'ed *)
        iApply (wp_edeinit _ _ _ _ _ _ _ _ _ _ _ false (* is_cur = false *) with "[$Ha Henclave $Hmap]"); eauto.
        { by simplify_map_eq. }
        { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
          apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
        { rewrite Hsealrange'. iFrame. }

        (* now to use IH *)
        iNext. iIntros (lregs' retv) "(%HSpec & Henclave & Hrmap & Hpca)".
        destruct HSpec as [Hincr |HFail].
        * congruence.
        * iApply wp_pure_step_later; auto.
          iMod ("Hclstidx" with "[Henclave]").
          { iNext. by iRight. }
          iModIntro.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro].
          iNext. iIntros "_".
          iApply wp_value. iIntros. discriminate.

    + (* no seal range... *)
      iApply (wp_edeinit with "[$Ha $Hmap]"); eauto.
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      rewrite Hsealrange. done.

      iNext. iIntros (lregs' retv) "(%HSpec & Henclave & Hrmap & Hpca)".
      destruct HSpec as [Hincr |HFail].
      -  (* Success cannot be true! *)
        exfalso. rewrite H1 in Hsealrange.
        simplify_map_eq. solve_addr.
      - (* Fail case *)
        iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro]. iNext.
        iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
        Unshelve. all: eauto.
        exact 0.
        exact 0.
        exact true.
  Qed.

End fundamental.
