From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_EDeInit.

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

  Lemma edeinit_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (r : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (EDeInit r) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "[Hcontract #Hsystem_inv] #IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
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
      set (tidx := tid_of_otype f).
      iDestruct "Hattest" as "(Hinvtidx & Hattest)".
      iInv (attestN.@ tidx) as ">Henclave" "Hclstidx".

      (* and consider the two options: either this enclave is still "current" or "live", in which case the invariant stores
         an `enclave_cur` resource,
         or the enclave was already deinitialized, and running edeinit will halt the machine (but we still need to close the invariant)
         and give an `enclave_prev` resource back! *)
      iDestruct "Henclave" as "[Henclave|Henclave]".
      - (* the enclave is current, i.e. not yet deinitialized (this is the interesting path) *)

        iDestruct "Henclave" as "(%I & Henclave)".
        iApply (wp_edeinit _ _ _ _ _ _ _ _ _ _ (Some tidx) true (* is_cur = true *) with "[$Ha Henclave $Hmap]"); eauto.
        { by simplify_map_eq. }
        { by simplify_map_eq. }
        { intros σb σb2 σa Hσb2 Hlsr. inversion Hlsr. now subst. }

        iNext. iIntros (lregs' retv) "(%HSpec & Henclave & Hrmap & Hpca)".
        destruct HSpec as [Hincr |HFail].
        * (* success when enclave_cur *)
          iApply wp_pure_step_later; auto.
          iMod ("Hclstidx" with "[Henclave]").
          { iNext. by iRight. }
          iModIntro.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro].
          iNext. iIntros "_".
          apply incrementLPC_Some_inv in H1 as (p''&b''&e''&a''& v''&? & HPC & Z & Hregs') .
          simplify_map_eq. rewrite insert_insert.

          iApply ("IH" with "[%] [] [Hrmap] [$Hown]"); eauto.
          iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
          { destruct Hp as [HRX | HRW]; by subst p''. }
          { by rewrite PermFlowsToReflexive. }

        * (* failure case when enclave_cur *)
          iApply wp_pure_step_later; auto.
          iMod ("Hclstidx" with "[Henclave]").
          { iNext. iLeft. by iExists _. }
          iModIntro.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro].
          iNext. iIntros "_".
          iApply wp_value. iIntros. discriminate.

      - (* enclave_prev holds, i.e. the enclave was already deinit'ed *)
        iApply (wp_edeinit _ _ _ _ _ _ _ _ _ _ (Some tidx) false (* is_cur = false *) 0 with "[$Ha Henclave $Hmap]"); eauto.
        { by simplify_map_eq. }
        { by simplify_map_eq. }
        { intros σb σb2 σa Hσb2 Heq. inversion Heq. now subst.  }

        (* now to use IH *)
        iNext. iIntros (lregs' retv) "(%HSpec & Henclave & Hrmap & Hpca)".
        destruct HSpec as [Hincr |HFail].
        * iApply wp_pure_step_later; auto.
          iMod ("Hclstidx" with "[Henclave]").
          { iNext. by iRight. }
          iModIntro.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro].
          iNext. iIntros "_".
          unfold incrementLPC in H1. rewrite lookup_insert in H1. destruct (a + 1)%a; inversion H1.
          rewrite insert_insert in H4.
          iApply ("IH" $! lregs' p b e f2 v with "[%] [] [Hrmap] [$Hown]"); eauto.
          { intros. subst lregs'.
            eapply lookup_insert_is_Some.
            now destruct (decide (PC = x)); [left|right].
          }
          { iIntros (r1 lv Hr1pc Hr1).
            iApply ("Hreg" $! _ _ Hr1pc with "[%]").
            subst lregs'.
            now rewrite lookup_insert_ne in Hr1.
          }
          { subst lregs'.
            now rewrite !insert_insert.
          }
          { iModIntro.
            iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
            { destruct Hp as [HRX | HRW]; by subst p. }
            { by rewrite PermFlowsToReflexive. }
          }
        * iApply wp_pure_step_later; auto.
          iMod ("Hclstidx" with "[Henclave]").
          { iNext. by iRight. }
          iModIntro.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro].
          iNext. iIntros "_".
          iApply wp_value. iIntros. discriminate.

    + (* no seal range... *)
      destruct (decide (r = PC)).
      * subst r.
        iApply (wp_edeinit _ _ _ _ _ _ _ _ _ _ None false (* is_cur = false *) 0 with "[$Ha $Hmap]"); eauto.
        { by simplify_map_eq. }
        { eapply lookup_insert. }
        { intros σb σb2 σe Hσb2 Heq. discriminate. }

        iNext. iIntros (lregs' retv) "(%HSpec & Henclave & Hrmap & Hpca)".
        destruct HSpec as [Hincr |HFail].
        --  (* Success cannot be true! *)
           discriminate.
        -- (* Fail case *)
          iApply wp_pure_step_later; auto.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro]. iNext.
          iIntros "_".
          iApply wp_value; auto. iIntros; discriminate.
      * specialize (Hsome r).
        destruct (lregs !! r) eqn:Hlregsr; last by inversion Hsome.
        iApply (wp_edeinit _ _ _ _ _ _ _ _ _ _ None false (* is_cur = false *) 0 with "[$Ha $Hmap]"); eauto.
        { by simplify_map_eq. }
        { by simplify_map_eq. }
        { intros σb σb2 σe Hσb2 Heq.
          rewrite lookup_insert_ne in Hsealrange; last eauto.
          rewrite Hlregsr in Hsealrange.
          rewrite Heq in Hsealrange.
          cbn in Hsealrange.
          rewrite Hσb2 in Hsealrange.
          rewrite Z.eqb_refl in Hsealrange.
          discriminate.
        }

        iNext. iIntros (lregs' retv) "(%HSpec & Henclave & Hrmap & Hpca)".
        destruct HSpec as [Hincr |HFail].
        --  (* Success cannot be true! *)
           discriminate.
        -- (* Fail case *)
          iApply wp_pure_step_later; auto.
          iMod ("Hcls" with "[Hpca HP]");[iExists lw;iFrame|iModIntro]. iNext.
          iIntros "_".
          iApply wp_value; auto. iIntros; discriminate.
  Qed.

End fundamental.
