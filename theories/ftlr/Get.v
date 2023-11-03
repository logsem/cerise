From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Export ftlr_base.
From cap_machine.rules Require Export rules_Get rules_base.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.
  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma get_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst r0 : RegName) (ins: instr) (P:D) :
    is_Get ins dst r0 →
    ftlr_instr r p b e a widc w ins P.
  Proof.
    intros Hinstr Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].
    rewrite <- Hi in Hinstr. clear Hi.
    iApply (wp_Get with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right.
      destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      iIntros "_".
      simplify_map_eq.
      destruct (decide (dst = idc)) ; subst.
      + (* dst = idc *)
        simplify_map_eq.
        (* TODO better/cleaner way to do this ? *)

        rewrite (_:
                  <[PC:=WCap x x0 x1 x3]>
                    (<[idc:=WInt z]> (<[PC:=WCap x x0 x1 x2]> (<[idc:=widc]> r))) =
                    (<[idc:=WInt z]> (<[PC:=WCap x x0 x1 x3]>
                                        (<[idc:=WInt z]> (<[idc:=widc]> (<[PC:=WCap x x0 x1 x2]> r)))))
                ).
        2: {
          repeat (try
                    rewrite insert_insert ||
                    (rewrite (insert_commute _ idc PC); auto));
          reflexivity.
        }

        iApply ("IH" $! (<[idc := _]> (<[idc := _]> (<[PC := _]> r))) with "[%] [] [Hmap] [$Hown]");
          try iClear "IH" ; eauto.
        { intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right). }
        iIntros (ri v Hri Hri' Hsv).
        destruct (decide (ri = idc)); simplify_map_eq.
        { by iApply "Hreg". }
        1,2: rewrite !fixpoint_interp1_eq //=. destruct Hp as [-> | ->] ;iFrame "Hinv_pc".

      + (* dst <> idc *)
        rewrite (_:
                  <[PC:=WCap x x0 x1 x3]>
                    (<[dst:=WInt z]> (<[PC:=WCap x x0 x1 x2]> (<[idc:=widc]> r))) =
                    (<[idc:=widc]> (<[PC:=WCap x x0 x1 x3]>
                                      (<[dst:=WInt z]> (<[idc:=widc]> (<[PC:=WCap x x0 x1 x2]> r)))))
                ).
        2: { rewrite (insert_commute _ idc PC); auto.
             rewrite (insert_commute _ idc dst); auto.
             rewrite (insert_insert).
             rewrite (insert_commute _ idc PC); auto.
        }

        iApply ("IH" $! (<[dst := _]> (<[idc := _]> (<[PC := _]> r))) with "[%] [] [Hmap] [$Hown]");
          try iClear "IH" ; eauto.
        { intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right). }
        iIntros (ri v Hri Hri' Hsv).
        destruct (decide (ri = dst)); simplify_map_eq.
        { repeat rewrite fixpoint_interp1_eq; auto. }
        { by iApply "Hreg". }
        rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->] ;iFrame "Hinv_pc". }
  Qed.

End fundamental.
