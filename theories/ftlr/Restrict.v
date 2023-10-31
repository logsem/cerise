From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Restrict.
From cap_machine Require Export logrel register_tactics.
From cap_machine Require Export stdpp_extra.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma PermPairFlows_interp_preserved p p' b e a widc :
    not (allows_read_IE p b e a) ->
    p <> E ->
    p <> IE ->
    PermFlowsTo p' p = true →
    (□ ▷ (∀ regs' p' b' e' a' widc',
             full_map regs'
          -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜r ≠ idc⌝ → ⌜regs' !! r = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[idc:=widc']> (<[PC:=WCap p' b' e' a']> regs'))
          -∗ na_own logrel_nais ⊤
          -∗ □ (fixpoint interp1) (WCap p' b' e' a')
          -∗ □ (fixpoint interp1) widc'
          -∗ interp_conf)) -∗
    (fixpoint interp1) widc -∗
    (fixpoint interp1) (WCap p b e a) -∗
    (fixpoint interp1) (WCap p' b e a).
  Proof.
    intros HpnotE HpnotIE Hp'notIE Hp. iIntros "#IH HIDC HA".
    iApply (interp_weakening_perm_bounds with "IH HIDC") ; eauto ; try solve_addr.
  Qed.

  Definition reg_allows_read_IE (regs : Reg) (r : RegName) p b e a :=
    regs !! r = Some (WCap p b e a)
    /\ readAllowed p = true
    ∧ withinBounds b e a = true
    ∧ withinBounds b e (a^+1)%a = true.

  Lemma read_IE_inr_eq {regs dst p b e a p' b' e' a'}:
    reg_allows_read_IE regs dst p b e a →
    read_reg_inr regs dst p' b' e' a' →
    p = p' ∧ b = b' ∧ e = e' ∧ a = a'.
  Proof.
    intros Hrar Hrinr.
    pose (Hrar' := Hrar).
    destruct Hrar' as (Hinr0 & _). rewrite /read_reg_inr Hinr0 in Hrinr. by inversion Hrinr.
  Qed.

  Lemma restrict_case (regs : leibnizO Reg) (p_pc : Perm)
        (b_pc e_pc a_pc : Addr) (widc wpc : Word) (dst : RegName) (r : Z + RegName) (P:D):
    ftlr_instr regs p_pc b_pc e_pc a_pc widc wpc (Restrict dst r) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Hpc_a HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    (* To read out PC's name later, and needed when calling wp_restrict *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p_pc b_pc e_pc a_pc]> (<[idc:=widc]> regs) !! x)) as Hsome'.
    {
      intros.
      destruct (decide (x = PC)) as [Heq|Heq].
      rewrite Heq lookup_insert; unfold is_Some. by eexists.
      destruct (decide (x = idc)) as [Heq'|Heq'].
      rewrite Heq' lookup_insert_ne //= lookup_insert; unfold is_Some. by eexists.
      by rewrite !lookup_insert_ne.
    }

    assert (∃ p b e a, read_reg_inr (<[PC:=WCap p_pc b_pc e_pc a_pc]> (<[idc:=widc]> regs)) dst p b e a)
      as (p & b & e & a & HVdst).
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. rewrite Hsomedst.
      destruct wdst as [|[ p b e a|] | ]; try done.
      by repeat eexists.
    }

    assert (∃ p b e a, read_reg_inr (<[PC:=WCap p_pc b_pc e_pc a_pc]> (<[idc:=widc]> regs)) idc p b e a)
      as (p_idc & b_idc & e_idc & a_idc & HVidc).
    {
      specialize Hsome' with idc as Hidc.
      destruct Hidc as [widc' Hsomeidc].
      unfold read_reg_inr. rewrite Hsomeidc.
      destruct widc' as [|[ p' b' e' a'|] | ]; try done.
      by repeat eexists.
    }

    rewrite /read_reg_inr in HVidc ; simplify_map_eq.
    destruct (decide (reg_allows_read_IE regs dst p b e a)) as [Hallows | Hallows].

    - (* we can restrict to IE *) admit.






    - (* we can't restrict to IE -> the proof will be trivial *)
    destruct (decide (dst = idc)) as [Hdst_idc|Hdst_idc]; simplify_map_eq.
    + (* dst = idc, *)

      iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
        right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
      }

      iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
      destruct HSpec as [ * Hdst He Hie Hz Hfl HincrPC | * Hdst Hz Hfl HincrPC | ].
      { apply incrementPC_Some_inv in HincrPC as (p'&b' &e' &a' & ? & HPC & Z & Hregs') .

        assert (a' = a_pc ∧ b' = b_pc ∧ e' = e_pc) as (-> & -> & ->)
            by (by simplify_map_eq).
        simplify_map_eq.
        rewrite insert_commute //= insert_insert //= insert_commute //=
          insert_insert.
        rewrite /read_reg_inr in HVdst ; simplify_map_eq.

        iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[HP Ha]");[iExists wpc;iFrame|iModIntro].
        iNext; iIntros "_".

        set (regs' := <[PC:=WCap p' b_pc e_pc x]>
                           (<[idc:=WCap (decodePerm n) b e a]> regs)).
        iApply ("IH" $! regs' _ _ _ _ with "[%] [] [Hmap] [$Hown]"); simplify_eq.
        { intros. admit. }
        { iIntros (ri v Hri Hri' Hvs).
          destruct (decide (ri = idc)) ; simplify_map_eq.
          repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto.
        }
        { subst regs'.
          rewrite insert_insert (insert_commute _ idc PC) //= insert_insert. iFrame "Hmap". }
        iModIntro; simplify_map_eq.
        iApply (interp_weakening_lea with "IH Hinv_pc"); auto
        ; try solve_addr.
        { destruct Hp; by subst p'. }
        { destruct Hp; by subst p'. }
        { rewrite /reg_allows_read_IE in Hallows.
          iDestruct (interp_weakening_perm_bounds with "IH Hinv_idc") as "Haa"
          ; eauto ; try solve_addr.
          iApply (interp_weakening_perm_bounds with "IH Hinv_idc"); auto.

        }
      }

  Qed.

End fundamental.
