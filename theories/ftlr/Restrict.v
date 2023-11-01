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

  Tactic Notation "iFailCase" constr(wpc) constr(hcls) "with" constr(hcls_res) :=
    iApply wp_pure_step_later; auto;
    iMod (hcls with hcls_res);[iExists wpc;iFrame|iModIntro];
    iNext; iIntros "_";
    iApply wp_value; auto; iIntros; discriminate.


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

    destruct (decide (allows_read_IE p b e a)) as [Hallows | Hallows].

    - (* we can restrict to IE *)
      destruct (decide (dst = idc)) as [Hdst_idc|Hdst_idc]; simplify_map_eq.
      + (* dst = idc *)
        rewrite /read_reg_inr in HVdst.
        rewrite /read_reg_inr in HVidc.
        simplify_map_eq.
        destruct_word widc; simplify_eq.
        { (* widc = WInt z *)
          iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
          { by simplify_map_eq. }
          { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
            apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
            right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
          }
          iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
          destruct HSpec as [ | | ];simplify_map_eq; cycle 1.
          iFailCase wpc "Hcls" with "[HP Hpc_a]".
        }

        { (* widc = WCap *)
          destruct p_idc.
          * (* p_idc = O *)
            iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
            { by simplify_map_eq. }
            { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
              apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
              right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
            }
            iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
            destruct HSpec as [ * Hdst He Hie Hz Hfl HincrPC | | ]; simplify_map_eq; cycle 1.
            iFailCase wpc "Hcls" with "[HP Hpc_a]".
            { (* Success *)
              apply incrementPC_Some_inv in HincrPC as (p'&b' &e' &a' & ? & HPC & Z & Hregs') .

              assert (a' = a_pc ∧ b' = b_pc ∧ e' = e_pc) as (-> & -> & ->)
                  by (by simplify_map_eq).
              simplify_map_eq.
              rewrite insert_commute //= insert_insert //= insert_commute //=
                insert_insert.

              iApply wp_pure_step_later; auto.
              iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
              iNext; iIntros "_".

              set (regs' := <[PC:=WCap p' b_pc e_pc x]>
                              (<[idc:=WCap (decodePerm n) b e a]> regs)).
              iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs' ; simplify_map_eq.
              { cbn. intros. admit. }
              { iIntros (ri v Hri Hri' Hvs).
                destruct (decide (ri = idc)) ; simplify_map_eq.
                repeat (rewrite lookup_insert_ne in Hvs); auto.
                iApply "Hreg"; auto.
              }
              { rewrite insert_insert (insert_commute _ idc PC) //= insert_insert. iFrame "Hmap". }
              iModIntro; simplify_map_eq.
              iApply (interp_weakening_lea with "IH Hinv_pc"); auto
              ; try solve_addr.
              { destruct Hp; by subst p'. }
              { destruct Hp; by subst p'. }
              { iModIntro. destruct (decodePerm n); done. }
            }
          * (* p_idc = RO *)
            admit.
          * (* p_idc = RW *)
            admit.
          * (* p_idc = RX *)
            admit.
          * (* p_idc = E *)
            iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
            { by simplify_map_eq. }
            { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
              apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
              right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
            }
            iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
            destruct HSpec as [ | | ]; simplify_map_eq; iFailCase wpc "Hcls" with "[HP Hpc_a]".
          * (* p_idc = IE *)
            iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
            { by simplify_map_eq. }
            { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
              apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
              right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
            }
            iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
            destruct HSpec as [ | | ]; simplify_map_eq; iFailCase wpc "Hcls" with "[HP Hpc_a]".
          * (* p_idc = RWX *)

            destruct Hallows as (Hra & Hwb & Hwb').
            apply andb_prop in Hwb as [Hle Hge].
            apply andb_prop in Hwb' as [Hle' Hge'].
            assert (a_idc <> a_idc^+ 1)%a as Ha_a' by solve_addr.

            iDestruct (read_allowed_inv a_idc with "Hinv_idc") as (Pa) "[Hinv_a [Hconds_a _] ]"
            ; auto; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
            iDestruct (read_allowed_inv (a_idc^+1)%a with "Hinv_idc") as (Pa') "[Hinv_a' [Hconds_a' _] ]"
            ; auto; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).

            destruct (decide (a_idc = a_pc));
            destruct (decide ((a_idc ^+ 1)%a = a_pc)); simplify_eq.
            ** (* a_idc = a_pc, a_pc ≠ a_idc+1 *) admit.
            ** (* a_idc ≠ a_pc, a_pc = a_idc+1 *) admit.
            ** (* a_idc ≠ a_pc, a_pc ≠ a_idc+1 *)

              (* Derive the ressources for idc_a and idc_a' *)
              iMod (inv_acc (⊤ ∖ ↑logN.@a_pc) with "Hinv_a") as "[Hrefa Hcls']";[solve_ndisj|].
              iMod (inv_acc (⊤ ∖ ↑logN.@a_pc ∖ ↑logN.@(a_idc)) with "Hinv_a'") as "[Hrefa' Hcls'']"
              ;[solve_ndisj|].

              (* Apply the rule *)
              iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
              { by simplify_map_eq. }
              { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
                apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
                right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
              }

              iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
              destruct HSpec as [ * Hdst He Hie Hz Hfl HincrPC | | ];simplify_map_eq ; cycle 1.
              { (* Failure *)
                iMod ("Hcls''" with "Hrefa'") as "_"; iModIntro.
                iMod ("Hcls'" with "Hrefa") as "_"; iModIntro.
                iFailCase wpc "Hcls" with "[HP Hpc_a]".
              }
              { (* Success *)

                apply incrementPC_Some_inv in HincrPC as (p'&b' &e' &a' & ? & HPC & Z & Hregs') .

                assert (a' = a_pc ∧ b' = b_pc ∧ e' = e_pc) as (-> & -> & ->)
                    by (by simplify_map_eq).
                simplify_map_eq.
                rewrite insert_commute //= insert_insert //= insert_commute //= insert_insert.

                iDestruct "Hrefa" as (w1) "[Ha HPa]".
                iDestruct "Hrefa'" as (w2) "[Ha' HPa']".

                iAssert (fixpoint interp1 (WCap (decodePerm n1) b e a)) as "#Hinv_idc'".
                {
                  rewrite (fixpoint_interp1_eq (WCap (decodePerm n1) b e a)).
                  destruct (decodePerm n1); cbn in Hfl.
                  - done.
                  - admit.
                  - admit.
                  - admit.
                  - (* E *)
                    iIntros (regs'). iNext; iModIntro.
                    iIntros (w') "#Hw'".
                    iIntros "([Hfull' Hreg'] & Hregs & Hna)".
                    iApply ("IH" with "Hfull' Hreg' Hregs Hna"); auto. iModIntro.
                    admit.
                  - iIntros "[%Hwb %Hwb']".
                    iExists w1, w2.
                    iAssert (interp w1)%I as "#Hw1"; first (by iApply "Hconds_a").
                    iAssert (interp w2)%I as "#Hw2"; first (by iApply "Hconds_a'").
                    iSplit.
                    (* TODO this seems not true,
                       because the existential is in the invariant *)
                    admit.
                    iSplit.
                    (* TODO this seems not true,
                       because the existential is in the invariant *)
                    (* NOTE ideas:
                       can we have a LR closed to the one for RO instead ?
                       ie. we enforce an arbitrary property over the content of
                       the addresses [a] and [a+1].
                       cf. read_cond.
                       This arbitrary property could (in practice) be
                       (w1 = ....), (w2 = ....). This way, we can still
                       remember w1 and w2 ?

                       Something interesting btw: because of the LR, a trusted code cannot
                       keep a capability pointing into the content.
                       For instance, if I create (IE, b, e, a) and prove V(IE, b, e, a),
                       I NEED to give up all [b,e), and will never be to overwrite them again.
                       Its the same for the E-cap though, I just never had the thought before.
                     *)
                    admit.
                    iIntros (regs'). iNext; iModIntro.
                    iIntros "([Hfull' Hreg'] & Hregs & Hna)".

                    (* Needed because IH disallows non-capability values *)
                    destruct w1 as [ | [p1 b1 e1 a1 | ] | ]; cycle 1.
                    iApply ("IH" with "Hfull' Hreg' Hregs Hna"); auto.

                    all: rewrite /registers_mapsto; iExtract "Hregs" PC as "HPC".
                    all: iApply (wp_bind (fill [SeqCtx]));
                      iApply (wp_notCorrectPC with "HPC")
                    ; [intros HFalse; inversion HFalse| ].
                    all: repeat iNext; iIntros "HPC /=".
                    all: iApply wp_pure_step_later; auto.
                    all: iNext; iIntros "_".
                    all: iApply wp_value.
                    all: iIntros; discriminate.
                  - admit.
                }

                set (regs' := <[PC:=WCap p' b_pc e_pc x]>
                                (<[idc:=WCap (decodePerm n1) b e a]> regs)).

                iApply wp_pure_step_later; auto.
                iMod ("Hcls''" with "[Ha' HPa']") as "_"; [iNext;iExists _ ; iFrame|]; iModIntro.
                iMod ("Hcls'" with "[Ha HPa]") as "_"; [iNext;iExists _ ; iFrame|]; iModIntro.
                iMod ("Hcls" with "[Hpc_a HP]") as "_"; [iNext;iExists _ ; iFrame|]; iModIntro.
                iNext; iIntros "_".

                iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown] [] []"); subst regs'
                ; simplify_map_eq.
                { intros. admit. }
                { iIntros (ri v Hri Hri' Hvs).
                  destruct (decide (ri = idc)) ; simplify_map_eq.
                  iApply "Hreg"; auto.
                }
                { rewrite insert_insert (insert_commute _ idc PC) //= insert_insert. iFrame "Hmap".}
                {
                  iModIntro.
                  iApply (interp_weakening_lea with "IH Hinv_pc"); auto
                  ; try solve_addr.
                  { destruct Hp; by subst p'. }
                  { destruct Hp; by subst p'. }
                }
                iFrame "#".
              }
        }

        { (* widc = WSealRange *)
          iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
          { by simplify_map_eq. }
          { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
            apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
            right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
          }

          iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
          destruct HSpec as [ | * Hdst Hz Hfl HincrPC | ];simplify_map_eq; cycle 1.
          iFailCase wpc "Hcls" with "[HP Hpc_a]".
          { (* Case Restrict_spec_success_sr *)
            apply incrementPC_Some_inv in HincrPC as (p'&b' &e' &a' & ? & HPC & Z & Hregs') .

            assert (p' = p_pc /\ a' = a_pc ∧ b' = b_pc ∧ e' = e_pc) as (-> & -> & -> & ->)
                by (by simplify_map_eq).

            iApply wp_pure_step_later; auto.
            iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
            iNext; iIntros "_".

            simplify_map_eq.
            rewrite insert_commute //= insert_insert //= insert_commute //= insert_insert.
            rewrite /read_reg_inr in HVdst ; simplify_map_eq.

            set (regs' := <[PC:=WCap p_pc b_pc e_pc x]>
                            (<[idc:=WSealRange (decodeSealPerms n) b0 e0 a0]> regs)).
            iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs' ; simplify_map_eq.
            { cbn. intros. admit. }
            { iIntros (ri v Hri Hri' Hvs).
              destruct (decide (ri = idc)) ; simplify_map_eq.
              iApply "Hreg"; auto.
            }
            { rewrite insert_insert (insert_commute _ idc PC) //= insert_insert. iFrame "Hmap". }
            iModIntro.
            iApply (interp_weakening_lea with "IH Hinv_pc"); auto
            ; try solve_addr.
            { destruct Hp; by subst p_pc. }
            { destruct Hp; by subst p_pc. }
            { rewrite /reg_allows_read_IE in Hallows.
              iModIntro.
              iApply (interp_weakening_ot with "Hinv_idc")
              ; eauto ; try solve_addr.
            }
          }
        }
        { (* widc = Sealed *)
          iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
          { by simplify_map_eq. }
          { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
            apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
            right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
          }
          iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
          destruct HSpec as [ | | ];simplify_map_eq; cycle 2.
          iFailCase wpc "Hcls" with "[HP Hpc_a]".
        }
      + (* dst ≠ idc *)
        (* Similar proof *)
      admit.















    - (* we can't restrict to IE -> the proof will be trivial *)
      destruct (decide (dst = idc)) as [Hdst_idc|Hdst_idc]; simplify_map_eq.
      + (* dst = idc *)

        iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
        { by simplify_map_eq. }
        { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
          apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
          right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
        }

        iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
        destruct HSpec as [ * Hdst He Hie Hz Hfl HincrPC | * Hdst Hz Hfl HincrPC | ]; cycle 2.
        iFailCase wpc "Hcls" with "[HP Hpc_a]".

        { (* Case Restrict_spec_success_cap *)
          apply incrementPC_Some_inv in HincrPC as (p'&b' &e' &a' & ? & HPC & Z & Hregs') .

          assert (a' = a_pc ∧ b' = b_pc ∧ e' = e_pc) as (-> & -> & ->)
              by (by simplify_map_eq).
          simplify_map_eq.
          rewrite insert_commute //= insert_insert //= insert_commute //=
            insert_insert.
          rewrite /read_reg_inr in HVdst ; simplify_map_eq.

          iApply wp_pure_step_later; auto.
          iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
          iNext; iIntros "_".

          set (regs' := <[PC:=WCap p' b_pc e_pc x]>
                          (<[idc:=WCap (decodePerm n) b e a]> regs)).
          iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs' ; simplify_map_eq.
          { cbn. intros. admit. }
          { iIntros (ri v Hri Hri' Hvs).
            destruct (decide (ri = idc)) ; simplify_map_eq.
            repeat (rewrite lookup_insert_ne in Hvs); auto.
            iApply "Hreg"; auto.
          }
          { rewrite insert_insert (insert_commute _ idc PC) //= insert_insert. iFrame "Hmap". }
          iModIntro; simplify_map_eq.
          iApply (interp_weakening_lea with "IH Hinv_pc"); auto
          ; try solve_addr.
          { destruct Hp; by subst p'. }
          { destruct Hp; by subst p'. }
          { rewrite /reg_allows_read_IE in Hallows.
            iModIntro.
            iApply (PermPairFlows_interp_preserved with "IH Hinv_idc")
            ; eauto ; try solve_addr.
          }
        }
        { (* Case Restrict_spec_success_sr *)
          apply incrementPC_Some_inv in HincrPC as (p'&b' &e' &a' & ? & HPC & Z & Hregs') .

          assert (p' = p_pc /\ a' = a_pc ∧ b' = b_pc ∧ e' = e_pc) as (-> & -> & -> & ->)
              by (by simplify_map_eq).

          iApply wp_pure_step_later; auto.
          iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
          iNext; iIntros "_".

          simplify_map_eq.
          rewrite insert_commute //= insert_insert //= insert_commute //= insert_insert.
          rewrite /read_reg_inr in HVdst ; simplify_map_eq.

          set (regs' := <[PC:=WCap p_pc b_pc e_pc x]>
                          (<[idc:=WSealRange (decodeSealPerms n) b0 e0 a0]> regs)).
          iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs' ; simplify_map_eq.
          { cbn. intros. admit. }
          { iIntros (ri v Hri Hri' Hvs).
            destruct (decide (ri = idc)) ; simplify_map_eq.
            iApply "Hreg"; auto.
          }
          { rewrite insert_insert (insert_commute _ idc PC) //= insert_insert. iFrame "Hmap". }
          iModIntro.
          iApply (interp_weakening_lea with "IH Hinv_pc"); auto
          ; try solve_addr.
          { destruct Hp; by subst p_pc. }
          { destruct Hp; by subst p_pc. }
          { rewrite /reg_allows_read_IE in Hallows.
            iModIntro.
            iApply (interp_weakening_ot with "Hinv_idc")
            ; eauto ; try solve_addr.
          }
        }

      + (* dst ≠ idc *)
        admit.
        (* should be a similar proof *)
  Admitted.

End fundamental.
