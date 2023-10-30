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
    p <> E ->
    p <> IE ->
    p' <> IE ->
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
    iApply (interp_weakening with "IH HIDC") ; eauto ; try solve_addr.
  Qed.

  Definition reg_allows_IE (regs : Reg) (r : RegName) b e a :=
    regs !! r = Some (WCap IE b e a) ∧
    withinBounds b e a = true /\
    withinBounds b e (a^+1)%a = true.

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately *)
  Definition region_open_resources (pc_a : Addr) (w1 w2 : Word) (a : Addr) : iProp Σ :=
    (▷ interp w1 ∗ ▷ interp w2 ∗
       ((▷ ∃ w, a ↦ₐ w ∗ interp w) ∗ (▷ ∃ w, (a^+1)%a ↦ₐ w ∗ interp w)
        ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@(a^+1)%a, ⊤ ∖ ↑logN.@pc_a}=∗ emp)
    )%I.

  (* Description of what the resources are supposed to look like after
     opening the region if we need to, but before closing the region up again *)
  Definition allow_IE_res (r : RegName) (regs : Reg) pc_a p b e a :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
      (if decide (reg_allows_IE regs r b e a ∧ a ≠ pc_a /\ (a^+1)%a ≠ pc_a)
       then |={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@(a^+1)%a}=>
              ∃ w1 w2, a ↦ₐ w1 ∗ (a^+1)%a ↦ₐ w2 ∗ region_open_resources pc_a w1 w2 a
    else True))%I.

  Definition allow_IE_mem (r : RegName) (regs : Reg) pc_a pc_w (mem : Mem) p b e a :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
      (if decide (reg_allows_IE regs r b e a ∧ a ≠ pc_a /\ (a^+1)%a ≠ pc_a)
       then ∃ w1 w2,
           ⌜mem = <[(a^+1)%a:=w2]> (<[a:=w1]> (<[pc_a:=pc_w]> ∅))⌝
                                     ∗ region_open_resources pc_a w1 w2 a
       else ⌜mem = (<[pc_a:=pc_w]> ∅)⌝))%I.

  Lemma indirect_sentry_allowed_inv (b e a: Addr) :
    (b ≤ a ∧ a < e)%Z →
    (b ≤ (a^+1)%a ∧ (a^+1)%a < e)%Z →
    ⊢ (interp (WCap IE b e a) →
       ∃ w1 w2,
         inv (logN .@ a) (a ↦ₐ w1) ∗ inv (logN .@ (a^+1)%a) ((a^+1)%a ↦ₐ w2))%I.
  Proof.
    iIntros ([Ha_b Ha_e] [Ha_b' Ha_e']) "#Hinterp".
    rewrite /interp //= fixpoint_interp1_eq /=; cbn.
    assert (withinBounds b e a) as Hwb. admit.
    assert (withinBounds b e (a^+1)%a) as Hwb'. admit.
  Admitted.

  (* Lemma create_IE_res: *)
  (*   ∀ (regs : leibnizO Reg) (p : Perm) (b e a : Addr) *)
  (*     (r : RegName) (b0 e0 a0 : Addr), *)
  (*     r <> idc (* TODO *) *)
  (*     -> read_reg_inr (<[PC:=WCap p b e a]> regs) r IE b0 e0 a0 *)
  (*     → (∀ (r' : RegName) v, ⌜r' ≠ PC⌝ → ⌜r' ≠ idc⌝ → ⌜regs !! r' = Some v⌝ → (fixpoint interp1) v) *)
  (*         -∗ allow_IE_res r (<[PC:=WCap p b e a]> regs) a IE b0 e0 a0. *)
  (* Proof. *)
  (*   intros regs p b e a r b0 e0 a0 Hr_idc HVr. *)
  (*   iIntros "#Hreg". *)
  (*   iFrame "%". *)
  (*   case_decide as Hallows. *)
  (*   - destruct Hallows as ((Hrinr & Hwb & Hwb') & Haeq & Ha'eq). *)
  (*     apply andb_prop in Hwb as [Hle Hge]. *)
  (*     apply andb_prop in Hwb' as [Hle' Hge']. *)
  (*     revert Hle Hge; rewrite !Z.leb_le Z.ltb_lt =>Hle Hge. *)
  (*     revert Hle' Hge'; rewrite !Z.leb_le Z.ltb_lt =>Hle' Hge'. *)
  (*     assert (r ≠ PC) as Hr_pc. *)
  (*     { refine (addr_ne_reg_ne Hrinr _ Haeq); by rewrite lookup_insert. } *)
  (*     (* assert (r ≠ idc) as Hr_idc. *) *)
  (*     (* { refine (addr_ne_reg_ne Hrinr _ Haeq). rewrite lookup_insert. } *) *)
  (*   rewrite lookup_insert_ne in Hrinr; last by congruence. *)
  (*   iDestruct ("Hreg" $! r _ Hr_pc Hr_idc Hrinr) as "Hvsrc". *)
  (*   iAssert (∃ w1 w2, inv (logN.@a0) (a0 ↦ₐ w1) *)
  (*                       ∗ inv (logN.@(a0^+1)%a) ((a0^+1)%a ↦ₐ w2))%I *)
  (*     as (w1 w2) "[#Hinva #Hinva']". *)
  (*   { iDestruct (indirect_sentry_allowed_inv with "Hvsrc") as (w1 w2) "[Hw1 Hw2]" *)
  (*     ; auto. } *)
  (*   iExists w1, w2. *)
  (*   iFrame "∗ #". *)
  (*   iMod (inv_acc with "Hinva") as "[>Ha0 Hcls']";[solve_ndisj|]. *)
  (*   iMod (inv_acc with "Hinva'") as "[>Ha0' Hcls'']";[admit|]. *)
  (*   iFrame. *)
  (*   rewrite /region_open_resources. *)
  (*   done. *)
  (*   - done. *)
  (* Qed. *)


  Lemma restrict_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst : RegName) (r0 : Z + RegName) (P:D):
    ftlr_instr r p b e a widc w (Restrict dst r0) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].


    (* TODO we need to do some manipulation in the resources here *)

    iApply (wp_Restrict with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst HnE HnIE Hz Hfl HincrPC | * Hdst Hz Hfl HincrPC | ].
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (a'' = a ∧ b'' = b ∧ e'' = e) as (-> & -> & ->).
      { destruct (decide (PC = dst)) ; simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".

      (* TODO rewrite regs' to match with the induction hypothesis *)
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)).
        { simplify_map_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
          destruct (decide ((decodePerm n) = IE)) as [ Heq | Hneq]; simplify_eq ; cycle 1.
           { iApply (interp_weakening with "IH Hreg") ; auto; solve_addr. }
           rewrite Heq; rewrite Heq in Hfl; clear Heq.
           admit. (* TODO lemma in case of IE *)

        }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
        { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { destruct (reg_eq_dec PC dst) as [Heq | Hne]; simplify_map_eq.
        auto. by rewrite PermFlowsToReflexive. }
    }
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (dst ≠ PC) as Hne.
      { destruct (decide (PC = dst)); last auto. simplify_map_eq; auto. }

      assert (p'' = p ∧ b'' = b ∧ e'' = e ∧ a'' = a) as (-> & -> & -> & ->).
      { simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert_ne in Hdst; auto.
          rewrite lookup_insert in Hvs; inversion Hvs. simplify_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply (interp_weakening_ot with "Hreg"); auto; solve_addr. }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
        { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { by rewrite PermFlowsToReflexive. }
    }
     { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
