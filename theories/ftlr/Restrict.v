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

  Definition reg_allows_read_IE (regs : Reg) (r : RegName) p b e a :=
    regs !! r = Some (WCap p b e a)
    /\ readAllowed p = true
    ∧ withinBounds b e a = true
    ∧ withinBounds b e (a^+1)%a = true.

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately *)
  Definition region_open_resources (Pa Pa' : D) (pc_a : Addr) (w1 w2 : Word) (a : Addr) (f:bool) : iProp Σ :=
    ((if f then ▷ Pa w1 else Pa w1) ∗ read_cond Pa interp ∗
       (if f then ▷ Pa' w2 else Pa' w2) ∗ read_cond Pa' interp
       (* Close the invariant for a *)
       ∗ ((▷ ∃ w1, a ↦ₐ w1 ∗ Pa w1) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a,⊤ ∖ ↑logN.@pc_a}=∗ emp)
       (* Close the invariant for (a+1) *)
       ∗ ((▷ ∃ w2, (a ^+ 1)%a ↦ₐ w2  ∗ Pa' w2) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@(a ^+ 1)%a,
           ⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a}=∗ emp)
    )%I.

  Definition allow_restrict_res
    (regs : leibnizO Reg) (dst : RegName)
    (pc_a : Addr) (p : Perm)
    (b e a : Addr) (Pa Pa' : D)
    :=
    (⌜read_reg_inr regs dst p b e a⌝ ∗
    if decide (reg_allows_read_IE regs dst p b e a ∧ a ≠ pc_a ∧ (a^+1)%a ≠ pc_a)
    then |={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@(a^+1)%a}=>
           ∃ w1 w2, a ↦ₐ w1
                      ∗ (a^+1)%a ↦ₐ w2
                      ∗ region_open_resources Pa Pa' pc_a w1 w2 a true
                      ∗ ▷ interp w1
                      ∗ ▷ interp w2
     else True)%I.

  Lemma create_restrict_res:
    ∀ (regs : leibnizO Reg) (dst : RegName)
      (p_pc : Perm) (b_pc e_pc a_pc : Addr)
      (p : Perm) (b e a : Addr),
      read_reg_inr (<[PC:=WCap p_pc b_pc e_pc a_pc]> regs) dst p b e a
      → (∀ (r : RegName) (w : Word),
            ⌜r ≠ PC⌝ → ⌜r ≠ idc⌝ → ⌜regs !! r = Some w⌝ → (fixpoint interp1) w)
        -∗ ∃ Pa Pa', allow_restrict_res (<[PC:=WCap p_pc b_pc e_pc a_pc]> regs) dst a_pc p b e a Pa Pa'.
  Proof.
    intros regs dst p_pc b_pc e_pc a_pc p b e a HVdst.
    iIntros "Hreg". rewrite /allow_restrict_res.
    iFrame "%".
    case_decide as Hdec; [|iExists (λne _, True%I), (λne _, True%I);done].
    destruct Hdec as (Hallows & Haeq &Ha'eq).
    destruct Hallows as (Hrinr & Hra & Hwb & Hwb').

    apply andb_prop in Hwb as [Hle Hge].
    apply andb_prop in Hwb' as [Hle' Hge'].
    assert (a <> a^+ 1)%a as Ha_a' by solve_addr.

    (* We prove that dst could not have been the PC, since the PC can't be an IE-cap *)
    assert (dst ≠ PC) as Hdst_pc.
    { refine (addr_ne_reg_ne Hrinr _ Haeq); by rewrite lookup_insert. }
    rewrite lookup_insert_ne in Hrinr; last by congruence.
    destruct (decide (dst = idc)) as [? | Hdst_idc]; simplify_map_eq.
    - (* dst = idc *)
      admit. (* By IH, I know already know V(widc) ? *)
    - (* dst ≠ idc *)
      iDestruct ("Hreg" $! dst _ Hdst_pc Hdst_idc Hrinr) as "#Hvdst".

      iDestruct (read_allowed_inv a with "Hvdst") as (Pa) "[Hinv_a [Hconds_a _] ]"; auto;
        first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).

      iDestruct (read_allowed_inv (a^+1)%a with "Hvdst") as (Pa') "[Hinv_a' [Hconds_a' _] ]"; auto;
        first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
      iExists Pa, Pa'.

      (* TODO is there a better way to open multiple invariant at once ? *)
      iMod (inv_acc (⊤ ∖ ↑logN.@a_pc) with "Hinv_a") as "[Hrefa Hcls]";[solve_ndisj|].
      iMod (inv_acc (⊤ ∖ ↑logN.@a_pc ∖ ↑logN.@a) with "Hinv_a'") as "[Hrefa' Hcls']";[solve_ndisj|].
      iDestruct "Hrefa" as (w1) "[>Ha HPa]".
      iDestruct "Hrefa'" as (w2) "[>Ha' HPa']".
      iExists w1, w2.
      iAssert (▷ interp w1)%I as "#Hw1".
      { iNext. iApply "Hconds_a". iFrame. }
      iAssert (▷ interp w2)%I as "#Hw2".
      { iNext. iApply "Hconds_a'". iFrame. }
      rewrite /interp_ref_inv /=. iFrame "∗ #". done.
  Admitted.

  Definition allow_read_IE_mem
    (mem : Mem) (regs : Reg) (dst : RegName)
    (pc_a : Addr) (pc_w : Word)
    (p : Perm) (b e a : Addr) (Pa Pa':D) (f:bool): iPropI Σ :=
    (⌜read_reg_inr regs dst p b e a⌝ ∗
       if decide (reg_allows_read_IE regs dst p b e a ∧ a ≠ pc_a ∧ (a^+1)%a ≠ pc_a)
       then ∃ (w1 w2 : Word),
           ⌜mem = <[(a^+1)%a := w2]> (<[a := w1]> ∅)⌝
           ∗ (region_open_resources Pa Pa' pc_a w1 w2 a f)
           ∗ (if f then ▷ interp w1 else interp w1)
           ∗ (if f then ▷ interp w2 else interp w2)
       else  ⌜mem = ∅⌝)%I.

   (* TODO move *)
   Lemma memMap_resource_3ne (a1 a2 a3 : Addr) (w1 w2 w3 : Word)  :
    a1 ≠ a2 →
    a1 ≠ a3 →
    a2 ≠ a3 →
    ([∗ map] a↦w ∈ <[a1:=w1]> (<[a2:=w2]> (<[a3:=w3]> ∅)),
      a ↦ₐ w)%I
      ⊣⊢ a1 ↦ₐ w1 ∗ a2 ↦ₐ w2 ∗ a3 ↦ₐ w3.
  Proof.
    intros.
    rewrite big_sepM_delete; last by apply lookup_insert.
  Admitted.

  Lemma restrict_res_implies_mem_map:
    ∀ (regs : leibnizO Reg) (dst : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr)
      (Pa Pa' : D),
      allow_restrict_res regs dst pc_a p b e a Pa Pa'
      -∗ pc_a ↦ₐ pc_w
      ={⊤ ∖ ↑logN.@pc_a,
        if decide (reg_allows_read_IE regs dst p b e a ∧ a ≠ pc_a ∧ (a^+1)%a ≠ pc_a)
        then ⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@(a ^+ 1)%a
        else ⊤ ∖ ↑logN.@pc_a}=∗
        ∃ mem : Mem,
          allow_read_IE_mem mem regs dst pc_a pc_w p b e a Pa Pa' true
            ∗ ▷ (([∗ map] a0↦w ∈ mem, a0 ↦ₐ w) ∗ pc_a ↦ₐ pc_w).
  Proof.
    intros regs dst pc_a pc_w p b e a Pa Pa'.
    iIntros "HRestrictRes Hpc_a".
    iDestruct "HRestrictRes" as "[% HRestrictRes]".
    case_decide as Hdec. destruct Hdec as (Hallows & Haeq & Ha'eq).
    - pose(Hallows' := Hallows).
      destruct Hallows' as (Hrinr & Hra & Hwb & Hwb').
      assert (a <> a^+ 1)%a as Ha_a' by admit.
      iMod "HRestrictRes" as (w1 w2) "(Ha & Ha' & HRestrictRes & #Hinterp_w1 & #Hinterp_w2)".
      iExists _.
      iSplitL "HRestrictRes".
      + iSplitR; first auto.
        case_decide as Hdec.
        iExists w1, w2. iSplitR; auto.
        exfalso; apply Hdec; auto.
      + iModIntro; iNext. iFrame.
        erewrite memMap_resource_2ne; auto ; iFrame.
  Admitted.

  Definition allow_read_IE_map_or_true (mem : Mem) (regs : Reg) (r : RegName) :=
    ∃ p b e a,
      read_reg_inr regs r p b e a ∧
        if decide (reg_allows_read_IE regs r p b e a) then
          ∃ w1 w2, mem !! a = Some w1 /\ mem !! (a^+1)%a = Some w2
        else True.

  Lemma mem_map_implies_pure_conds:
    ∀ (mem : Mem) (regs : leibnizO Reg)
      (pc_a : Addr) (pc_w : Word)
      (dst : RegName) (p : Perm) (b e a : Addr) (Pa Pa': D) (f : bool),
        allow_read_IE_mem mem regs dst pc_a pc_w p b e a Pa Pa' f
        -∗ ⌜mem !! pc_a = Some pc_w⌝
          ∗ ⌜allow_read_IE_map_or_true mem regs dst⌝.
  Proof.
  Admitted.

  Lemma allow_read_IE_mem_later:
    ∀ (mem : Mem) (regs : Reg) (dst : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr) (Pa Pa':D),
      allow_read_IE_mem mem regs dst pc_a pc_w p b e a Pa Pa' true
      -∗ ▷ allow_read_IE_mem mem regs dst pc_a pc_w p b e a Pa Pa' false.
  Proof.
    iIntros (mem regs dst pc_a pc_w p b e a Pa Pa' ) "HRestrictMem".
  Admitted.

  Instance if_Persistent regs dst pc_a p b e a w1 w2 :
    Persistent (if decide (reg_allows_read_IE regs dst p b e a ∧ a ≠ pc_a ∧ (a ^+ 1)%a ≠ pc_a) then
                  interp w1 ∗ interp w2 else emp)%I.
  Proof. intros. destruct (decide (reg_allows_read_IE regs dst p b e a ∧ a ≠ pc_a ∧ (a ^+ 1)%a ≠ pc_a));apply _. Qed.


   Lemma mem_map_recover_res:
    ∀ (mem : Mem) (regs : leibnizO Reg)
      (pc_a : Addr) (pc_w : Word) (dst : RegName)
      (p : Perm) (b e a : Addr) (w1 w2 : Word) (Pa Pa' : D),
      mem !! a = Some w1
      -> mem !! (a ^+1)%a = Some w2
      -> reg_allows_read_IE regs dst p b e a
      → allow_read_IE_mem mem regs dst pc_a pc_w p b e a Pa Pa' false
        -∗ ([∗ map] a'↦w' ∈ mem, a' ↦ₐ w')
        ={(if decide (reg_allows_read_IE regs dst p b e a ∧ a ≠ pc_a ∧ (a ^+ 1)%a ≠ pc_a)
          then ⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@(a ^+ 1)%a
          else ⊤ ∖ ↑logN.@pc_a),⊤ ∖ ↑logN.@pc_a}=∗
          a ↦ₐ w1 ∗ (a ^+ 1)%a ↦ₐ w2 ∗
          if decide (reg_allows_read_IE regs dst p b e a ∧ a ≠ pc_a ∧ (a ^+ 1)%a ≠ pc_a)
          then interp w1 ∗ interp w2
          else emp.
  Proof.
  Admitted.

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
    assert(∀ x : RegName, is_Some (<[PC:=WCap p_pc b_pc e_pc a_pc]> regs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)) as [Heq|Heq].
      rewrite Heq lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    assert (∃ p b e a, read_reg_inr (<[PC:=WCap p_pc b_pc e_pc a_pc]> regs) dst p b e a)
      as (p & b & e & a & HVdst).
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. rewrite Hsomedst.
      destruct wdst as [|[ p b e a|] | ]; try done.
      by repeat eexists.
    }


    destruct (decide (reg_allows_read_IE regs dst p b e a)) as [Hallows | Hallows].

    - (* we can restrict to IE *)
    - (* we can't restrict to IE -> the proof will be trivial *)


    (* Step 1: open the region, if necessary,
       and store all the resources obtained from the region
       in allow_restrict_res *)
    iDestruct (create_restrict_res with "Hreg") as (Pa Pa') "HRestrictRes"; eauto.
    (* NOTE "HRestrictRes" describes the resources that we _can_ obtain:
       - if the restricted capability can read `a` and `a+1`, then we can open the
       invariant (which open the masks) and we can derive the points-to predicate.
       - the restricted capability cannot read `a` and `a+1`, then we don't need to
       open the invariant, because proving the LR for IE is trivial *)

    (* Step2: derive the concrete map of memory we need,
       and any spatial predicates holding over it *)
    iMod (restrict_res_implies_mem_map with "HRestrictRes Hpc_a")
      as (mem) "[HRestrictMem >[Hmem Hpc_a]]".
    (* NOTE "HRestrictRes" describes the resources that we actually _own_.
       It is a conditional over the reg_allows_read_IE, describes whether we
       opened the invariant or not. *)

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HRestrictMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_restrict *)
    iDestruct (allow_read_IE_mem_later with "HRestrictMem") as "HRestrictMem"; auto.

    iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw".

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
    destruct HSpec as [ * Hdst HnE HnIE Hz Hfl HincrPC | * Hdst Hz Hfl HincrPC | ].
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (a'' = a_pc ∧ b'' = b_pc ∧ e'' = e_pc) as (-> & -> & ->).
      { destruct (decide (PC = dst)) ; simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.

      rewrite /allow_read_IE_map_or_true in HLoadAP.
      destruct HLoadAP as (p' & b'& e'& a'& Hread & Hmem).

      destruct (decide (reg_allows_read_IE (<[PC:=WCap p_pc b_pc e_pc a_pc]> regs) dst p b e a))
      as [Hdec|Hdec].
      +
        (* destruct Hdec as (Hallows & Haeq & Ha'eq). *)
        eapply read_IE_inr_eq in Hread; eauto.
        destruct Hread as (<- & <- & <- & <-).
        case_decide as Hcontra ; [|contradiction]; clear Hcontra.
        destruct Hmem as (w1 & w2 & Hw1 & Hw2).

        iMod (mem_map_recover_res with "HRestrictMem Hmem") as "(Ha & Ha' & #Hinterp)"
        ;[eauto|eauto|auto|iModIntro].
        (* destruct Hallows as (Hrinr & Hra & Hwb & Hwb'). *)

        iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
        (* Exceptional success case: we do not apply the induction hypothesis in case
           we have a faulty PC *)
        destruct (decide (p'' = RX ∨ p'' = RWX)).
        2 : {
          assert (p'' ≠ RX ∧ p'' ≠ RWX). split; by auto.
          iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
          { subst. by rewrite lookup_insert. }
          iNext; iIntros "_".
          iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
          iApply wp_pure_step_later; auto.
          iNext; iIntros "_".
          iApply wp_value.
          iIntros (a1); inversion a1.
        }


        iAssert (
            ∀ (r0 : RegName) (v : leibnizO Word),
              ⌜r0 ≠ PC⌝ → ⌜r0 ≠ idc⌝ → ⌜regs' !! r0 = Some v⌝ → fixpoint interp1 v
          )%I with "[Hmap Ha Ha']" as "Hinterp_reg".
        { iIntros (ri v Hri Hri' Hvs).
          subst regs'.
          rewrite lookup_insert_ne in Hvs; auto.
          destruct (decide (ri = dst)).
          { simplify_map_eq.
            unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
            destruct (decide ((decodePerm n) = IE)) as [ Heq | Hneq]; simplify_eq ; cycle 1.
            { iApply (interp_weakening with "IH Hreg") ; auto; solve_addr. }
            rewrite Heq; rewrite Heq in Hfl; clear Heq.
            simplify_map_eq.

            admit. (* TODO lemma in case of IE *)

          }
          { repeat (rewrite lookup_insert_ne in Hvs); auto.
            iApply "Hreg"; auto. } }

        }

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
            rewrite /allow_restrict_res.
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
