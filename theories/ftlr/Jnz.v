From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Jnz.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  (* TODO the whole proof strategy is very similar to the one for Jmp.
     Is there a way to factor out both of them ? *)

  (* Mask after the jump, depending on the address of the pc and the address
   of a *)
  Definition allow_jnz_mask (pc_a a : Addr) : coPset
    :=
    if decide (pc_a = a)
    then (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@(a^+1)%a)
    else
      if decide (pc_a = (a^+1)%a)
      then (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a)
      else (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@(a^+1)%a).


  Definition allow_jnz_mask_reg (regs : Reg) (dst src : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr) (wsrc : Word)
    : coPset :=
    if decide (reg_allows_IE_jmp regs dst p b e a
               /\ regs !! src = Some wsrc
               /\ nonZero wsrc = true)
    then allow_jnz_mask pc_a a
    else (⊤ ∖ ↑logN.@pc_a).

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately *)
  Definition region_open_resources2
    (pc_a : Addr) (a : Addr)
    (w1 : Word) (w2 : Word)
    (P1 P2 : D)
    : iProp Σ :=
    ▷ P1 w1 ∗ ▷ P2 w2
       ∗ persistent_cond P1 ∗ persistent_cond P2
       ∗ ((▷ ∃ w1 w2, a ↦ₐ w1 ∗ P1 w1 ∗ (a^+1)%a ↦ₐ w2 ∗ P2 w2)
          ={allow_jnz_mask pc_a a, ⊤ ∖ ↑logN.@pc_a}=∗ emp)%I.

  Definition region_open_resources
    (pc_a : Addr) (a : Addr) (w : Word)
    (P : D)
    : iProp Σ :=
    (▷ P w
       ∗ persistent_cond P
       ∗ ((▷ ∃ w, a ↦ₐ w ∗ P w)
        ={allow_jnz_mask pc_a a, ⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Definition region_open_resources'
    (pc_a : Addr) (a : Addr) (w' : Word)
    (P : D)
    : iProp Σ :=
    (▷ P w'
       ∗ persistent_cond P
       ∗ ((▷ ∃ w', (a^+1)%a ↦ₐ w' ∗ P w')
        ={allow_jnz_mask pc_a a, ⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  (* Description of what the resources are supposed to look like after opening the
     region if we need to, but before closing the region up again*)
  Definition allow_jnz_res (regs : Reg) (dst src : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr) (wsrc : Word)
    (P1 P2 : D): iProp Σ :=
    ( ⌜read_reg_inr regs dst p b e a⌝ ∗
      ⌜regs !! src = Some wsrc⌝ ∗
       if decide (reg_allows_IE_jmp regs dst p b e a
               /\ regs !! src = Some wsrc
               /\ nonZero wsrc = true)
       then
         (∀ w1 w2 regs', ▷ □ (P1 w1 ∗ (P2 w2 ∨ ⌜ is_int w2 ⌝)
                              -∗ (interp_expr_gen interp regs' w1 w2)))
           ∗
           |={⊤ ∖ ↑logN.@pc_a, allow_jnz_mask pc_a a}=>
           (if decide (pc_a = a)
            then ∃ w2, (a^+1)%a ↦ₐ w2 ∗ region_open_resources' pc_a a w2 P2
            else
              if decide (pc_a = (a^+1)%a)
              then ∃ w1, a ↦ₐ w1 ∗ region_open_resources pc_a a w1 P1
              else ∃ w1 w2, a ↦ₐ w1 ∗ (a^+1)%a ↦ₐ w2 ∗ region_open_resources2 pc_a a w1 w2 P1 P2
           )
       else True)%I.

  Lemma create_jnz_res:
    ∀ (regs : leibnizO Reg) (dst src : RegName)
      (pc_p : Perm) (pc_b pc_e pc_a : Addr)
      (widc : Word)
      (p : Perm) (b e a : Addr) (wsrc : Word),
      pc_p <> IE ->
      read_reg_inr (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:= widc]> regs)) dst p b e a ->
      (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:= widc]> regs)) !! src = Some wsrc ->
      (∀ (r' : RegName) (w : Word), ⌜r' ≠ PC⌝ → ⌜r' ≠ idc⌝ → ⌜regs !! r' = Some w⌝ → (fixpoint interp1) w)
      -∗ interp widc
      -∗ ∃ (P1 P2 : D),
           allow_jnz_res (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:=widc]> regs)) dst src pc_a p b
             e a wsrc P1 P2.
  Proof.
    intros regs dst src pc_p pc_b pc_e pc_a widc p b e a wsrc Hpc_p HVr Hsrc.
    iIntros "#Hreg #Hwidc".
    iFrame "%".
    case_decide as Hallows; cycle 1.
    - by iExists (λne _, True%I), (λne _, True%I).
    - rewrite /allow_jnz_mask.
      destruct Hallows as ((Hreg & -> & Hwb & Hwb') & Hsrc' & Hnz).
      assert (a <> (a^+1)%a) by (apply andb_prop in Hwb as [_ Hge]; solve_addr).
      apply Is_true_true_2 in Hwb, Hwb'.
      assert ( withinBounds b e a /\ withinBounds b e (a^+1)%a) as Hwbs by auto.

      assert (dst ≠ PC) as Hneq by (destruct (decide (dst = PC)) ; simplify_map_eq; auto).
      rewrite lookup_insert_ne //= in Hreg.

      (* TODO there are plenty of similar case, find a way to factor out *)

      case_decide as Ha; simplify_eq.
      {
        destruct (decide (dst = idc)) as [|Hneq']; simplify_map_eq.
        + rewrite fixpoint_interp1_eq /=.
          iDestruct ("Hwidc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & Hexec)".
          iExists P1, P2.
          iFrame "#".
          iMod (inv_acc (⊤ ∖ ↑logN.@a) with "Hinv_a'") as "[Hrefinv_a' Hcls_a']";[solve_ndisj|].
          iDestruct "Hrefinv_a'" as (w2) "[>Ha' HPa']".
          iExists w2.
          iFrame "∗ #".
          rewrite /allow_jnz_mask. do 2 (case_decide ; solve_addr).
        + iDestruct ("Hreg" $! dst _ Hneq Hneq' Hreg) as "Hvsrc".
          rewrite (fixpoint_interp1_eq (WCap _ _ _ _)) /=.
          iDestruct ("Hvsrc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & Hexec)".
          iExists P1, P2.
          iFrame "#".
          iMod (inv_acc (⊤ ∖ ↑logN.@a) with "Hinv_a'") as "[Hrefinv_a' Hcls_a']";[solve_ndisj|].
          iDestruct "Hrefinv_a'" as (w2) "[>Ha' HPa']".
          iExists w2.
          iFrame "∗ #".
          rewrite /allow_jnz_mask. do 2 (case_decide ; solve_addr).
      }

      case_decide as Ha'; simplify_eq.
      {
        destruct (decide (dst = idc)) as [|Hneq']; simplify_map_eq.
        + rewrite fixpoint_interp1_eq /=.
          iDestruct ("Hwidc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & Hexec)".
          iExists P1, P2.
          iFrame "#".
          iMod (inv_acc (⊤ ∖ ↑logN.@(a ^+ 1)%a) with "Hinv_a") as "[Hrefinv_a Hcls_a]";[solve_ndisj|].
          iDestruct "Hrefinv_a" as (w1) "[>Ha HPa]".
          iExists w1.
          iFrame "∗ #".
          rewrite /allow_jnz_mask. do 2 (case_decide ; try solve_addr).
        + iDestruct ("Hreg" $! dst _ Hneq Hneq' Hreg) as "Hvsrc".
          rewrite (fixpoint_interp1_eq (WCap _ _ _ _)) /=.
          iDestruct ("Hvsrc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & Hexec)".
          iExists P1, P2.
          iFrame "#".
          iMod (inv_acc (⊤ ∖ ↑logN.@(a ^+ 1)%a) with "Hinv_a") as "[Hrefinv_a Hcls_a]";[solve_ndisj|].
          iDestruct "Hrefinv_a" as (w1) "[>Ha HPa]".
          iExists w1.
          iFrame "∗ #".
          rewrite /allow_jnz_mask. do 2 (case_decide ; try solve_addr).
      }

      destruct (decide (dst = idc)) as [|Hneq']; simplify_map_eq.
      + rewrite fixpoint_interp1_eq /=.
        iDestruct ("Hwidc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & Hexec)".
        iExists P1, P2.

        iFrame "#".
        iMod (inv_acc (⊤ ∖ ↑logN.@pc_a) with "Hinv_a") as "[Hrefinv_a Hcls_a]";[solve_ndisj|].
        iMod (inv_acc (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a) with "Hinv_a'") as "[Hrefinv_a' Hcls_a']";[solve_ndisj|].
        iDestruct "Hrefinv_a" as (w1) "[>Ha HPa]".
        iDestruct "Hrefinv_a'" as (w2) "[>Ha' HPa']".
        iExists w1, w2.

        iFrame "∗ #".
        rewrite /region_open_resources2.
        iModIntro.
        iIntros "Ha".
        iDestruct "Ha" as (w1' w2') "(Hw1' & HP1' & Hw2' & HP2')".
        rewrite /allow_jnz_mask.
        case_decide; simplify_eq.
        case_decide; simplify_eq.
        iMod ("Hcls_a'" with "[Hw2' HP2']") as "_"; first (iExists _ ; iFrame).
        iMod ("Hcls_a" with "[Hw1' HP1']") as "_"; first (iExists _ ; iFrame).
        done.
      + iDestruct ("Hreg" $! dst _ Hneq Hneq' Hreg) as "Hvsrc".
        rewrite (fixpoint_interp1_eq (WCap _ _ _ _)) /=.
        iDestruct ("Hvsrc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & Hexec)".
        iExists P1, P2.

        iFrame "#".
        iMod (inv_acc (⊤ ∖ ↑logN.@pc_a) with "Hinv_a") as "[Hrefinv_a Hcls_a]";[solve_ndisj|].
        iMod (inv_acc (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a) with "Hinv_a'") as "[Hrefinv_a' Hcls_a']";[solve_ndisj|].
        iDestruct "Hrefinv_a" as (w1) "[>Ha HPa]".
        iDestruct "Hrefinv_a'" as (w2) "[>Ha' HPa']".
        iExists w1, w2.

        iFrame "∗ #".
        rewrite /region_open_resources2.
        iModIntro.
        iIntros "Ha".
        iDestruct "Ha" as (w1' w2') "(Hw1' & HP1' & Hw2' & HP2')".
        rewrite /allow_jnz_mask.
        case_decide; simplify_eq.
        case_decide; simplify_eq.
        iMod ("Hcls_a'" with "[Hw2' HP2']") as "_"; first (iExists _ ; iFrame).
        iMod ("Hcls_a" with "[Hw1' HP1']") as "_"; first (iExists _ ; iFrame).
        done.
  Qed.

  Definition allow_jnz_mem
    (regs : Reg) (mem : Mem) (dst src : RegName)
    (pc_a : Addr) (pc_w : Word)
    (p : Perm) (b e a : Addr) (wsrc : Word)
    (P1 P2 : D) :=
    ( ⌜read_reg_inr regs dst p b e a⌝ ∗
      ⌜regs !! src = Some wsrc⌝ ∗
       if decide (reg_allows_IE_jmp regs dst p b e a
               /\ regs !! src = Some wsrc
               /\ nonZero wsrc = true)
       then (if decide (pc_a = a)
             then ∃ w2, ⌜mem = <[(a^+1)%a:=w2]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources' pc_a a w2 P2
             else
               if decide (pc_a = (a^+1)%a)
               then ∃ w1, ⌜mem = <[a:=w1]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources pc_a a w1 P1
               else ∃ w1 w2,
                   ⌜mem = <[(a^+1)%a:=w2]> (<[a:=w1]> (<[pc_a:=pc_w]> ∅))⌝
                                             ∗ region_open_resources2 pc_a a w1 w2 P1 P2)
       else ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma jnz_res_implies_mem_map:
    ∀ (regs : leibnizO Reg) (dst src: RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a: Addr) (wsrc : Word)
      (P1 P2:D),
      allow_jnz_res regs dst src pc_a p b e a wsrc P1 P2
      -∗ pc_a ↦ₐ pc_w
      ={⊤ ∖ ↑logN.@pc_a, allow_jnz_mask_reg regs dst src pc_a p b e a wsrc}=∗
      ∃ mem : Mem,
          allow_jnz_mem regs mem dst src pc_a pc_w p b e a wsrc P1 P2
            ∗ ▷ ([∗ map] a0↦w ∈ mem, a0 ↦ₐ w).
  Proof.
    intros regs dst src pc_a pc_w p b e a wsrc P1 P2.
    iIntros "HJmpRes Hpc_a".
    iDestruct "HJmpRes" as "(%Hrinr & %Hsrc & HJmpRes)".
    rewrite /allow_jnz_mask /allow_jnz_mask_reg.

    case_decide as Hdec ; cycle 1.
    { rewrite /read_reg_inr in Hrinr.
      iExists _.
      iSplitL "HJmpRes".
      + iModIntro. rewrite /allow_jnz_mem.
        do 2 (iSplitR; auto).
        case_decide; auto; first by exfalso.
      + iModIntro. iNext. by iApply memMap_resource_1.
    }
    destruct Hdec as ((Hreg & -> & Hwb & Hwb') & Hsrc' & Hnz).
    assert (a <> (a^+1)%a) as Haeq by (apply andb_prop in Hwb as [_ Hge]; solve_addr).
    rewrite /allow_jnz_mask.
    iDestruct "HJmpRes" as "[Hexec HJmpRes]".
    iMod "HJmpRes" as "HJmpRes".

    case_decide as Ha ; simplify_eq.
    { (* pc_a = a *)
      iDestruct "HJmpRes" as (w2) "[Ha' HJmpRest]".
      iExists _.
      iSplitL "HJmpRest".
      + iSplitR; first auto.

        case_decide as Hdec1.
        2: {
          apply not_and_r in Hdec1 as [Hcontra|Hcontra]; simplify_eq.
          all: exfalso; apply Hcontra ; repeat (split ; auto).
        }
        case_decide; simplify_eq; auto.
      + iModIntro. iNext.
        rewrite memMap_resource_2ne; auto; iFrame.
    }
    (* pc_a ≠ a *)
    case_decide as Ha' ; simplify_eq.
    { (* pc_a = a+1 *)
      iDestruct "HJmpRes" as (w1) "[Ha HJmpRest]".
      iExists _.
      iSplitL "HJmpRest".
      + iSplitR; first auto.
        case_decide as Hdec1.
        2: {
          apply not_and_r in Hdec1 as [Hcontra|Hcontra]; simplify_eq.
          all: exfalso; apply Hcontra ; repeat (split ; auto).
        }
        case_decide; simplify_eq; auto.
        case_decide; simplify_eq; auto.
      + iModIntro. iNext.
        rewrite memMap_resource_2ne; auto; iFrame.
    }
    (* pc_a ≠ a+1 *)

    iDestruct "HJmpRes" as (w1 w2) "(Ha & Ha' & HJmpRest)".
    iExists _.
    iSplitL "HJmpRest".
    + iSplitR; first auto.
      case_decide as Hdec1.
      2: {
        apply not_and_r in Hdec1 as [Hcontra|Hcontra]; simplify_eq.
        all: exfalso; apply Hcontra ; repeat (split ; auto).
      }
      case_decide; simplify_eq; auto.
      case_decide; simplify_eq; auto.
      iModIntro; auto.
    + iModIntro. iNext.
      rewrite memMap_resource_3ne; auto; iFrame.
  Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (regs : leibnizO Reg) (mem : Mem) (dst src : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr) (wsrc : Word)
      (P1 P2 : D),
      allow_jnz_mem regs mem dst src pc_a pc_w p b e a wsrc P1 P2
        -∗ ⌜mem !! pc_a = Some pc_w⌝
          ∗ ⌜allow_jnz_mmap_or_true dst src regs mem⌝.
  Proof.
    iIntros (regs mem dst src pc_a pc_w p b e a wsrc P1 P2) "HJmpMem".
    iDestruct "HJmpMem" as "(%Hrinr & %Hsrc & HJmpRes)".
    case_decide as Hdec ; cycle 1.
    { iDestruct "HJmpRes" as "->".
      iSplitR. by rewrite lookup_insert.
      iPureIntro ; intros ? ? Hnz.
      exists p,b,e,a.
      split; auto.
      apply not_and_r in Hdec as [Hcontra|Hcontra]; simplify_eq; cycle 1.
      apply not_and_r in Hcontra as [Hcontra|Hcontra]; simplify_eq.
      apply Is_true_true_1 in Hnz.
      done.
      by destruct (decide (reg_allows_IE_jmp regs dst p b e a)).
    }
    destruct Hdec as (Hdec & _ & Hnz).
    assert (a <> (a^+1)%a)
    by (inversion Hdec as (_ & _ & Hwb%withinBounds_true_iff & _); solve_addr).
    case_decide as Ha; simplify_eq.
    { iDestruct "HJmpRes" as (w2) "[%Hmem _]" ; subst.
      iSplitL; iPureIntro.
      by simplify_map_eq.
      intros ? ? ?. exists p,b,e,a.
      split;auto.
      simplify_eq.
      case_decide; auto.
      inversion Hdec.
      exists pc_w, w2.
      by split ; simplify_map_eq.
    }
    case_decide as Ha'; simplify_eq.
    { iDestruct "HJmpRes" as (w1) "[%Hmem _]" ; subst.
      iSplitL; iPureIntro.
      by simplify_map_eq.
      intros ? ? ?. exists p,b,e,a.
      split;auto.
      simplify_eq.
      case_decide; auto.
      inversion Hdec.
      exists w1, pc_w.
      by split ; simplify_map_eq.
    }

    iDestruct "HJmpRes" as (w1 w2) "[%Hmem _]" ; subst.
    iSplitL; iPureIntro.
    by simplify_map_eq.
    intros ? ? ?. exists p,b,e,a.
    split;auto.
    simplify_eq.
    case_decide; auto.
    exists w1, w2.
    by split ; simplify_map_eq.
  Qed.

  Lemma reg_allows_IE_jmp_same
    (regs : Reg) (r : RegName)
    (p p' : Perm) (b b' e e' a a' : Addr):
    reg_allows_IE_jmp regs r p b e a ->
    regs !! r = Some (WCap p' b' e' a') ->
    (p = p' /\ b = b' /\ e = e' /\ a = a').
  Proof.
    intros HallowJmp Hregs.
    destruct HallowJmp as (Hregs'&->&_).
    by rewrite Hregs' in Hregs; simplify_eq.
  Qed.

  Lemma jnz_case (regs : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst src : RegName) (P : D):
    ftlr_instr regs p b e a widc w (Jnz dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread _] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p b e a]> (<[idc:=widc]> regs) !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      destruct (decide (x = idc)).
      rewrite lookup_insert_ne; auto.
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      by rewrite! lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0, read_reg_inr (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) dst p0 b0 e0 a0)
      as [p0 [b0 [e0 [a0 HVdst] ] ] ].
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. rewrite Hsomedst.
      destruct wdst as [|[ p0 b0 e0 a0|] | ]; try done.
      by repeat eexists.
    }

    assert (exists wsrc, (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) !! src = Some wsrc) as [wsrc HVsrc].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      by eexists.
    }

    (* Step 1: open the region, if necessary, and store all the resources
       obtained from the region in allow_IE_res *)
    iDestruct (create_jnz_res with "Hreg Hinv_idc") as (P1 P2) "HJmpRes"; eauto.
    { destruct Hp ; destruct p ; auto. }

    (* Step2: derive the concrete map of memory we need, and any spatial
       predicates holding over it *)
    iMod (jnz_res_implies_mem_map with "HJmpRes Ha") as (mem) "[HJmpMem HJmpRest]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HJmpMem") as
      %(HReadPC & HAJmpMem); auto.

    (* Step 3.5:  derive the non-spatial conditions over the registers *)
    iAssert (⌜allow_jnz_rmap_or_true dst src
               (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))⌝)%I as "%HAJmpReg".
    { rewrite /allow_jnz_rmap_or_true.
      iIntros (wsrc0) "%Hsrc0 %Hnz0".
      iExists p0, b0, e0, a0.
      iSplit; auto.
      case_decide as Heq; auto.
      by iExists widc; simplify_map_eq.
    }

    iApply (wp_Jnz _ _ _ _ _ _ _ _ (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))
             with "[Hmap HJmpRest]");eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".
    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw".
    rewrite /allow_jnz_res /allow_jnz_mem /allow_jnz_mask_reg /allow_jnz_mask.

    destruct HSpec as
      [ Hfail
      | * Hsrc Hdst Hcond Hwb Hwb' Ha Ha' HincrPC (* Success IE true*)
      | * Hsrc Hdst Hcond HnIE HincrPC (* Success true *)
      | * Hsrc Hcond HincrPC (* Success false *)
      ].
    - (* Fail *)
      case_decide as HallowJmp; cycle 1.
      {
        iModIntro.
        iDestruct "HJmpMem" as "(_&_&->)". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto; iIntros; discriminate.
      }
      iDestruct "HJmpMem" as "(_&_&H)".
      destruct HallowJmp as (HallowJmp & _ & Hnz).
      assert ((a0 ^+ 1)%a ≠ a0) as Ha0eq
          by (destruct HallowJmp as (_ & _ & Hwb%withinBounds_true_iff & _); solve_addr).

      (* TODO duplicated proof... could be better *)
      destruct (decide (a = a0)) as [Ha|Ha]; simplify_map_eq.
      { (* a = a0 *)
        iDestruct "H" as (w2) "(->&Hres)". rewrite /region_open_resources'.
        rewrite memMap_resource_2ne; auto.
        iDestruct "Hmem" as "(Ha0' & Ha0)".
        iDestruct "Hres" as "(HP2 & _ & Hcls')".
        rewrite /allow_jnz_mask.
        case_decide as H'; simplify_eq.
        iMod ("Hcls'" with "[HP2 Ha0']") as "_"
        ; [iNext ; iExists w2; iFrame|iModIntro].
        iMod ("Hcls" with "[Ha0 HP]") as "_";[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto; iIntros; discriminate.
      }
      (* a <> a0 *)
      destruct (decide (a = (a0 ^+1)%a)) as [Ha'|Ha']; simplify_map_eq.
      { (* a = a0+1 *)
        iDestruct "H" as (w1) "(->&Hres)". rewrite /region_open_resources.
        rewrite memMap_resource_2ne; auto.
        iDestruct "Hmem" as "(Ha0 & Ha0')".
        iDestruct "Hres" as "(HP1 & _ & Hcls')".
        rewrite /allow_jnz_mask.
        case_decide as H'; simplify_eq; clear H'.
        case_decide as H'; simplify_eq.
        iMod ("Hcls'" with "[HP1 Ha0]") as "_"
        ; [iNext ; iExists w1; iFrame|iModIntro].
        iMod ("Hcls" with "[Ha0' HP]") as "_";[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto; iIntros; discriminate.
      }

      (* a <> a0+1 *)
      iDestruct "H" as (w1 w2) "(->&Hres)". rewrite /region_open_resources2.
      rewrite memMap_resource_3ne; auto.
      iDestruct "Hmem" as "(Ha0' & Ha0 & Ha)".
      iDestruct "Hres" as "(HP1 & HP2 & _& _ & Hcls')".
      rewrite /allow_jnz_mask.
      case_decide as H'; simplify_eq ; clear H'.
      case_decide as H'; simplify_eq ; clear H'.
      iMod ("Hcls'" with "[HP1 HP2 Ha0 Ha0']") as "_"
      ; [iNext ; iExists w1, w2; iFrame|iModIntro].
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto; iIntros; discriminate.


    - (* Success IE true*)
      rewrite insert_insert insert_commute //= insert_insert in HincrPC; subst regs'.
      case_decide as HallowJmp.
      2: { (* contradiction *)
        rewrite /reg_allows_IE_jmp in HallowJmp.
        rewrite /read_reg_inr in HVdst.
        rewrite Hdst in HVdst; simplify_eq.
        rewrite Hsrc in HVsrc; simplify_eq.
        repeat (apply not_and_r in HallowJmp as [HallowJmp|HallowJmp]; simplify_eq).
      }
      destruct HallowJmp as (HallowJmp & _ & Hnz).
      assert (PC <> dst) as Hdst'
          by (destruct (decide (PC = dst)); auto; simplify_map_eq; by destruct Hp).
      assert (p0 = IE /\ b0 = b1 /\ e0 = e1 /\ a0 = a1) as (-> & -> & -> & ->)
          by (by eapply reg_allows_IE_jmp_same)
      ; simplify_map_eq.
      assert ((a1 ^+ 1)%a ≠ a1) as Haeq by (apply withinBounds_true_iff in Hwb ; solve_addr).
      assert (withinBounds b1 e1 a1 ∧ withinBounds b1 e1 (a1 ^+ 1)%a) as Hbounds
          by (by split ; apply Is_true_true_2).

      iDestruct "HJmpMem" as "(_& %H' & HJmpMem)"; simplify_eq.
      iDestruct "HJmpRes" as "(_& _ & Hexec &HJmpRes)".
      case_decide as Ha0; simplify_eq.
      { (* a = a0 *)

        (* NOTE he next PC is an integer. Thus, it's always safe to execute an integer.
           I can probably prove this case without further modification in the definition
           of the LR *)

        iDestruct "HJmpMem" as (w2) "(->& HP2& %Hpers2& Hcls')".
        iDestruct "HP2" as "#HP2".
        rewrite /allow_jnz_mask.
        case_decide ; simplify_eq.
        rewrite memMap_resource_2ne; auto.
        simplify_map_eq.

        iDestruct "Hmem" as  "[Ha0' Ha0]".
        iMod ("Hcls'" with "[HP2 Ha0']") as "_"; [iNext;iExists widc0;iFrame "∗ #"|iModIntro].
        iMod ("Hcls" with "[HP Ha0]") as "_"; [iNext;iExists wpc;iFrame|iModIntro].
        iClear "HJmpRes".
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        destruct wpc; cbn in Hi; try done.
        iExtract "Hmap" PC as "HPC".

        (* TODO extract as a lemma ? that if (PC = WInt z), then safe to execute.
           It is the second time that it's used (cf. fundamental.v) *)
        iApply (wp_bind (fill [SeqCtx])); iSimpl.
        iApply (wp_notCorrectPC with "HPC").
        intro Hcontra; inversion Hcontra.
        iNext; iIntros "HPC"; iSimpl.
        iApply wp_pure_step_later; [ exact I |].
        iIntros "!> _".
        iApply wp_value; iIntros "%"; done.
      }

      (* a ≠ a0 *)
      case_decide as Ha0'; simplify_eq.
      { (* a = a0+1 *)

        iDestruct "HJmpMem" as (w1) "(->& HP1& %Hpers1& Hcls')".
        iDestruct "HP1" as "#HP1".
        rewrite /allow_jnz_mask.
        case_decide ; simplify_eq.
        case_decide ; simplify_eq.
        rewrite memMap_resource_2ne; auto.
        simplify_map_eq.

        iDestruct "Hmem" as  "[Ha0' Ha0]".
        iMod ("Hcls'" with "[HP1 Ha0']") as "_"; [iNext;iExists wpc;iFrame "∗ #"|iModIntro].
        iMod ("Hcls" with "[HP Ha0]") as "_"; [iNext;iExists widc0;iFrame|iModIntro].
        iClear "HJmpRes".
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".

        iApply ("Hexec" $! _ widc0) ; iFrame "∗ #".
        iRight; destruct widc0; cbn in Hi; try done.

        rewrite insert_commute //=.
        repeat (iSplit ; try done).
      }

      (* a ≠ a0+1 *)
      iDestruct "HJmpMem" as (w1 w2) "(->& HP1& HP2& %Hpers1& %Hpers2& Hcls')".
      rewrite /region_open_resources2.
      iDestruct "HP1" as "#HP1"; iDestruct "HP2" as "#HP2".
      rewrite /allow_jnz_mask; case_decide ; simplify_eq; case_decide ; simplify_eq.
      rewrite memMap_resource_3ne; auto.
      simplify_map_eq.

      iDestruct "Hmem" as  "(Ha0' & Ha0 & Ha)".
      iMod ("Hcls'" with "[HP1 HP2 Ha0' Ha0]") as "_"; [iNext;iExists wpc,widc0;iFrame "∗ #"|iModIntro].
      iMod ("Hcls" with "[HP Ha]") as "_"; [iNext;iExists w;iFrame|iModIntro].
      iClear "HJmpRes".
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".

      iApply "Hexec" ; iFrame "∗ #".
      rewrite insert_commute //=.
      repeat (iSplit ; try done).

    - (* Success true *)
      rewrite insert_insert in HincrPC; subst regs'.
      case_decide as HallowJmp.
      { (* contradiction *)
        rewrite /reg_allows_IE_jmp in HallowJmp.
        destruct HallowJmp as ((Hregs0 & -> & Hwb & Hwb') & _ & _).
        simplify_eq.
      }
      iModIntro.
      iDestruct "HJmpMem" as "(_&_&->)". rewrite -memMap_resource_1.
      iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.

      set (regs' := <[PC:=updatePcPerm w0]> (<[idc:=widc]> regs)).
      (* Needed because IH disallows non-capability values *)
      destruct w' as [ | [p' b' e' a' | ] | ]; cycle 1.
      {
        rewrite /updatePcPerm.
        set (pc_p' := if decide (p' = E) then RX else p').

        destruct (decide (p' = E)); simplify_map_eq.
        (* Special case if p' is E *)
        - (* p' = E *)
          iAssert (interp (WCap E b' e' a')) as "Hinterp".
          {
          assert ( dst <> PC ).
          { destruct (decide (dst = PC)) ; simplify_map_eq ; destruct Hp; auto. }
          simplify_map_eq.
          destruct (decide (dst = idc)) ; simplify_map_eq; auto.
          iApply "Hreg"; auto.
          }
          rewrite (fixpoint_interp1_eq (WCap E _ _ _)) //=.
          rewrite (insert_commute _ PC _ (WCap RX _ _ _)) //=.
          iDestruct ("Hinterp" with "[$Hinv_idc] [$Hmap $Hown]") as "Hcont"; auto.
        - (* p' ≠ E *)
        iNext ; iIntros "_".
        iApply ("IH" $! regs' pc_p' with "[%] [] [Hmap] [$Hown]"); subst regs'.
        { intro; cbn; by repeat (rewrite lookup_insert_is_Some'; right). }
        { iIntros (ri v Hri Hri' Hvs).
          simplify_map_eq.
          iApply "Hreg"; auto.
        }
        { rewrite
            insert_insert
              (insert_commute _ idc) //=
              insert_insert.
          subst pc_p'; simplify_eq.
          by destruct p'.
        }
        { iModIntro.
          subst pc_p'.
          iClear "HJmpRes IH Hread".
          clear Hsome' HVdst HAJmpMem HAJmpReg.

          destruct (decide (dst = PC)); simplify_map_eq; auto.
          destruct (decide (dst = idc)); simplify_map_eq; auto.
          iApply "Hreg" ; auto.
        }
        { iFrame "Hinv_idc". }
      }

      all: iNext ; iIntros "_".
      all: iExtract "Hmap" PC as "HPC".
      all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
        iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ].
      all: repeat iNext; iIntros "HPC /=".
      all: iApply wp_pure_step_later; auto.
      all: iNext; iIntros "_".
      all: iApply wp_value;iIntros; discriminate.

    - (* Success IE false *)
      apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .
      rewrite insert_insert in Hregs'; subst regs'.
      simplify_map_eq.

      case_decide as Heq; simplify_eq.
      { (* contradiction *)
        exfalso.
        destruct Heq as (_& H' & Hnz) ; simplify_eq.
        congruence.
      }
      iModIntro.
      iDestruct "HJmpMem" as "(_& %H' & ->)"; simplify_eq. rewrite -memMap_resource_1.
      iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.

      set (regs' := <[PC:=WCap p'' b'' e'' x]> (<[idc:=widc]> regs)).
      simplify_map_eq.

      iNext ; iIntros "_".
      iApply ("IH" $! regs' p'' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { intro; cbn; by repeat (rewrite lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        simplify_map_eq.
        iApply "Hreg"; auto.
      }
      { rewrite
          insert_insert
            (insert_commute _ idc) //=
            insert_insert.
        iFrame.
      }
      { iModIntro.
        iClear "HJmpRes IH Hread".
        rewrite !fixpoint_interp1_eq //=; destruct Hp as [-> | ->] ;iFrame "Hinv_pc".
      }
      { iFrame "Hinv_idc". }
  Qed.

End fundamental.
