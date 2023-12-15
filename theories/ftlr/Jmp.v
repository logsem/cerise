From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Jmp.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  (* Mask after the jump, depending on the address of the pc and the address
   of a *)
  Definition allow_jmp_mask (pc_a a a' : Addr) : coPset
    :=
    if decide (pc_a = a)
    then (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a')
    else
      if decide (pc_a = a')
      then (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a)
      else (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@a').

  Definition allow_jmp_mask_reg (regs : Reg) (r : RegName) (pc_a : Addr)
    (p : Perm) (b e a : Addr)
    : coPset :=
    if decide (reg_allows_IE_jmp regs r p b e a)
    then allow_jmp_mask pc_a a (a ^+1)%a
    else (⊤ ∖ ↑logN.@pc_a).

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately *)
  Definition region_open_resources2
    (pc_a : Addr) (a a' : Addr)
    (w1 : Word) (w2 : Word)
    (P1 P2 : D)
    : iProp Σ :=
    ▷ P1 w1 ∗ ▷ P2 w2
       ∗ persistent_cond P1 ∗ persistent_cond P2
       ∗ ((▷ ∃ w1 w2, a ↦ₐ w1 ∗ P1 w1 ∗ a' ↦ₐ w2 ∗ P2 w2)
          ={allow_jmp_mask pc_a a a', ⊤ ∖ ↑logN.@pc_a}=∗ emp)%I.

  Definition region_open_resources
    (pc_a : Addr) (a a' : Addr) (w : Word)
    (P : D)
    : iProp Σ :=
    (▷ P w
       ∗ persistent_cond P
       ∗ ((▷ ∃ w, a ↦ₐ w ∗ P w)
        ={allow_jmp_mask pc_a a a', ⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Definition allow_jmp_res_mem
    (pc_a : Addr) (a : Addr)
    (P1 P2 : D): iProp Σ :=
    (|={⊤ ∖ ↑logN.@pc_a, allow_jmp_mask pc_a a (a ^+1)%a}=>
       (if decide (pc_a = a)
        then ∃ w2, (a^+1)%a ↦ₐ w2 ∗ region_open_resources pc_a (a ^+1)%a a w2 P2
        else
          if decide (pc_a = (a^+1)%a)
          then ∃ w1, a ↦ₐ w1 ∗ region_open_resources pc_a a (a ^+1)%a w1 P1
          else ∃ w1 w2, a ↦ₐ w1 ∗ (a^+1)%a ↦ₐ w2 ∗ region_open_resources2 pc_a a (a ^+1)%a w1 w2 P1 P2)
    )%I.

  (* Description of what the resources are supposed to look like after opening the
     region if we need to, but before closing the region up again*)
  Definition allow_jmp_res (regs : Reg) (r : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr)
    (P1 P2 : D): iProp Σ :=
    (if decide (reg_allows_IE_jmp regs r p b e a)
       then
         (∀ w1 w2 regs', ▷ □ (P1 w1 ∗ (P2 w2 ∨ ⌜ is_int w2 ⌝) -∗ (interp_expr_gen interp regs' w1 w2)))
           ∗ allow_jmp_res_mem pc_a a P1 P2
       else True)%I.

  Lemma create_jmp_res:
    ∀ (regs : leibnizO Reg) (r : RegName)
      (pc_p : Perm) (pc_b pc_e pc_a : Addr)
      (p : Perm) (b e a : Addr),
      pc_p <> IE ->
      (∀ (r' : RegName) (w : Word), ⌜r' ≠ PC⌝ → ⌜regs !! r' = Some w⌝ → (fixpoint interp1) w)
        -∗ ∃ (P1 P2 : D),
             allow_jmp_res (<[PC:=WCap pc_p pc_b pc_e pc_a]> regs) r pc_a p b e a P1 P2.
  Proof.
    intros regs r pc_p pc_b pc_e pc_a p b e a Hpc_p.
    iIntros "#Hreg".
    iFrame "%".
    rewrite /allow_jmp_res.
    case_decide as Hallows; cycle 1.
    - by iExists (λne _, True%I), (λne _, True%I).
    - rewrite /allow_jmp_mask.
      destruct Hallows as (Hreg & -> & Hwb & Hwb').
      assert (a <> (a^+1)%a) by (apply Is_true_true_1, andb_prop in Hwb as [_ Hge]; solve_addr).
      assert ( withinBounds b e a /\ withinBounds b e (a^+1)%a) as Hwbs by auto.

      assert (r ≠ PC) as Hneq by (destruct (decide (r = PC)) ; simplify_map_eq; auto).
      rewrite lookup_insert_ne //= in Hreg.

      iDestruct ("Hreg" $! r _ Hneq Hreg) as "Hvsrc".
      rewrite fixpoint_interp1_eq /=.
      iDestruct ("Hvsrc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & Hexec)".
      iExists P1, P2.
      iFrame "#".
      iClear "Hexec".
      rewrite /allow_jmp_res_mem.

      case_decide as Ha; simplify_eq.
      { (* pc_a = a *)
        iMod (inv_acc (⊤ ∖ ↑logN.@a) with "Hinv_a'") as "[Hrefinv_a' Hcls_a']";[solve_ndisj|].
        iDestruct "Hrefinv_a'" as (w2) "[>Ha' HPa']".
        iExists w2.
        iFrame "∗ #".
        rewrite /allow_jmp_mask.
        rewrite decide_True //= decide_False //= decide_True //=.
      }

      case_decide as Ha'; simplify_eq.
      { (* pc_a = a+1 *)
        iMod (inv_acc (⊤ ∖ ↑logN.@(a ^+ 1)%a) with "Hinv_a") as "[Hrefinv_a Hcls_a]";[solve_ndisj|].
        iDestruct "Hrefinv_a" as (w2) "[>Ha HPa]".
        iExists w2.
        iFrame "∗ #".
        rewrite /allow_jmp_mask.
        rewrite decide_False //= decide_True //=.
      }

      (* pc_a ≠ a ∧ pc_a ≠ a+1 *)
      iMod (inv_acc (⊤ ∖ ↑logN.@pc_a) with "Hinv_a") as "[Hrefinv_a Hcls_a]";[solve_ndisj|].
      iMod (inv_acc (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a) with "Hinv_a'") as "[Hrefinv_a' Hcls_a']";[solve_ndisj|].
      iDestruct "Hrefinv_a" as (w1) "[>Ha HPa]".
      iDestruct "Hrefinv_a'" as (w2) "[>Ha' HPa']".
      iExists w1, w2.

      rewrite /region_open_resources2.
      iFrame "∗ #".
      rewrite /allow_jmp_mask.
      rewrite decide_False //= decide_False //=.
      iModIntro.
      iIntros "Ha".
      iDestruct "Ha" as (w1' w2') "(Hw1' & HP1' & Hw2' & HP2')".
      iMod ("Hcls_a'" with "[Hw2' HP2']") as "_"; first (iExists _ ; iFrame).
      iMod ("Hcls_a" with "[Hw1' HP1']") as "_"; first (iExists _ ; iFrame).
      done.
  Qed.

  Definition allow_jmp_mem
    (regs : Reg) (mem : Mem) (r : RegName)
    (pc_a : Addr) (pc_w : Word) (p : Perm) (b e a : Addr) (P1 P2 : D) :=
    (if decide (reg_allows_IE_jmp regs r p b e a)
       then (if decide (pc_a = a)
             then ∃ w2, ⌜mem = <[(a^+1)%a:=w2]> (<[pc_a:=pc_w]> ∅)⌝ ∗
                                                  region_open_resources pc_a (a^+1)%a a w2 P2
             else
               if decide (pc_a = (a^+1)%a)
               then ∃ w1, ⌜mem = <[a:=w1]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources pc_a a (a^+1)%a w1 P1
               else ∃ w1 w2,
                   ⌜mem = <[(a^+1)%a:=w2]> (<[a:=w1]> (<[pc_a:=pc_w]> ∅))⌝
                                             ∗ region_open_resources2 pc_a a (a^+1)%a w1 w2 P1 P2)
       else ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma contra_reg_allows_IE_jmp r regs b e a :
    regs !! r = Some (WCap IE b e a) ->
    withinBounds b e a ->
    withinBounds b e (a ^+ 1)%a ->
    ¬ reg_allows_IE_jmp regs r IE b e a ->
    False.
  Proof.
    intros Hreg Hwb Hwb' Hdec1.
    apply not_and_r in Hdec1 as [Hcontra|Hcontra]; simplify_eq.
    apply Hcontra ; repeat (split ; auto).
  Qed.

  Lemma jmp_res_implies_mem_map:
    ∀ (regs : leibnizO Reg) (r : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a: Addr)
      (P1 P2:D),
      read_reg_inr regs r p b e a
      -> allow_jmp_res regs r pc_a p b e a P1 P2
      -∗ pc_a ↦ₐ pc_w
      ={⊤ ∖ ↑logN.@pc_a, allow_jmp_mask_reg regs r pc_a p b e a }=∗
      ∃ mem : Mem,
          allow_jmp_mem regs mem r pc_a pc_w p b e a P1 P2
            ∗ ▷ ([∗ map] a0↦w ∈ mem, a0 ↦ₐ w).
  Proof.
    intros regs r pc_a pc_w p b e a P1 P2 Hrinr.
    iIntros "HJmpRes Hpc_a".
    rewrite /allow_jmp_res.
    rewrite /allow_jmp_mask /allow_jmp_mask_reg.

    case_decide as Hdec ; cycle 1.
    { rewrite /read_reg_inr in Hrinr.
      iExists _.
      iSplitL "HJmpRes".
      + iModIntro. rewrite /allow_jmp_mem. (* iSplitR; auto. *)
        case_decide; first by exfalso. auto.
      + iModIntro. iNext. by iApply memMap_resource_1.
    }
    destruct Hdec as (Hreg & -> & Hwb & Hwb').
    assert (a <> (a^+1)%a) as Haeq by (apply Is_true_true_1, andb_prop in Hwb as [_ Hge]; solve_addr).
    rewrite /allow_jmp_mask /allow_jmp_mem.
    iDestruct "HJmpRes" as "[Hexec HJmpRes]".
    iMod "HJmpRes" as "HJmpRes".

    case_decide as Ha ; simplify_eq.
    { (* pc_a = a *)
      iDestruct "HJmpRes" as (w2) "[Ha' HJmpRest]".
      iExists _.
      iSplitL "HJmpRest"; rewrite /allow_jmp_mem.
      + case_decide as Hdec1 ; [| exfalso ; eapply contra_reg_allows_IE_jmp ; eauto].
        case_decide; simplify_eq; auto.
      + iModIntro; iNext.
        rewrite memMap_resource_2ne; auto; iFrame.
    }

    case_decide as Ha' ; simplify_eq.
    { (* pc_a = a+1 *)
      iDestruct "HJmpRes" as (w1) "[Ha HJmpRest]".
      iExists _.
      iSplitL "HJmpRest"; rewrite /allow_jmp_mem.
      + case_decide as Hdec1 ; [| exfalso ; eapply contra_reg_allows_IE_jmp ; eauto].
        do 2 (case_decide; simplify_eq; auto).
      + iModIntro; iNext.
        rewrite memMap_resource_2ne; auto; iFrame.
    }

    (* pc_a ≠ a ∧ pc_a ≠ a+1 *)
    iDestruct "HJmpRes" as (w1 w2) "(Ha & Ha' & HJmpRest)".
    iExists _.
    iSplitL "HJmpRest"; rewrite /allow_jmp_mem.
    + case_decide as Hdec1 ; [| exfalso ; eapply contra_reg_allows_IE_jmp ; eauto].
      do 2 (case_decide; simplify_eq; auto).
    + iModIntro; iNext.
      rewrite memMap_resource_3ne; auto; iFrame.
  Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (regs : leibnizO Reg) (mem : Mem) (r : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr) (P1 P2 : D),
      read_reg_inr regs r p b e a
      -> allow_jmp_mem regs mem r pc_a pc_w p b e a P1 P2
      -∗ ⌜mem !! pc_a = Some pc_w⌝ ∗ ⌜allow_jmp_mmap_or_true r regs mem⌝.
  Proof.
    iIntros (regs mem r pc_a pc_w p b e a P1 P2 Hrinr) "HJmpMem".
    rewrite /allow_jmp_mem.
    case_decide as Hdec ; cycle 1.
    { iDestruct "HJmpMem" as "->".
      iSplitR. by rewrite lookup_insert.
      iExists p,b,e,a.
      iSplitR; auto.
      case_decide as Hdec1; auto.
    }
    assert (a <> (a^+1)%a)
    by (inversion Hdec as (_ & _ & Hwb%Is_true_true_1%withinBounds_true_iff & _); solve_addr).

    case_decide as Ha; simplify_eq.
    { (* pc_a = a *)
      iDestruct "HJmpMem" as (w2) "[%Hmem _]" ; subst.
      iSplitL.
      by iPureIntro; simplify_map_eq.
      iExists p,b,e,a.
      iSplitR; auto.
      case_decide; auto.
      inversion Hdec.
      iExists pc_w, w2.
      by iPureIntro ; split ; simplify_map_eq.
    }

    case_decide as Ha'; simplify_eq.
    { (* pc_a = a+1 *)
      iDestruct "HJmpMem" as (w1) "[%Hmem _]" ; subst.
      iSplitL.
      by iPureIntro; simplify_map_eq.
      iExists p,b,e,a.
      iSplitR; auto.
      case_decide; auto.
      inversion Hdec.
      iExists w1, pc_w.
      by iPureIntro ; split ; simplify_map_eq.
    }

    (* pc_a ≠ a ∧ pc_a ≠ a+1 *)
    iDestruct "HJmpMem" as (w1 w2) "[%Hmem _]" ; subst.
    iSplitL.
    by iPureIntro; simplify_map_eq.
    iExists p,b,e,a.
    iSplitR; auto.
    case_decide; auto.
    inversion Hdec.
    iExists w1, w2.
    by iPureIntro ; split ; simplify_map_eq.
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

  Lemma jmp_case (regs : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (src : RegName) (P : D):
    ftlr_instr regs p b e a widc w (Jmp src) P.
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
    assert (∃ p0 b0 e0 a0, read_reg_inr (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) src p0 b0 e0 a0)
      as [p0 [b0 [e0 [a0 HVsrc] ] ] ].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p0 b0 e0 a0|] | ]; try done.
      by repeat eexists.
    }

    iAssert (∀ (r' : RegName) (w : Word),
                ⌜r' ≠ PC⌝ → ⌜<[idc:=widc]> regs  !! r' = Some w⌝ → fixpoint interp1 w)%I
      as "Hreg'".
    { iIntros.
      destruct (decide (r' = idc)); simplify_map_eq; auto.
      iApply "Hreg";eauto.
    }

    (* Step 1: open the region, if necessary, and store all the resources
       obtained from the region in allow_IE_res *)
    iDestruct ((create_jmp_res _ _ p)  with "Hreg'") as (P1 P2) "HJmpRes"; eauto.
    { destruct Hp ; destruct p ; eauto. }

    (* Step2: derive the concrete map of memory we need, and any spatial
       predicates holding over it *)
    iMod (jmp_res_implies_mem_map with "HJmpRes Ha") as (mem) "[HJmpMem HJmpRest]"; first eauto.

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HJmpMem") as
      %(HReadPC & HAJmpMem); auto.

    (* Step 3.5:  derive the non-spatial conditions over the registers *)
    iAssert (⌜allow_jmp_rmap_or_true src
               (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))⌝)%I as "%HAJmpReg".
    { rewrite /allow_jmp_rmap_or_true.
      iExists p0, b0, e0, a0.
      iSplit; auto.
      case_decide as Heq; auto.
      by iExists widc; simplify_map_eq.
    }

    iApply (wp_jmp with "[Hmap HJmpRest]");eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
    { iSplitR "Hmap"; auto. }

    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".
    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw".
    (* rewrite /allow_jmp_res /allow_jmp_mask_reg. *)

    destruct HSpec as [* Hregs Hwb Hwb' Ha Ha' HincrPC | * Hregs HnIE HincrPC | Hfail].
    - (* success jmp IE *)
      rewrite insert_insert insert_commute //= insert_insert in HincrPC; subst regs'.

      assert (p0 = IE /\ b0 = b1 /\ e0 = e1 /\ a0 = a1) as (-> & <- & <- & <-)
          by (by rewrite /read_reg_inr in HVsrc; rewrite Hregs in HVsrc; simplify_eq).
      assert ((a0 ^+ 1)%a ≠ a0) as Haeq by (apply Is_true_true_1, withinBounds_true_iff in Hwb ; solve_addr).
      assert (withinBounds b0 e0 a0 ∧ withinBounds b0 e0 (a0 ^+ 1)%a) as Hbounds by auto.
      assert (PC <> src) as Hsrc
          by (destruct (decide (PC = src)); auto; simplify_map_eq; by destruct Hp).


      rewrite /allow_jmp_res /allow_jmp_mask_reg.
      rewrite decide_True.
      iDestruct "HJmpRes" as "(Hexec&HJmpRes)".

      case_decide as Ha0; simplify_eq.
      { (* a = a0 *)

        iDestruct "HJmpMem" as (w2) "(->& HP2& %Hpers2& Hcls')".
        iDestruct "HP2" as "#HP2".
        rewrite /allow_jmp_mask.
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
        iApply interp_expr_invalid_pc; try iFrame ; eauto.
        intro Hcontra; inversion Hcontra.
        iPureIntro; apply regmap_full_dom in Hsome; rewrite -Hsome; set_solver.
      }

      (* a ≠ a0 *)
      case_decide as Ha0'; simplify_eq.
      { (* a = a0+1 *)

        iDestruct "HJmpMem" as (w1) "(->& HP1& %Hpers1& Hcls')".
        iDestruct "HP1" as "#HP1".
        rewrite /allow_jmp_mask.
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

      (* a ≠ a0 ∧ a ≠ a0+1 *)
      iDestruct "HJmpMem" as (w1 w2) "(->& HP1& HP2& %Hpers1& %Hpers2& Hcls')".
      rewrite /region_open_resources2.
      iDestruct "HP1" as "#HP1"; iDestruct "HP2" as "#HP2".
      rewrite /allow_jmp_mask; case_decide ; simplify_eq; case_decide ; simplify_eq.
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

    - (* success jmp not IE *)
      rewrite insert_insert in HincrPC; subst regs'.
      destruct (decide (reg_allows_IE_jmp
                          (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))
                          src p0 b0 e0 a0)) as [HallowJmp|_].
      { (* contradiction *)
        rewrite /reg_allows_IE_jmp in HallowJmp.
        destruct HallowJmp as (Hregs0 & -> & Hwb & Hwb').
        simplify_eq.
      }
      iModIntro.
      iDestruct "HJmpMem" as "(_&->)". rewrite -memMap_resource_1.
      iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.

      set (regs' := <[PC:=updatePcPerm w0]> (<[idc:=widc]> regs)).
      (* Needed because IH disallows non-capability values *)
      destruct w0 as [ | [p' b' e' a' | ] | ]; cycle 1.
      {
        rewrite /updatePcPerm.
        set (pc_p' := if decide (p' = E) then RX else p').

        destruct (decide (p' = E)); simplify_map_eq.
        (* Special case if p' is E *)
        - (* p' = E *)
          iAssert (interp (WCap E b' e' a')) as "Hinterp".
          {
          assert ( src <> PC ).
          { destruct (decide (src = PC)) ; simplify_map_eq ; destruct Hp; auto. }
          simplify_map_eq.
          iApply "Hreg'"; auto.
          }
          rewrite (fixpoint_interp1_eq (WCap E _ _ _)) //=.
          rewrite (insert_commute _ PC _ (WCap RX _ _ _)) //=.
          iDestruct ("Hinterp" with "[$Hinv_idc] [$Hmap $Hown]") as "Hcont"; auto.
        - (* p' = E *)
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
          clear Hsome' HVsrc HAJmpMem HAJmpReg.

          destruct (decide (src = PC)); simplify_map_eq; auto.
          iApply "Hreg'" ; auto.
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

    - (* fail *)
      inversion Hfail as [? ? ? Hregs Hbounds ].
      destruct (decide (reg_allows_IE_jmp
                          (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))
                          src p0 b0 e0 a0)) as [HallowJmp|_]
      ; cycle 1.
      {
        iModIntro.
        iDestruct "HJmpMem" as "(_&->)". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto; iIntros; discriminate.
      }

      assert ((a0 ^+ 1)%a ≠ a0) as Ha0eq
      by (destruct HallowJmp as (_ & _ & Hwb%Is_true_true_1%withinBounds_true_iff & _); solve_addr).
      assert (p0 = IE /\ b0 = b1 /\ e0 = e1 /\ a0 = a1) as (-> & <- & <- & <-)
          by (by rewrite /read_reg_inr in HVsrc; rewrite Hregs in HVsrc; simplify_eq).


      Set Nested Proofs Allowed.
      (* Lemma mem_map_recover_res: *)
      (*   ∀ (regs : leibnizO Reg) (mem : Mem) (r : RegName) *)
      (*     (pc_a : Addr) (pc_w : Word) *)
      (*     (p : Perm) (b e a : Addr) (storev loadv : Word), *)
      (*     reg_allows_store regs r p b e a *)
      (*     → mem !! a = Some loadv *)

      (*     → (* allow_store_mem regs mem r pc_a pc_w p b e a *) *)
      (*       allow_jmp_mem regs mem r pc_a pc_w p b e a P1 P2  *)

      (*       -∗ ([∗ map] a'↦w ∈ (<[a:=storev]> mem), a' ↦ₐ w) *)

      (*       -∗ interp storev *)

      (*       ={allow_jmp_mask pc_a a1 (a1 ^+1), ⊤ ∖ ↑logN.@pc_a}=∗ *)
      (*        if decide (reg_allows_store regs r p b e a ∧ a = pc_a) *)
      (*        then pc_a ↦ₐ storev *)
      (*        else pc_a ↦ₐ pc_w. *)

      iDestruct "HJmpMem" as "(_&H)".

      (* TODO duplicated proof... could be better *)
      case_decide as Ha0; simplify_eq.
      { (* a = a0 *)
        iDestruct "H" as (w2) "(->&Hres)". rewrite /region_open_resources.
        rewrite memMap_resource_2ne; auto.
        iDestruct "Hmem" as "(Ha0' & Ha0)".
        iDestruct "Hres" as "(HP2 & _ & Hcls')".
        rewrite /allow_jmp_mask.
        case_decide as H'; simplify_eq.
        case_decide; simplify_eq.
        iMod ("Hcls'" with "[HP2 Ha0']") as "_"
        ; [iNext ; iExists w2; iFrame|iModIntro].

        iMod ("Hcls" with "[Ha0 HP]") as "_";[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto; iIntros; discriminate.
      }

      case_decide as Ha0' ; simplify_eq.
      { (* a = a0+1 *)
        iDestruct "H" as (w1) "(->&Hres)". rewrite /region_open_resources.
        rewrite memMap_resource_2ne; auto.
        iDestruct "Hmem" as "(Ha0 & Ha0')".
        iDestruct "Hres" as "(HP1 & _ & Hcls')".
        rewrite /allow_jmp_mask.
        case_decide as H'; simplify_eq; clear H'.
        case_decide as H'; simplify_eq.
        iMod ("Hcls'" with "[HP1 Ha0]") as "_"
        ; [iNext ; iExists w1; iFrame|iModIntro].
        iMod ("Hcls" with "[Ha0' HP]") as "_";[iExists w;iFrame|iModIntro].

        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto; iIntros; discriminate.
      }

      (* a ≠ a0 ∧ a ≠ a0+1 *)
      iDestruct "H" as (w1 w2) "(->&Hres)". rewrite /region_open_resources2.
      rewrite memMap_resource_3ne; auto.
      iDestruct "Hmem" as "(Ha0' & Ha0 & Ha)".
      iDestruct "Hres" as "(HP1 & HP2 & _& _ & Hcls')".
      rewrite /allow_jmp_mask.
      case_decide as H'; simplify_eq ; clear H'.
      case_decide as H'; simplify_eq ; clear H'.
      iMod ("Hcls'" with "[HP1 HP2 Ha0 Ha0']") as "_"
      ; [iNext ; iExists w1, w2; iFrame|iModIntro].

      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto; iIntros; discriminate.
    Qed.

End fundamental.
