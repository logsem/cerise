From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_JmpIEpcc.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* The first part is common with Jnz. The argument =cond=
     expresses the pure conditions specific to the kind of jump.
   *)

  (* Mask after the jump, depending on the address of the pc and the address
   of a *)
  Definition allow_jmp_mask (pc_a a : Addr) : coPset
    :=
    if decide (pc_a = a)
    then (⊤ ∖ ↑logN.@pc_a)
    else(⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a).

  Definition allow_jmp_mask_reg (cond : Prop) `{Decision cond}
    (regs : Reg) (r : RegName) (pc_a : Addr)
    (p : Perm) (b e a : Addr) : coPset :=
    if decide (reg_allows_IEpcc_jmp regs r p b e a /\ cond /\ pc_a ≠ b)
    then allow_jmp_mask pc_a b
    else (⊤ ∖ ↑logN.@pc_a).

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately *)
  (* Definition region_open_resources2 *)
  (*   (pc_a : Addr) (a : Addr) *)
  (*   (w1 : Word) (w2 : Word) *)
  (*   (P1 P2 : D) *)
  (*   : iProp Σ := *)
  (*   ▷ P1 w1 *)
  (*   ∗ persistent_cond P1 *)
  (*   ∗ ((▷ ∃ w1, a ↦ₐ w1 ∗ P1 w1) *)
  (*      ={allow_jmp_mask pc_a a, ⊤ ∖ ↑logN.@pc_a}=∗ emp)%I. *)

  Definition region_open_resources
    (pc_a : Addr) (a : Addr) (w : Word) (P : D) : iProp Σ :=
    (▷ P w
       ∗ persistent_cond P
       ∗ ((▷ ∃ w, a ↦ₐ w ∗ P w)
        ={allow_jmp_mask pc_a a, ⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Definition allow_jmp_res_mem
    (pc_a : Addr) (a : Addr)
    (P : D): iProp Σ :=
    (|={⊤ ∖ ↑logN.@pc_a, allow_jmp_mask pc_a a}=>
       (if decide (pc_a = a)
        then True
        else ∃ w, a ↦ₐ w ∗ region_open_resources pc_a a w P)
    )%I.

  (* Description of what the resources are supposed to look like after opening the
     region if we need to, but before closing the region up again*)
  Definition allow_jmp_res (cond : Prop) `{Decision cond} (regs : Reg) (r : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr)
    (P : D): iProp Σ :=
    (if decide (reg_allows_IEpcc_jmp regs r p b e a /\ cond /\ pc_a ≠ b)
       then
         (∀ w1 regs', ▷ □ (P w1 -∗ (interp_expr_gen interp regs' w1 (WCap RW b e a))))
           ∗ allow_jmp_res_mem pc_a b P
       else True)%I.

  Lemma create_jmp_res (cond : Prop) `{Decision cond}:
    ∀ (regs : leibnizO Reg) (r : RegName)
      (pc_p : Perm) (pc_b pc_e pc_a : Addr)
      (p : Perm) (b e a : Addr),
      pc_p <> IEpcc ->
      pc_p <> IEpair ->
      (∀ (r' : RegName) (w : Word), ⌜r' ≠ PC⌝ → ⌜regs !! r' = Some w⌝ → (fixpoint interp1) w)
        -∗ ∃ (P : D),
             @allow_jmp_res cond _ (<[PC:=WCap pc_p pc_b pc_e pc_a]> regs) r pc_a p b e a P.
  Proof.
    intros regs r pc_p pc_b pc_e pc_a p b e a Hpc_p Hpc_p'.
    iIntros "#Hreg".
    rewrite /allow_jmp_res.
    case_decide as Hallows; cycle 1.
    - by iExists (λne _, True%I).
    - destruct Hallows as [(Hreg & -> & Hwb) Hcond].

      assert (r ≠ PC) as Hneq by (destruct (decide (r = PC)) ; simplify_map_eq; auto).
      rewrite lookup_insert_ne //= in Hreg.

      iDestruct ("Hreg" $! r _ Hneq Hreg) as "Hvsrc".
      rewrite fixpoint_interp1_eq /=.
      iDestruct ("Hvsrc" $! Hwb) as (P) "(Hpers_P1 & Hinv_b & Hexec)".
      iExists P.
      iFrame "#".
      iClear "Hexec".
      rewrite /allow_jmp_res_mem /allow_jmp_mask.

      case_decide as Hb; simplify_eq; first done.

      (* pc_a ≠ b  *)
      iMod (inv_acc (⊤ ∖ ↑logN.@pc_a) with "Hinv_b") as "[Hrefinv_b Hcls_b]";[solve_ndisj|].
      iDestruct "Hrefinv_b" as (w1) "[>Hb HPb]".
      iExists w1.

      rewrite /region_open_resources /allow_jmp_mask decide_False //=.
      iFrame "∗ #".
      by iModIntro.
      (* iIntros "Ha". *)
      (* iDestruct "Ha" as (w1' w2') "(Hw1' & HP1' & Hw2' & HP2')". *)
      (* iMod ("Hcls_a'" with "[Hw2' HP2']") as "_"; first (iExists _ ; iFrame). *)
      (* iMod ("Hcls_a" with "[Hw1' HP1']") as "_"; first (iExists _ ; iFrame). *)
      (* done. *)
  Qed.

  (* Definition allow_jmp_mem_res *)
  (*   (mem : Mem) (pc_a : Addr) (pc_w : Word) (a : Addr) (P : D) := *)
  (*   (if decide (pc_a = a) *)
  (*   then ∃ w2, ⌜mem = (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources pc_a a w P *)
  (*   else *)
  (*     if decide (pc_a = (a^+1)%a) *)
  (*     then ∃ w1, ⌜mem = <[a:=w1]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources pc_a a (a^+1)%a w1 P1 *)
  (*     else ∃ w1 w2, *)
  (*         ⌜mem = <[(a^+1)%a:=w2]> (<[a:=w1]> (<[pc_a:=pc_w]> ∅))⌝ ∗ region_open_resources2 pc_a a (a^+1)%a w1 w2 P1 P2)%I. *)

  Definition allow_jmp_mem (cond : Prop) `{Decision cond}
    (regs : Reg) (mem : Mem) (r : RegName)
    (pc_a : Addr) (pc_w : Word) (p : Perm) (b e a : Addr) (P : D) :=
    (if decide (reg_allows_IEpcc_jmp regs r p b e a /\ cond /\ pc_a ≠ b)
     then ∃ w, ⌜mem = <[b:=w]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources pc_a b w P
     else ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma jmp_res_implies_mem_map (cond : Prop) `{Decision cond}:
    ∀ (regs : leibnizO Reg) (r : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a: Addr)
      (P : D),
      read_reg_inr regs r p b e a
      -> @allow_jmp_res cond _ regs r pc_a p b e a P
      -∗ pc_a ↦ₐ pc_w
      ={⊤ ∖ ↑logN.@pc_a, @allow_jmp_mask_reg cond _ regs r pc_a p b e a }=∗
      ∃ mem : Mem,
          @allow_jmp_mem cond _ regs mem r pc_a pc_w p b e a P
            ∗ ▷ ([∗ map] a0↦w ∈ mem, a0 ↦ₐ w).
  Proof.
    intros regs r pc_a pc_w p b e a P Hrinr.
    iIntros "HJmpRes Hpc_a".
    rewrite /allow_jmp_res /allow_jmp_mask /allow_jmp_mask_reg.

    case_decide as Hdec ; cycle 1.
    { rewrite /read_reg_inr in Hrinr.
      iExists _.
      iSplitR "Hpc_a".
      + rewrite /allow_jmp_mem decide_False //=.
      + iModIntro. iNext. by iApply memMap_resource_1.
    }
    destruct Hdec as ((Hreg & -> & Hwb) & Hcond & Hb).
    iDestruct "HJmpRes" as "[Hexec HJmpRes]".
    iMod "HJmpRes" as "HJmpRes".
    rewrite /allow_jmp_mask /allow_jmp_mem.
    repeat (rewrite decide_False;[|done]).

    iDestruct "HJmpRes" as (w) "(Ha & HJmpRest)".
    iModIntro.
    iExists (<[b:=w]> (<[pc_a:=pc_w]> ∅)).
    rewrite decide_True;[|done].
    iSplitL "HJmpRest"; eauto.
    rewrite memMap_resource_2ne; auto; iFrame.
  Qed.

  (* Close the invariants, in case of fail*)
  (* Lemma mem_map_recover_res *)
  (*   (cond : Por(mem : Mem) (pc_a a : Addr) (pc_w : Word) (P : D): *)
  (*   allow_jmp_mem mem pc_a pc_w a P *)
  (*   -∗ ([∗ map] a'↦w' ∈ mem, a' ↦ₐ w') *)
  (*   ={allow_jmp_mask pc_a a , ⊤ ∖ ↑logN.@pc_a}=∗ pc_a ↦ₐ pc_w. *)
  (* Proof. *)
  (*   iIntros (Hneq) "HJmpMem Hmem". *)

  (*   rewrite /allow_jmp_mem_res /allow_jmp_mask. *)
  (*   case_decide as Ha; simplify_eq. *)
  (*   { (* pc_a = a *) *)
  (*     iDestruct "HJmpMem" as (w2) "(->&Hres)". rewrite /region_open_resources. *)
  (*     rewrite memMap_resource_2ne; auto. *)
  (*     iDestruct "Hmem" as "(Ha0' & Ha0)". *)
  (*     iDestruct "Hres" as "(HP2 & _ & Hcls')". *)
  (*     rewrite /allow_jmp_mask. *)
  (*     rewrite decide_False //= decide_True //=. *)
  (*     iMod ("Hcls'" with "[HP2 Ha0']") as "_" ; [iNext ; iExists w2; iFrame|auto]. *)
  (*   } *)

  (*   case_decide as Ha'; simplify_eq. *)
  (*   { (* pc_a = a+1 *) *)
  (*     iDestruct "HJmpMem" as (w1) "(->&Hres)". rewrite /region_open_resources. *)
  (*     rewrite memMap_resource_2ne; auto. *)
  (*     iDestruct "Hmem" as "(Ha0 & Ha0')". *)
  (*     iDestruct "Hres" as "(HP1 & _ & Hcls')". *)
  (*     rewrite /allow_jmp_mask. *)
  (*     rewrite decide_False //= decide_True //=. *)
  (*     iMod ("Hcls'" with "[HP1 Ha0]") as "_" ; [iNext ; iExists w1; iFrame|auto]. *)
  (*   } *)

  (*   (* a ≠ a0 ∧ a ≠ a0+1 *) *)
  (*   iDestruct "HJmpMem" as (w1 w2) "(->&Hres)". rewrite /region_open_resources2. *)
  (*   rewrite memMap_resource_3ne; auto. *)
  (*   iDestruct "Hmem" as "(Ha0' & Ha0 & Ha)". *)
  (*   iDestruct "Hres" as "(HP1 & HP2 & _& _ & Hcls')". *)
  (*   rewrite /allow_jmp_mask. *)
  (*   rewrite decide_False //= decide_False //=. *)
  (*   iMod ("Hcls'" with "[HP1 HP2 Ha0 Ha0']") as "_"; [iNext ; iExists w1,w2; iFrame|auto]. *)
  (* Qed. *)

  (* Close the invariants, in case of jump to IEpair *)
  (* Lemma mem_map_recover_res_ie *)
  (*   (mem : Mem) (pc_a a : Addr) (pc_w wpc widc : Word) (P P1 P2 : D): *)
  (*   (a ^+ 1)%a ≠ a -> *)
  (*   mem !! a = Some wpc -> *)
  (*   mem !! (a ^+ 1)%a = Some widc -> *)

  (*   allow_jmp_mem_res mem pc_a pc_w a P1 P2 *)
  (*   -∗ ([∗ map] a'↦w' ∈ mem, a' ↦ₐ w') *)
  (*   ={allow_jmp_mask pc_a a (a ^+1)%a, ⊤ ∖ ↑logN.@pc_a}=∗ *)
  (*     if (decide (pc_a = a)) *)
  (*     then pc_a ↦ₐ pc_w ∗ ⌜pc_w = wpc ⌝ *)
  (*     else *)
  (*       if (decide (pc_a = (a^+1)%a)) *)
  (*       then pc_a ↦ₐ widc ∗ ⌜pc_w = widc⌝ ∗ ▷ P1 wpc ∗ persistent_cond P1 *)
  (*       else pc_a ↦ₐ pc_w ∗ ▷ P1 wpc ∗ ▷ P2 widc ∗ persistent_cond P1 ∗ persistent_cond P2. *)
  (* Proof. *)
  (*   iIntros (Hneq Hmem_a Hmem_a') "HJmpMem Hmem". *)
  (*   rewrite /allow_jmp_mem_res /allow_jmp_mask. *)

  (*   case_decide as Ha; simplify_eq. *)
  (*   { (* a = a0 *) *)
  (*     iDestruct "HJmpMem" as (w2) "(->& HP2& %Hpers2& Hcls')". *)
  (*     rewrite /allow_jmp_mask. *)
  (*     rewrite decide_False //= decide_True //=. *)
  (*     rewrite memMap_resource_2ne; auto. *)
  (*     simplify_map_eq. *)
  (*     iDestruct "Hmem" as  "[Ha0' Ha0]". *)
  (*     iMod ("Hcls'" with "[HP2 Ha0']") as "_" ; [iNext;iExists widc;iFrame "∗ #"|auto]. *)
  (*   } *)

  (*   case_decide as Ha'; simplify_eq. *)
  (*   { (* a = a0+1 *) *)
  (*     iDestruct "HJmpMem" as (w1) "(->& HP1& %Hpers1& Hcls')". *)
  (*     iDestruct "HP1" as "#HP1". *)
  (*     rewrite /allow_jmp_mask. *)
  (*     rewrite decide_False //= decide_True //=. *)
  (*     rewrite memMap_resource_2ne; auto. *)
  (*     simplify_map_eq. *)
  (*     iDestruct "Hmem" as "[Ha0' Ha0]". *)
  (*     iMod ("Hcls'" with "[HP1 Ha0']") as "_" ; [iNext;iExists wpc;iFrame "∗ #"|auto]. *)
  (*   } *)

  (*   (* a ≠ a0 ∧ a ≠ a0+1 *) *)
  (*   iDestruct "HJmpMem" as (w1 w2) "(->& HP1& HP2& %Hpers1& %Hpers2& Hcls')". *)
  (*   rewrite /region_open_resources2. *)
  (*   iDestruct "HP1" as "#HP1"; iDestruct "HP2" as "#HP2". *)
  (*   rewrite /allow_jmp_mask; case_decide ; simplify_eq; case_decide ; simplify_eq. *)
  (*   rewrite memMap_resource_3ne; auto. *)
  (*   simplify_map_eq. *)
  (*   iDestruct "Hmem" as  "(Ha0' & Ha0 & Ha)". *)
  (*   iMod ("Hcls'" with "[HP1 HP2 Ha0' Ha0]") as "_"; [iNext;iExists wpc,widc;iFrame "∗ #"|auto]. *)
  (* Qed. *)

  (* Derice pure conds =allow_jmp_mmap_or_true= from =cond_jmp= *)
  Lemma mem_map_implies_pure_conds:
    ∀ (regs : leibnizO Reg) (mem : Mem) (r : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr) (P : D),
      read_reg_inr regs r p b e a
      -> allow_jmp_mem cond_jmp regs mem r pc_a pc_w p b e a P
      -∗ ⌜mem !! pc_a = Some pc_w⌝ ∗ ⌜allow_jmp_mmap_or_true cond_jmp r regs mem⌝.
  Proof.
    iIntros (regs mem r pc_a pc_w p b e a P Hrinr) "HJmpMem".
    rewrite /allow_jmp_mem.
    case_decide as Hdec ; cycle 1.
    { iDestruct "HJmpMem" as "->".
      iSplitR. by rewrite lookup_insert.
      iExists p,b,e,a.
      iSplitR; auto.
      (* rewrite decide_False //=. *)
      admit.
    }
    destruct Hdec as ((Hreg & -> & Hwb) & Hcond & Hb).

    (* pc_a ≠ a ∧ pc_a ≠ a+1 *)
    iDestruct "HJmpMem" as (w) "[%Hmem _]" ; subst.
    iSplitL.
    by iPureIntro; simplify_map_eq.
    iExists IEpcc,b,e,a.
    iSplitR; auto.
    case_decide; auto.
    iExists w.
    by iPureIntro ; simplify_map_eq.
  Admitted.

  Lemma jmpiepair_case (regs : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (src : RegName) (P : D):
    ftlr_instr regs p b e a widc w (JmpIEpcc src) P.
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
       obtained from the region in allow_IEpair_res *)
    iDestruct ((create_jmp_res cond_jmp _ _ p)  with "Hreg'") as (P1) "HJmpRes"; eauto.
    { destruct Hp ; destruct p ; eauto. }
    { destruct Hp ; destruct p ; eauto. }

    (* Step2: derive the concrete map of memory we need, and any spatial
       predicates holding over it *)
    iMod ((jmp_res_implies_mem_map cond_jmp) with "HJmpRes Ha") as (mem) "[HJmpMem HJmpRest]"; first eauto.

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HJmpMem") as
      %(HReadPC & HAJmpMem); auto.

    (* Step 3.5:  derive the non-spatial conditions over the registers *)
    assert (allow_jmp_rmap_or_true cond_jmp src
               (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))) as HAJmpReg.
    { rewrite /allow_jmp_rmap_or_true.
      exists p0, b0, e0, a0.
      split; auto.
      case_decide as Heq; auto.
      by exists widc; simplify_map_eq.
    }

    iApply (wp_jmpIEpcc with "[Hmap HJmpRest]");eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
    { iSplitR "Hmap"; auto. }

    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".
    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw".

    destruct HSpec as [* Hregs Hwb Ha HincrPC | Hfail].
    - (* success jmp IE *)
      rewrite insert_insert insert_commute //= insert_insert in HincrPC; subst regs'.

      assert (p0 = IEpcc /\ b0 = b1 /\ e0 = e1 /\ a0 = a1) as (-> & <- & <- & <-)
          by (by rewrite /read_reg_inr in HVsrc; rewrite Hregs in HVsrc; simplify_eq).
      assert (b0 < e0)%a as Hbounds by auto.
      assert (PC <> src) as Hsrc
          by (destruct (decide (PC = src)); auto; simplify_map_eq; by
                destruct Hp).
      assert (reg_allows_IEpcc_jmp
                (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))
                src IEpcc b0 e0 a0) as HallowJmp
          by (by rewrite /reg_allows_IEpcc_jmp; auto).

      rewrite /allow_jmp_res /allow_jmp_mask_reg.
      rewrite !decide_True //=.
      iDestruct "HJmpRes" as "(Hexec&HJmpRes)".
      rewrite /allow_jmp_mem.
      rewrite !decide_True //=.

      (* Step 4: return all the resources we had *)
      iMod ((mem_map_recover_res_ie _ _ _ w wpc widc0 P P1 P2) with "HJmpMem Hmem") as "Ha"
      ; auto; iModIntro.

      case_decide as Ha0; simplify_eq.
      { (* a = a0 *)

        iDestruct "Ha" as "[Ha0 ->]".

        iMod ("Hcls" with "[HP Ha0]") as "_"; [iNext;iExists wpc;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        destruct wpc; cbn in Hi; try done.
        iExtract "Hmap" PC as "HPC".
        iApply interp_expr_invalid_pc; try iFrame ; eauto.
        intro Hcontra; inversion Hcontra ; simplify_eq.
        iPureIntro; apply regmap_full_dom in Hsome; rewrite -Hsome; set_solver.
      }

      case_decide as Ha0'; simplify_eq.
      { (* a = a0+1 *)

        iDestruct "Ha" as "(Ha0 & -> & HP1 & %Hpers1)".
        iDestruct "HP1" as "#HP1".

        iMod ("Hcls" with "[HP Ha0]") as "_"; [iNext;iExists widc0;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iApply ("Hexec" $! _ widc0) ; iFrame "∗ #".
        iRight; destruct widc0; cbn in Hi; try done.
        rewrite insert_commute //=.
        repeat (iSplit ; try done).
      }

      (* a ≠ a0 ∧ a ≠ a0+1 *)
      iDestruct "Ha" as "(Ha & HP1 & HP2 & %Hpers1 & %Hpers2)".
      iDestruct "HP1" as "#HP1"; iDestruct "HP2" as "#HP2".
      iMod ("Hcls" with "[HP Ha]") as "_"; [iNext;iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply "Hexec" ; iFrame "∗ #".
      rewrite insert_commute //=.
      repeat (iSplit ; try done).

    - (* fail *)
      rewrite /allow_jmp_mask_reg /allow_jmp_mem /allow_jmp_res.
      destruct (decide ((reg_allows_IEpair_jmp
                          (<[PC:=WCap p b e a]> (<[idc:=widc]> regs))
                          src p0 b0 e0 a0) /\ cond_jmp)) as [HallowJmp|_]
      ; cycle 1.
      {
        iModIntro.
        iDestruct "HJmpMem" as "->". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]") as "_";[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto; iIntros; discriminate.
      }

      assert ((a0 ^+ 1)%a ≠ a0) as Ha0eq
      by (destruct HallowJmp as
           [(_ & _ & Hwb%Is_true_true_1%withinBounds_true_iff & _) _]; solve_addr).

      (* Step 4: return all the resources we had *)
      iMod (mem_map_recover_res with "HJmpMem Hmem") as "Ha"; auto.

      iModIntro.
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|iModIntro].
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto; iIntros; discriminate.
    Qed.

End fundamental.
