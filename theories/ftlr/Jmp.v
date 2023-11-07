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


  (*--------------------- Attempts ---------------------*)

  Definition reg_allow_IE (regs : Reg) (r : RegName) (p : Perm) (b e a : Addr) :=
    regs !! r = Some (WCap p b e a) ∧
    p = IE /\
    withinBounds b e a = true ∧
    withinBounds b e (a ^+1)%a = true.

  (* Mask after the jump, depending on the address of the pc and the address
   of a *)
  Definition mask_jmp (pc_a a : Addr) : coPset
    :=
    if decide (pc_a = a)
    then (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@(a^+1)%a)
    else
      if decide (pc_a = (a^+1)%a)
      then (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a)
      else (⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a ∖ ↑logN.@(a^+1)%a).

  Definition mask_jmp_reg (regs : Reg) (r : RegName) (pc_a : Addr) (p : Perm) (b e a : Addr)
    : coPset :=
    if decide (reg_allow_IE regs r p b e a)
    then mask_jmp pc_a a
    else (⊤ ∖ ↑logN.@pc_a).

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately *)
  Definition region_open_resources2
    (pc_a : Addr) (a : Addr)
    (w1 : Word) (w2 : Word)
    (P1 P2 : D)
    : iProp Σ :=
    (▷ P1 w1 ∗ ▷ P2 w2
       ∗ ((▷ ∃ w1 w2, a ↦ₐ w1 ∗ P1 w1 ∗ (a^+1)%a ↦ₐ w2 ∗ P2 w2)
          ={mask_jmp pc_a a, ⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Definition region_open_resources
    (pc_a : Addr) (a : Addr) (w : Word)
    (P : D)
    : iProp Σ :=
    (▷ P w ∗
       ((▷ ∃ w, a ↦ₐ w ∗ P w)
        ={mask_jmp pc_a a, ⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Definition region_open_resources'
    (pc_a : Addr) (a : Addr) (w' : Word)
    (P : D)
    : iProp Σ :=
    (▷ P w' ∗
       ((▷ ∃ w', (a^+1)%a ↦ₐ w' ∗ P w')
        ={mask_jmp pc_a a, ⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  (* Description of what the resources are supposed to look like after opening the
     region if we need to, but before closing the region up again*)
  Definition allow_IE_res (regs : Reg) (r : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr)
    (P1 P2 : D) : iProp Σ :=
    (⌜read_reg_inr regs r p b e a⌝ ∗

       if decide (reg_allow_IE regs r p b e a)
       then
         |={⊤ ∖ ↑logN.@pc_a, mask_jmp pc_a a}=>
           (if decide (pc_a = a)
            then ∃ w2, (a^+1)%a ↦ₐ w2 ∗ region_open_resources' pc_a a w2 P2
            else
              if decide (pc_a = (a^+1)%a)
              then ∃ w1, a ↦ₐ w1 ∗ region_open_resources pc_a a w1 P1
              else ∃ w1 w2, a ↦ₐ w1 ∗ (a^+1)%a ↦ₐ w2 ∗ region_open_resources2 pc_a a w1 w2 P1 P2
           )
       else True)%I.

  Definition allow_IE_mem
    (regs : Reg) (r : RegName)
    (pc_a : Addr) (pc_w : Word) (mem : Mem) (p : Perm) (b e a : Addr) (P1 P2 : D) :=
    (⌜read_reg_inr regs r IE b e a⌝ ∗
       if decide (reg_allow_IE regs r p b e a)
       then (if decide (pc_a = a)
             then ∃ w2, ⌜mem = <[(a^+1)%a:=w2]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources' pc_a a w2 P2
             else
               if decide (pc_a = (a^+1)%a)
               then ∃ w1, ⌜mem = <[a:=w1]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources pc_a a w1 P1
               else ∃ w1 w2,
                   ⌜mem = <[(a^+1)%a:=w2]> (<[a:=w1]> (<[pc_a:=pc_w]> ∅))⌝
                                             ∗ region_open_resources2 pc_a a w1 w2 P1 P2)
       else ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma create_IE_res:
    ∀ (regs : leibnizO Reg) (r : RegName)
      (pc_p : Perm) (pc_b pc_e pc_a : Addr)
      (widc : Word)
      (p : Perm) (b e a : Addr),
      read_reg_inr (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:= widc]> regs)) r p b e a
      → (∀ (r' : RegName) (w : Word), ⌜r' ≠ PC⌝ → ⌜r' ≠ idc⌝ → ⌜regs !! r' = Some w⌝ → (fixpoint interp1) w)
        -∗ interp widc
        -∗ ∃ (P1 P2 : D),
             allow_IE_res (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:=widc]> regs)) r pc_a p b e a P1 P2.
  Proof.
    intros regs r pc_p pc_b pc_e pc_a widc p b e a HVr.
    iIntros "#Hreg #Hwidc".
    iFrame "%".
    case_decide as Hallows; cycle 1.
    - by iExists (λne _, True%I), (λne _, True%I).
    - rewrite /mask_jmp.
      destruct Hallows as (Hreg & -> & Hwb & Hwb').
      assert (a <> (a^+1)%a) by (apply andb_prop in Hwb as [_ Hge]; solve_addr).
      apply Is_true_true_2 in Hwb, Hwb'.
      assert ( withinBounds b e a /\ withinBounds b e (a^+1)%a) as Hwbs by auto.
      case_decide as Ha; simplify_eq.
      {
      admit.
      }
      apply neq_Symmetric in Ha.
      assert (r ≠ PC) as Hneq.
      { refine (addr_ne_reg_ne Hreg _ Ha). by simplify_map_eq. }

      case_decide as Ha'; simplify_eq.
      {
      admit.
      }

      (* apply andb_prop in Hwb as [Hle Hge]. *)
      (* revert Hle Hge. rewrite !Z.leb_le Z.ltb_lt =>Hle Hge. *)
      (* apply andb_prop in Hwb' as [Hle' Hge']. *)
      (* revert Hle' Hge'. rewrite !Z.leb_le Z.ltb_lt =>Hle' Hge'. *)


      rewrite lookup_insert_ne //= in Hreg.
      destruct (decide (r = idc)) as [|Hneq']; simplify_map_eq.
      + rewrite fixpoint_interp1_eq /=.
        iDestruct ("Hwidc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & _)".
        iExists P1, P2.

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
        rewrite /mask_jmp.
        case_decide; simplify_eq.
        case_decide; simplify_eq.
        iMod ("Hcls_a'" with "[Hw2' HP2']") as "_"; first (iExists _ ; iFrame).
        iMod ("Hcls_a" with "[Hw1' HP1']") as "_"; first (iExists _ ; iFrame).
        done.
      + iDestruct ("Hreg" $! r _ Hneq Hneq' Hreg) as "Hvsrc".
        rewrite (fixpoint_interp1_eq (WCap _ _ _ _)) /=.
        iDestruct ("Hvsrc" $! Hwbs) as (P1 P2) "(Hpers_P1 & Hpers_P2 & Hinv_a & Hinv_a' & _)".
        iExists P1, P2.

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
        rewrite /mask_jmp.
        case_decide; simplify_eq.
        case_decide; simplify_eq.
        iMod ("Hcls_a'" with "[Hw2' HP2']") as "_"; first (iExists _ ; iFrame).
        iMod ("Hcls_a" with "[Hw1' HP1']") as "_"; first (iExists _ ; iFrame).
        done.
  Admitted.

  (*--------------------- Defs from rules_jmp.v ---------------------*)
  (* Definition allow_load_addr_or_true (b e a : Addr) (mem : Mem):= *)
  (*   if decide (withinBounds b e a = true) *)
  (*   then ∃ w, mem !! a = Some w *)
  (*   else True. *)

  (* Definition allow_IE_map_or_true (r : RegName) (regs : Reg) (mem : Mem) := *)
  (*   ∃ p b e a, *)
  (*     read_reg_inr regs r p b e a ∧ (* unify the content of `r` with cap (p,b,e,a) *) *)
  (*       allow_load_addr_or_true b e a mem /\ (* b ≤ a < e, and mem(a) = w *) *)
  (*       allow_load_addr_or_true b e (a^+1)%a mem. *)

  (* Definition allow_IE_cap (r : RegName) (regs : Reg) (mem : Mem) := *)
  (*   forall wr, regs !! r = Some wr -> *)
  (*         is_ie_cap wr -> *)
  (*         is_Some (regs !! idc) /\ allow_IE_map_or_true r regs mem. *)


  (*--------------------- Defs from rules_jmp.v ---------------------*)

  (* Definition reg_allows_store (regs : Reg) (r : RegName) p b e a := *)
  (*   regs !! r = Some (WCap p b e a) ∧ *)
  (*   writeAllowed p = true ∧ withinBounds b e a = true. *)

        (* if decide (reg_allows_store r r1 p1 b1 e1 a0 ∧ a0 ≠ a) *)
        (* then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0 *)
        (* else ⊤ ∖ ↑logN.@a}=∗ *)
        (*                      ∃ mem0 : gmap Addr Word, *)


  (*--------------------- Lemma ---------------------*)

  Lemma jmp_case (regs : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (src : RegName) (P : D):
    ftlr_instr regs p b e a widc w (Jmp src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #Hread Hown Ha HP Hcls HPC HIDC Hmap".
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

    (* Step 1: open the region, if necessary, and store all the resources
       obtained from the region in allow_IE_res *)
    iDestruct (create_IE_res with "Hreg Hinv_idc") as (P1 P2) "HJmpRes"; eauto.

    (* WIP.... *)

    Admitted.


    destruct (decide (src = PC)); simplify_map_eq.
    - iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame.
      iNext. iIntros "[HPC Ha] /=".
      (* reconstruct invariant *)
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|].
      iModIntro.
      iApply wp_pure_step_later; auto.
      (* reconstruct registers *)
      iNext. iIntros "_".
      iInsert "Hmap" PC.
      iApply ("IH" $! _ _ b e a with "[] [] [Hmap] [$Hown]"); eauto.
      { iPureIntro. apply Hsome. }
      destruct Hp as [-> | ->]; iFrame; by rewrite insert_commute.

    - destruct (decide (src = idc)); simplify_map_eq.
      + admit. (* TODO need the wp_rule.... *)
      + iInsertList "Hmap" [PC].
        iAssert ([∗ map] k↦x ∈ (<[a := w]> ∅), k ↦ₐ x)%I with "[Ha]" as "Hmem".
        { iApply (big_sepM_insert with "[Ha]"); auto ; iFrame. }


        specialize Hsome with src as Hsrc.
        destruct Hsrc as [wsrc Hsomesrc].
        iExtractList "Hmap" [src;idc] as ["Hsrc";"Hidc"].
        iAssert (fixpoint interp1 wsrc) as "#Hinv_src"; first (iApply "Hreg"; eauto).
        destruct (decide (is_ie_cap wsrc = true)) as [Hie|Hie].
        * (* EI cap *)
          destruct wsrc as [ | [ [] b' e' a' | ] | ]; cbn in Hie ; try done; clear Hie.
          (* open the invariants *)
          rewrite (fixpoint_interp1_eq (WCap IE _ _ _)) //=.
          destruct (decide (withinBounds b' e' a' ∧ withinBounds b' e' (a' ^+ 1)%a)) as
            [Hdec_wb|Hdec_wb].
          {
            iDestruct ("Hinv_src" $! Hdec_wb)
              as (P1 P2) "(%Hcond_Pa1 & %Hcond_Pa2 & Hinv_a1 & Hinv_a2 & Hexec)";
              iClear "Hinv_src".
            (* TODO we can probably encode the disjunction in a better way *)
            destruct Hdec_wb as [ Hwb%Is_true_true_1 Hwb'%Is_true_true_1].
            assert (a' ≠ (a' ^+1)%a) by (rewrite withinBounds_true_iff in Hwb'; solve_addr).


            destruct (decide (a = a')) as [Haeq|Haeq];
              destruct (decide (a = (a' ^+1)%a)) as [Haeq'|Haeq'].
            ** (* a' = a , a = a ^+ 1*) solve_addr.
            ** (* a' = a , a ≠ a ^+ 1*) admit.
            ** (* a' ≠ a , a = a ^+ 1*) admit.
            ** (* a' ≠ a , a ≠ a ^+ 1*)
              iInv "Hinv_a1" as (w1) "[>Ha1 #HPa1]" "Hcls_a1".
              iInv "Hinv_a2" as (w2) "[>Ha2 #HPa2]" "Hcls_a2".

              iApply (wp_jmp_success_IE with "[$HPC $Hsrc $Hidc $Ha $Ha1 $Ha2]"); eauto.
              iNext. iIntros "(HPC & Hsrc & Hidc & Ha & Ha1 & Ha2) /=".
              iApply wp_pure_step_later; auto.

              iMod ("Hcls_a2" with "[Ha2 HPa2]") as "_";[iExists w2; iFrame; iFrame "#"|iModIntro].
              iMod ("Hcls_a1" with "[Ha1 HPa1]") as "_";[iExists w1; iFrame; iFrame "#"|iModIntro].
              iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|iModIntro].
              iNext ; iIntros "_".

              (* Needed because IH disallows non-capability values *)
              destruct w1 as [ | [p0 b0 e0 a0 | ] | ]; cycle 1.
              {
                iApply "Hexec"; iFrame "#"; iFrame.
              (* iApply ("IH" with "[] [] [Hmap] [Hown]"). *)
                iInsertList "Hmap" [idc;PC].
                iDestruct (big_sepM_insert _ _ src with "[$Hmap $Hsrc]") as "Hmap".
                rewrite lookup_insert_ne //= lookup_insert_ne //=.
                apply lookup_delete; auto.
                rewrite
                  (insert_commute _ src) //=
                    (insert_commute _ src) //=
                    insert_delete //=
                    insert_commute //=.
                iFrame.
                iIntros (r'). iPureIntro ; apply Hsome.
              }

              (* Non-capability cases *)
              all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
                iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ].
              all: repeat iNext; iIntros "HPC /=".
              all: iApply wp_pure_step_later; auto.
              all: iNext; iIntros "_".
              all: iApply wp_value.
              all: iIntros; discriminate.
          }
          { (* fail case *)
            admit.
          }
        * (* TODO not EI-cap, works as before *) admit.
  Admitted.

End fundamental.
