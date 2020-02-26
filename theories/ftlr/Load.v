From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_Load.
Require Import Coq.Logic.Decidable.
Import uPred.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately
   The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources W l ls p φ v (bl : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std (countable.encode l) ρ
    ∗ ⌜ρ ≠ Revoked⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ (if bl then monotonicity_guarantees_region ρ v p φ ∗ φ (W, v)
       else ▷ monotonicity_guarantees_region ρ v p φ ∗  ▷ φ (W, v) )
    ∗ rel l p φ)%I.


  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_load_res_or_true W r (regs : Reg) pc_a pc_p:=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a ) then
       if decide (a ≠ pc_a) then
         ∃ p' w, a ↦ₐ [p'] w  ∗ ⌜PermFlows p p'⌝ ∗ (region_open_resources W a [pc_a] p' interpC w false)
       else ⌜PermFlows p pc_p⌝ ∗ open_region pc_a W
      else open_region pc_a W)%I.

  Definition allow_load_mem_or_true W r (regs : Reg) pc_a pc_p pc_w (mem : PermMem) (bl: bool):=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a) then
       if decide (a ≠ pc_a) then
         ∃ p' w, ⌜mem = <[a:=(p',w)]> (<[pc_a:=(pc_p,pc_w)]> ∅)⌝ ∗
            ⌜PermFlows p p'⌝ ∗ (region_open_resources W a [pc_a] p' interpC w bl)
       else  ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ ⌜PermFlows p pc_p⌝ ∗ open_region pc_a W     else  ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ open_region pc_a W)%I.

  Lemma load_case(W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst src : RegName) :
    ftlr_instr W r p p' g b e a w (Load dst src) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* Handy to read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=inr (p, g, b, e, a)]> r !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1*)
    specialize Hsome' with src as Hsrc.
    destruct Hsrc as [wsrc Hsomesrc].
    assert (∃ p0 g0 b0 e0 a0 , read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) src p0 g0 b0 e0 a0) as [p0 [g0 [b0 [e0 [a0 HVsrc] ] ] ] ].
    {
      unfold read_reg_inr. destruct wsrc. 2: destruct c,p0,p0,p0. all: repeat eexists.
      right. by exists z.
      by left.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res_or_true *)
    iAssert (allow_load_res_or_true W src (<[PC:=inr (p, g, b, e, a)]> r) a p' ∗ sts_full_world sts_std W)%I with "[Hr Hsts]" as "[HLoadRes Hsts]".
    {
      unfold allow_load_res_or_true.
      do 5 (iApply sep_exist_r; iExists _). iFrame "%".
      destruct (decide (reg_allows_load (<[PC:=inr (p, g, b, e, a)]> r) src p0 g0 b0 e0 a0)). 1: rename r0 into Hallows.

      -  destruct Hallows as [Hrinr [Hra Hwb] ].
         destruct (decide (a0 ≠ a)); rename n into Haeq.
         * apply andb_prop in Hwb as [Hle Hge].
           rewrite /leb_addr in Hle,Hge.

           (* Unlike in the old proof, we now go the other way around, and prove that the source register could not have been the PC, since both addresses differ. This saves us some cases.*)
           assert (src ≠ PC) as n.
           {
             intros contra. rewrite contra in Hrinr.
             rewrite lookup_insert in Hrinr. inversion Hrinr. congruence.
           }

           iDestruct ("Hreg" $! src n) as "Hvsrc".
           rewrite lookup_insert_ne in Hrinr; last by congruence.
           rewrite /RegLocate Hrinr.
           iDestruct (read_allowed_inv _ a0 with "Hvsrc") as "Hconds"; auto;
            first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).

          rewrite /read_write_cond.
          iDestruct "Hconds" as (p0' Hfl') "Hrel'".
          iDestruct (region_open_prepare with "Hr") as "Hr".
          iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as "%"; eauto.
          { rewrite /withinBounds /leb_addr Hle Hge. auto. }
          destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
          (*We can finally frame off Hsts here, since it is no longer needed after opening the region*)
          iDestruct (region_open_next _ _ _ a0 p0' ρ' with "[$Hrel' $Hr $Hsts]") as (w0) "($ & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists p0', w0. iSplitL "Ha0"; auto. iSplitR; auto. unfold region_open_resources.
          iExists ρ'. iFrame "%". iFrame. by iFrame "#".
        * iFrame.
          destruct (decide (src = PC)) ; simplify_eq.
          + rewrite lookup_insert in Hrinr.
            inversion Hrinr. rewrite -H4. auto.
          +  iDestruct ("Hreg" $! src n) as "Hsrcv".
             rewrite lookup_insert_ne in Hrinr; last by congruence.
             rewrite /RegLocate Hrinr.
             iDestruct (read_allowed_inv _ a0 with "Hsrcv") as (p'' Hfl') "#Harel'".
             { apply andb_true_iff in Hwb as [Hle Hge].
               split; [by apply Z.leb_le | by apply Z.ltb_lt]; auto. }
             { destruct p0; inversion Hra; auto. }
             rewrite /read_write_cond.
             assert (a0 = a). by apply dec_stable.
             rewrite -H3.
             by iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
      - iFrame.
    }
    (* Clear helper values; they exist in the existential now *)
    clear HVsrc p0 g0 b0 e0 a0.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iAssert (∃mem, allow_load_mem_or_true W src (<[PC:=inr (p, g, b, e, a)]> r) a p' w mem false ∗ (▷ [∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) )%I with "[HLoadRes Ha]" as (mem) "[HLoadMem HMemRes]".
    {
      unfold allow_load_res_or_true. iDestruct "HLoadRes" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
      unfold allow_load_mem_or_true.
      iAssert (∃ (p1 : Perm) (w1 : leibnizO Word), ⌜(p',w) = (p1, w1)⌝ ∗ a ↦ₐ[p1] w1)%I with "[Ha]" as "Ha". iExists p',w. auto.

      case_decide as Hallows.
      -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
         case_decide as Haeq.
         * iDestruct "HLoadRes" as (p'0 w0) "[HLoadCh HLoadRest]".
           iExists (<[a1:=(p'0, w0)]> (<[a:=(p', w)]> ∅)).

           iSplitL "HLoadRest".
           + iExists p1,g1,b1,e1,a1. iSplitR; first auto.
             do 2 (case_decide; last by exfalso).
             iExists p'0,w0. iSplitR; auto.
           + iNext.
             iAssert (∃ (p1 : Perm) (w1 : leibnizO Word), ⌜(p'0,w0) = (p1, w1)⌝ ∗ a1 ↦ₐ[p1] w1)%I with "[HLoadCh]" as "HLoadCh". iExists p'0,w0. by iSplitR.

             rewrite (big_sepM_insert _ _).
             rewrite (big_sepM_insert _ _).
             iFrame. rewrite (big_opM_empty). auto.
             ++ auto.
             ++ rewrite lookup_insert_ne; auto.
         * iExists ( <[a:=(p', w)]> ∅).
           iSplitL "HLoadRes".
           + iExists p1,g1,b1,e1,a1. iSplitR; auto.
             case_decide; last by exfalso. case_decide; first by exfalso.
             iDestruct "HLoadRes" as (HPF) "HLoadRes". iSplitR; auto.
           + iNext. rewrite (big_sepM_insert _ _ a (p',w)).
             iFrame.  rewrite (big_opM_empty). all: auto.
      - iExists ( <[a:=(p', w)]> ∅).
        iSplitL "HLoadRes".
        + iExists p1,g1,b1,e1,a1. iSplitR; auto.
          case_decide; first by exfalso. auto.
        + iNext. rewrite (big_sepM_insert _ _ a (p',w)).
          iFrame. rewrite (big_opM_empty). all: auto.
    }

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iAssert (⌜mem !! a = Some (p', w)⌝ ∗ ⌜allow_load_map_or_true src (<[PC:=inr (p, g, b, e, a)]> r) mem⌝)%I with "[HLoadMem]" as %(HReadPC & HLoadAP).
    {
      unfold allow_load_mem_or_true.
      iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
      unfold allow_load_map_or_true.
      case_decide as Hallows.
      -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
         case_decide as Haeq.
         * iDestruct "HLoadRes" as (p'0 w0 ->) "[% _]".
           iSplitR. rewrite lookup_insert_ne; auto. by rewrite lookup_insert.
           iExists p1,g1,b1,e1,a1. iSplitR; auto.
           case_decide; last by exfalso.
           iExists p'0,w0. iSplitR; auto.
           by rewrite lookup_insert.
         * iDestruct "HLoadRes" as "[-> [% HLoadRes] ]".
           iSplitR. by rewrite lookup_insert.
           iExists p1,g1,b1,e1,a1. iSplitR; auto.
           case_decide; last by exfalso.
           iExists p',w. by rewrite Haeq lookup_insert.
      - iDestruct "HLoadRes" as "[-> HLoadRes]".
        iSplitR. by rewrite lookup_insert.
        iExists p1,g1,b1,e1,a1. iSplitR; auto.
        case_decide; first by exfalso. auto.
    }

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iAssert (▷ allow_load_mem_or_true W src (<[PC:=inr (p, g, b, e, a)]> r) a p' w mem true)%I with "[HLoadMem]" as "HLoadMem".
    {
      unfold allow_load_mem_or_true.
      iDestruct "HLoadMem" as (p0 g0 b0 e0 a0) "[% HLoadMem]".
      do 5 (iApply later_exist_2; iExists _). iApply later_sep_2; iSplitR; auto.
      case_decide.
      - case_decide.
        * iDestruct "HLoadMem" as (p'0 w0) "[-> [% HLoadMem] ]".
        do 2 (iApply later_exist_2; iExists _).
        do 2 (iApply later_sep_2; iSplitR; auto).
        * iFrame.
      - iFrame.
    }

    iApply (wp_load with "[Hmap HMemRes]"); eauto.
    {by rewrite lookup_insert. }
    {iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [|].
    { subst retv.
      apply incrementPC_Some_inv in H6.
      destruct H6 as (?&?&?&?&?&?&?&?&?).

      iApply wp_pure_step_later; auto. iNext.

      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iAssert (open_region a W ∗ a ↦ₐ[p'] w ∗ ((fixpoint interp1) W) loadv)%I with "[HLoadMem Hmem]" as "[Hr [Ha #HLVInterp ] ]".
      {
        unfold allow_load_mem_or_true.
        iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
        destruct (decide (reg_allows_load (<[PC:=inr (p, g, b, e, a)]> r) src p1 g1 b1 e1 a1)). 1: rename r0 into Hallows.
        -  destruct Hallows as [Hrinr [Hra Hwb] ].
           destruct (decide (a1 ≠ a)); rename n into Haeq.
           * iDestruct "HLoadRes" as (p'1 w0) "[-> [% HLoadRes] ]".
             iDestruct "HLoadRes" as (ρ1) "(Hstate' & % & Hr & % & (Hfuture & #HV) & Hrel')".
             iAssert ( a ↦ₐ[p'] w ∗ a1 ↦ₐ[p'1] w0)%I  with "[Hmem]" as "[$ Ha1]".
             {
               rewrite (big_sepM_insert); last by rewrite lookup_insert_ne.
               rewrite (big_sepM_insert); last by auto.
               iDestruct "Hmem" as "[Ha1 [Ha _] ]".
               iSplitL "Ha".
               * iDestruct "Ha" as (p2 w1 Hpair) "Ha".
                   by inversion Hpair.
               * iDestruct "Ha1" as (p2 w1 Hpair) "Ha".
                   by inversion Hpair.
             }
             iDestruct (region_close_next with "[$Hr $Ha1 $Hrel' $Hstate' $Hfuture]") as "Hr"; eauto.
             { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
             iDestruct (region_open_prepare with "Hr") as "$".
             destruct H4 as (Hrinr0 & _ & _). rewrite Hrinr0 in Hrinr; inversion Hrinr.
             rewrite H16 lookup_insert in H5; inversion H5. done.
           * apply dec_stable in Haeq.
             iDestruct "HLoadRes" as "[-> [% $ ] ]".
             iAssert ( a ↦ₐ[p'] w)%I  with "[Hmem]" as "$".
             {
               rewrite (big_sepM_insert); last by auto.
               iDestruct "Hmem" as "[Ha _]".
               iDestruct "Ha" as (p2 w1 Hpair) "Ha".
                 by inversion Hpair.
             }
             destruct H4 as (Hrinr0 & _ & _). rewrite Hrinr0 in Hrinr; inversion Hrinr.
             rewrite H14 Haeq lookup_insert in H5; inversion H5. done.
        - pose (H4' := H4).
          destruct H4' as (Hinr0 & _ & _). destruct H8 as [Hinr1 | Hinl1].
          * rewrite Hinr0 in Hinr1. inversion Hinr1.
            rewrite H9 H10 H11 H12 H13 in H4. by exfalso.
          * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
      }

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC*)
      destruct (decide (x = RX ∨ x = RWX ∨ x = RWLX)).
      2 : {
        assert (x ≠ RX ∧ x ≠ RWX ∧ x ≠ RWLX). split; last split; by auto.
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { rewrite H7. by rewrite lookup_insert. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext. iApply wp_value.
        iIntros (a1); inversion a1.
      }

      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      iApply ("IH" $! _ regs' with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]").
      { cbn. intros. subst regs'.
        rewrite lookup_insert_is_Some.
        destruct (decide (PC = x5)); [ auto | right; split; auto].
        rewrite lookup_insert_is_Some.
        destruct (decide (dst = x5)); [ auto | right; split; auto]. }
      (* Prove in the general case that the value relation holds for the register that was loaded to - unless it was the PC.*)
       { iIntros (ri Hri).
        subst regs'.
        erewrite locate_ne_reg; [ | | reflexivity]; auto.
        destruct (decide (ri = dst)).
        { subst ri.
          erewrite locate_eq_reg; [ | reflexivity]; auto.
        }
        { repeat (erewrite locate_ne_reg; [ | | reflexivity]; auto).
          iApply "Hreg"; auto. }
       }
       { subst regs'. rewrite insert_insert. iApply "Hmap". }
       { destruct (decide (PC = dst)); simplify_eq.
         - destruct o as [HRX | [HRWX | HRWLX] ]; auto.
           rewrite lookup_insert in H3; inversion H3. rewrite HRWLX.
           iDestruct (writeLocalAllowed_implies_local _ RWLX with "[HLVInterp]") as "%"; auto.
           destruct x0; unfold isLocal in H7; first by congruence.
           iPureIntro; do 2 right; auto.
         - rewrite lookup_insert_ne in H3; last by auto. rewrite lookup_insert in H3; inversion H3.
           by rewrite -H8 -H9.
       }
       { iAlways. auto.
         destruct (decide (PC = dst)); simplify_eq.
         - rewrite lookup_insert in H3; inversion H3. rewrite (fixpoint_interp1_eq W).
           iApply readAllowed_implies_region_conditions; auto.
           { destruct o as [o | [o | o] ]; rewrite o; auto . }
         - iExists p'. rewrite lookup_insert_ne in H3; last by auto. rewrite lookup_insert in H3; inversion H3. iSplitR; first by rewrite -H8. auto.
       }
    }
    { subst retv.
      iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

End fundamental.
