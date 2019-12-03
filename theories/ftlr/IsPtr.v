From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.

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

  (*
  Lemma isptr_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (dst r0 : RegName) :
    ftlr_instr fs fr r p p' g b e a w (cap_lang.IsPtr dst r0).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst.
      specialize Hsome with r0 as Hr0. 
      destruct Hr0 as [wr0 Hsomesr0]. 
      iAssert ((if reg_eq_dec PC r0 then ▷ PC ↦ᵣ inr (p, g, b, e, a) else ▷ PC ↦ᵣ inr (p, g, b, e, a) ∗ ▷ r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[HPC Hmap]" as "[H Hmap]".
      { destruct (reg_eq_dec PC r0); iFrame.
        iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
        rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
      iApply (wp_IsPtr_fail_PC with "[Ha H]"); eauto; iFrame.
      iNext. iIntros "(H & Ha)".
      iApply wp_pure_step_later; auto.
      iAssert ([∗ map] k↦y ∈ <[PC:=inl (if reg_eq_dec PC r0 then 1%Z else match wr0 with inl _ => 0%Z | _ => 1%Z end)]> (if reg_eq_dec PC r0 then r else (<[r0:=wr0]> r)), k ↦ᵣ y)%I with "[H Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ PC) with "[H Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. iFrame.
        - iDestruct "H" as "[H1 H2]".
          iDestruct ((big_sepM_delete _ _ r0) with "[H2 Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[H1 Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. iFrame. }
      iApply wp_value.
      iNext. iIntros (Hcontr). inversion Hcontr. 
    * case_eq (a + 1)%a; intros.
      { destruct (reg_eq_dec PC r0).
        - subst r0.
          specialize Hsome with dst as Hdst. 
          destruct Hdst as [wdst Hsomesdst]. 
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
          rewrite (lookup_delete_ne _ PC dst); eauto.
          iApply (wp_IsPtr_successPC with "[$HPC $Ha $Hdst]"); eauto. 
          iNext. iIntros "(HPC & Ha & Hdst)".
          iApply wp_pure_step_later; auto.
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          iAssert (interp_registers _ (<[dst:=inl 1%Z]> r))
                    as "#[% Hreg']".
          { iSplitL.
            { iIntros (r0). iPureIntro.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
            iIntros (r0). iDestruct ("Hreg" $! (r0)) as "Hv".
            destruct Hsome with r0 as [c Hsomec].
            iIntros (Hnepc) "/=".
            rewrite /RegLocate.
            rewrite Hsomec. destruct (decide (dst = r0)); simplify_eq.
            * rewrite lookup_insert.
              repeat rewrite fixpoint_interp1_eq. simpl; eauto.
            * rewrite lookup_insert_ne. rewrite Hsomec. iApply "Hv"; auto.
              auto. }
          (* reestablish invariant *)
          iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
        - specialize Hsome with dst as Hdst. 
          destruct Hdst as [wdst Hsomesdst].
          specialize Hsome with r0 as Hr0. 
          destruct Hr0 as [wr0 Hsomer0]. 
          iAssert ((if reg_eq_dec r0 dst then ▷ r0 ↦ᵣ wr0 else ▷ r0 ↦ᵣ wr0 ∗ ▷ dst ↦ᵣ wdst) ∗ (if reg_eq_dec r0 dst then [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0dst Hmap]".
          { destruct (reg_eq_dec r0 dst).
            - subst dst. iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC r0); eauto. iFrame.
            - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC r0); eauto.
              iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
              rewrite (lookup_delete_ne _ r0 dst); eauto.
              rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
          iApply (wp_IsPtr_success with "[$HPC $Ha $Hr0dst]"); eauto.
          iNext. iIntros "(HPC & Ha & Hr0dst)".
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[r0:=inl match wr0 with | inl _ => 0%Z | inr _ => 1%Z end]> r else (<[r0:=wr0]> (<[dst:=inl match wr0 with | inl _ => 0%Z | inr _ => 1%Z end]> r))), k ↦ᵣ y)%I with "[Hr0dst HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec r0 dst).
            - iDestruct ((big_sepM_delete _ _ r0) with "[Hr0dst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              auto.
            - iDestruct "Hr0dst" as "[Hr0 Hdst]".
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto. rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              auto. }
          iAssert (interp_registers _ (if reg_eq_dec r0 dst
                        then <[r0:=inl match wr0 with
                                       | inl _ => 0%Z
                                       | inr _ => 1%Z
                                       end]> r
                        else <[r0:=wr0]> (<[dst:=inl match wr0 with
                                                     | inl _ => 0%Z
                                                     | inr _ => 1%Z
                                                     end]> r)))
                    as "#[% Hreg']".
          { iSplit.
            - iPureIntro.
              destruct (reg_eq_dec r0 dst); simpl.
              + subst r0. intros r1. destruct (reg_eq_dec dst r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto; rewrite Hsome; eauto.
              + intros r1. destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r1 dst); [subst; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto; rewrite Hsome; eauto].
            - iIntros (r1).
              specialize Hsome with r1 as Hr1. 
              destruct Hr1 as [c Hsomec].
              iIntros (Hnepc) "/=".
              iSpecialize ("Hreg" $! r1 Hnepc).  
              rewrite /RegLocate Hsomec.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert.
                  repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                * rewrite lookup_insert_ne; eauto. rewrite Hsomec. iApply "Hreg"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert.
                  rewrite Hsomec in Hsomer0; inv Hsomer0.
                  iApply "Hreg"; auto.
                * rewrite lookup_insert_ne; eauto.
                  destruct (reg_eq_dec r1 dst).
                  ** subst r1. rewrite lookup_insert.
                     repeat rewrite fixpoint_interp1_eq; simpl; eauto.
                  ** rewrite lookup_insert_ne; auto. rewrite Hsomec.
                     iApply "Hreg"; auto. }
          (* reestablish invariant *)
          iNext. iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
      } 
      { specialize Hsome with dst as Hdst. 
        destruct Hdst as [wdst Hsomesdst].
        specialize Hsome with r0 as Hr0. 
        destruct Hr0 as [wr0 Hsomer0]. 
        iAssert ((if reg_eq_dec r0 dst then ▷ r0 ↦ᵣ wr0 else if reg_eq_dec r0 PC then ▷ dst ↦ᵣ wdst else ▷ r0 ↦ᵣ wr0 ∗ ▷ dst ↦ᵣ wdst) ∗ (if reg_eq_dec r0 dst then [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y else if reg_eq_dec r0 PC then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y))%I with "[Hmap]" as "[H Hmap]".
      { destruct (reg_eq_dec r0 dst).
        - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hr0 Hmap]"; eauto.
          rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
        - destruct (reg_eq_dec r0 PC).
          + subst r0. iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hr0 Hmap]"; eauto.
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
          + iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
            rewrite (lookup_delete_ne _ PC r0); eauto. iFrame.
            iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
            rewrite (lookup_delete_ne _ r0 dst); eauto. rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
      iApply (wp_IsPtr_fail with "[$Ha $HPC $H]"); eauto. 
      iNext. iIntros "(HPC & Ha & H)".
      iApply wp_pure_step_later; auto.
      iAssert ([∗ map] k↦y ∈ (<[PC:=inr (p, g, b, e, a)]> (if reg_eq_dec r0 dst then <[r0:=inl match wr0 with inl _ => 0%Z | inr _ => 1%Z end]> r else (if reg_eq_dec r0 PC then <[dst:=inl 1%Z]> r else <[r0:= wr0]> (<[dst:=inl match wr0 with inl _ => 0%Z | inr _ => 1%Z end]> r)))), k ↦ᵣ y)%I with "[H HPC Hmap]" as "Hmap".
      { destruct (reg_eq_dec r0 dst).
        - subst dst. iDestruct ((big_sepM_delete _ _ r0) with "[H Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
        - destruct (reg_eq_dec r0 PC).
          + subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[H Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
          + iDestruct "H" as "[H1 H2]".
            iDestruct ((big_sepM_delete _ _ dst) with "[H2 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            repeat rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ r0) with "[H1 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
      iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
      } 
  Qed.*)

End fundamental.