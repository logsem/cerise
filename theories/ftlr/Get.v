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
  Lemma getL_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (dst r0 : RegName) :
    ftlr_instr fs fr r p p' g b e a w (cap_lang.GetL dst r0).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    specialize Hsome with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize Hsome with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetL_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0)".
      (* iDestruct (extract_from_region _ _ a with *)
      (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
      (* { iExists w. iFrame. iExact "Hva". } *)
      iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (encodeLoc g) else match wr0 with | inl _ => inr (p, g, b, e, a) | inr (_, g', _, _, _) => inl (encodeLoc g') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
          eapply lookup_insert.
          erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
        - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
      iAssert (interp_registers _ (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "#Hreg'".
      { iSplit.
        - iIntros (r1).
          iPureIntro. destruct (reg_eq_dec PC r0); auto.
          destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
        - iIntros (r1 Hnepc).
          iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
          specialize Hsome with r1 as [wr1 Hr1]. 
          destruct (reg_eq_dec PC r0); eauto.
          destruct (reg_eq_dec r0 r1).
          + subst r1. rewrite /RegLocate lookup_insert Hsomer0.
            iApply "Hv"; auto.
          + rewrite /RegLocate lookup_insert_ne; auto. }
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
    } 
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetL_success with "[$Hr0 $HPC $Hdst $Ha]"); eauto.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (<[dst:=inl (encodeLoc g)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl.
          iAssert (interp_registers _ (<[dst:=inl (encodeLoc g)]> r)) as "#[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [wr1 Hr1]. 
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p0, p0, p0. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (encodeLoc l)]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl (encodeLoc l)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
            iAssert (interp_registers (fs,fr) (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "#[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [w0 Hsome]. 
              rewrite /RegLocate.
              rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
            iNext.
            iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
      - iApply (wp_GetL_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr.
    }
    Unshelve.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _. 
  Qed. 

  Lemma getP_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (dst r0 : RegName) :
    ftlr_instr fs fr r p p' g b e a w (cap_lang.GetP dst r0).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    specialize Hsome with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize Hsome with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetP_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0)".
      (* iDestruct (extract_from_region _ _ a with *)
      (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
      (* { iExists w. iFrame. iExact "Hva". } *)
      iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (encodePerm p) else match wr0 with | inl _ => inr (p, g, b, e, a) | inr (p, _, _, _, _) => inl (encodePerm p) end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
          eapply lookup_insert.
          erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
        - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
      iAssert (interp_registers _ (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "#Hreg'".
      { iSplit.
        - iIntros (r1).
          iPureIntro. destruct (reg_eq_dec PC r0); auto.
          destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
        - iIntros (r1 Hnepc).
          iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
          specialize Hsome with r1 as [wr1 Hr1]. 
          destruct (reg_eq_dec PC r0); eauto.
          destruct (reg_eq_dec r0 r1).
          + subst r1. rewrite /RegLocate lookup_insert Hsomer0.
            iApply "Hv"; auto.
          + rewrite /RegLocate lookup_insert_ne; auto. }
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
    } 
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetP_success with "[$Hr0 $HPC $Hdst $Ha]"); eauto.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (<[dst:=inl (encodePerm p)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl.
          iAssert (interp_registers _ (<[dst:=inl (encodePerm p)]> r)) as "#[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [wr1 Hr1]. 
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p0, p0, p0. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (encodePerm p0)]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl (encodePerm p0)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
            iAssert (interp_registers (fs,fr) (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "#[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [w0 Hsome]. 
              rewrite /RegLocate.
              rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
            iNext.
            iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
      - iApply (wp_GetP_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr.
    }
    Unshelve.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _. 
  Qed.

  Lemma getB_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (dst r0 : RegName) :
    ftlr_instr fs fr r p p' g b e a w (cap_lang.GetB dst r0).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    specialize Hsome with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize Hsome with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetB_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0)".
      (* iDestruct (extract_from_region _ _ a with *)
      (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
      (* { iExists w. iFrame. iExact "Hva". } *)
      iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (z_of b) else match wr0 with | inl _ => inr (p, g, b, e, a) | inr (_, _, b', _, _) => inl (z_of b') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
          eapply lookup_insert.
          erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
        - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
      iAssert (interp_registers _ (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "#Hreg'".
      { iSplit.
        - iIntros (r1).
          iPureIntro. destruct (reg_eq_dec PC r0); auto.
          destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
        - iIntros (r1 Hnepc).
          iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
          specialize Hsome with r1 as [wr1 Hr1]. 
          destruct (reg_eq_dec PC r0); eauto.
          destruct (reg_eq_dec r0 r1).
          + subst r1. rewrite /RegLocate lookup_insert Hsomer0.
            iApply "Hv"; auto.
          + rewrite /RegLocate lookup_insert_ne; auto. }
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
    } 
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetB_success with "[$Hr0 $HPC $Hdst $Ha]"); eauto.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (<[dst:=inl (z_of b)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl.
          iAssert (interp_registers _ (<[dst:=inl (z_of b)]> r)) as "#[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [wr1 Hr1]. 
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p0, p0, p0. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a3)]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl (z_of a3)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                destruct a3; simpl. iFrame "Hmap".
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                destruct a3; auto. 
            } 
            iAssert (interp_registers (fs,fr) (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "#[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [w0 Hsome]. 
              rewrite /RegLocate.
              rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
            iNext.
            iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
      - iApply (wp_GetB_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr.
    }
    Unshelve.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _. 
  Qed.

  Lemma getE_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (dst r0 : RegName) :
    ftlr_instr fs fr r p p' g b e a w (cap_lang.GetE dst r0).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    specialize Hsome with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize Hsome with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetE_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0)".
      (* iDestruct (extract_from_region _ _ a with *)
      (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
      (* { iExists w. iFrame. iExact "Hva". } *)
      iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (z_of e) else match wr0 with | inl _ => inr (p, g, b, e, a) | inr (_, _, _, e', _) => inl (z_of e') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
          eapply lookup_insert.
          erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
        - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
      iAssert (interp_registers _ (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "#Hreg'".
      { iSplit.
        - iIntros (r1).
          iPureIntro. destruct (reg_eq_dec PC r0); auto.
          destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
        - iIntros (r1 Hnepc).
          iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
          specialize Hsome with r1 as [wr1 Hr1]. 
          destruct (reg_eq_dec PC r0); eauto.
          destruct (reg_eq_dec r0 r1).
          + subst r1. rewrite /RegLocate lookup_insert Hsomer0.
            iApply "Hv"; auto.
          + rewrite /RegLocate lookup_insert_ne; auto. }
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
    } 
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetE_success with "[$Hr0 $HPC $Hdst $Ha]"); eauto.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (<[dst:=inl (z_of e)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl.
          iAssert (interp_registers _ (<[dst:=inl (z_of e)]> r)) as "#[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [wr1 Hr1]. 
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p0, p0, p0. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a2)]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl (z_of a2)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
            } 
            iAssert (interp_registers (fs,fr) (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "#[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [w0 Hsome]. 
              rewrite /RegLocate.
              rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
            iNext.
            iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
      - iApply (wp_GetE_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr.
    }
    Unshelve.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _. 
  Qed.

  Lemma getA_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (dst r0 : RegName) :
    ftlr_instr fs fr r p p' g b e a w (cap_lang.GetA dst r0).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    specialize Hsome with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize Hsome with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetA_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0)".
      (* iDestruct (extract_from_region _ _ a with *)
      (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
      (* { iExists w. iFrame. iExact "Hva". } *)
      iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (z_of a) else match wr0 with | inl _ => inr (p, g, b, e, a) | inr (_, _, _, _, a') => inl (z_of a') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
          eapply lookup_insert.
          erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
        - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
      iAssert (interp_registers _ (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "#Hreg'".
      { iSplit.
        - iIntros (r1).
          iPureIntro. destruct (reg_eq_dec PC r0); auto.
          destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
        - iIntros (r1 Hnepc).
          iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
          specialize Hsome with r1 as [wr1 Hr1]. 
          destruct (reg_eq_dec PC r0); eauto.
          destruct (reg_eq_dec r0 r1).
          + subst r1. rewrite /RegLocate lookup_insert Hsomer0.
            iApply "Hv"; auto.
          + rewrite /RegLocate lookup_insert_ne; auto. }
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
    } 
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetA_success with "[$Hr0 $HPC $Hdst $Ha]"); eauto.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (<[dst:=inl (z_of a)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl.
          iAssert (interp_registers _ (<[dst:=inl (z_of a)]> r)) as "#[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [wr1 Hr1]. 
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p0, p0, p0. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (p, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a1)]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl (z_of a1)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
            } 
            iAssert (interp_registers (fs,fr) (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p0, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "#[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize Hsome with r1 as [w0 Hsome]. 
              rewrite /RegLocate.
              rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
            iNext.
            iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
      - iApply (wp_GetA_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr.
    }
    Unshelve.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _. 
  Qed.*)

End fundamental.