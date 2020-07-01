From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_LoadU.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* TODO: move somewhere *)
  Lemma isU_inv:
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality),
      (b ≤ a' < min a e)%Z
      → isU p = true
      → ((interp W) (inr (p, g, b, e, a))
         → ∃ p' : Perm, ⌜PermFlows (promote_perm p) p'⌝ ∗ read_write_cond a' p' interp
                        ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                                               ∧ ρ ≠ Revoked /\ (∀ g, ρ ≠ Static g))⌝)%I.
  Proof.
    intros. rewrite /interp fixpoint_interp1_eq /=. iIntros "H".
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]";try (iExists p'; iFrame; auto);[solve_addr|].
        iSplit;auto. iPureIntro; auto. eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H2; eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
      iPureIntro; eauto.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto; [solve_addr|].
        iSplit;auto. iPureIntro; auto. eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H1; eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto.
      iSplit;auto. iPureIntro; simpl in H1; eauto.
  Qed.

  Definition region_open_resources W l ls p φ v (bl : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std l ρ
    ∗ ⌜ρ ≠ Revoked ∧ (forall m, ρ ≠ Static m)⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ (if bl then monotonicity_guarantees_region ρ v p φ ∗ φ (W, v)
       else ▷ monotonicity_guarantees_region ρ v p φ ∗  ▷ φ (W, v) )
    ∗ rel l p φ)%I.

  Lemma loadU_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (rdst rsrc : RegName) (offs : Z + RegName):
    ftlr_instr W r p p' g b e a w (LoadU rdst rsrc offs) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion [Hnotrevoked Hnotstatic] HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    assert (Hsome': forall x, is_Some (<[PC:=inr (p, g, b, e, a)]> r !! x)).
    { intros. destruct (reg_eq_dec x PC).
      - subst x. rewrite lookup_insert; eauto.
      - rewrite lookup_insert_ne; auto. }
    destruct (Hsome' rsrc) as [wsrc Hrsrc].
    iDestruct (region_open_prepare with "Hr") as "Hr".
    (* Need to write using lets, otherwise Coq/Iris complains for no reason *)
    iAssert (∃ (mem: gmap Addr (Perm * Word)),
                ⌜let wx := <[PC:=inr (p, g, b, e, a)]> r !! rsrc in
                match wx with
                | Some (inr (px, gx, bx, ex, ax)) =>
                  if isU px
                  then let moffs := z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs in
                       match moffs with
                       | Some zoffs =>
                         let ma' := verify_access (LoadU_access bx ex ax zoffs) in
                         match ma' with
                         | Some a' =>
                           let mpw := mem !! a' in
                           match mpw with
                           | Some (p'', w') =>
                             p'' ≠ O
                           | None => False
                           end
                         | None => True
                         end
                       | None => True
                       end
                  else True
                | _ => True
                end⌝ ∗
                (▷ let wx := <[PC:=inr (p, g, b, e, a)]> r !! rsrc in
                match wx with
                | Some (inr (px, gx, bx, ex, ax)) =>
                  if isU px
                  then let moffs := z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs in
                       match moffs with
                       | Some zoffs =>
                         let ma' := verify_access (LoadU_access bx ex ax zoffs) in
                         match ma' with
                         | Some a' =>
                           let mpw := mem !! a' in
                           match mpw with
                           | Some (p'', w') =>
                              ⌜mem = if addr_eq_dec a a' then (<[a:=(p',w)]> ∅) else <[a:=(p',w)]> (<[a':=(p'',w')]> ∅)⌝ ∗ sts_full_world W ∗ if addr_eq_dec a a' then open_region_many [a] W else region_open_resources W a' [a] p'' interpC w' true
                           | None => ⌜False⌝
                           end
                         | None => True
                         end
                       | None => True
                       end
                  else True
                | _ => True
                end) ∗ ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗ ⌜mem !! a = Some (p', w)⌝)%I
        with "[Ha Hsts Hr]" as "H".
    { rewrite Hrsrc. destruct wsrc; auto.
      - iDestruct (memMap_resource_1 with "Ha") as "H".
        iExists _; iFrame; auto. rewrite lookup_insert; auto.
      - destruct_cap c. destruct (isU c) eqn:HisU.
        + destruct (z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs) eqn:Hzof.
          * destruct (verify_access (LoadU_access c2 c1 c0 z)) eqn:Hver.
            -- destruct (reg_eq_dec rsrc PC).
               ++ subst rsrc. rewrite lookup_insert in Hrsrc.
                  inv Hrsrc. destruct Hp as [-> | [-> | [-> ->] ] ]; simpl in HisU; inv HisU.
               ++ iDestruct ("Hreg" $! rsrc n) as "Hinvsrc"; auto.
                  rewrite lookup_insert_ne in Hrsrc; auto.
                  rewrite /RegLocate Hrsrc.
                  eapply verify_access_spec in Hver.
                  destruct Hver as [HA [HB [HC HD] ] ].
                  iDestruct (isU_inv _ a0 with "Hinvsrc") as "H"; auto. solve_addr.
                  iDestruct "H" as (p'') "[% [X %]]".
                  destruct (addr_eq_dec a a0).
                  ** subst a0. iDestruct (memMap_resource_1 with "Ha") as "H".
                     iExists _; iFrame; auto.
                     rewrite lookup_insert; auto.
                     iFrame. auto.
                  ** destruct H0 as [ρ' [X [Y Z] ] ].
                     iDestruct (region_open_next with "[$Hsts $Hr]") as "HH";eauto.
                     { intros [g1 Hcontr]. specialize (Z g1); contradiction. }
                     { apply not_elem_of_cons. split; auto.
                       apply not_elem_of_nil. }
                     iDestruct "HH" as (w') "(Hsts & Hstate & Hr & Ha' & % & Hmono & HX)".
                     iDestruct (memMap_resource_2ne with "[$Ha $Ha']") as "H"; auto.
                     iExists (<[a:=(p', w)]> (<[a0:=(p'', w')]> ∅)).
                     rewrite lookup_insert_ne; auto. rewrite lookup_insert.
                     iFrame. iSplitR; auto. iSplitL; auto. iNext. iSplitR; auto.
                     iExists ρ'. iFrame; auto. rewrite lookup_insert; auto.
            -- iDestruct (memMap_resource_1 with "Ha") as "H".
               iExists _; iFrame; auto. rewrite lookup_insert; auto.
          * iDestruct (memMap_resource_1 with "Ha") as "H".
            iExists _; iFrame; auto. rewrite lookup_insert; auto.
        + iDestruct (memMap_resource_1 with "Ha") as "H".
          iExists _; iFrame; auto. rewrite lookup_insert; auto. }

    iDestruct "H" as (mem) "[% [A [B %]]]".
    iApply (wp_loadU with "[Hmap B]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iFrame. }
    iNext. iIntros (r' v) "[% [B C]]".
    inv H1.
    { rewrite Hrsrc in H2. inv H2. rewrite Hrsrc H3 H4 H5 H6.
      iDestruct "A" as "[% [Hsts A]]".
      assert (Persistent (if addr_eq_dec a a' then emp%I else interp W w0)).
      { destruct (addr_eq_dec a a'). apply emp_persistent. apply interp_persistent. }
      iAssert (region W ∗ (if addr_eq_dec a a' then emp else interp W w0))%I with "[A B Hmono Hstate]" as "[Hregion #Hw']".
      { destruct (addr_eq_dec a a').
        - subst a'; subst mem.
          iDestruct (region_open_prepare with "A") as "A".
          iDestruct (memMap_resource_1 with "B") as "B".
          iDestruct (region_close with "[A B $Hmono $Hstate]") as "B";eauto.
          { destruct ρ;auto;[|specialize (Hnotstatic g1)];contradiction. }      
          iFrame. iSplitR; auto.
        - subst mem. iDestruct (memMap_resource_2ne with "B") as "[B C]"; auto.
          rewrite /region_open_resources. iDestruct "A" as (ρ') "[A1 [% [A2 [% [[A3 #Hw'] A4]]]]]".
          destruct H1 as [Hnotrevoked' Hnotstatic']. 
          iDestruct (region_close_next with "[$A1 $A2 $A3 $A4 $C]") as "A"; auto.
          { intros [g' Hcontr]. destruct ρ';auto;inversion Hcontr;try contradiction.
            specialize (Hnotstatic' g'). contradiction. 
          }
          { eapply not_elem_of_cons; split; auto. eapply not_elem_of_nil. }
          iFrame "#".
          iDestruct (region_open_prepare with "A") as "A".
          iDestruct (region_close with "[A B $Hmono $Hstate]") as "B"; try iFrame; auto.
          destruct ρ;auto;[..|specialize (Hnotstatic g1)];contradiction.
      }

      apply incrementPC_Some_inv in H7.
      destruct H7 as (?&?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto. iNext.
      destruct (decide (x = RX ∨ x = RWX ∨ x = RWLX)).
      2 : {
        assert (x ≠ RX ∧ x ≠ RWX ∧ x ≠ RWLX). split; last split; by auto.
        iDestruct ((big_sepM_delete _ _ PC) with "C") as "[HPC Hmap]".
        { rewrite H9. by rewrite lookup_insert. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext. iApply wp_value.
        iIntros (a1); inversion a1. }
      
      iApply ("IH" $! _ r' with "[%] [] [C] [$Hregion] [$Hsts] [$Hown]").
      - subst r'. intros. rewrite lookup_insert_is_Some'.
        destruct (reg_eq_dec PC x5); auto; right.
        rewrite lookup_insert_is_Some'. destruct (reg_eq_dec rdst x5); auto; right.
      - subst r'. iIntros (rx) "%".
        rewrite /RegLocate lookup_insert_ne; auto.
        destruct (reg_eq_dec rx rdst).
        + subst rx. rewrite lookup_insert.
          destruct (addr_eq_dec a a').
          * subst mem; subst a'. rewrite lookup_insert in H6.
            inv H6; auto.
          * auto.
        + rewrite !lookup_insert_ne; auto.
          iApply "Hreg"; auto.
      - subst r'. rewrite insert_insert. iApply "C".
      - destruct (reg_eq_dec PC rdst).
        + subst rdst. rewrite lookup_insert in H7.
          inv H7. destruct (addr_eq_dec a a').
          * subst a'. rewrite lookup_insert in H6. inv H6.
            destruct o as [-> | [-> | ->] ]; auto.
          * destruct o as [-> | [-> | ->] ]; auto.
            rewrite !fixpoint_interp1_eq /=. destruct x0; auto.
        + rewrite lookup_insert_ne in H7; auto.
          rewrite lookup_insert in H7. inv H7. auto.
      - iModIntro. destruct (reg_eq_dec PC rdst).
        + subst rdst. rewrite lookup_insert in H7.
          inv H7. destruct (addr_eq_dec a a').
          * subst a'. rewrite lookup_insert in H6. inv H6.
            iApply readAllowed_implies_region_conditions; auto.
            destruct o as [-> | [-> | ->] ]; auto.
          * iApply readAllowed_implies_region_conditions; auto.
            destruct o as [-> | [-> | ->] ]; auto.
        + rewrite lookup_insert_ne in H7; auto.
          rewrite lookup_insert in H7. inv H7. eauto. }

    { iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
