From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation WORLD := (leibnizO (STS_states * STS_rels)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).
  
  Lemma jmp_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm) 
        (g : Locality) (b e a : Addr) (w : Word) (r0 : RegName) :
      p = RX ∨ p = RWX ∨ p = RWLX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a <= e)%a
    → PermFlows p p'
    → p' ≠ O
    → cap_lang.decode w = Jmp r0
    -> □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
             full_map a2
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (a0, a1)) (a2 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a3, a4, a5, a6, a7)]> a2)
          -∗ region (a0, a1)
          -∗ sts_full a0 a1
          -∗ na_own logrel_nais ⊤
          -∗ ⌜a3 = RX ∨ a3 = RWX ∨ a3 = RWLX⌝
             → □ (∃ p'0 : Perm, ⌜PermFlows a3 p'0⌝
                    ∧ ([∗ list] a8 ∈ region_addrs a5 a6, read_write_cond a8 p'0 interp))
                 -∗ interp_conf a0 a1)
    -∗ ([∗ list] a0 ∈ region_addrs b e, read_write_cond a0 p' interp)
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (fs, fr)) (r !r! r1))
    -∗ read_write_cond a p' interp
    -∗ ▷ future_mono (λ Wv : prodO WORLD (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2)
    -∗ ▷ ((fixpoint interp1) (fs, fr)) w
    -∗ sts_full fs fr
    -∗ na_own logrel_nais ⊤
    -∗ open_region a (fs, fr)
    -∗ a ↦ₐ[p'] w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (fs' : STS_states) (fr' : STS_rels),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                           ∗ na_own logrel_nais ⊤
                                           ∗ sts_full fs' fr' ∗ region (fs', fr') }} }}.
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap". 
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r0).
    * subst r0.
      iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame. 
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iNext. 
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* close region *)
      iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
      (* apply IH *)
      iApply ("IH" $! _ _ _ _ g _ _ a
                       with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); eauto; iFrame "#".
      { iPureIntro. apply Hsome. }
      destruct p; iFrame. 
      destruct Hp as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. 
    * specialize Hsome with r0 as Hr0.
      destruct Hr0 as [wsrc Hsomesrc].
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
      rewrite (lookup_delete_ne r PC r0); eauto.
      iApply (wp_jmp_success with "[$HPC $Ha $Hsrc]"); eauto.
      iNext. iIntros "[HPC [Ha Hsrc]] /=".
      iApply wp_pure_step_later; auto. 
      (* reconstruct regions *)
      iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto. 
      destruct (updatePcPerm wsrc) eqn:Heq.
      { iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
        iNext. iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros. discriminate. }
      { destruct c,p0,p0,p0. 
        destruct p0.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence.
          + inv Heq. rewrite (fixpoint_interp1_eq _ (inr _)).
            simpl. rewrite /read_write_cond.
            iDestruct "Hwsrc" as (q) "[% [H1 H2]]".
            iNext.
            (* close region *)
            iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
            (* apply IH *)
            iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
          + inv Heq. rewrite (fixpoint_interp1_eq _ (inr _)).
            simpl. rewrite /enter_cond.
            rewrite /interp_expr /=.
            iDestruct "Hwsrc" as "#H".
            iAssert (future_world l (fs,fr) (fs,fr)) as "Hfuture".
            { destruct l; iPureIntro;
                [apply related_sts_priv_refl|apply related_sts_pub_refl]. }
            iSpecialize ("H" $! _ (fs,fr) with "Hfuture").
            iNext. 
            iDestruct "H" as (fs' fr' Heq1 Heq2) "HH". inversion Heq1. inversion Heq2.
            subst.
            iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
            iDestruct ("HH" with "[Hr Hfull Hmap Hna]") as "Hx"; iFrame; eauto.
            iDestruct "Hx" as "[_ Hx] /=". auto.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          rewrite (fixpoint_interp1_eq _ (inr _)).
          simpl. 
          iDestruct "Hwsrc" as (p'') "[% [H1 H2]]".
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
        - iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          rewrite (fixpoint_interp1_eq _ (inr _)).
          simpl. iDestruct "Hwsrc" as (p'') "[% [H1 H2]]".
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
          Unshelve. auto. auto. auto.
      }
  Qed.
  
End fundamental.