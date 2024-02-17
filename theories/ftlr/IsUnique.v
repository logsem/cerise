From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_IsUnique.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Definition compute_mask_range (E : coPset) (b e : Addr) (v : Version) :=
    (compute_mask E (list_to_set ((λ a, (a,v)) <$> (finz.seq_between b e)))).

  (* TODO move ; generalize ? *)
  (* Lemma for opening invariants of a region *)
  Lemma open_region_inv
    (E : coPset)
    (la : list Addr)
    (Ps : list D)
    (v : Version) :
    NoDup la ->
    length la = length Ps  ->
    Forall (fun a => ↑logN.@(a, v) ⊆ E) la ->
    ⊢ ([∗ list] a ∈ zip la Ps, inv (logN.@(a.1, v)) (interp_ref_inv a.1 v a.2))
    -∗ |={E, compute_mask E (list_to_set ((λ a, (a,v)) <$> la))}=>
       ([∗ list] a ∈ zip la Ps, (∃ lw, (a.1,v) ↦ₐ lw ∗ ▷ (a.2 : D) lw)) ∗
       (▷ ([∗ list] a ∈ zip la Ps,
         (interp_ref_inv a.1 v a.2)) ={compute_mask E (list_to_set ((λ a, (a,v)) <$> la)), E}=∗ True).
  Proof.
    move: E Ps v.
    induction la as [|a la IHla]
    ; iIntros (E Ps v HNoDup Hlen Hmask) "#Hinvs" ; cbn in *.
    - rewrite compute_mask_id; iModIntro ; iSplit ; first done.
      iIntros "?" ; iModIntro ; done.
    - destruct Ps as [|P Ps]; cbn in * ; first lia.
      injection Hlen ; clear Hlen ; intros Hlen.
      destruct_cons.
      iDestruct "Hinvs" as "[Hinv Hinvs]".
      assert (
          (a, v) ∉ (@list_to_set _ _ _ _ (@gset_union LAddr _ _)((λ a0 : Addr, (a0, v)) <$> la))
        ).
      { intro Hcontra.
        rewrite elem_of_list_to_set elem_of_list_fmap in Hcontra.
        destruct Hcontra as ( ? & ? & ? ) ; simplify_eq ; set_solver. }
      rewrite compute_mask_union; auto.
      iDestruct (IHla with "Hinvs") as "IH"; eauto.
      iMod "IH" as "[Hoinvs Hinvs_cls]".
      iInv "Hinv" as "Hoinv" "Hinv_cls".
      { apply compute_mask_elem_of; auto. }
      iEval (rewrite later_exist; setoid_rewrite later_sep) in "Hoinv".
      iDestruct "Hoinv" as (lwa) "[>Ha HPa]".
      iModIntro.
      iSplitL "Ha HPa Hoinvs"; first iFrame.
      iExists _ ; iFrame.
      iIntros "[Hoinv Hoinvs]".
      iMod ("Hinv_cls" with "Hoinv").
      iMod ("Hinvs_cls" with "Hoinvs").
      by iModIntro.
  Qed.

  Lemma zip_zip
    (la : list Addr) (lb : list D) (lc : list LWord) (v : Version):
    length la = length lb ->
    length lb = length lc ->

    ([∗ list] ab_c ∈ zip (zip la lb) lc,
      (ab_c.1.1, v) ↦ₐ ab_c.2 ∗ ▷ (ab_c.1.2 : D) ab_c.2)
      ∗-∗ ([∗ list] a_cb ∈ zip la (zip lc lb),
            (a_cb.1, v) ↦ₐ a_cb.2.1 ∗ ▷ (a_cb.2.2 : D) a_cb.2.1).
    revert lb lc.
    induction la as [|a la IHla]; intros * Hlen_lb Hlen_lc.
    - cbn in * ; simplify_eq. iSplit ; iIntros "?" ; done.
    - destruct lb as [|b lb] ; first (cbn in * ; lia).
      destruct lc as [|c lc] ; first (cbn in * ; lia).
      cbn in Hlen_lb, Hlen_lc.
      injection Hlen_lb ; clear Hlen_lb ; intro Hlen_lb.
      injection Hlen_lc ; clear Hlen_lc ; intro Hlen_lc.
      cbn ; iSplit ; iIntros "[Ha Hmem]"; iFrame; iApply IHla; eauto.
  Qed.
  Lemma zip_zip_nolater
    (la : list Addr) (lb : list D) (lc : list LWord) (v : Version):
    length la = length lb ->
    length lb = length lc ->

    ([∗ list] ab_c ∈ zip (zip la lb) lc,
      (ab_c.1.1, v) ↦ₐ ab_c.2 ∗ (ab_c.1.2 : D) ab_c.2)
      ∗-∗ ([∗ list] a_cb ∈ zip la (zip lc lb),
            (a_cb.1, v) ↦ₐ a_cb.2.1 ∗ (a_cb.2.2 : D) a_cb.2.1).
    revert lb lc.
    induction la as [|a la IHla]; intros * Hlen_lb Hlen_lc.
    - cbn in * ; simplify_eq. iSplit ; iIntros "?" ; done.
    - destruct lb as [|b lb] ; first (cbn in * ; lia).
      destruct lc as [|c lc] ; first (cbn in * ; lia).
      cbn in Hlen_lb, Hlen_lc.
      injection Hlen_lb ; clear Hlen_lb ; intro Hlen_lb.
      injection Hlen_lc ; clear Hlen_lc ; intro Hlen_lc.
      cbn ; iSplit ; iIntros "[Ha Hmem]"; iFrame; iApply IHla; eauto.
  Qed.

  Lemma zip_zip'
    (la : list Addr) (lb : list D) (lc : list LWord) (v : Version):
    length la = length lb ->
    length lb = length lc ->
    ([∗ list] y1;y2 ∈ la;zip lc lb, (y1, v) ↦ₐ y2.1)
    ∗-∗ ([∗ list] y1;y2 ∈ la;lc, (y1, v) ↦ₐ y2).
  Proof.
    revert lb lc.
    induction la as [|a la IHla]; intros * Hlen_lb Hlen_lc.
    - iSplit ; iIntros "?".
      all: rewrite -Hlen_lb in Hlen_lc; destruct lc as [|] ; last (cbn in * ; lia).
      all: done.
    - destruct lb as [|b lb] ; first (cbn in * ; lia).
      destruct lc as [|c lc] ; first (cbn in * ; lia).
      cbn in Hlen_lb, Hlen_lc.
      injection Hlen_lb ; clear Hlen_lb ; intro Hlen_lb.
      injection Hlen_lc ; clear Hlen_lc ; intro Hlen_lc.
      cbn ; iSplit ; iIntros "[Ha Hmem]"; iFrame; iApply IHla; eauto.
  Qed.

  Lemma logical_range_map_map
    (la : list Addr) (v : Version) (lws : list LWord) :
    NoDup la ->
    length lws = length la ->
    ([∗ map] a↦lw ∈ list_to_map (zip la lws), (a,v) ↦ₐ lw)
    ∗-∗ ([∗ map] a↦lw ∈ logical_region_map la lws v, a ↦ₐ lw).
  Proof.
    revert v lws.
    induction la as [|a la IHla] ; intros * HNoDup Hlen
    ; first (iSplit ; iIntros "H" ; cbn in * ; try done).
    destruct lws as [|lw lws] ; first (cbn in * ; lia) ; cbn.
    injection Hlen ; clear Hlen ; intro Hlen.
    destruct_cons.
    iSplit; iIntros "H".
    - iDestruct (big_sepM_insert with "H") as "[Ha H]"; eauto.
      {
        apply not_elem_of_list_to_map.
        intro Hcontra.
        rewrite fst_zip in Hcontra; first done.
        rewrite Hlen; lia.
      }
      iApply big_sepM_insert; eauto.
      {
        apply not_elem_of_list_to_map.
        intro Hcontra.
        rewrite fst_zip in Hcontra; last (rewrite map_length ; lia).
        eapply elem_of_list_fmap in Hcontra.
        destruct Hcontra as (? & ? & ?) ; simplify_eq ; done.
      }
      iFrame.
      iApply IHla; eauto.
    - iDestruct (big_sepM_insert with "H") as "[Ha H]"; eauto.
      {
        apply not_elem_of_list_to_map.
        intro Hcontra.
        rewrite fst_zip in Hcontra; last (rewrite map_length Hlen ; lia).
        eapply elem_of_list_fmap in Hcontra.
        destruct Hcontra as (? & ? & ?) ; simplify_eq ; done.
      }
      iApply big_sepM_insert; eauto.
      {
        apply not_elem_of_list_to_map.
        intro Hcontra.
        rewrite fst_zip in Hcontra; first done.
        rewrite Hlen; lia.
      }
      iFrame.
      iApply IHla; eauto.
  Qed.

  Lemma region_inv_destruct
    (b e : Addr) ( v : Version ) (Ps : list D) :
    length Ps = length (finz.seq_between b e) ->
    ([∗ list] a_Pa ∈ zip (finz.seq_between b e) Ps,
      ∃ lw, (a_Pa.1, v) ↦ₐ lw ∗ ▷ (a_Pa.2 : D) lw)
    -∗ (∃ lws, ⌜ length lws = length (finz.seq_between b e) ⌝ ∧
                 (([∗ map] la↦lw ∈ (logical_range_map b e lws v), la ↦ₐ lw)
                    ∗ ([∗ list] lw;Pw ∈ lws;Ps, ▷ (Pw : D) lw))).
  Proof.
    iIntros (Hlen) "Hrange".
    assert (NoDup (finz.seq_between b e)) as HNoDup
        by (apply finz_seq_between_NoDup).
    iDestruct (region_addrs_exists with "Hrange") as (lws) "[%Hlen_lws Hrange]".
    assert (length lws = length (finz.seq_between b e)) as Hlen'
        by (rewrite length_zip_l in Hlen_lws; lia).
    assert (length lws = length Ps) as Hlen'' by (by rewrite -Hlen in Hlen').
    iExists lws ; iSplit ; first done.
    iAssert (
        [∗ list] a;lwa_Pa ∈ finz.seq_between b e;(zip lws Ps),
          (a, v) ↦ₐ lwa_Pa.1 ∗ ▷ (lwa_Pa.2 : D) lwa_Pa.1)%I
      with "[Hrange]"
      as "Hrange".
    {
      iDestruct (big_sepL2_alt with "Hrange") as "[ _ Hrange]".
      iApply big_sepL2_alt.
      iSplit; first (iPureIntro; by (rewrite length_zip_l; lia)).
      iApply zip_zip; eauto.
    }
    iDestruct (big_sepL2_sep_sepL_r with "Hrange") as "[Hrange HrangeP]".
    iSplitR "HrangeP"; cycle 1.
    iApply big_sepL2_alt ; iFrame; auto.
    iDestruct (zip_zip' with "Hrange") as "Hrange"; auto.
    iDestruct (big_sepL2_to_big_sepM  with "Hrange") as "Hrange"; auto.
    iApply logical_range_map_map; auto.
  Qed.

  Lemma region_inv_construct
    (b e : Addr) ( v : Version ) (Ps : list D) :
    length Ps = length (finz.seq_between b e) ->
    (∃ lws, ⌜ length lws = length (finz.seq_between b e) ⌝ ∧
              (([∗ map] la↦lw ∈ (logical_range_map b e lws v), la ↦ₐ lw)
                 ∗ ([∗ list] lw;Pw ∈ lws;Ps, (Pw : D) lw)))
  -∗ ([∗ list] a_Pa ∈ zip (finz.seq_between b e) Ps,
      ∃ lw, (a_Pa.1, v) ↦ₐ lw ∗ (a_Pa.2 : D) lw).
  Proof.
    iIntros (Hlen) "Hrange".
    assert (NoDup (finz.seq_between b e)) as HNoDup
        by (apply finz_seq_between_NoDup).
    iDestruct "Hrange" as (lws) "(%Hlen' & Hrange & HPrange)".
    iApply region_addrs_exists; iExists lws; iSplit
    ; first (iPureIntro ; rewrite length_zip_l; auto; lia).
    assert (length lws = length Ps) as Hlen'' by (by rewrite -Hlen in Hlen').
    iDestruct (logical_range_map_map with "Hrange") as "Hrange"; auto; auto.
    iDestruct (big_sepM_to_big_sepL2  with "Hrange") as "Hrange"; auto.
    iDestruct (zip_zip' with "Hrange") as "Hrange"; eauto.
    iApply big_sepL2_alt ; iFrame; auto.
    iSplit; first (rewrite length_zip_l; [done|lia]).
    iDestruct (big_sepL2_sep_sepL_r with "[$Hrange HPrange]") as "Hrange".
    iDestruct (big_sepL2_alt with "HPrange") as "[? ?]"; iFrame.
    cbn.
    iApply zip_zip_nolater; eauto.
    iDestruct (big_sepL2_alt with "Hrange") as "[ _ Hrange]".
    iFrame.
  Qed.


  Lemma isunique_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst src : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (IsUnique dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=LCap p b e a v]> lregs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)) as [Hx|Hx].
      rewrite Hx lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0 v0, read_reg_inr (<[PC:=LCap p b e a v]> lregs) src p0 b0 e0 a0 v0)
      as (p0 & b0 & e0 & a0 & v0 & HVsrc).
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p0 b0 e0 a0 v0|] | ]; try done.
      by repeat eexists.
    }

    destruct (decide (PC = src)) as [?|Hsrc_neq_pc]; simplify_map_eq.
    - rewrite /read_reg_inr in HVsrc; simplify_map_eq.
      admit. (* temporary admit the case (PC = src) *)
    - pose proof (Hsome src) as [wsrc Hlregs_src].
      rewrite /read_reg_inr in HVsrc; simplify_map_eq.
      destruct (decide (is_lcap wsrc)) as [Hcap|Hcap]; cycle 1.
      { (* wsrc in not a lcap *)
        destruct_lword wsrc ; cbn in HVsrc; try done.
        all: rewrite memMap_resource_1.
        all: iApply (wp_isunique with "[$Hmap $Ha]")
        ; eauto
        ; [ by simplify_map_eq
          | rewrite /subseteq /map_subseteq /set_subseteq_instance
            ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
          | by simplify_map_eq
          |].
        all: try done.
        all: iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)".
        all: inversion Hspec as [ | | | ? ? Hfail]; simplify_map_eq
        ; try (rewrite H0 in Hlregs_src; simplify_eq).
        all: rewrite -memMap_resource_1.
        all: iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro].
        all: iApply wp_pure_step_later; auto.
        all: iNext; iIntros "_"; iApply wp_value; auto.
        all: iIntros; discriminate.
      }

      iAssert (interp wsrc) as "#Hinterp_src" ; first (iApply "Hreg"; eauto).
      (* wsrc is a lcap *)
      destruct (is_sealed wsrc) eqn:His_sealed.
      + (* wsrc is either E-cap or sealed cap *)
        rewrite memMap_resource_1.
        iApply (wp_isunique with "[$Hmap $Ha]")
        ; eauto
        ; [ by simplify_map_eq
          | rewrite /subseteq /map_subseteq /set_subseteq_instance
            ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
          | by simplify_map_eq
          |].
        iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)".
        inversion Hspec as [| ? Hlwsrc Hcannot_read Hunique_regs Hmem' Hincr_PC | |]
        ; simplify_map_eq.
        { (* case sweep success cap : contradiction *)
          rewrite H0 in Hlregs_src; simplify_map_eq.
          by destruct p0 ; cbn in * ; try congruence.
        }
        { (* case sweep success is_sealed *)
          cbn in *; simplify_eq.
          rewrite -memMap_resource_1.
          iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro].
          iApply wp_pure_step_later; auto.
          iNext; iIntros "_".
          incrementLPC_inv; simplify_map_eq.
          assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq).
          simplify_map_eq.
          rewrite (insert_commute _ _ PC) // insert_insert.
          iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto.
          { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
          {
            iIntros (ri ? Hri Hvs).
            destruct (decide (ri = dst)); simplify_map_eq.
            by rewrite !fixpoint_interp1_eq.
            iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
          }
          iModIntro.
          rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto.
        }
        { (* case sweep false*)
          cbn in *; simplify_eq.
          rewrite -memMap_resource_1.
          iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro].
          iApply wp_pure_step_later; auto.
          iNext; iIntros "_".
          incrementLPC_inv; simplify_map_eq.
          assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq).
          simplify_map_eq.
          rewrite (insert_commute _ _ PC) // insert_insert.
          iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto.
          { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
          {
            iIntros (ri ? Hri Hvs).
            destruct (decide (ri = dst)); simplify_map_eq.
            by rewrite !fixpoint_interp1_eq.
            iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
          }
          iModIntro.
          rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto.
        }
        {  (* Fail *)
          rewrite -memMap_resource_1.
          iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro].
          iApply wp_pure_step_later; auto.
          iNext; iIntros "_"; iApply wp_value; auto.
          iIntros; discriminate.
        }
      + (* wsrc is an actual capability, with at least read permission *)
        destruct_lword wsrc ; simplify_eq ; clear Hcap.
        destruct (readAllowed p0) eqn:Hread; cycle 1.
        { (* Case O-cap *)
          destruct p0 ; cbn in His_sealed, Hread ; try congruence.
          rewrite memMap_resource_1.
          iApply (wp_isunique with "[$Hmap $Ha]")
          ; eauto
          ; [ by simplify_map_eq
            | rewrite /subseteq /map_subseteq /set_subseteq_instance
              ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
            | by simplify_map_eq
            |].
          iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)".
          (* inversion Hspec as [| ? Hlwsrc Hcannot_read Hunique_regs Hmem' Hincr_PC | |] *)
          (* ; simplify_map_eq. *)
          admit. (* TODO is OK, just tedious *)
        }
        clear His_sealed.

        iDestruct (read_allowed_region_inv with "Hinterp_src") as "Hread_src" ;eauto.
        iDestruct (region_addrs_exists with "Hread_src") as "Hread_src'".
        iDestruct "Hread_src'" as (Ps) "[%Hlen Hread_src']".
        iDestruct (big_sepL2_alt with "Hread_src'") as "[_ Hread_src'']".
        iDestruct (big_sepL_sep with "Hread_src''") as "[Hsrc_pointsto Hread_src_P]".
        iDestruct (big_sepL_sep with "Hread_src_P") as "[Hread_P Hwrite_P]".
        iClear "Hread_src' Hread_src'' Hread_src Hread_src_P".

        assert (NoDup (finz.seq_between b0 e0)) as HNoDup_range by apply finz_seq_between_NoDup.

        destruct (decide (a ∈ finz.seq_between b0 e0)) as [ Ha_in_src | Ha_notin_src ].
        * admit. (* temporary admit *)
        * iMod (open_region_inv with "Hsrc_pointsto") as "[Hsrc Hcls_src]"; eauto.
          {
            apply Forall_forall; intros a' Ha'.
            assert (a' ≠ a) by (intro ; set_solver).
            apply namespaces.coPset_subseteq_difference_r; [solve_ndisj|set_solver].
          }

          iDestruct (region_inv_destruct with "Hsrc")
            as (lws) "(%Hlen_lws & Hrange & HPrange)"
          ; first done.

          iDestruct (big_sepM_insert with "[$Hrange $Ha]") as "Hmem"
          ; first ( by apply logical_range_notin ).


          iApply (wp_isunique with "[$Hmap $Hmem]")
          ; eauto
          ; [ by simplify_map_eq
            | rewrite /subseteq /map_subseteq /set_subseteq_instance
              ; intros rr _; apply elem_of_dom
              ; rewrite lookup_insert_is_Some';
              eauto
            | by simplify_map_eq
            |].
          iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)".
          destruct Hspec as
            [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC
            | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC
            | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hmem' Hincr_PC
            | ? ? Hfail]
          ; simplify_map_eq
          ; try (rewrite Hlwsrc' in Hlregs_src; simplify_eq)
          ; try (rewrite Hlwsrc in Hlregs_src; simplify_eq)
          ; try (cbn in Hlwsrc' ; simplify_eq)
          ; cycle 1.
          { (* Sweep false  *)
            iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"
            ; first (eapply logical_range_notin; eauto).
            iMod ("Hcls_src" with "[Hmem HPrange]") as "_".
            {
              iNext.
              iApply region_inv_construct; first done.
              iExists lws; iSplit ; first done; iFrame.
            }
            iModIntro.
            iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame).
            iModIntro.
            iApply wp_pure_step_later; auto.
            iNext; iIntros "_".
            incrementLPC_inv; simplify_map_eq.
            assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq).
            simplify_map_eq.
            rewrite (insert_commute _ _ PC) // insert_insert.
            iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto.
            { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
            {
              iIntros (ri ? Hri Hvs).
              destruct (decide (ri = dst)); simplify_map_eq.
              by rewrite !fixpoint_interp1_eq.
              iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
            }
            iModIntro.
            rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto.
          }
         { (* Sweep false  *)
            iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"
            ; first (eapply logical_range_notin; eauto).
            iMod ("Hcls_src" with "[Hmem HPrange]") as "_".
            {
              iNext.
              iApply region_inv_construct; first done.
              iExists lws; iSplit ; first done; iFrame.
            }
            iModIntro.
            iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame).
            iModIntro.
            iApply wp_pure_step_later; auto.
            iNext; iIntros "_".
            incrementLPC_inv; simplify_map_eq.
            assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq).
            simplify_map_eq.
            rewrite (insert_commute _ _ PC) // insert_insert.
            iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto.
            { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
            {
              iIntros (ri ? Hri Hvs).
              destruct (decide (ri = dst)); simplify_map_eq.
              by rewrite !fixpoint_interp1_eq.
              iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
            }
            iModIntro.
            rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto.
          }
          { (* Fail *)
            iDestruct (big_sepM_insert with "Hmem") as "[Ha Hrange]"
            ; first ( by apply logical_range_notin ).
            iMod ("Hcls_src" with "[Hrange HPrange]") as "_".
            {
              iNext.
              iApply region_inv_construct; first done.
              iExists lws; iSplit ; first done; iFrame.
            }
            iModIntro.
            iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame).
            iModIntro.
            iApply wp_pure_step_later; auto.
            iNext; iIntros "_"; iApply wp_value; auto.
            iIntros; discriminate.
          }

          { (* Sweep true  *)

            incrementLPC_inv
              as (p_pc' & b_pc' & e_pc' &a_pc' &v_pc' & ? & HPC & Z & Hregs')
            ; simplify_map_eq.
            assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq); simplify_map_eq.
            do 2 (rewrite (insert_commute _ _ PC) //); rewrite insert_insert.

            assert ( lmem' !! (a_pc', v_pc') = Some lw ) as Hmem'_pca.
            { eapply is_valid_updated_lmemory_preserves_lmem; eauto.
              by simplify_map_eq.
            }

            assert ( logical_range_map b0 e0 lws v0 ⊆ lmem' )
              as Hmem'_be.
            {
              eapply is_valid_updated_lmemory_lmem_incl with (la := (finz.seq_between b0 e0))
              ; eauto.
              eapply is_valid_updated_lmemory_insert; eauto.
              eapply logical_range_notin; eauto.
              eapply Forall_forall; intros a Ha.
              eapply logical_range_version_neq; eauto; last lia.
            }
            assert
              (logical_range_map b0 e0 lws (v0 + 1) ⊆ lmem')
              as Hmem'_be_next.
            { clear -Hupd Hlen_lws HNoDup_range Ha_notin_src.
              eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
              assert (v' = v0+1 /\ (a' ∈ (finz.seq_between b0 e0))) as [? Ha'_in_be]
                  by (eapply logical_range_map_some_inv; eauto); simplify_eq.
              destruct Hupd.
              eapply lookup_weaken; last eauto.
              rewrite update_version_region_preserves_lmem_next; eauto.
              all: rewrite lookup_insert_ne //=; last (intro ; set_solver).
              erewrite logical_range_map_lookup_versions; eauto.
              eapply logical_range_version_neq; eauto; lia.
            }

            rewrite -(insert_id lmem' (a_pc', v_pc') lw); auto.
            iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha Hmem]".
            eapply delete_subseteq_r with (k := ((a_pc', v_pc') : LAddr)) in Hmem'_be
            ; last (eapply logical_region_notin; eauto).
            iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange Hmem]"
            ; first (eapply Hmem'_be).
            eapply delete_subseteq_r with (k := ((a_pc', v_pc') : LAddr)) in Hmem'_be_next
            ; last (eapply logical_region_notin ; eauto).
            eapply delete_subseteq_list_r
              with (m3 := list_to_map (zip (map (λ a : Addr, (a, v0)) (finz.seq_between b0 e0)) lws))
              in Hmem'_be_next
            ; eauto
            ; last (by eapply update_logical_memory_region_disjoint).
            iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange' Hmem]"
            ; first (eapply Hmem'_be_next); iClear "Hmem".

            iAssert ( [∗ list] y1;y2 ∈ lws;Ps, (y2 : D) y1)%I as "HPrange'".
            { admit. (* TODO need P to be persistent..... *) }
            iMod (region_valid_alloc _ b0 e0 a0 (v0 +1) lws p0
                   with "[HPrange] [Hrange']")
            as "#Hinterp_src_next".
            { destruct p0 ; cbn in * ; try congruence; done. }
            { admit. }
            { iClear "#". clear -Hlen Hlen_lws.
              iApply big_sepL2_alt.
              iSplit; first (iPureIntro; rewrite map_length; lia).
              iDestruct (big_sepM_list_to_map with "Hrange'") as "?" ; last iFrame.
              rewrite fst_zip; first (apply NoDup_logical_region).
              rewrite /logical_region map_length ; lia.
            }

            iMod ("Hcls_src" with "[Hrange HPrange']") as "_".
            {
              iNext.
              iApply region_inv_construct; first done.
              iExists lws; iSplit ; first done; iFrame "#∗".
            }
            iModIntro.
            iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame).
            iModIntro.

            iApply wp_pure_step_later; auto.
            iNext; iIntros "_".
            simplify_map_eq.
            iApply ("IH" $! (<[dst := _]> (<[ src := _ ]> lregs)) with "[%] [] [Hmap] [$Hown]")
            ; eauto.
            { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
            { iIntros (r1 lw1 Hr1 Hlw1).
              destruct (decide (r1 = dst)) as [ |Hr1_dst]
              ; simplify_map_eq; first (rewrite !fixpoint_interp1_eq //=).
              destruct (decide (r1 = src)) as [ |Hr1_src]
              ; simplify_map_eq; first done.
              iApply "Hreg"; eauto. }
            { rewrite !fixpoint_interp1_eq //= ; destruct p_pc'; destruct Hp ; done. }
          }
  Admitted.
End fundamental.
