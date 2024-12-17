From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_IsUnique.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  (* TODO @June redo the proof in the same style as Load or Store *)
  Lemma isunique_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst src : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (IsUnique dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #(Hread & Hwrite & %HpersP) Hown Ha HP Hcls HPC Hmap".
    specialize (HpersP lw).
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
      assert (readAllowed p0) as Hread_p0 by (destruct p0 ; destruct Hp ; done).
      iDestruct (read_allowed_region_inv with "Hinv") as "Hread_pc" ;eauto.


      apply le_addr_withinBounds', withinBounds_in_seq_1 in Hbae.
      odestruct (list_remove_elem_in _ _ Hbae) as (la' & <- & Hla').
      set (la' := list_remove_elem a0 (finz.seq_between b0 e0)).
      assert (NoDup la') as HNoDup_la'.
      { eapply list_remove_elem_NoDup; eauto. apply finz_seq_between_NoDup. }
      assert (a0 ∉ la') as Ha0_notin_la'.
      { eapply not_elemof_list_remove_elem ; cycle 2 ; eauto.
        apply finz_seq_between_NoDup.
      }
      assert ( la' ⊆+ finz.seq_between b0 e0 ) as Hsubmset_la'
        by (by eapply list_remove_list_submsteq).

      (* not_elemof_list_remove_elem *)
      iDestruct (interp_open_region $ (⊤ ∖ ↑logN.@(a0, v0)) with "Hinv")
        as (Ps) "[%Hlen_Ps Hmod]"; eauto.
      { eapply Forall_forall. intros.
        assert ((x,v0) ≠ (a0,v0)) by set_solver.
        eapply namespaces.coPset_subseteq_difference_r; auto.
        solve_ndisj.
      }

      iMod "Hmod"
        as (lws) "(%Hlen_lws & %Hpers & Hrange & HPrange & #Hread_cond & Hcls_src)"
      ; eauto.

      assert (logical_region_map la' lws v0 !! (a0, v0) = None) as Ha0_notin_reg_la'
          by (eapply logical_region_notin; eauto).
      iDestruct (big_sepM_insert with "[$Hrange $Ha]") as "Hmem"; auto.


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
        iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"; auto.
        iMod ("Hcls_src" with "[Hmem HPrange]") as "_".
        {
          iNext.
          iApply region_inv_construct; auto.
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
        iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        iMod ("Hcls_src" with "[Hmem HPrange]") as "_".
        {
          iNext.
          iApply region_inv_construct; auto.
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
        iDestruct (big_sepM_insert with "Hmem") as "[Ha Hrange]"; auto.
        iMod ("Hcls_src" with "[Hrange HPrange]") as "_".
        {
          iNext.
          iApply region_inv_construct; auto.
        }
        iModIntro.
        iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame).
        iModIntro.
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_"; iApply wp_value; auto.
        iIntros; discriminate.
      }

     { (* Sweep true cap : update *)

       incrementLPC_inv
         as (p_pc' & b_pc' & e_pc' &a_pc' &v_pc' & ? & HPC & Z & Hregs')
       ; simplify_map_eq.
       assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq); simplify_map_eq.
       do 2 (rewrite (insert_commute _ _ PC) //);
       rewrite !insert_insert.

       assert ( lmem' !! (a_pc', v) = Some lw ) as Hmem'_pca.
       { eapply is_valid_updated_lmemory_preserves_lmem; cycle 1 ; eauto.
         by simplify_map_eq.
         apply finz_seq_between_NoDup.
       }

       assert (NoDup (finz.seq_between b_pc' e_pc')) as HNoDup_pc
           by (by apply finz_seq_between_NoDup).

       assert ( lmem' !! (a_pc', v+1) = Some lw ) as Hmem'_pca_next.
       { eapply is_valid_updated_lmemory_preserves_lmem_next; cycle 1
         ; eauto
         ; last by simplify_map_eq.
         eapply Forall_forall; intros a Ha.
         rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
         eapply logical_region_version_neq; eauto ; last lia.
       }

       assert ( ((logical_region_map la' lws) ) v ⊆ lmem' )
         as Hmem'_be.
       {
         eapply is_valid_updated_lmemory_lmem_incl with (la := (finz.seq_between b_pc' e_pc'))
         ; eauto.
         eapply is_valid_updated_lmemory_insert'; eauto.
         eapply Forall_forall; intros a Ha.
         eapply logical_region_version_neq; eauto ; last lia.
       }
       assert ( ((logical_region_map la' lws) ) (v+1) ⊆ lmem' )
         as Hmem'_be_next.
       {
         eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
         assert (v' = v+1 /\ (a' ∈ la')) as [? Ha'_in_be]
             by (eapply logical_region_map_some_inv; eauto)
         ; simplify_eq.
         simplify_eq.
         destruct Hupd.
         eapply lookup_weaken; last eapply H0.
         rewrite update_version_region_preserves_lmem_next; eauto.
         { rewrite lookup_insert_ne ; last (intro ; simplify_eq ; set_solver).
           erewrite logical_region_map_lookup_versions; eauto.
         }
         { subst la'.
           eapply elem_of_submseteq; eauto.
         }
         { rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
           eapply logical_region_version_neq; eauto; lia.
         }
       }

       rewrite -(insert_id lmem' (a_pc', v) lw); auto.
       iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha Hmem]".

       rewrite -(insert_id (_ lmem') (a_pc', v+1) lw); auto.
       2: { rewrite lookup_delete_ne ; first by simplify_map_eq. intro ; simplify_eq ; lia. }
       iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha_next Hmem]".

       eapply delete_subseteq_r with (k := ((a_pc', v) : LAddr)) in Hmem'_be
       ; last (eapply logical_region_notin; eauto).
       eapply delete_subseteq_r with (k := ((a_pc', v+1) : LAddr)) in Hmem'_be
       ; last (eapply logical_region_notin; eauto).
       iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange Hmem]"
       ; first (eapply Hmem'_be).

       eapply delete_subseteq_r with (k := ((a_pc', v) : LAddr)) in Hmem'_be_next
       ; last (eapply logical_region_notin ; eauto).
       eapply delete_subseteq_r with (k := ((a_pc', v+1) : LAddr)) in Hmem'_be_next
       ; last (eapply logical_region_notin ; eauto).
       eapply delete_subseteq_list_r
         with (m3 := list_to_map (zip (map (λ a : Addr, (a, v)) la') lws))
         in Hmem'_be_next
       ; eauto
       ; last (by eapply update_logical_memory_region_disjoint).
       iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange' Hmem]"
       ; first (eapply Hmem'_be_next); iClear "Hmem".
       iDestruct "HPrange" as "#HPrange".
       iDestruct "HP" as "#HP".

       iMod ("Hcls_src" with "[Hrange HPrange]") as "_".
       {
         iNext.
         iApply region_inv_construct; try done.
         iExists lws; iSplit ; first done; iFrame "#∗".
       }
       iModIntro.
       iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame "#∗").
       iModIntro.

       iMod (region_valid_alloc' _ b_pc' e_pc' a_pc' (a_pc'::la') (v +1) (lw::lws) p_pc'
              with "[HPrange HP] [Hrange' Ha_next]")
       as "#Hinterp_src_next".
       { destruct p_pc' ; cbn in * ; try congruence; done. }
       { eapply list_remove_list_region ; auto. }
       { iDestruct (big_sepL2_const_sepL_r _ lws with "[Hread_cond]") as "Hread_P0".
         iSplit ; last iFrame "Hread_cond".
         by rewrite Hlen_lws.
         cbn.
         iDestruct ( big_sepL2_sep_sepL_r with "[$Hread_cond $HPrange]") as "HPs".
         iDestruct (big_sepL2_alt with "HPs") as "[_ HPs']".
         iAssert (
             (∀ (k : nat) (x0 : leibnizO LWord * D),
                 ⌜zip lws Ps !! k = Some x0⌝
                 → x0.2 x0.1 ∗ □ (∀ lw0 : LWord, x0.2 lw0 -∗ fixpoint interp1 lw0) -∗ interp x0.1)
           )%I as "bla".
         { iIntros (? ? ?) "[Ha Hpa]"; by iDestruct ("Hpa" with "Ha") as "?". }
         iDestruct (big_sepL_impl _ (fun _ xy => interp xy.1) with "HPs' bla"
                   ) as "blaa".
         iDestruct (big_sepL2_alt (fun _ lw _ => interp lw) lws Ps with "[$blaa]") as "blaaa".
         by rewrite Hlen_lws.
         iSplit.
         by iApply "Hread".
         by iDestruct (big_sepL2_const_sepL_l (fun _ lw => interp lw) lws Ps with "blaaa") as "[? ?]".
       }
       { iClear "#". subst la'. clear -Hlen_Ps Hlen_lws HNoDup_la'.
         iApply big_sepL2_alt.
         iSplit; first (iPureIntro; rewrite /= map_length; lia).
         iDestruct (big_sepM_list_to_map with "Hrange'") as "?" ; last iFrame.
         rewrite fst_zip.
         apply NoDup_fmap; auto.
         { by intros x y Heq ; simplify_eq. }
         rewrite /logical_region map_length ; lia.
       }

       iApply wp_pure_step_later; auto.
       iNext; iIntros "_".
       simplify_map_eq.
       iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]")
       ; eauto.
       { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
       { iIntros (r1 lw1 Hr1 Hlw1).
         destruct (decide (r1 = dst)) as [ |Hr1_dst]
         ; simplify_map_eq; first (rewrite !fixpoint_interp1_eq //=).
         iApply "Hreg"; eauto. }
       { rewrite !fixpoint_interp1_eq //= ; destruct p_pc'; destruct Hp ; done. }
     }

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
          destruct p0 eqn:Hp0 ; cbn in His_sealed, Hread ; try congruence.
          rewrite memMap_resource_1.
          iApply (wp_isunique with "[$Hmap $Ha]")
          ; eauto
          ; [ by simplify_map_eq
            | rewrite /subseteq /map_subseteq /set_subseteq_instance
              ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
            | by simplify_map_eq
            |].
          iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)".
          inversion Hspec as
            [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC
            | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC
            | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hmem' Hincr_PC
            | ? ? Hfail]
          ; simplify_map_eq
          ; try (rewrite Hlregs_src in Hlwsrc ; simplify_eq)
          ; cycle 1.
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
          { (* case sweep true cap *)
            assert ( lmem' !! (a, v) = Some lw ) as Hmem'_pca.
            { eapply is_valid_updated_lmemory_preserves_lmem; eauto.
              apply finz_seq_between_NoDup.
              by simplify_map_eq.
            }
            rewrite -(insert_id lmem' (a,v) lw).
            iDestruct (big_sepM_insert_delete with "Hmem") as "[Hmem _]".
            iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro].
            iApply wp_pure_step_later; auto.
            iNext; iIntros "_".
            incrementLPC_inv; simplify_map_eq.
            assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq).
            simplify_map_eq.
            do 2 (rewrite (insert_commute _ _ PC) //) ; rewrite insert_insert.
            iApply ("IH" $! (<[dst := (LInt 1)]> (<[src:=LCap p1 b1 e1 a1 (v1 + 1)]> lregs))
                     with "[%] [] [Hmap] [$Hown]"); eauto.
            { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
            {
              iIntros (ri ? Hri Hvs).
              destruct (decide (ri = dst)) ; simplify_map_eq
              ; first by rewrite !fixpoint_interp1_eq.
              destruct (decide (ri = src)) ; rewrite Hlwsrc' in Hlregs_src ; simplify_map_eq
              ; first by rewrite !fixpoint_interp1_eq.
              iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
            }
            rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto.
            done.
          }
        }
        clear His_sealed.

        assert (NoDup (finz.seq_between b0 e0)) as HNoDup_range by apply finz_seq_between_NoDup.

        destruct (decide (a ∈ finz.seq_between b0 e0)) as [ Ha_in_src | Ha_notin_src ].
        * (* There's no need to open the invariant of the region,
             because we know that pc and src overlap *)
          rewrite memMap_resource_1.
          iApply (wp_isunique with "[$Hmap $Ha]")
          ; eauto
          ; [ by simplify_map_eq
            | rewrite /subseteq /map_subseteq /set_subseteq_instance
              ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
            | by simplify_map_eq
            |].
          iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)".
          inversion Hspec as
            [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC
            | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC
            | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hmem' Hincr_PC
            | ? ? Hfail]
          ; simplify_map_eq
          ; try (rewrite Hlregs_src in Hlwsrc' ; simplify_eq)
          ; try (rewrite Hlregs_src in Hlwsrc ; simplify_eq).
          { (* case sweep true cap : contradiction *)
            exfalso. clear -Hunique_regs Ha_in_src Hsrc_neq_pc Hbae.
            apply map_Forall_insert_1_1 in Hunique_regs.
            rewrite decide_False //= in Hunique_regs.
            apply Hunique_regs.
            rewrite elem_of_finz_seq_between in Ha_in_src.
            destruct Ha_in_src; cbn.
            destruct (b1 <? b)%a; solve_addr.
          }
          { (* case sweep true is_sealed : contradiction *)
            exfalso.
            clear -Hread Hnot_sealed.
            by destruct p0 ; cbn in *.
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
          {  (* case fail *)
            rewrite -memMap_resource_1.
            iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro].
            iApply wp_pure_step_later; auto.
            iNext; iIntros "_"; iApply wp_value; auto.
            iIntros; discriminate.
          }

        * (* src ≠ PC *)

          assert (readAllowed p) as Hread_p by (destruct p ; destruct Hp ; done).
          iDestruct (interp_open_region $ (⊤ ∖ ↑logN.@(a, v)) with "Hinterp_src")
            as (Ps) "[%Hlen_Ps Hmod]"; eauto.
          { apply Forall_forall; intros a' Ha'.
            assert (a' ≠ a) by set_solver.
            apply namespaces.coPset_subseteq_difference_r; [solve_ndisj|set_solver].
          }

          iMod "Hmod"
            as (lws) "(%Hlen_lws & %Hpers & Hrange & HPrange & #Hread_cond & Hcls_src)"
          ; eauto.

          assert (forall v', logical_region_map (finz.seq_between b0 e0) lws v' !! (a, v) = None) as Ha_notin_reg_la'.
          by (intro; eapply logical_region_notin; eauto).
          iDestruct (big_sepM_insert with "[$Hrange $Ha]") as "Hmem"; first done.

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
            iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"; first done.
            iMod ("Hcls_src" with "[Hmem HPrange]") as "_".
            {
              iNext.
              iApply region_inv_construct; auto.
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
            iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"; first done.
            iMod ("Hcls_src" with "[Hmem HPrange]") as "_".
            {
              iNext.
              iApply region_inv_construct; auto.
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
            iDestruct (big_sepM_insert with "Hmem") as "[Ha Hrange]"; first done.
            iMod ("Hcls_src" with "[Hrange HPrange]") as "_".
            {
              iNext.
              iApply region_inv_construct; auto.
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
              eapply Forall_forall; intros a Ha.
              eapply logical_range_version_neq; eauto ; last lia.
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
              erewrite logical_region_map_lookup_versions; eauto.
              eapply logical_region_version_neq; eauto; lia.
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
            iDestruct "HPrange" as "#HPrange".

            iMod (region_valid_alloc _ b0 e0 a0 (v0 +1) lws p0
                   with "[HPrange] [Hrange']")
            as "#Hinterp_src_next".
            { destruct p0 ; cbn in * ; try congruence; done. }
            { iDestruct (big_sepL2_const_sepL_r _ lws with "[Hread_cond]") as "Hread_P0".
              iSplit ; last iFrame "Hread_cond".
              by rewrite Hlen_lws.
              cbn.
              iDestruct ( big_sepL2_sep_sepL_r with "[$Hread_cond $HPrange]") as "HPs".
              iClear
                "IH Hinv Hinva Hreg Hread Hwrite Hinterp_src Hread_P0 HPrange".
              iDestruct (big_sepL2_alt with "HPs") as "[_ HPs']".
              iAssert (
                  (∀ (k : nat) (x0 : leibnizO LWord * D),
                      ⌜zip lws Ps !! k = Some x0⌝
                      → x0.2 x0.1 ∗ □ (∀ lw0 : LWord, x0.2 lw0 -∗ fixpoint interp1 lw0) -∗ interp x0.1)
                )%I as "bla".
              { iIntros (? ? ?) "[Ha Hpa]"; by iDestruct ("Hpa" with "Ha") as "?". }
              iDestruct (big_sepL_impl _ (fun _ xy => interp xy.1) with "HPs' bla"
                        ) as "blaa".
              iDestruct (big_sepL2_alt (fun _ lw _ => interp lw) lws Ps with "[$blaa]") as "blaaa".
              by rewrite Hlen_lws.
              by iDestruct (big_sepL2_const_sepL_l (fun _ lw => interp lw) lws Ps with "blaaa") as "[? ?]".
            }
            { iClear "#". clear -Hlen_Ps Hlen_lws.
              iApply big_sepL2_alt.
              iSplit; first (iPureIntro; rewrite map_length; lia).
              iDestruct (big_sepM_list_to_map with "Hrange'") as "?" ; last iFrame.
              rewrite fst_zip; first (apply NoDup_logical_region).
              rewrite /logical_region map_length ; lia.
            }

            iMod ("Hcls_src" with "[Hrange HPrange]") as "_".
            {
              iNext.
              iApply region_inv_construct; auto.
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
  Qed.
End fundamental.
