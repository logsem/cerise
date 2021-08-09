From iris.algebra Require Import agree auth gmap.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous fundamental.
From cap_machine Require Import dynamic_sealing interval list_new malloc interval_closure interval_client.
From cap_machine Require Import solve_pure proofmode map_simpl.

Section interval_client.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {sealG: sealLLG Σ}
          `{MP: MachineParameters}.

  Definition r_temp7 := r_t27.
  Definition r_temp8 := r_t28.

  Definition interval_client_closure (f_i f_m offset_to_checki : Z) :=
    (* jump to the linked interval_closure subroutine *)
    malloc_instrs f_m 3%nat ++
    encodeInstrsW [ Mov r_temp8 r_t1 ] ++
    fetch_instrs f_i ++
    encodeInstrsW [ Mov r_temp7 r_t0;
                  Mov r_t0 PC;
                  Lea r_t0 3;
                  Jmp r_t1;
                  Mov r_t0 r_temp7;
                  (* store the entry points into an environment table *)
                  Store r_temp8 r_t1;
                  Lea r_temp8 1;
                  Store r_temp8 r_t2;
                  Lea r_temp8 1;
                  Store r_temp8 r_t3;
                  Lea r_temp8 (-2)%Z;
                  (* create a closure around check_interval subroutine *)
                  Mov r_t2 r_temp8;
                  Mov r_t1 PC;
                  Lea r_t1 offset_to_checki ] ++
    crtcls_instrs f_m ++
    (* cleanup: note that we exposing the interval library *)
    encodeInstrsW [ Load r_t2 r_temp8;
                  Lea r_temp8 1;
                  Load r_t3 r_temp8;
                  Lea r_temp8 1;
                  Load r_t4 r_temp8;
                  Mov r_temp8 0;
                  Mov r_temp7 0;
                  Jmp r_t0 ].

  Definition interval_client_closure_move_offset_ : Z.
  Proof.
    unshelve refine (let x := _ : Z in _). {
      set instrs := interval_client_closure 0 0 0.
      assert (sig (λ l1, ∃ l2, instrs = l1 ++ l2)) as [l1 _]; [do 2 eexists | exact (length l1)].

      assert (forall A (l1 l2 l3 l4: list A), l2 = l3 ++ l4 → l1 ++ l2 = (l1 ++ l3) ++ l4) as step_app.
      { intros * ->. by rewrite app_assoc. }
      assert (forall A (l1 l2 l3: list A) x, l1 = l2 ++ l3 → x :: l1 = (x :: l2) ++ l3) as step_cons.
      { intros * ->. reflexivity. }
      assert (forall A (l1 l2: list A) x, x :: l1 = l2 → x :: l1 = l2) as prepare_cons.
      { auto. }
      assert (forall A (l: list A), l = [] ++ l) as stop.
      { reflexivity. }

      unfold instrs, interval_client_closure.
      (* Program-specific part *)
      eapply step_app. eapply step_cons. eapply step_app.

      repeat (eapply prepare_cons;
              lazymatch goal with
              | |- encodeInstrW (Mov r_t1 _) :: _ = _ => fail
              | _ => eapply step_cons end).
      eapply stop.
    }
    exact x.
  Defined.

  Definition interval_client_closure_move_offset : Z :=
    Eval cbv in interval_client_closure_move_offset_.

  Definition interval_client_closure_instrs_length : Z :=
    Eval cbv in (length (interval_client_closure 0 0 0)).

  (* the namespaces for the three subroutines of the interval library *)
  Definition mkintN : namespace := intN .@ "mkintN".
  Definition iminN : namespace := intN .@ "iminN".
  Definition imaxN : namespace := intN .@ "imaxN".

  (* namespace for the interval environment *)
  Definition envIN : namespace := intN .@ "envIN".

  (* namespace for client code and environment *)
  Definition clientN : namespace := nroot .@ "clientN".
  Definition envCN : namespace := clientN .@ "envCN".
  Definition checkiN : namespace := clientN .@ "checkiN".
  Definition actN : namespace := clientN .@ "actN".

  Definition mallocN : namespace := nroot .@ "mallocN".


  Definition int_bounds i_b i_e i_a_first f_m_i f_s_i i_first s_b s_e s_first offset_to_interval :=
    SubBounds i_b i_e i_a_first (i_a_first ^+ length (interval_closure f_m_i f_s_i offset_to_interval))%a ∧
    SubBounds i_b i_e i_first (i_first ^+ length (interval f_m_i))%a ∧
    SubBounds s_b s_e s_first (s_first ^+ length unseal_instrs
                                       ^+ length (seal_instrs 0)
                                       ^+ length (make_seal_preamble_instrs 0))%a.

  Definition int_table b_r_i e_r_i malloc_r_i makeseal_r_i a_r_i f_m_i f_s_i b_rs e_rs :=
    withinBounds b_r_i e_r_i malloc_r_i = true ∧
    withinBounds b_r_i e_r_i makeseal_r_i = true ∧
    (a_r_i + f_m_i)%a = Some malloc_r_i ∧
    (a_r_i + f_s_i)%a = Some makeseal_r_i ∧
    (b_rs + 1)%a = Some e_rs.

  Definition int_offsets i_a_first i_a_move offset_to_interval i_first :=
    (i_a_first + interval_closure_move_offset)%a = Some i_a_move ∧
    (i_a_move + offset_to_interval)%a = Some i_first.


  Lemma interval_client_closure_functional_spec
        a_first c_first a_move (* client level addresses *)
        pc_p pc_b pc_e (* client level PC *)
        f_a f_i f_mc offset_to_checki (* client level parameters *)
        b_r e_r a_r assert_r fail_cap int_cls_r malloc_r (* client table *)
        f_m_i f_s_i offset_to_interval (* interval parameters *)
        i_b i_e (* interval PC *)
        s_p s_b s_e (* seal PC *)
        i_a_first i_first s_first i_a_move (* interval and seal addresses *)
        b_r_i e_r_i a_r_i malloc_r_i makeseal_r_i (* interval table *)
        b_rs e_rs (* seal table *)
        b_m e_m (* malloc *)
        rmap :

    (* PC assumptions *)
    ExecPCPerm pc_p →
    ExecPCPerm s_p →

    (* Program addresses assumptions for client *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (interval_client_closure f_a f_mc offset_to_checki))%a →
    SubBounds pc_b pc_e c_first (c_first ^+ length (check_interval f_a))%a →

    (* Program adresses assumptions for interval and its nested seal library*)
    (* SubBounds i_b i_e i_a_first (i_a_first ^+ length (interval_closure f_m_i f_s_i offset_to_interval))%a → *)
    (* SubBounds i_b i_e i_first (i_first ^+ length (interval f_m_i))%a → *)
    (* SubBounds s_b s_e s_first (s_first ^+ length unseal_instrs *)
    (*                                    ^+ length (seal_instrs 0) *)
    (*                                    ^+ length (make_seal_preamble_instrs 0))%a → *)
    int_bounds i_b i_e i_a_first f_m_i f_s_i i_first s_b s_e s_first offset_to_interval →

    (* environment table of client: contains the assert subroutine *)
    withinBounds b_r e_r assert_r = true →
    withinBounds b_r e_r int_cls_r = true →
    withinBounds b_r e_r malloc_r = true →
    (a_r + f_a)%a = Some assert_r →
    (a_r + f_i)%a = Some int_cls_r →
    (a_r + f_mc)%a = Some malloc_r →

    (* environment table of interval: contains the makeseal entry, and malloc *)
    (* withinBounds b_r_i e_r_i malloc_r_i = true → *)
    (* withinBounds b_r_i e_r_i makeseal_r_i = true → *)
    (* (a_r_i + f_m_i)%a = Some malloc_r_i → *)
    (* (a_r_i + f_s_i)%a = Some makeseal_r_i → *)
    (* (b_rs + 1)%a = Some e_rs → *)
    int_table b_r_i e_r_i malloc_r_i makeseal_r_i a_r_i f_m_i f_s_i b_rs e_rs →

    (* offset between client preamble and check_interval subroutine *)
    (a_first + interval_client_closure_move_offset)%a = Some a_move →
    (a_move + offset_to_checki)%a = Some c_first →

    (* offset between interval preamble and interval library *)
    (* (i_a_first + interval_closure_move_offset)%a = Some i_a_move → *)
    (* (i_a_move + offset_to_interval)%a = Some i_first → *)
    int_offsets i_a_first i_a_move offset_to_interval i_first →

    (* Code of the client preamble *)
    codefrag a_first (interval_client_closure f_i f_mc offset_to_checki)

    (* Code of the checki subroutine *)
    ∗ codefrag c_first (check_interval f_a)

    (* Environment table for client *)
    ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
    ∗ assert_r ↦ₐ fail_cap
    ∗ int_cls_r ↦ₐ WCap E i_b i_e i_a_first
    ∗ malloc_r ↦ₐ WCap E b_m e_m b_m

    (* Code of the interval preamble *)
    ∗ codefrag i_a_first (interval_closure f_m_i f_s_i offset_to_interval)
    (* Code of the interval code *)
    ∗ codefrag i_first (interval f_m_i)
    (* Environment table for interval library *)
    ∗ i_b ↦ₐ WCap RO b_r_i e_r_i a_r_i
    ∗ malloc_r_i ↦ₐ WCap E b_m e_m b_m
    ∗ makeseal_r_i ↦ₐ WCap E s_b s_e (s_first ^+ length unseal_instrs ^+ length (seal_instrs 0))%a

    (* Code and environment table of the seal library *)
    ∗ codefrag s_first (unseal_instrs ++ seal_instrs 0 ++ make_seal_preamble_instrs 0)
    ∗ s_b ↦ₐ WCap RO b_rs e_rs b_rs ∗ b_rs ↦ₐ WCap E b_m e_m b_m

    (* Malloc invariant *)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)

    -∗ interp_expr interp rmap (WCap pc_p pc_b pc_e a_first).
  Proof.
    iIntros (Hvpc Hspc Hbounds_cls Hbounds Hint_bounds).
    iIntros (Hwb_r Hwb_i Hwb_m Hassert_r Hint_cls_r Hmalloc_r Hint_table).
    iIntros (Ha_move Hc_first Hint_offsets).
    iIntros "(Hclient_cls & Hckecki & Hpc_b & Hassert_r & Hint_cls_r & Hmalloc_r & Hint_cls & Hint & Hi_b &
              Hmalloc_r_i & Hmakeseal_r_i & Hseal & Hs_b & Hb_rs & #Hmalloc)".

    iIntros "((%Hfull&#Hrmap_valid) & Hrmap & Hown)".
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hregs]";
      [by simplify_map_eq|rewrite delete_insert_delete].
    destruct Hfull with r_t0 as [w0 Hr_t0].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr_t0 Hregs]";[by simplify_map_eq|].

    rewrite /interval_client_closure.
    (* trick to speed up tacticts that use solve_addr *)
    Local Opaque int_bounds int_table int_offsets.
    focus_block_0 "Hclient_cls" as "Hblock" "Hcont".
    iApply malloc_spec_alt;iFrameCapSolve;[..|iFrame "Hown Hmalloc Hregs"].
    { rewrite !dom_delete_L. apply regmap_full_dom in Hfull as ->. set_solver+. }
    { auto. }
    { lia. }
    iSplitR. iNext. iIntros (v) "H". iExact "H".
    iSplitR. iNext. iIntros (Hcontr). inversion Hcontr.
    iNext. iIntros "(HPC & Hblock & Hpc_b & Hmalloc_r & Hres & Hr_t0 & Hown & Hregs)".
    iDestruct "Hres" as (b e He) "(Hr_t1 & Hbe)".
    assert (is_Some (b + 1)%a) as [b1 Hb1]. solve_addr +He.
    assert (is_Some (b1 + 1)%a) as [b2 Hb2]. solve_addr +He Hb1.
    assert (b2 + 1 = Some e)%a as Hb3. solve_addr +He Hb1 Hb2.
    rewrite /region_addrs_zeroes /region_size.
    assert (e - b = 3)%Z as ->. solve_addr +He. iSimpl in "Hbe".
    iDestruct (region_mapsto_cons with "Hbe") as "[Hb Hbe]";[eauto|solve_addr +He Hb1 Hb2 Hb3|..].
    iDestruct (region_mapsto_cons with "Hbe") as "[Hb1 Hbe]";[eauto|solve_addr +He Hb1 Hb2 Hb3|..].
    iDestruct (region_mapsto_cons with "Hbe") as "[Hb2 _]";[eauto|solve_addr +He Hb1 Hb2 Hb3|..].
    unfocus_block "Hblock" "Hcont" as "Hcode".

    destruct Hfull with r_t1 as [w1 Hr_t1].
    destruct Hfull with r_t2 as [w2 Hr_t2].
    destruct Hfull with r_t3 as [w3 Hr_t3].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[by simplify_map_eq|].

    focus_block 1 "Hcode" as mid Hmid "Hblock" "Hcont".
    destruct Hfull with r_temp8 as [wtemp8 Hr_temp8].
    iDestruct (big_sepM_delete _ _ r_temp8 with "Hregs") as "[Hr_temp8 Hregs]";[by simplify_map_eq|].
    iGo "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as mid2 Hmid2 "Hblock" "Hcont".
    iApply fetch_spec;iFrameCapSolve.
    iNext. iIntros "(HPC & Hblock & Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Hint_cls_r)".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    destruct Hfull with r_temp7 as [wtemp7 Hr_temp7].
    iDestruct (big_sepM_delete _ _ r_temp7 with "Hregs") as "[Hr_temp7 Hregs]";[by simplify_map_eq|].

    focus_block 3 "Hcode" as a_mid3 Ha_mid3 "Hblock" "Hcont".
    iGo "Hblock".

    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp7 with "[$Hregs $Hr_temp7]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp8 with "[$Hregs $Hr_temp8]") as "Hregs";[by simplify_map_eq|].
    map_simpl "Hregs".

    Local Transparent int_bounds int_table int_offsets.
    iApply interval_closure_functional_spec;iFrameCapSolve;
      [..|iFrame "Hint Hseal Hs_b Hb_rs Hmalloc_r_i Hmakeseal_r_i Hmalloc Hregs Hown"];
      [destruct Hint_bounds as (?&?&?);destruct Hint_table as (?&?&?&?&?);
       destruct Hint_offsets as (?&?);eauto..|].
    { rewrite !dom_insert_L !dom_delete_L. apply regmap_full_dom in Hfull as ->. set_solver+. }
    iSplitR. iIntros (Hcontr). inversion Hcontr.
    iNext.
    iIntros "(HPC & Hint & Hi_b & Hmalloc_r_i & Hmakeseal_r_i & Hr_t0 & Hres & Hint_cls & Hown & Hregs)".
    iDestruct "Hres" as (b0 e0 b3 e1 b4 e3 benv0 eenv γ ll) "Hres".
    iDestruct "Hres" as (ll' a_imin a_imax (He0 & He1 & He3 & Ha_imin & Ha_imax))
                          "(#HsealLL & #HsealN & Hr_t1 & Hr_t2 & Hr_t3 & Hbe & Hbe0 & Hbe3)".
    Local Opaque int_bounds int_table int_offsets.

    rewrite updatePcPerm_cap_non_E;[|by inv Hvpc].
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[rewrite /rmapfinal; by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp7 with "Hregs") as "[Hr_temp7 Hregs]";[rewrite /rmapfinal; by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp8 with "Hregs") as "[Hr_temp8 Hregs]";[rewrite /rmapfinal; by simplify_map_eq|].
    assert ((a_mid3 ^+ 12 + offset_to_checki)%a = Some c_first) as Hlea.
    { rewrite /interval_client_closure_move_offset in Ha_move. simpl in Ha_mid3,Hmid,Hmid2.
      solve_addr+ Ha_mid3 Ha_move Hc_first. }
    iGo "Hblock". solve_addr+ He.
    iGo "Hblock". solve_addr+ He Hb1.
    iGo "Hblock". solve_addr+ He Hb1 Hb2.
    iGo "Hblock". instantiate (1 := b). solve_addr+ He Hb1 Hb2.
    iGo "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_mid4 Ha_mid4 "Hblock" "Hcont".
    rewrite /rmapfinal. map_simpl "Hregs".
    iDestruct (big_sepM_insert _ _ r_t4 with "[$Hregs $Hr_t4]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp7 with "[$Hregs $Hr_temp7]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp8 with "[$Hregs $Hr_temp8]") as "Hregs";[by simplify_map_eq|].
    map_simpl "Hregs".
    iApply crtcls_spec_alt;iFrameCapSolve;[..|iFrame "Hmalloc Hregs Hown"].
    { rewrite !dom_insert_L !dom_delete_L !dom_insert_L !dom_delete_L.
      apply regmap_full_dom in Hfull as ->. set_solver+. }
    auto. iSplitR. iNext. iIntros (v) "H". iExact "H".
    iSplitR. iNext. iIntros (Hcontr). inv Hcontr.
    iNext. iIntros "(HPC & Hblock & Hpc_b & Hmalloc_r & Hres)".
    iDestruct "Hres" as (b' e' He') "(Hr_t1 & Hbe' & Hr_t0 & Hr_t2 & Hown & Hregs)".
    map_simpl "Hregs".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    iDestruct (big_sepM_delete _ _ r_temp8 with "Hregs") as "[Hr_temp8 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp7 with "Hregs") as "[Hr_temp7 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[by simplify_map_eq|].
    focus_block 5 "Hcode" as a_mid5 Ha_mid5 "Hblock" "Hcont".
    map_simpl "Hregs".
    iDestruct ("Hrmap_valid" $! r_t0 w0 _ Hr_t0) as "Hw0_valid". Unshelve. 2:auto.
    iDestruct (jmp_to_unknown _ with "Hw0_valid") as "Hcallback_now".
    iGo "Hblock". split;auto. solve_addr+He.
    iGo "Hblock". split;auto. solve_addr+He Hb1.
    iGo "Hblock". split;auto. solve_addr+He Hb1 Hb2.
    iGo "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    iDestruct (big_sepM_insert _ _ r_temp7 with "[$Hregs $Hr_temp7]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp8 with "[$Hregs $Hr_temp8]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t4 with "[$Hregs $Hr_t4]") as "Hregs";[by simplify_map_eq|].
    map_simpl "Hregs".

    (* we will now allocate the invariants needed by all specs *)
    iMod (na_inv_alloc logrel_nais _ envIN (interval_env b e benv0 eenv RX i_b i_e i_first f_m_i b0 e0
                                                         b3 e1 b4 e3)
            with "[Hb Hb1 Hb2 Hbe Hbe0 Hbe3]") as "#Hint_env".
    { iNext. iExists _,_. iFrame "Hbe". rewrite Ha_imin. iFrame "Hbe0". iSimpl.
      assert (a_imin ^+ 12%nat = a_imax)%a as ->. solve_addr+Ha_imin Ha_imax.
      iFrame "Hbe3". iFrame. repeat iSplit;auto. iPureIntro. by constructor.
      all: iPureIntro. Local Transparent int_bounds int_table int_offsets.
      all: destruct Hint_bounds as (?&?&?);destruct Hint_table as (?&?&?&?&?);
        destruct Hint_offsets as (?&?). solve_addr +H0. 1,2:solve_addr +H0 Ha_imax Ha_imin. }

    iMod (na_inv_alloc logrel_nais _ envCN (pc_b ↦ₐ WCap RO b_r e_r a_r  ∗ assert_r ↦ₐ fail_cap)%I
            with "[$Hpc_b $Hassert_r]") as "#Hclient_env".
    iMod (na_inv_alloc logrel_nais _ envCN (i_b ↦ₐ WCap RO b_r_i e_r_i a_r_i ∗ malloc_r_i ↦ₐ WCap E b_m e_m b_m)%I
            with "[$Hi_b $Hmalloc_r_i]") as "#Hmakeint_env".

    iMod (na_inv_alloc logrel_nais _ checkiN with "Hckecki") as "#Hchecki".

    rewrite /interval.
    iAssert (codefrag i_first (makeint f_m_i)
           ∗ codefrag a_imin imin
           ∗ codefrag a_imax imax)%I with "[Hint]" as "(Hmkint & Himin & Himax)".
    { iClear "#". rewrite /codefrag /region_mapsto. rewrite (region_addrs_split i_first a_imin).
      2: solve_addr+Ha_imin. rewrite (region_addrs_split a_imin a_imax).
      2: solve_addr+Ha_imin Ha_imax.
      iDestruct (big_sepL2_app' with "Hint") as "[Hmkint Hint]";cycle 1.
      iDestruct (big_sepL2_app' with "Hint") as "[Himin Himax]";cycle 1.
      rewrite Ha_imin. assert ((a_imin ^+ length imin)%a = a_imax) as ->.
      solve_addr+Ha_imin Ha_imax.
      assert (i_first ^+ length (makeint f_m_i ++ imin ++ imax) = a_imax ^+ length imax)%a as ->.
      solve_addr+Ha_imin Ha_imax. iFrame.
      all: rewrite app_length /= region_addrs_length /region_size.
      all: solve_addr+Ha_imin Ha_imax. }

    iMod (na_inv_alloc logrel_nais _ mkintN with "Hmkint") as "#Hmkint".
    iMod (na_inv_alloc logrel_nais _ iminN with "Himin") as "#Himin".
    iMod (na_inv_alloc logrel_nais _ imaxN with "Himax") as "#Himax".

    iMod (na_inv_alloc logrel_nais _ actN with "Hbe'") as "#Hact".


    (** establish validity of all exposed entry points **)

    (* CHECKINT *)
    iAssert (interp (WCap E b' e' b')) as "Hval1".
    { iApply fixpoint_interp1_eq. iIntros (r). iNext. iModIntro.
      iIntros "((%Hfullr & #Hr_valid) & Hr & Hown)".
      iDestruct (big_sepM_delete _ _ PC with "Hr") as "[HPC Hregs]";
        [by simplify_map_eq|rewrite delete_insert_delete].
      iMod (na_inv_acc with "Hact Hown") as "(>Hact_code & Hown & Hcls)";auto.
      destruct Hfullr with r_t20 as [w20 Hr_t20].
      iDestruct (big_sepM_delete _ _ r_t20 with "Hregs") as "[Hr_t20 Hregs]";[by simplify_map_eq|].
      destruct Hfullr with r_env as [wenv Hr_env].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]";[by simplify_map_eq|].

      iApply closure_activation_spec;iFrameCapSolve. iFrame "Hact_code".
      iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hbe')".
      iMod ("Hcls" with "[$Hown $Hbe']") as "Hown".
      rewrite updatePcPerm_cap_non_E;[|by inv Hvpc].

      destruct Hfullr with r_t1 as [w1' Hr_t1'].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[by simplify_map_eq|].
      destruct Hfullr with r_t0 as [w0' Hr_t0'].
      iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr_t0 Hregs]";[by simplify_map_eq|].
      iApply (check_interval_spec with "[- $Hint_env $HsealN $HsealLL $Hown $Hclient_env]");iFrameCapSolve.
      10: rewrite Ha_imin /=.
      10: assert ((a_imin ^+ 12%nat)%a = a_imax) as ->;[solve_addr +Ha_imax Ha_imin|].
      10: iFrame "Hchecki Himin Himax".
      all: try solve_ndisj. all: cycle 1.
      { iSplitL "Hr_t20";[eauto|].
        iFrame "Hregs". iSplit. iApply ("Hr_valid" $! r_t0);auto.
        iApply big_sepM_forall. iIntros (reg w Hin).
        iApply ("Hr_valid" $! reg). iPureIntro. destruct (decide (reg = PC));auto;simplify_map_eq.
        clear -Hin.
        repeat match goal with
          _ : delete ?rr _ !! _ = Some _ |- _ => destruct (decide (rr = reg));simplify_map_eq
        end.
        done. }
      { iNext. iIntros (v) "H". iFrame. }
      { rewrite !dom_delete_L. apply regmap_full_dom in Hfullr as ->. set_solver+. }
    }

    (* MAKEINT *)
    iAssert (interp (WCap E b0 e0 b0)) as "Hval2".
    { iApply fixpoint_interp1_eq. iIntros (r). iNext. iModIntro.
      iIntros "((%Hfullr & #Hr_valid) & Hr & Hown)".
      iDestruct (big_sepM_delete _ _ PC with "Hr") as "[HPC Hregs]";
        [by simplify_map_eq|rewrite delete_insert_delete].
      iMod (na_inv_acc with "Hint_env Hown") as "(>Hact_code & Hown & Hcls)";auto.
      iDestruct "Hact_code" as (? ? (?&?&?)) "(Hb&Hb1&Hb2&%Heq&%Hbounds'&Hact1&Hact2&Hact3)".
      destruct Hbounds' as (?&?). destruct Heq as (?&?&?). simplify_eq.
      destruct Hfullr with r_t20 as [w20 Hr_t20].
      iDestruct (big_sepM_delete _ _ r_t20 with "Hregs") as "[Hr_t20 Hregs]";[by simplify_map_eq|].
      destruct Hfullr with r_env as [wenv Hr_env].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]";[by simplify_map_eq|].

      iApply closure_activation_spec;iFrameCapSolve. iFrame "Hact1".
      iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hbe')".
      iMod ("Hcls" with "[$Hown $Hbe' $Hact2 $Hact3 $Hb Hb1 Hb2]") as "Hown".
      { iNext. iExists _,_. iFrame. auto. }
      rewrite updatePcPerm_cap_non_E;[|by inv Hvpc].

      destruct Hfullr with r_t0 as [w0' Hr_t0'].
      iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr_t0 Hregs]";[by simplify_map_eq|].
      Local Transparent int_table.
      destruct Hint_table as (?&?&?&?&?).
      iApply (makint_valid with "[- $Hmakeint_env $Hmalloc $Hmkint $Hregs $HsealLL $HsealN]");iFrameCapSolve.
      solve_addr+ H3.
      { rewrite !dom_delete_L. apply regmap_full_dom in Hfullr as ->. set_solver+. }
      all: try solve_ndisj. iSplitL "Hr_t20";[eauto|]. iFrame.
      iSplit. iApply ("Hr_valid" $! r_t0);auto.
      iApply big_sepM_forall. iIntros (reg w Hin).
      iApply ("Hr_valid" $! reg). iPureIntro. destruct (decide (reg = PC));auto;simplify_map_eq.
      clear -Hin.
      repeat match goal with
               _ : delete ?rr _ !! _ = Some _ |- _ => destruct (decide (rr = reg));simplify_map_eq
             end.
      done.
      iNext. iIntros (v) "H". iFrame.
    }

    (* IMIN *)
    iAssert (interp (WCap E b3 e1 b3)) as "Hval3".
    { iApply fixpoint_interp1_eq. iIntros (r). iNext. iModIntro.
      iIntros "((%Hfullr & #Hr_valid) & Hr & Hown)".
      iDestruct (big_sepM_delete _ _ PC with "Hr") as "[HPC Hregs]";
        [by simplify_map_eq|rewrite delete_insert_delete].
      iMod (na_inv_acc with "Hint_env Hown") as "(>Hact_code & Hown & Hcls)";auto.
      iDestruct "Hact_code" as (? ? (?&?&?)) "(Hb&Hb1&Hb2&%Heq&%Hbounds'&Hact1&Hact2&Hact3)".
      destruct Hbounds' as (?&?). destruct Heq as (?&?&?). simplify_eq.
      destruct Hfullr with r_t20 as [w20 Hr_t20].
      iDestruct (big_sepM_delete _ _ r_t20 with "Hregs") as "[Hr_t20 Hregs]";[by simplify_map_eq|].
      destruct Hfullr with r_env as [wenv Hr_env].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]";[by simplify_map_eq|].

      iApply closure_activation_spec;iFrameCapSolve. iFrame "Hact2".
      iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hbe')".
      iMod ("Hcls" with "[$Hown $Hbe' $Hact1 $Hact3 $Hb Hb1 Hb2]") as "Hown".
      { iNext. iExists _,_. iFrame. auto. }
      rewrite updatePcPerm_cap_non_E;[|by inv Hvpc].

      destruct Hfullr with r_t0 as [w0' Hr_t0'].
      iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr_t0 Hregs]";[by simplify_map_eq|].
      Local Transparent int_table.
      destruct Hint_table as (?&?&?&?&?).
      rewrite Ha_imin. iSimpl in "HPC".
      iApply (imin_valid with "[- $Himin $Hregs $HsealLL $HsealN]");iFrameCapSolve.
      solve_addr+ H3 Ha_imin.
      { rewrite !dom_delete_L. apply regmap_full_dom in Hfullr as ->. set_solver+. }
      all: try solve_ndisj. iSplitL "Hr_t20";[eauto|]. iFrame.
      iSplit. iApply ("Hr_valid" $! r_t0);auto.
      iApply big_sepM_forall. iIntros (reg w Hin).
      iApply ("Hr_valid" $! reg). iPureIntro. destruct (decide (reg = PC));auto;simplify_map_eq.
      clear -Hin.
      repeat match goal with
               _ : delete ?rr _ !! _ = Some _ |- _ => destruct (decide (rr = reg));simplify_map_eq
             end.
      done.
      iNext. iIntros (v) "H". iFrame.
    }

    (* IMAX *)
    iAssert (interp (WCap E b4 e3 b4)) as "Hval4".
    { iApply fixpoint_interp1_eq. iIntros (r). iNext. iModIntro.
      iIntros "((%Hfullr & #Hr_valid) & Hr & Hown)".
      iDestruct (big_sepM_delete _ _ PC with "Hr") as "[HPC Hregs]";
        [by simplify_map_eq|rewrite delete_insert_delete].
      iMod (na_inv_acc with "Hint_env Hown") as "(>Hact_code & Hown & Hcls)";auto.
      iDestruct "Hact_code" as (? ? (?&?&?)) "(Hb&Hb1&Hb2&%Heq&%Hbounds'&Hact1&Hact2&Hact3)".
      destruct Hbounds' as (?&?). destruct Heq as (?&?&?). simplify_eq.
      destruct Hfullr with r_t20 as [w20 Hr_t20].
      iDestruct (big_sepM_delete _ _ r_t20 with "Hregs") as "[Hr_t20 Hregs]";[by simplify_map_eq|].
      destruct Hfullr with r_env as [wenv Hr_env].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]";[by simplify_map_eq|].

      iApply closure_activation_spec;iFrameCapSolve. iFrame "Hact3".
      iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hbe')".
      iMod ("Hcls" with "[$Hown $Hbe' $Hact1 $Hact2 $Hb Hb1 Hb2]") as "Hown".
      { iNext. iExists _,_. iFrame. auto. }
      rewrite updatePcPerm_cap_non_E;[|by inv Hvpc].

      destruct Hfullr with r_t0 as [w0' Hr_t0'].
      iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr_t0 Hregs]";[by simplify_map_eq|].
      Local Transparent int_table.
      destruct Hint_table as (?&?&?&?&?).
      rewrite Ha_imin. iSimpl in "HPC".
      assert (a_imin ^+ 12%nat = a_imax)%a as ->;[solve_addr +Ha_imax Ha_imin|].
      iApply (imax_valid with "[- $Himax $Hregs $HsealLL $HsealN]");iFrameCapSolve.
      solve_addr+ H3 Ha_imin Ha_imax.
      { rewrite !dom_delete_L. apply regmap_full_dom in Hfullr as ->. set_solver+. }
      all: try solve_ndisj. iSplitL "Hr_t20";[eauto|]. iFrame.
      iSplit. iApply ("Hr_valid" $! r_t0);auto.
      iApply big_sepM_forall. iIntros (reg w Hin).
      iApply ("Hr_valid" $! reg). iPureIntro. destruct (decide (reg = PC));auto;simplify_map_eq.
      clear -Hin.
      repeat match goal with
               _ : delete ?rr _ !! _ = Some _ |- _ => destruct (decide (rr = reg));simplify_map_eq
             end.
      done.
      iNext. iIntros (v) "H". iFrame.
    }

    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hregs $Hr_t0]") as "Hregs";[by simplify_map_eq|].
    map_simpl "Hregs".

    iApply ("Hcallback_now" with "[] [$HPC $Hown Hregs]"); cycle 1.
    { iApply big_sepM_sep. iFrame.
      repeat (iApply big_sepM_insert_2; [done|]).
      repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
      iApply big_sepM_forall. iIntros (k x Hin). iApply ("Hrmap_valid" $! k).
      all: destruct (decide (k = PC));simplify_map_eq;auto. }
    { iPureIntro. rewrite !dom_insert_L !dom_delete_L. apply regmap_full_dom in Hfull as ->. set_solver+. }
  Qed.

End interval_client.
