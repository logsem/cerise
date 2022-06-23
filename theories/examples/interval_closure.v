From iris.algebra Require Import agree auth gmap.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous fundamental.
From cap_machine Require Import dynamic_sealing interval keylist malloc.
From cap_machine Require Import solve_pure proofmode map_simpl.

Section interval_closure.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {sealG: sealLLG Σ}
          `{MP: MachineParameters}.

  Definition interval f_m :=
    (makeint f_m) ++ imin ++ imax.

  Definition r_temp1 := r_t21.
  Definition r_temp2 := r_t22.
  Definition r_temp3 := r_t23.
  Definition r_temp4 := r_t24.
  Definition r_temp6 := r_t26.


  Definition interval_closure (f_m f_s offset_to_interval : Z) :=
    (* allocate the environment of the interval library *)
    malloc_instrs f_m 2%nat ++
    encodeInstrsW [ Mov r_temp1 r_t1 ] ++
    (* jump to the makeseal subroutine *)
    fetch_instrs f_s ++
    encodeInstrsW [ Mov r_temp6 r_t0;
                  Mov r_t0 PC;
                  Lea r_t0 3;
                  Jmp r_t1;
                  (* store entry points into interval library *)
                  Store r_temp1 r_t1;
                  Lea r_temp1 1;
                  Store r_temp1 r_t2;
                  Lea r_temp1 (-1)%Z;
                  (* prepare to create a closure around makeint *)
                  Mov r_t2 r_temp1;
                  Mov r_t1 PC;
                  Lea r_t1 offset_to_interval;
                  Mov r_temp2 r_t1] ++
    (* create closure around makeint and the seal environment *)
    crtcls_instrs f_m ++
    (* we will need to store the result somewhere safe *)
    encodeInstrsW [ Mov r_temp3 r_t1;
                  (* prepare to create a closure around imin *)
                  Mov r_t2 r_temp1;
                  Mov r_t1 r_temp2;
                  Lea r_t1 (strings.length (makeint f_m));
                  Mov r_temp2 r_t1] ++
    (* create closure around imin and the seal environment *)
    crtcls_instrs f_m ++
    (* we will need to store the result somewhere safe *)
    encodeInstrsW [ Mov r_temp4 r_t1;
                  (* prepare to create a closure around imax *)
                  Mov r_t2 r_temp1;
                  Mov r_t1 r_temp2;
                  Lea r_t1 (strings.length imin)] ++
    (* create closure around imin and the seal environment *)
    crtcls_instrs f_m ++
    (* cleanup *)
    encodeInstrsW [ Mov r_t0 r_temp6;
                  Mov r_t3 r_t1;
                  Mov r_t2 r_temp4;
                  Mov r_t1 r_temp3;
                  Mov r_temp1 0;
                  Mov r_temp4 0;
                  Mov r_temp3 0;
                  Mov r_temp6 0;
                  Mov r_temp2 0;
                  Jmp r_t0 ].

  Definition intN : namespace := nroot .@ "intervalN".
  Definition sealN : namespace := intN .@ "sealN".
  Definition sealLLN : namespace := intN .@ "sealLLN".

  Definition interval_closure_move_offset_ : Z.
  Proof.
    unshelve refine (let x := _ : Z in _). {
      set instrs := interval_closure 0 0 0.
      assert (sig (λ l1, ∃ l2, instrs = l1 ++ l2)) as [l1 _]; [do 2 eexists | exact (length l1)].

      assert (forall A (l1 l2 l3 l4: list A), l2 = l3 ++ l4 → l1 ++ l2 = (l1 ++ l3) ++ l4) as step_app.
      { intros * ->. by rewrite app_assoc. }
      assert (forall A (l1 l2 l3: list A) x, l1 = l2 ++ l3 → x :: l1 = (x :: l2) ++ l3) as step_cons.
      { intros * ->. reflexivity. }
      assert (forall A (l1 l2: list A) x, x :: l1 = l2 → x :: l1 = l2) as prepare_cons.
      { auto. }
      assert (forall A (l: list A), l = [] ++ l) as stop.
      { reflexivity. }

      unfold instrs, interval_closure.
      (* Program-specific part *)
      eapply step_app. eapply step_app. eapply step_app.

      repeat (eapply prepare_cons;
              lazymatch goal with
              | |- encodeInstrW (Mov r_t1 _) :: _ = _ => fail
              | _ => eapply step_cons end).
      eapply stop.
    }
    exact x.
  Defined.

  Definition interval_closure_move_offset : Z :=
    Eval cbv in interval_closure_move_offset_.

  Definition interval_closure_instrs_length : Z :=
    Eval cbv in (length (interval_closure 0 0 0)).

  Definition rmapfinal rmap : Reg :=
    delete r_t3 (delete r_t1 (delete r_t2 (<[r_temp1:=WInt 0]> (<[r_temp2:=WInt 0]> (<[r_temp3:=WInt 0]>
     (<[r_temp4:=WInt 0]> (<[r_temp6:=WInt 0]> (<[r_t4:=WInt 0]> (<[r_t5:=WInt 0]>
      (<[r_t6:=WInt 0]> (<[r_t7:=WInt 0]> (<[r_t8:=WInt 0]>
       (<[r_t9:=WInt 0]> (<[r_t10:=WInt 0]> rmap)))))))))))))).


  Lemma interval_closure_functional_spec f_m f_s offset_to_interval
        a_first i_first s_first a_move
        pc_p pc_b pc_e
        s_p s_b s_e
        b_r e_r a_r malloc_r makeseal_r
        b_rs e_rs
        b_m e_m mallocN
        wret rmap Φ :

    (* PC assumptions *)
    ExecPCPerm pc_p →
    ExecPCPerm s_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (interval_closure f_m f_s offset_to_interval))%a →
    SubBounds pc_b pc_e i_first (i_first ^+ length (interval f_m))%a →
    SubBounds s_b s_e s_first (s_first ^+ (length unseal_instrs
                                           + length (seal_instrs 0)
                                           + length (make_seal_preamble_instrs 0)))%a →

    (* environment table: contains the makeseal entry, and malloc *)
    withinBounds b_r e_r malloc_r = true →
    withinBounds b_r e_r makeseal_r = true →
    (a_r + f_m)%a = Some malloc_r →
    (a_r + f_s)%a = Some makeseal_r →
    (b_rs + 1)%a = Some e_rs →

    (* offset between preamble and interval library *)
    (a_first + interval_closure_move_offset)%a = Some a_move →
    (a_move + offset_to_interval)%a = Some i_first →

    (* registers *)
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0]} →

    (* Code of the preamble *)
    codefrag a_first (interval_closure f_m f_s offset_to_interval)

    (* Code of the interval code *)
    ∗ codefrag i_first (interval f_m)

    (* Code and environment table of the seal library *)
    ∗ codefrag s_first (unseal_instrs ++ seal_instrs 0 ++ make_seal_preamble_instrs 0)
    ∗ s_b ↦ₐ WCap RO b_rs e_rs b_rs ∗ b_rs ↦ₐ WCap E b_m e_m b_m

    (* Environment table for interval library *)
    ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
    ∗ malloc_r ↦ₐ WCap E b_m e_m b_m
    ∗ makeseal_r ↦ₐ WCap E s_b s_e (s_first ^+ (length unseal_instrs + length (seal_instrs 0)))%a
    (* Malloc invariant *)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)

    (* registers *)
    ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ r_t0 ↦ᵣ wret
    ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)

    (* NA inv token *)
    ∗ na_own logrel_nais ⊤

    (* continuation *)
    ∗ Φ FailedV
    ∗ ▷ ( PC ↦ᵣ updatePcPerm wret
         ∗ codefrag i_first (interval f_m)
         ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
         ∗ malloc_r ↦ₐ WCap E b_m e_m b_m
         ∗ makeseal_r ↦ₐ WCap E s_b s_e (s_first ^+ (length unseal_instrs + length (seal_instrs 0)))%a
         ∗ r_t0 ↦ᵣ wret
         ∗ (∃ b e b0 e0 b3 e3 benv0 eenv γ ll ll' a_imin a_imax,
               ⌜(b + 8)%a = Some e
               ∧ (b0 + 8)%a = Some e0
               ∧ (b3 + 8)%a = Some e3
               ∧ (i_first + length (makeint f_m))%a = Some a_imin
               ∧ (i_first + length (makeint f_m ++ imin))%a = Some a_imax⌝
         ∗ sealLL sealLLN ll γ isInterval
         ∗ na_inv logrel_nais sealN (seal_env benv0 eenv ll ll' RX s_b s_e s_first b_m e_m b_rs e_rs)
         ∗ r_t1 ↦ᵣ WCap E b e b
         ∗ r_t2 ↦ᵣ WCap E b0 e0 b0
         ∗ r_t3 ↦ᵣ WCap E b3 e3 b3
         ∗ [[b,e]]↦ₐ[[activation_instrs (WCap pc_p pc_b pc_e i_first) (WCap RWX benv0 eenv benv0)]]
         ∗ [[b0,e0]]↦ₐ[[activation_instrs (WCap pc_p pc_b pc_e a_imin) (WCap RWX benv0 eenv benv0)]]
         ∗ [[b3,e3]]↦ₐ[[activation_instrs (WCap pc_p pc_b pc_e a_imax) (WCap RWX benv0 eenv benv0)]])
         ∗ codefrag a_first (interval_closure f_m f_s offset_to_interval)
         ∗ na_own logrel_nais ⊤
         ∗ ([∗ map] k↦y ∈ rmapfinal rmap, k ↦ᵣ y)
         -∗ WP Seq (Instr Executable) {{ Φ }} )


      ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hpc_p Hs_p Hbounds_preamble Hbounds_interval Hbounds_seal Hwb_mallocr Hwb_makesealr
                   Hlink_mallocr Hlink_makesealr Hsealtable Ha_move Hi_first Hdom).
    iIntros "(Hcode & Hinterval & Hseal & Hs_b & Hb_rs & Hpc_b & Hmalloc_r & Hmakeseal_r & #Hmalloc
              & HPC & Hr_t0 & Hregs & Hown & Hfailed & HΦ)".

    rewrite /interval_closure.

    focus_block_0 "Hcode" as "Hblock" "Hcont".

    (* malloc *)
    iApply (wp_wand _ _ _ (λ v, ((((Φ v ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)
                                  ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)%I
              with "[- Hfailed]"); cycle 1.
    { iIntros (v) "[ [ [ [ [H1 | H1] | H1] | H1] | H1] | H1]";iFrame; iDestruct "H1" as "->"; iFrame. }
    iApply malloc_spec;iFrameAutoSolve;[..|iFrame "Hmalloc Hown Hregs"];[auto|auto|clear;lia|..].
    iNext. iIntros "(HPC & Hblock & Hpc_b & Hmalloc_r & Henv & Hr_t0 & Hown & Hregs)".
    iDestruct "Henv" as (benv0 eenv Henvsize) "(Hr_t1 & Hbeenv)".

    (* malloc region cleanup *)
    assert (is_Some (benv0 + 1)%a) as [benv1 Henvincr];[solve_addr+Henvsize|].
    rewrite /region_addrs_zeroes /finz.dist.
    assert (Z.to_nat (eenv - benv0) = 2) as ->;[solve_addr+Henvsize|]. iSimpl in "Hbeenv".
    iDestruct (region_mapsto_cons with "Hbeenv") as "[Hbenv0 Hbeenv]";
      [eauto|solve_addr+Henvincr Henvsize|..].
    rewrite /region_mapsto finz_seq_between_singleton;[|solve_addr+Henvsize Henvincr].
    iDestruct "Hbeenv" as "[Hbenv1 _]".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    (* get some general purpose registers *)
    assert (is_Some (rmap !! r_temp1)) as [w Hr_temp1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete _ _ r_temp1 with "Hregs") as "[Hr_temp1 Hregs]".
    { rewrite !lookup_insert_ne// lookup_delete_ne//. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[by simplify_map_eq|].

    (* Mov r_temp1 r_t1 *)
    focus_block 1 "Hcode" as a_mid0 Ha_mid0 "Hblock" "Hcont".
    iInstr "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    (* fetch the makeseal capability *)
    focus_block 2 "Hcode" as a_mid1 Ha_mid1 "Hblock" "Hcont".
    iApply fetch_spec;iFrameAutoSolve.
    iNext. iIntros "(HPC & Hblock & Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Hmakeseal_r)".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    (* prepare to jump to makeseal *)
    assert (is_Some (rmap !! r_temp6)) as [w0 Hr_temp6];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete _ _ r_temp6 with "Hregs") as "[Hr_temp6 Hregs]".
    { rewrite !lookup_delete_ne// !lookup_insert_ne// lookup_delete_ne//. }
    focus_block 3 "Hcode" as a_mid2 Ha_mid2 "Hblock" "Hcont".
    iGo "Hblock".

    (* reconstruct registers *)
    iDestruct (big_sepM_insert _ _ r_temp1 with "[$Hregs $Hr_temp1]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp6 with "[$Hregs $Hr_temp6]") as "Hregs"; [by simplify_map_eq|].

    repeat (rewrite -(delete_insert_ne _ r_t1)//); rewrite !(delete_commute _ _ r_t1)//;
    rewrite -(delete_insert_ne _ r_t1)// -(delete_insert_ne _ r_t1)// -(delete_insert_ne _ r_t1)//.
    rewrite insert_delete_insert.

    repeat (rewrite -(delete_insert_ne _ r_t2)//); rewrite !(delete_commute _ _ r_t2)//.
    rewrite -(delete_insert_ne _ r_t2)//. rewrite insert_delete_insert.

    do 4 (rewrite -(delete_insert_ne _ r_temp6)//). rewrite insert_delete_insert.

    rewrite (delete_commute _ _ r_temp1)//. rewrite insert_delete_insert.

    rewrite (insert_commute _ r_t2 r_t3)//. rewrite delete_insert_delete.
    do 2 (rewrite -(delete_insert_ne _ r_t3)//). rewrite insert_delete_insert.

    rewrite (insert_commute _ r_temp1 r_t2)//. rewrite insert_insert.

    iApply make_seal_spec;iFrameAutoSolve;[..|iFrame "Hmalloc Hb_rs Hown Hregs"].
    { rewrite !dom_insert_L. rewrite Hdom. set_solver+. }
    { solve_addr+Hsealtable. }
    { solve_addr+Hsealtable. }
    { solve_ndisj. }
    iNext. iIntros "(HPC & Hr_t0 & Hs_b & Hb_rs & Hseal_res & Hregs & Hseal & Hown)".
    iDestruct "Hseal_res" as (b1 e1 b2 e2 ll ll')
                               "(Hr_t1 & Hr_t2 & %He1 & %He2 & Hact1 & Hact2 & %Hll & HsealLL)".
    iDestruct "HsealLL" as (γ) "#HsealLL".

    (* get some registers *)
    rewrite !(insert_commute _ _ r_temp1)// !(delete_insert_ne _ _ r_temp1)//
            !(insert_commute _ _ r_temp1)//.
    assert (is_Some (rmap !! r_temp2)) as [w1 Hr_temp2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete _ _ r_temp2 with "Hregs") as "[Hr_temp2 Hregs]".
    { rewrite !lookup_insert_ne// !lookup_delete_ne// !lookup_insert_ne//. }
    rewrite delete_insert_ne//.
    iDestruct (big_sepM_delete _ _ r_temp1 with "Hregs") as "[Hr_temp1 Hregs]";[by simplify_map_eq|].
    rewrite delete_insert_delete.

    rewrite updatePcPerm_cap_non_E;[|inv Hpc_p;auto].
    iGo "Hblock". solve_addr+Henvsize Henvincr.
    iGo "Hblock". solve_addr+Henvsize Henvincr.
    iGo "Hblock". assert (benv1 + -1 = Some benv0)%a;[solve_addr+Henvsize Henvincr|]. eauto.

    assert ((a_mid2 ^+ 9 + offset_to_interval)%a = Some i_first) as Hlea.
    { clear- Ha_mid2 Ha_move Hi_first. cbn in *.
      unfold interval_closure_move_offset in Ha_move. solve_addr. }
    iGo "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    (* We can now allocate the seal environment invariant *)
    iMod (na_inv_alloc logrel_nais _ sealN (seal_env benv0 eenv ll ll' RX s_b s_e s_first b_m e_m b_rs e_rs)
            with "[Hact1 Hact2 Hb_rs Hs_b Hbenv0 Hbenv1 Hseal]") as "#Hseal_env".
    { iNext. iFrame. iExists _,_,_,_,_. iFrame. repeat iSplit;eauto.
      all: iPureIntro. by constructor. inversion Hbounds_seal;auto. solve_addr+.
      destruct Hbounds_seal as (?&?&Hle). rewrite 3!app_length /=. solve_addr+Hle. }
    instantiate (3 := sealLLN). instantiate (2 := isInterval). Unshelve. 2: apply _.

    focus_block 4 "Hcode" as a_mid3 Ha_mid3 "Hblock" "Hcont".

    iDestruct (big_sepM_insert _ _ r_temp1 with "[$Hregs $Hr_temp1]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp2 with "[$Hregs $Hr_temp2]") as "Hregs";[by simplify_map_eq|].
    map_simpl "Hregs".

    iApply crtcls_spec;iFrameAutoSolve;[..|iFrame "Hmalloc Hregs Hown"].
    { rewrite !dom_insert_L !dom_delete_L !dom_insert_L Hdom. set_solver+. }
    { solve_ndisj. }
    iNext. iIntros "(HPC & Hblock & Hpc_b & Hmalloc_r & Hres)".
    iDestruct "Hres" as (b e He) "(Hr_t1 & Hact & Hr_t0 & Hr_t2 & Hown & Hregs)".
    map_simpl "Hregs".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    focus_block 5 "Hcode" as a_mid4 Ha_mid4 "Hblock" "Hcont".
    iDestruct (big_sepM_delete _ _ r_temp1 with "Hregs") as "[Hr_temp1 Hregs]";[by simplify_map_eq|].
    assert (is_Some (rmap !! r_temp3)) as [w3 Hr_temp3];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete _ _ r_temp3 with "Hregs") as "[Hr_temp3 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp2 with "Hregs") as "[Hr_temp2 Hregs]";[by simplify_map_eq|].

    rewrite /interval.
    iDestruct (codefrag_contiguous_region with "Hinterval") as %Hint_cont.
    assert (ContiguousRegion i_first (length (makeint f_m))) as [a_imin Ha_imin];[solve_addr+Hint_cont|].
    iGo "Hblock".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    iDestruct (big_sepM_insert _ _ r_temp1 with "[$Hregs $Hr_temp1]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp2 with "[$Hregs $Hr_temp2]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp3 with "[$Hregs $Hr_temp3]") as "Hregs"; [by simplify_map_eq|].
    map_simpl "Hregs".
    focus_block 6 "Hcode" as a_mid5 Ha_mid5 "Hblock" "Hcont".

    iApply crtcls_spec;iFrameAutoSolve;[..|iFrame "Hmalloc Hregs Hown"].
    { rewrite !dom_insert_L !dom_delete_L !dom_insert_L Hdom. set_solver+. }
    { solve_ndisj. }
    iNext. iIntros "(HPC & Hblock & Hpc_b & Hmalloc_r & Hres)".
    iDestruct "Hres" as (b0 e0 He0) "(Hr_t1 & Hact0 & Hr_t0 & Hr_t2 & Hown & Hregs)".
    map_simpl "Hregs".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    focus_block 7 "Hcode" as a_mid6 Ha_mid6 "Hblock" "Hcont".
    assert (is_Some (rmap !! r_temp4)) as [w4 Hr_temp4];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete _ _ r_temp4 with "Hregs") as "[Hr_temp4 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp1 with "Hregs") as "[Hr_temp1 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp2 with "Hregs") as "[Hr_temp2 Hregs]";[by simplify_map_eq|].
    assert (ContiguousRegion i_first (length (makeint f_m ++ imin))) as [a_imax Ha_imax];
      [solve_addr+Hint_cont|].
    iGo "Hblock". instantiate (1:=a_imax). solve_addr+Ha_imax Ha_imin.
    unfocus_block "Hblock" "Hcont" as "Hcode".

    iDestruct (big_sepM_insert _ _ r_temp1 with "[$Hregs $Hr_temp1]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp2 with "[$Hregs $Hr_temp2]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp4 with "[$Hregs $Hr_temp4]") as "Hregs"; [by simplify_map_eq|].
    map_simpl "Hregs".

    focus_block 8 "Hcode" as a_mid7 Ha_mid7 "Hblock" "Hcont".

    iApply crtcls_spec;iFrameAutoSolve;[..|iFrame "Hmalloc Hregs Hown"].
    { rewrite !dom_insert_L !dom_delete_L !dom_insert_L Hdom. set_solver+. }
    { solve_ndisj. }
    iNext. iIntros "(HPC & Hblock & Hpc_b & Hmalloc_r & Hres)".
    iDestruct "Hres" as (b3 e3 He3) "(Hr_t1 & Hact3 & Hr_t0 & Hr_t2 & Hown & Hregs)".
    map_simpl "Hregs".
    unfocus_block "Hblock" "Hcont" as "Hcode".

    focus_block 9 "Hcode" as a_mid8 Ha_mid8 "Hblock" "Hcont".
    iDestruct (big_sepM_delete _ _ r_temp6 with "Hregs") as "[Hr_temp6 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp1 with "Hregs") as "[Hr_temp1 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp2 with "Hregs") as "[Hr_temp2 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp3 with "Hregs") as "[Hr_temp3 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_temp4 with "Hregs") as "[Hr_temp4 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[by simplify_map_eq|].
    map_simpl "Hregs".
    iGo "Hblock".
    iDestruct (big_sepM_insert _ _ r_temp6 with "[$Hregs $Hr_temp6]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp4 with "[$Hregs $Hr_temp4]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp3 with "[$Hregs $Hr_temp3]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp2 with "[$Hregs $Hr_temp2]") as "Hregs"; [by simplify_map_eq|].
    iDestruct (big_sepM_insert _ _ r_temp1 with "[$Hregs $Hr_temp1]") as "Hregs"; [by simplify_map_eq|].
    map_simpl "Hregs". unfocus_block "Hblock" "Hcont" as "Hcode".
    repeat rewrite -(delete_insert_ne _ r_t3)//.
    repeat rewrite -(delete_insert_ne _ r_t1)//.
    repeat rewrite -(delete_insert_ne _ r_t2)//.

    (* continuation *)
    iApply "HΦ". unfold rmapfinal. iFrame. iExists _,_,_,_,_,_,_,_.
    iExists _,_,_,_,_. iFrame. iFrame "#". auto.
  Qed.


End interval_closure.
