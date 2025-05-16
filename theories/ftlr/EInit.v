From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_EInit.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Local Hint Resolve finz_seq_between_NoDup list_remove_elem_NoDup : core.


  (** Predicate that defines when the contents of a register can be swept;
      i.e. when the register contains a capability with at least R permissions... *)
  Definition reg_allows_einit_code
    (lregs : LReg) (r : RegName)
    (p : Perm) (b e a : Addr) (v : Version):=
    lregs !! r = Some (LCap p b e a v) ∧ p = RX.

  Definition code_addresses (a_pc : Addr) (code_la : list Addr)
    := (list_remove_elem a_pc code_la).
  Definition allow_einit_code_mask
    (a_pc : Addr) (v_pc : Version) (code_la : list Addr) (code_v : Version): coPset :=
    compute_mask_region (⊤ ∖ ↑logN.@(a_pc, v_pc)) (code_addresses a_pc code_la) code_v.

  Lemma allow_einit_code_mask_remove_nodup
    (a_pc : Addr) (v_pc : Version)
    (la_code : list Addr) (v_code : Version) :
    NoDup la_code ->
    allow_einit_code_mask a_pc v_pc (code_addresses a_pc la_code) v_code =
    allow_einit_code_mask a_pc v_pc la_code v_code.
  Proof.
    intros HNoDup.
    by rewrite /allow_einit_code_mask /code_addresses list_remove_elem_idem.
  Qed.


  Definition interp_list_pred
    (lws : list LWord) (Ps : list D) (has_later : bool) : iProp Σ :=
    ([∗ list] lw;Pw ∈ lws;Ps, (if has_later then ▷ (Pw : D) lw else (Pw : D) lw)).

  Definition interp_list_persistent
    (lws : list LWord) (Ps : list D) : iProp Σ :=
    ( ⌜ Persistent ([∗ list] lw;Pw ∈ lws;Ps, (Pw : D) lw) ⌝ ).

  Definition interp_list_readcond
    (lws : list LWord) (Ps : list D) (has_later : bool) : iProp Σ :=
    ( if has_later
      then [∗ list] Pa ∈ Ps, read_cond Pa interp
      else [∗ list] Pa ∈ Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw)
    )%I.

  Definition interp_list_close
    (la : list Addr) (Ps : list D) (v : Version) (E E' : coPset) : iProp Σ :=
    ( (▷ ([∗ list] a_Pa ∈ zip la Ps, (interp_ref_inv a_Pa.1 v a_Pa.2))) ={E', E }=∗ True).

  (* this will help us close the invariant again... *)
  (* it states which properties are enforced on all the lws *)
  Definition resources_open_invariant_code
    (a_pc : Addr) (v_pc : Version)
    (la_code : list Addr) (v_code : Version)
    (lws_code : list LWord) (Ps_code : list D)
    (has_later : bool)
    : iProp Σ :=

    let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E1 := allow_einit_code_mask a_pc v_pc la_code v_code in

    interp_list_pred lws_code Ps_code has_later
    ∗ interp_list_persistent lws_code Ps_code
    ∗ interp_list_readcond lws_code Ps_code has_later
    ∗ interp_list_close la_code Ps_code v_code E0 E1.

  Definition allows_einit_code (lregs : LReg) (r : RegName) :=
    ∀ p b e a v,
    lregs !! r = Some (LCap p b e a v)
    -> readAllowed p = true
    -> (finz.seq_between b e) ## reserved_addresses.

  Definition allows_einit_data (lmem : LMem) (b : Addr) (v : Version) :=
    ∀ p' b' e' a' v',
    lmem !! (b,v) = Some (LCap p' b' e' a' v')
    -> readAllowed p' = true
    -> (finz.seq_between b' e') ## reserved_addresses.

  Definition einit_code_mask_cond
    (lregs : LReg) (src : RegName)
    (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version)
    (a_pc : Addr) (v_pc : Version) :=
    decide (reg_allows_einit_code lregs src p_code b_code e_code a_code v_code
            /\ (src = PC \/ a_pc ∉ (finz.seq_between b_code e_code))).

  Definition allow_einit_code_resources
    (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version)
    (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D)
    :=

    let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in
    let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E1 := allow_einit_code_mask a_pc v_pc la_code v_code in

    (⌜read_reg_inr lregs src p_code b_code e_code a_code v_code⌝ ∗
     ⌜allows_einit_code lregs src⌝ ∗
     if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc
     then
      (|={E0, E1}=> (* we open this invariant with all the points-tos from b to e *)
         ∃ (lws_code :list LWord),
         ⌜ length lws_code = length la_code ⌝
         ∗ ([∗ map] la↦lw ∈ (logical_region_map la_code lws_code v_code), la ↦ₐ lw) (* here you get all the points-tos *)
         ∗ resources_open_invariant_code a_pc v_pc la_code v_code lws_code Ps_code true)%I
     else True)%I.


  Lemma create_einit_code_resources
    (lregs : LReg) (src : RegName)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version)
    (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) :

    let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in

    read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_code b_code e_code a_code v_code
    -> a_pc ∈ finz.seq_between b_pc e_pc
    → (∀ (r : RegName) lw, ⌜r ≠ PC⌝ → ⌜lregs !! r = Some lw⌝ → (fixpoint interp1) lw)
    -∗ interp (LCap p_pc b_pc e_pc a_pc v_pc)
    -∗ (∃ (Ps_code : list D),
           ⌜ length la_code = length Ps_code ⌝
           ∗ allow_einit_code_resources
               (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src
               a_pc v_pc
               p_code b_code e_code a_code v_code Ps_code).
  Proof.
    intros * Hread Hapc_inbounds.
    iIntros "#Hreg #Hinterp_pc".
    apply list_remove_elem_in in Hapc_inbounds.
    destruct Hapc_inbounds as (la' & <- & Hapc_inbounds).
    rewrite /allow_einit_code_resources /einit_code_mask_cond.
    case_decide as Hallows; cycle 1.
    { iExists (repeat (λne _, True%I) (length la_code)); iFrame "%".
      iSplit; first by rewrite repeat_length.
      iSplit; last done.
      iIntros (p b e a v Hlv HreadAllowed).
      destruct (decide (src = PC)) as [-> | Hneq_src_pc] ; simplify_map_eq.
      + iDestruct (readAllowed_not_reserved with "Hinterp_pc") as "%"; auto.
      + iAssert (interp (LCap p b e a v)) as "Hinterp_src".
        { iApply "Hreg"; eauto. }
        iDestruct (readAllowed_not_reserved with "Hinterp_src") as "%"; auto.
    }
    iFrame "%".
    cbn in Hapc_inbounds.
    apply bind_Some in Hapc_inbounds.
    destruct Hapc_inbounds as (? & Hrem & ?) ; simplify_eq.
    rewrite /reg_allows_einit_code in Hallows.
    destruct Hallows as ( (Hreg & HreadAllowed) & Hdecide).
    assert (la_code ⊆+ finz.seq_between b_code e_code)
      as Hla_subseteq by apply list_remove_elem_submsteq.
    assert (NoDup la_code) as Hla_NoDup by (by apply list_remove_elem_NoDup).
    rewrite /read_reg_inr in Hread; simplify_map_eq.

    destruct (decide (src = PC)) as [-> | Hneq_src_pc] ; simplify_map_eq.
    (* src = PC *)
    - rewrite /allow_einit_code_mask /code_addresses.
      rewrite list_remove_elem_idem; last done.
      iDestruct (interp_open_region $ (⊤ ∖ ↑logN.@(a_code, v_code)) with "Hinterp_pc")
        as (Ps) "[%Hlen_Ps Hmod]" ; eauto.
      { eapply Forall_forall. intros a' Ha'.
        subst la_code.
        eapply namespaces.coPset_subseteq_difference_r; auto.
        assert (a' ≠ a_code).
        {
          eapply list_remove_elem_neq; cycle 1 ; eauto.
          apply list_remove_Some in Hrem.
          setoid_rewrite Hrem; set_solver.
        }
        solve_ndisj.
      }
      iExists Ps.
      iSplit ; first by subst.
      iSplit.
      { iIntros (p b e a v Hsrc HreadAllowedp).
        iDestruct (readAllowed_not_reserved with "Hinterp_pc") as "%"; auto.
        by simplify_map_eq.
      }
      iMod "Hmod".
      iDestruct "Hmod" as (lws) "(%Hlws & %Hpers & Hmem & HPs & HPs' & Hclose)".
      iExists lws.
      iFrame; iFrame "%".
      iModIntro.
      iIntros "H".
      iDestruct ("Hclose" with "H") as "Hclose".
      rewrite /allow_einit_code_mask /code_addresses.
      rewrite list_remove_elem_notin.
      subst la_code.
      iFrame.
      apply not_elemof_list_remove_elem; done.

    (* src ≠ PC *)
    - destruct Hdecide as [Hcontra|Ha_notin_rem] ; first contradiction.
      iAssert (interp (LCap RX b_code e_code a_code v_code)) as "#Hinterp_code"
      ; first (iApply "Hreg"; eauto).
      iDestruct (interp_open_region $ (⊤ ∖ ↑logN.@(a_pc, v_pc)) with "Hinterp_code")
        as (Ps) "[%Hlen_Ps Hmod]" ; eauto.
      { apply Forall_forall; intros a' Ha'.
        subst la_code.
        assert (a' ≠ a_pc).
        { intro ; subst. by apply not_elemof_list_remove_elem in Ha'. }
        apply namespaces.coPset_subseteq_difference_r; [solve_ndisj|set_solver].
      }
      iExists Ps.
      iSplit ; first by subst.
      iSplit.
      { iIntros (p b e a v Hsrc HreadAllowedp).
        iDestruct (readAllowed_not_reserved with "Hinterp_code") as "%"; auto.
        by simplify_map_eq.
      }
      iMod "Hmod".
      rewrite allow_einit_code_mask_remove_nodup; auto.
      iDestruct "Hmod" as (lws) "(%Hlws & %Hpers & Hmem & HPs & HPs' & Hclose)".
      iExists lws.
      iFrame; iFrame "%".
      iModIntro.
      iIntros "H".
      iDestruct ("Hclose" with "H") as "Hclose".
      by rewrite allow_einit_code_mask_remove_nodup.
  Qed.

  Definition allow_einit_code_mem
    (lmem : LMem) (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D)
    (has_later : bool) :=

    let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in

    (⌜read_reg_inr lregs src p_code b_code e_code a_code v_code⌝ ∗
     if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc
     then (∃ (lws_code : list LWord),
              ⌜length lws_code = length la_code⌝
              ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> (logical_region_map la_code lws_code v_code)⌝
              ∗ resources_open_invariant_code a_pc v_pc la_code v_code lws_code Ps_code has_later)%I
     else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I.

  Lemma einit_code_resources_implies_mem_map
    (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D)
    :

    let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in
    let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E1 := allow_einit_code_mask a_pc v_pc la_code v_code in

    allow_einit_code_resources lregs src a_pc v_pc p_code b_code e_code a_code v_code Ps_code
    -∗ (a_pc, v_pc) ↦ₐ lw_pc
    ={ E0,
         if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc
         then E1
         else E0
      }=∗
    ∃ lmem : LMem,
      allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code true
      ∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw).
  Proof.
    intros *.
    iIntros "HSweepRes Ha_pc".
    iDestruct "HSweepRes" as "(%Hread & [ %Hreserved HSweepRes ] )".
    subst E1.
    rewrite /einit_code_mask_cond.
    case_decide as Hallows; cycle 1.
      - iExists _.
        iSplitR "Ha_pc".
        + iFrame "%".
          rewrite /einit_code_mask_cond; case_decide; first by exfalso. auto.
        + iModIntro. by iApply memMap_resource_1.
      - iMod "HSweepRes" as (lws) "(%Hlws & Hmem & HSweepRest)".
        iExists _.
        iSplitL "HSweepRest".
        * iFrame "%".
          rewrite decide_True; auto.
        * iModIntro.
          destruct Hallows as ((Hrinr & Hra) & Hne).
          iDestruct (big_sepM_insert with "[$Hmem $Ha_pc]") as "Hmem" ; cycle 1 ; auto.
          rewrite /logical_region_map.
          apply not_elem_of_list_to_map_1.
          rewrite fst_zip.
          2: { rewrite Hlws /logical_region fmap_length; lia. }
          rewrite /logical_region.
          intro Hcontra. clear -Hcontra.
          eapply elem_of_list_fmap_2 in Hcontra.
          destruct Hcontra as (a & Heq & Hcontra) ; simplify_eq.
          apply not_elemof_list_remove_elem in Hcontra; auto.
  Qed.


  Lemma mem_map_implies_pure_conds
    (lmem : LMem) (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version)
    (Ps_code : list D) (has_later : bool) :
    allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code has_later
    -∗ ⌜lmem !! (a_pc, v_pc) = Some lw_pc⌝.
  Proof.
    iIntros "(% & HSweepRes)".
    rewrite /einit_code_mask_cond.
    case_decide as Hallows.
    - pose (Hallows' := Hallows).
      destruct Hallows' as ((Hreg & Hread) & Hdecide).
      iDestruct "HSweepRes" as (lws) "(%Hlen & -> & HSweepRest)".
      by simplify_map_eq.
    - iDestruct "HSweepRes" as "->".
      by simplify_map_eq.
  Qed.

  Lemma allow_einit_code_mem_later
    (lmem : LMem) (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version)
    (Ps_code : list D) :
    allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code true
    -∗ ▷ allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code false.
  Proof.
    iIntros "[% HSweepMem]".
    rewrite !/allow_einit_code_mem /= /einit_code_mask_cond. iSplit;[auto|].
    case_decide; last (iNext;iFrame).
    iApply bi.later_exist_2. iDestruct "HSweepMem" as (lws) "(%&%&HSweepRest)".
      iExists lws.
      iDestruct "HSweepRest" as "(?&?&?&?)"; iFrame "%∗"; iNext ; iFrame.
  Qed.


    (* iAssert ( ⌜ *)
    (*             if ( einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src a_pc v_pc ) *)
    (*             then (∃ dcap, lmem !! (b_src, v_src) = Some dcap) *)
    (*             else True ⌝ )%I as "%Hdcap". *)
    (* { *)
    (*   rewrite /allow_einit_code_mem. *)
    (*   iDestruct "HEinitCodeMem" as "(_ & HEinitCodeMem)". *)
    (*   match goal with *)
    (*   | _ : _ |- context [ einit_code_mask_cond ?regs ?r ?p ?b ?e ?a ?v ?apc ?vpc] => *)
    (*       set (Hmask := einit_code_mask_cond regs r p b e a v apc vpc) *)
    (*   end. *)
    (*   destruct Hmask as [Hmask|] *)
    (*   ; rewrite /einit_code_mask_cond *)
    (*   ; [ iEval (rewrite decide_True //) | iEval (rewrite decide_False //)] *)
    (*   ; last done. *)
    (*   iDestruct "HEinitCodeMem" as (lws_code) "(%Hlength_lws_code & %Hlmem & _)"; subst. *)
    (*   iPureIntro. *)
    (*   destruct Hmask as [Hreg_allow Hcond]. *)
    (*   destruct Hcond as [-> | Hapc]. *)
    (*   - rewrite /reg_allows_einit_code in Hreg_allow; simplify_map_eq. *)
    (*     destruct Hreg_allow as [? ->]; simplify_eq. *)
    (*     destruct (decide ( b_src = a_src )) as [-> | Hbsrc]. *)
    (*     + by exists lw_pc; simplify_map_eq. *)
    (*     + destruct lws_code. *)
    (*       ++ exfalso. *)
    (*          cbn in *. *)
    (*          symmetry in Hlength_lws_code. *)
    (*          apply length_zero_iff_nil in Hlength_lws_code. *)
    (*          rewrite /code_addresses in Hlength_lws_code. *)
    (*          assert (b_src ∈  list_remove_elem a_src (finz.seq_between b_src e_src)) as Hcontra. *)
    (*          { admit. } *)
    (*          rewrite Hlength_lws_code in Hcontra. *)
    (*          set_solver. *)
    (*       ++ exists l. *)
    (*          rewrite lookup_insert_ne. *)
    (*          2:{ intro ; simplify_eq. } *)
    (*          rewrite /logical_region_map. *)
    (*          apply elem_of_list_to_map_1. *)
    (*          admit. *)
    (*          admit. *)
    (*   - destruct lws_code. *)
    (*     ++ exfalso. *)
    (*        cbn in *. *)
    (*        symmetry in Hlength_lws_code. *)
    (*        apply length_zero_iff_nil in Hlength_lws_code. *)
    (*        rewrite /code_addresses in Hlength_lws_code. *)
    (*        rewrite list_remove_elem_notin in Hlength_lws_code; auto. *)

    (*        assert (b_src ∈  list_remove_elem a_src (finz.seq_between b_src e_src)) as Hcontra. *)
    (*          { admit. } *)
    (*          rewrite Hlength_lws_code in Hcontra. *)
    (*          set_solver. *)
    (*       ++ exists l. *)
    (*          rewrite lookup_insert_ne. *)
    (*          2:{ intro ; simplify_eq. } *)
    (*          rewrite /logical_region_map. *)
    (*          apply elem_of_list_to_map_1. *)
    (*          admit. *)
    (*          admit. *)

    (*       by exists lw_pc; simplify_map_eq. *)




    (*   admit. *)
    (*   + rewrite /einit_code_mask_cond. *)
    (*   set ( Hmask := (einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src a_pc v_pc) ). *)
    (*   destruct *)
    (*     (einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src *)
    (*        a_src v_src a_pc v_pc) *)
    (*       as [Hmask|Hmask]. *)


    (* } *)


  Lemma einit_case (lregs : leibnizO LReg)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version)
    (lw_pc : LWord) (src : RegName) (P : D):
    ftlr_instr lregs p_pc b_pc e_pc a_pc v_pc lw_pc (EInit src) P.
  Proof.
    intros Hp Hsome HcorrectLPC Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #(Hread & Hwrite & %HpersP) Hown Ha #HP Hcls HPC Hmap".
    specialize (HpersP lw_pc).
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)) as [Hx|Hx].
      rewrite Hx lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p_src b_src e_src a_src v_src, read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src)
      as (p_src & b_src & e_src & a_src & v_src & HV_Src).
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsome_src].
      unfold read_reg_inr. rewrite Hsome_src.
      destruct wsrc as [|[ p_src b_src e_src a_src v_src|] | ]; try done.
      by repeat eexists.
    }

    (* Step 1: prepare all resources necessary to open the invariants of the argument (the cap given in is_unique), if necessary,
       and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_einit_code_resources with "[$Hreg] [$Hinv]") as (Ps_code) "[%Hlen_Ps HEinitCodeRes]"
    ; [ eassumption
      | by apply elem_of_finz_seq_between
      |].

    (* Open the invariants! *)
    (* Step 2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iMod (einit_code_resources_implies_mem_map with "HEinitCodeRes Ha") as (lmem) "[HEinitCodeMem HMemCodeRes]".
    (* rename the big masks to easy names *)
    set (E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc)).
    set (E1 := allow_einit_code_mask a_pc v_pc (code_addresses a_pc (finz.seq_between b_src e_src)) v_src).

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HEinitCodeMem") as %HReadPC.

    (* Step 4: move the later outside, so that we can remove it after applying wp_isunique *)
    (* iDestruct (allow_einit_code_mem_later with "HSweepMem") as "HSweepMem"; auto. *)

    iAssert ( ⌜ allows_einit_code (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src ⌝)%I as "%Hallows_einit_code".
    { iDestruct "HEinitCodeRes" as "(_&%HeinitCodeRes&_)".
      iPureIntro. apply HeinitCodeRes.
    }

    (* iAssert ( ⌜ *)
    (*             if ( einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src a_pc v_pc ) *)
    (*             then (∃ dcap, lmem !! (b_src, v_src) = Some dcap) *)
    (*             else True ⌝ )%I as "%Hdcap". *)
    (* { admit. } *)


    Set Nested Proofs Allowed.
    Fixpoint list_remove_elem_list `{A : Type} `{EqDecision A} (la' la : list A) : list A :=
      match la' with
      | [] => la
      | h::t => list_remove_elem h (list_remove_elem_list t la)
      end.

    Definition data_addresses (a_pc : Addr) (la_code la_data : list Addr)
      := (list_remove_elem_list (a_pc::la_code) la_data).

    Definition allow_einit_data_mask
      (a_pc : Addr) (v_pc : Version)
      (la_code : list Addr) (v_code : Version)
      (la_data : list Addr) (v_data : Version)
      : coPset :=
      let mask_code := allow_einit_code_mask a_pc v_pc la_code v_code in
      compute_mask_region mask_code (data_addresses a_pc la_code la_data) v_data.

  Definition read_lmem_inr (lmem : LMem) (a : Addr) (v : Version) p' b' e' a' v' :=
    match lmem !! (a,v) with
      | Some (LCap p'' b'' e'' a'' v'') => (LCap p'' b'' e'' a'' v'') = LCap p' b' e' a' v'
      | Some _ => True
      | None => False end.

  Definition mem_allows_einit_data
    (lmem : LMem) (a : Addr) (v : Version)
    (p' : Perm) (b' e' a' : Addr) (v' : Version):=
    lmem !! (a,v) = Some (LCap p' b' e' a' v') ∧ p' = RW.

  Definition einit_data_mask_cond
    (lmem : LMem) (b_code : Addr) (v_code : Version)
    (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version)
    (a_pc : Addr) (v_pc : Version) :=
    decide (
        mem_allows_einit_data lmem b_code v_code p_data b_data e_data a_data v_data
        ∧ a_pc ∉ (finz.seq_between b_data e_data)
      ).

  Definition interp_list_pred_data
    (lws : list LWord) (Ps : list D) (has_later : bool) : iProp Σ :=
    ([∗ list] lw;Pw ∈ lws;Ps, (if has_later then ▷▷ (Pw : D) lw else (Pw : D) lw)).

  Definition interp_list_persistent_data
    (lws : list LWord) (Ps : list D) : iProp Σ :=
    ( ⌜ Persistent ([∗ list] lw;Pw ∈ lws;Ps, (Pw : D) lw) ⌝ ).

  Definition interp_list_readcond_data
    (lws : list LWord) (Ps : list D) (has_later : bool) : iProp Σ :=
    ( if has_later
      then [∗ list] Pa ∈ Ps, ▷ read_cond Pa interp
      else [∗ list] Pa ∈ Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw)
    )%I.

  Definition interp_list_close_data
    (la : list Addr) (Ps : list D) (v : Version) (E E' : coPset) : iProp Σ :=
    ( ▷ (▷ ([∗ list] a_Pa ∈ zip la Ps, (interp_ref_inv a_Pa.1 v a_Pa.2))) ={E', E }=∗ True).

  Definition resources_open_invariant_data
    (a_pc : Addr) (v_pc : Version)
    (la_code : list Addr) (v_code : Version)
    (la_data : list Addr) (v_data : Version) (lws_data : list LWord) (Ps_data : list D)
    (has_later : bool)
    : iProp Σ :=

    (* let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
    let E1 := allow_einit_code_mask a_pc v_pc la_code v_code : coPset in
    let E2 := allow_einit_data_mask a_pc v_pc la_code v_code la_data v_data : coPset in

    interp_list_pred_data lws_data Ps_data has_later
    ∗ interp_list_persistent_data lws_data Ps_data
    ∗ interp_list_readcond_data lws_data Ps_data has_later
    ∗ interp_list_close_data la_data Ps_data v_data E1 E2.


  (* Definition allow_einit_data_resources *)
  (*   (* (lregs : LReg) *) *)
  (*   (lmem : LMem) *)
  (*   (* (src : RegName) *) *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) *)
  (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) (Ps_data : list D) *)
  (*   := *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let la_data  := data_addresses a_pc la_code (finz.seq_between b_data e_data) in *)
  (*   let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_code_mask a_pc v_pc la_code v_code : coPset in *)
  (*   let E1' := *)
  (*     (if einit_code_mask_cond (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src *)
  (*           a_src v_src a_pc v_pc then E1 else E0) *)
  (*   in *)
  (*   let E2 := allow_einit_data_mask a_pc v_pc la_code v_code la_data v_data : coPset in *)

  (*   ( *)
  (*     (* ⌜read_reg_inr lregs src p_code b_code e_code a_code v_code⌝ ∗ *) *)
  (*     ⌜read_lmem_inr lmem b_code v_code p_data b_data e_data a_data v_data⌝ ∗ *)
  (*     (* ⌜allows_einit_code lregs src⌝ ∗ *) *)
  (*     ⌜allows_einit_data lmem b_code v_code ⌝ ∗ *)
  (*    if einit_data_mask_cond lmem b_code v_code p_data b_data e_data a_data v_data a_pc v_pc *)
  (*    then *)
  (*     (|={E1, E2}=> (* we open this invariant with all the points-tos from b to e *) *)
  (*        ∃ (lws_data :list LWord), *)
  (*        ⌜ length lws_data = length la_data ⌝ *)
  (*        ∗ ([∗ map] la↦lw ∈ (logical_region_map la_data lws_data v_data), la ↦ₐ lw) (* here you get all the points-tos *) *)
  (*        ∗ resources_open_invariant_data a_pc v_pc la_code v_code la_data v_data lws_data Ps_data true)%I *)
  (*    else True)%I. *)


    (* Lemma create_einit_data_resources *)
    (*   (lregs : LReg) (lmem : LMem) (src : RegName) *)
    (*   (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
    (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) *)
    (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) : *)

    (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
    (*   let la_data  := data_addresses a_pc la_code (finz.seq_between b_data e_data) in *)
    (*   read_lmem_inr lmem b_code v_code p_data b_data e_data a_data v_data → *)

    (*   (allow_einit_code_resources *)
    (*      (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src a_pc v_pc *)
    (*      p_code b_code e_code a_code v_code Ps_code) -∗ *)
    (*   (allow_einit_code_mem *)
    (*     lmem (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src a_pc v_pc *)
    (*     lw_pc p_code b_code e_code a_code v_code Ps_code true) -∗ *)
    (*   ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw) -∗ *)

    (* (∃ (Ps_data : list D), *)
    (*        ⌜ length la_data = length Ps_data ⌝ *)
    (*        (* old resources *) *)
    (*        ∗ (allow_einit_code_resources *)
    (*             (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src a_pc v_pc *)
    (*             p_code b_code e_code a_code v_code Ps_code) *)
    (*        ∗ (allow_einit_code_mem *)
    (*             lmem (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src a_pc v_pc *)
    (*             lw_pc p_code b_code e_code a_code v_code Ps_code true) *)
    (*        ∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw) *)
    (*        (* new resources *) *)
    (*        ∗ allow_einit_data_resources *)
    (*            (* (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) *) *)
    (*            lmem *)
    (*            (* src *) *)
    (*            a_pc v_pc *)
    (*            p_code b_code e_code a_code v_code Ps_code *)
    (*            p_data b_data e_data a_data v_data Ps_data *)
    (* ). *)
    (* Admitted. *)

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p_data b_data e_data a_data v_data,
               read_lmem_inr lmem b_src v_src  p_data b_data e_data a_data v_data)
      as (p_data & b_data & e_data & a_data & v_data & HV_data).
    { admit. }

    (* iDestruct (create_einit_data_resources with "[$HEinitCodeRes] [$HEinitCodeMem] [$HMemCodeRes]") *)
    (*   as (Ps_data) "(%Hlen_Ps_data & _ & HEinitCodeMem & Hmem & HEinitDataRes)"; first eassumption. *)


  (* Definition allow_einit_data_mem *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) (lws_code : list LWord) *)
  (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) (Ps_data : list D) *)
  (*   (has_later : bool) := *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let la_data  := data_addresses a_pc la_code (finz.seq_between b_data e_data) in *)

  (*   ( *)
  (*     ⌜read_reg_inr lregs src p_code b_code e_code a_code v_code⌝ ∗ *)
  (*     ⌜read_lmem_inr lmem b_code v_code p_data b_data e_data a_data v_data⌝ ∗ *)
  (*     if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
  (*     then *)
  (*       (if einit_data_mask_cond lmem b_code v_code p_data b_data e_data a_data v_data a_pc v_pc *)
  (*        then *)
  (*          (∃ (lws_data : list LWord), *)
  (*              ⌜length lws_data = length la_data⌝ *)
  (*              ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> *)
  (*                          (logical_region_map la_code lws_code v_code *)
  (*                             ∪ logical_region_map la_data lws_data v_data)⌝ *)
  (*              ∗ resources_open_invariant_data a_pc v_pc la_code v_code la_data v_data lws_data Ps_data has_later)%I *)
  (*        else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> (logical_region_map la_code lws_code v_code)⌝ *)
  (*       ) *)
  (*       ∗ resources_open_invariant_code a_pc v_pc la_code v_code lws_code Ps_code has_later *)
  (*     else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I. *)

    (* ( *)
    (*  if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
    (*  then (∃ (lws_code : list LWord), *)
    (*           ⌜length lws_code = length la_code⌝ *)
    (*           ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> (logical_region_map la_code lws_code v_code)⌝ *)
    (*           ∗ resources_open_invariant_code a_pc v_pc la_code v_code lws_code Ps_code has_later)%I *)
    (*  else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I. *)

  (* Lemma einit_data_resources_implies_mem_map *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)
  (*   (p_code : Perm) (b_code e_code a_code : Addr) (v_code : Version) (Ps_code : list D) (lws_code : list LWord) *)
  (*   (p_data : Perm) (b_data e_data a_data : Addr) (v_data : Version) (Ps_data : list D) : *)

  (*   let la_code  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let la_data  := data_addresses a_pc la_code (finz.seq_between b_data e_data) in *)
  (*   (* let E0 := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *) *)
  (*   let E1 := allow_einit_code_mask a_pc v_pc la_code v_code : coPset in *)
  (*   let E2 := allow_einit_data_mask a_pc v_pc la_code v_code la_data v_data : coPset in *)

  (*   allow_einit_code_resources lregs src a_pc v_pc p_code b_code e_code a_code v_code Ps_code *)
  (*   allow_einit_data_resources lregs src a_pc v_pc p_code b_code e_code a_code v_code Ps_code *)
  (*   -∗ (a_pc, v_pc) ↦ₐ lw_pc *)
  (*   ={ E0, *)
  (*        if einit_code_mask_cond lregs src p_code b_code e_code a_code v_code a_pc v_pc *)
  (*        then E1 *)
  (*        else E0 *)
  (*     }=∗ *)
  (*   ∃ lmem : LMem, *)
  (*     allow_einit_code_mem lmem lregs src a_pc v_pc lw_pc p_code b_code e_code a_code v_code Ps_code true *)
  (*     ∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw). *)




  (* "HMemCodeRes" : [∗ map] la↦lw ∈ lmem, la ↦ₐ lw *)


  (*   iAssert ( ⌜ allows_einit_data lmem  ⌝)%I as "%Hallows_einit_code". *)
  (*   { iDestruct "HEinitCodeRes" as "(_&%HeinitCodeRes&_)". *)
  (*     iPureIntro. apply HeinitCodeRes. *)
  (*   } *)

  (*   iApply (wp_einit with "[$Hmap $HMemCodeRes]") *)
  (*   ; eauto *)
  (*   ; [ by simplify_map_eq *)
  (*     | rewrite /subseteq /map_subseteq /set_subseteq_instance *)
  (*       ; intros rr _; apply elem_of_dom *)
  (*       ; rewrite lookup_insert_is_Some'; *)
  (*       eauto *)
  (*     | | | ]. *)

  Admitted.






  (* (** Predicate that defines when the contents of a register can be swept; *)
  (*     i.e. when the register contains a capability with at least R permissions... *) *)
  (* Definition reg_allows_einit *)
  (*   (lregs : LReg) (lmem : LMem) (r : RegName) *)
  (*   (b e a : Addr) (v : Version) *)
  (*   (b' e' a' : Addr) (v' : Version):= *)
  (*   lregs !! r = Some (LCap RX b e a v) *)
  (*   ∧ lmem !! (a,v) = Some (LCap RW b' e' a' v'). *)

  (* (* TODO move stdpp_extra *) *)
  (* Fixpoint list_remove_elem_list `{A : Type} `{EqDecision A} (la' la : list A) : list A := *)
  (*   match la' with *)
  (*   | [] => la *)
  (*   | h::t => list_remove_elem h (list_remove_elem_list t la) *)
  (*   end. *)

  (* Definition code_addresses (a_pc : Addr) (code_la : list Addr) *)
  (*   := (list_remove_elem a_pc code_la). *)

  (* Definition allow_einit_mask_code *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (code_la : list Addr) (code_v : Version) *)
  (*   : coPset := *)
  (*   let pc_mask := (⊤ ∖ ↑logN.@(a_pc, v_pc)) in *)
  (*   compute_mask_region pc_mask (code_addresses a_pc code_la) code_v. *)

  (* Definition data_addresses (a_pc : Addr) (code_la data_la : list Addr) *)
  (*   := (list_remove_elem_list (a_pc::code_la) data_la). *)

  (* Definition allow_einit_mask_data *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (code_la : list Addr) (code_v : Version) *)
  (*   (data_la : list Addr) (data_v : Version) *)
  (*   : coPset := *)
  (*   let code_mask := allow_einit_mask_code a_pc v_pc code_la code_v in *)
  (*   compute_mask_region code_mask (data_addresses a_pc code_la data_la) data_v. *)

  (* (* Lemma allow_einit_mask_remove_nodup *) *)
  (* (*   (a_pc : Addr) (v_pc : Version) (code_la data_la : list Addr) (v : Version) : *) *)
  (* (*   NoDup code_la -> *) *)
  (* (*   NoDup data_la -> *) *)
  (* (*   allow_sweep_mask a_pc v_pc (list_remove_elem a_pc la) v = *) *)
  (* (*   allow_sweep_mask a_pc v_pc la v. *) *)
  (* (* Proof. *) *)
  (* (*   intros HNoDup. *) *)
  (* (*   by rewrite /allow_sweep_mask list_remove_elem_idem. *) *)
  (* (* Qed. *) *)

  (* (* this will help us close the invariant again... *) *)
  (* (* it states which properties are enforced on all the lws *) *)


  (* Definition region_open_resources *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (code_la : list Addr) (code_v : Version) *)
  (*   (code_lws : list LWord) (code_Ps : list D) *)
  (*   (data_la : list Addr) (data_v : Version) *)
  (*   (data_lws : list LWord) (data_Ps : list D) *)
  (*   (has_later : bool) *)
  (*   : iProp Σ := *)

  (*   let E := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_mask_code a_pc v_pc code_la code_v in *)
  (*   let E2 := allow_einit_mask_data a_pc v_pc code_la code_v data_la data_v in *)

  (*   ([∗ list] lw;Pw ∈ code_lws;code_Ps, (if has_later then ▷ (Pw : D) lw else (Pw : D) lw)) *)
  (*   ∗ ([∗ list] lw;Pw ∈ data_lws;data_Ps, (if has_later then ▷▷ (Pw : D) lw else (Pw : D) lw)) *)

  (*   ∗ ( ⌜ Persistent ([∗ list] lw;Pw ∈ code_lws;code_Ps, (Pw : D) lw) ⌝ ) (* All properties P are persistent *) *)
  (*   ∗ ( ⌜ Persistent ([∗ list] lw;Pw ∈ data_lws;data_Ps, (Pw : D) lw) ⌝ ) (* All properties P are persistent *) *)

  (*   ∗ ( if has_later *)
  (*       then ([∗ list] Pa ∈ code_Ps, read_cond Pa interp) *)
  (*            ∗ ([∗ list] Pa ∈ data_Ps, ▷ read_cond Pa interp) *)
  (*              (* the read cond holds *) *)
  (*       else ([∗ list] Pa ∈ code_Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw)) *)
  (*              ∗ ([∗ list] Pa ∈ data_Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw)) *)
  (*     )%I *)

  (*   ∗ (▷▷ ([∗ list] a_Pa ∈ zip data_la code_Ps, (interp_ref_inv a_Pa.1 data_v a_Pa.2)) ={E2, E1 }=∗ True) *)
  (*   ∗ (▷ ([∗ list] a_Pa ∈ zip code_la data_Ps, (interp_ref_inv a_Pa.1 code_v a_Pa.2)) ={E1, E }=∗ True). *)

  (* Definition einit_mask_cond *)
  (*   (lregs : LReg) (lmem : LMem) *)
  (*   (src : RegName) (b_code e_code a_code : Addr) (v_code : Version) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) *)
  (*   (a_pc : Addr) (v_pc : Version) := *)
  (*   decide (reg_allows_einit lregs lmem src b_code e_code a_code v_code b_data e_data a_data v_data *)
  (*           /\ (src = PC \/ a_pc ∉ (finz.seq_between b_code e_code)) *)
  (*           /\ a_pc ∉ (finz.seq_between b_data e_data) *)
  (*     ). *)

  (* (* Description of what the resources are supposed to look like after opening the region *) *)
  (* (*    if we need to, but before closing the region up again*) *)

  (* Definition allow_einit_res *)
  (*   (lregs : LReg) (lmem : LMem) *)
  (*   (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) *)
  (*   (b_code e_code a_code : Addr) (v_code : Version) (code_Ps : list D) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) (data_Ps : list D) *)
  (*   := *)

  (*   let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in *)
  (*   let E   := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_mask_code a_pc v_pc code_la v_code in *)
  (*   let E2 := allow_einit_mask_data a_pc v_pc code_la v_code data_la v_data in *)

  (*   (⌜read_reg_inr lregs src RX b_code e_code a_code v_code⌝ ∗ *)
  (*    ⌜allows_einit lregs lmem src⌝ ∗ *)
  (*    if einit_mask_cond lregs lmem *)
  (*         src b_code e_code a_code v_code *)
  (*         b_data e_data a_data v_data *)
  (*         a_pc v_pc *)
  (*    then *)
  (*     (|={E, E2}=> (* we open this invariant with all the points-tos from b to e *) *)
  (*        ∃ (code_lws : list LWord) (data_lws : list LWord), *)
  (*        ⌜ length code_lws = length code_la ⌝ *)
  (*        ∗ ⌜ length data_lws = length data_la ⌝ *)
  (*        ∗ ([∗ map] la↦lw ∈ (logical_region_map code_la code_lws v_code), la ↦ₐ lw) (* here you get all the points-tos *) *)
  (*        ∗ ([∗ map] la↦lw ∈ (logical_region_map data_la data_lws v_data), la ↦ₐ lw) *)
  (*        ∗ region_open_resources a_pc v_pc *)
  (*            code_la v_code code_lws code_Ps *)
  (*            data_la v_data data_lws data_Ps *)
  (*            true)%I *)
  (*    else True)%I. *)

  (* (* this does not yet open the invariant *) *)
  (* Lemma create_einit_res *)
  (*   (lregs : LReg) (lmem : LMem) *)
  (*   (src : RegName) *)
  (*   (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version) *)
  (*   (b_code e_code a_code : Addr) (v_code : Version) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) : *)

  (*   let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in *)

  (*   read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src RX b_code e_code a_code v_code *)
  (*   -> a_pc ∈ finz.seq_between b_pc e_pc *)
  (*   → (∀ (r : RegName) lw, ⌜r ≠ PC⌝ → ⌜lregs !! r = Some lw⌝ → (fixpoint interp1) lw) *)
  (*   -∗ interp (LCap p_pc b_pc e_pc a_pc v_pc) *)
  (*   -∗ (∃ (code_Ps : list D) (data_Ps  : list D), *)
  (*          ⌜ length code_la = length code_Ps ⌝ *)
  (*          ∗ ⌜length data_la = length data_Ps ⌝ *)
  (*          ∗ allow_einit_res *)
  (*              (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) lmem src *)
  (*              a_pc v_pc *)
  (*              b_code e_code a_code v_code code_Ps *)
  (*              b_data e_data a_data v_data data_Ps *)
  (*      ). *)
  (* Proof. *)
  (* Admitted. *)

  (* Definition allow_einit_mem *)
  (*   (lmem : LMem) (lregs : LReg) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)

  (*   (b_code e_code a_code : Addr) (v_code : Version) (code_Ps : list D) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) (data_Ps : list D) *)

  (*   (has_later : bool) := *)

  (*   let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in *)

  (*   (⌜read_reg_inr lregs src RX b_code e_code a_code v_code⌝ ∗ *)
  (*    if einit_mask_cond lregs lmem *)
  (*         src b_code e_code a_code v_code *)
  (*         b_data e_data a_data v_data *)
  (*         a_pc v_pc *)
  (*    then (∃ (code_lws : list LWord) (data_lws : list LWord), *)
  (*          ⌜ length code_la = length code_lws ⌝ *)
  (*          ∗ ⌜length data_la = length data_lws ⌝ *)
  (*          ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> *)
  (*                      (logical_region_map code_la code_lws v_code *)
  (*                         ∪ logical_region_map data_la data_lws v_data)⌝ *)
  (*             ∗ region_open_resources a_pc v_pc *)
  (*                 code_la v_code code_lws code_Ps *)
  (*                 data_la v_data data_lws data_Ps *)
  (*                 has_later) *)
  (*    else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I. *)

  (* (* Create the lmem with the points-tos we need for the is_unique case *) *)
  (* Lemma einit_res_implies_mem_map *)
  (*   (lregs : LReg) (lmem : LMem) (src : RegName) *)
  (*   (a_pc : Addr) (v_pc : Version) (lw_pc : LWord) *)

  (*   (b_code e_code a_code : Addr) (v_code : Version) (code_Ps : list D) *)
  (*   (b_data e_data a_data : Addr) (v_data : Version) (data_Ps : list D) : *)

  (*   let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in *)
  (*   let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in *)

  (*   let E   := ⊤ ∖ ↑logN.@(a_pc, v_pc) in *)
  (*   let E1 := allow_einit_mask_code a_pc v_pc code_la v_code in *)
  (*   let E2 := allow_einit_mask_data a_pc v_pc code_la v_code data_la v_data in *)

  (*   allow_einit_res lregs src a_pc v_pc lw_pc *)
  (*     b_code e_code a_code v_code code_Ps *)
  (*     b_data e_data a_data v_data data_Ps *)
  (*   -∗ (a_pc, v_pc) ↦ₐ lw_pc *)
  (*   ={ E, *)
  (*        if einit_mask_cond lregs *)
  (*         src b_code e_code a_code v_code *)
  (*         b_data e_data a_data v_data *)
  (*         a_pc v_pc *)
  (*        then E2 *)
  (*        else E *)
  (*     }=∗ *)
  (*   ∃ lmem : LMem, *)
  (*     allow_einit_mem lmem lregs src a_pc v_pc lw_pc *)
  (*                     b_code e_code a_code v_code code_Ps *)
  (*                     b_data e_data a_data v_data data_Ps *)
  (*                     true *)
  (*     ∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw). *)
  (* Proof. *)
  (*   intros *. *)
  (*   iIntros "HSweepRes Ha_pc". *)
  (*   iDestruct "HSweepRes" as "(%Hread & [ %Hreserved HSweepRes ] )". *)
  (*   subst E'. *)
  (*   rewrite /sweep_mask_cond. *)
  (*   case_decide as Hallows; cycle 1. *)
  (*     - iExists _. *)
  (*       iSplitR "Ha_pc". *)
  (*       + iFrame "%". *)
  (*         rewrite /sweep_mask_cond; case_decide; first by exfalso. auto. *)
  (*       + iModIntro; iNext. by iApply memMap_resource_1. *)
  (*     - iMod "HSweepRes" as (lws) "(%Hlws & Hmem & HSweepRest)". *)
  (*       iExists _. *)
  (*       iSplitL "HSweepRest". *)
  (*       * iFrame "%". *)
  (*         rewrite decide_True; auto. *)
  (*       * iModIntro;iNext. *)
  (*         destruct Hallows as ((Hrinr & Hra) & Hne). *)
  (*         iDestruct (big_sepM_insert with "[$Hmem $Ha_pc]") as "Hmem" ; cycle 1 ; auto. *)
  (*         rewrite /logical_region_map. *)
  (*         apply not_elem_of_list_to_map_1. *)
  (*         rewrite fst_zip. *)
  (*         2: { rewrite Hlws /logical_region fmap_length; lia. } *)
  (*         rewrite /logical_region. *)
  (*         intro Hcontra. clear -Hcontra. *)
  (*         eapply elem_of_list_fmap_2 in Hcontra. *)
  (*         destruct Hcontra as (a & Heq & Hcontra) ; simplify_eq. *)
  (*         apply not_elemof_list_remove_elem in Hcontra; auto. *)
  (* Qed. *)



End fundamental.
