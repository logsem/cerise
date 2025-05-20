From cap_machine.ftlr Require Export Jmp Jnz Mov Load Store AddSubLt Restrict
  Subseg Get Lea Seal UnSeal IsUnique Hash EInit EDeInit EStoreId.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
(* From cap_machine.rules Require Import rules_EInit rules_EDeInit rules_EStoreId rules_IsUnique. (* temporarily *) *)

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}
          {contract_enclaves : @CustomEnclavesMap Σ MP}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma extract_r_ex lregs (r : RegName) :
    (∃ lw, lregs !! r = Some lw) →
    ⊢ (([∗ map] reg↦lw ∈ lregs, reg ↦ᵣ lw) → ∃ lw, r ↦ᵣ lw)%I.
  Proof.
    intros [lw Hw].
    iIntros "Hmap". iExists lw.
    iApply (big_sepM_lookup (λ reg' i, reg' ↦ᵣ i)%I lregs r lw); eauto.
  Qed.

  Lemma extract_r lregs (r : RegName) lw :
    lregs !! r = Some lw →
    ⊢ (([∗ map] reg↦lw ∈ lregs, reg ↦ᵣ lw) →
     (r ↦ᵣ lw ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> lregs, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap".
    iDestruct (big_sepM_lookup_acc (λ (r : RegName) i, r ↦ᵣ i)%I lregs r lw) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ (r : RegName) i, r ↦ᵣ i)%I lregs r lw) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto.
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Lemma fundamental_cap
    lregs p b e a v (Hcontract: custom_enclave_contract_gen) :
    custom_enclave_inv
    ⊢ interp (LCap p b e a v) → (* PC safe to share *)
      interp_expression lregs (LCap p b e a v). (* PC safe to execute *)
  Proof.
    iIntros "#Hsystem_inv #Hinv /=".
    iIntros "[[Hfull Hreg] [Hmreg Hown]]".
    iRevert "Hinv".
    iLöb as "IH" forall (lregs p b e a v).
    iIntros "#Hinv".
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectLPC (LCap p b e a v))).
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
      { eapply in_range_is_correctLPC; eauto. solve_addr. }
      assert (p = RX ∨ p = RWX) as Hp.
      { inversion i. inversion H1; cbn in *; simplify_eq. auto. }
      iDestruct (read_allowed_inv_regs with "[] Hinv") as (P) "(#Hinva & #Hread)";[eauto|destruct Hp as [-> | ->];auto|iFrame "% #"|].
      rewrite /interp_ref_inv /=.
      iInv (logN.@(a, v)) as (lw) "[>Ha HP]" "Hcls".
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
        first apply (lookup_insert _ _ (LCap p b e a v)).

      destruct (decodeInstrWL lw) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (jmp_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Jnz *)
        iApply (jnz_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Mov *)
        iApply (mov_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Load *)
        iApply (load_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Store *)
        iApply (store_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Lt *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Add *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Sub *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Mod *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* HashConcat*)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Hash *)
        iApply (hash_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Lea *)
        iApply (lea_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Restrict *)
        iApply (restrict_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Subseg *)
        iApply (subseg_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetB *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetB _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetE *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetE _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetA *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetA _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetP *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetP _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetWType *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetWType _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetOType *)
        iApply (get_case _ _ _ _ _ _ _ _ _ (GetOType _ _) with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Seal *)
        iApply (seal_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* UnSeal *)
        iApply (unseal_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* EInit *)
        iApply (einit_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* EDeInit *)
        iApply (edeinit_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* EStoreId *)
        iApply (estoreid_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* IsUnique *)
        iApply (isunique_case with "[] [] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto. iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
        iNext ; iIntros "_".
        iApply wp_value.
        iIntros (Hcontr); inversion Hcontr.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iIntros (_).
        iExists (<[PC:=LCap p b e a v]> lregs). iFrame.
        iAssert (∀ r : RegName, ⌜is_Some (<[PC:=LCap p b e a v]> lregs !! r)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r).
          - subst r; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }
        iFrame "HA".
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (LCap p b e a v)).
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iNext ; iIntros "_".
     iApply wp_value.
     iIntros (Hcontr); inversion Hcontr.
  Admitted.

  Theorem fundamental w r :
    custom_enclave_contract_gen ->
       custom_enclave_inv ⊢ interp w -∗ interp_expression r w.
  Proof.
    iIntros (Hcontract) "#Hsys Hw". destruct w as [| [c | ] | ].
    2: { iApply fundamental_cap; done. }
    all: iClear "Hw"; iIntros "(? & Hreg & ?)"; unfold interp_conf.
    all: iApply (wp_wand with "[-]"); [ | iIntros (?) "H"; iApply "H"].
    all: iApply (wp_bind (fill [SeqCtx])); cbn.
    all: unfold registers_mapsto; rewrite -insert_delete_insert.
    all: iDestruct (big_sepM_insert with "Hreg") as "[HPC ?]"; first by rewrite lookup_delete.
    all: iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
    all: iNext; iIntros; cbn; iApply wp_pure_step_later; auto.
    all: iNext; iIntros "_"; iApply wp_value; iIntros (?); congruence.
  Qed.

  (* The fundamental theorem implies the exec_cond *)

  Definition exec_cond b e p v : iProp Σ :=
    (∀ a r, ⌜a ∈ₐ [[ b , e ]]⌝ → ▷ □ interp_expression r (LCap p b e a v))%I.

  Lemma interp_exec_cond p b e a v :
    p ≠ E ->
    custom_enclave_contract_gen ->
    custom_enclave_inv
    ⊢ interp (LCap p b e a v) -∗ exec_cond b e p v.
  Proof.
    iIntros (Hnp Hcontract) "#Hsys #Hw".
    iIntros (a0 r Hin). iNext. iModIntro.
    iApply fundamental; try done.
    rewrite !fixpoint_interp1_eq /=. destruct p; try done.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)

  Lemma exec_wp p b e a v :
    isCorrectLPC (LCap p b e a v) ->
    exec_cond b e p v -∗
    ∀ lregs, ▷ □ (interp_expr interp lregs) (LCap p b e a v).
  Proof.
    iIntros (Hvlpc) "#Hexec".
    rewrite /exec_cond.
    iIntros (lregs).
    assert (a ∈ₐ[[b,e]])%I as Hin.
    { rewrite /in_range.
      inversion Hvlpc as [lpc p' b' e' a' Harg Hvpc]; subst; cbn in *; simplify_eq.
      inversion Hvpc; subst; auto.
    }
    iSpecialize ("Hexec" $! a lregs Hin). iFrame "#".
  Qed.

  (* updatePcPerm adds a later because of the case of E-capabilities, which
     unfold to ▷ interp_expr *)
  Lemma interp_updatePcPermL lw :
    custom_enclave_contract_gen ->
    custom_enclave_inv
    ⊢ interp lw -∗ ▷ (∀ lregs, interp_expression lregs (updatePcPermL lw)).
  Proof.
    iIntros (Hcontract) "#Hsys #Hw".
    assert ((∃ b e a v, lw = LCap E b e a v) ∨ updatePcPermL lw = lw) as [Hw | ->].
    { destruct lw as [ | [ | ] | ]; eauto. unfold updatePcPermL.
      case_match; eauto. left. eexists _,_,_,_; eauto.
    }
    { destruct Hw as (b & e & a & v & ->). rewrite fixpoint_interp1_eq. cbn -[all_registers_s].
      iNext. iIntros (rmap). iSpecialize ("Hw" $! rmap). iDestruct "Hw" as "#Hw".
      iIntros "(HPC & Hr & ?)". iApply "Hw". iFrame. }
    { iNext. iIntros (rmap). iApply fundamental; eauto. }
  Qed.

  Lemma jmp_to_unknown lw :
    custom_enclave_contract_gen ->
    custom_enclave_inv
    ⊢ interp lw -∗
      ▷ (∀ rmap,
          ⌜dom rmap = all_registers_s ∖ {[ PC ]}⌝ →
          PC ↦ᵣ updatePcPermL lw
          ∗ ([∗ map] r↦lw ∈ rmap, r ↦ᵣ lw ∗ interp lw)
          ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable) {{ λ v, ⌜v = HaltedV⌝ →
               ∃ lr : LReg, full_map lr ∧ registers_mapsto lr ∗ na_own logrel_nais ⊤ }}).
  Proof.
    iIntros (Hcontract) "#Hsys #Hw". iDestruct (interp_updatePcPermL with "Hsys Hw") as "Hw'"
    ; first done.
    iNext.
    iIntros (rmap Hrmap).
    set rmap' := <[ PC := (LInt 0%Z: LWord) ]> rmap : LReg.
    iSpecialize ("Hw'" $! rmap').
    iIntros "(HPC & Hr & Hna)". unfold interp_expression, interp_expr, interp_conf. cbn.
    iApply "Hw'". iClear "Hw'". iFrame. rewrite /registers_mapsto.
    iDestruct (big_sepM_sep with "Hr") as "(Hr & HrV)".
    iSplitL "HrV"; [iSplit|].
    { unfold full_map. iIntros (r).
      destruct (decide (r = PC)). { subst r. rewrite lookup_insert //. }
      rewrite lookup_insert_ne //. iPureIntro. rewrite -elem_of_dom Hrmap. set_solver. }
    { iIntros (ri v Hri Hvs).
      rewrite lookup_insert_ne // in Hvs.
      iDestruct (big_sepM_lookup _ _ ri with "HrV") as "HrV"; eauto. }
    rewrite insert_insert. iApply big_sepM_insert.
    { apply not_elem_of_dom. rewrite Hrmap. set_solver. }
    iFrame.
  Qed.

  Lemma region_integers_alloc' E (b e a: Addr) (v : Version) l p :
    Forall (λ lw, is_zL lw = true) l →
    finz.seq_between b e ## reserved_addresses ->
    custom_enclave_contract_gen ->
    custom_enclave_inv
    ⊢
    ([∗ list] la;lw ∈ (fun a => (a,v)) <$> (finz.seq_between b e);l, la ↦ₐ lw) ={E}=∗
    interp (LCap p b e a v).
  Proof.
    iIntros (Hl Hreserved Hcontract) "#Hsys H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_integers_alloc _ _ _ a _ _ RX with "H") as ">#H"; auto.
         iModIntro. iIntros (r).
         iNext. iModIntro.
         iDestruct (fundamental _ r with "[$] [$]") as "H'"; eauto.
    }
    all: iApply region_integers_alloc; eauto.
  Qed.

  Lemma region_valid_alloc' E (b e a: Addr) v l p :
    finz.seq_between b e ## reserved_addresses ->
    custom_enclave_contract_gen ->
    custom_enclave_inv
    ⊢
    ([∗ list] w ∈ l, interp w) -∗
    ([∗ list] la;lw ∈ (fun a => (a,v)) <$> (finz.seq_between b e);l, la ↦ₐ lw) ={E}=∗
    interp (LCap p b e a v).
  Proof.
    iIntros (Hreserved Hcontract) "#Hsys #Hl H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_valid_alloc _ RX _ _ a _ _  with "Hl H") as ">#H"; auto.
         iModIntro. iIntros (r).
         iNext. iModIntro.
         iDestruct (fundamental _ r with "[$] [$]") as "H'"; eauto. }
    all: iApply (region_valid_alloc with "Hl"); eauto.
  Qed.

  Lemma region_in_region_alloc' E (b e a: Addr) v l p :
    finz.seq_between b e ## reserved_addresses ->
    Forall (λ a0 : Addr, ↑logN.@(a0, v) ⊆ E) (finz.seq_between b e) ->
    Forall (λ lw, is_zL lw = true \/ in_region lw b e v) l →
    custom_enclave_contract_gen ->
    custom_enclave_inv
    ⊢
    ([∗ list] a;w ∈ finz.seq_between b e;l, (a,v) ↦ₐ w) ={E}=∗
    interp (LCap p b e a v).
  Proof.
    iIntros (Hreserved Hmasks Hl Hcontract) "#Hsys H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_valid_in_region _ _ _ a _ _ RX with "H") as ">#H"; auto.
         iModIntro. iIntros (r).
         iNext. iModIntro.
         iDestruct (fundamental _ r with "[$] [$]") as "H'"; eauto. }
    all: iApply (region_valid_in_region with "H"); eauto.
  Qed.

End fundamental.
