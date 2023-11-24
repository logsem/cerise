From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel macros rules.
From cap_machine.proofmode Require Import tactics_helpers proofmode.

Section call.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* Macro for a heap based calling convention *)

  (*
     The calling convention performs the following steps:

     1. It allocates heap space to store the current r_env and the continuation
     2. It creates a copy of the PC and moves it to point to the continuing instruction
     3. It stores r_env, and continuation
     4. It restricts the allocated capability to be an IE capability, containing the return pointer
        and the env (a closure)
     5. It clears all registers except r1, rt_0 and the parameters
   *)

  Fixpoint store_locals_instrs r1 locals :=
    match locals with
    | [] => []
    | r :: locals => (store_r r1 r)
                 :: (lea_z r1 1)
                 :: store_locals_instrs r1 locals
    end.

  Definition store_locals a r1 locals :=
    ([∗ list] a_i;i ∈ a;(store_locals_instrs r1 locals), a_i ↦ₐ i)%I.

  (* helper lemma for the length of the registers *)
  Ltac iRegNotEq Hne :=
    repeat (apply not_elem_of_cons in Hne;
            (let Hneq := fresh "Hneq" in destruct Hne as [Hneq Hne])); auto.


  Lemma store_locals_spec_middle
        (* cont *) φ
        (* list of locals *) r1 locals mlocals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l a_l :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    finz.dist a_l e_l = strings.length locals →
    strings.length locals > 0 →
    writeAllowed p_l = true → withinBounds b_l e_l a_l = true ->
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length locals = length wsr ->

    (▷ store_locals a r1 locals
   ∗ ▷ PC ↦ᵣ WCap p b e a_first
   ∗ ▷ r1 ↦ᵣ WCap p_l b_l e_l a_l
   ∗ ▷ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
   ∗ ▷ (∃ ws, [[a_l,e_l]]↦ₐ[[ws]])
   ∗ ▷ (PC ↦ᵣ WCap p b e a_last
           ∗ r1 ↦ᵣ WCap p_l b_l e_l e_l
           ∗ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
           ∗ [[a_l,e_l]]↦ₐ[[wsr]]
           ∗ store_locals a r1 locals
           -∗ WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa Hwb Hperm Hlength) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)".
    iInduction (locals) as [|r locals] "IH" forall (a_l mlocals wsr a a_first Hvpc Hcont Hnz Hsize Hwb Hperm Hlength).
    { inversion Hnz. }
    destruct locals as [|r' locals].
    - destruct wsr;[inversion Hlength|]. destruct wsr;[|inversion Hlength].
      apply Permutation_sym, Permutation_singleton_r in Hperm.
      assert (mlocals = {[r:=w]}) as Heq;[|subst mlocals].
      { apply map_to_list_inj. rewrite map_to_list_singleton. apply Permutation_singleton_r. auto. }
      rewrite big_sepM_singleton.
      rewrite /store_locals /store_locals_instrs.
      iDestruct "Hbl" as (ws) "Hbl".
      iDestruct (big_sepL2_length with "Hbl") as %Hlength_bl.
      rewrite finz_seq_between_length Hsize in Hlength_bl.
      destruct ws;[inversion Hlength_bl|]. destruct ws;[|inversion Hlength_bl].
      assert (finz.seq_between a_l e_l = [a_l]) as Heq_locals;[ by rewrite /finz.seq_between Hsize /=|].
      rewrite /region_mapsto Heq_locals.
      iDestruct "Hbl" as "[Ha_l _]".
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      (* store r_t1 r *)
      destruct_list a.
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
      iPrologue "Hprog".
      iApply (wp_store_success_reg with "[$HPC $Hi $Hlocals $Ha_l $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto|auto|].
      iEpilogue "(HPC & Hprog_done & Hr & Hr_t1 & Ha_l)".
      (* lea r_t1 1 *)
      pose proof (contiguous_between_last _ _ _ a Hcont eq_refl) as Hlast.
      assert (a_l + 1 = Some e_l)%a as Hnext.
      { rewrite /finz.dist /= in Hsize. revert Hsize;clear;solve_addr. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hlast
        |apply Hnext |destruct p_l;auto;inversion Hwa |destruct p_l;auto;inversion Hwa| ..].
      iEpilogue "(HPC & Hi & Hr_t1)".
      (* φ *)
      iApply "Hcont".
      iFrame. done.
    - destruct wsr;[inversion Hlength|]. destruct wsr;[inversion Hlength|].
      simpl in *.
      assert (mlocals !! r = Some w) as Hrw.
      { apply elem_of_map_to_list. rewrite -Hperm. constructor. }
      iDestruct (big_sepM_delete _ _ r with "Hlocals") as "[Hr Hlocals]";[eauto|].
      assert (is_Some (a_l + 1)%a) as [a_l' Ha_l'].
      { rewrite /finz.dist /= in Hsize. destruct (a_l + 1)%a eqn:Hnone;eauto.
        simpl in Hsize. revert Hnone Hsize;clear;solve_addr. }
      assert (finz.seq_between a_l e_l = a_l :: finz.seq_between a_l' e_l) as Heq.
      { rewrite /finz.seq_between Hsize /=. rewrite (addr_incr_eq Ha_l') /=.
        f_equiv. assert (finz.dist a_l' e_l = S (strings.length locals)) as ->;auto.
        revert Ha_l' Hsize;clear. rewrite /finz.dist. solve_addr.
      }
      rewrite /region_mapsto Heq.
      iDestruct "Hbl" as (ws) "Hbl".
      iDestruct (big_sepL2_length with "Hbl") as %Hlengthbl.
      destruct ws;[inversion Hlengthbl|].
      iDestruct "Hbl" as "[Ha_l Hbl]".
      (* store r_t1 r *)
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog. simpl in Hlength_prog.
      destruct a;[inversion Hlength_prog|].
      destruct a;[inversion Hlength_prog|].
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
      iPrologue "Hprog".
      iApply (wp_store_success_reg with "[$HPC $Hi $Hr $Ha_l $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto|auto|].
      iEpilogue "(HPC & Hprog_done & Hr & Hr_t1 & Ha_l)".
      (* lea r_t1 1 *) simpl in Hlength_prog.
      destruct a;[inversion Hlength_prog|].
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 1
        |apply Ha_l' |destruct p_l;auto;inversion Hwa |destruct p_l;auto;inversion Hwa|].
      iEpilogue "(HPC & Hi & Hr_t1)".
      iApply ("IH" $! a_l' (delete r mlocals) (w0 :: wsr) with "[] [] [] [] [] [] [] Hprog HPC Hr_t1 Hlocals [Hbl]").
      + iPureIntro. eapply isCorrectPC_range_restrict;[eauto|].
        assert (a_first + 1 = Some f0)%a;[iContiguous_next Hcont 0|].
        assert (f0 + 1 = Some f)%a;[iContiguous_next Hcont 1|].
        split;[revert H H0;clear|clear];solve_addr.
      + iPureIntro.
        assert (a_first + 1 = Some f0)%a;[iContiguous_next Hcont 0|].
        assert (f0 + 1 = Some f)%a;[iContiguous_next Hcont 1|].
        inversion Hcont;simplify_eq.
        inversion H6;simplify_eq. auto.
      + iPureIntro;simpl. lia.
      + iPureIntro. simpl in *.
        revert Hsize Ha_l'. rewrite /finz.dist. clear. solve_addr.
      + iPureIntro. simpl in *.
        revert Hsize Ha_l' Hwb. rewrite /finz.dist. clear. intros.
        apply andb_true_intro.
        apply andb_prop in Hwb. revert Hwb. rewrite !Z.leb_le !Z.ltb_lt.
        intros.
        split; try solve_addr.
      + iPureIntro. rewrite stdpp_extra.map_to_list_delete;eauto.
        assert (NoDup (r :: r' :: locals))%I as HNoDup.
        { assert (r :: r' :: locals = (zip (r :: r' :: locals) (w :: w0 :: wsr)).*1).
          { simpl. f_equal. f_equal. assert (list_fmap (RegName * Word)%type RegName fst (zip locals wsr) = (zip locals wsr).*1) as ->;[auto|].
            rewrite fst_zip;auto. lia. }
          rewrite H.
          assert (zip (r :: r' :: locals) (w :: w0 :: wsr) = (r, w) :: (r', w0) :: zip locals wsr) as ->;auto.
          rewrite Hperm. apply NoDup_map_to_list_fst. apply _. }
        clear -HNoDup Hlength. apply NoDup_cons in HNoDup as [? HNoDup].
        apply NoDup_cons. split.
        { intros Hcontr. apply H.
          apply fst_elem_of_cons with (w0 :: wsr). auto. }
        simpl. assert (list_fmap (RegName * Word)%type RegName fst (zip locals wsr) = (zip locals wsr).*1) as ->;auto.
        rewrite fst_zip;auto. lia.
      + eauto.
      + eauto.
      + iNext. iIntros "(HPC & Hr_t1 & Hlocals & Hbl & Hprog)".
        iApply "Hcont". iFrame.
        iApply (big_sepM_delete);[|iFrame]. apply elem_of_map_to_list. rewrite -Hperm. constructor.
  Qed.


  Lemma store_locals_spec
        (* cont *) φ
        (* list of locals *) r1 mlocals locals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    finz.dist b_l e_l = strings.length locals →
    strings.length locals > 0 → (* we assume the length of locals is non zero, or we would not be able to take a step before invoking continuation *)
    writeAllowed p_l = true →
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length locals = length wsr ->

    (▷ store_locals a r1 locals
   ∗ ▷ PC ↦ᵣ WCap p b e a_first
   ∗ ▷ r1 ↦ᵣ WCap p_l b_l e_l b_l
   ∗ ▷ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
   ∗ ▷ (∃ ws, [[b_l,e_l]]↦ₐ[[ws]])
   ∗ ▷ (PC ↦ᵣ WCap p b e a_last
           ∗ r1 ↦ᵣ WCap p_l b_l e_l e_l
           ∗ ([∗ map] r↦w ∈ mlocals, r ↦ᵣ w)
           ∗ [[b_l,e_l]]↦ₐ[[wsr]]
           ∗ store_locals a r1 locals
           -∗ WP Seq (Instr Executable) {{ φ }})

   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa Hperm Hlen) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)".
    iApply (store_locals_spec_middle with "[$HPC $Hprog $Hr_t1 $Hlocals $Hbl $Hcont]");eauto.
    simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt.
    split;[clear;lia|].
    rewrite /finz.dist in Hsize. lia.
  Qed.

  Definition call_instrs f_m offset_to_cont r1 (locals params : list RegName) :=
    (* allocate and store locals *)
    malloc_instrs f_m (strings.length locals) ++
    store_locals_instrs r_t1 locals ++
    (* allocate the space for the indirection of the IE-cap *)
    [move_r r_t6 r_t1] ++
    malloc_instrs f_m 2 ++

    (* prepare and store continuation *)
    [move_r r_t31 r_t1;
    move_r r_t1 PC;

    lea_z r_t1 offset_to_cont;
    store_r r_t31 r_t1;
    lea_z r_t31 1;
    (* store locals cap *)
    store_r r_t31 r_t6;
    (* setup return capability *)
    lea_z r_t31 (-1);
    restrict_z r_t31 ie] ++
    (* clear all registers except params, PC, r_t31 and r1 *)
    rclear_instrs (list_difference all_registers ([PC;r_t31;r1]++params)) ++
    (* jmp to r1 *)
    [jmp r1].


  Definition offset_to_cont_call params :=
    6 + (strings.length (rclear_instrs (list_difference all_registers params))) - 1.

  Definition call a f_m r1 locals params :=
    ([∗ list] a_i;w ∈ a;(call_instrs f_m (offset_to_cont_call params) r1 locals params), a_i ↦ₐ w)%I.


  Lemma rclear_length l :
    length (rclear_instrs l) = length l.
  Proof.
    induction l;auto.
    simpl. auto.
  Qed.

  (* stops just before the jmp *)
  Lemma call_spec_main
        (* call *) r1 mlocals mparams wadv
        (* remaining registers *) (rmap rmap' : gmap RegName Word)
        (* pc *) a p b e a_first a_last
        (* malloc *) f_m b_m e_m mallocN EN
        (* linking *) b_link a_link e_link a_entry
        (* cont *) φ :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    strings.length (map_to_list mlocals).*1 > 0 →

    dom rmap = all_registers_s ∖ {[ PC; r_t31; r1 ]} ∖ (dom mparams) ∖ (dom mlocals) →
    dom rmap' = all_registers_s ∖ {[ PC; r_t31; r1 ]} ∖ (dom mparams) →
    {[r_t1; r_t2; r_t3; r_t4; r_t5; r_t6]} ⊆ dom rmap → (* we need to know that neither params nor locals use these gen pur registers *)
    ↑mallocN ⊆ EN →
    (* len_call = length (call a f_m r1 (map_to_list mlocals).*1 (map_to_list mparams).*1) -> *)

    (▷ call a f_m r1 (map_to_list mlocals).*1 (map_to_list mparams).*1
    ∗ ▷ PC ↦ᵣ WCap p b e a_first
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* registers *)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ mparams, r_i ↦ᵣ w_i)
    ∗ ▷ (∃ w, r_t31 ↦ᵣ w)
    ∗ ▷ r1 ↦ᵣ wadv
    ∗ ▷ ([∗ map] r_i↦w_i ∈ mlocals, r_i ↦ᵣ w_i)

    (* continuation *)
    ∗ ▷ ((∃ b_c e_c b_l e_l a_end,
             ⌜(a_end + 1)%a = Some a_last⌝
            ∗ ⌜(b_c + 2)%a = Some e_c⌝
            ∗ PC ↦ᵣ WCap p b e a_end
            ∗ ([∗ map] r_i↦_ ∈ rmap', r_i ↦ᵣ WInt 0%Z)
            ∗ ([∗ map] r_i↦w_i ∈ mparams, r_i ↦ᵣ w_i)
            ∗ b ↦ₐ WCap RO b_link e_link a_link
            ∗ a_entry ↦ₐ WCap E b_m e_m b_m
            ∗ r1 ↦ᵣ wadv
            ∗ r_t31 ↦ᵣ WCap IE b_c e_c b_c
            ∗ [[b_c,e_c]]↦ₐ[[ [WCap p b e a_last;WCap RWX b_l e_l e_l] ]]
            ∗ [[b_l,e_l]]↦ₐ[[ (map_to_list mlocals).*2 ]]
            ∗ call a f_m r1 (map_to_list mlocals).*1 (map_to_list mparams).*1
            ∗ na_own logrel_nais EN)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hwb Hlink Hnz Hdom1 Hdom2 Hsub Hnainv)
            "(>Hprog & >HPC & #Hnainv & Hown & >Hb & >Ha_entry & >Hgen & >Hparams & >Hr_t31 & >Hr1 & >Hlocals & Hcont)".
    (* prepare the registers *)
    iDestruct "Hr_t31" as (w) "Hr_t31".
    iAssert (⌜mparams ##ₘ mlocals⌝)%I as %Hdisj1.
    { rewrite map_disjoint_spec. iIntros (i x y Hx Hy).
      iDestruct (big_sepM_delete _ _ i with "Hparams") as "[Hi1 Hparams]";[eauto|].
      iDestruct (big_sepM_delete _ _ i with "Hlocals") as "[Hi2 Hlocals]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    iAssert (⌜mparams ##ₘ rmap⌝)%I as %Hdisj2.
    { rewrite map_disjoint_spec. iIntros (i x y Hx Hy).
      iDestruct (big_sepM_delete _ _ i with "Hparams") as "[Hi1 Hparams]";[eauto|].
      iDestruct (big_sepM_delete _ _ i with "Hgen") as "[Hi2 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    iAssert (⌜mlocals ##ₘ rmap⌝)%I as %Hdisj3.
    { rewrite map_disjoint_spec. iIntros (i x y Hx Hy).
      iDestruct (big_sepM_delete _ _ i with "Hgen") as "[Hi1 Hgen]";[eauto|].
      iDestruct (big_sepM_delete _ _ i with "Hlocals") as "[Hi2 Hlocals]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    iAssert (⌜PC ∉ dom mparams ∧ r_t31 ∉ dom mparams ∧ r1 ∉ dom mparams⌝)%I as %Hdisj4.
    { repeat iSplit; iIntros (Hcontr); apply elem_of_dom in Hcontr as [? Hi];
        (iDestruct (big_sepM_delete with "Hparams") as "[Hi1 Hparams]";[by eauto|]).
      by iDestruct (regname_dupl_false with "Hi1 HPC") as "Hfalse".
      by iDestruct (regname_dupl_false with "Hi1 Hr_t31") as "Hfalse".
      by iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse".
    }
    iAssert (⌜PC ∉ dom mlocals ∧ r_t31 ∉ dom mlocals ∧ r1 ∉ dom mlocals⌝)%I as %Hdisj5.
    { repeat iSplit; iIntros (Hcontr); apply elem_of_dom in Hcontr as [? Hi];
        (iDestruct (big_sepM_delete with "Hlocals") as "[Hi1 Hlocals]";[by eauto|]).
      by iDestruct (regname_dupl_false with "Hi1 HPC") as "Hfalse".
      by iDestruct (regname_dupl_false with "Hi1 Hr_t31") as "Hfalse".
      by iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse".
    }
    iAssert (⌜∀ r, r ∈ {[r_t1; r_t2; r_t3; r_t4; r_t5; r_t6]} → r ≠ r1⌝)%I as %Hneregs.
    { iIntros (r Hin Hcontr). subst. apply Hsub in Hin.
      apply elem_of_dom in Hin as [x Hx].
      iDestruct (big_sepM_delete with "Hgen") as "[Hr Hgen]";[apply Hx|].
      by iDestruct (regname_dupl_false with "Hr Hr1") as "Hfalse".
    }

    iDestruct (big_sepM_union with "[$Hlocals $Hparams]") as "Hlocalsparams";[auto|].
    iDestruct (big_sepM_union with "[$Hgen $Hlocalsparams]") as "Hgenlocalsparams";[apply map_disjoint_union_r_2;auto|].
    iAssert (⌜(rmap ∪ (mlocals ∪ mparams)) !! r1 = None⌝)%I as %Hnone.
    { destruct ((rmap ∪ (mlocals ∪ mparams)) !! r1) eqn:Hsome;auto.
      iDestruct (big_sepM_delete _ _ r1 with "Hgenlocalsparams") as "[Hi1 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse". done. }
    iAssert (⌜(rmap ∪ (mlocals ∪ mparams)) !! r_t31 = None⌝)%I as %Hnone'.
    { destruct ((rmap ∪ (mlocals ∪ mparams)) !! r_t31) eqn:Hsome;auto.
      iDestruct (big_sepM_delete _ _ r_t31 with "Hgenlocalsparams") as "[Hi1 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hr_t31") as "Hfalse". done. }
    iAssert (⌜r1 ≠ PC⌝)%I as %Hne1.
    { iIntros (->). iDestruct (regname_dupl_false with "HPC Hr1") as "Hfalse". done. }
    iAssert (⌜r1 ≠ r_t31⌝)%I as %Hne2.
    { iIntros (->). iDestruct (regname_dupl_false with "Hr_t31 Hr1") as "Hfalse". done. }
    iDestruct (big_sepM_insert with "[$Hgenlocalsparams $Hr1]") as "Hgenlocalsparams";[auto|].

    assert (dom (<[r1:=wadv]> (rmap ∪ (mlocals ∪ mparams))) = all_registers_s ∖ {[PC; r_t31]}) as Hdomeq.
    { rewrite dom_insert_L !dom_union_L. revert Hdom1 Hne1 Hne2 Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5. clear. intros Hdom1 Hne1 Hne2 Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5.
      assert (all_registers_s ∖ {[PC; r_t31]} = {[r1]} ∪ all_registers_s ∖ {[PC; r_t31; r1]}) as ->.
      { rewrite - !difference_difference_l_L.
        rewrite -union_difference_L; auto.
        apply subseteq_difference_r;[set_solver|].
        apply subseteq_difference_r;[set_solver|].
        apply all_registers_subseteq. }
      assert (dom rmap ∪ (dom mlocals ∪ dom mparams) =
              dom mparams ∪ (dom mlocals ∪ dom rmap)) as ->.
      { rewrite (union_comm_L _ (dom mparams)). rewrite union_assoc_L. rewrite (union_comm_L _ (dom mparams)).
        rewrite -union_assoc_L. rewrite (union_comm_L _ (dom mlocals)). auto. }
      rewrite Hdom1. rewrite - !difference_difference_l_L - !union_difference_L; auto.
      repeat (apply subseteq_difference_r;[set_solver|]). apply all_registers_subseteq.
      repeat (apply subseteq_difference_r;[set_solver|]). apply all_registers_subseteq.
      apply subseteq_difference_r;[apply map_disjoint_dom;auto|].
      repeat (apply subseteq_difference_r;[set_solver|]). apply all_registers_subseteq.
    }

    (* malloc f_m |locals| *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog rest1 link1) "(Hmalloc_prog & Hprog & #Hcont1)";[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont1 & Hcont2 & Heqapp1 & Hlink1).
    rewrite -/(malloc _ _ _).
    iApply (wp_wand_l _ _ _ (λne (v : discreteO val), ((φ v ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)))%I. iSplitR.
    { iIntros (v) "[H|H] /=";auto. }
    iApply (malloc_spec with "[- $HPC $Hnainv $Hown $Hb $Ha_entry $Hmalloc_prog $Hr_t31 $Hgenlocalsparams]");auto;[|apply Hcont1|..].
    { eapply isCorrectPC_range_restrict;eauto. split;[clear;solve_addr|]. apply contiguous_between_bounds in Hcont2. auto. }
    iNext. iIntros "(HPC & Hmalloc & Hb & Ha_entry & Hregion & Hr_t31 & Hna & Hgenlocalsparams)".
    iDestruct "Hregion" as (b_l e_l Hlocals_size) "(Hr_t1 & Hbl)".

    (* in order to store the locals, we need to extract locals from the map *)
    rewrite !delete_insert_ne;auto. 2: { apply Hneregs. constructor. }
    rewrite delete_union. rewrite !insert_union_l.
    rewrite (delete_notin (mlocals ∪ mparams));[|disjoint_from_rmap rmap].
    iDestruct (big_sepM_union with "Hgenlocalsparams") as "[Hgen Hlocalsparams]".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap|]).
      apply map_disjoint_insert_l_2. apply lookup_union_None in Hnone as [? ?];auto.
      apply map_disjoint_delete_l. apply map_disjoint_union_r_2;auto. }
    iDestruct (big_sepM_union with "Hlocalsparams") as "[Hlocals Hparams]";auto.

    (* store locals *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (storelocals_prog rest2 link2) "(Hstorelocals_prog & Hprog & #Hcont2)";[apply Hcont2|].
    iDestruct "Hcont2" as %(Hcont3 & Hcont4 & Heqapp2 & Hlink2).
    iApply (store_locals_spec _ _ _ _ ((map_to_list mlocals).*2) with "[- $HPC $Hstorelocals_prog $Hr_t1 $Hlocals]");[|apply Hcont3|auto..].
    { eapply isCorrectPC_range_restrict;[apply Hvpc|].
      apply contiguous_between_bounds in Hcont1.
      apply contiguous_between_bounds in Hcont4. auto. }
    { clear -Hlocals_size. rewrite /finz.dist. solve_addr. }
    { rewrite zip_fst_snd. auto. }
    { apply length_fst_snd. }
    iSplitL "Hbl";[eauto|].
    iNext. iIntros "(HPC & Hr_t1 & Hmlocals & Hbl & Hstorelocals_prog)".

    (* prepare for the rest of the program: new correct PC range, get length of rest2, and assert its first element is link2 *)
    assert (isCorrectPC_range p b e link2 a_last) as Hvpc1.
    { eapply isCorrectPC_range_restrict;[apply Hvpc|]. split;[|clear;solve_addr].
      apply contiguous_between_bounds in Hcont1.
      apply contiguous_between_bounds in Hcont3. clear -Hcont3 Hcont1 Hlink2. solve_addr. }
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    destruct rest2 as [|? rest2];[inversion Hlength_prog|].
    apply contiguous_between_cons_inv_first in Hcont4 as Heq; subst f.

    (* get some general purpose registers *)
    assert (is_Some (rmap !! r_t6)) as [w6 Hw6];[apply elem_of_dom;apply Hsub;repeat constructor|].
    iDestruct (big_sepM_delete _ _ r_t6 with "Hgen") as "[Hr_t6 Hgen]".
    { assert (r_t6 ≠ r1) as Hne;[apply Hneregs;repeat constructor|].
      rewrite !lookup_insert_ne;auto. rewrite lookup_delete_ne;auto. eauto. }

    (* move r_t6 r_t1 *)
    destruct rest2 as [|? rest2];[inversion Hlength_prog|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t6 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link2 a_last|iContiguous_next Hcont4 0|].
    iEpilogue "(HPC & Hi & Hr_t6 & Hr_t1)". iCombine "Hstorelocals_prog Hmalloc" as "Hprog_done".
    iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* malloc 2 *)
    (* prepare the registers *)
    iDestruct (big_sepM_insert with "[$Hgen $Hr_t6]") as "Hgen";[apply lookup_delete|rewrite insert_delete_insert].
    rewrite -delete_insert_ne;[|apply Hneregs;constructor]. rewrite - !delete_insert_ne;auto.
    iDestruct (big_sepM_insert with "[$Hgen $Hr_t1]") as "Hgen";[apply lookup_delete|rewrite insert_delete_insert].
    iDestruct (big_sepM_union with "[$Hmlocals $Hparams]") as "Hlocalsparams";[auto|].
    iDestruct (big_sepM_union with "[$Hgen $Hlocalsparams]") as "Hgenlocalsparams".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap|]).
      apply map_disjoint_insert_l_2;[|apply map_disjoint_union_r_2];auto. apply lookup_union_None in Hnone as [? ?];auto. }
    (* we assert the register state has the needed domain *)
    assert (dom (<[r_t1:=WCap RWX b_l e_l e_l]> (<[r_t6:=WCap RWX b_l e_l e_l]> (<[r_t2:=WInt 0%Z]> (<[r_t3:=WInt 0%Z]>
            (<[r_t4:=WInt 0%Z]> (<[r_t5:=WInt 0%Z]> (<[r1:=wadv]> rmap)))))) ∪ (mlocals ∪ mparams)) = all_registers_s ∖ {[PC; r_t31]}) as Hdomeq'.
    { rewrite dom_union_L 6!dom_insert_L.
      assert ({[r_t1]} ∪ ({[r_t6]} ∪ ({[r_t2]} ∪ ({[r_t3]} ∪ ({[r_t4]} ∪ ({[r_t5]}
             ∪ dom (<[r1:=wadv]> rmap)))))) = dom (<[r1:=wadv]> rmap)) as ->.
      { clear -Hsub. rewrite dom_insert_L. set_solver. }
      rewrite -dom_union_L -insert_union_l. auto. }

    (* prepare the program memory *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog2 rest3 link3) "(Hmalloc & Hprog & #Hcont5)".
    { apply contiguous_between_cons_inv in Hcont4 as [?[? [? Hcont5] ] ].
      apply contiguous_between_cons_inv_first in Hcont5 as Heq;subst x. apply Hcont5. }
    iDestruct "Hcont5" as %(Hcont5 & Hcont6 & Heqapp3 & Hlink3).

    (* apply malloc spec *)
    iApply (malloc_spec _ 2 with
             "[- $HPC $Hnainv $Hna $Hb $Ha_entry $Hmalloc $Hr_t31 $Hgenlocalsparams]")
    ;auto;[|apply Hcont5|].
    { eapply isCorrectPC_range_restrict;eauto.
      assert (link2 + 1 = Some f)%a as Hnext;[iContiguous_next Hcont4 0|].
      apply contiguous_between_bounds in Hcont6. clear -Hnext Hcont6. solve_addr. }
    iNext. iIntros "(HPC & Hmalloc & Hb & Ha_entry & Hregion & Hr_t31 & Hna & Hgenlocalsparams)".
    iDestruct "Hregion" as (b_l' e_l' Hact_size) "(Hr_t1 & Hbl')". iCombine "Hmalloc" "Hprog_done" as "Hprog_done".

    (* prepare for the rest of the program: new correct PC range, get length of rest2, and assert its first element is link2 *)
    assert (isCorrectPC_range p b e link3 a_last) as Hvpc2.
    { eapply isCorrectPC_range_restrict;[apply Hvpc|]. split;[|clear;solve_addr].
      apply contiguous_between_bounds in Hcont1.
      apply contiguous_between_bounds in Hcont3.
      assert (link2 + 1 = Some f)%a as Hnext;[iContiguous_next Hcont4 0|].
      apply contiguous_between_bounds in Hcont5.
      clear -Hcont3 Hcont5 Hnext Hcont1 Hlink2. solve_addr. }
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog'.
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    apply contiguous_between_cons_inv_first in Hcont6 as Heq;subst f0.

    (* prepare the memory for the indirection *)
    assert (b_l' <= e_l')%a as Hle';[clear -Hact_size;solve_addr|].
    assert (finz.dist b_l' e_l' = 2) as Hact_size_alt;[rewrite /finz.dist;clear -Hact_size;solve_addr|].
    rewrite /region_addrs_zeroes Hact_size_alt. iSimpl in "Hbl'".
    set l := finz.seq_between b_l' e_l'.
    assert (contiguous_between l b_l' e_l') as Hcontbl';[rewrite /l;apply contiguous_between_region_addrs;auto|].
    assert (length l = 2) as Hlength_l;[rewrite /l finz_seq_between_length;auto|].
    assert (∀ a, a ∈ l → withinBounds b_l' e_l' a = true) as Hwbbl'.
    { intros a1 Hin. rewrite andb_true_iff. rewrite Z.leb_le Z.ltb_lt.
      eapply contiguous_between_middle_bounds';[apply Hcontbl'|auto]. }
    destruct l;[inversion Hlength_l|]. apply contiguous_between_cons_inv_first in Hcontbl' as Heq. subst f0.

    (* move r_t31 r_t1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t31 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 0|].
    iEpilogue "(HPC & Hi & Hr_t31 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* move r_t1 PC *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 1|].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* lea r_t1 offset_to_cont *)
    destruct l as [|b_l'' ?];[inversion Hlength_l|].
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest3.

    (* We need to know that the result of the lea is the last correct continuation *)
    (* The following proof is quite tedious, and should perhaps be generalized *)
    assert (f0 + (offset_to_cont_call (map_to_list mparams).*1) = Some a_last)%a as Hlea.
    { rewrite /offset_to_cont_call.
      eapply (contiguous_between_middle_to_end _ _ _ 1);[apply Hcont6|auto|..].
      clear -Hlength_rest3 Hne1 Hne2 Hdisj4. revert Hlength_rest3.
      set a := rclear_instrs (list_difference all_registers ([PC; r_t31; r1] ++ (map_to_list mparams).*1)).
      intros Hlength_rest3.
      simpl in Hlength_rest3.
      set a' := (rclear_instrs (list_difference all_registers (map_to_list mparams).*1)).
      simpl. repeat f_equal. rewrite app_length /a rclear_length in Hlength_rest3.
      assert (length (list_difference all_registers [PC; r_t31; r1]) = 30) as Hregs.
      { assert ([PC;r_t31;r1] = [PC;r_t31]++[r1]) as ->;[auto|]. rewrite list_difference_app.
        rewrite stdpp_extra.list_difference_length;auto.
        apply NoDup_list_difference,all_registers_NoDup. apply NoDup_singleton.
        apply NoDup_submseteq. apply NoDup_singleton.
        intros ? ->%elem_of_list_singleton. apply elem_of_list_difference. split. apply all_registers_correct.
        repeat (apply not_elem_of_cons;split;auto);apply not_elem_of_nil. }
      assert (NoDup all_registers) as Hdup1.
      { apply all_registers_NoDup. }
      assert (NoDup [PC; r_t31; r1]) as Hdup2.
      { repeat (apply NoDup_cons; split; [repeat (apply not_elem_of_cons; split; [done|])|]).
        all: try apply not_elem_of_nil. by apply NoDup_nil. }
      assert (∀ x : RegName, x ∈ [PC; r_t31; r1] → x ∉ (map_to_list mparams).*1) as Hforall.
      { intros x Hin. intros Hcontr%map_to_list_fst. destruct Hdisj4 as [HPC [Hr_t31 Hr1] ].
        apply elem_of_cons in Hin as [-> | Hin]. apply HPC. apply elem_of_dom.
        destruct Hcontr as [? Hcontr]. apply elem_of_map_to_list in Hcontr. eauto.
        apply elem_of_cons in Hin as [-> | Hin]. apply Hr_t31. apply elem_of_dom.
        destruct Hcontr as [? Hcontr]. apply elem_of_map_to_list in Hcontr. eauto.
        apply elem_of_cons in Hin as [-> | Hin]. apply Hr1. apply elem_of_dom.
        destruct Hcontr as [? Hcontr]. apply elem_of_map_to_list in Hcontr. eauto. inversion Hin.  }
      assert (NoDup ([PC; r_t31; r1] ++ (map_to_list mparams).*1)) as Hdup3.
      { apply NoDup_app. split;[auto|].
        split;[|apply NoDup_map_to_list_fst;apply reg_eq_dec]. auto. }
      assert ([PC; r_t31; r1] ++ (map_to_list mparams).*1 ⊆+ all_registers) as Hsub.
      { apply all_registers_correct_sub;auto. }
      rewrite list_difference_length in Hlength_rest3;auto.
      assert ((map_to_list mparams).*1 ⊆+ all_registers) as Hsub'.
      { apply all_registers_correct_sub;auto. apply NoDup_map_to_list_fst, reg_eq_dec. }
      assert (strings.length (map_to_list mparams).*1 ≤ 30) as Hle.
      { assert ((map_to_list mparams).*1 ⊆+ list_difference all_registers [PC;r_t31;r1]).
        { apply submseteq_list_difference;[apply NoDup_map_to_list_fst, reg_eq_dec|auto..]. }
        apply submseteq_length in H as Hle. by rewrite Hregs in Hle. }
      apply eq_add_S in Hlength_rest3.
      rewrite Hlength_rest3 /a'.
      rewrite rclear_length. rewrite list_difference_length;auto.
      clear -Hle;simpl. lia.
      apply NoDup_map_to_list_fst, reg_eq_dec.
    }

    assert (exists a_end, f0 + ((offset_to_cont_call (map_to_list mparams).*1) - 1) = Some a_end)%a as [a_end Hlea'].
    { clear -Hlea. revert Hlea.
      rewrite /offset_to_cont_call. set (l := strings.length (rclear_instrs (list_difference all_registers (map_to_list mparams).*1))).
      intros Hlea. destruct (f0 + ((6 + l - 1)%nat - 1))%a eqn:Hsome; eauto. simpl in Hsome, Hlea. exfalso.
      clearbody l. solve_addr. }

    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 2|apply Hlea|..].
    { eapply isCorrectPC_range_perm_non_E;[apply Hvpc2|].
      apply contiguous_between_middle_bounds with (i:=0) (ai:=link3) in Hcont6 as [? ?];auto. }
    { eapply isCorrectPC_range_perm_non_IE;[apply Hvpc2|].
      apply contiguous_between_middle_bounds with (i:=0) (ai:=link3) in Hcont6 as [? ?];auto. }
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* destruct the buffer of the indirection *)
    destruct l;[|inversion Hlength_l].
    iDestruct (region_mapsto_cons with "Hbl'") as "[Ha1 Hbl']";[iContiguous_next Hcontbl' 0|iContiguous_le Hcontbl' 1|].
    assert (b_l'' + 1 = Some e_l')%a as Hllast;[eapply contiguous_between_last;[apply Hcontbl'|auto]|].
    apply finz_seq_between_singleton in Hllast as Heql. rewrite /region_mapsto Heql.
    iDestruct "Hbl'" as "[Ha2 _]".

    (* store r_t31 r_t1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t1 $Hr_t31 $Ha1]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 3|..]; auto.
    { apply Hwbbl'. constructor. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t31 & Ha1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t31 1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t31]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 4|iContiguous_next Hcontbl' 0|auto..].
    iEpilogue "(HPC & Hi & Hr_t31)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* store r_t31 r_t6 *)
    (* first we must get r_t6 *)
    rewrite (insert_commute _ _ r_t6)// -(insert_union_l _ _ r_t6) delete_insert_ne// !(insert_commute _ _ r_t6)//.
    iDestruct (big_sepM_delete with "Hgenlocalsparams") as "[Hr_t6 Hgenlocalsparams]";[apply lookup_insert|].
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t6 $Hr_t31 $Ha2]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 5|..]; auto.
    { apply Hwbbl'. repeat constructor. }
    iEpilogue "(HPC & Hi & Hr_t6 & Hr_t31 & Ha2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* lea r_t0 -6 *)
    assert (b_l'' + (-1) = Some b_l')%a as Hlea''.
    { apply contiguous_between_length_minus in Hcontbl'. clear -Hcontbl' Hllast. simpl in *. solve_addr. }
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t31]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 6|apply Hlea''|auto|auto|..].
    iEpilogue "(HPC & Hi & Hr_t31)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* restrict r_t0 IE *)
    destruct rest3 as [|? rest3].
    { exfalso. revert Hlength_rest3. rewrite Permutation_app_comm.
      assert (strings.length [f1; f2; f3; f4; f5; f6] = 6) as ->;[auto|].
      rewrite 5!cons_length.
      intros Hcontr.
      inversion Hcontr. }

    iPrologue "Hprog".
    iApply (wp_restrict_success_z with "[$HPC $Hi $Hr_t31]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 7|auto..].
    { rewrite decode_encode_perm_inv. auto. }
    rewrite decode_encode_perm_inv.
    iEpilogue "(HPC & Hi & Hr_t31)"; iCombine "Hi" "Hprog_done" as "Hprog_done".


    (* rclear all_registers \ { PC; r_t0; r1 } \ params *)

    (* rebuild register map *)
    (* we begin by clearning up the current register map *)
    iDestruct (big_sepM_insert with "[$Hgenlocalsparams $Hr_t6]") as "Hgenlocalsparams";[apply lookup_delete|rewrite insert_delete_insert insert_insert].
    rewrite - !insert_union_l delete_insert_delete - !delete_insert_ne//.
    iDestruct (big_sepM_insert with "[$Hgenlocalsparams $Hr_t1]") as "Hgenlocalsparams";[apply lookup_delete|rewrite insert_delete_insert].
    rewrite !(insert_commute _ _ r_t2)// insert_insert. rewrite !(insert_commute _ _ r_t3)// insert_insert.
    rewrite !(insert_commute _ _ r_t4)// insert_insert. rewrite !(insert_commute _ _ r_t5)// insert_insert.
    rewrite !insert_union_l.
    (* next we separate the params from the map, since we do not want to clear it *)
    iDestruct (big_sepM_union with "Hgenlocalsparams") as "[Hgen Hlocalsparams]".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap|]).
      apply map_disjoint_insert_l_2;[|apply map_disjoint_union_r_2];auto. apply lookup_union_None in Hnone as [? ?];auto. }
    iDestruct (big_sepM_union with "Hlocalsparams") as "[Hlocals Hparams]";[auto|].
    iDestruct (big_sepM_union with "[$Hgen $Hlocals]") as "Hgenlocals".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap|]).
      apply map_disjoint_insert_l_2;auto. do 2 (apply lookup_union_None in Hnone as [? Hnone]). auto. }
    repeat (rewrite (insert_commute _ _ r1);[|apply Hneregs;constructor]). rewrite -insert_union_l.
    iDestruct (big_sepM_delete with "Hgenlocals") as "[Hradv Hgenlocals]"; [apply lookup_insert|].
    rewrite delete_insert.
    2: { rewrite - !insert_union_l. repeat (rewrite lookup_insert_ne;[|apply Hneregs;constructor]).
         do 2 apply lookup_union_None in Hnone as [? Hnone]. apply lookup_union_None. split; auto. }

    (* prepare the program memory *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (rclear_prog rest4 link4) "(Hrclear & Hprog & #Hcont6)".
    { assert (link3 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: rest3 =
              (link3 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: [f6]) ++ (f7 :: rest3)) as Happ;auto.
      eapply contiguous_between_app with (k:=f7) in Happ as [? ?];[|apply Hcont6|apply contiguous_between_length in Hcont6 as Hlen];eauto.
      simpl.
      eapply contiguous_between_incr_addr;[apply Hcont6|]. auto. }
    iDestruct "Hcont6" as %(Hcont7 & Hcont8 & Heqapp4 & Hlink4).
    iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
    destruct rclear_prog.
    { exfalso. revert Hrclear_length. rewrite rclear_length (list_difference_cons _ _ r_t1).
      intros Hcontr;inversion Hcontr.
      apply all_registers_NoDup. apply all_registers_correct.
      apply not_elem_of_app. split.
      - repeat (apply not_elem_of_cons;split;[auto|]);[|apply not_elem_of_nil]. apply Hneregs. constructor.
      - intros Hcontr%map_to_list_fst. destruct Hcontr as [x Hx].
        apply elem_of_map_to_list in Hx. apply map_disjoint_Some_r with (m1:=rmap) in Hx;auto.
        apply not_elem_of_dom in Hx. apply Hx. apply Hsub. constructor.
    }
    apply contiguous_between_cons_inv_first in Hcont7 as Heq. subst f8.

    (* a useful assumption about the current register state to clear *)
    assert (dom rmap' =
            {[r_t5; r_t4; r_t3; r_t2; r_t1; r_t6]} ∪ (dom mlocals ∪ dom rmap' ∖ dom mlocals))
      as Hrmap'eq.
    { rewrite Hdom2. rewrite Hdom1 in Hsub. clear -Hsub Hdisj1 Hdisj5. rewrite -union_difference_L.
      assert ({[r_t1; r_t2; r_t3; r_t4; r_t5; r_t6]} ⊆ all_registers_s ∖ {[PC; r_t31; r1]} ∖ dom mparams) as Hsub'.
      { etrans;[eauto|]. apply subseteq_difference_l. auto. }
      apply subseteq_union_L in Hsub'.
      assert ({[r_t5; r_t4; r_t3; r_t2; r_t1; r_t6]} = {[r_t1; r_t2; r_t3; r_t4; r_t5; r_t6]}) as ->;[clear;set_solver|rewrite Hsub';auto].
      apply subseteq_difference_r. apply map_disjoint_dom;auto.
      apply subseteq_difference_r;[|apply all_registers_subseteq].
      apply elem_of_disjoint. intros x Hin Heq. destruct Hdisj5 as [? [? ?] ].
      repeat (apply elem_of_union in Heq as [Heq | Heq];[try apply elem_of_singleton_1 in Heq|apply elem_of_singleton_1 in Heq];subst;try done).
    }

    (* rclear *)
    set instrs := (list_difference all_registers ([PC; r_t31; r1] ++ (map_to_list mparams).*1)).
    iApply (rclear_spec _ instrs with "[-]");[apply Hcont7|..];last (iFrame "Hgenlocals HPC").

    { apply not_elem_of_list. constructor. }
    { auto. }
    { eapply isCorrectPC_range_restrict;[apply Hvpc|].
      apply contiguous_between_bounds in Hcont8. split;auto.
      apply contiguous_between_middle_bounds with (i:=8) (ai:=f7) in Hcont6 as [Hle _];[|auto].
      apply contiguous_between_bounds in Hcont5. apply contiguous_between_bounds in Hcont3.
      apply contiguous_between_middle_bounds with (i:=1) (ai:=f) in Hcont4 as [Hle'' _];[|auto].
      clear -Hlink1 Hcont8 Hle Hle'' Hcont5 Hcont3. solve_addr. }
    { rewrite list_to_set_difference list_to_set_app_L.
      assert (list_to_set [PC; r_t31; r1] = {[PC;r_t31;r1]}) as ->;[simpl;clear;set_solver|].
      rewrite -/all_registers_s. rewrite -difference_difference_l_L.
      rewrite - !insert_union_l !dom_insert_L. rewrite !union_assoc_L dom_union_L (union_comm_L (dom rmap)) Hdom1.
      assert (list_to_set (map_to_list mparams).*1 = dom mparams) as ->;[apply list_to_set_map_to_list|].
      rewrite -Hdom2. apply Hrmap'eq.
    }

    iSplitL "Hrclear". iNext. rewrite /rclear. iExact "Hrclear".
    iNext. iIntros "(HPC & Hgenlocals & Hrclear)".
    (* prepare for the last instruction *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest4.
    destruct rest4;[inversion Hlength_rest4|]. destruct rest4;[|inversion Hlength_rest4].
    apply contiguous_between_cons_inv_first in Hcont8 as Heq. subst f8.
    assert (isCorrectPC_range p b e link4 a_last) as Hvpc3.
    { eapply isCorrectPC_range_restrict;[apply Hvpc|]. split;[|clear;solve_addr].
      apply contiguous_between_bounds in Hcont1.
      apply contiguous_between_bounds in Hcont3.
      assert (link2 + 1 = Some f)%a as Hnext;[iContiguous_next Hcont4 0|].
      apply contiguous_between_bounds in Hcont5. apply contiguous_between_bounds in Hcont7.
      apply contiguous_between_middle_bounds with (i:=8) (ai:=f7) in Hcont6 as [Hle _];[|auto].
      clear -Hcont3 Hcont5 Hnext Hcont1 Hlink2 Hle Hcont7. solve_addr. }

    (* continuation *)
    iApply "Hcont".
    iExists b_l',e_l',b_l,e_l,a_end.
    assert (Hlast: link4 = (a_last ^+ (- 1))%a).
    {
      clear - Hcont8.
      eapply contiguous_between_cons_inv in Hcont8.
      destruct Hcont8 as (_ & a' & Ha' & Hcont8).
      inversion Hcont8 ; subst. solve_addr.
    }
    assert (Haend: a_end = (a_last ^+ (- 1))%a).
    {
      clear - Hlea Hlea'.
      solve_addr.
    }
    subst link4.
    subst a_end.
    iSplitR.
    { iPureIntro. revert Hlea Hlea'. clear.
      rewrite /offset_to_cont_call. set (l := strings.length (rclear_instrs (list_difference all_registers (map_to_list mparams).*1))).
      generalize l. clear. solve_addr. }
    iSplitR.
    { iPureIntro.
      clear -Hllast Hlea''. solve_addr.
    }
    iFrame "HPC Hparams Hradv Hr_t31 Hbl Hb Ha_entry Hna".
    iSplitL "Hgenlocals".
    { rewrite !big_sepM_dom. iApply (big_sepS_subseteq with "Hgenlocals").
      rewrite - !insert_union_l !dom_insert_L !union_assoc_L dom_union_L (union_comm_L (dom rmap)) Hdom1.
      rewrite -Hdom2. rewrite Hrmap'eq. clear. set_solver. }
    iSplitL "Ha1 Ha2".
    { apply region_addrs_of_contiguous_between in Hcontbl' as <-. iFrame. done. }
    rewrite Heqapp1 Heqapp2 Heqapp3 Heqapp4.
    rewrite /call.
    iDestruct "Hprog_done" as "(?&?&?&?&?&?&?&?&malloc&?&locals&malloc')".
    iApply (big_sepL2_app with "malloc'").
    iApply (big_sepL2_app with "locals").
    iFrame.
  Qed.

  (* TODO specification after the jmp ? maybe not necessary *)


  (* Helpful lemmas to split the program *)
  Definition call_instrs_main f_m offset_to_cont r1 (locals params : list RegName) :=
    (* allocate and store locals *)
    malloc_instrs f_m (strings.length locals) ++
    store_locals_instrs r_t1 locals ++
    (* allocate the space for the indirection of the IE-cap *)
    [move_r r_t6 r_t1] ++
    malloc_instrs f_m 2 ++

    (* prepare and store continuation *)
    [move_r r_t31 r_t1;
    move_r r_t1 PC;

    lea_z r_t1 offset_to_cont;
    store_r r_t31 r_t1;
    lea_z r_t31 1;
    (* store locals cap *)
    store_r r_t31 r_t6;
    (* setup return capability *)
    lea_z r_t31 (-1);
    restrict_z r_t31 ie] ++
    (* clear all registers except params, PC, r_t31 and r1 *)
    rclear_instrs (list_difference all_registers ([PC;r_t31;r1]++params)).

  Lemma call_instrs_main_jmp f_m offset_to_cont r1 (locals params : list RegName)
    : call_instrs f_m offset_to_cont r1 locals params =
         call_instrs_main f_m offset_to_cont r1 locals params ++ [jmp r1].
  Proof.
    rewrite /call_instrs_main /call_instrs.
    by rewrite -!app_assoc !app_inv_head_iff.
  Qed.

  Lemma call_main' al f_m r1 locals params :
    length al = length (call_instrs f_m (offset_to_cont_call params) r1 locals params) ->
    (call al f_m r1 locals params ⊢
    ∃ a' al',
         ⌜ al = al' ++ [a']⌝ ∧
         [∗ list] a_i;w ∈ (al' ++ [a']);(call_instrs_main f_m (offset_to_cont_call params) r1 locals params ++ [jmp r1]), a_i ↦ₐ w)%I.
  Proof.
    iIntros (Hlen) "Hcall".
    rewrite /call.
    rewrite call_instrs_main_jmp.
    rewrite call_instrs_main_jmp in Hlen.
    rewrite app_length in Hlen.
    assert (exists a_end, last al = Some a_end) as [a_end Ha_end].
    { apply last_is_Some. intro. subst al.
      rewrite cons_length nil_length in Hlen; lia. }
    iExists a_end, (removelast al).
    assert (Hal : al = removelast al ++ [a_end]).
    apply last_Some in Ha_end.
    destruct Ha_end as [l' ->].
    by rewrite removelast_last.
    rewrite {1}Hal.
    iFrame. auto.
  Qed.

  Lemma call_main al f_m r1 locals params :
    length al = length (call_instrs f_m (offset_to_cont_call params) r1 locals params) ->
    (call al f_m r1 locals params ⊢
    ∃ a' al',
         ⌜ al = al' ++ [a']⌝
                  ∗ a' ↦ₐ jmp r1
                  ∗ [∗ list] a_i;w ∈ al';(call_instrs_main f_m (offset_to_cont_call params) r1 locals params), a_i ↦ₐ w
    )%I.
  Proof.
    iIntros (Hlen) "Hcall".
    iDestruct (call_main' with "Hcall") as (a_end_call call_addrs') "[-> Hcall]"; auto.
    iExists a_end_call, call_addrs'.
    iDestruct (big_sepL2_app' with "Hcall") as "[Hcall' Hi]".
    rewrite call_instrs_main_jmp in Hlen.
    rewrite 2!app_length in Hlen.
    rewrite 2!cons_length 2!nil_length in Hlen; lia.
    iSplit; first eauto.
    iDestruct (big_sepL2_cons with "Hi") as "[Hi _]".
    iFrame.
  Qed.


  (* TODO use the call_main instead of re-doing the whole proof *)
  Lemma call_main_end al f_m r1 locals params a_call a_end_call a_restore :
    (a_end_call + 1)%a = Some a_restore ->
    contiguous_between al a_call a_restore ->
    (a_call + length al)%a = Some a_restore ->

    length al = length (call_instrs f_m (offset_to_cont_call params) r1 locals params) ->
    (call al f_m r1 locals params ⊢
       ∃ al',
         ⌜ al = al' ++ [a_end_call]⌝
                  ∗ a_end_call ↦ₐ jmp r1
                  ∗ [∗ list] a_i;w ∈ al';(call_instrs_main f_m (offset_to_cont_call params) r1 locals params), a_i ↦ₐ w
    )%I.
  Proof.
    iIntros (Hnext Hcont_call Ha_restore Hlen) "Hcall".
    iDestruct (call_main' with "Hcall") as (a_end_call' call_addrs') "[-> Hcall]"; auto.
    iExists call_addrs'.

    assert (a_end_call' = a_end_call) as ->.
    { clear -Hcont_call Hnext Ha_restore.
      eapply (contiguous_between_app _ call_addrs' [a_end_call'] _ _ a_end_call) in Hcont_call.
      destruct Hcont_call as [Hcall_main Hcall_jmp].
      by apply contiguous_between_cons_inv_first in Hcall_jmp.
      auto.
      rewrite -Hnext in Ha_restore.
      rewrite app_length cons_length nil_length in Ha_restore.
      solve_addr.
    }

    iDestruct (big_sepL2_app' with "Hcall") as "[Hcall' Hi]".
    rewrite call_instrs_main_jmp in Hlen.
    rewrite 2!app_length in Hlen.
    rewrite 2!cons_length 2!nil_length in Hlen; lia.

    iSplit; first eauto.
    iDestruct (big_sepL2_cons with "Hi") as "[Hi _]".
    iFrame.
  Qed.

End call.
