From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel macros_helpers macros rules proofmode.
From stdpp Require Import list.

Section call.
  Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
          `{LK: static_spinlock.lockG Σ, MP: MachineParameters}.


  (* Macro for a heap based calling convention *)

  (*
     The calling convention performs the following steps:

     1. It allocates heap space to store the activation record, the current r_env and the continuation
     2. It creates a copy of the PC and moves it to point to the continuing instruction
     3. It stores the activation record, r_env, and continuation
     4. It restricts the allocated capability to be an E capability (a closure)
     5. It clears all registers except r1, rt_0 and the parameters
   *)

  Definition hw_1 := encodeInstr (Mov r_t1 (inr PC)).
  Definition hw_2 := encodeInstr (Lea r_t1 (inl 5%Z)).
  Definition hw_3 := encodeInstr (Load r_t2 r_t1).
  Definition hw_4 := encodeInstr (Lea r_t1 (inl 1%Z)).
  Definition hw_5 := encodeInstr (Load PC r_t1).

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


  Lemma store_locals_spec_middle (i : CoreN)
        (* cont *) φ
        (* list of locals *) r1 locals mlocals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l a_l
    EN:
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    finz.dist a_l e_l = strings.length locals →
    strings.length locals > 0 →
    writeAllowed p_l = true → withinBounds b_l e_l a_l = true ->
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length locals = length wsr ->

    (▷ store_locals a r1 locals
   ∗ ▷ (i,PC) ↦ᵣ WCap p b e a_first
   ∗ ▷ (i,r1) ↦ᵣ WCap p_l b_l e_l a_l
   ∗ ▷ ([∗ map] r↦w ∈ mlocals, (i,r) ↦ᵣ w)
   ∗ ▷ (∃ ws, [[a_l,e_l]]↦ₐ[[ws]])
   ∗ ▷ ((i,PC) ↦ᵣ WCap p b e a_last
           ∗ (i,r1) ↦ᵣ WCap p_l b_l e_l e_l
           ∗ ([∗ map] r↦w ∈ mlocals, (i,r) ↦ᵣ w)
           ∗ [[a_l,e_l]]↦ₐ[[wsr]]
           ∗ store_locals a r1 locals
           -∗ WP (i, Seq (Instr Executable)) @EN {{ φ }})
   ⊢ WP (i, Seq (Instr Executable)) @EN {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hsize Hnz Hwa Hwb Hperm Hlength) "(>Hprog & >HPC& >Hr_t1& >Hlocals& >Hbl& Hcont)".
    iInduction (locals) as [|r locals] "IH" forall (a_l mlocals wsr a a_first Hvpc Hcont Hnz Hsize Hwb Hperm Hlength).
    { cbn in Hperm. apply Permutation_nil_l in Hperm. inversion Hnz. }
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
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hlast|apply Hnext|destruct p_l;auto;inversion Hwa|].
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
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 1|apply Ha_l'|destruct p_l;auto;inversion Hwa|].
      iEpilogue "(HPC & Hi & Hr_t1)".
      iApply ("IH" $! a_l' (delete r mlocals) (w0 :: wsr) with "[] [] [] [] [] [] [] Hprog HPC Hr_t1 Hlocals [Hbl]").
      + iPureIntro. eapply isCorrectPC_range_restrict;[eauto|].
        assert (a_first + 1 = Some f0)%a;[iContiguous_next Hcont 0|].
        assert (f0 + 1 = Some f)%a;[iContiguous_next Hcont 1|].
        split;[revert H H0;clear|clear];try solve_addr.
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


  Lemma store_locals_spec i
        (* cont *) φ
        (* list of locals *) r1 mlocals locals wsr
        (* PC *) a p b e a_first a_last
        (* capability for locals *) p_l b_l e_l
    EN :
    isCorrectPC_range p b e a_first a_last →
    contiguous_between a a_first a_last →
    finz.dist b_l e_l = strings.length locals →
    strings.length locals > 0 → (* we assume the length of locals is non zero, or we would not be able to take a step before invoking continuation *)
    writeAllowed p_l = true →
    zip locals wsr ≡ₚ(map_to_list mlocals) →
    length locals = length wsr ->

    (▷ store_locals a r1 locals
   ∗ ▷ (i,PC) ↦ᵣ WCap p b e a_first
   ∗ ▷ (i,r1) ↦ᵣ WCap p_l b_l e_l b_l
   ∗ ▷ ([∗ map] r↦w ∈ mlocals, (i, r) ↦ᵣ w)
   ∗ ▷ (∃ ws, [[b_l,e_l]]↦ₐ[[ws]])
   ∗ ▷ ((i,PC) ↦ᵣ WCap p b e a_last
           ∗ (i,r1) ↦ᵣ WCap p_l b_l e_l e_l
           ∗ ([∗ map] r↦w ∈ mlocals, (i, r) ↦ᵣ w)
           ∗ [[b_l,e_l]]↦ₐ[[wsr]]
           ∗ store_locals a r1 locals
           -∗ WP (i, Seq (Instr Executable)) @EN {{ φ }})

   ⊢ WP (i, Seq (Instr Executable)) @EN {{ φ }})%I.
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
    (* allocate the space for the activation record *)
    [move_r r_t10 r_t1] ++
    malloc_instrs f_m 7 ++
    (* store the activation code *)
    [move_r r_t0 r_t1;
    store_z r_t0 hw_1;
    lea_z r_t0 1;
    store_z r_t0 hw_2;
    lea_z r_t0 1;
    store_z r_t0 hw_3;
    lea_z r_t0 1;
    store_z r_t0 hw_4;
    lea_z r_t0 1;
    store_z r_t0 hw_5;
    lea_z r_t0 1;
    (* store locals cap *)
    store_r r_t0 r_t10;
    lea_z r_t0 1;
    (* prepare and store continuation *)
    move_r r_t1 PC;
    lea_z r_t1 (offset_to_cont - 1);
    store_r r_t0 r_t1;
    (* setup return capability *)
    lea_z r_t0 (-6);
    restrict_z r_t0 e] ++
    (* clear all registers except params, PC, r_t0 and r1 *)
    rclear_instrs (list_difference all_registers ([PC;r_t0;r1]++params)) ++
    (* jmp to r1 *)
    [jmp r1].

  Definition offset_to_cont_call params :=
    6 + (strings.length (rclear_instrs (list_difference all_registers params))) - 3.

  Definition call a f_m r1 locals params :=
    ([∗ list] a_i;w ∈ a;(call_instrs f_m (offset_to_cont_call params) r1 locals params), a_i ↦ₐ w)%I.

  Lemma rclear_length l :
    length (rclear_instrs l) = length l.
  Proof.
    induction l;auto.
    simpl. auto.
  Qed.


Definition registers_s_core (i:CoreN) (regs : gset RegName) : gset (CoreN * RegName)
  := set_map (fun r => (i,r)) regs.

(* Requires newer version of stdpp *)
Program Definition registers_map_core `{A : Type} (i:CoreN) (regs : gmap RegName A)
  : gmap (CoreN * RegName) A := kmap (fun r => (i,r)) regs.

Lemma big_sepM_register_map_core (i : CoreN) (l : gmap RegName Word) :
  ([∗ map] k↦y ∈ (registers_map_core i l), k ↦ᵣ y)
  ⊣⊢ ([∗ map] k↦y ∈ l, (i, k) ↦ᵣ y).
Proof.
  iSplit ; iIntros "H".
  - unfold registers_map_core.
    iInduction l as [|l'] "IH" using map_ind.
    + by rewrite kmap_empty.
    + rewrite kmap_insert.
      do 2 rewrite big_sepM_insert_delete.
      iDestruct "H" as "[? H]"; iFrame.
      rewrite delete_notin; last by rewrite lookup_kmap.
      rewrite delete_notin; auto.
      by iApply "IH".
  - unfold registers_map_core.
    iInduction l as [|l'] "IH" using map_ind.
    + by rewrite kmap_empty.
    + rewrite kmap_insert.
      do 2 rewrite big_sepM_insert_delete.
      iDestruct "H" as "[? H]"; iFrame.
      rewrite delete_notin; auto.
      rewrite delete_notin; last by rewrite lookup_kmap.
      by iApply "IH".
Qed.

Instance registers_map_core_inj {i : CoreN} : Inj eq eq (λ r : RegName, (i, r)).
Proof.
  repeat intro.
  by inversion H.
Defined.
Hint Resolve registers_map_core_inj : core.

Lemma registers_map_core_union (i : CoreN) (m1 m2 : gmap RegName Word) :
  registers_map_core i (m1 ∪ m2) =
    registers_map_core i m1 ∪ registers_map_core i m2.
Proof.
  unfold registers_map_core.
  apply kmap_union;auto.
Qed.


Lemma call_spec (i : CoreN)
  (* call *) (r1 : RegName) (mlocals mparams : gmap RegName Word) (wadv : Word)
  (* remaining registers *) (rmap rmap' : gmap (CoreN*RegName) Word)
  (* pc *) a p b e a_first a_last
  (* malloc *) f_m b_m e_m mallocN EN γ
  (* linking *) b_link a_link e_link a_entry
  (* cont *) φ :
  isCorrectPC_range p b e a_first a_last →
  contiguous_between a a_first a_last →
  withinBounds b_link e_link a_entry = true →
  (a_link + f_m)%a = Some a_entry →
  strings.length (map_to_list mlocals).*1 > 0 →

    dom rmap = ((all_registers_s_core i)
                  ∖ registers_s_core i {[ PC; r_t0; r1 ]}
                  ∖ registers_s_core i (dom mparams)
                  ∖ registers_s_core i (dom mlocals)) →
    dom rmap' = ((all_registers_s_core i)
                   ∖ registers_s_core i {[ PC; r_t0; r1 ]}
                   ∖ registers_s_core i (dom mparams)) →
    registers_s_core i {[r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9 ; r_t10]} ⊆
      dom rmap → (* we need to know that neither params nor locals use these gen pur registers *)
    ↑mallocN ⊆ EN →

    (▷ call a f_m r1 (map_to_list mlocals).*1 (map_to_list mparams).*1
    ∗ inv mallocN (malloc_inv b_m e_m γ)
    ∗ ▷ (i,PC) ↦ᵣ WCap p b e a_first
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* registers *)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ mparams, (i, r_i) ↦ᵣ w_i)
    ∗ ▷ (∃ w, (i,r_t0) ↦ᵣ w)
    ∗ ▷ (i,r1) ↦ᵣ wadv
    ∗ ▷ ([∗ map] r_i↦w_i ∈ mlocals, (i, r_i) ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ ((∃ b_c e_c b_l e_l a_end, ⌜(a_end + 1)%a = Some a_last⌝
            ∗ (i,PC) ↦ᵣ updatePcPerm wadv
            ∗ ([∗ map] r_i↦_ ∈ rmap', r_i ↦ᵣ WInt 0%Z)
            ∗ ([∗ map] r_i↦w_i ∈ mparams, (i, r_i) ↦ᵣ w_i)
            ∗ b ↦ₐ WCap RO b_link e_link a_link
            ∗ a_entry ↦ₐ WCap E b_m e_m b_m
            ∗ (i,r1) ↦ᵣ wadv
            ∗ (i, r_t0) ↦ᵣ WCap E b_c e_c b_c
            ∗ [[b_c,e_c]]↦ₐ[[ [WInt hw_1;WInt hw_2;WInt hw_3;WInt hw_4;WInt hw_5;WCap RWX b_l e_l e_l;WCap p b e a_end] ]]
            ∗ [[b_l,e_l]]↦ₐ[[ (map_to_list mlocals).*2 ]]
            ∗ call a f_m r1 (map_to_list mlocals).*1 (map_to_list mparams).*1
            -∗ WP (i, Seq (Instr Executable)) @EN {{ λ v, φ v }}))
    ⊢ WP (i, Seq (Instr Executable)) @EN {{ λ v, φ v ∨ ⌜v = (i, FailedV)⌝ }})%I.
  Proof.
    iIntros (Hvpc Hcont Hwb Hlink Hnz Hdom1 Hdom2 Hsub Hnainv)
            "(>Hprog & #Hinv & >HPC & >Hb & >Ha_entry & >Hgen & >Hparams & >Hr_t0 & >Hr1 & >Hlocals & Hcont)".
    (* prepare the registers *)
    iDestruct "Hr_t0" as (w) "Hr_t0".
    iAssert (⌜mparams ##ₘmlocals⌝)%I as %Hdisj1.
    { rewrite map_disjoint_spec. iIntros (j x y Hx Hy).
      iDestruct (big_sepM_delete _ _ j with "Hparams") as "[Hi1 Hparams]";[eauto|].
      iDestruct (big_sepM_delete _ _ j with "Hlocals") as "[Hi2 Hlocals]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    assert (Hdisj1': registers_map_core i mlocals ##ₘ registers_map_core i mparams).
    { apply map_disjoint_kmap; auto. }

    iAssert (⌜ registers_map_core i mparams ##ₘrmap⌝)%I as %Hdisj2.
    { rewrite map_disjoint_spec. iIntros (j x y Hx Hy).
      iDestruct (big_sepM_delete _ _ j with "Hgen") as "[Hi2 Hgen]";[eauto|].
      unfold registers_map_core in Hx.
      rewrite lookup_kmap_Some in Hx.
      destruct Hx as (k' & -> & Hx).
      iDestruct (big_sepM_delete _ _ k' with "Hparams") as "[Hi1 Hparams]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    iAssert (⌜registers_map_core i mlocals ##ₘrmap⌝)%I as %Hdisj3.
    { rewrite map_disjoint_spec.
      iIntros (k x y Hx Hy).
      iDestruct (big_sepM_delete _ _ k with "Hgen") as "[Hi1 Hgen]";[eauto|].
      unfold registers_map_core in Hx.
      rewrite lookup_kmap_Some in Hx.
      destruct Hx as (k' & -> & Hx).
      iDestruct (big_sepM_delete _ _ k' with "Hlocals") as "[Hi2 Hlocals]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hi2") as "Hfalse". done. }
    iAssert (⌜PC ∉ dom mparams ∧ r_t0 ∉ dom mparams ∧ r1 ∉ dom mparams⌝)%I as %Hdisj4.
    { repeat iSplit; iIntros (Hcontr); apply elem_of_gmap_dom in Hcontr as [? Hi];
        (iDestruct (big_sepM_delete with "Hparams") as "[Hi1 Hparams]";[by eauto|]).
      by iDestruct (regname_dupl_false with "Hi1 HPC") as "Hfalse".
      by iDestruct (regname_dupl_false with "Hi1 Hr_t0") as "Hfalse".
      by iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse".
    }
    iAssert (⌜PC ∉ dom mlocals ∧ r_t0 ∉ dom mlocals ∧ r1 ∉ dom mlocals⌝)%I as %Hdisj5.
    { repeat iSplit; iIntros (Hcontr); apply elem_of_gmap_dom in Hcontr as [? Hi];
        (iDestruct (big_sepM_delete with "Hlocals") as "[Hi1 Hlocals]";[by eauto|]).
      by iDestruct (regname_dupl_false with "Hi1 HPC") as "Hfalse".
      by iDestruct (regname_dupl_false with "Hi1 Hr_t0") as "Hfalse".
      by iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse".
    }
    iAssert (⌜∀ r, (i,r) ∈ registers_s_core i {[r_t1; r_t2; r_t3; r_t4; r_t5
                                                ; r_t6; r_t7; r_t8; r_t9; r_t10]} → (i,r) ≠ (i,r1)⌝)%I as %Hneregs.
    { iIntros (r Hin Hcontr). subst. apply Hsub in Hin.
      apply elem_of_gmap_dom in Hin as [x Hx].
      iDestruct (big_sepM_delete with "Hgen") as "[Hr Hgen]";[apply Hx|].
      inversion Hcontr ; subst.
      by iDestruct (regname_dupl_false with "Hr Hr1") as "Hfalse".
    }

    iDestruct (big_sepM_union with "[$Hlocals $Hparams]") as "Hlocalsparams"
    ;[auto|].

    iAssert ([∗ map] k↦y ∈ (registers_map_core i (mlocals ∪ mparams)), k ↦ᵣ y)%I
    with "[Hlocalsparams]" as "Hlocalsparams".
    { rewrite big_sepM_register_map_core; iFrame. }

    iDestruct (big_sepM_union with "[$Hgen $Hlocalsparams]") as
      "Hgenlocalsparams".
    { rewrite registers_map_core_union.
      apply map_disjoint_union_r_2; auto. }

    set (rmap_full :=  (rmap ∪ registers_map_core i (mlocals ∪ mparams))).
    iAssert (⌜rmap_full !! (i, r1) = None⌝)%I
      as %Hnone.
    { destruct (rmap_full !! (i, r1)) eqn:Hsome ; last auto.
      iDestruct (big_sepM_delete _ _ (i, r1) with "Hgenlocalsparams") as "[Hi1 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hr1") as "Hfalse". done. }
    iAssert (⌜rmap_full !! (i, r_t0) = None⌝)%I as %Hnone'.
    { destruct (rmap_full !! (i, r_t0)) eqn:Hsome ; last auto.
      iDestruct (big_sepM_delete _ _ (i, r_t0) with "Hgenlocalsparams") as "[Hi1 Hgen]";[eauto|].
      iDestruct (regname_dupl_false with "Hi1 Hr_t0") as "Hfalse". done. }
    iAssert (⌜r1 ≠ PC⌝)%I as %Hne1.
    { iIntros (->). iDestruct (regname_dupl_false with "HPC Hr1") as "Hfalse". done. }
    iAssert (⌜r1 ≠ r_t0⌝)%I as %Hne2.
    { iIntros (->). iDestruct (regname_dupl_false with "Hr_t0 Hr1") as "Hfalse". done. }
    iDestruct (big_sepM_insert with "[$Hgenlocalsparams $Hr1]") as
      "Hgenlocalsparams";[eauto|].

    assert (dom
              (<[(i, r1):=wadv]> rmap_full)
            = all_registers_s_core i ∖ {[(i, PC); (i, r_t0)]}) as Hdomeq.
    { rewrite dom_insert_L !dom_union_L.
      revert Hdom1 Hne1 Hne2 Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5.
      clear.
      intros Hdom1 Hne1 Hne2 Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5.
      assert (all_registers_s_core i ∖ {[(i, PC); (i, r_t0)]}
              = {[(i, r1)]} ∪ all_registers_s_core i ∖
                  {[(i, PC); (i, r_t0); (i, r1)]}) as ->.
      { rewrite - !difference_difference_L.
        rewrite -union_difference_L; auto.
        rewrite /all_registers_s_core.
        replace {[(i, r1)]} with (@set_map _ _ _ _
                                    (@gset (@CoreN CP * RegName)
                                       (@prod_eq_dec (@CoreN CP) (@finz_eq_dec (@coreNum CP)) RegName reg_eq_dec)
                                       (@prod_countable (@CoreN CP) (@finz_eq_dec (@coreNum CP)) (@finz_countable (@coreNum CP))
                                          RegName reg_eq_dec reg_countable))
                                    _ _ _
                                    (λ r : RegName, (i, r))
                                    (@singleton RegName (@gset RegName reg_eq_dec reg_countable)
                                       (@gset_singleton RegName reg_eq_dec
                                          reg_countable) r1)) by set_solver +.
        clear -Hne1 Hne2.
        set_solver.
      }
      assert ( (dom rmap ∪ dom (registers_map_core i (mlocals ∪ mparams))) =
                 all_registers_s_core i ∖ {[(i, PC); (i, r_t0); (i, r1)]}) as ->.
     { assert ( dom rmap ∪ dom (registers_map_core i (mlocals ∪ mparams)) =
                  dom (registers_map_core i (mlocals ∪ mparams)) ∪ dom rmap) as ->.
       set_solver +.
       rewrite registers_map_core_union.
       rewrite dom_union_L.
       rewrite !dom_kmap_L.
       rewrite Hdom1.
       assert ( all_registers_s_core i ∖ registers_s_core i {[PC; r_t0; r1]}
                = all_registers_s_core i ∖ {[(i, PC); (i, r_t0); (i, r1)]}) as ->.
       { set_solver +. }
       unfold all_registers_s_core.
       unfold registers_s_core.
       set ( mmlocals := set_map (λ r : RegName, (i, r)) (dom mlocals)).
       set ( mmparams := set_map (λ r : RegName, (i, r)) (dom mparams)).
       set (base := set_map (λ r : RegName, (i, r)) all_registers_s ∖ {[(i, PC); (i, r_t0); (i, r1)]}).
       rewrite difference_difference_L.
       rewrite (union_comm_L mmlocals).
       set (garbage := (mmparams ∪ mmlocals)).
       rewrite -(union_difference_L _ base); auto.
       subst garbage.
       apply union_subseteq.
       subst mmparams mmlocals base.
       split; [clear -Hdisj4 | clear -Hdisj5]; set_solver. }
     reflexivity. }
    (* malloc f_m |locals| *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog rest1 link1) "(Hmalloc_prog & Hprog & #Hcont1)";[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont1 & Hcont2 & Heqapp1 & Hlink1).
    rewrite -/(malloc _ _ _).
    iApply (wp_wand_l (Λ := cap_lang) _ _ _ (λ v , ((φ v ∨ ⌜v = (i, FailedV)⌝) ∨ ⌜v = (i, FailedV)⌝)))%I.
    iSplitR.
    { iIntros (v) "[H|H] /=";auto. }
    iApply (malloc_spec with "[- $HPC $Hinv $Hb $Ha_entry $Hmalloc_prog $Hr_t0 $Hgenlocalsparams]");auto;[|apply Hcont1|..].
    { eapply isCorrectPC_range_restrict;eauto. split;[clear;solve_addr|]. apply
        contiguous_between_bounds in Hcont2. auto. }
    eauto.
    iNext. iIntros "(HPC & Hmalloc & Hb & Ha_entry & Hregion & Hr_t0 & Hgenlocalsparams)".
    iDestruct "Hregion" as (b_l e_l Hlocals_size) "(Hr_t1 & Hbl)".
    (* TODO move*)
    Ltac disjoint_from_rmap rmap i :=
      match goal with
      | Hsub : _ ⊆ dom rmap |- _ !! ?r = _ =>
          assert (is_Some (rmap !! r)) as [x Hx]
          ;[apply elem_of_gmap_dom;apply Hsub;set_solver+|];
      apply map_disjoint_Some_l with rmap x;auto;rewrite registers_map_core_union; apply map_disjoint_union_r_2;auto
      end.

    (* in order to store the locals, we need to extract locals from the map *)
    rewrite delete_insert_ne. 2: { apply Hneregs. rewrite /registers_s_core. set_solver+. }
    rewrite delete_union. rewrite !insert_union_l.
    rewrite (delete_notin (registers_map_core i (mlocals ∪ mparams)));
    [|disjoint_from_rmap rmap i].
    iDestruct (big_sepM_union with "Hgenlocalsparams") as "[Hgen Hlocalsparams]".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap i|]).
      apply map_disjoint_insert_l_2. rewrite registers_map_core_union.
      subst rmap_full.
      rewrite registers_map_core_union in Hnone.
      epose proof (lookup_union_None rmap) ; apply H in Hnone as [? ?];auto.
      apply map_disjoint_delete_l.
      rewrite registers_map_core_union; apply map_disjoint_union_r_2;auto. }
    rewrite registers_map_core_union.
    iDestruct (big_sepM_union with "Hlocalsparams") as "[Hlocals Hparams]";auto.

    (* store locals *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (storelocals_prog rest2 link2) "(Hstorelocals_prog & Hprog & #Hcont2)";[apply Hcont2|].
    iDestruct "Hcont2" as %(Hcont3 & Hcont4 & Heqapp2 & Hlink2).
    iAssert ([∗ map] k↦y ∈ mlocals, (i,k) ↦ᵣ y)%I with "[Hlocals]" as
      "Hlocals" ; [by rewrite big_sepM_register_map_core|].
    iApply (store_locals_spec _ _ _ _ ((map_to_list mlocals).*1) with "[-$HPC $Hstorelocals_prog $Hr_t1 $Hlocals]");[|apply Hcont3|auto..].
    { eapply isCorrectPC_range_restrict;[apply Hvpc|].
      apply contiguous_between_bounds in Hcont1.
      apply contiguous_between_bounds in Hcont4. auto. }
    { clear - Hlocals_size.
      rewrite /finz.dist. solve_addr. }
    { Unshelve. 2: exact (map_to_list mlocals).*2.
      rewrite zip_fst_snd. auto. }
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
    assert (is_Some (rmap !! (i, r_t10))) as [w10 Hw10]
    ;[apply elem_of_gmap_dom;apply Hsub;rewrite /registers_s_core;set_solver+|].
    iDestruct (big_sepM_delete _ _ (i, r_t10) with "Hgen") as "[Hr_t10 Hgen]".
    { assert ((i, r_t10) ≠ (i, r1)) as Hne
      ;[apply Hneregs;rewrite /registers_s_core;set_solver+|].
      rewrite !lookup_insert_ne;auto. rewrite lookup_delete_ne;auto. eauto. }

    (* move r_t6 r_t1 *)
    destruct rest2 as [|? rest2];[inversion Hlength_prog|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t10 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link2 a_last|iContiguous_next Hcont4 0|].
    iEpilogue "(HPC & Hi & Hr_t10 & Hr_t1)". iCombine "Hstorelocals_prog Hmalloc" as "Hprog_done".
    iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* malloc 7 *)
    (* prepare the registers *)
    iDestruct (big_sepM_insert with "[$Hgen $Hr_t10]") as "Hgen";[apply lookup_delete|rewrite insert_delete_insert].
    rewrite -delete_insert_ne;[|apply Hneregs;rewrite /registers_s_core ;set_solver+].
    rewrite - !delete_insert_ne;auto.
    iDestruct (big_sepM_insert with "[$Hgen $Hr_t1]") as "Hgen"
    ; [apply lookup_delete|rewrite insert_delete_insert].
    iAssert ([∗ map] k↦y ∈ (registers_map_core i (mlocals ∪ mparams)), k ↦ᵣ y)%I
    with "[Hmlocals Hparams]" as "Hlocalsparams".
    { rewrite registers_map_core_union.
      rewrite <- big_sepM_register_map_core.
      iApply big_sepM_union;auto.
      iFrame. }
    (* iDestruct (big_sepM_union with "[$Hmlocals $Hparams]") as "Hlocalsparams";[auto|]. *)
    iDestruct (big_sepM_union with "[$Hgen $Hlocalsparams]") as "Hgenlocalsparams".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap i|]).
      apply map_disjoint_insert_l_2. rewrite registers_map_core_union.
      subst rmap_full.
      rewrite registers_map_core_union in Hnone.
      epose proof (lookup_union_None rmap) ; apply H in Hnone as [? ?];auto.
      rewrite registers_map_core_union; apply map_disjoint_union_r_2;auto. }

    (* we assert the register state has the needed domain *)
    assert (dom (<[(i, r_t1):=WCap RWX b_l e_l e_l]>
                   (<[(i, r_t10):=WCap RWX b_l e_l e_l]>
                      (<[(i, r_t2):=WInt 0%Z]>
                         (<[(i, r_t3):=WInt 0%Z]>
                            (<[(i, r_t4):=WInt 0%Z]>
                               (<[(i, r_t5):=WInt 0%Z]>
                                  (<[(i, r_t6):=WInt 0%Z]>
                                     (<[(i, r_t7):=WInt 0%Z]>
                                        (<[(i, r_t8):=WInt 0%Z]>
                                           (<[(i, r_t9):=WInt 0%Z]>
                                              (<[(i, r1):=wadv]> rmap)))))))))) ∪
                     registers_map_core i (mlocals ∪ mparams)) =
              all_registers_s_core i ∖ {[(i, PC); (i, r_t0)]}) as Hdomeq'.
    { rewrite dom_union_L 10!dom_insert_L.
      assert ( {[(i, r_t1)]} ∪ ({[(i, r_t10)]} ∪ ({[(i, r_t2)]} ∪ ({[(i, r_t3)]} ∪ ({[(i, r_t4)]} ∪ ({[(i, r_t5)]} ∪ ({[(i, r_t6)]} ∪ ({[(i, r_t7)]} ∪ ({[(i, r_t8)]} ∪ ({[(i, r_t9)]} ∪ dom (<[(i, r1) :=wadv]> rmap))))))))))
                       = dom (<[(i, r1):=wadv]> rmap)) as ->.
      { clear -Hsub. rewrite dom_insert_L. set_solver. }
      rewrite -dom_union_L -insert_union_l. auto. }

    (* prepare the program memory *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog2 rest3 link3) "(Hmalloc & Hprog & #Hcont5)".
    { apply contiguous_between_cons_inv in Hcont4 as [?[? [? Hcont5] ] ].
      apply contiguous_between_cons_inv_first in Hcont5 as Heq;subst x. apply Hcont5. }
    iDestruct "Hcont5" as %(Hcont5 & Hcont6 & Heqapp3 & Hlink3).

    (* apply malloc spec *)
    iApply (malloc_spec i _ 7 with
             "[- $HPC $Hinv $Hb $Ha_entry $Hmalloc $Hr_t0 $Hgenlocalsparams]")
    ;auto
    ;[|apply Hcont5|clear;lia|].
    { eapply isCorrectPC_range_restrict;eauto.
      assert (link2 + 1 = Some f)%a as Hnext;[iContiguous_next Hcont4 0|].
      apply contiguous_between_bounds in Hcont6. clear -Hnext Hcont6. solve_addr. }
    iNext. iIntros "(HPC & Hmalloc & Hb & Ha_entry & Hregion & Hr_t0 & Hgenlocalsparams)".
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

    (* prepare the memory for the activation record *)
    assert (b_l' <= e_l')%a as Hle';[clear -Hact_size;solve_addr|].
    assert (finz.dist b_l' e_l' = 7) as Hact_size_alt;[rewrite /finz.dist;clear -Hact_size;solve_addr|].
    rewrite /region_addrs_zeroes Hact_size_alt. iSimpl in "Hbl'".
    set l := finz.seq_between b_l' e_l'.
    assert (contiguous_between l b_l' e_l') as Hcontbl';[rewrite /l;apply contiguous_between_region_addrs;auto|].
    assert (length l = 7) as Hlength_l;[rewrite /l finz_seq_between_length;auto|].
    assert (∀ a, a ∈ l → withinBounds b_l' e_l' a = true) as Hwbbl'.
    { intros a1 Hin. rewrite andb_true_iff. rewrite Z.leb_le Z.ltb_lt.
      eapply contiguous_between_middle_bounds';[apply Hcontbl'|auto]. }
    destruct l;[inversion Hlength_l|]. apply contiguous_between_cons_inv_first in Hcontbl' as Heq. subst f0.

    (* move r_t0 r_t1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 0|].
    iEpilogue "(HPC & Hi & Hr_t0 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t0 hw_1 *)
    destruct l;[inversion Hlength_l|].
    iDestruct (region_mapsto_cons with "Hbl'") as "[Ha1 Hbl']";[iContiguous_next Hcontbl' 0|iContiguous_le Hcontbl' 1|].
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t0 $Ha1]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 1|..]; auto.
    { apply Hwbbl'. constructor. }
    iEpilogue "(HPC & Hi & Hr_t0 & Ha1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 2|iContiguous_next Hcontbl' 0|auto..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t0 hw_2 *)
    destruct l;[inversion Hlength_l|].
    iDestruct (region_mapsto_cons with "Hbl'") as "[Ha2 Hbl']";[iContiguous_next Hcontbl' 1|iContiguous_le Hcontbl' 2|].
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t0 $Ha2]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 3|..]; auto.
    { apply Hwbbl'. repeat constructor. }
    iEpilogue "(HPC & Hi & Hr_t0 & Ha2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 4|iContiguous_next Hcontbl' 1|auto..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t0 hw_3 *)
    destruct l;[inversion Hlength_l|].
    iDestruct (region_mapsto_cons with "Hbl'") as "[Ha3 Hbl']";[iContiguous_next Hcontbl' 2|iContiguous_le Hcontbl' 3|].
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t0 $Ha3]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 5|..]; auto.
    { apply Hwbbl'. repeat constructor. }
    iEpilogue "(HPC & Hi & Hr_t0 & Ha3)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 6|iContiguous_next Hcontbl' 2|auto..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t0 hw_4 *)
    destruct l;[inversion Hlength_l|].
    iDestruct (region_mapsto_cons with "Hbl'") as "[Ha4 Hbl']";[iContiguous_next Hcontbl' 3|iContiguous_le Hcontbl' 4|].
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t0 $Ha4]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 7|..]; auto.
    { apply Hwbbl'. repeat constructor. }
    iEpilogue "(HPC & Hi & Hr_t0 & Ha4)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 8|iContiguous_next Hcontbl' 3|auto..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t0 hw_5 *)
    destruct l;[inversion Hlength_l|].
    iDestruct (region_mapsto_cons with "Hbl'") as "[Ha5 Hbl']";[iContiguous_next Hcontbl' 4|iContiguous_le Hcontbl' 5|].
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t0 $Ha5]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 9|..]; auto.
    { apply Hwbbl'. repeat constructor. }
    iEpilogue "(HPC & Hi & Hr_t0 & Ha5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 10|iContiguous_next Hcontbl' 4|auto..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t0 r_t10 *)
    (* first we must get r_t10 *)
    rewrite (insert_commute _ _ (i, r_t10)); last (simplify_pair_eq).
    rewrite -(insert_union_l _ _ (i, r_t10)).
    rewrite delete_insert_ne; last simplify_pair_eq.
    repeat (rewrite (insert_commute _ _ (i, r_t10)) ; last simplify_pair_eq).
    iDestruct (big_sepM_delete with "Hgenlocalsparams") as "[Hr_t10 Hgenlocalsparams]";[apply lookup_insert|].
    (* next we get the next memory of the activation *)
    destruct l;[inversion Hlength_l|].
    iDestruct (region_mapsto_cons with "Hbl'") as "[Ha6 Hbl']";[iContiguous_next Hcontbl' 5|iContiguous_le Hcontbl' 6|].
    (* and we store *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t10 $Hr_t0 $Ha6]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 11|..]; auto.
    { apply Hwbbl'. repeat constructor. }
    iEpilogue "(HPC & Hi & Hr_t10 & Hr_t0 & Ha6)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 1 *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 12|iContiguous_next Hcontbl' 5|auto..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 PC *)
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 13|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 offset_to_cont *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest3.

    (* We need to know that the result of the lea is the last correct continuation *)
    (* The following proof is quite tedious, and should perhaps be generalized *)
    assert (f18 + (offset_to_cont_call (map_to_list mparams).*1) = Some a_last)%a as Hlea.
    { rewrite /offset_to_cont_call.
      eapply (contiguous_between_middle_to_end _ _ _ 13);[apply Hcont6|auto|..].
      clear -Hlength_rest3 Hne1 Hne2 Hdisj4. revert Hlength_rest3.
      set a := rclear_instrs (list_difference all_registers ([PC; r_t0; r1] ++ (map_to_list mparams).*1)).
      intros Hlength_rest3. simpl in Hlength_rest3.
      set a' := (rclear_instrs (list_difference all_registers (map_to_list mparams).*1)).
      simpl. repeat f_equal. rewrite app_length /a rclear_length in Hlength_rest3.
      assert (length (list_difference all_registers [PC; r_t0; r1]) = 30) as Hregs.
      { assert ([PC;r_t0;r1] = [PC;r_t0]++[r1]) as ->;[auto|]. rewrite list_difference_app.
        rewrite stdpp_extra.list_difference_length;auto.
        apply NoDup_list_difference,all_registers_NoDup. apply NoDup_singleton.
        apply NoDup_submseteq. apply NoDup_singleton.
        intros ? ->%elem_of_list_singleton. apply elem_of_list_difference. split. apply all_registers_correct.
        repeat (apply not_elem_of_cons;split;auto);apply not_elem_of_nil. }
      assert (NoDup all_registers) as Hdup1.
      { apply all_registers_NoDup. }
      assert (NoDup [PC; r_t0; r1]) as Hdup2.
      { repeat (apply NoDup_cons; split; [repeat (apply not_elem_of_cons; split; [done|])|]).
        all: try apply not_elem_of_nil. by apply NoDup_nil. }
      assert (∀ x : RegName, x ∈ [PC; r_t0; r1] → x ∉ (map_to_list mparams).*1) as Hforall.
      { intros x Hin. intros Hcontr%map_to_list_fst. destruct Hdisj4 as [HPC [Hr_t0 Hr1] ].
        apply elem_of_cons in Hin as [-> | Hin]. apply HPC. apply elem_of_gmap_dom.
        destruct Hcontr as [? Hcontr]. apply elem_of_map_to_list in Hcontr. eauto.
        apply elem_of_cons in Hin as [-> | Hin]. apply Hr_t0. apply elem_of_gmap_dom.
        destruct Hcontr as [? Hcontr]. apply elem_of_map_to_list in Hcontr. eauto.
        apply elem_of_cons in Hin as [-> | Hin]. apply Hr1. apply elem_of_gmap_dom.
        destruct Hcontr as [? Hcontr]. apply elem_of_map_to_list in Hcontr. eauto. inversion Hin.  }
      assert (NoDup ([PC; r_t0; r1] ++ (map_to_list mparams).*1)) as Hdup3.
      { apply NoDup_app. split;[auto|].
        split;[|apply NoDup_map_to_list_fst;apply reg_eq_dec]. auto. }
      assert ([PC; r_t0; r1] ++ (map_to_list mparams).*1 ⊆+ all_registers) as Hsub.
      { apply all_registers_correct_sub;auto. }
      rewrite list_difference_length in Hlength_rest3;auto.
      assert ((map_to_list mparams).*1 ⊆+ all_registers) as Hsub'.
      { apply all_registers_correct_sub;auto. apply NoDup_map_to_list_fst, reg_eq_dec. }
      assert (strings.length (map_to_list mparams).*1 ≤ 30) as Hle.
      { assert ((map_to_list mparams).*1 ⊆+ list_difference all_registers [PC;r_t0;r1]).
        { apply submseteq_list_difference;[apply NoDup_map_to_list_fst, reg_eq_dec|auto..]. }
        apply submseteq_length in H as Hle. by rewrite Hregs in Hle. }
      apply eq_add_S in Hlength_rest3. rewrite Hlength_rest3 /a'.
      rewrite rclear_length. rewrite list_difference_length;auto.
      clear -Hle;simpl. lia.
      apply NoDup_map_to_list_fst, reg_eq_dec.
    }

    assert (exists a_end, f18 + ((offset_to_cont_call (map_to_list mparams).*1) - 1) = Some a_end)%a as [a_end Hlea'].
    { clear -Hlea. revert Hlea.
      rewrite /offset_to_cont_call. set (l := strings.length (rclear_instrs (list_difference all_registers (map_to_list mparams).*1))).
      intros Hlea. destruct (f18 + ((6 + l - 3)%nat - 1))%a eqn:Hsome; eauto. simpl in Hsome, Hlea. exfalso.
      clearbody l. solve_addr. }

    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 14|apply Hlea'|..].
    { eapply isCorrectPC_range_perm_non_E;[apply Hvpc2|].
      apply contiguous_between_middle_bounds with (i:=0) (ai:=link3) in Hcont6 as [? ?];auto. }
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* store r_t0 r_t1 *)
    destruct l;[|inversion Hlength_l].
    assert (f16 + 1 = Some e_l')%a as Hllast;[eapply contiguous_between_last;[apply Hcontbl'|auto]|].
    apply finz_seq_between_singleton in Hllast as Heql. rewrite /region_mapsto Heql.
    iDestruct "Hbl'" as "[Ha7 _]".
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t1 $Hr_t0 $Ha7]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 15|..]; auto.
    { apply Hwbbl'. repeat constructor. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t0 & Ha7)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* lea r_t0 -6 *)
    assert (f16 + (-6) = Some b_l')%a as Hlea''.
    { apply contiguous_between_length_minus in Hcontbl'. clear -Hcontbl' Hllast. simpl in *. solve_addr. }
    destruct rest3 as [|? rest3];[inversion Hlength_prog'|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 16|apply Hlea''|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* restrict r_t0 E *)
    destruct rest3 as [|? rest3].
    { exfalso. revert Hlength_rest3. rewrite Permutation_app_comm.
      assert (strings.length [f19; f20; f21; f22] = 4) as ->;[auto|].
      rewrite 5!cons_length.
      intros Hcontr.
      inversion Hcontr. }

    iPrologue "Hprog".
    iApply (wp_restrict_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|iContiguous_next Hcont6 17|auto..].
    { rewrite decode_encode_perm_inv. auto. }
    rewrite decode_encode_perm_inv.
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".


    (* rclear all_registers \ { PC; r_t0; r1 } \ params *)

    (* rebuild register map *)
    (* we begin by cleaning up the current register map *)
    iDestruct (big_sepM_insert with "[$Hgenlocalsparams $Hr_t10]") as
      "Hgenlocalsparams";[apply lookup_delete|rewrite insert_delete_insert
                                                insert_insert].

    rewrite - !insert_union_l delete_insert_delete - !delete_insert_ne.
    all: try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end).
    iDestruct (big_sepM_insert with "[$Hgenlocalsparams $Hr_t1]") as "Hgenlocalsparams";[apply lookup_delete|rewrite insert_delete_insert].
    rewrite !(insert_commute _ _ (i, r_t2))
    ; try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end)
    ; rewrite insert_insert.
    rewrite !(insert_commute _ _ (i, r_t3))
    ; try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end)
    ; rewrite insert_insert.
    rewrite !(insert_commute _ _ (i, r_t4))
    ; try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end)
    ; rewrite insert_insert.
    rewrite !(insert_commute _ _ (i, r_t5))
    ; try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end)
    ; rewrite insert_insert.
    rewrite !(insert_commute _ _ (i, r_t6))
    ; try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end)
    ; rewrite insert_insert.
    rewrite !(insert_commute _ _ (i, r_t7))
    ; try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end)
    ; rewrite insert_insert.
    rewrite !(insert_commute _ _ (i, r_t8))
    ; try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end)
    ; rewrite insert_insert.
    rewrite !(insert_commute _ _ (i, r_t9))
    ; try (match goal with | h: _ |- _ <> _ => simplify_pair_eq end)
    ; rewrite insert_insert.
    rewrite !insert_union_l.
    (* next we separate the params from the map, since we do not want to clear it *)
    iDestruct (big_sepM_union with "Hgenlocalsparams") as "[Hgen Hlocalsparams]".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap i|]);
      apply map_disjoint_insert_l_2 ;[|rewrite registers_map_core_union
                                       ; apply map_disjoint_union_r_2];auto.
      epose proof (lookup_union_None _) ; apply H in Hnone as [? ?];auto. }
    rewrite registers_map_core_union.
    iDestruct (big_sepM_union with "Hlocalsparams") as "[Hlocals Hparams]";[auto|].
    iDestruct (big_sepM_union with "[$Hgen $Hlocals]") as "Hgenlocals".
    { repeat (apply map_disjoint_insert_l_2;[disjoint_from_rmap rmap i|]).
      apply map_disjoint_insert_l_2;auto.
      epose proof (lookup_union_None _)
      ;apply H in Hnone as [? Hnone]; clear H.
      rewrite registers_map_core_union in Hnone.
      epose proof (lookup_union_None _)
      ;apply H in Hnone as [? Hnone]; clear H. auto. }
    repeat (rewrite (insert_commute _ _ (i, r1));[|apply Hneregs;set_solver+]). rewrite -insert_union_l.
    iDestruct (big_sepM_delete with "Hgenlocals") as "[Hradv Hgenlocals]"; [apply lookup_insert|].
    rewrite delete_insert.
    2: { rewrite - !insert_union_l.
         repeat (rewrite lookup_insert_ne;[|apply Hneregs;set_solver+]).
         epose proof (lookup_union_None _)
         ;apply H in Hnone as [? Hnone]; clear H.
         rewrite registers_map_core_union in Hnone.
         epose proof (lookup_union_None _)
         ;apply H in Hnone as [? Hnone]; clear H.
         apply lookup_union_None. split ;auto. }

    (* prepare the program memory *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (rclear_prog rest4 link4) "(Hrclear & Hprog & #Hcont6)".
    { assert (link3 :: f0 :: f2 :: f3 :: f5 :: f6 :: f8 :: f9 :: f11 :: f12 :: f14 :: f15 :: f17 :: f18 :: f19 :: f20 :: f21 :: f22 :: f23 :: rest3 =
              (link3 :: f0 :: f2 :: f3 :: f5 :: f6 :: f8 :: f9 :: f11 :: f12 :: f14 :: f15 :: f17 :: f18 :: f19 :: f20 :: f21 :: [f22]) ++ (f23 :: rest3)) as Happ;auto.
      eapply contiguous_between_app with (k:=f23) in Happ as [? ?];[|apply Hcont6|apply contiguous_between_length in Hcont6 as Hlen];eauto.
      simpl.
      eapply contiguous_between_incr_addr;[apply Hcont6|]. auto. }
    iDestruct "Hcont6" as %(Hcont7 & Hcont8 & Heqapp4 & Hlink4).
    iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
    destruct rclear_prog.
    { exfalso. revert Hrclear_length. rewrite rclear_length (list_difference_cons _ _ r_t1).
      intros Hcontr;inversion Hcontr.
      apply all_registers_NoDup. apply all_registers_correct.
      apply not_elem_of_app. split.
      - do 2 (apply not_elem_of_cons;split;[auto|]).
        apply not_elem_of_cons;split;[|apply not_elem_of_nil].
        assert (Htmp : forall r, (i, r) ≠ (i, r1) -> r <> r1).
        { clear. intros. intro. subst. contradiction. }
        apply Htmp; apply Hneregs.
        set_solver +.
      - intros Hcontr%map_to_list_fst. destruct Hcontr as [x Hx].
        apply elem_of_map_to_list in Hx.
        assert (Hy: (registers_map_core i mparams) !! (i, r_t1) = Some x).
        { rewrite lookup_kmap_Some. eexists;eauto. }
        apply map_disjoint_Some_r with (m1:=rmap) in Hy;auto.
        apply elem_of_gmap_dom_none in Hy. apply Hy. apply Hsub. set_solver +.
    }
    apply contiguous_between_cons_inv_first in Hcont7 as Heq. subst f24.

    (* a useful assumption about the current register state to clear *)
    assert (dom rmap' =
            {[(i, r_t9); (i, r_t8); (i, r_t7); (i, r_t6); (i, r_t5); (i, r_t4); (i, r_t3); (i, r_t2); (i, r_t1); (i, r_t10)]}
              ∪ (dom (registers_map_core i mlocals) ∪ dom rmap' ∖ dom (registers_map_core i mlocals)))
      as Hrmap'eq.
    { rewrite Hdom2. rewrite Hdom1 in Hsub. clear -Hsub Hdisj1 Hdisj5. rewrite -union_difference_L.
      assert ({[(i, r_t1); (i, r_t2); (i, r_t3); (i, r_t4); (i, r_t5); (i, r_t6); (i, r_t7); (i, r_t8); (i, r_t9); (i, r_t10)]}
                ⊆ all_registers_s_core i ∖ {[(i, PC); (i, r_t0); (i, r1)]} ∖
                registers_s_core i (dom mparams)) as Hsub'.
      (* { etrans;[eauto|]. apply subseteq_difference_l. auto. } *)
      { clear -Hsub.
        unfold registers_s_core in Hsub.
        match goal with
          | h: _ |- ?s ⊆ _ => set (rmap := s)
        end.
        assert ( @set_map _ _ (@gset_elements RegName _ _) _ _ gset_singleton _ _
           (λ r : RegName, (i, r))
           {[r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10]}
                 = rmap
          ) as <- by set_solver+.
        etrans;[eauto|].
        set_solver. }
      apply subseteq_union_L in Hsub'.
      assert ({[(i, r_t9); (i, r_t8); (i, r_t7); (i, r_t6); (i, r_t5); (i, r_t4); (i, r_t3);
                (i, r_t2); (i, r_t1); (i, r_t10)]}
              = {[(i, r_t1); (i, r_t2); (i, r_t3); (i, r_t4); (i, r_t5)
                  ; (i, r_t6); (i, r_t7); (i, r_t8); (i, r_t9); (i, r_t10)]})
        as ->
      ;[clear;set_solver|].
      assert ( registers_s_core i {[PC; r_t0; r1]} =
                 {[(i, PC); (i, r_t0); (i, r1)]} ) as ->
      ;[clear;set_solver|].
      rewrite Hsub';auto.
      rewrite dom_kmap_L.
      apply subseteq_difference_r.
      { clear -Hdisj1.
        apply map_disjoint_dom in Hdisj1 ; set_solver. }
      apply subseteq_difference_r.
      { clear -Hdisj5; set_solver. }
      clear; set_solver.
    }

    (* rclear *)
    set instrs := (list_difference all_registers ([PC; r_t0; r1] ++ (map_to_list mparams).*1)).
    iApply (rclear_spec i _ instrs with "[-]");[apply Hcont7|..];last (iFrame "Hgenlocals HPC").
    { apply not_elem_of_list. constructor. }
    { auto. }
    { eapply isCorrectPC_range_restrict;[apply Hvpc|].
      apply contiguous_between_bounds in Hcont8. split;auto.
      apply contiguous_between_middle_bounds with (i:=18) (ai:=f23) in Hcont6 as [Hle _];[|auto].
      apply contiguous_between_bounds in Hcont5. apply contiguous_between_bounds in Hcont3.
      apply contiguous_between_middle_bounds with (i:=1) (ai:=f) in Hcont4 as [Hle'' _];[|auto].
      clear -Hlink1 Hcont8 Hle Hle'' Hcont5 Hcont3. solve_addr. }
    { rewrite list_to_set_difference list_to_set_app_L.
      assert (list_to_set [PC; r_t0; r1] = {[PC;r_t0;r1]}) as ->;[simpl;clear;set_solver|].
      rewrite -/all_registers_s. rewrite -difference_difference_L.
      rewrite - !insert_union_l !dom_insert_L. rewrite !union_assoc_L dom_union_L (union_comm_L (dom rmap)) Hdom1.
      assert (list_to_set (map_to_list mparams).*1 = dom mparams) as ->;[apply list_to_set_map_to_list|].
      rewrite -Hdom2.
      assert (Hdom2': dom rmap' = set_map (λ r' : RegName, (i, r')) (all_registers_s ∖ {[PC; r_t0; r1]} ∖ dom mparams)).
      { rewrite Hdom2. set_solver+. }
      assert (Hdom_reg:
               dom (registers_map_core i mlocals)
               = registers_s_core i (dom mlocals)).
      { by rewrite dom_kmap_L. }
      rewrite -Hdom_reg.
      rewrite -Hdom2'.
      apply Hrmap'eq.
    }

    iSplitL "Hrclear". iNext. rewrite /rclear. iExact "Hrclear".
    iNext. iIntros "(HPC & Hgenlocals & Hrclear)".
    (* prepare for the last instruction *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest4.
    destruct rest4;[inversion Hlength_rest4|]. destruct rest4;[|inversion Hlength_rest4].
    apply contiguous_between_cons_inv_first in Hcont8 as Heq. subst f24.
    assert (isCorrectPC_range p b e link4 a_last) as Hvpc3.
    { eapply isCorrectPC_range_restrict;[apply Hvpc|]. split;[|clear;solve_addr].
      apply contiguous_between_bounds in Hcont1.
      apply contiguous_between_bounds in Hcont3.
      assert (link2 + 1 = Some f)%a as Hnext;[iContiguous_next Hcont4 0|].
      apply contiguous_between_bounds in Hcont5. apply contiguous_between_bounds in Hcont7.
      apply contiguous_between_middle_bounds with (i:=18) (ai:=f23) in Hcont6 as [Hle _];[|auto].
      clear -Hcont3 Hcont5 Hnext Hcont1 Hlink2 Hle Hcont7. solve_addr. }

    (* jmp r1 *)
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hradv]");
      [apply decode_encode_instrW_inv|iCorrectPC link4 a_last|].
    iEpilogue "(HPC & Hi & Hradv)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* continuation *)
    (* FIXME : why can't I apply Hcont here ?? *)
    iApply "Hcont".
    iExists b_l',e_l',b_l,e_l,a_end.
    iSplitR.
    { iPureIntro. revert Hlea Hlea'. clear.
      rewrite /offset_to_cont_call. set (l := strings.length (rclear_instrs (list_difference all_registers (map_to_list mparams).*1))).
      generalize l. clear. solve_addr. }
    iFrame "HPC Hparams Hradv Hr_t0 Hbl Hb Ha_entry Hna".
    iSplitL "Hgenlocals".
    { rewrite !big_sepM_dom. iApply (big_sepS_subseteq with "Hgenlocals").
      rewrite - !insert_union_l !dom_insert_L !union_assoc_L dom_union_L (union_comm_L (dom rmap)) Hdom1.
      rewrite -Hdom2. rewrite Hrmap'eq. clear. set_solver. }
    iSplitL "Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7".
    { apply region_addrs_of_contiguous_between in Hcontbl' as <-. iFrame. done. }
    rewrite Heqapp1 Heqapp2 Heqapp3 Heqapp4.
    rewrite /call.
    iDestruct "Hprog_done" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&malloc&?&locals&malloc')".
    iApply (big_sepL2_app with "malloc'").
    iApply (big_sepL2_app with "locals").
    iFrame.
  Qed.

End call.
