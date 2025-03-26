From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth.
From cap_machine Require Export logical_mapsto.
From cap_machine Require Export cap_lang iris_extra stdpp_extra.

(* --------------------------- LTAC DEFINITIONS ----------------------------------- *)

(* Ltac destruct_cons_hook ::= destruct_cons_hook2. *)
Ltac inv_head_step :=
  repeat match goal with
         | _ => progress simplify_map_eq/= (* simplify memory stuff *)
         | H : to_val _ = Some _ |- _ => apply of_to_val in H
         | H : _ = of_val ?v |- _ =>
           is_var v; destruct v; first[discriminate H|injection H as H]
         | H : cap_lang.prim_step ?e _ _ _ _ _ |- _ =>
           try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
           (*    and can thus better be avoided. *)
           let φ := fresh "φ" in
           inversion H as [| φ]; subst φ; clear H
         end.

Section cap_lang_rules.
  Context `{MachineParameters}.
  Context `{memG Σ, regG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types la: LAddr.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  (* Conditionally unify on the read register value *)
  Definition read_reg_inr (lregs : LReg) (r : RegName) p b e a v :=
    match lregs !! r with
      | Some (LCap p' b' e' a' v') => (LCap p' b' e' a' v') = LCap p b e a v
      | Some _ => True
      | None => False end.

  (* ------------------------- registers points-to --------------------------------- *)

  Lemma regname_dupl_false r lw1 lw2 :
    r ↦ᵣ lw1 -∗ r ↦ᵣ lw2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %?.
    destruct H2. eapply dfrac_full_exclusive in H2. auto.
  Qed.

  Lemma regname_neq r1 r2 lw1 lw2 :
    r1 ↦ᵣ lw1 -∗ r2 ↦ᵣ lw2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (regname_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_regs_1 (r1: RegName) (lw1: LWord) :
    r1 ↦ᵣ lw1 -∗
    ([∗ map] k↦y ∈ <[r1:=lw1]> ∅, k ↦ᵣ y).
  Proof.
    iIntros "H1".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
  Qed.

  Lemma regs_of_map_1 (r1: RegName) (lw1: LWord) :
    ([∗ map] k↦y ∈ {[r1 := lw1]}, k ↦ᵣ y) -∗
    r1 ↦ᵣ lw1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma map_of_regs_2 (r1 r2: RegName) (lw1 lw2: LWord) :
    r1 ↦ᵣ lw1 -∗ r2 ↦ᵣ lw2 -∗
    ([∗ map] k↦y ∈ (<[r1:=lw1]> (<[r2:=lw2]> ∅)), k ↦ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: RegName) (lw1 lw2: LWord) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=lw1]> (<[r2:=lw2]> ∅)), k ↦ᵣ y) -∗
    r1 ↦ᵣ lw1 ∗ r2 ↦ᵣ lw2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: LWord) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ⌝.
  Proof.
    iIntros "H1 H2 H3".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: LWord) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: LWord) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗ r4 ↦ᵣ w4 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4 ∧ r2 ≠ r3 ∧ r2 ≠ r4 ∧ r3 ≠ r4 ⌝.
  Proof.
    iIntros "H1 H2 H3 H4".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H1 H4") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    iPoseProof (regname_neq with "H2 H4") as "%".
    iPoseProof (regname_neq with "H3 H4") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: LWord) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3 ∗ r4 ↦ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  (* ------------------------- memory points-to --------------------------------- *)

  Lemma addr_dupl_false la lw1 lw2 :
    la ↦ₐ lw1 -∗ la ↦ₐ lw2 -∗ False.
  Proof.
    iIntros "Ha1 Ha2".
    iDestruct (mapsto_valid_2 with "Ha1 Ha2") as %?.
    destruct H2. eapply dfrac_full_exclusive in H2.
    auto.
  Qed.

  (* -------------- semantic heap + a map of pointsto -------------------------- *)

  Lemma gen_heap_valid_inSepM_general:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (dσ : gmap L (dfrac * V)) (σ : gmap L V)
      (l : L) (dq : dfrac) (v : V),
      dσ !! l = Some (dq, v) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦dqw ∈ dσ, mapsto k dqw.1 dqw.2)
      -∗ ⌜σ !! l = Some v⌝.
  Proof.
    intros * Hσ'.
    rewrite (big_sepM_delete _ dσ l) //. iIntros "? [? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (l : L) (q : Qp) (v : V),
      σ' !! l = Some v →
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜σ !! l = Some v⌝.
  Proof.
    intros * Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "? [? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inSepM':
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜forall (l: L) (v: V), σ' !! l = Some v → σ !! l = Some v⌝.
  Proof.
    intros *. iIntros "? Hmap" (l v Hσ').
    rewrite (big_sepM_delete _ σ' l) //. iDestruct "Hmap" as "[? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inSepM'_general:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (dσ : gmap L (dfrac * V)) (σ : gmap L V) ,
      gen_heap_interp σ
      -∗ ([∗ map] k↦dqw ∈ dσ, mapsto k dqw.1 dqw.2)
      -∗ ⌜forall (l: L) (d : dfrac) (v: V), dσ !! l = Some (d, v) → σ !! l = Some v⌝.
  Proof.
    intros. iIntros "? Hmap" (l d v Hσ).
    rewrite (big_sepM_delete _ dσ l) //.
    iDestruct "Hmap" as "[? ?]". cbn.
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inclSepM_general:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (dσ : gmap L (dfrac * V)) (σ : gmap L V),
      gen_heap_interp σ
      -∗ ([∗ map] k↦dqw ∈ dσ, mapsto k dqw.1 dqw.2)
      -∗ ⌜(fmap snd dσ) ⊆ σ⌝.
  Proof.
    intros. iIntros "Hσ Hmap".
    iDestruct (gen_heap_valid_inSepM'_general with "Hσ Hmap") as "#H". eauto.
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (dσ !! l) eqn:HH'; destruct (σ !! l) eqn:HH
    ; rewrite lookup_fmap HH'
    ; try naive_solver.
    + destruct p; cbn in * ; apply Hincl in HH'; simplify_eq; reflexivity.
    + destruct p; cbn in * ; apply Hincl in HH'; simplify_eq; reflexivity.
    (* + cbn. *)
  Qed.

  Lemma gen_heap_valid_inclSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜σ' ⊆ σ⌝.
  Proof.
    intros *. iIntros "Hσ Hmap".
    iDestruct (gen_heap_valid_inSepM' with "Hσ Hmap") as "#H".
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (σ' !! l) eqn:HH'; destruct (σ !! l) eqn:HH; naive_solver.
  Qed.

  Lemma gen_heap_valid_allSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (EV: Equiv V) (REV: Reflexive EV) (LEV: @LeibnizEquiv V EV)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      (forall (l:L), is_Some (σ' !! l)) →
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜ σ = σ' ⌝.
  Proof.
    intros * ? ? * Hσ'. iIntros "A B".
    iAssert (⌜ forall l, σ !! l = σ' !! l ⌝)%I with "[A B]" as %HH.
    { iIntros (l).
      specialize (Hσ' l). unfold is_Some in Hσ'. destruct Hσ' as [v Hσ'].
      rewrite Hσ'.
      eapply (gen_heap_valid_inSepM _ _ _ _ _ _ σ σ') in Hσ'.
      iApply (Hσ' with "[$]"). eauto. }
    iPureIntro. eapply map_leibniz. intro.
    eapply leibniz_equiv_iff. auto.
    Unshelve.
    unfold equiv. unfold Reflexive. intros [ x |].
    { unfold option_equiv. constructor. apply REV. } constructor.
  Qed.

  Lemma gen_heap_update_inSepM_general :
    ∀ {L V : Type} {EqDecision0 : EqDecision L}
      {H : Countable L} {Σ : gFunctors}
      {gen_heapG0 : gen_heapGS L V Σ}
      (σ : gmap L V) (σ' : gmap L (dfrac * V)) (l : L) (v : V),
      (exists w, (σ' !! l = Some (DfracOwn 1, w))) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦y ∈ σ', mapsto k y.1 y.2)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=(DfracOwn 1, v)]> σ'), mapsto k y.1 y.2.
  Proof.
    intros * Hw. destruct Hw.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=(DfracOwn 1, v)]> σ') l (DfracOwn 1, v)).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.


  Lemma gen_heap_update_inSepM :
    ∀ {L V : Type} {EqDecision0 : EqDecision L}
      {H : Countable L} {Σ : gFunctors}
      {gen_heapG0 : gen_heapGS L V Σ}
      (σ σ' : gmap L V) (l : L) (v : V),
      is_Some (σ' !! l) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), mapsto k (DfracOwn 1) y.
  Proof.
    intros * Hσ'. destruct Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=v]> σ') l).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.

  (* Note: glm and lm should really be the same, but the generalization is needed for the inductive case. *)
  Lemma gen_heap_lmem_version_update_addr `{HmemG : memG Σ, HregG : regG Σ}
    {lmem glm lm lmem' lm': LMem} {vmap vmap': VMap}
      {a : Addr} {v : Version} :
      lmem ⊆ lm ->
      lmem' = update_version_addr glm a v lmem ->
      lm' = update_version_addr glm a v lm ->
      vmap' = update_version_addr_vmap a v vmap ->
      lm !! (a, v+1) = None ->
      is_cur_addr (a,v) vmap ->
      gen_heap_interp lm
      -∗ ([∗ map] k↦y ∈ lmem, mapsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp lm' ∗ [∗ map] k↦y ∈ lmem', mapsto k (DfracOwn 1) y.
  Proof.
    iIntros (Hlmem_incl Hupdlmem Hupdlm Hupdvm Hmaxvm_lm Hcur_lm) "Hgen Hmem".
    rewrite /update_version_addr in Hupdlm, Hupdlmem.
    unfold is_cur_addr in Hcur_lm; cbn in Hcur_lm.
    destruct (glm !! (a,v)) as [lw|]eqn:Hlmav.
    - iMod (((gen_heap_alloc lm (a, v + 1) lw) with "Hgen"))
        as "(Hgen & Ha & _)"; auto.
      iModIntro; subst; iFrame.
      (* local knowledge about (a,v) *)
      iApply (big_sepM_insert with "[Hmem Ha]"); last iFrame.
      eapply lookup_weaken_None; eauto.
    - (*shouldn't happen, but okay *)
      subst. now iFrame.
  Qed.

  (* Note: glm and lm should really be the same, but the generalization is needed for the inductive case. *)
  Lemma gen_heap_lmem_version_update' `{HmemG : memG Σ, HregG : regG Σ} :
    ∀ (glm lmem lm lmem' lm': LMem) (vmap vmap': VMap)
      (la : list Addr) ( v : Version ),
      NoDup la ->
      lmem ⊆ lm ->
      lmem' = update_version_region glm la v lmem ->
      lm' = update_version_region glm la v lm ->
      vmap' = update_version_region_vmap la v vmap ->
      Forall (λ a : Addr, lm !! (a, v+1) = None) la ->
      Forall (λ a : Addr, is_cur_addr (a,v) vmap) la ->
      gen_heap_interp lm
      -∗ ([∗ map] k↦y ∈ lmem, mapsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp lm' ∗ [∗ map] k↦y ∈ lmem', mapsto k (DfracOwn 1) y.
  Proof.
    move=> glm lmem lm lmem' lm' vmap vmap' la.
    move: glm lmem lm lmem' lm' vmap vmap'.
    induction la as [|a la IH]
    ; iIntros
        (glm lmem lm lmem' lm' vmap vmap' v
           HNoDup_la Hlmem_incl Hupdlmem Hupdlm Hupdvmap Hmaxv_lm Hcur_lm)
        "Hgen Hmem".
    - (* no addresses updated *)
      cbn in Hupdlm, Hupdvmap, Hupdlmem; simplify_eq.
      iModIntro; iFrame.
    - destruct_cons.
      iDestruct (IH glm with "Hgen Hmem") as ">[Hgen Hmem]"; eauto.
      simpl in Hupdlmem, Hupdlm, Hupdvmap.
      set (lm'' := update_version_region glm la v lm').
      set (lmem'' := update_version_region glm la v lmem').
      iDestruct (gen_heap_lmem_version_update_addr with "Hgen Hmem") as ">[Hgen Hmem]"; eauto.
      + now apply update_version_region_mono.
      + rewrite <-Hmaxv_lm_a.
        now apply update_version_region_notin_preserves_lmem.
      + unfold is_cur_addr; cbn.
        rewrite (update_version_region_notin_preserves_cur _ _ _ _ _ eq_refl Ha_notin_la).
        exact Hcur_lm_a.
      + now iFrame.
  Qed.

  Lemma prim_step_no_kappa {e1 σ1 κ e2 σ2 efs}:
    prim_step e1 σ1 κ e2 σ2 efs -> κ = [].
  Proof.
    now induction 1.
  Qed.

  Lemma prim_step_no_efs {e1 σ1 κ e2 σ2 efs}:
    prim_step e1 σ1 κ e2 σ2 efs -> efs = [].
  Proof.
    now induction 1.
  Qed.

  Definition LMemF := gmap LAddr (dfrac * LWord).

  Definition transiently (Pcommitted : iProp Σ) (Ptransient : iProp Σ) : iProp Σ :=
    Pcommitted ∗ (∀ Ep, Pcommitted ={Ep}=∗ Ptransient).

  Lemma transiently_abort Pcommitted Ptransient :
    transiently Pcommitted Ptransient ⊢ Pcommitted.
  Proof. now iIntros "[P _]". Qed.

  Lemma transiently_commit Pcommitted Ptransient Ep :
    transiently Pcommitted Ptransient ⊢ |={Ep}=> Ptransient.
  Proof. iIntros "[Hc Ht]". now iApply ("Ht" with "Hc"). Qed.

  Definition state_interp_transient (φ φt : ExecConf) (lr lrt : LReg) (lm lmt : LMemF) : iProp Σ :=
    transiently
      (state_interp_logical φ ∗ ([∗ map] k↦y ∈ lr, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ lm, k ↦ₐ{y.1} y.2))
      (state_interp_logical φt ∗ ([∗ map] k↦y ∈ lrt, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ lmt, k ↦ₐ{y.1} y.2)) ∗
    ∃ lreg_t lmem_t cur_map,
      ⌜ lrt ⊆ lreg_t ⌝ ∗ ⌜ snd <$> lmt ⊆ lmem_t ⌝ ∗
      ⌜state_phys_log_corresponds φt.(reg) φt.(mem) lreg_t lmem_t cur_map⌝.

  (* Definition state_interp_transient (φ φt : ExecConf) (lr lrt : LReg) (lm lmt : LMemF) : iProp Σ := *)
  (*   state_interp_logical φ *)
  (*     ∗ ([∗ map] k↦y ∈ lr, k ↦ᵣ y) *)
  (*     (* ∗ ⌜ lreg_strip lrt ⊆ reg φt ⌝ *) *)
  (*     ∗ ([∗ map] k↦y ∈ lm, k ↦ₐ{y.1} y.2) *)
  (*     ∗ (∃ lreg_t lmem_t cur_map, *)
  (*       ⌜ lrt ⊆ lreg_t ⌝ ∗ ⌜ snd <$> lmt ⊆ lmem_t ⌝ ∗ *)
  (*         ⌜state_phys_log_corresponds φt.(reg) φt.(mem) lreg_t lmem_t cur_map⌝) *)

  (*     ∗ (∀ Ep, state_interp_logical φ *)
  (*                ∗ ([∗ map] k↦y ∈ lr, k ↦ᵣ y) *)
  (*                ∗ ([∗ map] k↦y ∈ lm, k ↦ₐ{y.1} y.2) *)
  (*              ={Ep}=∗ state_interp_logical φt *)
  (*                      ∗ ([∗ map] k↦y ∈ lrt, k ↦ᵣ y) *)
  (*                      ∗ ([∗ map] k↦y ∈ lmt, k ↦ₐ{y.1} y.2)). *)

  Lemma state_interp_corr {σ lregs Ep} {lmem : LMemF} :
    state_interp_logical σ ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ lmem, k ↦ₐ{y.1} y.2) ⊢
      |={Ep}=> state_interp_logical σ ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ lmem, k ↦ₐ{y.1} y.2)
      ∗ ∃ lreg_t lmem_t cur_map,
        ⌜ lregs ⊆ lreg_t ⌝ ∗ ⌜ (snd <$> lmem) ⊆ lmem_t ⌝ ∗
        ⌜state_phys_log_corresponds σ.(reg) σ.(mem) lreg_t lmem_t cur_map⌝.
  Proof.
    iIntros "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iPoseProof (gen_heap_valid_inclSepM_general with "Hm Hmem") as "%Hlmem_incl".
    iModIntro.
    iSplitL "Hr Hm".
    { iExists _, _, _. now iFrame. }
    iFrame.
    iPureIntro; cbn.
    exists lr, lm, cur_map.
    do 2 (split ; auto).
  Qed.

  Lemma state_interp_transient_intro {Ep} {φ : ExecConf} {lr : LReg} {lm : LMemF} :
    state_interp_logical φ ∗ ([∗ map] k↦y ∈ lr, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ lm, k ↦ₐ{y.1} y.2)
                ⊢ |={Ep}=> state_interp_transient φ φ lr lr lm lm.
  Proof.
    iIntros "(Hφ & Hregs & Hmem)".
    iMod (state_interp_corr with "[$Hφ $Hregs $Hmem]") as "(Hφ & Hregs & Hmem & Hcorr)"; auto.
    iDestruct "Hcorr" as (lr' lm' cur_map) "(%Hlr_incl & %Hlm_incl & %Hcorr)".
    iModIntro. iFrame.
    iSplit.
    now iIntros.
    now iExists lr', lm', cur_map.
  Qed.

  Lemma state_interp_transient_intro_nodfracs {Ep} {φ : ExecConf} {lr : LReg} {lm : LMem} :
    state_interp_logical φ ∗ ([∗ map] k↦y ∈ lr, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ lm, k ↦ₐ y)
      ⊢ |={Ep}=> state_interp_transient φ φ lr lr ((fun y => (DfracOwn 1 , y)) <$> lm) ((fun y => (DfracOwn 1 , y)) <$> lm).
  Proof.
    rewrite <-state_interp_transient_intro.
    now rewrite big_sepM_fmap.
  Qed.

  Lemma state_interp_transient_elim_abort {φ φt: ExecConf} {lr lrt : LReg} {lm lmt : LMemF} :
    state_interp_transient φ φt lr lrt lm lmt
      ⊢ state_interp_logical φ
      ∗ ([∗ map] k↦y ∈ lr, k ↦ᵣ y)
      ∗ ([∗ map] k↦y ∈ lm, k ↦ₐ{y.1} y.2).
  Proof.
    iIntros "((Hφ & _) & _)".
    now iFrame.
  Qed.

  Lemma state_interp_transient_elim_commit
    {Ep} {φ φt: ExecConf} {lr lrt : LReg} {lm lmt : LMemF}:
    state_interp_transient φ φt lr lrt lm lmt ⊢
      |={Ep}=> state_interp_logical φt
                ∗ ([∗ map] k↦y ∈ lrt, k ↦ᵣ y)
                ∗ ([∗ map] k↦y ∈ lmt, k ↦ₐ{y.1} y.2).
  Proof.
    iIntros "(((Hφ & Hregs & Hmem) & Hupd) & _)".
    iMod ("Hupd" with "[$Hφ $Hregs $Hmem]") as "(Hφ & Hregs & Hmem)".
    now iFrame.
  Qed.

  Lemma wp_cap_lang {s E} {Φ} : ∀ e1 : language.expr cap_ectx_lang,
      to_val e1 = None →
      (∀ (σ1 : language.state cap_ectx_lang),
            state_interp_logical σ1 ={E}=∗
              ⌜head_reducible e1 σ1⌝ ∗
              ▷(∀ (e2 : language.expr cap_ectx_lang)
                  (σ2 : ectx_language.state cap_ectx_lang),
                  ⌜prim_step e1 σ1 [] e2 σ2 []⌝ -∗
                                                   £ 1 ={E}=∗ state_interp_logical σ2 ∗ from_option Φ False (language.to_val e2)))
        ⊢ wp s E e1 Φ.
  Proof.
    iIntros (? Hnoval) "H".
    iApply wp_lift_atomic_head_step_no_fork; try assumption.
    iIntros (σ1 ns κ κs nt) "Hσ1 /=".
    iMod ("H" $! σ1 with "[$Hσ1]") as "[%Hred H]".
    iModIntro. iSplitR; first by iPureIntro.
    iModIntro. iIntros (? ? ?) "%Hstep Hcred".
    destruct (prim_step_no_efs Hstep).
    destruct (prim_step_no_kappa Hstep).
    iMod ("H" $! e2 σ2 Hstep with "Hcred") as "H".
    now iSplitR.
  Qed.

  Lemma wp_instr_exec {s E} {Φ} :
      (∀ (σ1 : language.state cap_ectx_lang),
            state_interp_logical σ1 ={E}=∗
              ▷(∀ (e2 : ConfFlag)
                  (σ2 : ExecConf),
                  ⌜step (Executable, σ1) (e2, σ2)⌝ -∗
                                                   £ 1 ={E}=∗ state_interp_logical σ2 ∗ from_option Φ False (language.to_val (Instr e2))))
        ⊢ wp s E (Instr Executable) Φ.
  Proof.
    iIntros "H".
    iApply wp_cap_lang; first easy.
    iIntros (σ1) "Hσ1".
    iMod ("H" $! _ with "Hσ1") as "H".
    iModIntro. iSplitR.
    { iPureIntro. apply normal_always_head_reducible. }
    iModIntro.
    iIntros (e2 σ2) "%Hstep".
    destruct (prim_step_exec_inv _ _ _ _ _ Hstep) as (_ & _ & c & -> & Hstep2).
    now iApply "H".
  Qed.

  Program Definition wp_lift_atomic_head_step_no_fork_determ {s E Φ} e1 :
    to_val e1 = None →
    (∀ (σ1:cap_lang.state) ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
     ∃ κ e2 (σ2:cap_lang.state) efs, ⌜cap_lang.prim_step e1 σ1 κ e2 σ2 efs⌝ ∗
      (▷ |==> (state_interp σ2 (S ns) κs nt ∗ from_option Φ False (to_val e2))))
      ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns κ κs nt)  "Hσ1 /=".
    iMod ("H" $! σ1 ns κ κs nt with "[Hσ1]") as "H"; auto.
    iDestruct "H" as (κ' e2 σ2 efs) "[H1 H2]".
    iModIntro. iSplit.
    - rewrite /head_reducible /=.
      iExists κ', e2, σ2, efs. auto.
    - iNext. iIntros (? ? ?) "H".
      iDestruct "H" as %Hs1.
      iDestruct "H1" as %Hs2.
      destruct (cap_lang_determ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2) as [Heq1 [Heq2 [Heq3 Heq4]]].
      subst. iMod "H2". iIntros "_".
      iModIntro. iFrame. inv Hs1; auto.
  Qed.

  (* -------------- predicates on memory maps -------------------------- *)

  Lemma extract_sep_if_split (a pc_a : LAddr) P Q R:
     (if (a =? pc_a)%la then P else Q ∗ R)%I ≡
     ((if (a =? pc_a)%la then P else Q) ∗
     if (a =? pc_a)%la then emp else R)%I.
  Proof.
    destruct (a =? pc_a)%la; auto.
    iSplit; auto. iIntros "[H1 H2]"; auto.
  Qed.

  Lemma memMap_resource_0  :
        True ⊣⊢ ([∗ map] la↦w ∈ ∅, la ↦ₐ w).
  Proof.
    by rewrite big_sepM_empty.
  Qed.

  Lemma memMap_resource_1 (a : LAddr) (w : LWord)  :
        a ↦ₐ w  ⊣⊢ ([∗ map] la↦w ∈ <[a:=w]> ∅, la ↦ₐ w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_1_dq (a : LAddr) (w : LWord) dq :
        a ↦ₐ{dq} w  ⊣⊢ ([∗ map] la↦w ∈ <[a:=w]> ∅, la ↦ₐ{dq} w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite big_sepM_empty.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_2ne (a1 a2 : LAddr) (w1 w2 : LWord)  :
    a1 ≠ a2 → ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↦ₐ w)%I ⊣⊢ a1 ↦ₐ w1 ∗ a2 ↦ₐ w2.
  Proof.
    intros.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite (big_sepM_delete _ _ a2 w2); rewrite delete_insert; try by rewrite lookup_insert_ne. 2: by rewrite lookup_insert.
    rewrite delete_insert; auto.
    rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iDestruct "HH" as "[H1 [H2 _ ] ]".  iFrame.
    - iDestruct "HH" as "[H1 H2]". iFrame.
  Qed.

  Lemma address_neq la1 la2 lw1 lw2 :
    la1 ↦ₐ lw1 -∗ la2 ↦ₐ lw2 -∗ ⌜la1 ≠ la2⌝.
  Proof.
    iIntros "Ha1 Ha2".
    destruct (finz_eq_dec la1.1 la2.1); auto; subst;
    destruct (Nat.eq_dec la1.2 la2.2); auto; subst;
      try (iPureIntro; congruence).
    iExFalso.
    replace la1 with la2.
    iApply (addr_dupl_false with "[$Ha1] [$Ha2]").
    auto.
    by apply injective_projections.
  Qed.

  Lemma memMap_resource_2ne_apply (la1 la2 : LAddr) (lw1 lw2 : LWord)  :
    la1 ↦ₐ lw1
    -∗ la2 ↦ₐ lw2
    -∗ ([∗ map] la↦lw ∈  <[la1:=lw1]> (<[la2:=lw2]> ∅), la ↦ₐ lw) ∗ ⌜la1 ≠ la2⌝.
  Proof.
    iIntros "Hi Hr2a".
    iDestruct (address_neq  with "Hi Hr2a") as %Hne; auto.
    iSplitL; last by auto.
    iApply memMap_resource_2ne; auto. iSplitL "Hi"; auto.
  Qed.

  Lemma memMap_resource_2gen (la1 la2 : LAddr) (lw1 lw2 : LWord)  :
    ( ∃ lmem, ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∧
       ⌜ if  (la2 =? la1)%la
       then lmem = (<[la1:=lw1]> ∅)
       else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)⌝
    )%I ⊣⊢ (la1 ↦ₐ lw1 ∗ if (la2 =? la1)%la then emp else la2 ↦ₐ lw2) .
  Proof.
    destruct (la2 =? la1)%la eqn:Heq.
    - apply andb_true_iff in Heq ; destruct Heq as [HeqZ HeqV].
      apply Z.eqb_eq, finz_to_z_eq in HeqZ. apply Nat.eqb_eq in HeqV.
      assert (la2 = la1) by (by apply injective_projections).
      rewrite memMap_resource_1.
      iSplit.
      * iDestruct 1 as (lmem) "[HH ->]".  by iSplit.
      * iDestruct 1 as "[Hmap _]". iExists (<[la1:=lw1]> ∅); iSplitL; auto.
    - apply laddr_neq in Heq.
      rewrite -memMap_resource_2ne; auto ; try congruence.
      iSplit.
      + iDestruct 1 as (mem) "[HH ->]" ; done.
      + iDestruct 1 as "Hmap"; iExists (<[la1:=lw1]> (<[la2:=lw2]> ∅)); iSplitL; auto.
  Qed.

  Lemma memMap_resource_2gen_d
    (Φ : LAddr → LWord → iProp Σ)
    (la1 la2 : LAddr) (lw1 lw2 : LWord) :
    ( ∃ lmem, ([∗ map] la↦lw ∈ lmem, Φ la lw) ∧
       ⌜ if (la2 =? la1)%la
       then lmem =  (<[la1:=lw1]> ∅)
       else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)⌝
    ) -∗ (Φ la1 lw1 ∗ if (la2 =? la1)%la then emp else Φ la2 lw2) .
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (lmem) "[Hmem Hif]".
    destruct ((la2 =? la1)%la) eqn:Heq.
    - iDestruct "Hif" as %->.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne;auto. apply laddr_neq in Heq; congruence. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.

  Lemma memMap_resource_2gen_d_dq (Φ : LAddr → dfrac → LWord → iProp Σ)
    (la1 la2 : LAddr) (dq1 dq2 : dfrac) (lw1 lw2 : LWord)  :
    ( ∃ lmem dfracs, ([∗ map] la↦dlw ∈ prod_merge dfracs lmem, Φ la dlw.1 dlw.2) ∧
       ⌜ (if  (la2 =? la1)%la
          then lmem = <[la1:=lw1]> ∅
          else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)) ∧
       (if  (la2 =? la1)%la
       then dfracs = <[la1:=dq1]> ∅
       else dfracs = <[la1:=dq1]> (<[la2:=dq2]> ∅))⌝
    ) -∗ (Φ la1 dq1 lw1 ∗ if (la2 =? la1)%la then emp else Φ la2 dq2 lw2) .
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (mem dfracs) "[Hmem [Hif Hif'] ]".
    destruct ((la2 =? la1)%la) eqn:Heq.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,lw1));auto. rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,lw1));auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,lw2));auto.
      rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne;auto. apply laddr_neq in Heq; congruence. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.

  (* Not the world's most beautiful lemma, but it does avoid us having to fiddle around with a later under an if in proofs *)
  Lemma memMap_resource_2gen_clater (la1 la2 : LAddr) (lw1 lw2 : LWord) (Φ : LAddr -> LWord -> iProp Σ) :
    (▷ Φ la1 lw1)
    -∗ (if (la2 =? la1)%la then emp else ▷ Φ la2 lw2)
    -∗ (∃ lmem, ▷ ([∗ map] la↦lw ∈ lmem, Φ la lw) ∗
                  ⌜if  (la2 =? la1)%la
        then lmem = <[la1:=lw1]> ∅
        else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)⌝
       )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (la2 =? la1)%la eqn:Heq.
    - iExists (<[la1:= lw1]> ∅); iSplitL; auto. iNext. iApply big_sepM_insert;[|by iFrame].
      auto.
    - iExists (<[la1:=lw1]> (<[la2:=lw2]> ∅)); iSplitL; auto.
      iNext.
      iApply big_sepM_insert;[|iFrame].
      { rewrite lookup_insert_ne;auto. apply laddr_neq in Heq; congruence. }
      iApply big_sepM_insert;[|by iFrame]. auto.
  Qed.

  (* More general lemmas *)
   Lemma memMap_resource_2gen_clater_dq (la1 la2 : LAddr) (dq1 dq2 : dfrac) (lw1 lw2 : LWord) (Φ : LAddr -> dfrac → LWord -> iProp Σ)  :
    (▷ Φ la1 dq1 lw1) -∗
    (if (la2 =? la1)%la then emp else ▷ Φ la2 dq2 lw2) -∗
    (∃ lmem dfracs, ▷ ([∗ map] la↦dlw ∈ prod_merge dfracs lmem, Φ la dlw.1 dlw.2) ∗
       ⌜(if  (la2 =? la1)%la
       then lmem = <[la1:=lw1]> ∅
       else lmem = <[la1:=lw1]> (<[la2:=lw2]> ∅)) ∧
       (if  (la2 =? la1)%la
       then dfracs = (<[la1:=dq1]> ∅)
       else dfracs = <[la1:=dq1]> (<[la2:=dq2]> ∅))⌝
    )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (la2 =? la1)%la eqn:Heq.
    - iExists (<[la1:= lw1]> ∅),(<[la1:= dq1]> ∅); iSplitL; auto. iNext.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,lw1));auto. rewrite merge_empty.
      iApply big_sepM_insert;[|by iFrame].
      auto.
    - iExists (<[la1:=lw1]> (<[la2:=lw2]> ∅)),(<[la1:=dq1]> (<[la2:=dq2]> ∅)); iSplitL; auto.
      iNext.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,lw1));auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,lw2));auto.
      rewrite merge_empty.
      iApply big_sepM_insert;[|iFrame].
      { rewrite lookup_insert_ne;auto. apply laddr_neq in Heq; congruence. }
      iApply big_sepM_insert;[|by iFrame]. auto.
  Qed.

  Lemma memMap_delete:
    ∀ (la : LAddr) (lw : LWord) lmem,
      lmem !! la = Some lw →
      ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw)
      ⊣⊢ (la ↦ₐ lw ∗ ([∗ map] k↦y ∈ delete la lmem, k ↦ₐ y)).
  Proof.
    intros la lw lmem Hmem.
    rewrite -(big_sepM_delete _ _ la); auto.
  Qed.

 Lemma mem_remove_dq lmem dq :
    ([∗ map] la↦lw ∈ lmem, la ↦ₐ{dq} lw) ⊣⊢
    ([∗ map] la↦dw ∈ (prod_merge (create_gmap_default (elements (dom lmem)) dq) lmem), la ↦ₐ{dw.1} dw.2).
  Proof.
    iInduction (lmem) as [|la k lmem] "IH" using map_ind.
    - rewrite big_sepM_empty dom_empty_L elements_empty
              /= /prod_merge merge_empty big_sepM_empty. done.
    - rewrite dom_insert_L.
      assert (elements ({[la]} ∪ dom lmem) ≡ₚ la :: elements (dom lmem)) as Hperm.
      { apply elements_union_singleton. apply not_elem_of_dom. auto. }
      apply (create_gmap_default_permutation _ _ dq) in Hperm. rewrite Hperm /=.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq,k)) //.
      iSplit.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        iApply big_sepM_insert.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom lmem)) dq !! la);auto; rewrite H2;auto. }
        iFrame. iApply "IH". iFrame.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom lmem)) dq !! la);auto; rewrite H2;auto. }
        iApply big_sepM_insert. auto.
        iFrame. iApply "IH". iFrame.
  Qed.

  (* a more general version of load to work also with any fraction and persistent points tos *)
  Lemma gen_mem_valid_inSepM_general:
    ∀ (lmem : gmap LAddr (dfrac * LWord)) (lmem' : LMem)
      (la : LAddr) (lw : LWord) (dq : dfrac),
      lmem !! la = Some (dq, lw) →
      gen_heap_interp lmem'
      -∗ ([∗ map] a↦dqw ∈ lmem, a ↦ₐ{ dqw.1 } dqw.2)
      -∗ ⌜lmem' !! la = Some lw⌝.
  Proof.
    iIntros (lmem lmem' la lw dq Hmem_pc) "Hm Hmem".
    iDestruct (big_sepM_delete _ _ la with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto.
  Qed.

  Lemma gen_mem_valid_inSepM:
    ∀ (lmem lm : LMem) (la : LAddr) (lw : LWord),
      lmem !! la = Some lw →
      gen_heap_interp lm
      -∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw)
      -∗ ⌜lm !! la = Some lw⌝.
  Proof.
    iIntros (lmem lm la lw Hmem_pc) "Hm Hmem".
    iDestruct (memMap_delete la with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto.
  Qed.

  Lemma gen_mem_update_inSepM :
    ∀ {Σ : gFunctors} {gen_heapG0 : gen_heapGS Addr Word Σ}
      (lmem lmem': LMem) (la : LAddr) (lw lw' : LWord),
      lmem' !! la = Some lw' →
      gen_heap_interp lmem
      -∗ ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw)
      ==∗ gen_heap_interp (<[la:=lw]> lmem)
          ∗ ([∗ map] a↦w ∈ <[la:=lw]> lmem', a ↦ₐ w).
  Proof.
    intros.
    rewrite (big_sepM_delete _ _ la);[|eauto].
    iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]"; eauto.
    iModIntro.
    iSplitL "Hh"; eauto.
    iDestruct (big_sepM_insert _ _ la with "[$Hmap $Hl]") as "H".
    apply lookup_delete.
    rewrite insert_delete_insert. iFrame.
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)
  (* Bind Scope expr_scope with language.expr cap_lang. *)

  Lemma wp_notCorrectPC:
    forall E (lw : LWord),
      ~ isCorrectLPC lw ->
      {{{ PC ↦ᵣ lw }}}
         Instr Executable @ E
        {{{ RET FailedV; PC ↦ᵣ lw }}}.
  Proof.
    intros * Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "Hσ1 /="; destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap) "(Hr & Hm & %HLinv)".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iApply fupd_frame_l.
    iSplit. by iPureIntro; apply normal_always_head_reducible.
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    2: eapply state_corresponds_reg_get_word; eauto.
    2: intro contra; apply isCorrectLPC_isCorrectPC_iff in contra; auto.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn.
    iSplitR "Hϕ HPC"; last by iApply "Hϕ".
    iExists lr, lm, vmap.
    iFrame; auto.
  Qed.

  (* Subcases for respecitvely permissions and bounds *)

  Lemma wp_notCorrectPC_perm E pc_p pc_b pc_e pc_a pc_v :
      pc_p ≠ RX ∧ pc_p ≠ RWX →
      {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]") ; [eapply not_isCorrectLPC_perm; eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  Lemma wp_notCorrectPC_range E pc_p pc_b pc_e pc_a pc_v :
    ¬ (pc_b <= pc_a < pc_e)%a →
    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]") ; [eapply not_isCorrectLPC_bounds; eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_b pc_e pc_a pc_v lw :

    decodeInstrWL lw = Halt →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v) ∗ (pc_a, pc_v) ↦ₐ lw }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v) ∗ (pc_a, pc_v) ↦ₐ lw }}}.

  Proof.
    intros Hinstr Hvpc. apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto.
    2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)))
    ; eapply state_corresponds_reg_get_word ; eauto.
    2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto.
    cbn in Hstep. simplify_eq.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn.
    iSplitR "Hφ Hpc Hpca"; last (iApply "Hφ" ; iFrame).
    iExists lr, lm, vmap.
    iFrame; auto.
  Qed.

  Lemma wp_fail E pc_p pc_b pc_e pc_a pc_v lw :

    decodeInstrWL lw = Fail →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v) ∗ (pc_a, pc_v) ↦ₐ lw }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v) ∗ (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    intros Hinstr Hvpc. apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto.
    2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)))
    ; eapply state_corresponds_reg_get_word ; eauto.
    2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto.
    cbn in Hstep. simplify_eq.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn.
    iSplitR "Hφ Hpc Hpca"; last (iApply "Hφ" ; iFrame).
    iExists lr, lm, vmap.
    iFrame; auto.
   Qed.

  (* ----------------------------------- PURE RULES ---------------------------------- *)

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_exec_pure := intros ?; apply nsteps_once, pure_head_step_pure_step;
                                constructor; [solve_exec_safe|]; intros;
                                (match goal with
                                | H : head_step _ _ _ _ _ _ |- _ => inversion H end).

  Global Instance pure_seq_failed :
    PureExec True 1 (Seq (Instr Failed)) (Instr Failed).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_halted :
    PureExec True 1 (Seq (Instr Halted)) (Instr Halted).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_done :
    PureExec True 1 (Seq (Instr NextI)) (Seq (Instr Executable)).
  Proof. by solve_exec_pure. Qed.

End cap_lang_rules.

(* Used to close the failing cases of the ftlr.
  - Hcont is the (iris) name of the closing hypothesis (usually "Hφ")
  - fail_case_name is one constructor of the spec_name,
    indicating the appropriate error case
 *)
Ltac iFailCore fail_case_name :=
      iPureIntro;
      econstructor; eauto;
      eapply fail_case_name ; eauto.

Ltac iFailWP Hcont fail_case_name :=
  by (cbn; iFrame; iApply Hcont; iFrame; iFailCore fail_case_name).

(* ----------------- useful definitions to factor out the wp specs ---------------- *)

(*--- register equality ---*)
  Lemma addr_ne_reg_ne {regs : leibnizO Reg} {r1 r2 : RegName}
        {p0 b0 e0 a0 p b e a}:
    regs !! r1 = Some (WCap p0 b0 e0 a0)
    → regs !! r2 = Some (WCap p b e a)
    → a0 ≠ a → r1 ≠ r2.
  Proof.
    intros Hr1 Hr2 Hne.
    destruct (decide (r1 = r2)); simplify_eq; auto.
  Qed.

(*--- regs_of ---*)

Definition regs_of_argument (arg: Z + RegName): gset RegName :=
  match arg with
  | inl _ => ∅
  | inr r => {[ r ]}
  end.

Definition regs_of (i: instr): gset RegName :=
  match i with
  | Lea r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | GetP r1 r2 => {[ r1; r2 ]}
  | GetB r1 r2 => {[ r1; r2 ]}
  | GetE r1 r2 => {[ r1; r2 ]}
  | GetA r1 r2 => {[ r1; r2 ]}
  | GetOType dst src => {[ dst; src ]}
  | GetWType dst src => {[ dst; src ]}
  | Add r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Sub r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Lt r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Mov r arg => {[ r ]} ∪ regs_of_argument arg
  | Restrict r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Subseg r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Load r1 r2 => {[ r1; r2 ]}
  | Store r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Jnz r1 r2 => {[ r1; r2 ]}
  | Seal dst r1 r2 => {[dst; r1; r2]}
  | UnSeal dst r1 r2 => {[dst; r1; r2]}
  | IsUnique dst src => {[dst; src]}
  (* TODO @Denis add enclaves instructions here *)
  | _ => ∅
  end.

Lemma indom_regs_incl D (regs regs': Reg) :
  D ⊆ dom regs →
  regs ⊆ regs' →
  ∀ r, r ∈ D →
       ∃ (w:Word), (regs !! r = Some w) ∧ (regs' !! r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (regs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset RegName). typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
Qed.

Lemma indom_lregs_incl D (lregs lregs': LReg) :
  D ⊆ dom lregs →
  lregs ⊆ lregs' →
  ∀ r, r ∈ D →
       ∃ (w:LWord), (lregs !! r = Some w) ∧ (lregs' !! r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (lregs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset RegName). typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
  Qed.

(*--- incrementPC ---*)

Definition incrementPC (regs: Reg) : option Reg :=
  match regs !! PC with
  | Some (WCap p b e a) =>
    match (a + 1)%a with
    | Some a' => Some (<[ PC := WCap p b e a' ]> regs)
    | None => None
    end
  | _ => None
  end.

Lemma incrementPC_Some_inv regs regs' :
  incrementPC regs = Some regs' ->
  exists p b e a a',
    regs !! PC = Some (WCap p b e a) ∧
    (a + 1)%a = Some a' ∧
    regs' = <[ PC := WCap p b e a' ]> regs.
Proof.
  unfold incrementPC.
  destruct (regs !! PC) as [ [ | [? ? ? u | ] | ] | ];
    try congruence.
  case_eq (u+1)%a; try congruence. intros ? ?. inversion 1.
  do 5 eexists. split; eauto.
Qed.

Lemma incrementPC_None_inv regs pg b e a :
  incrementPC regs = None ->
  regs !! PC = Some (WCap pg b e a) ->
  (a + 1)%a = None.
Proof.
  unfold incrementPC.
  destruct (regs !! PC) as [ [ | [? ? ? u | ] | ] |];
    try congruence.
  case_eq (u+1)%a; congruence.
Qed.

Lemma incrementPC_overflow_mono regs regs' :
  incrementPC regs = None →
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  incrementPC regs' = None.
Proof.
  intros Hi HPC Hincl. unfold incrementPC in *. destruct HPC as [c HPC].
  pose proof (lookup_weaken _ _ _ _ HPC Hincl) as HPC'.
  rewrite HPC HPC' in Hi |- *. destruct c as [| [? ? ? aa | ] | ]; auto.
  destruct (aa+1)%a; last by auto. congruence.
Qed.

Lemma incrementPC_overflow_antimono regs regs' :
  incrementPC regs = None →
  regs' ⊆ regs →
  incrementPC regs' = None.
Proof.
  intros Hi Hincl. unfold incrementPC in *.
  destruct (regs' !! PC) eqn:HrpPC; last easy.
  rewrite (lookup_weaken _ _ _ _ HrpPC Hincl) in Hi.
  destruct w; try easy.
  destruct sb; try easy.
  now destruct (f1 + 1)%a.
Qed.

(* todo: instead, define updatePC on top of incrementPC *)
Lemma incrementPC_fail_updatePC regs m etbl ecur:
   incrementPC regs = None ->
   updatePC {| reg := regs; mem := m; etable := etbl ; enumcur := ecur |} = None.
Proof.
   rewrite /incrementPC /updatePC /=.
   destruct (regs !! PC) as [X|]; auto.
   destruct X as [| [? ? ? a' | ] |]; auto.
   destruct (a' + 1)%a; auto. congruence.
Qed.

Lemma incrementPC_success_updatePC regs m etbl ecur regs' :
  incrementPC regs = Some regs' ->
  ∃ p b e a a',
    regs !! PC = Some (WCap p b e a) ∧
    (a + 1)%a = Some a' ∧
    updatePC {| reg := regs; mem := m; etable := etbl ; enumcur := ecur |} =
      Some (NextI,
          {| reg := <[ PC := WCap p b e a' ]> regs; mem := m; etable := etbl ; enumcur := ecur |}) ∧
    regs' = <[ PC := WCap p b e a' ]> regs.
Proof.
  rewrite /incrementPC /updatePC /update_reg /=.
  destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
  destruct X as [| [? ? ? a'|]|] eqn:?; try congruence; [].
  destruct (a' + 1)%a eqn:?; [| congruence]. inversion 1; subst regs'.
  do 5 eexists. repeat split; auto.
Qed.

Lemma updatePC_success_incl m m' regs regs' etbl etbl' ecur ecur' w :
  regs ⊆ regs' →
  updatePC {| reg := regs; mem := m; etable := etbl ; enumcur := ecur |}
    = Some (NextI, {| reg := <[ PC := w ]> regs; mem := m; etable := etbl ; enumcur := ecur |}) →
  updatePC {| reg := regs'; mem := m'; etable := etbl' ; enumcur := ecur' |}
  = Some (NextI, {| reg := <[ PC := w ]> regs'; mem := m'; etable := etbl' ; enumcur := ecur' |}).
Proof.
  intros * Hincl Hu. rewrite /updatePC /= in Hu |- *.
  destruct (regs !! PC) as [ w1 |] eqn:Hrr.
  { pose proof (lookup_weaken _ _ _ _ Hrr Hincl) as Hregs'. rewrite Hregs'.
    destruct w1 as [|[ ? ? ? a1|] | ]; simplify_eq.
    destruct (a1 + 1)%a eqn:Ha1; simplify_eq. rewrite /update_reg /=.
    f_equal. f_equal.
    assert (HH: forall (reg1 reg2:Reg), reg1 = reg2 -> reg1 !! PC = reg2 !! PC)
      by (intros * ->; auto).
    unfold update_reg in Hu; cbn in Hu.
    injection Hu; intros.
    apply HH in H. rewrite !lookup_insert in H. by simplify_eq. }
  {  inversion Hu. }
Qed.

Lemma updatePC_fail_incl m m' regs regs' etbl etbl' ecur ecur'  :
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  updatePC {| reg := regs; mem := m; etable := etbl ; enumcur := ecur |} = None →
  updatePC {| reg := regs'; mem := m'; etable := etbl' ; enumcur := ecur' |} = None.
Proof.
  intros [w HPC] Hincl Hfail. rewrite /updatePC /= in Hfail |- *.
  rewrite !HPC in Hfail. have -> := lookup_weaken _ _ _ _ HPC Hincl.
  destruct w as [| [? ? ? a1 | ] |]; simplify_eq; auto;[].
  destruct (a1 + 1)%a; simplify_eq; auto.
Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H
  end; simplify_eq.

Lemma updatePC_incrementPC {φ} :
  updatePC φ =
    r' ← incrementPC (reg φ) ;
    Some (NextI , update_regs φ r').
Proof.
  unfold updatePC, incrementPC.
  destruct (reg φ !! PC); try now cbn.
  unfold update_reg, update_regs.
  destruct w; try now cbn.
  destruct sb; try now cbn.
  destruct (f1 + 1)%a; try now cbn.
Qed.

(*--- incrementLPC ---*)

Definition incrementLPC (regs: LReg) : option LReg :=
  match regs !! PC with
  | Some (LCap p b e a v) =>
    match (a + 1)%a with
    | Some a' => Some (<[ PC := LCap p b e a' v ]> regs)
    | None => None
    end
  | _ => None
  end.

(* Lemma incrementLPC_incrementPC_some regs regs' : *)
(*   incrementLPC regs = Some regs' -> *)
(*   incrementPC (lreg_strip regs) = Some (lreg_strip regs'). *)
(* Proof. *)
(*   rewrite /incrementPC /incrementLPC. *)
(*   intros Hlpc. *)
(*   rewrite /lreg_strip lookup_fmap; cbn. *)
(*   destruct (regs !! PC) as [lw|] eqn:Heq ; rewrite Heq; cbn in *; last done. *)
(*   destruct_lword lw; cbn in *; try done. *)
(*   destruct (a + 1)%a; last done. *)
(*   simplify_eq. *)
(*   by rewrite fmap_insert. *)
(* Qed. *)

(* Lemma incrementLPC_incrementPC_none regs : *)
(*   incrementLPC regs = None <-> incrementPC (lreg_strip regs) = None. *)
(* Proof. *)
(*   intros. *)
(*   rewrite /incrementPC /incrementLPC. *)
(*   rewrite /lreg_strip lookup_fmap; cbn. *)
(*   destruct (regs !! PC) as [LX|] eqn:Heq ; rewrite Heq; cbn; last done. *)
(*   destruct LX ; cbn ; [(clear; firstorder) | | (clear; firstorder)]. *)
(*   destruct sb as [? ? ? a' | ] ; eauto; cbn; last done. *)
(*   destruct (a' + 1)%a eqn:Heq'; done. *)
(* Qed. *)

(* Lemma incrementLPC_fail_updatePC regs m etbl ecur: *)
(*   incrementLPC regs = None -> *)
(*   updatePC {| reg := (lreg_strip regs); mem := m; etable := etbl ; enumcur := ecur |} = None. *)
(* Proof. *)
(*   intro Hincr. apply incrementLPC_incrementPC_none in Hincr. *)
(*   by apply incrementPC_fail_updatePC. *)
(* Qed. *)

Lemma incrementLPC_Some_inv lregs lregs' :
  incrementLPC lregs = Some lregs' ->
  exists p b e a v a',
    lregs !! PC = Some (LCap p b e a v) ∧
      (a + 1)%a = Some a' ∧
      lregs' = <[ PC := (LCap p b e a' v) ]> lregs.
Proof.
  rewrite /incrementLPC.
  destruct (lregs !! PC) as [ [ | [? ? ? u ? | ] | ] | ]; try congruence.
  case_eq (u+1)%a; try congruence.
  intros ? ?. inversion 1.
  do 6 eexists. split; eauto.
Qed.

Lemma incrementLPC_None_inv lregs pg b e a v :
  incrementLPC lregs = None ->
  lregs !! PC = Some (LCap pg b e a v) ->
  (a + 1)%a = None.
Proof.
  unfold incrementLPC.
  destruct (lregs !! PC) as [ [ | [? ? ? u ? | ] | ] |]; try congruence.
  case_eq (u+1)%a; congruence.
Qed.

(* Lemma incrementLPC_success_updatePC regs m etbl ecur regs' : *)
(*   incrementLPC regs = Some regs' -> *)
(*   ∃ p b e a a' (v : Version), *)
(*     regs !! PC = Some (LCap p b e a v) ∧ *)
(*       (a + 1)%a = Some a' ∧ *)
(*       updatePC {| reg := (lreg_strip regs); mem := m; etable := etbl ; enumcur := ecur |} = *)
(*         Some (NextI, *)
(*             {| reg := (<[PC:=WCap p b e a']> (lreg_strip regs)); *)
(*               mem := m; *)
(*               etable := etbl ; *)
(*               enumcur := ecur |}) *)
(*     ∧ regs' = <[ PC := (LCap p b e a' v) ]> regs. *)
(* Proof. *)
(*   intro Hincr. *)
(*   opose proof (incrementLPC_incrementPC_some _ _ Hincr) as HincrPC. *)
(*   eapply (incrementPC_success_updatePC _ m etbl ecur) in HincrPC. *)
(*   destruct HincrPC as (p'&b'&e'&a''&a'''&Hregs&Heq&Hupd&Hregseq). *)
(*   rewrite /incrementLPC in Hincr. *)
(*   destruct (regs !! PC) as [wpc |]; last done. *)
(*   destruct_lword wpc; try done. *)
(*   destruct (a + 1)%a as [a'|] eqn:Heq'; last done; simplify_eq. *)
(*   rewrite /lreg_strip fmap_insert //= -/(lreg_strip regs)  in Hregseq. *)
(*   exists p, b, e, a, a', v. *)
(*   repeat (split; try done). *)
(*   by rewrite Hupd Hregseq. *)
(* Qed. *)

Ltac incrementLPC_inv :=
  match goal with
  | H : incrementLPC _ = Some _ |- _ =>
    apply incrementLPC_Some_inv in H as (?&?&?&?&?&?&?&?&?)
  | H : incrementLPC _ = None |- _ =>
    eapply incrementLPC_None_inv in H
  end; simplify_eq.

Tactic Notation "incrementLPC_inv" "as" simple_intropattern(pat):=
  match goal with
  | H : incrementLPC _ = Some _ |- _ =>
    apply incrementLPC_Some_inv in H as pat
  | H : incrementLPC _ = None |- _ =>
    eapply incrementLPC_None_inv in H
  end; simplify_eq.

Section cap_lang_rules_opt.
  Context `{MachineParameters}.
  Context `{memG Σ, regG Σ}.

  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types la: LAddr.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.


  Definition wp_opt {A} (φ : option A) (Φf : iProp Σ) (Φs : A -> iProp Σ) : iProp Σ :=
    match φ with
      None => Φf
    | Some φ' => Φs φ'
    end.

  Lemma wp_opt_unfold {A} {φ : option A} {Φf Φs} :
    (⌜ φ = None ⌝ -∗ Φf) ∧ (∀ x, ⌜ φ = Some x ⌝ -∗ Φs x)
    ⊢ wp_opt φ Φf Φs.
  Proof.
    iIntros "H".
    destruct φ; [rewrite bi.and_elim_r| rewrite bi.and_elim_l];
      now iApply "H".
  Qed.

  Lemma wp_opt_eqn {A} (φ : option A) (Φf : iProp Σ) (Φs : A -> iProp Σ) :
    wp_opt φ Φf (fun x => ⌜ φ = Some x ⌝ → Φs x) ⊢ wp_opt φ Φf Φs.
  Proof.
    destruct φ; cbn; last done.
    iIntros "Hk".
    now iApply "Hk".
  Qed.

  Lemma wp_opt_is_Some {A Φs Φf} {φ : option A} : is_Some (φ) -> wp_opt φ Φf Φs ⊢ wp_opt φ False Φs.
  Proof.
    destruct φ; first by cbn.
    now inversion 1.
  Qed.

  Lemma wp_opt_univ {A Φs} {φ : option A} : (∀ x, Φs x) ⊢ wp_opt φ True Φs.
  Proof.
    iIntros "H".
    now destruct φ.
  Qed.

  Lemma wp_opt_bind {A B} {φ : option A} {K : A -> option B} {Φf Φs} :
    wp_opt φ Φf (fun φ' => wp_opt (K φ') Φf Φs) ⊣⊢
      wp_opt (φ ≫= K) Φf Φs.
  Proof.
    destruct φ; now cbn.
  Qed.

  Lemma wp_opt_mono {A} {m : option A} {Φf Φs1 Φs2} :
    (∀ x, Φs1 x -∗ Φs2 x) ∗ wp_opt m Φf Φs1 ⊢ wp_opt m Φf Φs2.
  Proof.
    iIntros "(HΦs & Hwp)".
    destruct m; cbn; last done.
    now iApply "HΦs".
  Qed.

  Definition wp_opt2 {A1 A2} Ep (φ1 : option A1) (φ2 : option A2) (Φf : iProp Σ) (Φs : A1 -> A2 -> iProp Σ) : iProp Σ :=
    match φ1 , φ2 with
      None , None => |={Ep}=> Φf
    | Some x1 , Some x2 => |={Ep}=> Φs x1 x2
    | _ , _ => |={Ep}=> False
    end.

  Lemma wp2_diag_univ {A} {φ : option A} {Ep Φf} {Φs : A -> A -> iProp Σ} :
    (Φf ∧ (∀ x, Φs x x)) ⊢ wp_opt2 Ep φ φ Φf Φs.
  Proof.
    destruct φ; [rewrite bi.and_elim_r | rewrite bi.and_elim_l];
      now iIntros "Hk".
  Qed.

  Lemma wp_wp2 {Ep A1 A2} {φ1 : option A1} {φ2 : option A2} {Φf Φs} :
    wp_opt2 Ep φ1 φ2 Φf (fun x1 x2 => Φs x2) ⊢ wp_opt φ2 (|={Ep}=> Φf) (fun x => |={Ep}=> Φs x).
  Proof.
    iIntros "Hk".
    destruct φ1 , φ2; now iMod "Hk" as "Hk".
  Qed.

  Lemma wp2_val {A1 A2} {x1 : A1} {x2 : A2} {Φf Φs Ep} :
    (|={Ep}=> Φs x1 x2) ⊢ wp_opt2 Ep (Some x1) (Some x2) Φf Φs.
  Proof.
    now iIntros "Hk".
  Qed.

  Lemma wp_opt2_eqn {Ep} {A1 A2} {φ1 : option A1} {φ2 : option A2} (Φf : iProp Σ) (Φs : A1 -> A2 -> iProp Σ) :
    wp_opt2 Ep φ1 φ2 Φf (fun x1 x2 => ⌜ φ1 = Some x1 ⌝ → ⌜ φ2 = Some x2 ⌝ → Φs x1 x2) ⊢ wp_opt2 Ep φ1 φ2 Φf Φs.
  Proof.
    destruct φ1, φ2; cbn; try done.
    iIntros "Hk".
    now iApply "Hk".
  Qed.

  Lemma wp_opt2_eqn_both {Ep} {A1 A2} {φ1 : option A1} {φ2 : option A2} (Φf : iProp Σ) (Φs : A1 -> A2 -> iProp Σ) :
    wp_opt2 Ep φ1 φ2 (⌜ φ1 = None ⌝ → ⌜ φ2 = None ⌝ → Φf) (fun x1 x2 => ⌜ φ1 = Some x1 ⌝ → ⌜ φ2 = Some x2 ⌝ → Φs x1 x2) ⊢ wp_opt2 Ep φ1 φ2 Φf Φs.
  Proof.
    destruct φ1, φ2; cbn; try done.
    - iIntros "Hk".
      now iApply "Hk".
    - iIntros "Hk".
      now iApply "Hk".
  Qed.

  Lemma wp_opt2_mod {Ep} {A1 A2} {φ1 : option A1} {φ2 : option A2} {Φf Φs} :
    (|={Ep}=> wp_opt2 Ep φ1 φ2 Φf Φs) ⊢ wp_opt2 Ep φ1 φ2 Φf Φs.
  Proof.
    destruct φ1, φ2;
      now iIntros ">H".
  Qed.

  Lemma wp_opt2_bind {Ep} {A1 A2} {B1 B2} {φ1 : option A1} {φ2 : option A2} {k1 : A1 -> option B1} {k2 : A2 -> option B2} {Φf Φs} :
    wp_opt2 Ep φ1 φ2 Φf (fun x1 x2 => wp_opt2 Ep (k1 x1) (k2 x2) Φf Φs) ⊢
      wp_opt2 Ep (x1 ← φ1 ; k1 x1) (x2 ← φ2 ; k2 x2) Φf Φs.
  Proof.
    iIntros "Hk".
    iApply wp_opt2_mod.
    destruct φ1, φ2; now iMod "Hk" as "Hk".
  Qed.

  Lemma wp_opt2_mono {Ep} {A1 A2} {φ1 : option A1} {φ2 : option A2} {Φf Φsa Φsb} :
    (∀ x1 x2, Φsa x1 x2 -∗ Φsb x1 x2) ∗ wp_opt2 Ep φ1 φ2 Φf Φsa ⊢ wp_opt2 Ep φ1 φ2 Φf Φsb.
  Proof.
    destruct φ1, φ2; cbn; iIntros "(Hab & Hwp)"; try done.
    now iApply "Hab".
  Qed.

  Lemma wp_instr_exec_opt {s E Φ pc_a pc_v dq regs lw pc_p pc_b pc_e instr} :
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    decodeInstrWL lw = instr →
    regs_of instr ⊆ dom regs →
    ((▷ (pc_a, pc_v) ↦ₐ{dq} lw) ∗
     (▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
      ▷ (∀ (σ1 : language.state cap_ectx_lang),
            state_interp_logical σ1 ∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗ (pc_a, pc_v) ↦ₐ{dq} lw ={E}=∗
              (∀ wa,
                  ⌜ (reg σ1) !! PC = Some (WCap pc_p pc_b pc_e pc_a) /\
                    (mem σ1) !! pc_a = Some wa /\
                    isCorrectPC (WCap pc_p pc_b pc_e pc_a) /\
                    decodeInstrW wa = instr ⌝ -∗ £ 1 ={E}=∗
                 wp_opt (exec_opt instr σ1) (|={E}=> state_interp_logical σ1 ∗ Φ FailedV)
                 (fun (c2 : Conf) => |={E}=> (state_interp_logical c2.2 ∗ from_option Φ False (language.to_val (Instr c2.1))))))
        ⊢ wp s E (Instr Executable) Φ).
  Proof.
    iIntros (Hcorrpc Hregspc Hdecode Hregs_incl) "(>Hcode & >Hregs & H)".
    apply isCorrectLPC_isCorrectPC_iff in Hcorrpc; cbn in Hcorrpc.
    iApply wp_instr_exec.
    iIntros (σ1) "Hσ1".
    destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iModIntro.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hregsincl".
    have Hregs_pc := lookup_weaken _ _ _ _ Hregspc Hregsincl.
    iDestruct (@gen_heap_valid with "Hm Hcode") as %Hlcode; auto.
    iModIntro.
    iIntros (e2 σ2 Hstep) "Hcred".
    iMod ("H" $! {| reg := reg; mem := mem; etable := etable; enumcur := enumcur |} with "[Hr Hm $Hregs $Hcode]") as "H".
    { iExists _, _, _. iFrame. iPureIntro. cbn.
      (* TODO: allow changing cur_map? *)
      eassumption.
    }

    eapply step_exec_inv in Hstep; eauto; cbn.
    2: eapply state_corresponds_reg_get_word_cap ; eauto.
    2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto.

    iMod ("H" $! (lword_get_word lw) with "[%] Hcred") as "H".
    { intuition.
      + now eapply (state_corresponds_reg_get_word _ _ _ _ _ _ (LCap pc_p pc_b pc_e pc_a pc_v) HLinv).
      + eapply (state_corresponds_mem_get_word _ _ _ _ _ pc_a pc_v lw HLinv )
        ; try now cbn.
        eapply state_corresponds_cap_cur_word ; [ apply HLinv | | | | apply Hregs_pc | ]
        ; try now cbn.
        eapply (isCorrectPC_withinBounds _ _ _ _ Hcorrpc).
    }
    unfold exec in Hstep.
    destruct (exec_opt instr {| reg := reg; mem := mem; etable := etable; enumcur := enumcur |});
    now inversion Hstep.
  Qed.

  (* Lemma wp_opt_updatePC {φ Φs Φf w E}: *)
  (*   reg φ !! PC = Some w -> *)
  (*     (∀ p b e a a', ⌜ w = WCap p b e a ⌝ -∗ ⌜ (a + 1)%a = Some a' ⌝ -∗ |={E}=> Φs (NextI , update_reg φ PC (WCap p b e a'))) ∧ *)
  (*       (⌜ incrementPC (reg φ) = None ⌝ -∗ Φf) *)
  (*     ⊢ *)
  (*   |={E}=> wp_opt (updatePC φ) Φf Φs. *)
  (* Proof. *)
  (*   unfold updatePC, incrementPC. *)
  (*   iIntros (->) "Hsf". *)
  (*   destruct w eqn:Heqw; iFrame; cbn. *)
  (*   - rewrite bi.and_elim_r. *)
  (*     now iApply "Hsf". *)
  (*   - destruct sb eqn:Heqsb; iFrame; cbn. *)
  (*     + destruct (f1 + 1)%a eqn:Heqf; cbn; iFrame. *)
  (*       {rewrite bi.and_elim_l. *)
  (*        now iApply "Hsf". *)
  (*       } *)
  (*       { rewrite bi.and_elim_r. now iApply "Hsf". } *)
  (*     + rewrite bi.and_elim_r. now iApply "Hsf". *)
  (*   - rewrite bi.and_elim_r. now iApply "Hsf". *)
  (* Qed. *)

  Lemma state_phys_log_corresponds_update_reg {reg mem lr lm cur_map i w lw}:
    lword_get_word lw = w ->
    is_cur_word lw cur_map ->
    state_phys_log_corresponds reg mem lr lm cur_map ->
    state_phys_log_corresponds (<[i := w]> reg) mem (<[i:=lw]> lr) lm cur_map.
  Proof.
    intros Hlw Hcw ((HLreg & HLcurreg) & HLmem).
    split; last easy.
    split.
    - unfold lreg_strip in *.
      now rewrite fmap_insert HLreg Hlw.
    - now apply map_Forall_insert_2.
  Qed.

  Lemma state_phys_log_corresponds_update_mem {reg mem lr lm cur_map la lw}:
    is_cur_addr la cur_map ->
    is_cur_word lw cur_map ->
    state_phys_log_corresponds reg mem lr lm cur_map ->
    state_phys_log_corresponds reg (<[(laddr_get_addr la) := (lword_get_word lw)]> mem) lr (<[la:=lw]> lm) cur_map.
  Proof.
    intros Hcurra Hcurrw (Hreg & Hmemcurr & Hmem).
    split; first easy.
    apply lmem_corresponds_insert_respects; auto.
    unfold mem_phys_log_corresponds; auto.
  Qed.

  Lemma lookup_insert_dec:
    forall {K : Type} {M : forall _ : Type, Type} {H : FMap M} {H0 : forall A : Type, Lookup K A (M A)}
      {H1 : forall A : Type, Empty (M A)} {H2 : forall A : Type, PartialAlter K A (M A)} {H3 : OMap M}
      {H4 : Merge M} {H5 : forall A : Type, MapFold K A (M A)} {EqDecision0 : RelDecision eq}
      {_ : FinMap K M} {A : Type} {m : M A} {i j : K} {x y : A},
      m !! j = Some y ->
      (<[ i := x ]> m) !! j =
        Some (if (bool_decide (i = j)) then x else y).
  Proof.
    intros.
    destruct (bool_decide_reflect (i = j)).
    - subst. now apply lookup_insert.
    - now rewrite lookup_insert_ne.
  Qed.

  Lemma state_interp_transient_corr {φ φt lr lrt lm lmt} :
    state_interp_transient φ φt lr lrt lm lmt ⊢
      ∃ lreg_t lmem_t cur_map,
        ⌜ lrt ⊆ lreg_t ⌝ ∗ ⌜ snd <$> lmt ⊆ lmem_t ⌝ ∗
          ⌜state_phys_log_corresponds φt.(reg) φt.(mem) lreg_t lmem_t cur_map⌝.
  Proof.
    now iIntros "(((Hσ & Hregs & Hmem) & Hcommit) & %Hcor)".
  Qed.
  (* Lemma wp_reg_lookup lrt {r φ φt lr Φs Φf} : *)
  (*   (state_interp_regs_transient φ φt lr lrt ∗ *)
  (*      wp_opt (lrt !! r) False *)
  (*         (fun lwr => state_interp_regs_transient φ φt lr lrt -∗ Φs (lword_get_word lwr))) ⊢ *)
  (*      wp_opt (reg φt !! r) Φf Φs. *)
  (* Proof. *)
  (*   iIntros "(Hσr & Hk)". *)
  (*   iPoseProof (state_interp_regs_transient_corr with "Hσr") as "%Hregs_incl". *)
  (*   destruct (lrt !! r) as [lwr|] eqn:Heqr ; last done. *)
  (*   rewrite map_subseteq_spec in Hregs_incl. *)
  (*   erewrite Hregs_incl. *)
  (*   - now iApply "Hk". *)
  (*   - now rewrite lookup_fmap Heqr. *)
  (* Qed. *)

  Lemma wp2_reg_lookup {Ep} {lrt lmt r φ φt lr lm Φs Φf} :
    r ∈ dom lrt ->
    state_interp_transient φ φt lr lrt lm lmt ∗
      (∀ lwr, state_interp_transient φ φt lr lrt lm lmt -∗ Φs lwr (lword_get_word lwr)) ⊢
      wp_opt2 Ep (lrt !! r) (reg φt !! r) Φf Φs.
  Proof.
    iIntros (Hdom) "(Hσr & Hk)".
    iPoseProof (state_interp_transient_corr with "Hσr") as "%HInv".
    destruct HInv as (lregs_t & lmem_t & cur_map & Hregs_incl & Hmem_incl & HInv).
    destruct (proj1 (elem_of_dom lrt r) Hdom) as (lrw & Hlrt).
    rewrite Hlrt.
    rewrite map_subseteq_spec in  Hregs_incl.
    specialize (Hregs_incl r lrw Hlrt).
    eapply state_corresponds_reg_get_word in Hregs_incl; eauto.
    erewrite Hregs_incl.

  (* Lemma wp_word_of_argument {src lw Φf Φs φ φt lr lrt} : *)
  (*   regs_of_argument src ⊆ dom lrt -> *)
  (*   state_interp_regs_transient φ φt lr lrt ∗ *)
  (*     wp_opt (word_of_argumentL lrt src) False  *)
  (*     (fun lw => state_interp_regs_transient φ φt lr lrt -∗ Φs (lword_get_word lw)) ⊢ *)
  (*     wp_opt (word_of_argument (reg φt) src) Φf Φs. *)
  (* Proof. *)
  (*   iIntros (Hdom) "(Hσr & HΦs)". *)
  (*   destruct src as [z|r]; cbn. *)
  (*   - now iApply ("HΦs" with "Hσr"). *)
  (*   - now iApply (wp_reg_lookup lrt with "[$Hσr $HΦs]"). *)
  (* Qed. *)
    iApply wp2_val. now iApply "Hk".
  Qed.

  Lemma wp2_word_of_argument {Ep} {src lw Φf Φs φ φt lr lrt lm lmt} :
    regs_of_argument src ⊆ dom lrt ->
    state_interp_transient φ φt lr lrt lm lmt ∗
      (∀ lw, state_interp_transient φ φt lr lrt lm lmt -∗ Φs lw (lword_get_word lw))
      ⊢ wp_opt2 Ep (word_of_argumentL lrt src) (word_of_argument (reg φt) src) Φf Φs.
  Proof.
    iIntros (Hdom) "(Hσr & HΦs)".
    destruct src as [z|r]; cbn.
    - now iApply ("HΦs" with "Hσr").
    - iApply (wp2_reg_lookup with "[$Hσr $HΦs]").
      now set_solver.
  Qed.


  Lemma wp2_word_get_cap {Ep} {w Φf Φs} :
         Φf ∧ (∀ p b e a v, Φs (p , b , e , a , v) (p , b , e , a))
      ⊢ wp_opt2 Ep (lword_get_cap w) (get_wcap (lword_get_word w)) Φf Φs.
  Proof.
    iIntros "HΦ".
    destruct w as [z | [p b e a v | x] | w]; cbn.
    all: try now rewrite bi.and_elim_l. all: try now rewrite bi.and_elim_r.
  Qed.

  Lemma wp2_mem_lookup {Ep} {lrt lmt φ φt lr lm Φs Φf r p b e a v lwa} :
    withinBounds b e a = true ->
    lrt !! r = Some (LCap p b e a v) ->
    (snd <$> lmt) !! (a,v) = Some lwa ->
    state_interp_transient φ φt lr lrt lm lmt ∗
    (state_interp_transient φ φt lr lrt lm lmt -∗ Φs lwa (lword_get_word lwa)) ⊢
    wp_opt2 Ep ((snd <$> lmt) !! (a,v)) (mem φt !! a) Φf Φs.
  Proof.
    iIntros (Hin_bounds Hlrt_r Hlmt_a) "(Hσr & Hk)".
    iPoseProof (state_interp_transient_corr with "Hσr") as "%Hcor".
    destruct Hcor as (lr' & lm' & cur_map & Hlrt_incl & Hlmt_incl & Hinv).
    rewrite Hlmt_a.
    eapply lookup_weaken in Hlmt_a, Hlrt_r; eauto.
    eapply state_corresponds_mem_get_word in Hlmt_a; eauto; cbn in Hlmt_a.
    2: { eapply state_corresponds_cap_cur_word; eauto; by cbn. }
    rewrite Hlmt_a.
    iApply wp2_val. now iApply "Hk".
  Qed.

  Lemma wp2_z_of_argument {Ep} {src Φf Φs φ φt lr lrt lm lmt} :
    regs_of_argument src ⊆ dom lrt ->
    state_interp_transient φ φt lr lrt lm  lmt ∗
      (state_interp_transient φ φt lr lrt lm lmt -∗ Φf) ∧
      ((∀ z, state_interp_transient φ φt lr lrt lm lmt -∗ Φs z z))
      ⊢ wp_opt2 Ep (z_of_argumentL lrt src) (z_of_argument (reg φt) src) Φf Φs.
  Proof.
    iIntros (Hregs) "(Hφ & Hk)".
    destruct src; cbn.
    - rewrite bi.and_elim_r. by iApply "Hk".
    - change (wp_opt2 _ _ _ _ _) with
        (wp_opt2 Ep (lrt !! r ≫= fun y => match y with | LInt z => Some z | _ => None end)
           (reg φt !! r ≫= fun y => match y with | WInt z => Some z | _ => None end)
           Φf Φs).
      rewrite <-wp_opt2_bind.
      iApply (wp2_reg_lookup with "[$Hφ Hk]").
      { set_solver. }
      iIntros (lwr) "Hφ".
      destruct lwr; cbn.
      + rewrite bi.and_elim_r. by iApply "Hk".
      + rewrite bi.and_elim_l. by iApply "Hk".
      + rewrite bi.and_elim_l. by iApply "Hk".
  Qed.

  (* More expressive version of update_state_interp_from_reg_nomod.
     This is needed for operations that edit a current (in terms of version) word,
     requiring us to re-prove "currentness" of the edited word.
     Think e.g. shrinking the bounds of a capability read from a register. *)
  Lemma update_state_interp_from_regs_mod {σ dst lw2 Ep lregs}:
    dst ∈ dom lregs ->
    (forall cur_map, is_cur_regs lregs cur_map -> is_cur_word lw2 cur_map) ->
    state_interp_logical σ ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y) ⊢
      |={Ep}=> state_interp_logical (update_reg σ dst (lword_get_word lw2)) ∗
                ([∗ map] k↦y ∈ <[ dst := lw2 ]> lregs, k ↦ᵣ y).
  Proof.
    iIntros (Hdst Hcur) "(Hσ & Hregs)".
    iDestruct "Hσ" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hregs_incl".
    iMod ((gen_heap_update_inSepM _ _ dst lw2) with "Hr Hregs") as "[Hr Hregs]"; eauto.
    { now apply elem_of_dom. }
    iModIntro. iFrame.
    iExists _,_,cur_map; iFrame.
    iPureIntro.
    apply state_phys_log_corresponds_update_reg; try easy.
    eapply Hcur.
    eapply (is_cur_regs_mono Hregs_incl).
    now eapply (proj2 (proj1 HLinv)).
  Qed.

  Lemma update_state_interp_transient_from_regs_mod {σ σt lr lrt lm lmt dst lw2}:
    dst ∈ dom lrt ->
    (forall cur_map, is_cur_regs lrt cur_map -> is_cur_word lw2 cur_map) ->
    state_interp_transient σ σt lr lrt lm lmt ⊢
      state_interp_transient
      σ (update_reg σt dst (lword_get_word lw2))
      lr (<[ dst := lw2 ]> lrt) lm lmt .
  Proof.
    iIntros (Hdom Hcur).
    iIntros "(((Hσ & Hregs & Hmem) & Hcommit) & %Hcor)"; cbn in *.
    iFrame "Hσ Hregs Hmem".
    iSplit.
    - iIntros (Ep) "H".
      iMod ("Hcommit" with "H") as "(Hσ & Hregs & Hmem)".
      iFrame.
      iApply (update_state_interp_from_regs_mod Hdom Hcur with "[$Hσ $Hregs]").
    - iPureIntro; cbn.
      destruct Hcor as (lr' & lm' & cur_map & Hlrt_incl & Hlmt_incl & Hinv).
      exists (<[dst:=lw2]> lr'), lm', cur_map.
      split; auto.
      now apply insert_mono.
      split; auto.
      assert (is_cur_regs lr' cur_map) as Hcur_lr'
          by (by destruct Hinv as [[_ Hcur'] _]).
      eapply is_cur_regs_mono in Hcur_lr'; eauto.
      specialize (Hcur cur_map Hcur_lr').
      destruct Hinv as [Hregs ?] ; split ; auto.
      by apply lreg_corresponds_insert_respects.
  Qed.

  (* This lemma updates the state for operations where a current word is
     immediately moved (to another register). Since the word was not edited,
     and it was read from a register, it is obviously already "current" *)
  Lemma update_state_interp_from_reg_nomod {σ src dst lw Ep regs}:
    dst ∈ dom regs ->
    regs !! src = Some lw ->
    state_interp_logical σ ∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ⊢
      |={Ep}=> state_interp_logical (update_reg σ dst (lword_get_word lw)) ∗
                ([∗ map] k↦y ∈ <[ dst := lw ]> regs, k ↦ᵣ y).
  Proof.
    intros Hdst Hsrc.
    eapply update_state_interp_from_regs_mod; now eauto.
  Qed.

  Lemma update_state_interp_int {σ dst z Ep regs}:
    dst ∈ dom regs ->
    state_interp_logical σ ∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ⊢
      |={Ep}=> state_interp_logical (update_reg σ dst (WInt z)) ∗ ([∗ map] k↦y ∈ <[ dst := LWInt z ]> regs, k ↦ᵣ y).
  Proof.
    intros Hdst.
    eapply (update_state_interp_from_regs_mod (lw2 := LWInt z)); now eauto.
  Qed.

  Lemma update_state_interp_transient_int {σ σt lr lrt lm lmt dst z}:
    dst ∈ dom lrt ->
    state_interp_transient σ σt lr lrt lm lmt ⊢
      state_interp_transient σ (update_reg σt dst (WInt z))
      lr (<[ dst := LWInt z ]> lrt) lm lmt.
  Proof.
    intros Hdom.
    now apply (update_state_interp_transient_from_regs_mod (lw2 := LWInt z) Hdom).
  Qed.

  Lemma update_state_interp_from_cap_mod {σ dst lw2 Ep lregs} {lmem : LMemF} {p b e a v r}:
    dst ∈ dom lregs ->

    lregs !! r = Some (LCap p b e a v) ->
    withinBounds b e a = true ->
    (snd <$> lmem) !! (a, v) = Some lw2 ->

    state_interp_logical σ
      ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y)
      ∗ ([∗ map] la↦dw ∈ lmem, la ↦ₐ{dw.1} dw.2)
      ⊢ |={Ep}=>
          state_interp_logical (update_reg σ dst (lword_get_word lw2))
            ∗ ([∗ map] k↦y ∈ <[ dst := lw2 ]> lregs, k ↦ᵣ y)
            ∗ ([∗ map] la↦dw ∈ lmem, la ↦ₐ{dw.1} dw.2)
  .
  Proof.
    iIntros (Hdst Hr Hinbounds Ha) "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iPoseProof (gen_heap_valid_inclSepM_general with "Hm Hmem") as "%Hlmem_incl".
    iMod ((gen_heap_update_inSepM _ _ dst lw2) with "Hr Hregs") as "[Hr Hregs]"; eauto.
    { now apply elem_of_dom. }
    iModIntro. iFrame.
    iExists _,_,cur_map; iFrame.
    iPureIntro.
    eapply lookup_weaken in Ha ; eauto.
    apply state_phys_log_corresponds_update_reg; try easy.
    destruct HLinv as [Hinv_reg Hinv_mem].
    eapply lmem_corresponds_read_iscur; eauto.
    eapply lookup_weaken in Hr ; eauto.
    eapply state_corresponds_cap_cur_word ; eauto; by cbn.
  Qed.

  Lemma update_state_interp_transient_from_cap_mod
    {σ σt lr lrt lm lmt dst lw2 r p b e a v}:
    dst ∈ dom lrt ->
    lrt !! r = Some (LCap p b e a v) ->
    withinBounds b e a = true ->
    (snd <$> lmt) !! (a, v) = Some lw2 ->
    state_interp_transient σ σt lr lrt lm lmt ⊢
      state_interp_transient
      σ (update_reg σt dst (lword_get_word lw2))
      lr (<[ dst := lw2 ]> lrt) lm lmt.
  Proof.
    iIntros (Hdom Hr Hinbounds Ha) "(((Hσ & Hregs & Hmem) & Hcommit) & %Hcor)"; cbn in *.
    iFrame "Hσ Hregs Hmem".
    iSplitL.
    - iIntros (Ep) "H".
      iMod ("Hcommit" with "H") as "(Hσ & Hregs & Hmem)".
      iApply (update_state_interp_from_cap_mod Hdom Hr Hinbounds Ha with "[$Hσ $Hregs $Hmem]").
    - iPureIntro; cbn.
      destruct Hcor as (lr' & lm' & cur_map & Hlrt_incl & Hlmt_incl & Hinv).
      exists (<[dst:=lw2]> lr'), lm', cur_map.
      split; auto.
      now apply insert_mono.
      split; auto.
      assert (is_cur_regs lr' cur_map) as Hcur_lr'
          by (by destruct Hinv as [[_ Hcur'] _]).
      eapply is_cur_regs_mono in Hcur_lr'; eauto.
      destruct Hinv as [Hregs ?] ; split ; auto.
      eapply lookup_weaken in Ha, Hr ; eauto.
      eapply lmem_corresponds_read_iscur in Ha; eauto.
      by apply lreg_corresponds_insert_respects.
      eapply state_corresponds_cap_cur_word; eauto ; by cbn.
  Qed.

  Lemma update_state_interp_from_mem_mod {σ Ep lregs} {lmem : LMemF} laddr lwold lwnew :
    (forall cur_map, is_cur_regs lregs cur_map -> is_cur_word lwnew cur_map) ->
    (forall cur_map, is_cur_regs lregs cur_map -> is_cur_addr laddr cur_map) ->
    lmem !! laddr = Some (DfracOwn 1, lwold) ->

    state_interp_logical σ
      ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y)
      ∗ ([∗ map] la↦dw ∈ lmem, la ↦ₐ{dw.1} dw.2)
      ⊢ |={Ep}=>
          state_interp_logical (update_mem σ (laddr_get_addr laddr) (lword_get_word lwnew))
            ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y)
            ∗ ([∗ map] la↦dw ∈ <[laddr := (DfracOwn 1, lwnew) ]> lmem, la ↦ₐ{dw.1} dw.2).
  Proof.
    iIntros (Hcurw Hcura Hladdr) "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iPoseProof (gen_heap_valid_inclSepM_general with "Hm Hmem") as "%Hlmem_incl".
    iFrame.
    iMod ((@gen_heap_update_inSepM_general LAddr _ _ _ _ _ _ _ laddr lwnew) with "Hm Hmem") as "[Hm Hmem]"; eauto.
    iModIntro. iFrame.
    iExists _,_,cur_map; iFrame.
    iPureIntro.
    destruct HLinv as [[? Hregscur] Hinv_mem].
    apply state_phys_log_corresponds_update_mem; try easy.
    1: apply Hcura.
    2: apply Hcurw.
    all: apply (is_cur_regs_mono Hlregs_incl); auto.
Qed.

  Lemma update_state_interp_transient_from_mem_mod {σ σt lr lrt} {lm lmt : LMemF} la lw lw' :
    (forall cur_map, is_cur_regs lrt cur_map -> is_cur_word lw cur_map) ->
    (forall cur_map, is_cur_regs lrt cur_map -> is_cur_addr la cur_map) ->
    lmt !! la = Some (DfracOwn 1, lw') ->
    state_interp_transient σ σt lr lrt lm lmt ⊢
    state_interp_transient σ (update_mem σt (laddr_get_addr la) (lword_get_word lw))
                          lr lrt (* registers remain unchanged *)
                          lm (<[ la := (DfracOwn 1, lw)]> lmt).
  Proof.
    iIntros (Hcurw Hcura Hla) "(((Hσ & Hregs & Hmem) & Hcommit) & %Hcor)". cbn in *.
    iFrame "Hσ Hregs Hmem".
    iSplit.
    - iIntros (Ep) "H".
      iMod ("Hcommit" with "H") as "(Hσ & Hregs & Hmem)".
      iApply (update_state_interp_from_mem_mod la lw' lw Hcurw Hcura Hla). iFrame.
    - iPureIntro; cbn.
      destruct Hcor as (lr' & lm' & cur_map & Hlrt_incl & Hlmt_incl & Hinv).
      exists lr', (<[la:=lw]> lm'), cur_map.
      split; auto. split.
      rewrite fmap_insert. cbn.
      apply insert_mono. auto.
      assert (is_cur_regs lr' cur_map) as Hcur_lr'
          by (by destruct Hinv as [[_ Hcur'] _]).
      eapply is_cur_regs_mono in Hcur_lr'; eauto.
      apply state_phys_log_corresponds_update_mem; auto.
  Qed.

  Lemma word_of_argumentL_cur {lregs src lw2 cur_map} :
    word_of_argumentL lregs src = Some lw2 ->
    is_cur_regs lregs cur_map → is_cur_word lw2 cur_map.
  Proof.
    destruct src.
    - now inversion 1.
    - cbn. intros Hreg Hcurregs.
      apply (map_Forall_lookup_1 _ _ _ _ Hcurregs Hreg).
  Qed.

  Lemma cap_of_argumentL_cur {lregs rsrc p b e a v cur_map} :
    word_of_argumentL lregs rsrc = Some (LCap p b e a v) ->
    withinBounds b e a ->
    is_cur_regs lregs cur_map → is_cur_addr (a, v) cur_map.
  Proof.
    intros. apply (cur_lword_cur_addr (LCap p b e a v) p b e). unfold is_lword_version. all: auto.
    eapply word_of_argumentL_cur. eauto. all: auto. now apply Is_true_true_1.
  Qed.

  (* Lemma updatePC_impl {φ} : *)
  (*   updatePC φ = (reg' ← incrementPC (reg φ); Some (NextI , update_regs φ reg')). *)
  (* Proof. *)
  (*   unfold updatePC, incrementPC. *)
  (*   destruct (reg φ !! PC); last done. *)
  (*   destruct w; try done.  *)
  (*   destruct sb; try done. *)
  (*   now destruct (f1 + 1)%a. *)
  (* Qed. *)

  (* Lemma wp_opt_incrementPC {φ φt lr lrt Φs Φf} : *)
  (*   PC ∈ dom lrt -> *)
  (*   state_interp_regs_transient φ φt lr lrt ∗ *)
  (*   (wp_opt (incrementLPC lrt) (∀ φt' lrt', state_interp_regs_transient φ φt' lr lrt' -∗ Φf) *)
  (*      (fun lrt' => ∀ φt', state_interp_regs_transient φ φt' lr lrt' -∗ Φs (reg φt'))) *)
  (*   ⊢ wp_opt (incrementPC (reg φt)) Φf Φs. *)
  (* Proof. *)
  (*   iIntros (Hdom) "(Hφr & Hk)". *)
  (*   iApply wp_opt_bind. *)
  (*   unfold incrementLPC, incrementPC. *)
  (*   change (wp_opt match lrt !! PC with *)
  (*             | Some (LCap p b e a v) => match (a + 1)%a with *)
  (*                                       | Some a' => Some (<[PC:=LCap p b e a' v]> lrt) *)
  (*                                       | None => None *)
  (*                                       end *)
  (*             | _ => None *)
  (*             end ?Φf ?Φs) with (wp_opt ((lrt !! PC) ≫= (fun w => match w with *)
  (*                                                   | (LCap p b e a v) => match (a + 1)%a with *)
  (*                                                                             | Some a' => Some (<[PC:=LCap p b e a' v]> lrt) *)
  (*                                                                             | None => None *)
  (*                                                                             end *)
  (*                                                   | _ => None *)
  (*                                                   end) ) Φf Φs). *)
  (*   rewrite <-wp_opt_bind. *)
  (*   iApply ((wp_reg_lookup lrt (r := PC) (φt := φt)) with "[$Hφr Hk]"). *)
  (*   iApply wp_opt_eqn. *)
  (*   rewrite wp_opt_is_Some; last by apply elem_of_dom. *)
  (*   iApply (wp_opt_mono with "[$Hk]"). *)
  (*   iIntros (x) "Hk %Hltrpceqn Hφr". *)
  (*   destruct x eqn:Heqx; try (now iApply "Hk"); cbn. *)
  (*   destruct sb; try (now iApply "Hk"); cbn. *)
  (*   destruct (f1 + 1)%a; try (now iApply "Hk"); cbn. *)
  (*   iApply ("Hk" $! (update_reg φt PC (WCap p f f0 f2)) with "[Hφr]"). *)
  (*   iApply (update_state_interp_transient_from_regs_mod Hdom with "Hφr"). *)
  (*   intros cur_map Hcurregs. *)
  (*   by eapply is_cur_word_cap_change, (map_Forall_lookup_1 _ _ _ _ Hcurregs). *)
  (* Qed. *)

  Lemma wp2_opt_incrementPC {Ep} {φ φt lr lrt lm lmt Φs Φf} :
    PC ∈ dom lrt ->
    state_interp_transient φ φt lr lrt lm lmt ∗
    ((∀ φt' lrt', state_interp_transient φ φt' lr lrt' lm lmt -∗ Φf) ∧
       (∀ lrt' rs',
           state_interp_transient φ (update_regs φt rs') lr lrt' lm lmt -∗ Φs lrt' rs'))
    ⊢ wp_opt2 Ep (incrementLPC lrt) (incrementPC (reg φt)) Φf Φs.
  Proof.
    iIntros (Hdom) "(Hφr & Hk)".
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.
    iApply (wp2_reg_lookup with "[$Hφr Hk]"); first done.

    iIntros (lwr) "Hφr %Heq1 %Heq2".
    destruct lwr; cbn;
      try (rewrite bi.and_elim_l; now iApply "Hk").
    destruct sb; cbn;
      try (rewrite bi.and_elim_l; now iApply "Hk").
    destruct (f1 + 1)%a; cbn;
      try (rewrite bi.and_elim_l; now iApply "Hk").
    rewrite bi.and_elim_r.
    iApply ("Hk" $! _ (<[PC := _ ]> (reg φt))).
    iApply (update_state_interp_transient_from_regs_mod Hdom (lw2 := LCap p f f0 f2 v) with "Hφr").

    intros cur_map Hcurregs.
    eapply is_cur_lword_lea with (lw := LCap p f f0 f1 v); try now cbn.
    by eapply (map_Forall_lookup_1 _ _ _ _ Hcurregs).
  Qed.


End cap_lang_rules_opt.
