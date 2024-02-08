From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth.
From cap_machine Require Export logical_mapsto.
From cap_machine Require Export cap_lang iris_extra stdpp_extra.

(* --------------------------- LTAC DEFINITIONS ----------------------------------- *)

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

  Lemma gen_heap_lmem_version_update `{HmemG : memG Σ, HregG : regG Σ} :
    ∀ (lm lmem lm' lmem': LMem) (vmap vmap_m' vmap_mem': VMap)
      (la : list Addr) ( v : Version ),
      NoDup la ->
      lmem ⊆ lm ->
      update_cur_version_region_local lm vmap la = (lm', vmap_m') ->
      update_cur_version_region_global lmem lm vmap la = (lmem', vmap_mem') ->
      Forall (λ a : Addr, lm !! (a, v+1) = None) la ->
      Forall (λ a : Addr, is_cur_addr (a,v) vmap) la ->
      gen_heap_interp lm
      -∗ ([∗ map] k↦y ∈ lmem, mapsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp lm' ∗ [∗ map] k↦y ∈ lmem', mapsto k (DfracOwn 1) y.
  Proof.
    move=> lm lmem lm' lmem' vmap vmap_m' vmap_mem' la.
    move: lm lmem lm' lmem' vmap vmap_m' vmap_mem'.
    induction la as [|a la IH]
    ; iIntros
        (lm lmem lm' lmem' vmap vmap_m' vmap_mem' v
           HNoDup_la Hlmem_incl Hupd_lm Hupd_lmem Hmaxv_lm Hcur_lm)
        "Hgen Hmem".
    - (* no addresses updated *)
      cbn in Hupd_lm, Hupd_lmem ; simplify_eq.
      iModIntro; iFrame.
    - (* TODO because I ofter do this trick, maybe I could have an LTac
         that automatically detects and breaks everything *)
      apply NoDup_cons in HNoDup_la.
      destruct HNoDup_la as [Ha_not_la HNoDup_la].

      apply Forall_cons in Hcur_lm.
      destruct Hcur_lm as (Hcur_a_lm & Hcur_lm).

      apply Forall_cons in Hmaxv_lm.
      destruct Hmaxv_lm as (Hmaxv_a & Hmaxv_lm).

      apply update_cur_version_region_local_cons in Hupd_lm
      ; destruct Hupd_lm as (lm0 & vmap_m0 & Hupd_lm & Hupd_lm0).

      apply update_cur_version_region_global_cons in Hupd_lmem
      ; destruct Hupd_lmem as (lmem0 & vmap_mem0 & Hupd_lmem & Hupd_lmem0).

      eapply update_cur_version_inter in Hupd_lmem0 ; eauto.

      assert (lmem0 ⊆ lm0 /\ vmap_mem0 ⊆ vmap_m0) as [Hlmem0_incl Hvmap0_incl].
      eapply update_cur_version_region_inter_incl; eauto.
      { apply Forall_forall. intros a' Ha' v' Hcur_a'.
        apply elem_of_list_lookup_1 in Ha'. destruct Ha' as [lwa' Ha'].
        eapply Forall_lookup in Hcur_lm; eauto.
        eapply is_cur_addr_same in Hcur_a'; eauto; simplify_eq.
        eapply Forall_lookup in Hmaxv_lm; eauto.
      }

      opose proof
        (update_cur_version_addr_inter_incl_vmap _ _ _ _ _ _ _ _ _ _ _ Hupd_lmem0 Hupd_lm0)
        as Hvmap_incl ; eauto.
      rewrite /update_cur_version_addr_global in Hupd_lmem0.
      rewrite /update_cur_version_addr_local in Hupd_lm0.

      destruct (vmap_mem0 !! a) as [va |] eqn:Hvmap_mem0_a.
      2: {
        erewrite update_cur_version_region_inter_incl_vmap in Hvmap_mem0_a; eauto.
        rewrite Hvmap_mem0_a in Hupd_lm0; simplify_eq.
        iApply (IH with "Hgen"); eauto.
      }
      rewrite /is_cur_addr /= in Hcur_a_lm.
      erewrite <- update_cur_version_region_local_notin_preserves_cur
        in Hcur_a_lm; eauto.
      eapply lookup_weaken in Hvmap_mem0_a; eauto.
      rewrite -/(is_cur_addr (a,va) vmap_m0) in Hvmap_mem0_a.
      eapply is_cur_addr_same in Hcur_a_lm; eauto; simplify_map_eq.
      destruct (lm0 !! (a, v)) as [lw|] eqn:Hlm0_a
      ; rewrite Hlm0_a in Hupd_lm0, Hupd_lmem0
      ; simplify_eq .
      2: { iApply (IH with "Hgen"); eauto. }
      specialize (IH lm lmem lm0 lmem0 vmap vmap_m0 vmap_mem0 v
                    HNoDup_la Hlmem_incl Hupd_lm Hupd_lmem).

      iDestruct (IH with "Hgen Hmem") as ">[Hgen Hmem]"; eauto.
      erewrite <- update_cur_version_region_local_notin_preserves_lmem in Hmaxv_a; eauto.

      iMod (((gen_heap_alloc lm0 (a, v + 1) lw) with "Hgen"))
        as "(Hgen & Ha & _)"; auto.
      iModIntro ; iFrame.
      iApply (big_sepM_insert with "[Hmem Ha]"); last iFrame.
      eapply lookup_weaken_None; eauto.
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

Lemma incrementLPC_incrementPC_some regs regs' :
  incrementLPC regs = Some regs' ->
  incrementPC (lreg_strip regs) = Some (lreg_strip regs').
Proof.
  rewrite /incrementPC /incrementLPC.
  intros Hlpc.
  rewrite /lreg_strip lookup_fmap; cbn.
  destruct (regs !! PC) as [lw|] eqn:Heq ; rewrite Heq; cbn in *; last done.
  destruct_lword lw; cbn in *; try done.
  destruct (a + 1)%a; last done.
  simplify_eq.
  by rewrite fmap_insert.
Qed.

Lemma incrementLPC_incrementPC_none regs :
  incrementLPC regs = None <-> incrementPC (lreg_strip regs) = None.
Proof.
  intros.
  rewrite /incrementPC /incrementLPC.
  rewrite /lreg_strip lookup_fmap; cbn.
  destruct (regs !! PC) as [LX|] eqn:Heq ; rewrite Heq; cbn; last done.
  destruct LX ; cbn ; [(clear; firstorder) | | (clear; firstorder)].
  destruct sb as [? ? ? a' | ] ; eauto; cbn; last done.
  destruct (a' + 1)%a eqn:Heq'; done.
Qed.

Lemma incrementLPC_fail_updatePC regs m etbl ecur:
  incrementLPC regs = None ->
  updatePC {| reg := (lreg_strip regs); mem := m; etable := etbl ; enumcur := ecur |} = None.
Proof.
  intro Hincr. apply incrementLPC_incrementPC_none in Hincr.
  by apply incrementPC_fail_updatePC.
Qed.

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

Lemma incrementLPC_success_updatePC regs m etbl ecur regs' :
  incrementLPC regs = Some regs' ->
  ∃ p b e a a' (v : Version),
    regs !! PC = Some (LCap p b e a v) ∧
      (a + 1)%a = Some a' ∧
      updatePC {| reg := (lreg_strip regs); mem := m; etable := etbl ; enumcur := ecur |} =
        Some (NextI,
            {| reg := (<[PC:=WCap p b e a']> (lreg_strip regs));
              mem := m;
              etable := etbl ;
              enumcur := ecur |})
    ∧ regs' = <[ PC := (LCap p b e a' v) ]> regs.
Proof.
  intro Hincr.
  opose proof (incrementLPC_incrementPC_some _ _ Hincr) as HincrPC.
  eapply (incrementPC_success_updatePC _ m etbl ecur) in HincrPC.
  destruct HincrPC as (p'&b'&e'&a''&a'''&Hregs&Heq&Hupd&Hregseq).
  rewrite /incrementLPC in Hincr.
  destruct (regs !! PC) as [wpc |]; last done.
  destruct_lword wpc; try done.
  destruct (a + 1)%a as [a'|] eqn:Heq'; last done; simplify_eq.
  rewrite /lreg_strip fmap_insert //= -/(lreg_strip regs)  in Hregseq.
  exists p, b, e, a, a', v.
  repeat (split; try done).
  by rewrite Hupd Hregseq.
Qed.

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
