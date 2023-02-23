From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac auth gmap excl list.
From cap_machine Require Export cap_lang iris_extra rules_base.


Definition specN := nroot .@ "spec".

(* heap and register CMRA for the specification *)
(* These need to be notations rather than definitions, as it otherwise causes performance issues *)
Notation memspecUR :=
  (gmapUR Addr (prodR fracR (agreeR (leibnizO Word)))).
Notation regspecUR :=
  (gmapUR RegName (prodR fracR (agreeR (leibnizO Word)))).
Notation memreg_specUR := (prodUR regspecUR memspecUR).

(* CMRA for the specification *)
Notation exprR := (exclR (leibnizO expr)).
Notation cfgUR := (prodUR (optionUR exprR) memreg_specUR).

Definition to_spec_map {L V : Type} `{Countable L} : gmap L V -> gmapUR L (prodR fracR (agreeR (leibnizO V))) :=
  fmap (λ w, (1%Qp, to_agree w)).

(* the CMRA for the specification side *)
Class cfgSG Σ := CFGSG {
  cfg_invG :> inG Σ (authR cfgUR);
  cfg_name : gname
}.

Section to_spec_map.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.

  Lemma lookup_to_spec_map_None σ l : σ !! l = None → to_spec_map σ !! l = None.
  Proof. by rewrite /to_spec_map lookup_fmap=> ->. Qed.
  Lemma to_spec_map_insert l v σ :
    to_spec_map (<[l:=v]> σ) = <[l:=(1%Qp, to_agree (v:leibnizO V))]> (to_spec_map σ).
  Proof. by rewrite /to_spec_map fmap_insert. Qed.

  Lemma spec_map_singleton_included σ l q v :
    {[l := (q, to_agree v)]} ≼ to_spec_map σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included_l=> -[[q' av] []].
    rewrite /to_spec_map lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.

End to_spec_map.

Section definitionsS.
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.

  Definition memspec_mapsto (a : Addr) (q : Qp) (w : Word) : iProp Σ :=
    own cfg_name (◯ (ε, (∅,{[ a := (q, to_agree w) ]}))).

  Definition regspec_mapsto (r : RegName) (q : Qp) (w : Word) : iProp Σ :=
    own cfg_name (◯ (ε, ({[ r := (q, to_agree w) ]},∅))).

  Definition exprspec_mapsto (e : expr) : iProp Σ :=
    own cfg_name (◯ (Excl' e : optionUR (exclR (leibnizO expr)),(∅,∅))).

  (* The following invariant contains the authoritative view of specification state *)
  Definition spec_res (e: leibnizO expr) (σ: gmap RegName Word * gmap Addr Word) : iProp Σ :=
    (own cfg_name (● (Excl' e,(to_spec_map σ.1,to_spec_map σ.2))))%I.
  Definition spec_inv (ρ : cfg cap_lang) : iProp Σ :=
    (∃ e σ, spec_res e σ ∗ ⌜rtc erased_step ρ ([e],σ)⌝)%I.
  Definition spec_ctx : iProp Σ :=
    (∃ ρ, inv specN (spec_inv ρ))%I.

  Global Instance memspec_mapsto_timeless l q v : Timeless (memspec_mapsto l q v).
  Proof. apply _. Qed.
  Global Instance regspec_mapsto_timeless l q v : Timeless (regspec_mapsto l q v).
  Proof. apply _. Qed.
  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.

  Lemma spec_heap_valid e σ a q w :
    spec_res e σ ∗ memspec_mapsto a q w -∗ ⌜σ.2 !! a = Some w⌝.
  Proof.
    iIntros "(Hown & Ha)".
    iDestruct (own_valid_2 with "Hown Ha")
      as %[[_ [_ ?%spec_map_singleton_included]%prod_included]%prod_included _]%auth_both_valid_discrete.
    auto.
  Qed.

  Lemma spec_regs_valid e σ r q w :
    spec_res e σ ∗ regspec_mapsto r q w -∗ ⌜σ.1 !! r = Some w⌝.
  Proof.
    iIntros "(Hown & Ha)".
    iDestruct (own_valid_2 with "Hown Ha")
      as %[[_ [?%spec_map_singleton_included _]%prod_included]%prod_included _]%auth_both_valid_discrete.
    auto.
  Qed.

  Lemma spec_expr_valid e e' σ :
    spec_res e σ ∗ exprspec_mapsto e' -∗ ⌜e = e'⌝.
  Proof.
    iIntros "(Hown & Ha)".
    iDestruct (own_valid_2 with "Hown Ha")
      as %[[? _]%prod_included _]%auth_both_valid_discrete.
    assert (e ≡ e') as Heq.
    { apply symmetry. apply Excl_included. auto. }
    iPureIntro. apply leibniz_equiv. auto.
  Qed.

  Lemma regspec_mapsto_agree l q1 q2 v1 v2 : regspec_mapsto l q1 v1 -∗ regspec_mapsto l q2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hr1 Hr2". iCombine "Hr1 Hr2" as "Hr".
    rewrite /regspec_mapsto own_valid !uPred.discrete_valid
            !auth_frag_valid.
    iDestruct "Hr" as %[_ [[_ Hr]%singleton_valid _]].
    simpl in Hr. apply @to_agree_op_inv_L with (A:=leibnizO Word) in Hr;auto. apply _.
  Qed.
  Lemma regspec_mapsto_valid r q v : regspec_mapsto r q v -∗ ✓ q.
  Proof.
    rewrite /regspec_mapsto own_valid !uPred.discrete_valid
            !auth_frag_valid. iPureIntro.
    intros [_ [[? _]%singleton_valid _]]. auto.
  Qed.
  Lemma regspec_mapsto_valid_2 r q1 q2 v1 v2 :
    regspec_mapsto r q1 v1 -∗ regspec_mapsto r q2 v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (regspec_mapsto_agree with "Hr1 Hr2") as %->.
    iCombine "Hr1 Hr2" as "Hr".
    by iApply regspec_mapsto_valid.
  Qed.
  Lemma regspec_mapsto_update e (σ : gmap RegName Word * gmap Addr Word) r (w w' : Word) :
    spec_res e σ -∗ regspec_mapsto r 1 w ==∗ spec_res e (<[r:=w']> σ.1,σ.2) ∗ regspec_mapsto r 1 w'.
  Proof.
    iIntros "Hσ Hr".
    iDestruct (spec_regs_valid with "[$Hσ $Hr]") as %Hr.
    rewrite /spec_res /regspec_mapsto.
    iMod (own_update_2 with "Hσ Hr") as "[Hσ Hr]".
    { eapply auth_update, prod_local_update_2,prod_local_update_1.
      eapply (singleton_local_update (to_spec_map σ.1) r (1%Qp, to_agree w) _ (1%Qp, to_agree w')).
      by rewrite lookup_fmap Hr. apply exclusive_local_update. done. }
    iModIntro. iFrame "Hr". iFrame. rewrite -fmap_insert. iFrame.
  Qed.

  Lemma memspec_mapsto_agree l q1 q2 v1 v2 : memspec_mapsto l q1 v1 -∗ memspec_mapsto l q2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hr1 Hr2". iCombine "Hr1 Hr2" as "Hr".
    rewrite /regspec_mapsto own_valid !uPred.discrete_valid
            !auth_frag_valid.
    iDestruct "Hr" as %[_ [_ [_ Hr]%singleton_valid]].
    simpl in Hr. apply @to_agree_op_inv_L with (A:=leibnizO Word) in Hr;auto. apply _.
  Qed.
  Lemma memspec_mapsto_valid r q v : memspec_mapsto r q v -∗ ✓ q.
  Proof.
    rewrite /memspec_mapsto own_valid !uPred.discrete_valid
            !auth_frag_valid. iPureIntro.
    intros [_ [_ [? _]%singleton_valid]]. auto.
  Qed.
  Lemma memspec_mapsto_valid_2 r q1 q2 v1 v2 :
    memspec_mapsto r q1 v1 -∗ memspec_mapsto r q2 v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (memspec_mapsto_agree with "Hr1 Hr2") as %->.
    iCombine "Hr1 Hr2" as "Hr".
    by iApply memspec_mapsto_valid.
  Qed.
  Lemma memspec_mapsto_update e (σ : gmap RegName Word * gmap Addr Word) r (w w' : Word) :
    spec_res e σ -∗ memspec_mapsto r 1 w ==∗ spec_res e (σ.1,<[r:=w']>σ.2) ∗ memspec_mapsto r 1 w'.
  Proof.
    iIntros "Hσ Hr".
    iDestruct (spec_heap_valid with "[$Hσ $Hr]") as %Hr.
    rewrite /spec_res /memspec_mapsto.
    iMod (own_update_2 with "Hσ Hr") as "[Hσ Hr]".
    { eapply auth_update, prod_local_update_2,prod_local_update_2.
      eapply (singleton_local_update (to_spec_map σ.2) r (1%Qp, to_agree w) _ (1%Qp, to_agree w')).
      by rewrite lookup_fmap Hr. apply exclusive_local_update. done. }
    iModIntro. iFrame "Hr". rewrite -fmap_insert. iFrame.
  Qed.

  Lemma exprspec_mapsto_update e σ e' :
    spec_res e σ -∗ exprspec_mapsto e ==∗ spec_res e' σ ∗ exprspec_mapsto e'.
  Proof.
    iIntros "Hσ He".
    rewrite /spec_res /exprspec_mapsto.
    iMod (own_update_2 with "Hσ He") as "[Hσ He]".
    { by eapply auth_update, prod_local_update_1, (option_local_update (A:=exprR)),
      (exclusive_local_update (A:=exprR) _ (Excl e')). }
    iFrame. done.
  Qed.

End definitionsS.
#[global] Typeclasses Opaque memspec_mapsto regspec_mapsto exprspec_mapsto.

Notation "a ↣ₐ{ q } v" := (memspec_mapsto a q v)
  (at level 20, q at level 50, format "a  ↣ₐ{ q }  v") : bi_scope.
Notation "a ↣ₐ v" := (memspec_mapsto a 1 v) (at level 20) : bi_scope.
Notation "r ↣ᵣ{ q } v" := (regspec_mapsto r q v)
  (at level 20, q at level 50, format "r  ↣ᵣ{ q }  v") : bi_scope.
Notation "r ↣ᵣ v" := (regspec_mapsto r 1 v) (at level 20) : bi_scope.
Notation "⤇ e" := (exprspec_mapsto e) (at level 20) : bi_scope.

Ltac iAsimpl :=
  repeat match goal with
  | |- context [ (⤇ ?e)%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [simpl; unfold e'; reflexivity|];
    unfold e'; clear e')
  | |- context [ WP ?e @ _ {{ _ }}%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [simpl; unfold e'; reflexivity|];
    unfold e'; clear e')
         end.

Section cap_lang_spec_resources.
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.

  (* ------------------------- registers points-to --------------------------------- *)

  Lemma regname_dupl_false r w1 w2 :
    r ↣ᵣ w1 -∗ r ↣ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (regspec_mapsto_valid_2 with "Hr1 Hr2") as %?.
    contradiction.
  Qed.

  Lemma regname_neq r1 r2 w1 w2 :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (regname_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_regs_1 (r1: RegName) (w1: Word) :
    r1 ↣ᵣ w1 -∗
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↣ᵣ y).
  Proof. by rewrite big_sepM_singleton. Qed.

  Lemma regs_of_map_1 (r1: RegName) (w1: Word) :
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↣ᵣ y) -∗
    r1 ↣ᵣ w1.
  Proof. by rewrite big_sepM_singleton. Qed.

  Lemma map_of_regs_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↣ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ r3 ↣ᵣ w3 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↣ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ⌝.
  Proof.
    iIntros "H1 H2 H3".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2 ∗ r3 ↣ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ r3 ↣ᵣ w3 -∗ r4 ↣ᵣ w4 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↣ᵣ y) ∗
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

  Lemma regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2 ∗ r3 ↣ᵣ w3 ∗ r4 ↣ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  (* ------------------------- address points-to --------------------------------- *)

  Lemma memMap_resource_2ne (a1 a2 : Addr) (w1 w2 : Word)  :
    a1 ≠ a2 → ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↣ₐ w)%I ⊣⊢ a1 ↣ₐ w1 ∗ a2 ↣ₐ w2.
  Proof.
    intros.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite (big_sepM_delete _ _ a2 w2); rewrite delete_insert; try by rewrite lookup_insert_ne. 2: by rewrite lookup_insert.
    rewrite delete_insert; auto.
    iSplit; iIntros "HH".
    - iDestruct "HH" as "[H1 [H2 _ ] ]".  iFrame.
    - iDestruct "HH" as "[H1 H2]". iFrame. done.
  Qed.

  (* -------------- semantic heap + a map of pointsto: spec side -------------------------- *)

  Lemma memspec_heap_valid_inSepM e σ σ' q l v :
      σ' !! l = Some v →
      spec_res e σ -∗
      ([∗ map] k↦y ∈ σ', memspec_mapsto k q y) -∗
      ⌜σ.2 !! l = Some v⌝.
  Proof.
    intros * Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "? [? ?]".
    iApply (spec_heap_valid with "[$]").
  Qed.
  Lemma regspec_heap_valid_inSepM e σ σ' q l v :
      σ' !! l = Some v →
      spec_res e σ -∗
      ([∗ map] k↦y ∈ σ', regspec_mapsto k q y) -∗
      ⌜σ.1 !! l = Some v⌝.
  Proof.
    intros * Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "? [? ?]".
    iApply (spec_regs_valid with "[$]").
  Qed.

  Lemma memspec_heap_valid_inSepM' e σ σ' q :
      spec_res e σ -∗
      ([∗ map] k↦y ∈ σ', memspec_mapsto k q y) -∗
      ⌜forall l v, σ' !! l = Some v → σ.2 !! l = Some v⌝.
  Proof.
    intros *. iIntros "? Hmap" (l v Hσ').
    rewrite (big_sepM_delete _ σ' l) //. iDestruct "Hmap" as "[? ?]".
    iApply (spec_heap_valid with "[$]").
  Qed.
  Lemma regspec_heap_valid_inSepM' e σ σ' q :
      spec_res e σ -∗
      ([∗ map] k↦y ∈ σ', regspec_mapsto k q y) -∗
      ⌜forall l v, σ' !! l = Some v → σ.1 !! l = Some v⌝.
  Proof.
    intros *. iIntros "? Hmap" (l v Hσ').
    rewrite (big_sepM_delete _ σ' l) //. iDestruct "Hmap" as "[? ?]".
    iApply (spec_regs_valid with "[$]").
  Qed.

  Lemma memspec_heap_valid_inclSepM e σ σ' q :
      spec_res e σ -∗
      ([∗ map] k↦y ∈ σ', memspec_mapsto k q y) -∗
      ⌜σ' ⊆ σ.2⌝.
  Proof.
    intros *. iIntros "Hσ Hmap".
    iDestruct (memspec_heap_valid_inSepM' with "Hσ Hmap") as "#H".
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (σ' !! l) eqn:HH'; destruct (σ.2 !! l) eqn:HH; naive_solver.
  Qed.
  Lemma regspec_heap_valid_inclSepM e σ σ' q :
      spec_res e σ -∗
      ([∗ map] k↦y ∈ σ', regspec_mapsto k q y) -∗
      ⌜σ' ⊆ σ.1⌝.
  Proof.
    intros *. iIntros "Hσ Hmap".
    iDestruct (regspec_heap_valid_inSepM' with "Hσ Hmap") as "#H".
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (σ' !! l) eqn:HH'; destruct (σ.1 !! l) eqn:HH; naive_solver.
  Qed.

  Lemma memspec_heap_valid_allSepM e σ σ' q :
      (forall l, is_Some (σ' !! l)) →
      spec_res e σ -∗
      ([∗ map] k↦y ∈ σ', memspec_mapsto k q y) -∗
      ⌜ σ.2 = σ' ⌝.
  Proof.
    intros * Hσ'. iIntros "A B".
    iAssert (⌜ forall l, σ.2 !! l = σ' !! l ⌝)%I with "[A B]" as %HH.
    { iIntros (l).
      specialize (Hσ' l). unfold is_Some in Hσ'. destruct Hσ' as [v Hσ'].
      rewrite Hσ'.
      eapply (memspec_heap_valid_inSepM e σ σ') in Hσ'.
      iApply (Hσ' with "[$]"). eauto. }
    iPureIntro. eapply map_leibniz. intro.
    eapply leibniz_equiv_iff. auto.
    Unshelve.
  Qed.
  Lemma regspec_heap_valid_allSepM e σ σ' q :
      (forall l, is_Some (σ' !! l)) →
      spec_res e σ -∗
      ([∗ map] k↦y ∈ σ', regspec_mapsto k q y) -∗
      ⌜ σ.1 = σ' ⌝.
  Proof.
    intros * Hσ'. iIntros "A B".
    iAssert (⌜ forall l, σ.1 !! l = σ' !! l ⌝)%I with "[A B]" as %HH.
    { iIntros (l).
      specialize (Hσ' l). unfold is_Some in Hσ'. destruct Hσ' as [v Hσ'].
      rewrite Hσ'.
      eapply (regspec_heap_valid_inSepM e σ σ') in Hσ'.
      iApply (Hσ' with "[$]"). eauto. }
    iPureIntro. eapply map_leibniz. intro.
    eapply leibniz_equiv_iff. auto.
    Unshelve.
  Qed.

  Lemma memspec_v_implies_m_v:
    ∀ mem0 σ e' (b e a : Addr) (v : Word) q,
      mem0 !! a = Some v
      → ([∗ map] a0↦w ∈ mem0, memspec_mapsto a0 q w)
          -∗ spec_res e' σ -∗ ⌜σ.2 !! a = Some v⌝.
  Proof.
    iIntros (mem0 σ e' b e a v q Hmem) "Hmem Hm".
    rewrite (big_sepM_delete _ mem0 a) //.
    iDestruct "Hmem" as "[H_a Hmem]".
    iDestruct (spec_heap_valid with "[$Hm $H_a]") as %?; auto.
  Qed.

  Lemma memspec_heap_update_inSepM e σ σ' l v :
      is_Some (σ' !! l) →
      spec_res e σ
      -∗ ([∗ map] k↦y ∈ σ', memspec_mapsto k 1 y)
      ==∗ spec_res e (σ.1,<[l:=v]>σ.2)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), memspec_mapsto k 1 y.
  Proof.
    intros * Hσ'. destruct Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (memspec_mapsto_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=v]> σ') l).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.
  Lemma regspec_heap_update_inSepM e σ σ' l v :
      is_Some (σ' !! l) →
      spec_res e σ
      -∗ ([∗ map] k↦y ∈ σ', regspec_mapsto k 1 y)
      ==∗ spec_res e (<[l:=v]> σ.1,σ.2)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), regspec_mapsto k 1 y.
  Proof.
    intros * Hσ'. destruct Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (regspec_mapsto_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=v]> σ') l).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.

  Lemma spec_memMap_resource_2ne_apply (a1 a2 : Addr) (w1 w2 : Word)  :
    a1 ↣ₐ w1 -∗ a2 ↣ₐ w2 -∗ ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↣ₐ w) ∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "Hi Hr2a".
    destruct (decide (a1 = a2)).
    { subst. iDestruct (memspec_mapsto_valid_2 with "Hi Hr2a") as %Hne; auto. done. }
    iSplitL; last by auto.
    iApply memMap_resource_2ne; auto. iSplitL "Hi"; auto.
  Qed.

End cap_lang_spec_resources.


Section cap_lang_spec_rules.
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma spec_step_bind K e σ κ e' σ' :
    head_step e σ κ e' σ' [] ->
    erased_step ([fill K e],σ) ([fill K e'],σ').
  Proof.
    intros.
    assert ([fill K e'] = <[0:=fill K e']> [fill K e]) as ->;[auto|].
    rewrite -(right_id_L [] (++) (<[_:=_]>_)).
    rewrite -(take_drop_middle [fill K e] 0 (fill K e)) //.
    eexists. eapply step_atomic; eauto.
    apply Ectx_step'. eauto.
  Qed.

  Lemma spec_step_pure E K e e' (P : Prop) n :
    P -> PureExec P n e e' ->
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K e ={E}=∗ ⤇ fill K e'.
  Proof.
    iIntros (HP Hpure Hsub) "[#Hinv He]".
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_inv /exprspec_mapsto.
    iInv specN as ">H" "Hclose".
    iDestruct "H" as (c σ) "[Hcfg Hstep]".
    iDestruct "Hstep" as %Hstep.
    iDestruct (own_valid_2 with "Hcfg He") as %[[Hincle _]%prod_included Hvalid]%auth_both_valid_discrete;simpl in *.
    assert ((ectxi_language.fill K e : exprO cap_lang) ≡ c) as Heq;[by apply Excl_included|simplify_eq].
    iMod (own_update_2 with "Hcfg He") as "[Hcfg He]".
    { by eapply auth_update,prod_local_update_1,(option_local_update (A:=exprR)),
      (exclusive_local_update (A:=exprR) _ (Excl (fill K e'))). }
    iFrame. iApply "Hclose".
    iNext. iExists (fill K e'),σ. iFrame. iPureIntro.
    apply rtc_nsteps_1 in Hstep; destruct Hstep as [m Hrtc].
    specialize (Hpure HP). apply (rtc_nsteps_2 (m + n)).
    eapply nsteps_trans; eauto. clear -Hpure.
    revert e e' Hpure. induction n => e e' Hpure.
    - inversion Hpure. subst. apply nsteps_O.
    - inversion Hpure;subst. apply IHn in H2.
      eapply relations.nsteps_l;eauto.
      inversion H1 as [Hexs Hexd].
      specialize (Hexs σ). destruct Hexs as [e'' [σ' [efs Hexs]]].
      specialize (Hexd σ [] e'' σ' efs Hexs); destruct Hexd as [? [? [? ?]]]; subst.
      simpl in Hexs. apply fill_prim_step with (K:=K) in Hexs.
      econstructor;auto. eapply step_atomic with (t1:=[]) (t2:=[]);eauto.
  Qed.

  Lemma do_step_pure E K e e' `{!PureExec True 1 e e'}:
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K e ={E}=∗ ⤇ fill K e'.
  Proof. by eapply spec_step_pure; last eauto. Qed.

End cap_lang_spec_rules.

Ltac prim_step_from_exec :=
    match goal with
    | H : exec _ _ = ?res |- _ =>
      exists [];eapply step_atomic with (t1:=[]) (t2:=[]);eauto;
      econstructor;eauto;constructor;
      eapply step_exec_instr with (c:=res); try exact; simplify_map_eq;eauto
    end.

Ltac iFailStep fail_type :=
    iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
    iMod ("Hclose" with "[Hown]") as "_";
    [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|];
    iExists (FailedV),_; iFrame;iModIntro;iFailCore fail_type.

(* FIXME: simplify_map_eq ought to do this but fails *)
  Ltac simplify_map_eq_alt :=
    repeat (match goal with
            | H : context [<[_:=_]> _ !! _] |- _ =>
              revert H; rewrite lookup_insert_ne;[|done]; intros H
            end);
    repeat (match goal with
            | H : context [<[_:=_]> _ !! _] |- _ =>
              revert H; rewrite lookup_insert; intros H
            end); simplify_eq.

Section cap_lang_spec_rules.
  Context `{cfgSG Σ, MachineParameters, invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  (* ----------------------------- Fail and Halt --------------------------------- *)

  Lemma step_halt E K pc_p pc_b pc_e pc_a w :
    decodeInstrW w = Halt →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ pc_a ↣ₐ w
    ={E}=∗ ⤇ fill K (Instr Halted)
         ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↣ₐ w.
  Proof.
    intros Hinstr Hvpc Hnclose.
    iIntros "(Hinv & Hj & Hpc & Hpca)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (@spec_regs_valid with "[$Hown $Hpc]") as %?.
    iDestruct (@spec_heap_valid with "[$Hown $Hpca]") as %?.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto. assert (Hstep':=Hstep).
    cbn in Hstep. simplify_eq.
    iMod (exprspec_mapsto_update _ _ (fill K (Instr Halted)) with "Hown Hj") as "[Hown Hj]".
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto. simpl. prim_step_from_exec. }
    by iFrame.
  Qed.

  Lemma step_fail E K pc_p pc_b pc_e pc_a w :
    decodeInstrW w = Fail →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ pc_a ↣ₐ w
    ={E}=∗ ⤇ fill K (Instr Failed)
         ∗ PC ↣ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↣ₐ w.
  Proof.
    intros Hinstr Hvpc Hnclose.
    iIntros "(Hinv & Hj & Hpc & Hpca)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (@spec_regs_valid with "[$Hown $Hpc]") as %?.
    iDestruct (@spec_heap_valid with "[$Hown $Hpca]") as %?.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto. assert (Hstep':=Hstep).
    cbn in Hstep. simplify_eq.
    iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto. simpl. prim_step_from_exec. }
    by iFrame.
  Qed.

End cap_lang_spec_rules.
