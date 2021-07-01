From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac auth.
From cap_machine Require Export cap_lang iris_extra.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invG Σ;
  mem_gen_memG :> gen_heapG Addr Word Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invG Σ;
  reg_gen_regG :> gen_heapG RegName Word Σ; }.


(* invariants for memory, and a state interpretation for (mem,reg) *)
Instance memG_irisG `{MachineParameters} `{memG Σ, regG Σ} : irisG cap_lang Σ := {
  iris_invG := mem_invG;
  state_interp σ κs _ := ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2))%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (mapsto (L:=RegName) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (mapsto (L:=RegName) (V:=Word) r (DfracOwn 1) w) (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ { q } w" := (mapsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ { q }  w") : bi_scope.
Notation "a ↦ₐ w" := (mapsto (L:=Addr) (V:=Word) a (DfracOwn 1) w) (at level 20) : bi_scope.

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
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.


  (* Conditionally unify on the read register value *)
  Definition read_reg_inr  (regs : Reg) (r : RegName) p b e a :=
    match regs !! r with
      | Some (WCap p' b' e' a') => WCap p' b' e' a' = WCap p b e a
      | Some _ => True
      | None => False end.

  (* ------------------------- registers points-to --------------------------------- *)

  Lemma regname_dupl_false r w1 w2 :
    r ↦ᵣ w1 -∗ r ↦ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %?.
    destruct H2. eapply dfrac_full_exclusive in H2. auto.
  Qed.

  Lemma regname_neq r1 r2 w1 w2 :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (regname_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_regs_1 (r1: RegName) (w1: Word) :
    r1 ↦ᵣ w1 -∗
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y).
  Proof. by rewrite big_sepM_singleton. Qed.

  Lemma regs_of_map_1 (r1: RegName) (w1: Word) :
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y) -∗
    r1 ↦ᵣ w1.
  Proof. by rewrite big_sepM_singleton. Qed.

  Lemma map_of_regs_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
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

  Lemma regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
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

  Lemma regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3 ∗ r4 ↦ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  (* ------------------------- memory points-to --------------------------------- *)

  Lemma addr_dupl_false a w1 w2 :
    a ↦ₐ w1 -∗ a ↦ₐ w2 -∗ False.
  Proof.
    iIntros "Ha1 Ha2".
    iDestruct (mapsto_valid_2 with "Ha1 Ha2") as %?.
    destruct H2. eapply dfrac_full_exclusive in H2.
    auto.
  Qed.

  (* -------------- semantic heap + a map of pointsto -------------------------- *)

  Lemma gen_heap_valid_inSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
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
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜forall (l: L) (v: V), σ' !! l = Some v → σ !! l = Some v⌝.
  Proof.
    intros *. iIntros "? Hmap" (l v Hσ').
    rewrite (big_sepM_delete _ σ' l) //. iDestruct "Hmap" as "[? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inclSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
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
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
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
      {gen_heapG0 : gen_heapG L V Σ}
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

  Lemma wp_lift_atomic_head_step_no_fork_determ {s E Φ} e1 :
    to_val e1 = None →
    (∀ (σ1:cap_lang.state) κ κs n, state_interp σ1 (κ ++ κs) n ={E}=∗
     ∃ κ e2 (σ2:cap_lang.state) efs, ⌜cap_lang.prim_step e1 σ1 κ e2 σ2 efs⌝ ∗
      (▷ |==> (state_interp σ2 κs n ∗ from_option Φ False (to_val e2))))
      ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 κ κs n)  "Hσ1 /=".
    iMod ("H" $! σ1 κ κs n with "[Hσ1]") as "H"; auto.
    iDestruct "H" as (κ' e2 σ2 efs) "[H1 H2]".
    iModIntro. iSplit.
    - rewrite /head_reducible /=.
      iExists κ', e2, σ2, efs. auto.
    - iNext. iIntros (? ? ?) "H".
      iDestruct "H" as %Hs1.
      iDestruct "H1" as %Hs2.
      destruct (cap_lang_determ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2) as [Heq1 [Heq2 [Heq3 Heq4]]].
      subst. iMod "H2". iModIntro. iFrame. inv Hs1; auto.
  Qed.

  (* -------------- predicates on memory maps -------------------------- *)

  Lemma extract_sep_if_split a pc_a P Q R:
     (if (a =? pc_a)%a then P else Q ∗ R)%I ≡
     ((if (a =? pc_a)%a then P else Q) ∗
     if (a =? pc_a)%a then emp else R)%I.
  Proof.
    destruct (a =? pc_a)%a; auto.
    iSplit; auto. iIntros "[H1 H2]"; auto.
  Qed.

  Lemma memMap_resource_0  :
        True ⊣⊢ ([∗ map] a↦w ∈ ∅, a ↦ₐ w).
  Proof.
    by rewrite big_sepM_empty.
  Qed.


  Lemma memMap_resource_1 (a : Addr) (w : Word)  :
        a ↦ₐ w  ⊣⊢ ([∗ map] a↦w ∈ <[a:=w]> ∅, a ↦ₐ w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_2ne (a1 a2 : Addr) (w1 w2 : Word)  :
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

  Lemma address_neq a1 a2 w1 w2 :
    a1 ↦ₐ w1 -∗ a2 ↦ₐ w2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "Ha1 Ha2".
    destruct (addr_eq_dec a1 a2); auto. subst.
    iExFalso. iApply (addr_dupl_false with "[$Ha1] [$Ha2]").
  Qed.

  Lemma memMap_resource_2ne_apply (a1 a2 : Addr) (w1 w2 : Word)  :
    a1 ↦ₐ w1 -∗ a2 ↦ₐ w2 -∗ ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↦ₐ w) ∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "Hi Hr2a".
    iDestruct (address_neq  with "Hi Hr2a") as %Hne; auto.
    iSplitL; last by auto.
    iApply memMap_resource_2ne; auto. iSplitL "Hi"; auto.
  Qed.

  Lemma memMap_resource_2gen (a1 a2 : Addr) (w1 w2 : Word)  :
    ( ∃ mem, ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∧
       ⌜ if  (a2 =? a1)%a
       then mem =  (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)⌝
    )%I ⊣⊢ (a1 ↦ₐ w1 ∗ if (a2 =? a1)%a then emp else a2 ↦ₐ w2) .
  Proof.
    destruct (a2 =? a1)%a eqn:Heq.
    - apply Z.eqb_eq, z_of_eq in Heq. rewrite memMap_resource_1.
      iSplit.
      * iDestruct 1 as (mem) "[HH ->]".  by iSplit.
      * iDestruct 1 as "[Hmap _]". iExists (<[a1:=w1]> ∅); iSplitL; auto.
    - apply Z.eqb_neq in Heq.
      rewrite -memMap_resource_2ne; auto. 2 : congruence.
      iSplit.
      * iDestruct 1 as (mem) "[HH ->]". done.
      * iDestruct 1 as "Hmap". iExists (<[a1:=w1]> (<[a2:=w2]> ∅)); iSplitL; auto.
  Qed.

  Lemma memMap_resource_2gen_d (Φ : Addr → Word → iProp Σ) (a1 a2 : Addr) (w1 w2 : Word)  :
    ( ∃ mem, ([∗ map] a↦w ∈ mem, Φ a w) ∧
       ⌜ if  (a2 =? a1)%a
       then mem =  (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)⌝
    ) -∗ (Φ a1 w1 ∗ if (a2 =? a1)%a then emp else Φ a2 w2) .
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (mem) "[Hmem Hif]".
    destruct ((a2 =? a1)%a) eqn:Heq.
    - iDestruct "Hif" as %->.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne;auto. apply Z.eqb_neq in Heq. solve_addr. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.

  (* Not the world's most beautiful lemma, but it does avoid us having to fiddle around with a later under an if in proofs *)
  Lemma memMap_resource_2gen_clater (a1 a2 : Addr) (w1 w2 : Word) (Φ : Addr -> Word -> iProp Σ)  :
    (▷ Φ a1 w1) -∗
    (if (a2 =? a1)%a then emp else ▷ Φ a2 w2) -∗
    (∃ mem, ▷ ([∗ map] a↦w ∈ mem, Φ a w) ∗
       ⌜if  (a2 =? a1)%a
       then mem =  (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)⌝
    )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (a2 =? a1)%a eqn:Heq.
    - iExists (<[a1:= w1]> ∅); iSplitL; auto. iNext. iApply big_sepM_insert;[|by iFrame].
      auto.
    - iExists (<[a1:=w1]> (<[a2:=w2]> ∅)); iSplitL; auto.
      iNext.
      iApply big_sepM_insert;[|iFrame].
      { apply Z.eqb_neq in Heq. rewrite lookup_insert_ne//. congruence. }
      iApply big_sepM_insert;[|by iFrame]. auto.
  Qed.

  Lemma memMap_delete:
    ∀(a : Addr) (w : Word) mem0,
      mem0 !! a = Some w →
      ([∗ map] a↦w ∈ mem0, a ↦ₐ w)
      ⊣⊢ (a ↦ₐ w
         ∗ ([∗ map] k↦y ∈ delete a mem0,
               k ↦ₐ y)).
  Proof.
    intros a w mem0 Hmem0a.
    rewrite -(big_sepM_delete _ _ a); auto.
  Qed.

  Lemma gen_mem_valid_inSepM:
    ∀ mem0 (m : Mem) (a : Addr) (w : Word),
      mem0 !! a = Some w →
      gen_heap_interp m
                   -∗ ([∗ map] a↦w ∈ mem0, a ↦ₐ w)
                   -∗ ⌜m !! a = Some w⌝.
  Proof.
    iIntros (mem0 m a w Hmem_pc) "Hm Hmem".
    iDestruct (memMap_delete a with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto.
  Qed.

  Lemma gen_mem_update_inSepM :
    ∀ {Σ : gFunctors} {gen_heapG0 : gen_heapG Addr Word Σ}
      (σ : gmap Addr Word) mem0 (l : Addr) (v' v : Word),
      mem0 !! l = Some v' →
      gen_heap_interp σ
      -∗ ([∗ map] a↦w ∈ mem0, a ↦ₐ w)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ ([∗ map] a↦w ∈ <[l:=v]> mem0, a ↦ₐ w).
  Proof.
    intros.
    rewrite (big_sepM_delete _ _ l);[|eauto].
    iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]"; eauto.
    iModIntro.
    iSplitL "Hh"; eauto.
    iDestruct (big_sepM_insert _ _ l with "[$Hmap $Hl]") as "H".
    apply lookup_delete.
    rewrite insert_delete. iFrame.
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)

  Lemma wp_notCorrectPC:
    forall E w,
      ~ isCorrectPC w ->
      {{{ PC ↦ᵣ w }}}
        Instr Executable @ E
        {{{ RET FailedV; PC ↦ᵣ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iApply fupd_frame_l.
    iSplit. by iPureIntro; apply normal_always_head_reducible.
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    iNext. iModIntro. iSplitR; auto. iFrame. cbn. by iApply "Hϕ".
  Qed.

  (* Subcases for respecitvely permissions and bounds *)

  Lemma wp_notCorrectPC_perm E pc_p pc_b pc_e pc_a :
      pc_p ≠ RX ∧ pc_p ≠ RWX →
      {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");
      [apply not_isCorrectPC_perm;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  Lemma wp_notCorrectPC_range E pc_p pc_b pc_e pc_a :
       ¬ (pc_b <= pc_a < pc_e)%a →
      {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");
      [apply not_isCorrectPC_bounds;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_b pc_e pc_a w :
    decodeInstrW w = Halt →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↦ₐ w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iModIntro. iSplitR; eauto. iFrame. iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_fail E pc_p pc_b pc_e pc_a w :
    decodeInstrW w = Fail →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↦ₐ w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iModIntro. iSplitR; eauto. iFrame. iApply "Hφ". by iFrame.
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
  | Add r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Sub r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Lt r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | IsPtr dst src => {[ dst; src ]}
  | Mov r arg => {[ r ]} ∪ regs_of_argument arg
  | Restrict r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Subseg r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Load r1 r2 => {[ r1; r2 ]}
  | Store r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Jnz r1 r2 => {[ r1; r2 ]}
  | Seal dst r1 r2 => {[dst; r1; r2]}
  | UnSeal dst r1 r2 => {[dst; r1; r2]}
  | _ => ∅
  end.

Lemma indom_regs_incl D (regs regs': Reg) :
  D ⊆ dom (gset RegName) regs →
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
  destruct (regs !! PC) as [ [| ? ? ? u ] |];
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
  destruct (regs !! PC) as [ [| ? ? ? u ] |];
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
  rewrite HPC HPC' in Hi |- *. destruct c as [| ? ? ? aa]; auto.
  destruct (aa+1)%a; last by auto. congruence.
Qed.

(* todo: instead, define updatePC on top of incrementPC *)
Lemma incrementPC_fail_updatePC regs m :
   incrementPC regs = None ->
   updatePC (regs, m) = None.
Proof.
   rewrite /incrementPC /updatePC /=.
   destruct (regs !! PC) as [X|]; auto.
   destruct X as [| ? ? ? a']; auto.
   destruct (a' + 1)%a; auto. congruence.
Qed.

Lemma incrementPC_success_updatePC regs m regs' :
  incrementPC regs = Some regs' ->
  ∃ p b e a a',
    regs !! PC = Some (WCap p b e a) ∧
    (a + 1)%a = Some a' ∧
    updatePC (regs, m) = Some (NextI, (<[ PC := WCap p b e a' ]> regs, m)) ∧
    regs' = <[ PC := WCap p b e a' ]> regs.
Proof.
  rewrite /incrementPC /updatePC /update_reg /=.
  destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
  destruct X as [| ? ? ? a'] eqn:?; try congruence; [].
  destruct (a' + 1)%a eqn:?; [| congruence]. inversion 1; subst regs'.
  do 5 eexists. repeat split; auto.
Qed.

Lemma updatePC_success_incl m m' regs regs' w :
  regs ⊆ regs' →
  updatePC (regs, m) = Some (NextI, (<[ PC := w ]> regs, m)) →
  updatePC (regs', m') = Some (NextI, (<[ PC := w ]> regs', m')).
Proof.
  intros * Hincl Hu. rewrite /updatePC /= in Hu |- *.
  destruct (regs !! PC) as [ w1 |] eqn:Hrr.
  { pose proof (lookup_weaken _ _ _ _ Hrr Hincl) as Hregs'. rewrite Hregs'.
    destruct w1 as [| ? ? ? a1 ]; simplify_eq.
    destruct (a1 + 1)%a eqn:Ha1; simplify_eq. rewrite /update_reg /=.
    f_equal. f_equal.
    assert (HH: forall (reg1 reg2:Reg), reg1 = reg2 -> reg1 !! PC = reg2 !! PC)
      by (intros * ->; auto).
    apply HH in Hu. rewrite !lookup_insert in Hu. by simplify_eq. }
  {  inversion Hu. }
Qed.

Lemma updatePC_fail_incl m m' regs regs' :
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  updatePC (regs, m) = None →
  updatePC (regs', m') = None.
Proof.
  intros [w HPC] Hincl Hfail. rewrite /updatePC /= in Hfail |- *.
  rewrite !HPC in Hfail. have -> := lookup_weaken _ _ _ _ HPC Hincl.
  destruct w as [| ? ? ? a1]; simplify_eq; auto;[].
  destruct (a1 + 1)%a; simplify_eq; auto.
Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H
  end; simplify_eq.

Lemma pair_eq_inv {A B} {y u : A} {z t : B} {x} :
    x = (y, z) -> x = (u, t) ->
    y = u ∧ z = t.
Proof. intros ->. inversion 1. auto. Qed.

(* TODO: integrate into stdpp? *)
Tactic Notation "simplify_pair_eq" :=
  repeat
    lazymatch goal with
    | H1 : ?x = (?y, ?z), H2 : ?x = (?u, ?t) |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 H2)); clear H2
    | H1 : (?y, ?z) = ?x, H2 : ?x = (?u, ?t) |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv (eq_sym H1) H2)); clear H2
    | H1 : ?x = (?y, ?z), H2 : (?u, ?t) = ?x |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 (eq_sym H2))); clear H2
    | H1 : (?y, ?z) = ?x, H2 : (?u, ?t) = ?x |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv (eq_sym H1) (eq_sym H2))); clear H2
    | |- _ => progress simplify_eq
    end.

(*----------------------- FIXME TEMPORARY ------------------------------------*)
(* This is a copy-paste from stdpp (fin_maps.v), plus a fix to avoid using
   "rewrite .. by .." that is not available when using ssreflect's rewrite. *)
(* TODO: upstream the fix into stdpp, and remove the code below whenever we
   upgrade to a version of stdpp that includes it *)

Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite lookup_insert in H || (rewrite lookup_insert_ne in H; [| by tac])
  | H : context[ (alter _ _ _) !! _] |- _ =>
    rewrite lookup_alter in H || (rewrite lookup_alter_ne in H; [| by tac])
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete in H || (rewrite lookup_delete_ne in H; [| by tac])
  | H : context[ {[ _ := _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton in H || (rewrite lookup_singleton_ne in H; [| by tac])
  | H : context[ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
  | H : context[ (omap _ _) !! _ ] |- _ => rewrite lookup_omap in H
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] =>
    rewrite lookup_insert || (rewrite lookup_insert_ne; [| by tac])
  | |- context[ (alter _ _ _) !! _ ] =>
    rewrite lookup_alter || (rewrite lookup_alter_ne; [| by tac])
  | |- context[ (delete _ _) !! _ ] =>
    rewrite lookup_delete || (rewrite lookup_delete_ne; [| by tac])
  | |- context[ {[ _ := _ ]} !! _ ] =>
    rewrite lookup_singleton || (rewrite lookup_singleton_ne; [| by tac])
  | |- context[ (_ <$> _) !! _ ] => rewrite lookup_fmap
  | |- context[ (omap _ _) !! _ ] => rewrite lookup_omap
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert (m !! i = Some x') as E by tac;
    rewrite E; clear E
  end.

Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map map_disjoint.

Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | H : {[ _ := _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ := _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    feed pose proof (lookup_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_weaken _ m2) in H1; [congruence|by tac]
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply map_union_cancel_l in H; [|by tac|by tac]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply map_union_cancel_r in H; [|by tac|by tac]
  | H : {[?i := ?x]} = ∅ |- _ => by destruct (map_non_empty_singleton i x)
  | H : ∅ = {[?i := ?x]} |- _ => by destruct (map_non_empty_singleton i x)
  | H : ?m !! ?i = Some _, H2 : ?m !! ?j = None |- _ =>
     unless (i ≠ j) by done;
     assert (i ≠ j) by (by intros ?; simplify_eq)
  end.
Tactic Notation "simplify_map_eq" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || simplify_map_eq by tac).
Tactic Notation "simplify_map_eq" :=
  simplify_map_eq by eauto with simpl_map map_disjoint.
Tactic Notation "simplify_map_eq" "/=" :=
  simplify_map_eq/= by eauto with simpl_map map_disjoint.
