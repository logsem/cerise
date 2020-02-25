From cap_machine Require Export lang mono_ref sts.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac auth.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invG Σ;
  mem_gen_memG :> gen_heapG Addr Word Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invG Σ;
  reg_gen_regG :> gen_heapG RegName Word Σ; }.


(* invariants for memory, and a state interpretation for (mem,reg) *)
Instance memG_irisG `{memG Σ, regG Σ} : irisG cap_lang Σ := {
  iris_invG := mem_invG;
  state_interp σ κs _ := ((gen_heap_ctx σ.1) ∗ (gen_heap_ctx σ.2))%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (mapsto (L:=RegName) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (mapsto (L:=RegName) (V:=Word) r 1 w) (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ { q } w" := (mapsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ { q }  w") : bi_scope.
Notation "a ↦ₐ w" := (mapsto (L:=Addr) (V:=Word) a 1 w) (at level 20) : bi_scope.

(* capabilities. We use the monotone monoid to construct a pointer which may only
   update according to its permission *)
Section Capabilities.

  Definition PermFlows : Perm → Perm → Prop := λ p1 p2, PermFlowsTo p1 p2 = true.
  Definition LeastPermUpd (w : Word) : Perm :=
    match w with
    | inl _ => RW
    | inr ((_,Global),_,_,_) => RW
    | _ => RWL
    end.

  Lemma PermFlows_refl : ∀ p, PermFlows p p.
  Proof.
    rewrite /PermFlows /PermFlowsTo.
    destruct p; auto.
  Qed.

  Lemma PermFlows_trans P1 P2 P3 :
    PermFlows P1 P2 → PermFlows P2 P3 → PermFlows P1 P3.
  Proof.
    intros Hp1 Hp2. rewrite /PermFlows /PermFlowsTo.
    destruct P1,P3,P2; simpl; auto; contradiction.
  Qed.

  Inductive CapR : relation (Word * Perm) :=
  | P_res w p1 p2 : PermFlows p1 p2 → CapR (w,p2) (w,p1)
  | W_upd w1 w2 p : PermFlows (LeastPermUpd w2) p → CapR (w1,p) (w2,p).

  Definition PerP := λ p1 p2, PermFlows p2 p1.
  Lemma PerP_refl : ∀ p, PerP p p.
  Proof. apply PermFlows_refl. Qed.
  Lemma PerP_trans : ∀ P1 P2 P3, PerP P1 P2 → PerP P2 P3 → PerP P1 P3.
  Proof.
    intros p1 p2 p3. rewrite /PerP /PermFlows /PermFlowsTo;
    intros Hp1 Hp2.
    destruct p1,p2,p3; simpl; auto.
  Qed.

  Definition CapR_rtc := rtc CapR.

  Instance WordPerm_Equiv : Equiv (leibnizO (Word * Perm)).
  Proof. apply _. Defined.

  Instance WordPerm_Dist : Dist (leibnizO (Word * Perm)).
  Proof. apply _. Defined.

  Global Instance CapR_rtc_ProperPreOrder : monocmra.ProperPreOrder CapR_rtc.
  Proof. split; apply _. Defined.

  Instance PermFlows_Equiv : Equiv (leibnizO Perm).
  Proof. apply _. Defined.

  Instance PermFlows_Dist : Dist (leibnizO Perm).
  Proof. apply _. Defined.

  Global Instance PerP_ProperPreOrder : monocmra.ProperPreOrder PerP.
  Proof.
    split; [|apply _].
    split; intro;[rewrite /Reflexive;apply PerP_refl|rewrite /Transitive;apply PerP_trans].
  Defined.

  Global Instance PermFlows_ProperPreOrder : monocmra.ProperPreOrder PermFlows.
  Proof.
    split; [|apply _].
    split; intro;[rewrite /Reflexive;apply PerP_refl|rewrite /Transitive;apply PermFlows_trans].
  Defined.

  Context `{MonRefG (leibnizO _) CapR_rtc Σ, !memG Σ}.
  Notation A := (leibnizO (Word * Perm)).

  Definition MonRefMapsto_def l γ (v : A) :=
    (Exact (A:=A) CapR_rtc γ v ∗ atleast (A:=A) CapR_rtc γ v
           ∗ (l ↦ₐ v.1 ∨ ⌜v.2 = O⌝))%I.
  (* if the permission is O, we do not have ownership of the location *)
  Definition MonRefMapsto_aux l γ v : seal (MonRefMapsto_def l γ v).
  Proof. by eexists. Qed.
  Definition MonRefMapsto l γ v : iProp Σ := (MonRefMapsto_aux l γ v).(unseal).
  Definition MonRefMapsto_eq l γ v :
    MonRefMapsto l γ v = MonRefMapsto_def l γ v :=
    (MonRefMapsto_aux l γ v).(seal_eq).

  Lemma MonRefAlloc l v p :
    l ↦ₐ v ==∗ ∃ γ, MonRefMapsto l γ (v,p).
  Proof.
    iIntros "Hl".
    iMod (MonRef_alloc (A:=A)) as (γ) "[HE Hal]"; eauto.
    iModIntro. iExists _.
    rewrite MonRefMapsto_eq /MonRefMapsto_def. iFrame.
  Qed.

  Lemma MonRefDealloc l γ v p :
    MonRefMapsto l γ (v,p) -∗
                 (l ↦ₐ v ∨ ⌜p = O⌝) ∗
       ∃ P, P ∗ (P -∗ ∀ w, ⌜CapR_rtc (v,p) w⌝ -∗
                       (l ↦ₐ w.1 ∨ ⌜w.2 = O⌝) ==∗ MonRefMapsto l γ w).
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros "(HE & Ha & Hl)".
    iFrame.
    iDestruct (MonRef_related (A:=A) with "HE Ha") as %Hab.
    iExists (Exact (A:=A) CapR_rtc γ (v,p) ∗
                   atleast (A:=A) CapR_rtc γ (v,p))%I; iFrame.
    iIntros "[HE Ha]". iIntros ([w p'] Hcap) "Hl /=".
    rewrite MonRefMapsto_eq /MonRefMapsto_def; iFrame.
    iMod (MonRef_update (A:=A) CapR_rtc γ (v,p) with "HE") as "[$ $]"; eauto.
  Qed.

  Lemma snap_shot l γ v : MonRefMapsto l γ v ==∗ atleast (A:=A) CapR_rtc γ v.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def atleast_eq /atleast_def.
    iIntros "(HE & Hal & Hl)"; eauto.
  Qed.

  Lemma recall l γ v w :
    atleast (A:=A) CapR_rtc γ w -∗ MonRefMapsto l γ v -∗ ⌜CapR_rtc w v⌝.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros "Hal (HE & Hal' & Hl)".
    iDestruct (MonRef_related with "HE Hal") as "?"; eauto.
  Qed.

  Instance Exact_Timeless : Timeless (Exact (A:=A) CapR_rtc γ v).
  Proof. apply _. Qed.

  Instance atleast_Timeless : Timeless (atleast (A:=A) CapR_rtc γ v).
  Proof.
    intros. rewrite (atleast_eq (A:=A) CapR_rtc γ v). apply _. Qed.

  Global Instance MonRefMapsto_Timeless : Timeless (MonRefMapsto l γ v).
  Proof.
    intros.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    apply _.
  Qed.

End Capabilities.

Section World.
  Local Definition STS : Type := (STS_states * STS_rels).

  Inductive RelW : (STS * bool) → (STS * bool) -> Prop :=
  | RelW_pr (W1 W2 : STS) : related_sts_priv W1.1 W2.1 W1.2 W2.2
                            -> RelW (W1,true) (W2,true)
  | RelW_pu (W1 W2 : STS) : related_sts_pub W1.1 W2.1 W1.2 W2.2
                            -> RelW (W1,false) (W2,false)
  | RelW_pu_to_pr (W1 W2 : STS) : related_sts_priv W1.1 W2.1 W1.2 W2.2
                              → RelW (W1,false) (W2,true).

  Instance PrivRelW_Equiv : Equiv (leibnizO (STS * bool)).
  Proof. apply _. Defined.

  Instance PrivRelW_Dist : Dist (leibnizO (STS * bool)).
  Proof. apply _. Defined.

  Global Instance PrivRelW_ProperPreOrder : monocmra.ProperPreOrder RelW.
  Proof.
    split; [|apply _].
    split; intro.
    - destruct x. destruct b.
      + apply RelW_pr. apply related_sts_priv_refl.
      + apply RelW_pu. apply related_sts_pub_refl.
    - intros y z. destruct x,y,z; inversion 1; inversion 1.
      + constructor. apply related_sts_priv_trans with s0.1 s0.2; auto.
      + constructor. apply related_sts_pub_trans with s0.1 s0.2; auto.
      + subst. constructor. apply related_sts_pub_priv_trans with s0.1 s0.2; auto.
      + subst. constructor. apply related_sts_priv_trans with s0.1 s0.2; auto.
  Defined.

End World.

Definition logN : namespace := nroot .@ "logN".

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

Ltac option_locate_mr_once m r :=
  match goal with
  | H : m !! ?a = Some ?w |- _ => let Ha := fresh "H"a in
                                assert (m !m! a = w) as Ha; [ by (unfold MemLocate; rewrite H) | clear H]
  | H : r !! ?a = Some ?w |- _ => let Ha := fresh "H"a in
                                assert (r !r! a = w) as Ha; [ by (unfold RegLocate; rewrite H) | clear H]
  end.

Ltac option_locate_mr m r :=
  repeat option_locate_mr_once m r.

Ltac inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1 :=
  match goal with
  | H : cap_lang.prim_step (Instr Executable) (r, m) _ ?e1 ?σ2 _ |- _ =>
    let σ := fresh "σ" in
    let e' := fresh "e'" in
    let σ' := fresh "σ'" in
    let Hstep' := fresh "Hstep'" in
    let He0 := fresh "He0" in
    let Ho := fresh "Ho" in
    let He' := fresh "H"e' in
    let Hσ' := fresh "H"σ' in
    let Hefs := fresh "Hefs" in
    let φ0 := fresh "φ" in
    let p0 := fresh "p" in
    let g0 := fresh "g" in
    let b0 := fresh "b" in
    let e2 := fresh "e" in
    let a0 := fresh "a" in
    let i := fresh "i" in
    let c0 := fresh "c" in
    let HregPC := fresh "HregPC" in
    let Hi := fresh "H"i in
    let Hexec := fresh "Hexec" in
    inversion Hstep as [ σ e' σ' Hstep' He0 Hσ Ho He' Hσ' Hefs |?|?|?];
    inversion Hstep' as [φ0 | φ0 p0 g0 b0 e2 a0 i c0 HregPC ? Hi Hexec];
    (simpl in *; try congruence );
    subst e1 σ2 φ0 σ' e' σ; try subst c0; simpl in *;
    try (rewrite HPC in HregPC;
         inversion HregPC;
         repeat match goal with
                | H : _ = p0 |- _ => destruct H
                | H : _ = g0 |- _ => destruct H
                | H : _ = b0 |- _ => destruct H
                | H : _ = e2 |- _ => destruct H
                | H : _ = a0 |- _ => destruct H
                end ; destruct Hi ; clear HregPC ;
         rewrite Hpc_a Hinstr /= ;
         rewrite Hpc_a Hinstr in Hstep)
  end.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRefG (leibnizO _) CapR_rtc Σ,
            World: MonRefG (leibnizO _) RelW Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.
  Notation A := (leibnizO (Word * Perm)).
  Notation P := (leibnizO Perm).
  Notation WORLD_S := (leibnizO ((STS_states * STS_rels) * bool)).
  Implicit Types M : WORLD_S.
  Implicit Types W : (STS_states * STS_rels).

  (* Definition atleast_p γ p := atleast (A:=P) PermFlows γ p. *)
  (* Definition Exact_p γ p := Exact (A:=P) PermFlows γ p. *)

  (* --------------------------- WORLD REL MONOID ----------------------------------- *)
  Definition atleast_w γ M := atleast (A:=WORLD_S) RelW γ M.
  Definition Exact_w γ M := Exact (A:=WORLD_S) RelW γ M.

  Lemma RelW_private M W γ :
    atleast_w γ M -∗ Exact_w γ (W,true) -∗ ⌜related_sts_priv M.1.1 W.1 M.1.2 W.2⌝.
  Proof.
    rewrite /atleast_w /Exact_w.
    iIntros "#HM HW".
    iDestruct (MonRef_related (A:=WORLD_S) with "HW HM") as %Hrel.
      by inversion Hrel; subst.
  Qed.

  Lemma RelW_public M W γ :
    atleast_w γ M -∗ Exact_w γ (W,false) -∗ ⌜related_sts_pub M.1.1 W.1 M.1.2 W.2⌝.
  Proof.
    rewrite /atleast_w /Exact_w.
    iIntros "#HM HW".
    iDestruct (MonRef_related (A:=WORLD_S) with "HW HM") as %Hrel.
      by inversion Hrel; subst.
  Qed.

  Lemma RelW_public_to_private W γ :
    Exact_w γ (W,false) ==∗ Exact_w γ (W,true) ∗ atleast_w γ (W,true).
  Proof.
    iIntros "HW".
    iMod (MonRef_update (A:=WORLD_S) with "HW"); auto.
    constructor. apply related_sts_priv_refl.
  Qed.

  (* ----------------------------- LOCATΕ LEMMAS ----------------------------------- *)

  Lemma locate_ne_reg reg r1 r2 w w' :
    r1 ≠ r2 → reg !r! r1 = w → <[r2:=w']> reg !r! r1 = w.
  Proof.
    intros. rewrite /RegLocate.
    rewrite lookup_partial_alter_ne; eauto.
  Qed.

  Lemma locate_eq_reg reg r1 w w' :
    reg !r! r1 = w → <[r1:=w']> reg !r! r1 = w'.
  Proof.
    intros. rewrite /RegLocate.
    rewrite lookup_partial_alter; eauto.
  Qed.

  Lemma locate_ne_mem mem a1 a2 w w' :
    a1 ≠ a2 → mem !m! a1 = w → <[a2:=w']> mem !m! a1 = w.
  Proof.
    intros. rewrite /MemLocate.
    rewrite lookup_partial_alter_ne; eauto.
  Qed.

  (* ------------------------- registers points-to --------------------------------- *)

  Lemma regname_dupl_false r w1 w2 :
    r ↦ᵣ w1 -∗ r ↦ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %?.
    contradiction.
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

  (* -------------- semantic heap + a map of pointsto -------------------------- *)

  Lemma gen_heap_valid_inSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
      (σ σ' : gmap L V) (l : L) (q : Qp) (v : V),
      σ' !! l = Some v →
      gen_heap_ctx σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k q y) -∗
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
      gen_heap_ctx σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k q y) -∗
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
      gen_heap_ctx σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k q y) -∗
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
      gen_heap_ctx σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k q y) -∗
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
      gen_heap_ctx σ
      -∗ ([∗ map] k↦y ∈ σ', mapsto k 1 y)
      ==∗ gen_heap_ctx (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), mapsto k 1 y.
  Proof.
    intros * Hσ'. destruct Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=v]> σ') l).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.

  (* Permission-carrying memory type, used to describe maps of locations and permissions in the load and store cases *)
  Definition PermMem := gmap Addr (Perm * Word).


  (* --------------------------- CAPABILITY PREDICATE ------------------------------- *)
  (* Points to predicates for memory *)
  Notation "a ↦ₐ [ p ] w" := (∃ cap_γ, MonRefMapsto a cap_γ (w,p))%I
             (at level 20, p at level 50, format "a  ↦ₐ [ p ]  w") : bi_scope.

  Lemma gen_heap_valid_cap
        (σ : gmap Addr Word) (a : Addr) (w : Word) (p : Perm) :
    p ≠ O →
    gen_heap_ctx σ -∗ a ↦ₐ[p] w -∗ ⌜σ !! a = Some w⌝.
  Proof.
    iIntros (Hne) "Hσ Ha".
    iDestruct "Ha" as (γ_cap) "Ha".
    rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iDestruct "Ha" as "(Hex & Hal & [Ha | %])"; [|contradiction].
    iApply (gen_heap_valid with "Hσ Ha").
  Qed.

  Lemma cap_duplicate_false a p p' w w' :
    p ≠ O ∧ p' ≠ O →
    a ↦ₐ[p] w ∗ a ↦ₐ[p'] w' -∗ False.
  Proof.
    iIntros ([Hne1 Hne2]) "[Ha1 Ha2]".
    iDestruct "Ha1" as (γ1) "Ha1".
    iDestruct "Ha2" as (γ2) "Ha2".
    do 2 rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iDestruct "Ha1" as "(_ & _ & [Ha | %])"; [|contradiction].
    iDestruct "Ha2" as "(_ & _ & [Ha' | %])"; [|contradiction].
    iDestruct (mapsto_valid_2 with "Ha Ha'") as %Hcontr. done.
  Qed.

  Lemma cap_restrict (a : Addr) (w : Word) (p p' : Perm) :
    PermFlows p' p →
    a ↦ₐ[p] w ==∗ a ↦ₐ[p'] w.
  Proof.
    iIntros (Hfl) "Ha".
    iDestruct "Ha" as (γ_cap) "Ha". iExists (γ_cap).
    do 2 rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iDestruct "Ha" as "(Hex & Hal & Ha)".
    iMod (MonRef_update (A:=A) with "Hex") as "[HE HFr']"; eauto.
    right with (w,p');[|left].
    constructor; auto.
    iFrame.
    iDestruct "Ha" as "[Ha | %]".
    - iLeft. by iFrame.
    - rewrite H2 in Hfl. destruct p'; inversion Hfl.
      by iRight.
  Qed.

  Lemma gen_heap_update_cap (σ : gmap Addr Word) (a : Addr) (p : Perm) (w w' : Word) :
    p ≠ O →
    PermFlows (LeastPermUpd w') p →
    gen_heap_ctx σ -∗ a ↦ₐ[p] w ==∗ gen_heap_ctx (<[a:=w']> σ) ∗ a ↦ₐ[p] w'.
  Proof.
    iIntros (Ho Hf) "Hσ Ha".
    iDestruct "Ha" as (γ_cap) "Ha". iApply bi.sep_exist_l. iExists γ_cap.
    do 2 rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iDestruct "Ha" as "(Hex & Hal & [Ha | %])"; [|contradiction].
    iMod (MonRef_update (A:=A) with "Hex") as "[$ $]"; eauto.
    { right with (w',p); [|left]. by constructor. }
    by iMod (gen_heap_update with "Hσ Ha") as "[$ $]".
  Qed.


  Lemma cap_lang_determ:
    forall e1 σ1 κ κ' e2 e2' σ2 σ2' efs efs',
      cap_lang.prim_step e1 σ1 κ e2 σ2 efs ->
      cap_lang.prim_step e1 σ1 κ' e2' σ2' efs' ->
      κ = κ' /\ e2 = e2' /\ σ2 = σ2' /\ efs = efs'.
  Proof.
    intros. inv H2; inv H3; auto.
    inv H2; inv H4; auto; try congruence.
    rewrite H7 in H6; inv H6. auto.
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
      iDestruct "H" as %?.
      iDestruct "H1" as %?.
      destruct (cap_lang_determ _ _ _ _ _ _ _ _ _ _ H4 H3) as [Heq1 [Heq2 [Heq3 Heq4]]].
      subst a; subst a0; subst a1.
      iMod "H2". iModIntro. iFrame.
      inv H3; auto.
  Qed.

End cap_lang_rules.

(* Points to predicates for memory *)
Notation "a ↦ₐ [ p ] w" := (∃ cap_γ, MonRefMapsto a cap_γ (w,p))%I
  (at level 20, p at level 50, format "a  ↦ₐ [ p ]  w") : bi_scope.


(* ----------------- useful definitions to factor out the wp specs ---------------- *)

(*--- z_of_argument ---*)

Definition z_of_argument (regs: Reg) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !! r with
    | Some (inl z) => Some z
    | _ => None
    end
  end.

(*--- regs_of ---*)

Definition regs_of_argument (arg: Z + RegName): gset RegName :=
  match arg with
  | inl _ => ∅
  | inr r => {[ r ]}
  end.

Definition regs_of (i: instr): gset RegName :=
  match i with
  | Lea r1 arg => {[ r1 ]} ∪ regs_of_argument arg
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
  | Some (inr ((p, g), b, e, a)) =>
    match (a + 1)%a with
    | Some a' => Some (<[ PC := inr ((p, g), b, e, a') ]> regs)
    | None => None
    end
  | _ => None
  end.

Lemma incrementPC_Some_inv regs regs' :
  incrementPC regs = Some regs' ->
  exists p g b e a a',
    regs !! PC = Some (inr ((p, g), b, e, a)) ∧
    (a + 1)%a = Some a' ∧
    regs' = <[ PC := inr ((p, g), b, e, a') ]> regs.
Proof.
  unfold incrementPC.
  destruct (regs !! PC) as [ [| [ [ [ [? ?] ?] ?] u] ] |];
    try congruence.
  case_eq (u+1)%a; try congruence. intros ? ?. inversion 1.
  do 6 eexists. split; eauto.
Qed.

Lemma incrementPC_None_inv regs p g b e a :
  incrementPC regs = None ->
  regs !! PC = Some (inr ((p, g), b, e, a)) ->
  (a + 1)%a = None.
Proof.
  unfold incrementPC.
  destruct (regs !! PC) as [ [| [ [ [ [? ?] ?] ?] u] ] |];
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
  rewrite HPC HPC' in Hi |- *.
  destruct c as [| ((((?&?)&?)&?)&aa)]; first by auto.
  destruct (aa+1)%a; last by auto. congruence.
Qed.

(* todo: instead, define updatePC on top of incrementPC *)
Lemma incrementPC_fail_updatePC regs m :
   incrementPC regs = None ->
   updatePC (regs, m) = (Failed, (regs, m)).
Proof.
   rewrite /incrementPC /updatePC /RegLocate /=.
   destruct (regs !! PC) as [X|]; auto.
   destruct X as [| [[[[? ?] ?] ?] a']]; auto.
   destruct (a' + 1)%a; auto. congruence.
Qed.

Lemma incrementPC_success_updatePC regs m regs' :
  incrementPC regs = Some regs' ->
  ∃ p g b e a a',
    regs !! PC = Some (inr ((p, g, b, e, a))) ∧
    (a + 1)%a = Some a' ∧
    updatePC (regs, m) = (NextI, (<[ PC := inr ((p, g), b, e, a') ]> regs, m)) ∧
    regs' = <[ PC := inr ((p, g), b, e, a') ]> regs.
Proof.
  rewrite /incrementPC /updatePC /update_reg /RegLocate /=.
  destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
  destruct X as [| [[[[? ?] ?] ?] a']] eqn:?; try congruence; [].
  destruct (a' + 1)%a eqn:?; [| congruence]. inversion 1; subst regs'.
  do 6 eexists. repeat split; auto.
Qed.

Lemma updatePC_success_incl m m' regs regs' w :
  regs ⊆ regs' →
  updatePC (regs, m) = (NextI, (<[ PC := w ]> regs, m)) →
  updatePC (regs', m') = (NextI, (<[ PC := w ]> regs', m')).
Proof.
  intros * Hincl Hu. rewrite /updatePC /= in Hu |- *.
  destruct (regs !! PC) as [ w1 |] eqn:Hrr.
  { pose proof (regs_lookup_eq _ _ _ Hrr) as Hrr2. rewrite Hrr2 in Hu.
    pose proof (lookup_weaken _ _ _ _ Hrr Hincl) as ->%regs_lookup_eq.
    destruct w1 as [|((((?&?)&?)&?)&a1)]; simplify_eq.
    destruct (a1 + 1)%a eqn:Ha1; simplify_eq. rewrite /update_reg /=.
    f_equal. f_equal.
    assert (HH: forall (reg1 reg2:Reg), reg1 = reg2 -> reg1 !! PC = reg2 !! PC)
      by (intros * ->; auto).
    apply HH in Hu. rewrite !lookup_insert in Hu. by simplify_eq. }
  { unfold RegLocate in Hu. rewrite Hrr in Hu. inversion Hu. }
Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H
  end; simplify_eq.

(* TODO: add to stdpp *)
Lemma lookup_insert_is_Some_weaken
  {K : Type} {M : Type → Type} `{FMap M} `{∀ A : Type, Lookup K A (M A)} `{∀ A : Type, Empty (M A)}
             `{∀ A : Type, PartialAlter K A (M A)} `{OMap M} `{Merge M}
             `{∀ A : Type, FinMapToList K A (M A)} `{EqDecision K} `{FinMap K M} :
  ∀ {A : Type} (m : M A) (i j : K) (x : A),
    is_Some (m !! j) → is_Some (<[i:=x]> m !! j).
Proof.
  intros. rewrite lookup_insert_is_Some. destruct (decide (i = j)); auto.
Qed.

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
