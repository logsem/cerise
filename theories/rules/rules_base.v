From cap_machine Require Export lang mono_ref sts.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac auth.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invG Σ;
  mem_gen_memG :> gen_heapG Addr Word Σ;
  cap_γ : gname; }.

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
  
(* Points to predicates for memory *)
Notation "a ↦ₐ [ p ] w" := (MonRefMapsto a cap_γ (w,p))
  (at level 20, p at level 50, format "a  ↦ₐ [ p ]  w") : bi_scope.

Definition logN : namespace := nroot .@ "logN".

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
  

  (* --------------------------- CAPABILITY PREDICATE ------------------------------- *)
  Lemma gen_heap_valid_cap
        (σ : gmap Addr Word) (a : Addr) (w : Word) (p : Perm) :
    p ≠ O →
    gen_heap_ctx σ -∗ a ↦ₐ[p] w -∗ ⌜σ !! a = Some w⌝.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iIntros (Hne) "Hσ (Hex & Hal & [Ha | %])"; [|contradiction].
    iApply (gen_heap_valid with "Hσ Ha"). 
  Qed.

  Lemma cap_restrict (a : Addr) (w : Word) (p p' : Perm) :
    PermFlows p' p →
    a ↦ₐ[p] w ==∗ a ↦ₐ[p'] w.
  Proof.
    do 2 rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iIntros (Hf) "(Hex & Hal & Ha)".
    iFrame.
    iMod (MonRef_update (A:=A) with "Hex") as "[HE HFr']"; eauto.
    right with (w,p');[|left].
    constructor; auto.
    iFrame.
    iDestruct "Ha" as "[Ha | %]".
    - iLeft. by iFrame.
    - rewrite H2 in Hf. destruct p'; inversion Hf.
      by iRight. 
  Qed.

  Lemma gen_heap_update_cap (σ : gmap Addr Word) (a : Addr) (p : Perm) (w w' : Word) :
    p ≠ O →
    PermFlows (LeastPermUpd w') p →
    gen_heap_ctx σ -∗ a ↦ₐ[p] w ==∗ gen_heap_ctx (<[a:=w']> σ) ∗ a ↦ₐ[p] w'.
  Proof.
    do 2 rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iIntros (Ho Hf) "Hσ (Hex & Hal & [Ha | %])"; [|contradiction].
    iMod (MonRef_update (A:=A) with "Hex") as "[$ $]"; eauto.
    { right with (w',p); [|left]. by constructor. }
    by iMod (gen_heap_update with "Hσ Ha") as "[$ $]".
  Qed. 


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

  Ltac option_locate_mr m r :=
    repeat match goal with
    | H : m !! ?a = Some ?w |- _ => let Ha := fresh "H"a in
        assert (m !m! a = w) as Ha; [ by (unfold MemLocate; rewrite H) | clear H]
    | H : r !! ?a = Some ?w |- _ => let Ha := fresh "H"a in
        assert (r !r! a = w) as Ha; [ by (unfold RegLocate; rewrite H) | clear H]
           end.

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