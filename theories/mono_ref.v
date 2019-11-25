From iris.algebra Require Import auth frac gmap agree.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From cap_machine Require Import monocmra.


(** An example of using the monotone monoid construction to create
    monotone refrences. *)

Section Resources.
  Context {A : ofeT} {R : relation A}.

  Class MonRefG Σ := monrefG {
    MonRefIG_monauth :> inG Σ (authUR (monotoneUR R));
  }.

  Definition MonRefΣ :=
    #[GFunctor (authUR (monotoneUR R))].

  Instance subG_MonRefIGΣ {Σ} : subG MonRefΣ Σ → MonRefG Σ.
  Proof. solve_inG. Qed.
End Resources.

Global Arguments MonRefG {_} _ _.

Section MonRef.
  Context {A : ofeT} (R : relation A) `{!ProperPreOrder R}.
  Context `{!MonRefG R Σ}.

  Definition Exact γ v :=
    (own γ (● (principal R v)))%I.

  Definition atleast_def γ v :=
    (own γ (◯ (principal R v)))%I.
  Definition atleast_aux γ v : seal (atleast_def γ v). by eexists. Qed.
  Definition atleast γ v : iProp Σ := (atleast_aux γ v).(unseal).
  Definition atleast_eq γ v : atleast γ v = atleast_def γ v :=
    (atleast_aux γ v).(seal_eq).

  Lemma MonRef_related γ v w :
    Exact γ v -∗ atleast γ w -∗ ⌜R w v⌝.
  Proof.
    rewrite atleast_eq /atleast_def /Exact.
    iIntros "HF Hf".
    iDestruct (own_valid_2 with "HF Hf") as %[Hv Hvl]%auth_valid_discrete;
      simpl in *.
    destruct Hvl as [a [Hag [Hvl Ha]]].
    iAssert ((principal R v) ≡ a)%I as %Heq.
    { iApply agree_equivI; auto. }
    iPureIntro.
    apply (principal_included w v).
    rewrite Heq. 
    rewrite left_id_L in Hvl. auto. 
  Qed.

  Global Instance atleas_presistent l v : Persistent (atleast l v).
  Proof. rewrite atleast_eq /atleast_def; apply _. Qed.

  Lemma MonRef_alloc v :
    (|==> ∃ γ, Exact γ v ∗ atleast γ v)%I.
  Proof.
    setoid_rewrite atleast_eq. rewrite /atleast_def /Exact.
    iMod (own_alloc (● (principal R v) ⋅ ◯ (principal R v))) as (γ) "[HF Hf]".
    { rewrite auth_valid_eq /=; split; first done. intros ?; rewrite left_id_L.
      exists (principal R v). repeat (split;auto). }
    iModIntro; iExists _; iSplitL "HF"; iFrame; eauto.
  Qed.

  Lemma MonRef_update γ v w :
    R v w →
    Exact γ v ==∗ Exact γ w ∗ atleast γ w.
  Proof.
    rewrite atleast_eq /atleast_def.
    iIntros (HR) "HF".
    iDestruct "HF" as "HF"; simplify_eq.
    iMod (own_update _ _ (● (principal R w) ⋅ ◯ (principal R w))
            with "HF") as "[HF Hf]".
    { apply auth_update_alloc.
      apply local_update_unital_discrete => mz _ HM.
      split; first done. rewrite left_id_L in HM.
      rewrite -HM (comm op) principal_R_op; eauto. }
    iModIntro; iSplitL "HF"; eauto.
  Qed.

  Lemma MonRef_update' γ v w :
    R v w →
    Exact γ v ==∗ Exact γ w ∗ atleast γ w.
  Proof.
    rewrite atleast_eq /atleast_def.
    iIntros (HR) "HF".
    iDestruct "HF" as "HF"; simplify_eq.
    iMod (own_update _ _ (● (principal R w) ⋅ ◯ (principal R w))
            with "HF") as "[HF Hf]".
    { apply auth_update_alloc.
      apply local_update_unital_discrete => mz _ HM.
      split; first done. rewrite left_id_L in HM.
      rewrite -HM (comm op) principal_R_op; eauto. }
    iModIntro; iSplitL "HF"; eauto.
  Qed.

End MonRef.
