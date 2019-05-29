From cap_machine Require Import rules.
From iris.proofmode Require Import tactics.

Section examples.
  Context `{memG Σ, regG Σ}.

  Lemma load_halt_1 pc_p pc_g pc_b pc_e pc_a pc_a1 wl wh w1 w2 r1 r2 p g b e a :
    cap_lang.decode wl = Load r1 r2 → cap_lang.decode wh = Halt →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a1 →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a1)) → (* these are annoying *)
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    r1 ≠ PC →
    
    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ wl
           ∗ pc_a1 ↦ₐ wh
           ∗ r1 ↦ᵣ w1
           ∗ r2 ↦ᵣ inr (p, g, b, e, a)
           ∗ a ↦ₐ w2 }}}
      (Seq (Instr Executable) : cap_lang.expr)
      {{{ RET HaltedV; r1 ↦ᵣ w2 }}}.
  Proof.
    intros Hil Hih Hvpc Hpca1 Hvpc' [Hra Hwb] Hne.
    iIntros (φ) "(Hpc & Hpca & Hpca' & Hr1 & Hr2 & Ha) Hφ".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_load_success _ _ _ _ _ _ _ pc_a with "[-Hpca' Hφ]"); eauto. iFrame.
    iNext. iIntros "(Hpc & Hr1 & _ & _ & _) /=".
    iApply wp_pure_step_later; eauto. iNext.z
    iApply (wp_bind (fill [SeqCtx])). 
    iApply (wp_halt _ _ _ _ _ pc_a1 with "[-Hr1 Hφ]"); eauto. iFrame. 
    iNext. iIntros "[_ _] /=".
    iApply wp_pure_step_later; eauto. iNext. 
    iApply wp_value. 
    iApply "Hφ". iFrame. 
  Qed.

End examples. 