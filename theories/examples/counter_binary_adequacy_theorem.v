From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.

From cap_machine Require Import
     stdpp_extra iris_extra
     logrel_binary fundamental_binary linking
     contextual_refinement ftlr_bin_ctxt_ref
     counter_binary_adequacy.

Definition is_initial_configuration_left `{memory_layout} c_adv r :=
  is_machine_context c_adv comp1 r.

Definition is_initial_configuration_right `{memory_layout} c_adv r :=
  is_machine_context c_adv comp2 r.

Definition soundness_binaryΣ : gFunctors :=
  #[GFunctor (authR cfgUR); invΣ; gen_heapΣ Addr Word;
   gen_heapΣ RegName Word;
   na_invΣ;
   sealStorePreΣ].

Global Instance inG_soundness_binaryΣ Σ : subG soundness_binaryΣ Σ → inG Σ (authR cfgUR).
Proof. solve_inG. Qed.


Theorem counter_adequacy_l `{MachineParameters} `{memory_layout}
        c_adv r reg' m' (es: list cap_lang.expr):
  is_initial_configuration_left c_adv r →
  is_initial_configuration_right c_adv r →
  is_initial_context c_adv r →
  rtc erased_step (initial_state (c_adv ⋈ comp1) r) (of_val HaltedV :: es, (reg', m')) →
  (∃ es' conf', rtc erased_step (initial_state (c_adv ⋈ comp2) r) (of_val HaltedV :: es', conf')).
Proof.
  intros. eapply (@confidentiality_adequacy_l' soundness_binaryΣ);last eauto;eauto.
  all: typeclasses eauto.
Qed.

Theorem counter_adequacy_r `{MachineParameters} `{memory_layout}
        c_adv r reg' m' (es: list cap_lang.expr):
  is_initial_configuration_left c_adv r →
  is_initial_configuration_right c_adv r →
  is_initial_context c_adv r →
  rtc erased_step (initial_state (c_adv ⋈ comp2) r) (of_val HaltedV :: es, (reg', m')) →
  (∃ es' conf', rtc erased_step (initial_state (c_adv ⋈ comp1) r) (of_val HaltedV :: es', conf')).
Proof.
  intros. eapply (@confidentiality_adequacy_r' soundness_binaryΣ);last eauto;eauto.
  all: typeclasses eauto.
Qed.

Theorem counter_ctx_equivalent `{MachineParameters} `{memory_layout}
        c_adv r :
  is_initial_configuration_left c_adv r →
  is_initial_configuration_right c_adv r →
  is_initial_context c_adv r →
  (∃ es conf, rtc erased_step (initial_state (c_adv ⋈ comp1) r) (of_val HaltedV :: es, conf)) ↔
  (∃ es conf, rtc erased_step (initial_state (c_adv ⋈ comp2) r) (of_val HaltedV :: es, conf)).
Proof.
  intros. split.
  - intros (?&[? ?]&?). eapply counter_adequacy_l;eauto.
  - intros (?&[? ?]&?). eapply counter_adequacy_r;eauto.
Qed.
