From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang linking machine_run.

(** Minimal free memory in which to write our contexts *)
Definition reserved_context_size_z: Z := 100000.
Definition reserved_context_size: Addr := (za ^+ reserved_context_size_z)%a.

Lemma reserved_context_size_le_mem :
  (reserved_context_size_z < MemNum)%Z.
Proof.
  Transparent MemNum.
  unfold MemNum, reserved_context_size_z.
  lia.
Qed.

Lemma reserved_context_size_to_z :
  finz.to_z reserved_context_size = reserved_context_size_z.
Proof. simpl. lia. Qed.

Section contextual_refinement.
  Context {MP: MachineParameters}.

  (* Type of symbols to uniquely identify exports/inports. *)
  Context {Symbols : Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Definition unconstrained_addr : gset Addr -> Prop :=
    fun _ => True.
  Lemma unconstrained_addr_union_stable:
    ∀ dom1 dom2,
      unconstrained_addr dom1 -> unconstrained_addr dom2 ->
      unconstrained_addr (dom1 ∪ dom2).
  Proof. auto. Qed.

  Notation wf_comp := (well_formed_comp can_address_only (addr_gt_than reserved_context_size)).
  Infix "##ₗ" := (can_link can_address_only (addr_gt_than reserved_context_size)) (at level 70).

  (** This is the contextual refinement relation
      A component 'impl' contextually refines 'spec' if,
      for all contexts 'ctxt'
      if
      - 'ctxt' is a valid context to run 'impl' (implies that 'ctxt' is well-formed)
      - 'ctxt' linked with 'impl' terminates in a final state 'c'
        (either HALTED or FAILED)
      then
      - 'ctxt' is a valid context to run 'spec'
      - 'ctxt' linked with 'spce' also terminates in 'c' *)
  Inductive contextual_refinement impl spec : Prop :=
  | ctxt_ref_intro : forall
    (Hwf_impl : wf_comp impl)
    (Hwf_spec : wf_comp spec)
    (Hrefines :
      forall (ctxt: component Symbols) (regs:Reg) (c: ConfFlag),
        is_context can_address_only unconstrained_addr ctxt impl regs ->
        (exists n, machine_run n (Executable, (regs, segment (link ctxt impl))) = Some c) ->
        is_context can_address_only unconstrained_addr ctxt spec regs /\
          exists n, machine_run n (Executable, (regs, segment (link ctxt spec))) = Some c),
    contextual_refinement impl spec.

  Section facts.
    Lemma ctxt_ref_reflexive {comp}:
      wf_comp comp -> contextual_refinement comp comp.
    Proof.
      intros wcomp.
      apply ctxt_ref_intro. 1,2: exact wcomp.
      intros ctxt regs c ctxt_impl mr_ctxt_impl.
      split; assumption.
    Qed.

    Instance ctxt_ref_transitive: Transitive contextual_refinement.
    Proof.
      intros a b c a_b b_c.
      inversion a_b. inversion b_c.
      apply ctxt_ref_intro; try assumption.
      intros ctxt regs conf ctxt_a mr_ctxt_a.
      destruct (Hrefines ctxt regs conf ctxt_a mr_ctxt_a) as [ctxt_b mr_ctxt_b].
      apply (Hrefines0 ctxt regs conf ctxt_b mr_ctxt_b).
    Qed.

    Lemma addr_gt_than_implies_unconstrained:
      ∀ a, addr_gt_than reserved_context_size a -> unconstrained_addr a.
    Proof. intros. unfold unconstrained_addr. auto. Qed.

    Lemma ctxt_ref_link_l {common impl spec} :
      common ##ₗ impl -> common ##ₗ spec ->
      contextual_refinement impl spec ->
      contextual_refinement (link common impl) (link common spec).
    Proof.
      intros sep_impl sep_spec impl_spec.
      apply ctxt_ref_intro.
      1,2: apply (link_well_formed _ can_address_only_incr _ (addr_gt_than_union_stable _));
           assumption.
      intros ctxt regs c ctxt_impl mr_impl.
      inversion ctxt_impl. inversion impl_spec.
      pose (can_link_weaken_ar addr_gt_than_implies_unconstrained sep_impl) as common_impl.
      apply (is_context_move_in _ can_address_only_incr _ unconstrained_addr_union_stable common_impl) in ctxt_impl.
      symmetry in Hcan_link.
      pose (can_link_weaken_l _ _ common_impl Hcan_link) as ctxt_common.
      pose (can_link_weaken_r _ _ common_impl Hcan_link) as ctxt_impl'.
      symmetry in ctxt_common, ctxt_impl'.
      rewrite (link_assoc _ can_address_only_incr _ unconstrained_addr_union_stable ctxt_common ctxt_impl' common_impl) in mr_impl.
      destruct (Hrefines (link ctxt common) regs c ctxt_impl mr_impl) as [ctxt_spec mr_spec].
      inversion ctxt_spec.
      pose (can_link_weaken_ar addr_gt_than_implies_unconstrained sep_spec) as common_spec.
      split.
      apply (is_context_move_out _ can_address_only_incr _ unconstrained_addr_union_stable ctxt_common).
      exact Hwr_regs. exact ctxt_spec.
      rewrite (link_assoc _ can_address_only_incr _ unconstrained_addr_union_stable ctxt_common (can_link_weaken_l _ _ ctxt_common Hcan_link0) common_spec).
      exact mr_spec.
    Qed.

    Lemma ctxt_ref_link_r {common impl spec} :
      common ##ₗ impl -> common ##ₗ spec ->
      contextual_refinement impl spec ->
      contextual_refinement (link impl common) (link spec common).
    Proof.
      intros common_impl common_spec impl_spec.
      rewrite <- (link_comm _ _ common_impl).
      rewrite <- (link_comm _ _ common_spec).
      exact (ctxt_ref_link_l common_impl common_spec impl_spec).
    Qed.

    (* Lemma ctxt_ref_link {impl impl' spec spec'} :
      impl ##ₗ impl' -> spec ##ₗ spec' ->
      contextual_refinement impl spec ->
      contextual_refinement impl' spec' ->
      contextual_refinement (link impl impl') (link spec spec').
    Proof.
      intros imp spe is is'.
      apply (ctxt_ref_link_l imp)
      impl *)
  End facts.

End contextual_refinement.
