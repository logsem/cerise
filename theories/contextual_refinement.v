From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang linking machine_run.

(** Minimal free memory in which to write our contexts *)
Definition reserved_context_size: Addr := (za ^+ 100000)%a.

Section contextual_refinement.
  Context `{MachineParameters}.

  (* Type of symbols to uniquely identify exports/inports. *)
  Variable Symbols : Type.
  Variable Symbols_eq_dec: EqDecision Symbols.
  Variable Symbols_countable: Countable Symbols.

  (** A predicate that must hold on all word of our segments
      Typically that if it is a capability, it only points into the segment
      (given as second argument)

      When in doubt, instanciate this with can_address_only *)
  Variable word_restrictions: Word -> gset Addr -> Prop.

  (** Creating a link requires word_restrictions to remain true
      as the segment increases (to the link of two segments) *)
  Variable word_restrictions_incr:
    forall w dom1 dom2,
      dom1 ⊆ dom2 ->
      word_restrictions w dom1 ->
      word_restrictions w dom2.

  (** Contextual refinement requires word_restrictions to imply
      that capabilities only point to the given set *)
  Variable word_restrictions_implies_address_only:
      ∀ w dom, word_restrictions w dom -> can_address_only w dom.

  (** A predicate on the addresses used by our components
      Since memory is finite, we need have some free memory for our contexts
      otherwise any program that takes the whole memory would refine into anything

      When in doubt, instanciate this with [addr_gt_than reserved_context_size] *)
  Variable addr_restrictions: gset Addr -> Prop.

  (** Creating a link requires that addr_restriction remains true on unions *)
  Variable addr_restrictions_union_stable:
    forall dom1 dom2,
      addr_restrictions dom1 ->
      addr_restrictions dom2 ->
      addr_restrictions (dom1 ∪ dom2).

  (** Contextual refinement requires addr_restrictions to imply
      that the first [reserved_context_size] addresses are free *)
  Variable addr_restrictions_implies_addr_gt:
    ∀ dom, addr_restrictions dom -> addr_gt_than reserved_context_size dom.

  (** Register that holds the stack capability. Any != PC will do
      since we quantify over all programs *)
  Definition r_stk := r_t1.

  Section definition.

    (** Component with proof of their well-formedness *)
    Record component_wf := {
      comp : pre_component Symbols_countable;
      comp_is_wf : well_formed_pre_comp word_restrictions addr_restrictions comp
    }.

    (** Create a initial machine state from a component:
        - registers are all 0, except PC which is main, and r_stk which points to the stack
        - the memory is the one specified in the segment *)
    Definition initial_state (c: component Symbols_countable) :=
      match c with
      | Lib pre_comp => (∅, ∅) (* dummy value *)
      | Main pre_comp c_main =>
        (<[PC := c_main]> (gset_to_gmap (WInt 0) (list_to_set all_registers)),
        pre_comp.(segment))
      end.

    Definition unconstrained_addr : gset Addr -> Prop :=
      fun _ => True.

    (** This is the contextual refinement relation
        A component 'impl' contextually refines 'spec' if,
        for all contexts 'ctxt'
        if
        - 'ctxt' is well formed
        - 'ctxt' is a valid context to run 'impl'
        - 'ctxt' linked with 'impl' terminates in a final state 'c'
          (either HALTED or FAILED)
        then
        - 'ctxt' is a valid context to run 'spec'
        - 'ctxt' linked with 'spce' also terminates in 'c' *)
    Definition contextual_refinement : relation component_wf :=
      fun impl spec =>
      forall (context: pre_component Symbols_countable) (main:Word) (c: ConfFlag),
        let linked_impl := link_main_lib context impl.(comp) main in
        let linked_spec := link_main_lib context spec.(comp) main in
        let ctxt := Main context main in
        well_formed_comp word_restrictions unconstrained_addr ctxt ->
        is_context word_restrictions unconstrained_addr ctxt (Lib impl.(comp)) linked_impl ->
        (exists n, machine_run n (Executable, initial_state linked_impl) = Some c) ->
        is_context word_restrictions unconstrained_addr ctxt (Lib spec.(comp)) linked_spec /\
          (exists n, machine_run n (Executable, initial_state linked_spec) = Some c).
  End definition.

  Section facts.

    (** Contextual refinement is reflexive *)
    #[global] Instance ctxt_ref_reflexive : Reflexive contextual_refinement.
    Proof.
      intros [impl impl_wf] context main c linked_impl linked_spec ctxt wf_context is_ctxt1 mr.
      split; assumption.
    Qed.

    (** Contextual refinement is transitive *)
    #[global] Instance ctxt_ref_transitive : Transitive contextual_refinement.
    Proof.
      intros [lib_a a_wf] [lib_b b_wf] [lib_c c_wf] a_b b_c.
      intros context main c linked_a linked_c ctxt wf_context is_ctxt_a mr_a.
      destruct (a_b context main c wf_context is_ctxt_a mr_a) as [is_ctxt_b mr_b].
      apply (b_c context main c wf_context is_ctxt_b mr_b).
    Qed.

  End facts.

End contextual_refinement.
