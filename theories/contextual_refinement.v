From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang linking machine_run.



Section contextual_refinement.
  Context `{MachineParameters}.

  Variable b_stk: Addr.
  Variable e_stk: Addr.

  (* Type of symbols to uniquely identify exports/inports. *)
  Variable Symbols : Type.
  Variable Symbols_eq_dec: EqDecision Symbols.
  Variable Symbols_countable: Countable Symbols.

  (** Predicate that states a word can only access addresses in a given set *)
  Definition can_address_only (word: Word) (addr_set: gset Addr) :=
    match word with
    | WInt _ => True
    | WCap _ b e _ => ∀ a, (b <= a < e)%a -> a ∈ addr_set
    end.

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

  #[local] Notation m_pre_component := (pre_component Symbols _ _).
  #[local] Notation m_component := (component Symbols _ _).
  #[local] Notation Main := (Main _ _ _).
  #[local] Notation Lib := (Lib _ _ _).

  #[local] Notation exports := (exports Symbols _ _).
  #[local] Notation imports := (imports Symbols _ _).

  #[local] Notation is_context := (is_context e_stk Symbols _ _ word_restrictions).
  #[local] Notation link := (link e_stk Symbols _ _ word_restrictions).

  #[local] Notation wf_pre_comp := (well_formed_pre_comp e_stk Symbols _ _ word_restrictions).

  #[local] Notation make_link_main_lib := (make_link_main_lib Symbols _ _).

  (** Register that holds the stack capability. Any != PC will do
      since we quantify over all programs *)
  Definition r_stk := r_t1.

  Section ctxt_ref_def.

    (** Component with proof of their well-formedness *)
    Definition component_wf := { x: m_pre_component | wf_pre_comp x }.

    (** Create a initial machine state from a component:
        - registers are all 0, except PC which is main, and r_stk which points to the stack
        - the memory is the one specified in the segment *)
    Definition initial_state (c: m_component) :=
      match c with
      | Lib pre_comp => (∅, ∅) (* dummy value *)
      | Main (ms, _, _) c_main =>
        (<[r_stk := WCap RWX b_stk e_stk b_stk]>
        (<[PC := c_main]> (gset_to_gmap (WInt 0) (list_to_set all_registers))), ms)
      end.

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
      fun implementation specification: component_wf =>
      let impl := proj1_sig implementation in
      let spec := proj1_sig specification in
      forall (context: m_pre_component) (main:Word) (c: ConfFlag),
        let linked_impl := make_link_main_lib context impl main in
        let linked_spec := make_link_main_lib context spec main in
        let ctxt := Main context main in
        well_formed_comp e_stk Symbols _ _ word_restrictions ctxt ->
        is_context ctxt (Lib impl) linked_impl ->
        (exists n, machine_run n (Executable, initial_state linked_impl) = Some c) ->
        is_context ctxt (Lib spec) linked_spec /\
          (exists n, machine_run n (Executable, initial_state linked_spec) = Some c).
  End ctxt_ref_def.

  Lemma contextual_reflexive : Reflexive contextual_refinement.
  Proof.
    intros [impl impl_wf] context main c linked_impl linked_spec ctxt wf_context is_ctxt1 mr.
    split; assumption.
  Qed.

  Lemma contextual_transitive : Transitive contextual_refinement.
  Proof.
    intros [lib_a a_wf] [lib_b b_wf] [lib_c c_wf] a_b b_c.
    intros context main c linked_a linked_c ctxt wf_context is_ctxt_a mr_a.
    destruct (a_b context main c wf_context is_ctxt_a mr_a) as [is_ctxt_b mr_b].
    apply (b_c context main c wf_context is_ctxt_b mr_b).
  Qed.


End contextual_refinement.
