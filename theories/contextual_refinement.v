From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang linking machine_run.

Section contextual_refinement.
  Context `{MachineParameters}.

  Variable b_stk: Addr.
  Variable e_stk: Addr.

  Definition Symbols := nat.
  (* Variable Symbols_eq_dec: EqDecision Symbols.
  Variable Symbols_countable: Countable Symbols. *)

  (** A predicate that must hold on all word of our segments
      Typically that if it is a capability, it only points into the segment
      (given as second argument)
      This should remain true if the segment increases *)
  Variable word_restrictions: Word -> gset Addr -> Prop.
  Variable word_restrictions_incr:
    forall w dom1 dom2,
      dom1 ⊆ dom2 ->
      word_restrictions w dom1 ->
      word_restrictions w dom2.

  #[local] Notation m_pre_component := (pre_component Symbols _ _).
  #[local] Notation m_component := (component Symbols _ _).
  #[local] Notation Main := (Main _ _ _).
  #[local] Notation Lib := (Lib _ _ _).

  #[local] Notation exports := (exports Symbols _ _).
  #[local] Notation imports := (imports Symbols _ _).

  #[local] Notation is_context := (is_context e_stk Symbols _ _ word_restrictions).
  #[local] Notation link := (link e_stk Symbols _ _ word_restrictions).

  #[local] Notation wf_pre_comp := (well_formed_pre_comp e_stk Symbols _ _ word_restrictions).

  Section ctxt_ref_def.
    Variable implementation specification: m_pre_component.
    Variable wf_impl : wf_pre_comp implementation.
    Variable wf_spec : wf_pre_comp specification.

    Definition initial_state
      `{MachineParameters} (r_stk: RegName)
      (b_stk e_stk: Addr) (c: m_component) :=
      match c with
      | Lib pre_comp => (∅, ∅) (* dummy value *)
      | Main (ms, _, _) c_main =>
        (<[r_stk := WCap RWX b_stk e_stk b_stk]>
        (<[PC := c_main]> (gset_to_gmap (WInt 0) (list_to_set all_registers))), ms)
      end.

    Definition contextual_refinement (r_stk: RegName) :=
      forall (context linked_impl linked_spec: m_component),
        is_context context (Lib implementation) linked_impl ->
        is_context context (Lib specification) linked_spec ->
        forall (c: ConfFlag),
          (exists n, machine_run n (Executable, initial_state r_stk b_stk e_stk linked_impl) = Some c) ->
          (exists n, machine_run n (Executable, initial_state r_stk b_stk e_stk linked_spec) = Some c).
  End ctxt_ref_def.


  Lemma contextual_reflexive (lib: m_pre_component) (r_stk: RegName) :
    contextual_refinement lib lib r_stk.
  Proof.
    intros context link1 link2 is_ctxt1 is_ctxt2 c [n run_n].
    exists n.
    rewrite <- (context_unique _ _ _ _ _ is_ctxt1 is_ctxt2).
    apply run_n.
  Qed.

  Lemma contextual_transitive (lib_a lib_b lib_c : m_pre_component) (r_stk: RegName) :
    contextual_refinement lib_a lib_b r_stk ->
    contextual_refinement lib_b lib_c r_stk ->
    contextual_refinement lib_a lib_c r_stk.
  Proof.
    intros a_b b_c ctxt link_a link_c is_link_a is_link_c c [n a].
    destruct ctxt as [ p | ctxt ].
    { inversion is_link_a.
    destruct His_program as [link_a' is_prgm].
    inversion link_a'. rewrite <- H0 in is_prgm.
    inversion is_prgm. }
    assert (is_context (Main ctxt w) (Lib lib_b) (make_link_main_lib _ _ _ lib_b ctxt w)).
    destruct ctxt as [[ms_ctxt imps_ctxt] exp_ctxt].
    destruct lib_b as [[ms_lib_b imps_lib_b] exp_lib_b].
    apply make_link_main_lib_is_context.

End contextual_refinement.
