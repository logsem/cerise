From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang linking machine_run.



Section contextual_refinement.
  Context `{MachineParameters}.

  Lemma machine_run_ends_in_halted_or_error:
    ∀ n init c, machine_run n init = Some c -> c = Halted \/ c = Failed.
  Proof.
    intros n.
    induction n; intros init c mr.
    - discriminate mr.
    - simpl in mr.
      destruct init as [[ | | | ] [r m]].
      destruct (r !! PC).
      destruct (isCorrectPCb w).
      destruct (m !! match w with
      | WInt _ => finz.largest 0%a
      | WCap _ _ _ a => a
      end). apply IHn in mr. apply mr.
      1,2,3,5: right; symmetry; apply Some_inj in mr; apply mr.
      left; symmetry. apply Some_inj in mr; apply mr.
      apply IHn in mr. apply mr.
  Qed.

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

  (** Register that holds the stack capability. Any != PC will do
      since we quantify over all programs *)
  Definition r_stk := r_t1.

  Section ctxt_ref_def.
    Variable implementation specification: m_pre_component.
    Variable wf_impl : wf_pre_comp implementation.
    Variable wf_spec : wf_pre_comp specification.

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

    Definition contextual_refinement :=
      forall (context linked_impl linked_spec: m_component),
        is_context context (Lib implementation) linked_impl ->
        is_context context (Lib specification) linked_spec ->
        forall (c: ConfFlag),
          (exists n, machine_run n (Executable, initial_state linked_impl) = Some c) ->
          (exists n, machine_run n (Executable, initial_state linked_spec) = Some c).
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
