From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang.
From cap_machine Require Import stdpp_img linking machine_run.

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
    (Hexp_incl : dom (exports spec) ⊆ dom (exports impl))
    (Hrefines :
      forall (ctxt: component Symbols) (regs:Reg) (c: ConfFlag),
        is_context can_address_only unconstrained_addr ctxt impl regs ->
        (exists n, machine_run n (Executable, (regs, segment (ctxt ⋈ impl))) = Some c) ->
        is_context can_address_only unconstrained_addr ctxt spec regs /\
          exists n, machine_run n (Executable, (regs, segment (ctxt ⋈ spec))) = Some c),
    contextual_refinement impl spec.

  Infix "≼ᵣ" := contextual_refinement (at level 80).

  Section facts.
    Lemma ctxt_ref_reflexive {comp}:
      wf_comp comp -> comp ≼ᵣ comp.
    Proof.
      intros wcomp.
      apply ctxt_ref_intro. 1,2: exact wcomp.
      reflexivity.
      intros ctxt regs c ctxt_impl mr_ctxt_impl.
      split; assumption.
    Qed.

    Instance ctxt_ref_transitive: Transitive contextual_refinement.
    Proof.
      intros a b c a_b b_c.
      inversion a_b. inversion b_c.
      apply ctxt_ref_intro; try assumption.
      transitivity (dom (exports b)); assumption.
      intros ctxt regs conf ctxt_a mr_ctxt_a.
      destruct (Hrefines ctxt regs conf ctxt_a mr_ctxt_a) as [ctxt_b mr_ctxt_b].
      apply (Hrefines0 ctxt regs conf ctxt_b mr_ctxt_b).
    Qed.

    (* Infix "###" := (can_link can_address_only unconstrained_addr) (at level 70). *)

    Lemma ctxt_ref_grow_impl {impl spec extra}:
      extra ##ₗ impl -> exports extra = ∅ -> impl ≼ᵣ spec ->
      extra ⋈ impl ≼ᵣ spec.
    Proof.
      intros Hsep_ei Hexp [ ].
      apply ctxt_ref_intro.
      apply (link_well_formed _ _). solve_can_link. assumption.
      unfold link. simpl. clear Hexp. set_solver.
      intros ctxt regs c ctxt_impl mr_impl.
      apply (is_context_move_in _ _) in ctxt_impl as Hctxt; try solve_can_link.
      rewrite (link_assoc can_address_only unconstrained_addr) in mr_impl; try solve_can_link.
      destruct (Hrefines (ctxt ⋈ extra) regs c Hctxt mr_impl) as [Hc Hmr].
      split.
      eapply (is_context_remove_exportless_r _ _ _ Hexp).
      rewrite <- (link_comm can_address_only unconstrained_addr).
      apply (is_context_move_out can_address_only unconstrained_addr).
      all: try solve_can_link. inversion ctxt_impl.
      exact Hwr_regs. exact Hc.

      destruct Hmr as [n Hmr]. exists n.
      rewrite (@machine_run_segment_subseteq _ _ _ _ (segment (ctxt ⋈ spec)) (segment ((ctxt ⋈ extra) ⋈ spec))).
      exact Hmr.
      replace ((ctxt ⋈ extra) ⋈ spec) with ((ctxt ⋈ spec) ⋈ extra).
      2: {
        rewrite <- (link_assoc can_address_only unconstrained_addr).
        rewrite <- (link_assoc can_address_only unconstrained_addr).
        f_equal. apply (link_comm can_address_only unconstrained_addr).
        all: solve_can_link.
       }
      rewrite (link_segment_union can_address_only unconstrained_addr).
      rewrite (link_segment_union can_address_only unconstrained_addr).
      rewrite <- (link_segment_union can_address_only unconstrained_addr).
      2,3,4: solve_can_link.
      transitivity (resolve_imports (imports (ctxt ⋈ spec)) (exports extra) (segment (ctxt ⋈ spec))).
      rewrite Hexp.
      pose (@resolve_imports_exports_empty Symbols _ _) as ri.
      unfold exports_type in ri. rewrite ri. reflexivity.
      apply map_union_subseteq_l.
      inversion Hc.

      1,2: assert (Hdom_ctxt: dom (segment ctxt) ⊆ dom (segment (ctxt ⋈ spec))).
      1,3: apply (link_segment_dom_subseteq_l can_address_only unconstrained_addr);
           inversion ctxt_impl; try inversion Hcan_link0; inversion Hcan_link; try assumption.
           apply (wf_comp_weaken_ar any_implies_unconstrained_addr Hwf_spec).

      assert (Hdom_spec: dom (segment spec) ⊆ dom (segment (ctxt ⋈ spec))).
      apply (link_segment_dom_subseteq_r can_address_only unconstrained_addr);
      inversion ctxt_impl; try inversion Hcan_link0; inversion Hcan_link; assumption.

      assert (Hex: ∀ w, w ∈ img (exports ctxt ∪ exports spec) -> can_address_only w (dom (segment (ctxt ⋈ spec)))).
      intros w Hw'. apply elem_of_img in Hw' as [s Hw'].
      apply lookup_union_Some_raw in Hw' as [Hw' | [_ Hw']].
      apply (can_address_only_subseteq_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      inversion ctxt_impl as [[[]]]. apply Hwr_exp. apply elem_of_img_rev in Hw'. assumption.
      apply (can_address_only_subseteq_stable2 w (dom (segment spec)) _ Hdom_spec).
      inversion Hcan_link. inversion Hwf_r. apply Hwr_exp. apply elem_of_img_rev in Hw'. assumption.

      assert (Hse: ∀ a' w, (segment ctxt ∪ segment spec) !! a' = Some w -> can_address_only w (dom (segment (ctxt ⋈ spec)))).
      intros a w Hw'.
      apply lookup_union_Some_raw in Hw' as [Hw' | [_ Hw']].
      apply (can_address_only_subseteq_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      inversion ctxt_impl as [[[]]]. apply Hwr_ms. apply elem_of_img_rev in Hw'. assumption.
      apply (can_address_only_subseteq_stable2 w (dom (segment spec)) _ Hdom_spec).
      inversion Hcan_link. inversion Hwf_r. apply Hwr_ms. apply elem_of_img_rev in Hw'. assumption.

      intros w Hw.
      apply elem_of_img in Hw as [a Hw].
      unfold link in Hw. simpl in Hw.
      rewrite resolve_imports_spec in Hw.
      destruct (imports spec !! a).
      destruct ((exports ctxt ∪ exports spec) !! s) eqn:He;
      unfold exports_type in Hw; rewrite He in Hw. apply Some_inj in Hw. rewrite <-Hw.
      apply elem_of_img_rev in He. apply (Hex _ He).
      1,2: rewrite resolve_imports_spec in Hw;
           destruct (imports ctxt !! a) as [s'|]; apply (Hse _ _ Hw) ||
           destruct ((exports ctxt ∪ exports spec) !! s') eqn:He';
           unfold exports_type in Hw; rewrite He' in Hw;
           apply (Hse _ _ Hw) || apply Some_inj in Hw; rewrite <-Hw;
           apply elem_of_img_rev in He'; apply (Hex _ He').


      inversion ctxt_impl. intros w Hw.
      apply (can_address_only_subseteq_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      apply (Hwr_regs w Hw).

      Unshelve. solve_can_link.
    Qed.

    (* Lemma ctxt_ref_segment_subseteq {impl spec}:
      impl ≼ᵣ spec ->
      dom spec.(segment) ⊆ dom impl.(segment).
    Proof.
      intros [ ] a Ha. *)

    Lemma ctxt_ref_link_l {common impl spec} :
      common ##ₗ impl -> common ##ₗ spec ->
      impl ≼ᵣ spec ->
      common ⋈ impl ≼ᵣ common ⋈ spec.
    Proof.
      intros sep_impl sep_spec impl_spec.
      inversion impl_spec.
      apply ctxt_ref_intro.
      1,2: apply (link_well_formed _ can_address_only_incr _ (addr_gt_than_union_stable _));
           assumption.
      unfold link. simpl.
      rewrite (dom_union_L (exports common) (exports spec)).
      rewrite (dom_union_L (exports common) (exports impl)).
      apply union_subseteq. split.
      apply union_subseteq_l.
      transitivity (dom (exports impl)).
      exact Hexp_incl. apply union_subseteq_r.
      intros ctxt regs c ctxt_impl mr_impl.
      inversion ctxt_impl.
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
      impl ≼ᵣ spec ->
      impl ⋈ common ≼ᵣ spec ⋈ common.
    Proof.
      intros common_impl common_spec impl_spec.
      rewrite <- (link_comm _ _ common_impl).
      rewrite <- (link_comm _ _ common_spec).
      exact (ctxt_ref_link_l common_impl common_spec impl_spec).
    Qed.

    Lemma ctxt_ref_link {impl impl' spec spec'} :
      impl ##ₗ impl' -> spec ##ₗ spec' ->
      impl ≼ᵣ spec -> impl' ≼ᵣ spec' ->
      impl ⋈ impl' ≼ᵣ spec ⋈ spec'.
    Proof.
      intros Hii' Hss' His Hi's'.
      transitivity (spec ⋈ impl').
      apply ctxt_ref_link_r.
      symmetry. exact Hii'. admit. exact His.
      apply ctxt_ref_link_l. admit. exact Hss'. exact Hi's'.
    Admitted.

    From iris.program_logic Require Import adequacy.

    Search (rtc erased_step).

(*
    Context (Σ: gFunctors).
    Context {inv_preg: invGpreS Σ}. *)

    (* Let x := wp_invariance Σ (@cap_lang MP) NotStuck.
    Let y := (state cap_lang). *)

    From cap_machine Require Import stdpp_img.
    dom_insert_lookup_L

    Lemma ctxt_ref_segment_subseteq {impl spec}:
      contextual_refinement impl spec ->
      segment spec ⊆ segment impl.
    Proof.
      intros [ ].
      intros *)

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

Infix "≼ᵣ" := contextual_refinement (at level 80).
