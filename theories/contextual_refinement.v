From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang.
From cap_machine Require Import stdpp_img linking machine_run addr_reg_sample.

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

  (** A simple function generating dummy export (all 0)
      for a given list of imports, usefull for building contexts *)
  Section dummy_exports.
    Definition dummy_exports target : exports_type Symbols :=
      map_fold (fun _ s exp => <[s:=WInt 0]> exp)
      ∅ target.(imports).

    Lemma dummy_exports_spec target : forall s,
      match dummy_exports target !! s with
        | None => s ∉ img target.(imports)
        | Some w => w = WInt 0 /\ s ∈ img target.(imports)
      end.
    Proof.
      apply (map_fold_ind
        (fun m imp => ∀ k, match m !! k with
          | None => k ∉ img imp
          | Some w => w = WInt 0 /\ k ∈ img imp
        end)
        (fun (_:Addr) (s:Symbols) exp => <[s:=WInt 0]> exp)).
      intros s. rewrite lookup_empty. rewrite img_empty_L. set_solver.
      intros a s exp exp' imp IH k.
      destruct (Symbols_eq_dec s k) as [sk | sk].
      rewrite sk. rewrite lookup_insert.
      split. reflexivity. rewrite elem_of_img. exists a. apply lookup_insert.
      rewrite lookup_insert_ne. 2: exact sk.
      specialize (IH k). destruct (exp' !! k).
      destruct IH as [IHw Hexp].
      split. exact IHw.
      rewrite elem_of_img. rewrite elem_of_img in Hexp. destruct Hexp as [a' Hexp].
      exists a'. rewrite lookup_insert_ne. exact Hexp.
      intros aa'. rewrite aa' in imp. rewrite imp in Hexp. discriminate.
      rewrite elem_of_img. rewrite elem_of_img in IH.
      intros [a' Hexp].
      apply lookup_insert_Some in Hexp.
      destruct Hexp as [ [aa' ss'] | [aa' Hexpa'] ].
      contradiction.
      apply (IH (ex_intro _ _ Hexpa')).
    Qed.
    Lemma dummy_exports_lookup {target} :
      ∀ w, w ∈ img (dummy_exports target) -> w = WInt 0.
    Proof.
      intros w Hsw. apply elem_of_img in Hsw. destruct Hsw as [s Hsw].
      specialize (dummy_exports_spec target s). intros H.
      rewrite Hsw in H. destruct H. exact H.
    Qed.
    Lemma dummy_exports_from_imports {target} :
      dom (dummy_exports target) = img (target.(imports)).
    Proof.
      apply set_eq.
      intros s.
      specialize (dummy_exports_spec target s). intros H.
      rewrite elem_of_dom.
      split. intros [w Hde_s_w]. rewrite Hde_s_w in H. destruct H. exact H0.
      intros Himg.
      destruct (Some_dec (dummy_exports target !! s)) as [ [w Hexp_s] | Hexp_s];
      rewrite Hexp_s; rewrite Hexp_s in H. auto.
      contradiction.
    Qed.
  End dummy_exports.

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
      rewrite resolve_imports_exports_empty. reflexivity.
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
      apply lookup_union_Some_raw in Hw' as [Hw' | [_ Hw'] ].
      apply (can_address_only_subseteq_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      inversion ctxt_impl as [ [ [] ] ]. apply Hwr_exp. apply elem_of_img_rev in Hw'. assumption.
      apply (can_address_only_subseteq_stable2 w (dom (segment spec)) _ Hdom_spec).
      inversion Hcan_link. inversion Hwf_r. apply Hwr_exp. apply elem_of_img_rev in Hw'. assumption.

      assert (Hse: ∀ a' w, (segment ctxt ∪ segment spec) !! a' = Some w -> can_address_only w (dom (segment (ctxt ⋈ spec)))).
      intros a w Hw'.
      apply lookup_union_Some_raw in Hw' as [Hw' | [_ Hw'] ].
      apply (can_address_only_subseteq_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      inversion ctxt_impl as [ [ [] ] ]. apply Hwr_ms. apply elem_of_img_rev in Hw'. assumption.
      apply (can_address_only_subseteq_stable2 w (dom (segment spec)) _ Hdom_spec).
      inversion Hcan_link. inversion Hwf_r. apply Hwr_ms. apply elem_of_img_rev in Hw'. assumption.

      intros w Hw.
      apply elem_of_img in Hw as [a Hw].
      unfold link in Hw. simpl in Hw.
      rewrite resolve_imports_spec in Hw.
      destruct (imports spec !! a).
      destruct ((exports ctxt ∪ exports spec) !! s) eqn:He.
      apply Some_inj in Hw. rewrite <-Hw.
      apply elem_of_img_rev in He. apply (Hex _ He).
      1,2: rewrite resolve_imports_spec in Hw;
           destruct (imports ctxt !! a) as [s'|]; apply (Hse _ _ Hw) ||
           destruct ((exports ctxt ∪ exports spec) !! s') eqn:He';
           apply (Hse _ _ Hw) || apply Some_inj in Hw; rewrite <-Hw;
           apply elem_of_img_rev in He'; apply (Hex _ He').

      inversion ctxt_impl. intros w Hw.
      apply (can_address_only_subseteq_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      apply (Hwr_regs w Hw).
      Unshelve. solve_can_link.
    Qed.

    (* When a ≼ᵣ b then
       - dom (imports b) ⊆ dom (imports a)
       - dom (segment b) ⊆ dom (segment a) *)
    Section component_part_subseteq.
      (** Basic context to prove the forall is non-empty
          Halt immediatly *)
      Example halt_context addr target : component Symbols := {|
        segment := {[ addr := halt ]};
        imports := ∅;
        exports := dummy_exports target;
      |}.

      Lemma halt_context_wf {addr target}:
        well_formed_comp can_address_only unconstrained_addr (halt_context addr target).
      Proof.
        unfold halt_context.
        apply wf_comp_intro; simpl.
        - rewrite img_empty_L. apply disjoint_empty_r.
        - rewrite dom_empty. apply empty_subseteq.
        - intros w exp_s.
          apply dummy_exports_lookup in exp_s.
          rewrite exp_s. unfold can_address_only. exact I.
        - intros w H. apply img_singleton, elem_of_singleton in H.
          rewrite H. exact I.
        - exact I.
      Qed.

      Lemma halt_context_can_link {addr target} :
        wf_comp target -> addr ∉ dom (segment target) ->
        can_link can_address_only unconstrained_addr (halt_context addr target) target.
      Proof.
        intros t_wf Haddr.
        apply can_link_intro.
        - apply halt_context_wf.
        - apply (wf_comp_weaken_ar any_implies_unconstrained_addr t_wf).
        - rewrite map_disjoint_spec. intros i x y Hix Hiy.
          apply Haddr.
          unfold halt_context in Hix. simpl in Hix.
          apply lookup_singleton_Some in Hix as [Hi _].
          rewrite -Hi in Hiy. apply mk_is_Some, elem_of_dom in Hiy. apply Hiy.
        - inversion t_wf.
          rewrite map_disjoint_dom.
          rewrite dummy_exports_from_imports.
          symmetry. exact Hdisj.
      Qed.

      Lemma halt_context_machine_run {addr target} :
        wf_comp target -> addr ∉ dom (segment target) -> (addr <? addr ^+ 1 = true)%a ->
        machine_run 2 (Executable, (
          {[ PC := WCap RWX addr (addr^+1)%a addr ]},
          segment ((halt_context addr target) ⋈ target))
        ) = Some Halted.
      Proof.
        intros wft Haddr Haddr'.
        unfold machine_run.
        rewrite lookup_singleton.
        unfold isCorrectPCb.
        replace ((addr <=? addr)%a && (addr <? addr ^+ 1)%a && (isPerm RWX RX || isPerm RWX RWX)) with true.
        simpl.
        rewrite resolve_imports_spec.
        replace (imports target !! addr) with (@None Symbols).
        rewrite resolve_imports_spec lookup_empty.
        replace (({[addr := halt]} ∪ segment target) !! addr) with (Some halt).
        unfold exec, exec_opt, halt; rewrite (decode_encode_instrW_inv Halt); simpl.
        reflexivity.
        symmetry. apply lookup_union_Some_l. apply lookup_singleton.
        destruct (imports target !! addr) as [w|] eqn:Hita.
        exfalso. apply Haddr.
        inversion wft. apply Himp. apply mk_is_Some, elem_of_dom in Hita. apply Hita.
        reflexivity.
        simpl. symmetry. rewrite andb_true_iff. split.
        rewrite andb_true_iff. split. solve_finz. solve_addr. reflexivity.
        (* specialize (Har_ms addr (Himp addr Hita)).
        unfold finz.lt in Har_ms.
        rewrite reserved_context_size_to_z in Har_ms.
        simpl in Har_ms. unfold reserved_context_size_z in Har_ms.
        lia. reflexivity. *)
      Qed.

      Lemma halt_context_is_context {addr target} :
        wf_comp target -> addr ∉ dom (segment target) ->
        is_context can_address_only unconstrained_addr
          (halt_context addr target) target {[ PC := WCap RWX addr (addr^+1)%a addr ]}.
      Proof.
        intros Hwf_t Haddr.
        apply is_context_intro.
        - apply (halt_context_can_link Hwf_t Haddr).
        - intros w Hsr_w.
          apply img_singleton, elem_of_singleton in Hsr_w.
          rewrite Hsr_w.
          intros a Ha01. simpl. rewrite dom_singleton elem_of_singleton.
          solve_finz.
        - rewrite dummy_exports_from_imports. reflexivity.
        - simpl. rewrite img_empty_L. apply empty_subseteq.
      Qed.

      (** Contextual refinement implies that the
          implementation imports all the specifications symbols *)
      Lemma ctxt_ref_imports_subseteq {impl spec: component Symbols}:
        contextual_refinement impl spec ->
        img spec.(imports) ⊆ img impl.(imports).
      Proof.
        intros Href s Hspec_s.
        inversion Href.
        assert (H: 0%a ∉ (dom (segment impl))).
        { intros Hita. inversion Hwf_impl.
          specialize (Har_ms 0%a Hita). solve_finz. }
        assert (H1 : (0 <? 0 ^+ 1 = true)%a). auto.
        specialize (Hrefines
          (halt_context 0%a impl)
          {[ PC := WCap RWX za (za^+1)%a za ]} _
          (halt_context_is_context Hwf_impl H)
          (ex_intro _ 2 (halt_context_machine_run Hwf_impl H H1))).
        destruct Hrefines as [Hctxt_spec _].
        inversion Hctxt_spec.
        specialize (Hno_imps_l s Hspec_s).
        simpl in Hno_imps_l.
        rewrite dummy_exports_from_imports in Hno_imps_l.
        apply Hno_imps_l.
      Qed.

      Lemma ctxt_ref_segment_subseteq {impl spec}:
        impl ≼ᵣ spec ->
        dom spec.(segment) ⊆ dom impl.(segment).
      Proof.
        intros [ ] a Ha.
        destruct (segment impl !! a) as [w|] eqn:HeqA.
        apply mk_is_Some, elem_of_dom in HeqA. apply HeqA.
        apply not_elem_of_dom in HeqA.
        assert (H1 : (a <? a ^+ 1 = true)%a). admit.
        specialize (Hrefines
          (halt_context a impl)
          {[ PC := WCap RWX a (a^+1)%a a ]} _
          (halt_context_is_context Hwf_impl HeqA)
          (ex_intro _ 2 (halt_context_machine_run Hwf_impl HeqA H1))).
        destruct Hrefines as [Hctxt_spec _].
        inversion Hctxt_spec. inversion Hcan_link.
        rewrite map_disjoint_dom in Hms_disj.
        exfalso. apply (Hms_disj a).
        unfold halt_context. simpl. rewrite dom_singleton elem_of_singleton.
        reflexivity.
        assumption.
      Admitted.
    End component_part_subseteq.

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
