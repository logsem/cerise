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

  Notation is_ctxt := (is_context can_address_only unconstrained_addr).
  Infix "###ₗ" := (can_link can_address_only unconstrained_addr) (at level 70).


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
        is_ctxt ctxt impl regs ->
        (∃ n, machine_run n (Executable, (regs, segment (ctxt ⋈ impl))) = Some c) ->
        is_ctxt ctxt spec regs /\
          ∃ n, machine_run n (Executable, (regs, segment (ctxt ⋈ spec))) = Some c),
    contextual_refinement impl spec.

  Infix "≼ᵣ" := contextual_refinement (at level 80).

  (** Easy results about contextual refinement *)
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

    (** This can be weakened, since
        (common ##ₗ impl) and (impl ≼ᵣ spec) implies
        (common ##ₗ spec).

        See ctxt_ref_link_l for the stronger version *)
    Lemma ctxt_ref_link_l_1 {common impl spec} :
      common ##ₗ impl -> common ##ₗ spec ->
      impl ≼ᵣ spec ->
      common ⋈ impl ≼ᵣ common ⋈ spec.
    Proof.
      intros sep_impl sep_spec impl_spec.
      inversion impl_spec.
      apply ctxt_ref_intro.
      1,2: apply (link_well_formed _ _); assumption.
      unfold link. simpl.
      rewrite (dom_union_L (exports common) (exports spec)).
      rewrite (dom_union_L (exports common) (exports impl)).
      apply union_subseteq. split.
      apply union_subseteq_l.
      transitivity (dom (exports impl)).
      exact Hexp_incl. apply union_subseteq_r.
      intros ctxt regs c ctxt_impl mr_impl.
      inversion ctxt_impl.
      apply (is_context_move_in _ _) in ctxt_impl as HC.
      rewrite (link_assoc can_address_only unconstrained_addr) in mr_impl.
      destruct (Hrefines (link ctxt common) regs c HC mr_impl) as [ctxt_spec mr_spec].
      split.
      apply (is_context_move_out _ _). solve_can_link.
      exact Hwr_regs. exact ctxt_spec.
      rewrite (link_assoc can_address_only unconstrained_addr).
      exact mr_spec.
      all: solve_can_link.
    Qed.

    (** Same as above, one hypothesis is redundant,
        see ctxt_ref_link_r for the stronger_version *)
    Lemma ctxt_ref_link_r_1 {common impl spec} :
      common ##ₗ impl -> common ##ₗ spec ->
      impl ≼ᵣ spec ->
      impl ⋈ common ≼ᵣ spec ⋈ common.
    Proof.
      intros common_impl common_spec impl_spec.
      rewrite <- (link_comm _ _ common_impl).
      rewrite <- (link_comm _ _ common_spec).
      exact (ctxt_ref_link_l_1 common_impl common_spec impl_spec).
    Qed.

    (** Same as above, some hypotheses are redundant,
        see ctxt_ref_link for the stronger_version *)
    Lemma ctxt_ref_link_1 {impl impl' spec spec'} :
      impl ##ₗ impl' -> spec ##ₗ spec' ->
      impl' ##ₗ spec ->
      impl ≼ᵣ spec -> impl' ≼ᵣ spec' ->
      impl ⋈ impl' ≼ᵣ spec ⋈ spec'.
    Proof.
      intros Hii' Hss' His' His Hi's'.
      transitivity (spec ⋈ impl').
      apply ctxt_ref_link_r_1; solve_can_link || assumption.
      apply ctxt_ref_link_l_1; solve_can_link || assumption.
    Qed.

  End facts.

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

  (* When a ≼ᵣ b then
      - img (imports b) ⊆ img (imports a)
      - dom (segment b) ⊆ dom (segment a)
      - exports b = exports a (not proved here) *)
  Section component_part_subseteq.
    (** Basic context to prove the forall is non-empty
        Halt immediatly *)
    Example halt_context target : component Symbols := {|
      segment := {[ 0%a := halt ]};
      imports := ∅;
      exports := dummy_exports target;
    |}.

    Lemma halt_context_wf {target}:
      well_formed_comp can_address_only unconstrained_addr (halt_context target).
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

    Lemma halt_context_can_link {target} :
      wf_comp target ->
      can_link can_address_only unconstrained_addr (halt_context target) target.
    Proof.
      intros t_wf.
      apply can_link_intro.
      - apply halt_context_wf.
      - apply (wf_comp_weaken_ar any_implies_unconstrained_addr t_wf).
      - rewrite map_disjoint_spec. intros i x y Hix Hiy.
        unfold halt_context in Hix. simpl in Hix.
        apply lookup_singleton_Some in Hix as [Hi _].
        rewrite -Hi in Hiy. apply mk_is_Some, elem_of_dom in Hiy.
        inversion t_wf. specialize (Har_ms 0%a Hiy). solve_addr.
      - inversion t_wf.
        rewrite map_disjoint_dom.
        rewrite dummy_exports_from_imports.
        symmetry. exact Hdisj.
    Qed.

    Lemma halt_context_machine_run {target comp: component Symbols} :
      wf_comp comp ->
      machine_run 2 (Executable, (
        {[ PC := WCap RWX za (za^+1)%a za ]},
        segment ((halt_context target) ⋈ comp))
      ) = Some Halted.
    Proof.
      intros Hwf.
      unfold machine_run.
      rewrite lookup_singleton.
      unfold isCorrectPCb.
      assert (H: (0 <=? 0)%a && (0 <? 0 ^+ 1)%a && (isPerm RWX RX || isPerm RWX RWX) = true).
      auto. rewrite H. simpl. rewrite resolve_imports_spec.
      destruct (imports comp !! 0%a) as [w|] eqn:Hita.
      inversion Hwf. apply mk_is_Some, elem_of_dom in Hita.
      specialize (Har_ms 0%a (Himp 0%a Hita)). solve_addr.
      rewrite resolve_imports_spec lookup_empty.
      replace (({[0%a := halt]} ∪ segment comp) !! 0%a) with (Some halt).
      unfold exec, exec_opt, halt; rewrite (decode_encode_instrW_inv Halt); simpl.
      reflexivity.
      symmetry. apply lookup_union_Some_l. apply lookup_singleton.
    Qed.

    Lemma halt_context_is_context {target} :
      wf_comp target ->
      is_ctxt (halt_context target) target {[ PC := WCap RWX 0%a (0%a^+1)%a 0%a ]}.
    Proof.
      intros Hwf.
      apply is_context_intro.
      - apply (halt_context_can_link Hwf).
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
      impl ≼ᵣ spec -> img spec.(imports) ⊆ img impl.(imports).
    Proof.
      intros Href s Hspec_s.
      inversion Href.
      specialize (Hrefines
        (halt_context impl)
        {[ PC := WCap RWX 0%a (0^+1)%a 0%a ]} _
        (halt_context_is_context Hwf_impl)
        (ex_intro _ 2 (halt_context_machine_run Hwf_impl))).
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
      pose ({|
        segment := {[ a := WInt 0 ]};
        imports := ∅ : imports_type Symbols;
        exports := ∅ |}) as sa.
      assert (Hwf: wf_comp sa). unfold sa.
      { apply wf_comp_intro; simpl. set_solver. set_solver.
        - intros w Hw. apply elem_of_img in Hw. set_solver.
        - intros w Hw. apply elem_of_img in Hw as [k Hw].
          apply lookup_singleton_Some in Hw as [_ Hw].
          rewrite -Hw. exact I.
        - intros a' Ha'. rewrite dom_singleton elem_of_singleton in Ha'.
          rewrite Ha'. inversion Hwf_spec. apply (Har_ms _ Ha). }
      assert (Hsai: sa ##ₗ impl).
      { apply can_link_intro. exact Hwf. exact Hwf_impl.
        1,2: unfold sa; simpl; rewrite map_disjoint_dom.
        rewrite dom_singleton. set_solver. set_solver. }
      assert (Hctxt: is_ctxt (halt_context impl ⋈ sa) impl {[PC := WCap RWX 0%a (0%a ^+ 1)%a 0%a]}).
      { apply (is_context_move_in _ _).
        apply (can_link_weaken_ar any_implies_unconstrained_addr Hsai).
        replace (halt_context impl) with (halt_context (sa ⋈ impl)).
        apply halt_context_is_context. apply (link_well_formed _ _). solve_can_link.
        unfold halt_context. f_equal; try reflexivity.
        unfold dummy_exports. f_equal. unfold link. simpl.
        rewrite map_empty_union. rewrite map_empty_union.
        apply (anti_symm (⊆)).
        apply map_filter_subseteq. apply map_subseteq_spec.
        intros addr s Haddr.
        apply map_filter_lookup_Some. split. apply Haddr.
        inversion Hwf_impl.
        apply elem_of_img_rev in Haddr. rewrite -not_elem_of_dom.
        set_solver. }
      assert (Hmr:(∃ n, machine_run n (Executable, ({[PC := WCap RWX 0%a (0 ^+ 1)%a 0%a]}, segment ((halt_context impl ⋈ sa) ⋈ impl))) = Some Halted)).
      { exists 2.
        replace ((halt_context impl ⋈ sa) ⋈ impl) with (halt_context impl ⋈ (sa ⋈ impl)).
        apply (@halt_context_machine_run impl (sa ⋈ impl)). solve_can_link.
        specialize (halt_context_is_context Hwf_impl) as Hi.
        apply (link_assoc _ _). 2,3: solve_can_link.
        apply can_link_intro.
        specialize (@halt_context_wf impl) as H. solve_can_link.
        solve_can_link.
        all: unfold sa, halt_context; simpl; rewrite map_disjoint_dom.
        rewrite dom_singleton dom_singleton.
        intros x. rewrite elem_of_singleton elem_of_singleton.
        intros Hx0 Hxa. rewrite Hxa in Hx0. rewrite Hx0 in Ha.
        inversion Hwf_spec. specialize (Har_ms 0%a Ha). solve_addr.
        rewrite dom_empty. apply disjoint_empty_r.
      }
      specialize (Hrefines
        (halt_context impl ⋈ sa)
        {[ PC := WCap RWX 0%a (0^+1)%a 0%a ]} Halted
        Hctxt Hmr).
      destruct Hrefines as [Hctxt_spec _].
      inversion Hctxt_spec. inversion Hcan_link.
      rewrite map_disjoint_dom in Hms_disj.
      exfalso. apply (Hms_disj a).
      unfold halt_context. simpl.
      repeat rewrite resolve_imports_imports_empty.
      rewrite dom_union_L !dom_singleton. set_solver.
      assumption.
    Qed.
  End component_part_subseteq.

  (** Stronger results then those in facts, using
      a ≼ᵣ b -> a ##ₗ c -> b ##ₗ c
      to eliminate redundant hypotheses *)
  Section ctxt_ref_link.
    Lemma ctxt_ref_can_link {a b c}:
      a ≼ᵣ b -> a ##ₗ c -> b ##ₗ c.
    Proof.
      intros Hctxt_ref Hsep.
      apply can_link_intro.
      inversion Hctxt_ref. solve_can_link. solve_can_link.
      all: rewrite map_disjoint_dom.
      intros addr Hb_addr. inversion Hsep.
      apply map_disjoint_dom in Hms_disj. apply Hms_disj.
      apply (ctxt_ref_segment_subseteq Hctxt_ref addr Hb_addr).
      intros s Hb_s. inversion Hsep.
      apply map_disjoint_dom in Hexp_disj. apply Hexp_disj.
      inversion Hctxt_ref. apply (Hexp_incl s Hb_s).
    Qed.

    Lemma ctxt_ref_link_l {common impl spec} :
      common ##ₗ impl -> impl ≼ᵣ spec ->
      common ⋈ impl ≼ᵣ common ⋈ spec.
    Proof.
      intros H1 H2. apply ctxt_ref_link_l_1. exact H1.
      symmetry in H1. specialize (ctxt_ref_can_link H2 H1) as H.
      solve_can_link.
      exact H2.
    Qed.

    Lemma ctxt_ref_link_r {common impl spec} :
      common ##ₗ impl -> impl ≼ᵣ spec ->
      impl ⋈ common ≼ᵣ spec ⋈ common.
    Proof.
      intros H1 H2. apply ctxt_ref_link_r_1. exact H1.
      symmetry in H1. specialize (ctxt_ref_can_link H2 H1) as H.
      solve_can_link.
      exact H2.
    Qed.

    (** Same as above, some hypotheses are redundant,
        see ctxt_ref_link for the stronger_version *)
    Lemma ctxt_ref_link {impl impl' spec spec'} :
      impl ##ₗ impl' -> impl ≼ᵣ spec -> impl' ≼ᵣ spec' ->
      impl ⋈ impl' ≼ᵣ spec ⋈ spec'.
    Proof.
      intros H1 H2 H3.
      assert (H: impl' ##ₗ spec).
      specialize (ctxt_ref_can_link H2 H1) as H. solve_can_link.
      apply ctxt_ref_link_1. exact H1.
      specialize (ctxt_ref_can_link H3 H) as H4. solve_can_link.
      exact H. exact H2. exact H3.
    Qed.
  End ctxt_ref_link.
End contextual_refinement.

Infix "≼ᵣ" := contextual_refinement (at level 80).
