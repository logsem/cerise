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

  (** Example addr_restriction, address greater than a given end_stack parameter *)
Definition addr_gt_than (e_stk: Addr) (dom: gset Addr) :=
  forall a, a ∈ dom -> (e_stk < a)%a.
Lemma addr_gt_than_union_stable (e_stk: Addr) :
  forall s1 s2, addr_gt_than e_stk s1 -> addr_gt_than e_stk s2 ->
    addr_gt_than e_stk (s1 ∪ s2).
Proof.
  intros dom1 dom2 gt_dom1 gt_dom2 a a_in_1or2.
  apply elem_of_union in a_in_1or2.
  destruct a_in_1or2 as [ a_in_1 | a_in_2 ].
  apply (gt_dom1 a a_in_1).
  apply (gt_dom2 a a_in_2).
Qed.

Section contextual_refinement.
  Context {MP: MachineParameters}.

  (* Type of symbols to uniquely identify exports/inports. *)
  Context {Symbols : Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Notation wf_comp := (well_formed_comp can_address_only_no_seals).
  Infix "##ₗ" := (can_link can_address_only_no_seals) (at level 70).

  Notation is_ctxt := (is_context can_address_only_no_seals).

  Definition has_free_space (x: component Symbols) :=
    addr_gt_than reserved_context_size (dom (segment x)).

  Lemma has_free_space_link {x y}:
    x ##ₗ y -> has_free_space x -> has_free_space y ->
    has_free_space (x ⋈ y).
  Proof.
    intros Hxy Hx Hy.
    unfold has_free_space.
    rewrite -(link_segment_dom can_address_only_no_seals).
    apply addr_gt_than_union_stable; assumption.
    all: solve_can_link.
  Qed.

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
    (** We need some free addresses to place our contexts *)
    (Hfree : has_free_space impl)
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
      has_free_space comp ->
      wf_comp comp -> comp ≼ᵣ comp.
    Proof.
      intros Haddr Hwf_comp.
      apply ctxt_ref_intro. 1,2,4: assumption.
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
      has_free_space extra ->
      extra ##ₗ impl -> exports extra = ∅ -> impl ≼ᵣ spec ->
      extra ⋈ impl ≼ᵣ spec.
    Proof.
      intros Haddr Hsep_ei Hexp [ ].
      apply ctxt_ref_intro.
      apply (link_well_formed _). solve_can_link. assumption.
      unfold link. simpl. clear Hexp. set_solver.
      apply has_free_space_link; assumption.
      intros ctxt regs c ctxt_impl mr_impl.
      apply (is_context_move_in _) in ctxt_impl as Hctxt; try solve_can_link.
      rewrite (link_assoc can_address_only_no_seals) in mr_impl; try solve_can_link.
      destruct (Hrefines (ctxt ⋈ extra) regs c Hctxt mr_impl) as [Hc Hmr].
      split.
      eapply (is_context_remove_exportless_r _ _ Hexp).
      rewrite <- (link_comm can_address_only_no_seals).
      apply (is_context_move_out can_address_only_no_seals).
      all: try solve_can_link. inversion ctxt_impl.
      exact Hwr_regs. exact Hc.

      destruct Hmr as [n Hmr]. exists n.
      rewrite (@machine_run_segment_subseteq _ _ _ _ (segment (ctxt ⋈ spec)) (segment ((ctxt ⋈ extra) ⋈ spec))).
      exact Hmr.
      replace ((ctxt ⋈ extra) ⋈ spec) with ((ctxt ⋈ spec) ⋈ extra).
      2: {
        rewrite <- (link_assoc can_address_only_no_seals).
        rewrite <- (link_assoc can_address_only_no_seals).
        f_equal. apply (link_comm can_address_only_no_seals).
        all: solve_can_link.
       }
      rewrite (link_segment_union can_address_only_no_seals).
      rewrite (link_segment_union can_address_only_no_seals).
      rewrite <- (link_segment_union can_address_only_no_seals).
      2,3,4: solve_can_link.
      transitivity (resolve_imports (imports (ctxt ⋈ spec)) (exports extra) (segment (ctxt ⋈ spec))).
      rewrite Hexp.
      rewrite resolve_imports_exports_empty. reflexivity.
      apply map_union_subseteq_l.
      inversion Hc.

      1,2: assert (Hdom_ctxt: dom (segment ctxt) ⊆ dom (segment (ctxt ⋈ spec))).
      1,3: apply (link_segment_dom_subseteq_l can_address_only_no_seals);
           inversion ctxt_impl; try inversion Hcan_link0; inversion Hcan_link; try assumption.

      assert (Hdom_spec: dom (segment spec) ⊆ dom (segment (ctxt ⋈ spec))).
      apply (link_segment_dom_subseteq_r can_address_only_no_seals);
      inversion ctxt_impl; try inversion Hcan_link0; inversion Hcan_link; assumption.

      assert (Hex: ∀ w, w ∈ img (exports ctxt ∪ exports spec) -> can_address_only_no_seals w (dom (segment (ctxt ⋈ spec)))).
      intros w Hw'. apply elem_of_img in Hw' as [s Hw'].
      apply lookup_union_Some_raw in Hw' as [Hw' | [_ Hw'] ].
      apply (relation_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      inversion ctxt_impl as [ [ [] ] ]. apply Hwr_exp. apply elem_of_img_rev in Hw'. assumption.
      apply (relation_stable2 w (dom (segment spec)) _ Hdom_spec).
      inversion Hcan_link. inversion Hwf_r. apply Hwr_exp. apply elem_of_img_rev in Hw'. assumption.

      assert (Hse: ∀ a' w, (segment ctxt ∪ segment spec) !! a' = Some w -> can_address_only_no_seals w (dom (segment (ctxt ⋈ spec)))).
      intros a w Hw'.
      apply lookup_union_Some_raw in Hw' as [Hw' | [_ Hw'] ].
      apply (relation_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      inversion ctxt_impl as [ [ [] ] ]. apply Hwr_ms. apply elem_of_img_rev in Hw'. assumption.
      apply (relation_stable2 w (dom (segment spec)) _ Hdom_spec).
      inversion Hcan_link. inversion Hwf_r. apply Hwr_ms. apply elem_of_img_rev in Hw'. assumption.

      intros w Hw.
      apply elem_of_img in Hw as [a Hw].
      unfold link in Hw. simpl in Hw.
      apply can_address_only_no_seals_weaken.
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

      inversion ctxt_impl as [ [ [] ] ]. intros w Hw.
      apply (relation_stable2 w (dom (segment ctxt)) _ Hdom_ctxt).
      apply can_address_only_no_seals_weaken.
      apply (Hwr_regs w Hw).
      Unshelve. solve_can_link.
    Qed.

    (** This can be weakened, since
        (common ##ₗ impl) and (impl ≼ᵣ spec) implies
        (common ##ₗ spec).

        See ctxt_ref_link_l for the stronger version *)
    Lemma ctxt_ref_link_l_1 {common impl spec} :
      has_free_space common ->
      common ##ₗ impl -> common ##ₗ spec ->
      impl ≼ᵣ spec ->
      common ⋈ impl ≼ᵣ common ⋈ spec.
    Proof.
      intros Hf sep_impl sep_spec impl_spec.
      inversion impl_spec.
      apply ctxt_ref_intro.
      1,2: apply (link_well_formed _ ); assumption.
      unfold link. simpl.
      rewrite (dom_union_L (exports common) (exports spec)).
      rewrite (dom_union_L (exports common) (exports impl)).
      apply union_subseteq. split.
      apply union_subseteq_l.
      transitivity (dom (exports impl)).
      exact Hexp_incl. apply union_subseteq_r.
      apply has_free_space_link; assumption.
      intros ctxt regs c ctxt_impl mr_impl.
      inversion ctxt_impl.
      apply (is_context_move_in _) in ctxt_impl as HC.
      rewrite (link_assoc can_address_only_no_seals) in mr_impl.
      destruct (Hrefines (link ctxt common) regs c HC mr_impl) as [ctxt_spec mr_spec].
      split.
      apply (is_context_move_out _). solve_can_link.
      exact Hwr_regs. exact ctxt_spec.
      rewrite (link_assoc can_address_only_no_seals).
      exact mr_spec.
      all: solve_can_link.
    Qed.

    (** Same as above, one hypothesis is redundant,
        see ctxt_ref_link_r for the stronger_version *)
    Lemma ctxt_ref_link_r_1 {common impl spec} :
      has_free_space common ->
      common ##ₗ impl -> common ##ₗ spec ->
      impl ≼ᵣ spec ->
      impl ⋈ common ≼ᵣ spec ⋈ common.
    Proof.
      intros Hf common_impl common_spec impl_spec.
      rewrite <- (link_comm _ common_impl).
      rewrite <- (link_comm _ common_spec).
      exact (ctxt_ref_link_l_1 Hf common_impl common_spec impl_spec).
    Qed.

    (** Same as above, some hypotheses are redundant,
        see ctxt_ref_link for the stronger_version *)
    Lemma ctxt_ref_link_1 {impl impl' spec spec'} :
      has_free_space spec ->
      impl ##ₗ impl' -> spec ##ₗ spec' ->
      impl' ##ₗ spec ->
      impl ≼ᵣ spec -> impl' ≼ᵣ spec' ->
      impl ⋈ impl' ≼ᵣ spec ⋈ spec'.
    Proof.
      intros Hf Hii' Hss' His' His Hi's'.
      inversion His. inversion Hi's'.
      transitivity (spec ⋈ impl').
      apply ctxt_ref_link_r_1; solve_can_link || assumption.
      apply ctxt_ref_link_l_1; solve_can_link || assumption.
    Qed.

  End facts.

  (** A simple function generating dummy export (all 0) and dummy registers
      for a given list of imports, usefull for building contexts *)
  Section dummy_exports.
    Definition dummy_exports target : exports_type Symbols :=
      map_fold (fun _ s exp => <[s:=WInt 0]> exp)
      ∅ target.(imports).

    Definition dummy_registers :=
      set_fold (fun r (map:Reg) => <[r := WInt 0]> map) ∅ all_registers_s.

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

    Lemma dummy_registers_spec r :
      dummy_registers !! r = Some (WInt 0).
    Proof.
      generalize (all_registers_s_correct r). revert r.
      apply (set_fold_ind_L (fun m s => ∀ r, r ∈ s -> m !! r = Some (WInt 0))).
      intros r Hr. apply elem_of_empty in Hr. contradiction Hr.
      intros r s m Hrs IH r' Hr'.
      apply elem_of_union in Hr' as [Hr' | Hr'].
      rewrite elem_of_singleton in Hr'. rewrite Hr'. apply lookup_insert.
      destruct (decide (r = r')) as [H | H]. rewrite H. apply lookup_insert.
      rewrite (lookup_insert_ne _ _ _ _ H). apply (IH r' Hr').
    Qed.
    Lemma dummy_registers_insert {r' x} r :
      is_Some ((<[r' := x]> dummy_registers) !! r).
    Proof.
      destruct (decide (r' = r)) as [H | H]. rewrite H lookup_insert.
      auto. rewrite (lookup_insert_ne _ _ _ _ H). rewrite dummy_registers_spec.
      auto.
    Qed.
    Lemma dummy_registers_img : img dummy_registers = {[WInt 0]}.
    Proof.
      apply (anti_symm (⊆)).
      - intros w Hw. apply elem_of_img in Hw as [r Hw].
        rewrite dummy_registers_spec in Hw. apply Some_inj in Hw.
        apply elem_of_singleton. symmetry. apply Hw.
      - intros w Hw. apply elem_of_singleton in Hw. rewrite Hw.
        apply elem_of_img. exists PC. apply dummy_registers_spec.
    Qed.
  End dummy_exports.

  (* When a ≼ᵣ b then
      - img (imports b) ⊆ img (imports a)
      - dom (segment b) ⊆ dom (segment a)
      - exports b = exports a (not proved here) *)
  Section component_part_subseteq.
    (** Basic context to prove the forall is non-empty
        Halt immediatly *)
    Local Example halt_context target : component Symbols := {|
      segment := {[ 0%a := halt ]};
      imports := ∅;
      exports := dummy_exports target;
    |}.

    Local Lemma halt_context_wf {target}:
      wf_comp (halt_context target).
    Proof.
      unfold halt_context.
      apply wf_comp_intro; simpl.
      - rewrite img_empty_L. apply disjoint_empty_r.
      - rewrite dom_empty. apply empty_subseteq.
      - intros w exp_s.
        apply dummy_exports_lookup in exp_s.
        rewrite exp_s. unfold can_address_only_no_seals. exact I.
      - intros w H. apply img_singleton, elem_of_singleton in H.
        rewrite H. exact I.
    Qed.

    Local Lemma halt_context_can_link {target} :
      has_free_space target -> wf_comp target ->
      (halt_context target) ##ₗ target.
    Proof.
      intros Hf Hwf.
      apply can_link_intro.
      - apply halt_context_wf.
      - apply Hwf.
      - rewrite map_disjoint_spec. intros i x y Hix Hiy.
        unfold halt_context in Hix. simpl in Hix.
        apply lookup_singleton_Some in Hix as [Hi _].
        rewrite -Hi in Hiy. apply mk_is_Some, elem_of_dom in Hiy.
        specialize (Hf 0%a Hiy). solve_addr.
      - inversion Hwf.
        rewrite map_disjoint_dom.
        rewrite dummy_exports_from_imports.
        symmetry. exact Hdisj.
    Qed.

    Local Lemma halt_context_machine_run {target comp: component Symbols} :
      0%a ∉ (dom (segment comp)) ->
      wf_comp comp ->
      machine_run 2 (Executable, (
        <[ PC := WCap RWX za (za^+1)%a za ]> dummy_registers,
        segment ((halt_context target) ⋈ comp))
      ) = Some Halted.
    Proof.
      intros Hi Hwf.
      unfold machine_run.
      rewrite lookup_insert.
      unfold isCorrectPCb.
      assert (H: (0 <=? 0)%a && (0 <? 0 ^+ 1)%a && (isPerm RWX RX || isPerm RWX RWX) = true).
      auto. rewrite H. simpl. rewrite resolve_imports_spec.
      destruct (imports comp !! 0%a) as [w|] eqn:Hita.
      inversion Hwf. apply mk_is_Some, elem_of_dom in Hita.
      contradiction (Hi (Himp 0%a Hita)).
      rewrite resolve_imports_spec lookup_empty.
      replace (({[0%a := halt]} ∪ segment comp) !! 0%a) with (Some halt).
      unfold exec, exec_opt, halt; rewrite (decode_encode_instrW_inv Halt); simpl.
      reflexivity.
      symmetry. apply lookup_union_Some_l. apply lookup_singleton.
    Qed.

    Local Lemma halt_context_is_context {target} :
      has_free_space target -> wf_comp target ->
      is_ctxt (halt_context target) target
        (<[ PC := WCap RWX 0%a (0%a^+1)%a 0%a ]> dummy_registers).
    Proof.
      intros Hf Hwf.
      apply is_context_intro.
      - apply (halt_context_can_link Hf Hwf).
      - intros w Hw. apply img_insert in Hw.
        rewrite dummy_registers_img in Hw.
        apply elem_of_union in Hw as [Hw | Hw];
        apply elem_of_singleton in Hw; rewrite Hw.
        intros a Ha01. simpl. rewrite dom_singleton elem_of_singleton.
        solve_finz. exact I.
      - apply dummy_registers_insert.
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
      assert (H0: 0%a ∉ dom (segment impl)).
      intros Ha. specialize (Hfree 0%a Ha). solve_addr.
      specialize (Hrefines
        (halt_context impl)
        (<[ PC := WCap RWX 0%a (0^+1)%a 0%a ]> dummy_registers) _
        (halt_context_is_context Hfree Hwf_impl)
        (ex_intro _ 2 (halt_context_machine_run H0 Hwf_impl))).
      destruct Hrefines as [Hctxt_spec _].
      inversion Hctxt_spec.
      specialize (Hno_imps_l s Hspec_s).
      simpl in Hno_imps_l.
      rewrite dummy_exports_from_imports in Hno_imps_l.
      apply Hno_imps_l.
    Qed.

    Local Example addr_ctxt a := {|
      segment := {[ a := WInt 0 ]};
      imports := ∅ : imports_type Symbols;
      exports := ∅ |}.

    Local Lemma addr_ctxt_wf a : wf_comp (addr_ctxt a).
    Proof.
      apply wf_comp_intro; simpl. set_solver. set_solver.
      - intros w Hw. apply elem_of_img in Hw. set_solver.
      - intros w Hw. apply elem_of_img in Hw as [k Hw].
        apply lookup_singleton_Some in Hw as [_ Hw].
        rewrite -Hw. exact I.
    Qed.

    Local Lemma addr_ctxt_sep {target a}:
      wf_comp target -> a ∉ dom (segment target) -> addr_ctxt a ##ₗ target.
    Proof.
      intros Himpl Ha. apply can_link_intro.
      apply addr_ctxt_wf. apply Himpl.
      1,2: unfold addr_ctxt; simpl; rewrite map_disjoint_dom.
      rewrite dom_singleton. all: set_solver.
    Qed.

    Local Lemma addr_ctxt_halt_ctxt {target a}:
      wf_comp target ->
      halt_context target = halt_context (addr_ctxt a ⋈ target).
    Proof.
      intros Hwf.
      unfold halt_context. f_equal; try reflexivity.
      unfold dummy_exports. f_equal. unfold link. simpl.
      rewrite !map_empty_union.
      apply (anti_symm (⊆)).
      rewrite map_subseteq_spec. intros addr s Haddr.
      apply map_filter_lookup_Some. split. apply Haddr.
      inversion Hwf.
      apply elem_of_img_rev in Haddr. rewrite -not_elem_of_dom.
      set_solver.
      apply map_filter_subseteq; apply map_subseteq_spec.
    Qed.

    Local Lemma addr_ctxt_is_ctxt {target a}:
      has_free_space target ->
      wf_comp target -> a ∉ dom (segment target) -> a ≠ 0%a ->
      is_ctxt (halt_context target ⋈ addr_ctxt a) target
             (<[PC:=WCap RWX 0%a (0 ^+ 1)%a 0%a]> dummy_registers).
    Proof.
      intros Hfree Hwf Ha1 Ha2.
      specialize (addr_ctxt_sep Hwf Ha1) as Hsep1.
      assert (Ha3: a ∉ dom (segment (halt_context target))).
      unfold halt_context. simpl. set_solver.
      specialize (addr_ctxt_sep (halt_context_wf) Ha3) as Hsep2.
      specialize (halt_context_can_link Hfree Hwf) as Hsep3.
      apply is_context_intro.
      - solve_can_link.
      - intros w Hw. apply img_insert in Hw.
        rewrite dummy_registers_img in Hw.
        apply elem_of_union in Hw as [Hw | Hw];
        apply elem_of_singleton in Hw; rewrite Hw.
        simpl. rewrite !resolve_imports_imports_empty.
        intros a' Ha01. rewrite dom_union !dom_singleton elem_of_union.
        left. rewrite elem_of_singleton. solve_finz.
        exact I.
      - apply dummy_registers_insert.
      - transitivity (dom (exports (halt_context target))).
        rewrite dummy_exports_from_imports. reflexivity.
        rewrite dom_union. set_solver.
      - simpl. rewrite img_empty_L. apply empty_subseteq.
    Qed.

    Local Lemma addr_ctxt_machine_run {target a} :
      has_free_space target ->
      wf_comp target -> a ∉ dom (segment target) -> a ≠ 0%a ->
      machine_run 2
      (Executable,
      (<[PC:=WCap RWX 0%a (0 ^+ 1)%a 0%a]> dummy_registers,
        segment ((halt_context target ⋈ addr_ctxt a) ⋈ target))) = Some Halted.
    Proof.
      intros Hfree Hwf Ha1 Ha2.
      specialize (addr_ctxt_sep Hwf Ha1) as Hsep1.
      assert (Ha3: a ∉ dom (segment (halt_context target))).
      unfold halt_context. simpl. set_solver.
      specialize (addr_ctxt_sep (halt_context_wf) Ha3) as Hsep2.
      specialize (halt_context_can_link Hfree Hwf) as Hsep3.
      rewrite - (link_assoc _); try solve_can_link.
      rewrite (@addr_ctxt_halt_ctxt target a Hwf).
      apply halt_context_machine_run.
      rewrite -(link_segment_dom can_address_only_no_seals); try solve_can_link.
      rewrite elem_of_union. intros [Ha | Ha].
      simpl in Ha. rewrite dom_singleton elem_of_singleton in Ha. auto.
      specialize (Hfree 0%a Ha). solve_addr.
      solve_can_link.
    Qed.

    Lemma ctxt_ref_segment_subseteq {impl spec}:
      impl ≼ᵣ spec ->
      dom spec.(segment) ⊆ dom impl.(segment).
    Proof.
      intros [ ] a Ha.
      destruct (segment impl !! a) as [w|] eqn:HeqA.
      apply mk_is_Some, elem_of_dom in HeqA. apply HeqA.
      apply not_elem_of_dom in HeqA.
      assert (H0: 0%a ∉ dom (segment impl)).
      intros Ha'. specialize (Hfree 0%a Ha'). solve_addr.
      destruct (decide (a = 0%a)) as [ Ha0 | Ha0 ].
      - specialize (Hrefines
          (halt_context impl)
          (<[ PC := WCap RWX 0%a (0^+1)%a 0%a ]> dummy_registers) _
          (halt_context_is_context Hfree Hwf_impl)
          (ex_intro _ 2 (halt_context_machine_run H0 Hwf_impl))).
        destruct Hrefines as [Hctxt_spec _].
        inversion Hctxt_spec. inversion Hcan_link.
        rewrite map_disjoint_dom in Hms_disj.
        exfalso. apply (Hms_disj a).
        unfold halt_context. simpl.
        rewrite dom_singleton. set_solver. assumption.
      - specialize (Hrefines
          (halt_context impl ⋈ addr_ctxt a)
          (<[ PC := WCap RWX 0%a (0^+1)%a 0%a ]> dummy_registers)
          Halted
          (addr_ctxt_is_ctxt Hfree Hwf_impl HeqA Ha0)
          (ex_intro _ 2 (addr_ctxt_machine_run Hfree Hwf_impl HeqA Ha0))).
        destruct Hrefines as [Hctxt_spec _].
        inversion Hctxt_spec. inversion Hcan_link.
        rewrite map_disjoint_dom in Hms_disj.
        exfalso. apply (Hms_disj a).
        unfold halt_context. simpl.
        rewrite !resolve_imports_imports_empty dom_union elem_of_union !dom_singleton.
        set_solver.
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

    Lemma ctxt_ref_has_free_space {a b} :
      a ≼ᵣ b -> has_free_space b.
    Proof.
      intros Hab addr Haddr.
      apply (ctxt_ref_segment_subseteq Hab) in Haddr.
      inversion Hab.
      apply (Hfree addr Haddr).
    Qed.

    Lemma ctxt_ref_link_l {common impl spec} :
      has_free_space common ->
      common ##ₗ impl -> impl ≼ᵣ spec ->
      common ⋈ impl ≼ᵣ common ⋈ spec.
    Proof.
      intros H0 H1 H2. apply ctxt_ref_link_l_1. exact H0. exact H1.
      symmetry in H1. specialize (ctxt_ref_can_link H2 H1) as H.
      solve_can_link.
      exact H2.
    Qed.

    Lemma ctxt_ref_link_r {common impl spec} :
      has_free_space common ->
      common ##ₗ impl -> impl ≼ᵣ spec ->
      impl ⋈ common ≼ᵣ spec ⋈ common.
    Proof.
      intros H0 H1 H2. apply ctxt_ref_link_r_1. exact H0. exact H1.
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
      apply ctxt_ref_link_1.
      apply (ctxt_ref_has_free_space H2). exact H1.
      specialize (ctxt_ref_can_link H3 H) as H4. solve_can_link.
      exact H. exact H2. exact H3.
    Qed.
  End ctxt_ref_link.
End contextual_refinement.

Infix "≼ᵣ" := contextual_refinement (at level 80).
