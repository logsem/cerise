From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang.
From cap_machine Require Import linking machine_run addr_reg_sample.

(** ** Reserve a minimal free memory in which to write our contexts *)
Section reserved_context_size.
  Local Transparent MemNum.
  Definition reserved_context_size_z: Z := 10000.
  Definition reserved_context_size: Addr := (za ^+ reserved_context_size_z)%a.

  Lemma reserved_context_size_le_mem :
    (reserved_context_size_z < MemNum)%Z.
  Proof. unfold MemNum, reserved_context_size_z. lia. Qed.
  Lemma reserved_context_size_to_z :
    finz.to_z reserved_context_size = reserved_context_size_z.
  Proof. simpl. lia. Qed.

  Opaque MemNum.

  (** Address greater than a given end_stack parameter *)
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
End reserved_context_size.

Notation wf_comp := (well_formed_comp can_address_only_no_seals).
Infix "##ₗ" := (can_link can_address_only_no_seals) (at level 70).

Notation is_ctxt := (is_context can_address_only_no_seals).

(** ** Contextual Refinement definition *)
Section contextual_refinement.
  Context {MP: MachineParameters}.

  (* Type of symbols to uniquely identify exports/inports. *)
  Context {Symbols : Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Definition initial_state (c : component Symbols) (r : Reg) : cfg cap_lang :=
    ([Seq (Instr Executable)], (r, segment c)).

  (** We need our [component]s to leave some space for contexts
      The simplest way is just to require them to not define
      any addresses in between [0] and [reserved_context_size] *)
  Definition has_free_space (x: component Symbols) :=
    addr_gt_than reserved_context_size (dom (segment x)).

  Lemma has_free_space_link {x y}:
    x ##ₗ y -> has_free_space x -> has_free_space y ->
    has_free_space (x ⋈ y).
  Proof.
    intros Hxy Hx Hy.
    unfold has_free_space.
    rewrite -(link_segment_dom can_address_only_no_seals).
    by apply addr_gt_than_union_stable.
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
    (Hfree : has_free_space impl)
    (Hrefines :
      forall (ctxt: component Symbols) (regs:Reg) (c: ConfFlag),
        is_ctxt ctxt impl regs ->
        (∃ n, machine_run n (Executable, (regs, segment (ctxt ⋈ impl))) = Some c) ->
        is_ctxt ctxt spec regs ∧
          ∃ n, machine_run n (Executable, (regs, segment (ctxt ⋈ spec))) = Some c),
    contextual_refinement impl spec.

  Infix "≼ᵣ" := contextual_refinement (at level 80).

  (** ** Easy results about contextual refinement *)
  Section facts.
    Lemma ctxt_ref_reflexive {comp}:
      has_free_space comp ->
      wf_comp comp -> comp ≼ᵣ comp.
    Proof.
      intros Haddr Hwf_comp.
      apply ctxt_ref_intro. 1,2,4: done.
      reflexivity.
      intros ctxt regs c ctxt_impl mr_ctxt_impl. by split.
    Qed.

    Global Instance ctxt_ref_transitive: Transitive contextual_refinement.
    Proof.
      intros a b c [] [].
      apply ctxt_ref_intro. 1,2,4: done.
      by transitivity (dom (exports b)).
      intros ctxt regs conf ctxt_a mr_ctxt_a.
      destruct (Hrefines ctxt regs conf ctxt_a mr_ctxt_a) as [ctxt_b mr_ctxt_b].
      apply (Hrefines0 ctxt regs conf ctxt_b mr_ctxt_b).
    Qed.

    (** Alternative Hrefines hypothesis,
        using [rtc erased_step] instead of [machine_run] *)
    Section alt_refines.
      Lemma refines_alt {a b: component Symbols} :
        (∀ c r cf,
        is_ctxt c a r ->
        (∃ n, machine_run n (Executable, (r, segment (c ⋈ a))) = Some cf) ->
        is_ctxt c b r /\
          ∃ n, machine_run n (Executable, (r, segment (c ⋈ b))) = Some cf)
        <->
        (∀ c r cf,
        is_ctxt c a r ->
        (∃ φ', rtc erased_step
          (initial_state (c ⋈ a) r)
          ([Instr cf], φ')) ->
        is_ctxt c b r /\
          ∃ φ', rtc erased_step
            (initial_state (c ⋈ b) r)
            ([Instr cf], φ')).
      Proof.
        split; intros Href c r cf Hc [p Hmr].
        apply machine_run_complete in Hmr.
        2: apply machine_run_correct in Hmr.
        all: specialize (Href c r cf Hc Hmr) as [Hc' Hmr'];
            split; [exact Hc'|destruct Hmr' as [p' Hmr'] ].
        apply (machine_run_correct p' Executable _ cf Hmr').
        apply (machine_run_complete Executable _ _ cf Hmr').
      Qed.

      Lemma contextual_refinement_rtc_erased_step {impl spec} :
        impl ≼ᵣ spec ->
        ∀ (ctxt: component Symbols) (regs:Reg) (c: ConfFlag),
        is_ctxt ctxt impl regs ->
        (∃ φ', rtc erased_step
          (initial_state (ctxt ⋈ impl) regs)
          ([Instr c], φ')) ->
        is_ctxt ctxt spec regs /\
        ∃ φ', rtc erased_step
          (initial_state (ctxt ⋈ spec) regs)
          ([Instr c], φ').
      Proof. intros []. by rewrite -refines_alt. Qed.

      Lemma contextual_refinement_alt {impl spec} :
        wf_comp impl ->
        wf_comp spec ->
        dom (exports spec) ⊆ dom (exports impl) ->
        has_free_space impl ->
        (∀ (ctxt: component Symbols) (regs:Reg) (c: ConfFlag),
        is_ctxt ctxt impl regs ->
        (∃ φ', rtc erased_step
          (initial_state (ctxt ⋈ impl) regs)
          ([Instr c], φ')) ->
        is_ctxt ctxt spec regs /\
        ∃ φ', rtc erased_step
          (initial_state (ctxt ⋈ spec) regs)
          ([Instr c], φ')) ->
        impl ≼ᵣ spec.
      Proof.
        intros Hi Hs Hsi Hfree Href'.
        apply ctxt_ref_intro; try done.
        rewrite refines_alt. done.
      Qed.
    End alt_refines.

    Lemma ctxt_ref_add_exportless {impl spec extra}:
      has_free_space extra ->
      extra ##ₗ impl -> exports extra = ∅ -> impl ≼ᵣ spec ->
      extra ⋈ impl ≼ᵣ spec.
    Proof.
      intros Haddr Hsep_ei Hexp [ ].
      apply ctxt_ref_intro.
      apply (link_well_formed _). solve_can_link. solve_can_link.
      by rewrite /= Hexp map_empty_union.
      by apply has_free_space_link.
      intros ctxt regs c ctxt_impl mr_impl.
      apply (is_context_move_in _) in ctxt_impl as Hctxt; [|solve_can_link].
      rewrite (link_assoc can_address_only_no_seals) in mr_impl; try solve_can_link.
      destruct (Hrefines (ctxt ⋈ extra) regs c Hctxt mr_impl) as [Hc Hmr].
      assert (Hctxt': is_ctxt ctxt spec regs). {
        assert (Hspec_extra: spec ##ₗ extra). solve_can_link.
        apply (is_context_remove_exportless_r _ Hspec_extra Hexp).
        rewrite <- (link_comm can_address_only_no_seals); [|solve_can_link].
        apply (is_context_move_out can_address_only_no_seals). solve_can_link.
        exact Hc.
      }
      split. done.

      destruct Hmr as [n Hmr]. exists n.
      specialize (link_segment_dom_subseteq_l can_address_only_no_seals ctxt spec) as Hdom_ctxt.
      specialize (link_segment_dom_subseteq_r can_address_only_no_seals ctxt spec) as Hdom_spec.
      rewrite (@machine_run_segment_subseteq _ _ _ _ (segment (ctxt ⋈ spec)) (segment ((ctxt ⋈ extra) ⋈ spec))).
      done.
      replace ((ctxt ⋈ extra) ⋈ spec) with ((ctxt ⋈ spec) ⋈ extra).
      2: {
        rewrite <- (link_assoc can_address_only_no_seals).
        rewrite <- (link_assoc can_address_only_no_seals).
        f_equal. apply (link_comm can_address_only_no_seals).
        all: solve_can_link.
       }
      transitivity (resolve_imports (imports (ctxt ⋈ spec)) (exports extra) (segment (ctxt ⋈ spec))).
      rewrite Hexp. by rewrite resolve_imports_exports_empty.
      apply map_union_subseteq_l.
      inversion Hc.

      apply (is_context_is_program _) in Hctxt' as [ [] ].
      intros w Hw. apply can_address_only_no_seals_weaken.
      apply (Hwr_ms w Hw).
      apply (is_context_is_program _) in Hctxt' as [ ].
      intros w Hw. apply can_address_only_no_seals_weaken.
      specialize (Hregs w Hw).
      apply elem_of_union in Hregs as [Hw'%elem_of_singleton | Hw'].
      by rewrite Hw'.
      inversion Hwf_comp. apply (Hwr_exp w Hw').
    Qed.

    Lemma ctxt_ref_rm_exportless {impl spec extra}:
      extra ##ₗ spec ->
      exports extra = ∅ ->
      impl ≼ᵣ extra ⋈ spec ->
      impl ≼ᵣ spec.
    Proof.
      intros Hsep Hexp [].
      apply ctxt_ref_intro.
      - solve_can_link.
      - solve_can_link.
      - unfold link in Hexp_incl. simpl in Hexp_incl.
        by rewrite Hexp map_empty_union in Hexp_incl.
      - done.
      - intros ctxt regs c Hctxt Hmr.
        specialize (Hrefines ctxt regs c Hctxt Hmr) as [Hctxt' Hmr'].
        assert (Hctxt'': is_ctxt ctxt spec regs).
        { rewrite (link_comm _ Hsep) in Hctxt'. symmetry in Hsep.
          apply (is_context_remove_exportless_r _ Hsep Hexp Hctxt'). }
        split. done.
        destruct Hmr' as [n Hmr']. exists n.
        rewrite (@machine_run_segment_subseteq _ _ _ _ (segment (ctxt ⋈ spec)) (segment (ctxt ⋈ (extra ⋈ spec)))).
        + done.
        + rewrite (link_comm _ Hsep).
          rewrite (link_assoc can_address_only_no_seals); try solve_can_link.
          transitivity (resolve_imports (imports (ctxt ⋈ spec)) (exports extra) (segment (ctxt ⋈ spec))).
          rewrite Hexp. by rewrite resolve_imports_exports_empty.
          apply map_union_subseteq_l.
        + apply (is_context_is_program _) in Hctxt'' as [ [] ].
          intros w Hw. apply can_address_only_no_seals_weaken.
          apply (Hwr_ms w Hw).
        + apply (is_context_is_program _) in Hctxt'' as [ ].
          intros w Hw. apply can_address_only_no_seals_weaken.
          specialize (Hregs w Hw).
          apply elem_of_union in Hregs as [Hw'%elem_of_singleton | Hw'].
          by rewrite Hw'.
          inversion Hwf_comp. apply (Hwr_exp w Hw').
    Qed.

    (** This can be weakened using [ctxt_ref_can_link], as
        [common ##ₗ impl] and [impl ≼ᵣ spec] often implies
        [common ##ₗ spec] (if we have a new symbol [s] not in [impl])

        See [ctxt_ref_link_l_inf] for such a stronger version when
        [Symbols] is [Infinite]. *)
    Lemma ctxt_ref_link_l {common impl spec} :
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
      exact ctxt_spec.
      rewrite (link_assoc can_address_only_no_seals).
      exact mr_spec.
      all: solve_can_link.
    Qed.

    (** Same as above, one hypothesis is redundant provided we have fresh [Symbols]
        see [ctxt_ref_link_r_inf] for the stronger_version *)
    Lemma ctxt_ref_link_r {common impl spec} :
      has_free_space common ->
      common ##ₗ impl -> common ##ₗ spec ->
      impl ≼ᵣ spec ->
      impl ⋈ common ≼ᵣ spec ⋈ common.
    Proof.
      intros Hf common_impl common_spec impl_spec.
      rewrite <- (link_comm _ common_impl).
      rewrite <- (link_comm _ common_spec).
      exact (ctxt_ref_link_l Hf common_impl common_spec impl_spec).
    Qed.

    (** Same as above, some hypotheses are redundant provided we have fresh [Symbols]
        see [ctxt_ref_link_inf] for the stronger_version *)
    Lemma ctxt_ref_link {impl impl' spec spec'} :
      has_free_space spec ->
      impl ##ₗ impl' -> spec ##ₗ spec' ->
      impl' ##ₗ spec ->
      impl ≼ᵣ spec -> impl' ≼ᵣ spec' ->
      impl ⋈ impl' ≼ᵣ spec ⋈ spec'.
    Proof.
      intros Hf Hii' Hss' His' His Hi's'.
      inversion His. inversion Hi's'.
      transitivity (spec ⋈ impl').
      apply ctxt_ref_link_r; [done|..|done]; solve_can_link.
      apply ctxt_ref_link_l; [done|..|done]; solve_can_link.
    Qed.
  End facts.

  (** ** Dummy exports and registers *)
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
      intros s. rewrite lookup_empty. rewrite map_img_empty_L. set_solver.
      intros a s exp exp' imp IH k.
      destruct (Symbols_eq_dec s k) as [sk | sk].
      rewrite sk. rewrite lookup_insert.
      split. reflexivity. rewrite elem_of_map_img. exists a. apply lookup_insert.
      rewrite lookup_insert_ne. 2: exact sk.
      specialize (IH k). destruct (exp' !! k).
      destruct IH as [IHw Hexp].
      split. exact IHw.
      rewrite elem_of_map_img. rewrite elem_of_map_img in Hexp. destruct Hexp as [a' Hexp].
      exists a'. rewrite lookup_insert_ne. exact Hexp.
      intros aa'. rewrite aa' in imp. rewrite imp in Hexp. discriminate.
      rewrite elem_of_map_img. rewrite elem_of_map_img in IH.
      intros [a' Hexp].
      apply lookup_insert_Some in Hexp.
      destruct Hexp as [ [aa' ss'] | [aa' Hexpa'] ].
      contradiction.
      apply (IH (ex_intro _ _ Hexpa')).
    Qed.
    Lemma dummy_exports_lookup {target} :
      ∀ w, w ∈ img (dummy_exports target) -> w = WInt 0.
    Proof.
      intros w Hsw. apply elem_of_map_img in Hsw. destruct Hsw as [s Hsw].
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
      - intros w Hw. apply elem_of_map_img in Hw as [r Hw].
        rewrite dummy_registers_spec in Hw. apply Some_inj in Hw.
        apply elem_of_singleton. symmetry. apply Hw.
      - intros w Hw. apply elem_of_singleton in Hw. rewrite Hw.
        apply elem_of_map_img. exists PC. apply dummy_registers_spec.
    Qed.
  End dummy_exports.

  (** Further consequence of refinement *)
  (* When [a ≼ᵣ b] then
      - [img (imports b) ⊆ img (imports a)]
      - [dom (segment b) ⊆ dom (segment a)]
      - [dom (exports b) = dom (exports a)] *)
  Section component_part_subseteq.

    (** We will need a fresh symbol, so we assume our set is infinite *)
    Context `{Infinite Symbols}.

    (** Basic context to prove the forall is non-empty
        Halt immediatly *)
    Local Example halt_context s target : component Symbols := {|
      segment := {[ 0%a := halt ]};
      imports := ∅;
      exports := <[s := WCap RX za (za^+1)%a za]> (dummy_exports target);
    |}.

    Local Lemma halt_context_wf {s target}:
      wf_comp (halt_context s target).
    Proof.
      unfold halt_context.
      apply wf_comp_intro; simpl.
      - rewrite map_img_empty_L. apply disjoint_empty_r.
      - rewrite dom_empty. apply empty_subseteq.
      - intros w Hw.
        apply map_img_insert_subseteq, elem_of_union in Hw as [Hw | Hw].
        apply elem_of_singleton in Hw. rewrite Hw.
        simpl. intros a. rewrite dom_singleton elem_of_singleton. solve_addr.
        apply dummy_exports_lookup in Hw. rewrite Hw. exact I.
      - intros w Hw. apply map_img_singleton, elem_of_singleton in Hw.
        rewrite Hw. exact I.
    Qed.

    Local Lemma halt_context_can_link {s target} :
      s ∉ dom (exports target) ->
      has_free_space target ->
      wf_comp target ->
      (halt_context s target) ##ₗ target.
    Proof.
      intros Hs Hf Hwf.
      apply can_link_intro.
      - apply halt_context_wf.
      - apply Hwf.
      - rewrite map_disjoint_spec. intros i x y Hix Hiy.
        unfold halt_context in Hix. simpl in Hix.
        apply lookup_singleton_Some in Hix as [Hi _].
        rewrite -Hi in Hiy. apply mk_is_Some, elem_of_dom in Hiy.
        specialize (Hf 0%a Hiy). solve_addr.
      - inversion Hwf.
        rewrite map_disjoint_dom. simpl.
        rewrite dom_insert dummy_exports_from_imports.
        intros s' [Hs'%elem_of_singleton | Hs']%elem_of_union Hs''.
        rewrite Hs' in Hs''. apply (Hs Hs'').
        apply (Hdisj _ Hs'' Hs').
    Qed.

    Local Lemma halt_context_machine_run s {target comp: component Symbols} :
      0%a ∉ (dom (segment comp)) ->
      wf_comp comp ->
      machine_run 2 (Executable, (
        <[ PC := WCap RX za (za^+1)%a za ]> dummy_registers,
        segment ((halt_context s target) ⋈ comp))
      ) = Some Halted.
    Proof.
      intros Hi Hwf.
      unfold machine_run.
      rewrite lookup_insert.
      unfold isCorrectPCb.
      assert (Hp: (0 <=? 0)%a && (0 <? 0 ^+ 1)%a && (isPerm RWX RX || isPerm RWX RWX) = true).
      auto. rewrite Hp. simpl.
      rewrite resolve_imports_imports_empty.
      replace (({[0%a := halt]} ∪ _) !! 0%a) with (Some halt).
      unfold exec, exec_opt, halt; rewrite (decode_encode_instrW_inv Halt); simpl.
      reflexivity.
      symmetry. apply lookup_union_Some_l. apply lookup_singleton.
    Qed.

    Local Lemma halt_context_is_context s {target} :
      s ∉ dom (exports target) ->
      has_free_space target ->
      wf_comp target ->
      is_ctxt (halt_context s target) target
        (<[ PC := WCap RX 0%a (0%a^+1)%a 0%a ]> dummy_registers).
    Proof.
      intros Hs Hf Hwf.
      apply is_context_intro.
      - apply (halt_context_can_link Hs Hf Hwf).
      - intros w Hw. apply map_img_insert_subseteq in Hw.
        rewrite dummy_registers_img in Hw.
        apply elem_of_union in Hw as [Hw | Hw];
        apply elem_of_singleton in Hw; rewrite Hw.
        rewrite !elem_of_union. left. right.
        apply elem_of_map_img_insert.
        rewrite !elem_of_union. left. left. by apply elem_of_singleton.
      - apply dummy_registers_insert.
      - transitivity (dom (dummy_exports target)).
        by rewrite dummy_exports_from_imports. set_solver.
      - simpl. rewrite map_img_empty_L. apply empty_subseteq.
    Qed.

    (** Contextual refinement implies that the
        implementation imports all the specifications symbols *)
    Lemma ctxt_ref_imports_subseteq s {impl spec : component Symbols} :
      s ∉ dom (exports impl) ->
      s ∉ img (imports spec) ->
      impl ≼ᵣ spec ->
      img spec.(imports) ⊆ img impl.(imports).
    Proof.
      intros Hs1 Hs2 Href s' Hspec_s.
      inversion Href.
      assert (H0: 0%a ∉ dom (segment impl)).
      intros Ha. specialize (Hfree 0%a Ha). solve_addr.
      specialize (Hrefines
        (halt_context s impl)
        (<[ PC := WCap RX 0%a (0^+1)%a 0%a ]> dummy_registers) Halted
        (halt_context_is_context s Hs1 Hfree Hwf_impl)
        (ex_intro _ 2 (halt_context_machine_run s H0 Hwf_impl))).
      destruct Hrefines as [Hctxt_spec _].
      inversion Hctxt_spec.
      specialize (Hno_imps_l _ Hspec_s).
      rewrite dom_insert dummy_exports_from_imports in Hno_imps_l.
      apply elem_of_union in Hno_imps_l as [Hs'%elem_of_singleton | Hs'].
      rewrite Hs' in Hspec_s. contradiction (Hs2 Hspec_s). done.
    Qed.

    (** Context with a single defined address, optionally an import *)
    Local Example addr_ctxt a s' := {|
      segment := {[ a := WInt 0 ]};
      imports := match s' with
        | None => ∅ : imports_type Symbols
        | Some s' => {[ a := s' ]} end;
      exports := ∅ |}.

    Local Lemma addr_ctxt_wf a s' : wf_comp (addr_ctxt a s').
    Proof.
      apply wf_comp_intro; simpl. set_solver. destruct s'; set_solver.
      - intros w Hw. apply elem_of_map_img in Hw. set_solver.
      - intros w Hw. apply elem_of_map_img in Hw as [k Hw].
        apply lookup_singleton_Some in Hw as [_ Hw].
        rewrite -Hw. exact I.
    Qed.

    Local Lemma addr_ctxt_sep {target a s'}:
      wf_comp target -> a ∉ dom (segment target) -> addr_ctxt a s' ##ₗ target.
    Proof.
      intros Himpl Ha. apply can_link_intro.
      apply addr_ctxt_wf. apply Himpl.
      1,2: unfold addr_ctxt; simpl; rewrite map_disjoint_dom.
      rewrite dom_singleton. all: set_solver.
    Qed.

    Local Lemma addr_ctxt_halt_ctxt s {target a s'}:
      wf_comp target ->
      a ∉ dom (segment target) ->
      (match s' with None => True | Some s => s ∈ dom (exports target) end) ->
      halt_context s target = halt_context s (addr_ctxt a s' ⋈ target).
    Proof.
      intros Hwf Ha Hs.
      unfold halt_context. f_equal; try reflexivity. f_equal.
      unfold dummy_exports. f_equal. unfold link. simpl.
      rewrite !map_empty_union. apply (anti_symm (⊆));
      rewrite map_subseteq_spec; intros addr s'' Haddr.
      - destruct (decide (a=addr)) as [Ha'|Ha'].
        { apply mk_is_Some, elem_of_dom in Haddr. rewrite Ha' in Ha.
          inversion Hwf as [_ Hi _ _]. contradiction (Ha (Hi _ Haddr)). }
        apply map_filter_lookup_Some. split.
        + destruct s'. rewrite lookup_union_r. apply Haddr. by apply lookup_singleton_None.
          by rewrite map_empty_union.
        + inversion Hwf as [He _ _ _]. destruct (exports target !! s'') eqn:He'.
          apply mk_is_Some, elem_of_dom in He'. contradiction (He _ He' (elem_of_map_img_2 _ _ _ Haddr)).
          done.
      - apply map_filter_lookup_Some in Haddr as [Haddr Hs'].
        destruct (decide (a=addr)) as [Ha'|Ha'].
        { destruct s'. rewrite -insert_union_singleton_l Ha' lookup_insert in Haddr.
          apply Some_inj in Haddr. rewrite Haddr in Hs. apply not_elem_of_dom in Hs'.
          contradiction.
          by rewrite map_empty_union in Haddr. }
        destruct s'. by rewrite -insert_union_singleton_l lookup_insert_ne in Haddr.
        by rewrite map_empty_union in Haddr.
    Qed.

    Local Lemma addr_ctxt_is_ctxt s {target a s'}:
      s ∉ dom (exports target) ->
      has_free_space target ->
      wf_comp target ->
      a ∉ dom (segment target) ->
      a ≠ 0%a ->
      (match s' with None => True | Some s => s ∈ dom (exports target) end) ->
      is_ctxt (halt_context s target ⋈ addr_ctxt a s') target
             (<[PC:=WCap RX 0%a (0 ^+ 1)%a 0%a]> dummy_registers).
    Proof.
      intros Hs Hfree Hwf Ha1 Ha2 Hs'.
      specialize (@addr_ctxt_sep target a s' Hwf Ha1) as Hsep1.
      assert (Ha3: a ∉ dom (segment (halt_context s target))).
      unfold halt_context. simpl. set_solver.
      specialize (@addr_ctxt_sep _ _ s' (halt_context_wf) Ha3) as Hsep2.
      specialize (halt_context_can_link Hs Hfree Hwf) as Hsep3.
      apply is_context_intro.
      - solve_can_link.
      - intros w Hw. apply map_img_insert_subseteq in Hw.
        rewrite dummy_registers_img in Hw.
        apply elem_of_union in Hw as [Hw | Hw];
        apply elem_of_singleton in Hw; rewrite Hw.
        rewrite !elem_of_union. left. right.
        rewrite /= map_union_empty. apply elem_of_map_img_insert.
        rewrite !elem_of_union. left. left. by apply elem_of_singleton.
      - apply dummy_registers_insert.
      - transitivity (dom (exports (halt_context s target))). simpl.
        rewrite dom_insert dummy_exports_from_imports. set_solver.
        rewrite dom_union. set_solver.
      - simpl. destruct s' as [s'|]. transitivity (img ({[a:=s']}:gmap _ _)).
        apply map_subseteq_img. rewrite map_empty_union. apply map_filter_subseteq.
        rewrite map_img_singleton -elem_of_subseteq_singleton. done.
        set_solver.
    Qed.

    Local Lemma addr_ctxt_machine_run s {target a s'} :
      s ∉ dom (exports target) ->
      has_free_space target ->
      wf_comp target -> a ∉ dom (segment target) ->
      a ≠ 0%a ->
      (match s' with None => True | Some s => s ∈ dom (exports target) end) ->
      machine_run 2
        (Executable, (<[PC:=WCap RX 0%a (0 ^+ 1)%a 0%a]> dummy_registers,
        segment ((halt_context s target ⋈ addr_ctxt a s') ⋈ target))) = Some Halted.
    Proof.
      intros Hs Hfree Hwf Ha1 Ha2 Hs'.
      specialize (@addr_ctxt_sep _ _ s' Hwf Ha1) as Hsep1.
      assert (Ha3: a ∉ dom (segment (halt_context s target))).
      unfold halt_context. simpl. set_solver.
      specialize (@addr_ctxt_sep _ _ s' (halt_context_wf) Ha3) as Hsep2.
      specialize (halt_context_can_link Hs Hfree Hwf) as Hsep3.
      rewrite - (link_assoc _); try solve_can_link.
      rewrite (@addr_ctxt_halt_ctxt s target a s' Hwf).
      apply halt_context_machine_run.
      rewrite -(link_segment_dom can_address_only_no_seals); try solve_can_link.
      rewrite elem_of_union. intros [Ha | Ha].
      simpl in Ha. rewrite dom_singleton elem_of_singleton in Ha. auto.
      specialize (Hfree 0%a Ha). solve_addr.
      solve_can_link. done. done.
    Qed.

    Lemma ctxt_ref_segment_subseteq s {impl spec}:
      s ∉ dom (exports impl) ->
      impl ≼ᵣ spec ->
      dom spec.(segment) ⊆ dom impl.(segment).
    Proof.
      intros Hs [ ] a Ha.
      destruct (segment impl !! a) as [w|] eqn:HeqA.
      apply mk_is_Some, elem_of_dom in HeqA. apply HeqA.
      apply not_elem_of_dom in HeqA.
      assert (H0: 0%a ∉ dom (segment impl)).
      intros Ha'. specialize (Hfree 0%a Ha'). solve_addr.
      destruct (decide (a = 0%a)) as [ Ha0 | Ha0 ].
      - specialize (Hrefines
          (halt_context s impl)
          (<[ PC := WCap RX 0%a (0^+1)%a 0%a ]> dummy_registers) _
          (halt_context_is_context s Hs Hfree Hwf_impl)
          (ex_intro _ 2 (halt_context_machine_run s H0 Hwf_impl))).
        destruct Hrefines as [Hctxt_spec _].
        inversion Hctxt_spec. inversion Hcan_link.
        rewrite map_disjoint_dom in Hms_disj.
        exfalso. apply (Hms_disj a).
        unfold halt_context. simpl.
        rewrite dom_singleton. set_solver. assumption.
      - specialize (Hrefines
          (halt_context s impl ⋈ addr_ctxt a None)
          (<[ PC := WCap RX 0%a (0^+1)%a 0%a ]> dummy_registers)
          Halted
          (@addr_ctxt_is_ctxt s _ _ None Hs Hfree Hwf_impl HeqA Ha0 I)
          (ex_intro _ 2 (@addr_ctxt_machine_run s _ _ None Hs Hfree Hwf_impl HeqA Ha0 I))).
        destruct Hrefines as [Hctxt_spec _].
        inversion Hctxt_spec. inversion Hcan_link.
        rewrite map_disjoint_dom in Hms_disj.
        exfalso. apply (Hms_disj a).
        unfold halt_context. simpl.
        rewrite !resolve_imports_imports_empty dom_union elem_of_union !dom_singleton.
        set_solver. done.
    Qed.

    Lemma ctxt_ref_dom_exports s {impl spec} :
      s ∉ dom (exports impl) ->
      impl ≼ᵣ spec ->
      dom impl.(exports) = dom spec.(exports).
    Proof.
      intros Hs [ ]. apply (anti_symm (⊆)); [intros s' Hs'|done].
      destruct (exports spec !! s') as [w|] eqn:HeqS.
      apply elem_of_dom. by exists w.
      assert (Ha: (0^+1)%a ≠ 0%a). discriminate.
      assert (Ha': (0^+1)%a ∉ dom (segment impl)).
      intros Ha'. specialize (Hfree _ Ha'). discriminate.
      specialize (Hrefines
          (halt_context s impl ⋈ addr_ctxt (0^+1)%a (Some s'))
          (<[ PC := WCap RX 0%a (0^+1)%a 0%a ]> dummy_registers)
          Halted
          (@addr_ctxt_is_ctxt s _ _ (Some s') Hs Hfree Hwf_impl Ha' Ha Hs')
          (ex_intro _ 2 (@addr_ctxt_machine_run s _ _ (Some s') Hs Hfree Hwf_impl Ha' Ha Hs'))) as [Hctxt_spec _].
      inversion Hctxt_spec as [_ _ _ _ Himps]. apply Himps.
      rewrite elem_of_map_img. exists (0 ^+ 1)%a.
      simpl. rewrite map_empty_union.
      apply map_filter_lookup_Some. split.
      apply lookup_singleton.
      rewrite map_union_empty.
      specialize (dummy_exports_spec impl s') as Hspec.
      destruct (dummy_exports impl !! s'). destruct Hspec as [_ Hspec].
      inversion Hwf_impl as [Hwf _ _ _]. contradiction (Hwf s' Hs' Hspec).
      rewrite lookup_insert_ne.
      by rewrite -dummy_exports_from_imports elem_of_dom -eq_None_not_Some in Hspec.
      intros Heq. rewrite Heq in Hs. apply (Hs Hs').
    Qed.

    Lemma ctxt_ref_can_link s {a b c} :
      s ∉ dom (exports a) ->
      a ≼ᵣ b -> a ##ₗ c -> b ##ₗ c.
    Proof.
      intros Hs Hctxt_ref Hsep.
      apply can_link_intro.
      inversion Hctxt_ref. solve_can_link. solve_can_link.
      all: rewrite map_disjoint_dom.
      intros addr Hb_addr. inversion Hsep.
      apply map_disjoint_dom in Hms_disj. apply Hms_disj.
      apply (ctxt_ref_segment_subseteq s Hs Hctxt_ref addr Hb_addr).
      intros s' Hb_s. inversion Hsep.
      apply map_disjoint_dom in Hexp_disj. apply Hexp_disj.
      inversion Hctxt_ref. apply (Hexp_incl s' Hb_s).
    Qed.

    Lemma ctxt_ref_has_free_space s {a b} :
      s ∉ dom (exports a) ->
      a ≼ᵣ b -> has_free_space b.
    Proof.
      intros Hs Hab addr Haddr.
      apply (ctxt_ref_segment_subseteq s Hs Hab) in Haddr.
      inversion Hab.
      apply (Hfree addr Haddr).
    Qed.
  End component_part_subseteq.

  (** ** Results with infinite symbols *)
  (** We can simplify a few lemmas by just requiring [Symbols]
      to be infinite *)
  Section infinite_symbols.
    Context {Symbols_infinite: Infinite Symbols}.

    Lemma ctxt_ref_imports_subseteq_inf {impl spec : component Symbols} :
      impl ≼ᵣ spec ->
      img spec.(imports) ⊆ img impl.(imports).
    Proof.
      specialize (is_fresh (dom (exports impl) ∪ map_img (imports spec))) as Hf.
      apply (ctxt_ref_imports_subseteq (fresh (dom (exports impl) ∪ img (imports spec))));
      set_solver.
    Qed.

    Lemma ctxt_ref_segment_subseteq_inf {impl spec}:
      impl ≼ᵣ spec ->
      dom spec.(segment) ⊆ dom impl.(segment).
    Proof.
      specialize (is_fresh (dom (exports impl))) as Hf.
      apply (ctxt_ref_segment_subseteq (fresh (dom (exports impl))));
      set_solver.
    Qed.

    Lemma ctxt_ref_dom_exports_inf {impl spec} :
      impl ≼ᵣ spec ->
      dom impl.(exports) = dom spec.(exports).
    Proof.
      specialize (is_fresh (dom (exports impl))) as Hf.
      apply (ctxt_ref_dom_exports (fresh (dom (exports impl))));
      set_solver.
    Qed.

    Lemma ctxt_ref_can_link_inf {a b c} :
      a ≼ᵣ b -> a ##ₗ c -> b ##ₗ c.
    Proof.
      specialize (is_fresh (dom (exports a))) as Hf.
      apply (ctxt_ref_can_link (fresh (dom (exports a))));
      set_solver.
    Qed.

    Lemma ctxt_ref_has_free_space_inf {a b} :
      a ≼ᵣ b -> has_free_space b.
    Proof.
      specialize (is_fresh (dom (exports a))) as Hf.
      apply (ctxt_ref_has_free_space (fresh (dom (exports a))));
      set_solver.
    Qed.

    Lemma ctxt_ref_link_l_inf {common impl spec} :
      has_free_space common ->
      common ##ₗ impl -> impl ≼ᵣ spec ->
      common ⋈ impl ≼ᵣ common ⋈ spec.
    Proof.
      intros H0 H1 H2. apply ctxt_ref_link_l. exact H0. exact H1.
      symmetry in H1. specialize (ctxt_ref_can_link_inf H2 H1) as H.
      solve_can_link.
      exact H2.
    Qed.

    Lemma ctxt_ref_link_r_inf {common impl spec} :
      has_free_space common ->
      common ##ₗ impl -> impl ≼ᵣ spec ->
      impl ⋈ common ≼ᵣ spec ⋈ common.
    Proof.
      intros H0 H1 H2. apply ctxt_ref_link_r. exact H0. exact H1.
      symmetry in H1. specialize (ctxt_ref_can_link_inf H2 H1) as H.
      solve_can_link.
      exact H2.
    Qed.

    Lemma ctxt_ref_link_inf {impl impl' spec spec'} :
      impl ##ₗ impl' -> impl ≼ᵣ spec -> impl' ≼ᵣ spec' ->
      impl ⋈ impl' ≼ᵣ spec ⋈ spec'.
    Proof.
      intros H1 H2 H3.
      assert (H: impl' ##ₗ spec).
      specialize (ctxt_ref_can_link_inf H2 H1) as H. solve_can_link.
      apply ctxt_ref_link.
      apply (ctxt_ref_has_free_space_inf H2). exact H1.
      specialize (ctxt_ref_can_link_inf H3 H) as H4. solve_can_link.
      exact H. exact H2. exact H3.
    Qed.
  End infinite_symbols.
End contextual_refinement.

Infix "≼ᵣ" := contextual_refinement (at level 80).
