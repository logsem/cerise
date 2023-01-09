From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang linking machine_run.
From cap_machine Require Import stdpp_img contextual_refinement addr_reg_sample.

Section examples.
  Context {MR:MachineParameters}.

  Context {Symbols: Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.


  (** Transform a list of word (instructions) into a memory segment
      The first element has address za, the second za+1... *)
  Fixpoint wlist2segment addr (instrs: list Word) : segment_type :=
    match instrs with
    | [] => ∅
    | i::instrs =>
        <[addr:=i]> (wlist2segment (addr ^+ 1)%a instrs)
    end.

  Lemma wlist2segment_max {n addr:Addr} {wlist: list Word} :
    is_Some (wlist2segment n wlist !! addr) ->
    (addr <= n + length wlist)%Z.
  Proof.
    generalize n. clear n.
    induction wlist.
    - simpl. rewrite lookup_empty.
      intros n x. contradiction (is_Some_None x).
    - intros n is_some. simpl in is_some.
      destruct (addr_eq_dec n addr) as [n_addr | n_addr].
      rewrite n_addr. lia.
      rewrite (lookup_insert_ne _ _ _ _ n_addr) in is_some.
      apply (Z.le_trans _ _ _ (IHwlist _ is_some)).
      simpl.
      rewrite Nat2Z.inj_succ.
      destruct (finz_incr_default_spec _ n 1) as [ [_ [_ d] ] | [ [ neg | big ] d] ].
      rewrite d. lia.
      destruct (finz_spec n) as [ _ gt_0 ]. lia.
      unfold finz.largest in d. rewrite d. simpl.
      lia.
  Qed.

  Lemma wlist2segment_disjoint (cmp : component Symbols) {wlist: list Word} :
    (length wlist <= reserved_context_size_z)%Z ->
    addr_gt_than reserved_context_size (dom (segment cmp)) ->
    wlist2segment za wlist ##ₘ cmp.(segment).
  Proof.
    intros list_short segment_big.
    apply map_disjoint_spec. intros a x y wlist_a_x cmp_a_y.
    destruct cmp as [cmp [] ]. simpl in cmp_a_y.
    assert (a_inf: (a <= reserved_context_size)%Z).
    apply mk_is_Some in wlist_a_x.
    apply wlist2segment_max in wlist_a_x.
    rewrite Z.add_0_l in wlist_a_x.
    apply (Z.le_trans _ _ _ wlist_a_x).
    apply list_short.
    apply (Zle_not_lt _ _ a_inf).
    apply segment_big. rewrite elem_of_dom. exists y. apply cmp_a_y.
  Qed.

  Example dummy_exports target : exports_type Symbols :=
    map_fold (fun _ s exp => <[s:=WInt 0]> exp)
    ∅ target.(imports).

  Lemma dummy_exports_spec target : forall s,
    match dummy_exports target !! s with
      | None => s ∉ img target.(imports)
      | Some w => w = WInt 0 /\ s ∈ img target.(imports)
    end.
  Proof.
    unfold dummy_exports, exports_type, imports_type.
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
    intros w Hsw. rewrite elem_of_img in Hsw. destruct Hsw as [s Hsw].
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

  (** Basic context to prove the forall is non-empty
      Halt immediatly *)
  Example halt_context target : component Symbols := {|
    segment := wlist2segment za [ halt ];
    imports := ∅;
    exports := dummy_exports target;
  |}.

  Lemma halt_context_wf {target}:
    well_formed_comp can_address_only unconstrained_addr (halt_context target).
  Proof.
    unfold halt_context.
    apply wf_comp_intro; simpl.
    - rewrite img_empty_L. apply disjoint_empty_r.
    - unfold imports_type.
      rewrite dom_empty. apply empty_subseteq.
    - intros w exp_s.
      apply dummy_exports_lookup in exp_s.
      rewrite exp_s. unfold can_address_only. exact I.
    - intros w H.
      rewrite insert_empty in H.
      apply img_singleton in H. rewrite elem_of_singleton in H.
      rewrite H. exact I.
    - exact I.
  Qed.

  Lemma halt_context_can_link {target} :
    well_formed_comp can_address_only (addr_gt_than reserved_context_size) target ->
    can_link can_address_only unconstrained_addr (halt_context target) target.
  Proof.
    intros t_wf.
    apply can_link_intro.
    - apply halt_context_wf.
    - apply (wf_comp_weaken_ar addr_gt_than_implies_unconstrained t_wf).
    - apply wlist2segment_disjoint.
      simpl. unfold reserved_context_size_z. lia.
      inversion t_wf. assumption.
    - inversion t_wf.
      rewrite map_disjoint_dom.
      rewrite dummy_exports_from_imports.
      symmetry. exact Hdisj.
  Qed.

  Lemma halt_context_machine_run {target} :
    well_formed_comp can_address_only (addr_gt_than reserved_context_size) target ->
    machine_run 2 (Executable, (
      {[ PC := WCap RWX za (za^+1)%a za ]},
      segment ((halt_context target) ⋈ target))
    ) = Some Halted.
  Proof.
    intros wft.
    unfold machine_run.
    rewrite lookup_singleton.
    unfold isCorrectPCb.
    replace ((0 <=? 0)%a && (0 <? 0 ^+ 1)%a && (isPerm RWX RX || isPerm RWX RWX)) with true.
    simpl.
    rewrite resolve_imports_spec.
    replace (imports target !! 0%a) with (@None Symbols).
    rewrite resolve_imports_spec.
    unfold imports_type, exports_type, segment_type.
    rewrite lookup_empty.
    replace ((<[0%a:=halt]> ∅ ∪ segment target) !! 0%a) with (Some halt).
    unfold exec, exec_opt, halt.
    rewrite (decode_encode_instrW_inv Halt). simpl.
    reflexivity.
    symmetry. apply lookup_union_Some_l.
    rewrite insert_empty. apply lookup_singleton.
    destruct (Some_dec (imports target !! 0%a)) as [ [w Hita] | Hita].
    exfalso.
    inversion wft. apply mk_is_Some in Hita.
    unfold imports_type, exports_type, segment_type in Hita.
    apply elem_of_dom in Hita.
    specialize (Har_ms 0%a (Himp 0%a Hita)).
    unfold finz.lt in Har_ms.
    rewrite reserved_context_size_to_z in Har_ms.
    simpl in Har_ms. unfold reserved_context_size_z in Har_ms.
    lia.
    rewrite Hita. reflexivity.
    auto.
  Qed.

  Lemma halt_context_is_context {target} :
    well_formed_comp can_address_only (addr_gt_than reserved_context_size) target ->
    is_context can_address_only unconstrained_addr
      (halt_context target) target {[ PC := WCap RWX za (za^+1)%a za ]}.
  Proof.
    intros Hwf_t.
    apply is_context_intro.
    - apply (halt_context_can_link Hwf_t).
    - intros w Hsr_w.
      apply img_singleton, elem_of_singleton in Hsr_w.
      rewrite Hsr_w.
      intros a Ha01. simpl. rewrite insert_empty.
      rewrite dom_singleton. rewrite elem_of_singleton.
      solve_finz.
    - rewrite dummy_exports_from_imports.
      reflexivity.
    - simpl.
      rewrite img_empty_L.
      apply empty_subseteq.
  Qed.

  (** Contextual refinement implies that the
      implementation imports all the specifications symbols *)
  Lemma ctxt_ref_imports_subseteq {impl spec: component Symbols}:
    contextual_refinement impl spec ->
    img spec.(imports) ⊆ img impl.(imports).
  Proof.
    intros Href s Hspec_s.
    inversion Href.
    specialize (Hrefines
      (halt_context impl)
      {[ PC := WCap RWX za (za^+1)%a za ]} _
      (halt_context_is_context Hwf_impl)
      (ex_intro _ 2 (halt_context_machine_run Hwf_impl))).
    destruct Hrefines as [Hctxt_spec _].
    inversion Hctxt_spec.
    specialize (Hno_imps_l s Hspec_s).
    simpl in Hno_imps_l.
    rewrite dummy_exports_from_imports in Hno_imps_l.
    apply Hno_imps_l.
  Qed.

  (** Instructions that assert that the to be imported value
      at PC.end - 1 is equal to w *)
  Definition assert_exports_incl_instr w :=
    match w with
    | WInt n => [
        (* load imported value (at PC.end - 1) into r0 *)
        gete r_t0 PC;
        lea_z r_t0 (-1);
        load_r r_t0 r_t0;
        (* point r3 to a fail instruction *)
        load_r r_t3 PC;
        lea_z PC 1;
        fail_end;
        lea_z r_t3 2; (* points to previous instruction *)
        (* set r1 != 0 <-> r0 != n *)
        lt_r_z r_t1 r_t0 n; (* r1 = r0 < n ? 1 : 0 *)
        lt_z_r r_t2 n r_t0; (* r2 = n < r0 ? 1 : 0 *)
        add_r_r r_t1 r_t1 r_t2; (* r1 != 0 <-> n != r0 *)
        (* jump if r0 != n *)
        jnz r_t3 r_t1;
        halt;
        halt (* dummy overwritten by import *)
    ]
    | WCap _ _ _ _ => []
    end.

  Definition assert_exports_incl_context s w (imps : imports_type Symbols) :=
    let addr_e : Addr := (za ^+ (length (assert_exports_incl_instr w)))%a in
    ({|
        segment := wlist2segment za (assert_exports_incl_instr w);
        (* imports only the single value to test *)
        imports := {[ (addr_e ^+ (-1))%a := s ]};
        (* exports are all dummy values, just to ensure we can link *)
        exports := map_fold
          (fun _ s exp => <[s:=WInt 0]> exp)
          ∅ imps;
    |}, (WCap RWX za addr_e za)).

(*
  Lemma assert_exports_incl_context_is_context (cmp : component_wf word_restrictions addr_restrictions) {s w} :
    cmp.(comp).(exports) !! s = Some w ->
    let ctxt := fst (assert_exports_incl_context s w cmp.(comp).(imports)) in
    let main := snd (assert_exports_incl_context s w cmp.(comp).(imports)) in
    is_context can_address_only unconstrained_addr (Main ctxt main) (Lib cmp.(comp)) (link_main_lib ctxt cmp.(comp) main).
  Proof.
    intros es_w ctxt main.
    apply link_main_lib_is_context.
    - apply can_address_only_incr.
    - auto.
    - apply wlist2segment_disjoint.
      unfold assert_exports_incl_instr, reserved_context_size_z.
      destruct w; simpl; lia.
    - apply wf_main.
      shelve.
      unfold main, can_address_only.


      pose (addr_gt_than reserved_context_size (dom _ cmp.(segment))).
      apply addr_restrictions_implies_addr_gt.
      rewrite elem_of_dom in sa_y.
      apply
    - shelve.
    - apply (well_formed_comp_weaken_addr_restrictions addr_restrictions_implies_unconstrained).
      apply (well_formed_comp_weaken_word_restrictions word_restrictions_implies_address_only).
      apply wf_lib.
      apply cmp.(comp_is_wf).
    -

  Lemma ctxt_ref_export_dom_incl a b  :
    contextual_refinement a b ->
    a.(comp).(exports) ⊆ b.(comp).(exports).
  Proof.
    intros a_b x.
    unfold option_relation.
    destruct (Some_dec (a.(comp).(exports) !! x)) as [[wa exp_ax] | exp_ax];
    destruct (Some_dec (b.(comp).(exports) !! x)) as [[wb exp_bx] | exp_bx];
    unfold exports_type in exp_ax, exp_bx;
    rewrite exp_bx, exp_ax.
    3,4: trivial. *)

End examples.
