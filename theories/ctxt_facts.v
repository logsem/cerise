From stdpp Require Import gmap fin_maps fin_sets.

From cap_machine Require Import machine_parameters cap_lang linking machine_run.
From cap_machine Require Import contextual_refinement addr_reg_sample.

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
    addr_gt_than reserved_context_size (dom _ (segment cmp)) ->
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
    3,4: trivial.

End examples.
