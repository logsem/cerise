From Coq Require Import Eqdep_dec.
From iris Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps fin_sets.
From cap_machine Require Import addr_reg machine_base.

Section Linking.

  (** Symbols are used to identify imported/exported word (often capabilites)
      They can be of any type with decidable equality *)
  Context {Symbols: Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

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

  (** Example of a word_restrictions, ensure all capabilites point
      into the given segment *)
  Example can_address_only (word: Word) (addr_set: gset Addr) :=
    match word with
    | WInt _ => True
    | WCap _ b e _ => ∀ a, (b <= a < e)%a -> a ∈ addr_set
    end.
  Lemma can_address_only_incr :
    forall w dom1 dom2,
      dom1 ⊆ dom2 ->
      can_address_only w dom1 ->
      can_address_only w dom2.
  Proof.
    intros w dom1 dom2 dom1_dom2.
    destruct w. auto.
    intros ca_dom1 addr addr_in_be.
    apply dom1_dom2. apply (ca_dom1 addr addr_in_be).
  Qed.

  (** A predicate that can be used to restrict the address space to a subsection
      of memory (ex: reserve space for a stack).
      This should remain true on the link (union of segments where it holds) *)
  Variable addr_restrictions: gset Addr -> Prop.
  Variable addr_restrictions_union_stable:
    forall dom1 dom2,
      addr_restrictions dom1 ->
      addr_restrictions dom2 ->
      addr_restrictions (dom1 ∪ dom2).

  (** Example addr_restriction, address greater than a given end_stack parameter *)
  Example addr_gt_than (e_stk: Addr) (dom: gset Addr) :=
    forall a, a ∈ dom -> (e_stk < a)%a.
  Lemma addr_gt_than_union_stable (e_stk: Addr) :
    forall dom1 dom2,
      addr_gt_than e_stk dom1 ->
      addr_gt_than e_stk dom2 ->
      addr_gt_than e_stk (dom1 ∪ dom2).
  Proof.
    intros dom1 dom2 gt_dom1 gt_dom2 a a_in_1or2.
    apply elem_of_union in a_in_1or2.
    destruct a_in_1or2 as [ a_in_1 | a_in_2 ].
    apply (gt_dom1 a a_in_1).
    apply (gt_dom2 a a_in_2).
  Qed.

  Definition imports_type := (gmap Addr Symbols).
  Definition exports_type := (gmap Symbols Word).
  Definition segment_type := (gmap Addr Word).

  #[global] Instance exports_subseteq : SubsetEq exports_type.
    unfold exports_type.
    apply map_subseteq.
  Defined.

  (** Components are memory segments "with holes" for imported values
      (mostly capabilities) from other segments.

      These holes are identified by symbols.
      - imports shows where the imported values should be place in memory
        it is a map to ensure we don't import two symbols in the same address
      - exports is word to place in segments linked with this one.
      *)
  Record component := {
    segment : segment_type;
    (** the component's memory segment, a map addr -> word *)

    imports : imports_type;
    (** the segment imports, a map addr -> symbol to place *)

    exports : exports_type;
    (** Segment exports, a map symbols -> word (often capabilities) *)
  }.

  Inductive well_formed_comp (comp:component) : Prop :=
  | wf_comp_intro: forall
      (* This should be "dom comp.(exports) ## img comp.(imports)" but stdpp doesn't have img/codom... *)
      (Hdisj: ∀ s a, is_Some (comp.(exports) !! s) -> comp.(imports) !! a = Some s -> False)
      (* We import only to addresses in our segment *)
      (Himp: dom (gset Addr) comp.(imports) ⊆ dom _ comp.(segment))
      (* Word restriction on segment and exports, again would be better expresses with img/codom... *)
      (Hwr_exp: ∀ s w, comp.(exports) !! s = Some w -> word_restrictions w (dom _ comp.(segment)))
      (Hwr_ms: ∀ a w, comp.(segment) !! a = Some w -> word_restrictions w (dom _ comp.(segment)))
      (Har_ms: addr_restrictions (dom _ comp.(segment))),
      well_formed_comp comp.

  (** A program is a segment without imports and some register allocations *)
  Inductive is_program (comp:component) (regs:Reg) : Prop :=
  | is_program_intro: forall
      (Hwfcomp: well_formed_comp comp)
      (Hnoimports: comp.(imports) = ∅)
      (Hwr_regs: ∀ r w, regs !! r = Some w -> word_restrictions w (dom _ comp.(segment))),
      is_program comp regs.

  (** Add values defined in exp to the segment
      at addresses specified in imp *)
  Definition resolve_imports
  (imp: imports_type) (exp: exports_type) (ms: segment_type) :=
  map_fold (fun a s m => match exp !! s with
    | Some w => <[a:=w]> m
    | None => m end) ms imp.

  (** To form well defined links, our componement must be well-formed
      and have separates memory segments and exported symbols *)
  Inductive can_link (comp_l comp_r : component) : Prop :=
  | can_link_intro: forall
      (Hwf_l: well_formed_comp comp_l)
      (Hwf_r: well_formed_comp comp_r)
      (Hms_disj: comp_l.(segment) ##ₘ comp_r.(segment))
      (Hexp_disj: comp_l.(exports) ##ₘ comp_r.(exports)),
      can_link comp_l comp_r.

  Infix "##ₗ" := can_link (at level 70).

  (** Creates link for two components
      the arguments should satisfy can_link *)
  Definition link comp_l comp_r :=
    (* exports is union of exports *)
    let exp := comp_l.(exports) ∪ comp_r.(exports) in
    {|
      exports := exp;
      (* memory segment is union of segments, with resolved imports *)
      segment :=
        resolve_imports comp_r.(imports) exp (
          resolve_imports comp_l.(imports) exp (
            comp_l.(segment) ∪ comp_r.(segment)));
      (* imports is union of imports minus symbols is export *)
      imports :=
        filter
          (fun '(_,s) => exp !! s = None)
          (comp_l.(imports) ∪ comp_r.(imports));
    |}.

  (** Asserts that context is a valid context to run library lib.
      i.e. sufficient condition to ensure that (link context lib) is a program *)
  Inductive is_context (context lib: component) (regs:Reg): Prop :=
  | is_context_intro: forall
      (Hcan_link: context ##ₗ lib)
      (Hwr_regs: ∀ r w, regs !! r = Some w -> word_restrictions w (dom _ context.(segment)))
      (Hno_imps_l: ∀ a s, lib.(imports) !! a = Some s -> s ∈ (dom (gset Symbols) context.(exports)))
      (Hno_imps_r: ∀ a s, context.(imports) !! a = Some s -> s ∈ (dom (gset Symbols) lib.(exports))),
      is_context context lib regs.

  (** Lemmas about resolve_imports: specification and utilities *)
  Section resolve_imports.
    Lemma resolve_imports_spec:
      forall imp exp ms a,
      (resolve_imports imp exp ms) !! a =
        match imp !! a with
        | None => ms !! a
        | Some s =>
            match exp !! s with
            | None => ms !! a
            | Some wexp => Some wexp
            end
        end.
    Proof.
      intros imp exp ms a.
      eapply (map_fold_ind
      (fun m imp => forall a,
         m !! a = match imp !! a with
        | None => ms !! a
        | Some s => match exp !! s with
                    | None => ms !! a
                    | Some wexp => Some wexp
                    end
        end)
       (fun a s m => match exp !! s with
      | Some w => <[a:=w]> m
      | None => m end)).
      - intros. split.
      - intros addr s imp' ms' imp'_addr_none Himp' addr'.
        specialize (Himp' addr').
        destruct (addr_eq_dec addr addr') as [addr_addr' | addr_addr'].
        rewrite addr_addr'.
        rewrite addr_addr' in imp'_addr_none.
        rewrite imp'_addr_none in Himp'.
        rewrite lookup_insert.
        destruct (exp !! s). rewrite lookup_insert. reflexivity. apply Himp'.
        rewrite (lookup_insert_ne _ _ _ _ addr_addr').
        destruct (imp' !! addr').
        destruct (exp !! s0).
        all: destruct (exp !! s);
        try rewrite (lookup_insert_ne _ _ _ _ addr_addr'); apply Himp'.
    Qed.

    (** Resolve imports of an address in imports is either
        - unchanged if the address are in not in the exports
        - the exported value if it is in exports *)
    Lemma resolve_imports_spec_in:
      forall imp exp ms a s,
        imp !! a = Some s ->
        (resolve_imports imp exp ms) !! a =
        match exp !! s with
        | None => ms !! a
        | Some wexp => Some wexp
        end.
    Proof.
      intros imp exp ms a s H.
      pose resolve_imports_spec as spec.
      specialize (spec imp exp ms a).
      rewrite H in spec. apply spec.
    Qed.

    (** Resolve imports does not change addresses not in imports *)
    Lemma resolve_imports_spec_not_in:
      forall imp exp ms a,
        imp !! a = None ->
        (resolve_imports imp exp ms) !! a = ms !! a.
    Proof.
      intros imp exp ms a H.
      pose resolve_imports_spec as spec.
      specialize (spec imp exp ms a).
      rewrite H in spec. apply spec.
    Qed.

    (** A address from resolve imports contains either:
        - an added export
        - an original memory segment value *)
    Lemma resolve_imports_spec_simple:
      forall {imp exp ms a w},
        (resolve_imports imp exp ms) !! a = Some w ->
          (∃ s, exp !! s = Some w) \/ (ms !! a = Some w).
    Proof.
      intros imp exp ms a w H.
      pose resolve_imports_spec as spec.
      specialize (spec imp exp ms a).
      destruct (imp !! a).
      destruct (Some_dec (exp !! s)) as [[w' exp_s] | exp_s];
      rewrite exp_s in spec. all: rewrite spec in H.
      left. rewrite <- exp_s in H. exists s. apply H.
      all: right; apply H.
    Qed.

    (** Resolve imports increases the domain of the memory segment *)
    Lemma resolve_imports_dom :
      forall {imp exp ms},
        dom (gset Addr) ms ⊆ dom (gset Addr) (resolve_imports imp exp ms).
    Proof.
      intros imp exp ms a a_in_ms.
      apply (map_fold_ind (fun ms imp => a ∈ dom _ ms)).
      - apply a_in_ms.
      - intros a' s m ms' ma'_none H. destruct (exp !! s).
        apply dom_insert_subseteq. all: apply H.
    Qed.

    (** We have equality of domains when imports are all in the memory segment
        (which is the case in well formed components) *)
    Lemma resolve_imports_dom_eq :
      forall {imp exp ms},
        dom (gset Addr) imp ⊆ dom _ ms ->
        dom (gset Addr) (resolve_imports imp exp ms) = dom (gset Addr) ms.
    Proof.
      intros imp exp ms.
      apply (map_fold_ind (fun m imp => dom (gset Addr) imp ⊆ dom _ ms -> dom _ m = dom _ ms)).
      - reflexivity.
      - intros addr s m ms' m_addr_none dom_ms'_dom_ms dom_incl.
        assert (m_ms: dom (gset Addr) m ⊆ dom _ ms).
        transitivity (dom (gset Addr) (<[addr:=s]> m)); auto.
        apply dom_insert_subseteq.
        rewrite <- (dom_ms'_dom_ms m_ms).
        destruct (exp !! s).
        rewrite dom_insert_L.
        rewrite <- subseteq_union_L.
        rewrite dom_insert_L in dom_incl.
        rewrite <- (dom_ms'_dom_ms m_ms) in dom_incl.
        apply union_subseteq in dom_incl.
        destruct dom_incl as [ addr_in_ms' _ ]. auto.
        auto.
    Qed.

    Lemma resolve_imports_link_dom {c1 c2} :
      well_formed_comp c1 ->
      well_formed_comp c2 ->
      dom (gset Addr) (link c1 c2).(segment) =
      dom _ (c1.(segment) ∪ c2.(segment)).
    Proof.
      intros wf1 wf2.
      rewrite resolve_imports_dom_eq;
      rewrite resolve_imports_dom_eq.
      reflexivity.
      all: inversion wf1; inversion wf2.
      2: transitivity (dom (gset Addr) (segment c2));
         assumption || (rewrite dom_union_L; apply union_subseteq_r).
      all: transitivity (dom (gset Addr) (segment c1));
         assumption || (rewrite dom_union_L; apply union_subseteq_l).
    Qed.

    Lemma resolve_imports_twice:
      ∀ {imp1 imp2 exp ms},
        imp1 ##ₘ imp2 ->
        resolve_imports imp1 exp (resolve_imports imp2 exp ms) =
        resolve_imports (imp1 ∪ imp2) exp ms.
    Proof.
      intros. apply map_eq. intros addr.
      destruct (map_disjoint_spec imp1 imp2) as [ H' ].
      pose resolve_imports_spec as spec1.
      specialize (spec1 imp1 exp (resolve_imports imp2 exp ms) addr).
      pose resolve_imports_spec as spec2.
      specialize (spec2 imp2 exp ms addr).
      pose resolve_imports_spec as spec3.
      specialize (spec3 (imp1 ∪ imp2) exp ms addr).
      destruct (Some_dec (imp1 !! addr)) as [[w1 imp1_a] | imp1_a];
      rewrite imp1_a in spec1.
      rewrite (lookup_union_Some_l _ imp2 _ _ imp1_a) in spec3.
      destruct (exp !! w1); rewrite spec1; rewrite spec3. reflexivity.
      destruct (Some_dec (imp2 !! addr)) as [[w2 imp2_a] | imp2_a].
      contradiction (H' H _ _ _ imp1_a imp2_a).
      rewrite imp2_a in spec2. rewrite spec2. reflexivity.
      rewrite spec1.
      destruct (Some_dec (imp2 !! addr)) as [[w2 imp2_a] | imp2_a];
      rewrite imp2_a in spec2.
      rewrite (lookup_union_Some_r _ imp2 _ _ H imp2_a) in spec3.
      destruct (exp !! w2); rewrite spec2; rewrite spec3; reflexivity.
      destruct (lookup_union_None imp1 imp2 addr) as [ _ r ].
      rewrite (r _) in spec3.
      rewrite spec2. rewrite spec3. reflexivity.
      split; assumption.
    Qed.

  End resolve_imports.

  (** well_formedness of [link a b] and usefull lemmas *)
  Section LinkWellFormed.
    Lemma link_segment_dom_subseteq_l {c1 c2} :
      well_formed_comp c1 ->
      well_formed_comp c2 ->
      dom (gset Addr) (segment c1) ⊆ dom _ (segment (link c1 c2)).
    Proof.
      intros wf1 wf2. rewrite (resolve_imports_link_dom wf1 wf2).
      rewrite dom_union_L. apply union_subseteq_l.
    Qed.

    Lemma link_segment_dom_subseteq_r {c1 c2} :
      well_formed_comp c1 ->
      well_formed_comp c2 ->
      dom (gset Addr) (segment c2) ⊆ dom _ (segment (link c1 c2)).
    Proof.
      intros wf1 wf2.
      rewrite (resolve_imports_link_dom wf1 wf2).
      rewrite dom_union_L. apply union_subseteq_r.
    Qed.

    (** link generates a well formed component
        if its arguments are well formed and disjoint *)
    Lemma link_well_formed {comp1 comp2} :
      comp1 ##ₗ comp2 ->
      well_formed_comp (link comp1 comp2).
    Proof.
      intros disj.
      inversion disj.
      inversion Hwf_l as [Hdisj1 Himp1 Hexp1 Hwr_ms1 Har_ms1].
      inversion Hwf_r as [Hdisj2 Himp2 Hexp2 Hwr_ms2 Har_ms2].
      specialize (link_segment_dom_subseteq_l Hwf_l Hwf_r).
      specialize (link_segment_dom_subseteq_r Hwf_l Hwf_r).
      intros imp2 imp1.
      apply wf_comp_intro.
      + intros s a is_some_s. (* exports are disjoint from import *)
        intros sa_in_imps.
        apply map_filter_lookup_Some in sa_in_imps.
        destruct sa_in_imps as [_ is_none_s].
        rewrite is_none_s in is_some_s.
        apply (is_Some_None is_some_s).
      + transitivity (dom (gset Addr) (map_union comp1.(imports) comp2.(imports))).
        apply dom_filter_subseteq.
        rewrite dom_union_L.
        rewrite union_subseteq. split.
        transitivity (dom (gset Addr) (segment comp1)); assumption.
        transitivity (dom (gset Addr) (segment comp2)); assumption.
      + intros s w exp_s_w. (* exported word respect word restrictions *)
        apply lookup_union_Some in exp_s_w. 2: assumption.
        destruct exp_s_w as [exp1_s | exp2_s].
        apply (word_restrictions_incr _ _ _ imp1 (Hexp1 s w exp1_s)).
        apply (word_restrictions_incr _ _ _ imp2 (Hexp2 s w exp2_s)).
      + intros a w ms_a_w. (* word in segment follow word restrictions *)
        specialize (Hwr_ms1 a w). specialize (Hwr_ms2 a w).
        destruct (resolve_imports_spec_simple ms_a_w) as [[ s exp_s_w ] | ms_a_w'].
        apply lookup_union_Some in exp_s_w. 2: assumption.
        destruct exp_s_w as [exp1_s | exp2_s].
        apply (word_restrictions_incr _ _ _ imp1 (Hexp1 s w exp1_s)).
        apply (word_restrictions_incr _ _ _ imp2 (Hexp2 s w exp2_s)).
        destruct (resolve_imports_spec_simple ms_a_w') as [[ s exp_s_w ] | ms_a_w''].
        apply lookup_union_Some in exp_s_w. 2: assumption.
        destruct exp_s_w as [exp1_s | exp2_s].
        apply (word_restrictions_incr _ _ _ imp1 (Hexp1 s w exp1_s)).
        apply (word_restrictions_incr _ _ _ imp2 (Hexp2 s w exp2_s)).
        apply lookup_union_Some in ms_a_w''. 2: assumption.
        destruct ms_a_w'' as [ms1_a_w | ms2_a_w].
        apply (word_restrictions_incr _ _ _ imp1 (Hwr_ms1 ms1_a_w)).
        apply (word_restrictions_incr _ _ _ imp2 (Hwr_ms2 ms2_a_w)).
      + rewrite (resolve_imports_link_dom Hwf_l Hwf_r).
        rewrite dom_union_L.
        apply addr_restrictions_union_stable; assumption.
    Qed.

    Lemma can_link_disjoint_impls {comp_l comp_r} :
      (* We only need the Himp hypothesis, so this could be weakeaned if needed *)
      comp_l ##ₗ comp_r ->
      comp_l.(imports) ##ₘ comp_r.(imports).
    Proof.
      intros [].
      inversion Hwf_l. inversion Hwf_r.
      apply map_disjoint_spec.
      intros a s t p1_a p2_a.
      apply mk_is_Some in p1_a, p2_a.
      apply elem_of_dom in p1_a, p2_a.
      apply Himp in p1_a. apply Himp0 in p2_a.
      apply elem_of_dom in p1_a, p2_a.
      destruct p1_a as [w1 p1_a]. destruct p2_a as [w2 p2_a].
      apply (map_disjoint_spec comp_l.(segment) comp_r.(segment)) with a w1 w2;
      assumption.
    Qed.

    Lemma is_context_is_program {context lib regs}:
      is_context context lib regs ->
      is_program (link context lib) regs.
    Proof.
      intros [ ].
      apply is_program_intro.
      - apply link_well_formed. assumption.
      - apply map_eq. intros a.
        rewrite lookup_empty.
        apply map_filter_lookup_None.
        right. intros s a_imps.
        apply lookup_union_Some in a_imps.
        intros none.
        apply lookup_union_None in none.
        destruct none as [n_l n_r].
        destruct a_imps as [a_l | a_r].
        specialize (Hno_imps_r _ _ a_l).
        apply elem_of_dom in Hno_imps_r.
        rewrite n_r in Hno_imps_r.
        contradiction (is_Some_None Hno_imps_r).
        specialize (Hno_imps_l _ _ a_r).
        apply elem_of_dom in Hno_imps_l.
        rewrite n_l in Hno_imps_l.
        contradiction (is_Some_None Hno_imps_l).
        apply can_link_disjoint_impls. assumption.
      - intros r w rw.
        inversion Hcan_link.
        apply (word_restrictions_incr _ _ _ (link_segment_dom_subseteq_l Hwf_l Hwf_r)).
        apply (Hwr_regs r w rw).
    Qed.

  End LinkWellFormed.

  (** Lemmas on the symmetry/commutativity of links *)
  Section LinkSymmetric.
    Lemma can_link_sym : Symmetric can_link.
    Proof.
      intros x y [ ].
      apply can_link_intro; try apply map_disjoint_sym; assumption.
    Qed.

    Lemma link_comm {a b}: a ##ₗ b -> link a b = link b a.
    Proof.
      intros sep. inversion sep.
      specialize (can_link_disjoint_impls sep). intros Himp_disj.
      unfold link. f_equal.
      - rewrite resolve_imports_twice.
        rewrite resolve_imports_twice.
        f_equal; apply map_union_comm.
        1,5: apply map_disjoint_sym.
        all: try assumption.
      - rewrite map_union_comm.
        f_equal. apply map_union_comm.
        all: assumption.
      - apply map_union_comm; assumption.
    Qed.
  End LinkSymmetric.

  (** Lemmas on the associativity of links *)
  Section LinkAssociative.
    Lemma can_link_weaken_l {a b c} :
      a ##ₗ b ->
      link a b ##ₗ c ->
      a ##ₗ c.
    Proof.
      intros a_b ab_c.
      inversion a_b. inversion ab_c.
      apply can_link_intro; try assumption.
      specialize (link_segment_dom_subseteq_l Hwf_l Hwf_r).
      intros seg_a_seg_ab.
      rewrite map_disjoint_dom.
      intros x xa xb.
      specialize (seg_a_seg_ab x xa).
      apply map_disjoint_dom in Hms_disj0.
      apply (Hms_disj0 x seg_a_seg_ab xb).
      apply (map_disjoint_weaken_l _ _ _ Hexp_disj0).
      apply map_union_subseteq_l.
    Qed.

    Lemma can_link_weaken_r {a b c} :
      a ##ₗ b ->
      link a b ##ₗ c ->
      b ##ₗ c.
    Proof.
      intros a_b ab_c.
      apply can_link_sym in a_b.
      apply (@can_link_weaken_l b a). assumption.
      rewrite link_comm; assumption.
    Qed.

    Lemma can_link_assoc {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      link a b ##ₗ c.
    Proof.
      intros ab ac bc.
      inversion ab. inversion ac. inversion bc.
      apply can_link_intro.
      - apply link_well_formed; assumption.
      - assumption.
      - rewrite map_disjoint_dom.
        rewrite resolve_imports_link_dom; try assumption.
        rewrite dom_union_L.
        rewrite disjoint_union_l.
        split; rewrite <- map_disjoint_dom; assumption.
      - rewrite map_disjoint_union_l.
        split; assumption.
    Qed.

    Lemma link_exports_assoc a b c :
      exports a ∪ exports (link b c) = exports (link a b) ∪ exports c.
    Proof. apply map_union_assoc. Qed.

    Lemma link_imports_rev {a b} :
      a ##ₗ b ->
      ∀ addr symbol,
        exports (link a b) !! symbol = None ->
        imports (link a b) !! addr = Some symbol <->
        (imports a !! addr = Some symbol \/ imports b !! addr = Some symbol).
    Proof.
      intros sep addr symbol exp_diff.
      split.
      - intros ab_addr.
        apply map_filter_lookup_Some in ab_addr.
        destruct ab_addr as [union_addr export_symbol].
        rewrite - lookup_union_Some. assumption.
        apply (can_link_disjoint_impls sep).
      - intros imps_union.
        rewrite map_filter_lookup_Some.
        split.
        rewrite lookup_union_Some. assumption.
        apply (can_link_disjoint_impls sep).
        assumption.
    Qed.

    Lemma link_imports_none {a b}:
      ∀ addr,
        imports a !! addr = None ->
        imports b !! addr = None ->
        imports (link a b) !! addr = None.
    Proof.
      intros.
      rewrite map_filter_lookup_None.
      left. rewrite lookup_union_None.
      split; assumption.
    Qed.

    Lemma resolve_imports_assoc {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      resolve_imports
        (imports (link a b))
        (exports (link a b) ∪ exports c)
        (segment (link a b) ∪ segment c) =
      resolve_imports
        (imports a)
        (exports (link a b) ∪ exports c)
        (resolve_imports
          (imports b)
          (exports (link a b) ∪ exports c)
          (segment a ∪ segment b ∪ segment c)).
    Proof.
      intros ab ac bc.
      (* destruct a as [ ms imps exp ]. simpl.
      assert (imps = map_fold (fun '(k,v) m => (@insert Addr Symbols (gmap Addr Symbols) k v m)) (∅ : imports_type) imps).
      apply (map_fold_ind
        (fun (m:segment_type) (imp:imports_type) =>
        imp = imps ->
        resolve_imports
          (filter
              (λ '(_, s), (exp ∪ exports b) !! s = None)
              (imp ∪ imports b))
          (exp ∪ exports b ∪ exports c)
          (m) =
        resolve_imports imp (exp ∪ exports b ∪ exports c)
          (resolve_imports (imports b) (exp ∪ exports b ∪ exports c)
            (ms ∪ segment b ∪ segment c)))).

        dom (gset Addr) imp ⊆ dom _ ms -> dom _ m = dom _ ms)). *)
      inversion ab. inversion Hwf_l. inversion Hwf_r.
      apply map_eq. intros addr.
      specialize (can_link_disjoint_impls ab). intro iab.
      destruct (
        map_filter_lookup_None
          (fun '(_,s) => (exports (link a b)) !! s = None)
          (imports a ∪ imports b) addr) as [ _ l_none ].
      do 3 rewrite resolve_imports_spec.
      destruct (Some_dec (imports a !! addr)) as [[sa ia_addr] | ia_addr];
      destruct (Some_dec (imports b !! addr)) as [[sb ib_addr] | ib_addr].
      exfalso.
      apply (map_disjoint_spec (imports a) (imports b)) with addr sa sb; assumption.
      all: rewrite ia_addr; rewrite ib_addr.
      rename sa into s. 2: rename sb into s.
      destruct (Some_dec (exports a !! s)) as [[wa ea_s] | ea_s].
      exfalso. apply (Hdisj s addr (mk_is_Some _ _ ea_s) ia_addr).
      2: destruct (Some_dec (exports b !! s)) as [[wb eb_s] | eb_s].
      2: exfalso; apply (Hdisj0 s addr (mk_is_Some _ _ eb_s) ib_addr).
      destruct (Some_dec (exports b !! s)) as [[w eb_s] | eb_s].
      3: destruct (Some_dec (exports a !! s)) as [[w ea_s] | ea_s].

      1,3: assert (ab_s: exports (link a b) !! s = Some w).
           apply lookup_union_Some_r; assumption.
           2: apply lookup_union_Some_l; assumption.
      1,2: assert (∀ x : Symbols, (imports a ∪ imports b) !! addr = Some x → (exports (link a b)) !! x ≠ None).
      1,3: intros x ux;
           apply lookup_union_Some in ux; try assumption;
           rewrite ia_addr in ux; rewrite ib_addr in ux;
           destruct ux as [ H | H ]; try discriminate H;
           apply Some_inj in H; rewrite <- H; rewrite ab_s;
           discriminate.
      1,2: rewrite (l_none (or_intror H));
           unfold link; simpl;
           rewrite resolve_imports_twice; try auto using map_disjoint_sym.
      1,2: assert (abc_s: (exports a ∪ exports b ∪ exports c) !! s = Some w).
      1,3: apply lookup_union_Some_l; assumption.
      1,2: rewrite abc_s; apply lookup_union_Some_l;
           rewrite resolve_imports_spec.
      rewrite lookup_union_r; try assumption. rewrite ia_addr.
      2: rewrite (lookup_union_Some_l _ _ _ _ ib_addr).
      1,2: rewrite ab_s; reflexivity.

      1,2: assert (Hi : (imports a ∪ imports b) !! addr = Some s).
           apply lookup_union_Some_l. assumption.
           2: rewrite lookup_union_r; assumption.
      1,2: assert (He: (exports a ∪ exports b) !! s = None);
           try (apply lookup_union_None; split; assumption).
      1,2: destruct (
            map_filter_lookup_Some
              (fun '(_,s) => (exports (link a b)) !! s = None)
              (imports a ∪ imports b) addr s) as [ _ l_some ].

      1,2: rewrite (l_some (conj Hi He));
           destruct ((exports (link a b) ∪ exports c) !! s); try reflexivity.
      assert (is_Some (segment a !! addr)).
      3: assert (is_Some (segment b !! addr)).
      1,3: rewrite -elem_of_dom;
           apply Himp || apply Himp0; rewrite elem_of_dom;
           apply (mk_is_Some _ _ ia_addr) || apply (mk_is_Some _ _ ib_addr).
      1,2: destruct H as [w sa_w];
           rewrite -map_union_assoc.
      2: assert (segment a !! addr = None).
      2: {
          destruct (Some_dec ((segment a) !! addr)) as [[w' sa_w' ] | sa_w' ].
          exfalso. apply (map_disjoint_spec (segment a) (segment b)) with addr w' w; assumption.
          assumption.
       }
      2: symmetry; rewrite lookup_union_r; try assumption; symmetry.
      1,2:
      rewrite (lookup_union_Some_l _ _ _ _ sa_w);
      apply lookup_union_Some_l; rewrite resolve_imports_spec;
      rewrite ib_addr;
      rewrite resolve_imports_spec;
      rewrite ia_addr; rewrite He.
      apply lookup_union_Some_l. assumption.
      rewrite lookup_union_r. assumption. assumption.
      assert (imports (link a b) !! addr = None).
      apply l_none. left.
      apply lookup_union_None; split; assumption.
      rewrite H.
    Admitted.


    Lemma link_assoc {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      link a (link b c) = link (link a b) c.
    Proof.
      intros ab ac bc.
      assert (a_bc: a ##ₗ link b c).
      { apply can_link_sym. apply can_link_assoc; auto using can_link_sym. }
      assert (ab_c: link a b ##ₗ c).
      { apply can_link_assoc; auto using can_link_sym. }
      specialize (link_exports_assoc a b c). intros exp_eq.
      (* assert (imp_eq: imports a ∪ imports (link b c) = imports (link a b) ∪ imports c).

      apply map_union_assoc.
      inversion ab. inversion ac. inversion bc.
      inversion a_bc. inversion ab_c. *)

      unfold link at 1. symmetry. unfold link at 1. f_equal.
      - repeat rewrite resolve_imports_twice.
        2,3: apply can_link_disjoint_impls; auto using can_link_sym.
        apply map_eq. intros addr.
        rewrite resolve_imports_spec.
        rewrite resolve_imports_spec.
        unfold link. simpl.
        repeat rewrite resolve_imports_twice.
        2,3: apply can_link_disjoint_impls; auto using can_link_sym.
        rewrite exp_eq.
        specialize (can_link_disjoint_impls ab).
        specialize (can_link_disjoint_impls ac).
        specialize (can_link_disjoint_impls bc).
        intros Hbc Hac Hab.
        inversion ab. inversion ac. inversion bc.
        inversion Hwf_l. inversion Hwf_r. inversion Hwf_r0.
        destruct (Some_dec (imports c !! addr)) as [[sc ic_addr] | ic_addr];
        destruct (Some_dec (imports b !! addr)) as [[sb ib_addr] | ib_addr];
        destruct (Some_dec (imports a !! addr)) as [[sa ia_addr] | ia_addr];
        try (exfalso; apply (map_disjoint_spec (imports a) (imports b)) with addr sa sb; assumption);
        try (exfalso; apply (map_disjoint_spec (imports a) (imports c)) with addr sa sc; assumption);
        try (exfalso; apply (map_disjoint_spec (imports b) (imports c)) with addr sb sc; assumption).
        rewrite (lookup_union_Some_l _ _ _ _ ic_addr).
        rename sc into s. 2: rename sb into s. 3: rename sa into s.
        destruct (Some_dec (exports c !! s)) as [[sc ec_s] | ec_s];
        destruct (Some_dec (exports b !! s)) as [[sb eb_s] | eb_s];
        destruct (Some_dec (exports a !! s)) as [[sa ea_s] | ea_s];
        try (exfalso; apply (map_disjoint_spec (exports a) (exports b)) with s sa sb; assumption);
        try (exfalso; apply (map_disjoint_spec (exports a) (exports c)) with s sa sc; assumption);
        try (exfalso; apply (map_disjoint_spec (exports b) (exports c)) with s sb sc; assumption).
        contradiction (Hdisj1 s addr (mk_is_Some _ _ ec_s) ic_addr).
        rewrite -map_union_assoc.
        rewrite (lookup_union_r _ _ _ ea_s).
        rewrite (lookup_union_Some_l _ _ _ _ eb_s).
        (* rewrite (lookup_union_r _ _ _ eb_s).
        rewrite ec_s. *)
        rewrite map_filter_lookup_Some.
        destruct ()
        rewrite (lookup_union)
        ia_addr ib_addr.
        contradiction (map_disjoint_spec Hbc addr ib_addr ic_addr).
        specialize (Hbc addr).
        contradiction (Hbc addr ib_addr ia_addr).

        destruct (Some_dec ((imports c ∪ imports (link a b)) !! addr)) as [[s cab_addr] | cab_addr];
        rewrite cab_addr.
        shelve.
      - apply map_filter_strong_ext.
        intros addr symbol. rewrite exp_eq.
        split;
        intros [export_symbol import_addr]; split; try assumption.
        all: apply lookup_union_None in export_symbol;
          destruct export_symbol as [export_symbol ec];
          apply lookup_union_None in export_symbol;
          destruct export_symbol as [ea eb].
        all: rewrite lookup_union_Some;
          try (apply can_link_disjoint_impls; auto using can_link_sym).
        rewrite (link_imports_rev bc).
        3: rewrite (link_imports_rev ab).
        2,4: apply lookup_union_None; split; assumption.
        all: apply lookup_union_Some in import_addr.
        2,4: apply can_link_disjoint_impls; auto using can_link_sym.
        all: destruct import_addr as [import_addr | import_addr].
        apply (link_imports_rev ab) in import_addr.
        apply or_assoc. auto.
        apply lookup_union_None; split; assumption.
        auto. auto.
        apply (link_imports_rev bc) in import_addr.
        apply or_assoc. auto.
        apply lookup_union_None; split; assumption.
      - symmetry. apply exp_eq.
      Admitted.

  End LinkAssociative.
End Linking.

Arguments component _ {_ _}.
Arguments exports_type _ {_ _}.
Arguments imports_type _ : clear implicits.

(** Simple lemmas used to weaken word_restrictions
    and address_restrictions in is_link and well_formed_xxx *)
Section LinkWeakenRestrictions.
  Context {Symbols: Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Context {word_restrictions: Word -> gset Addr -> Prop}.
  Context {word_restrictions': Word -> gset Addr -> Prop}.
  Variable word_restrictions_weaken:
    ∀ w a, word_restrictions w a -> word_restrictions' w a.

  Context {addr_restrictions: gset Addr -> Prop}.
  Context {addr_restrictions': gset Addr -> Prop}.
  Variable addr_restrictions_weaken:
    ∀ a, addr_restrictions a -> addr_restrictions' a.

  (* ==== Well formed comp ==== *)

  Lemma wf_comp_weaken_wr :
    ∀ {comp : component Symbols},
    well_formed_comp word_restrictions addr_restrictions comp ->
    well_formed_comp word_restrictions' addr_restrictions comp.
  Proof.
    intros comp [ ].
    apply wf_comp_intro.
    all: try assumption.
    intros s a H.
    apply word_restrictions_weaken.
    apply (Hwr_exp s a H).
    intros a w H.
    apply word_restrictions_weaken.
    apply (Hwr_ms a w H).
  Qed.

  Lemma wf_comp_weaken_ar :
    ∀ {comp : component Symbols},
    well_formed_comp word_restrictions addr_restrictions comp ->
    well_formed_comp word_restrictions addr_restrictions' comp.
  Proof.
    intros comp [ ].
    apply wf_comp_intro.
    all: try assumption.
    apply addr_restrictions_weaken.
    assumption.
  Qed.

  (* ==== can_link ==== *)

  Lemma can_link_weaken_wr :
    ∀ {a b : component Symbols},
    can_link word_restrictions addr_restrictions a b ->
    can_link word_restrictions' addr_restrictions a b.
  Proof.
    intros a b [ ].
    apply can_link_intro; try apply wf_comp_weaken_wr; assumption.
  Qed.

  Lemma can_link_weaken_ar :
    ∀ {a b : component Symbols},
    can_link word_restrictions addr_restrictions a b ->
    can_link word_restrictions addr_restrictions' a b.
  Proof.
    intros a b [ ].
    apply can_link_intro; try apply wf_comp_weaken_ar; assumption.
  Qed.

  (* ==== is_program ==== *)

  Lemma is_program_weaken_wr :
    ∀ {comp : component Symbols} {regs},
    is_program word_restrictions addr_restrictions comp regs ->
    is_program word_restrictions' addr_restrictions comp regs.
  Proof.
    intros comp regs [].
    apply is_program_intro.
    apply wf_comp_weaken_wr. assumption.
    assumption.
    intros r w rr_w.
    apply (word_restrictions_weaken w _ (Hwr_regs r w rr_w)).
  Qed.

  Lemma is_program_weaken_ar :
    ∀ {comp : component Symbols} {regs},
    is_program word_restrictions addr_restrictions comp regs ->
    is_program word_restrictions addr_restrictions' comp regs.
  Proof.
    intros comp regs [].
    apply is_program_intro.
    apply wf_comp_weaken_ar.
    all: assumption.
  Qed.

  (* ==== is context ==== *)

  Lemma is_context_weaken_wr :
    ∀ {context lib : component Symbols} {regs},
    is_context word_restrictions addr_restrictions context lib regs ->
    is_context word_restrictions' addr_restrictions context lib regs.
  Proof.
    intros context lib regs [].
    apply is_context_intro.
    apply can_link_weaken_wr. assumption.
    intros r w rr_w.
    apply (word_restrictions_weaken w _ (Hwr_regs r w rr_w)).
    all: assumption.
  Qed.

  Lemma is_context_weaken_ar :
    ∀ {context lib : component Symbols} {regs},
    is_context word_restrictions addr_restrictions context lib regs ->
    is_context word_restrictions addr_restrictions' context lib regs.
  Proof.
    intros context lib regs [].
    apply is_context_intro.
    apply can_link_weaken_ar. all: assumption.
  Qed.

End LinkWeakenRestrictions.
