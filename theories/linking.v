From Coq Require Import Eqdep_dec.
From iris Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps fin_sets.
From cap_machine Require Import stdpp_img addr_reg machine_base.


Class RelationStable2 {A B:Type} (R:relation B) (P: A -> B -> Prop) :=
  relation_stable2 : ∀ w a b, R a b -> P w a -> P w b.

Class OperatorStable {A:Type} (f:A -> A -> A) (P: A -> Prop) :=
  operator_stable : ∀ a b, P a -> P b -> P (f a b).

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
  Context {word_restrictions_subseteq_stable2: RelationStable2 (⊆) word_restrictions}.

  (** Example of a word_restrictions, ensure all capabilites point
      into the given segment *)
  Example can_address_only (word: Word) (addr_set: gset Addr) :=
    match word with
    | WInt _ => True
    | WCap _ b e _ => ∀ a, (b <= a < e)%a -> a ∈ addr_set
    end.
  #[global] Instance can_address_only_subseteq_stable2:
    RelationStable2 (⊆) can_address_only.
  Proof.
    intros w dom1 dom2 dom1_dom2. destruct w. auto.
    intros ca_dom1 addr addr_in_be.
    apply dom1_dom2. apply (ca_dom1 addr addr_in_be).
  Qed.

  (** Another example, no constraints on words at all *)
  Example unconstrained_word: Word -> gset Addr -> Prop := fun _ _ => True.
  #[global] Instance unconstrained_word_subseteqstable:
    RelationStable2 (⊆) unconstrained_word.
  Proof. intros w a b _ _. apply I. Qed.

  (** A predicate that can be used to restrict the address space to a subsection
      of memory (ex: reserve space for a stack).
      This should remain true on the link (union of segments where it holds) *)
  Variable addr_restrictions: gset Addr -> Prop.
  Context {addr_restrictions_union_stable: OperatorStable (∪) addr_restrictions}.

  (** Example addr_restriction, address greater than a given end_stack parameter *)
  Example addr_gt_than (e_stk: Addr) (dom: gset Addr) :=
    forall a, a ∈ dom -> (e_stk < a)%a.
  #[global] Instance addr_gt_than_union_stable (e_stk: Addr) :
    OperatorStable (∪) (addr_gt_than e_stk).
  Proof.
    intros dom1 dom2 gt_dom1 gt_dom2 a a_in_1or2.
    apply elem_of_union in a_in_1or2.
    destruct a_in_1or2 as [ a_in_1 | a_in_2 ].
    apply (gt_dom1 a a_in_1).
    apply (gt_dom2 a a_in_2).
  Qed.

  (** Another example, no constraints at all here *)
  Example unconstrained_addr : gset Addr -> Prop := fun _ => True.
  #[global] Instance unconstrained_addr_union_stable:
    OperatorStable (∪) unconstrained_addr.
  Proof. intros a. auto. Qed.

  Notation imports_type := (gmap Addr Symbols).
  Notation exports_type := (gmap Symbols Word).
  Notation segment_type := (gmap Addr Word).

  #[global] Instance exports_subseteq : SubsetEq exports_type := map_subseteq.

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

    exports : gmap Symbols Word;
    (** Segment exports, a map symbols -> word (often capabilities) *)
  }.

  #[global] Instance component_eq_dec : EqDecision component.
  Proof.
    intros [seg imp exp] [seg' imp' exp'].
    destruct (decide (seg = seg')) as [Hs | Hs].
    destruct (decide (imp = imp')) as [Hi | Hi].
    destruct (decide (exp = exp')) as [He | He].
    left. rewrite Hs. rewrite Hi. rewrite He. reflexivity.
    all: right; intros eq.
    apply (f_equal exports) in eq. contradiction (He eq).
    apply (f_equal imports) in eq. contradiction (Hi eq).
    apply (f_equal segment) in eq. contradiction (Hs eq).
  Qed.

  Inductive well_formed_comp (comp:component) : Prop :=
  | wf_comp_intro: forall
      (* the exported symbols and the imported symbols are disjoint *)
      (Hdisj: dom comp.(exports) ## img comp.(imports))
      (* We import only to addresses in our segment *)
      (Himp: dom comp.(imports) ⊆ dom comp.(segment))
      (* Word restriction on segment and exports *)
      (Hwr_exp: ∀ w, w ∈ img comp.(exports) -> word_restrictions w (dom comp.(segment)))
      (Hwr_ms: ∀ w, w ∈ img comp.(segment) -> word_restrictions w (dom comp.(segment)))
      (Har_ms: addr_restrictions (dom comp.(segment))),
      well_formed_comp comp.

  (** A program is a segment without imports and some register allocations *)
  Inductive is_program (comp:component) (regs:Reg) : Prop :=
  | is_program_intro: forall
      (Hwfcomp: well_formed_comp comp)
      (Hnoimports: comp.(imports) = ∅)
      (Hwr_regs: ∀ w, w ∈ img regs -> word_restrictions w (dom comp.(segment))),
      is_program comp regs.

  (** Add values defined in exp to the segment
      at addresses specified in imp *)
  Definition resolve_imports
  (imp: imports_type) (exp: exports_type) (ms: segment_type) :=
  map_fold (fun a s m => match exp !! s with
    | Some w => <[a:=w]> m
    | None => m end) ms imp.

  (** To form well defined links, our components must be well-formed
      and have separates memory segments and exported symbols *)
  Inductive can_link (comp_l comp_r : component) : Prop :=
  | can_link_intro: forall
      (Hwf_l: well_formed_comp comp_l)
      (Hwf_r: well_formed_comp comp_r)
      (Hms_disj: comp_l.(segment) ##ₘ comp_r.(segment))
      (Hexp_disj: comp_l.(exports) ##ₘ comp_r.(exports)),
      can_link comp_l comp_r.

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

  Infix "##ₗ" := can_link (at level 70).
  Infix "⋈" := link (at level 50).

  (** Asserts that context is a valid context to run library lib.
      i.e. sufficient condition to ensure that (link context lib) is a program *)
  Inductive is_context (context lib: component) (regs:Reg): Prop :=
  | is_context_intro: forall
      (Hcan_link: context ##ₗ lib)
      (Hwr_regs: ∀ w, w ∈ img regs -> word_restrictions w (dom context.(segment)))
      (Hno_imps_l: img lib.(imports) ⊆ dom context.(exports))
      (Hno_imps_r: img context.(imports) ⊆ dom lib.(exports)),
      is_context context lib regs.

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
      forall {imp exp ms w},
        w ∈ img (resolve_imports imp exp ms) -> (w ∈ img exp) \/ (w ∈ img ms).
    Proof.
      intros imp exp ms w H.
      apply elem_of_img in H. destruct H as [a H].
      pose resolve_imports_spec as spec.
      specialize (spec imp exp ms a).
      destruct (imp !! a).
      destruct (exp !! s) as [w'|] eqn:exp_s.
      all: rewrite spec in H.
      left. rewrite <- exp_s in H. apply elem_of_img. exists s. apply H.
      all: right; apply elem_of_img; exists a; apply H.
    Qed.

    (** Resolve imports increases the domain of the memory segment *)
    Lemma resolve_imports_dom :
      forall {imp exp ms},
        dom ms ⊆ dom (resolve_imports imp exp ms).
    Proof.
      intros imp exp ms a a_in_ms.
      apply (map_fold_ind (fun ms imp => a ∈ dom ms)).
      - apply a_in_ms.
      - intros a' s m ms' ma'_none H. destruct (exp !! s).
        apply dom_insert_subseteq. all: apply H.
    Qed.

    (** We have equality of domains when imports are all in the memory segment
        (which is the case in well formed components) *)
    Lemma resolve_imports_dom_eq :
      forall {imp exp ms},
        dom imp ⊆ dom ms ->
        dom (resolve_imports imp exp ms) = dom ms.
    Proof.
      intros imp exp ms.
      apply (map_fold_ind (fun m imp => dom imp ⊆ dom ms -> dom m = dom ms)).
      - reflexivity.
      - intros addr s m ms' m_addr_none dom_ms'_dom_ms dom_incl.
        assert (m_ms: dom m ⊆ dom ms).
        transitivity (dom (<[addr:=s]> m)); auto.
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
      dom (c1 ⋈ c2).(segment) = dom (c1.(segment) ∪ c2.(segment)).
    Proof.
      intros wf1 wf2.
      rewrite resolve_imports_dom_eq;
      rewrite resolve_imports_dom_eq.
      reflexivity.
      all: inversion wf1; inversion wf2.
      2: transitivity (dom (segment c2));
         assumption || (rewrite dom_union_L; apply union_subseteq_r).
      all: transitivity (dom (segment c1));
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
      destruct (imp1 !! addr) as [w1|] eqn:imp1_a.
      rewrite (lookup_union_Some_l _ imp2 _ _ imp1_a) in spec3.
      destruct (exp !! w1); rewrite spec1; rewrite spec3. reflexivity.
      destruct (imp2 !! addr) as [w2|] eqn:imp2_a.
      contradiction (H' H _ _ _ imp1_a imp2_a).
      rewrite spec2. reflexivity.
      rewrite spec1.
      destruct (imp2 !! addr) as [w2|] eqn:imp2_a.
      rewrite (lookup_union_Some_r _ imp2 _ _ H imp2_a) in spec3.
      destruct (exp !! w2); rewrite spec2; rewrite spec3; reflexivity.
      destruct (lookup_union_None imp1 imp2 addr) as [ _ r ].
      rewrite (r _) in spec3.
      rewrite spec2. rewrite spec3. reflexivity.
      split; assumption.
    Qed.

    Lemma resolve_imports_comm:
      ∀ {imp1 imp2 exp ms},
        imp1 ##ₘ imp2 ->
        resolve_imports imp1 exp (resolve_imports imp2 exp ms) =
        resolve_imports imp2 exp (resolve_imports imp1 exp ms).
    Proof.
      intros.
      rewrite (resolve_imports_twice H).
      symmetry in H. rewrite (resolve_imports_twice H).
      f_equal; try reflexivity.
      apply map_union_comm. symmetry. apply H.
    Qed.

    Lemma resolve_imports_imports_empty:
      ∀ exp ms, resolve_imports ∅ exp ms = ms.
    Proof.
      intros exp ms. apply map_eq. intros addr.
      rewrite resolve_imports_spec. reflexivity.
    Qed.

    Lemma resolve_imports_exports_empty:
      ∀ imp ms, resolve_imports imp ∅ ms = ms.
    Proof.
      intros imp ms. apply map_eq. intros addr.
      rewrite resolve_imports_spec.
      destruct (imp !! addr). rewrite lookup_empty. all: reflexivity.
    Qed.

    Lemma link_segment_union {a b}:
      a ##ₗ b ->
      segment (a ⋈ b) =
        (resolve_imports a.(imports) b.(exports) a.(segment)) ∪
        (resolve_imports b.(imports) a.(exports) b.(segment)).
    Proof.
      intros Hsep. inversion Hsep.
      apply map_eq. intros addr.
      unfold link. simpl. rewrite resolve_imports_twice.
      rewrite resolve_imports_spec.
      destruct (segment a !! addr) as [w|] eqn:Ha_addr;
      destruct (segment b !! addr) as [w'|] eqn:Hb_addr.
      rewrite (map_disjoint_spec _ _) in Hms_disj.
      contradiction (Hms_disj _ _ _ Ha_addr Hb_addr).
      destruct (imports b !! addr) as [s'|] eqn:Hib_addr.
      inversion Hwf_r. apply mk_is_Some, elem_of_dom in Hib_addr.
      specialize (Himp addr Hib_addr). rewrite elem_of_dom Hb_addr in Himp.
      contradiction (is_Some_None Himp).
      rewrite lookup_union_r; try assumption.
      destruct (imports a !! addr) as [s|] eqn:Hia_addr.
      destruct (exports a !! s) eqn:Hea.
      inversion Hwf_l. apply mk_is_Some, elem_of_dom in Hea. apply elem_of_img_rev in Hia_addr.
      contradiction (Hdisj _ Hea Hia_addr).
      rewrite lookup_union_r; try assumption.
      symmetry. rewrite lookup_union_l. rewrite resolve_imports_spec Hia_addr.
      rewrite lookup_union_l. reflexivity. assumption.
      2: rewrite lookup_union_l; try assumption; rewrite lookup_union_l.
      1,3:rewrite -not_elem_of_dom resolve_imports_dom_eq; inversion Hwf_r;
          auto; rewrite not_elem_of_dom; assumption.
      rewrite resolve_imports_spec Hia_addr. reflexivity.

      destruct (imports a !! addr) as [s'|] eqn:Hia_addr.
      inversion Hwf_l. apply mk_is_Some, elem_of_dom in Hia_addr.
      specialize (Himp addr Hia_addr). rewrite elem_of_dom Ha_addr in Himp.
      contradiction (is_Some_None Himp).
      rewrite lookup_union_l; try assumption.
      destruct (imports b !! addr) as [s|] eqn:Hib_addr.
      destruct (exports b !! s) eqn:Heb.
      inversion Hwf_r. apply mk_is_Some, elem_of_dom in Heb. apply elem_of_img_rev in Hib_addr.
      contradiction (Hdisj _ Heb Hib_addr).
      rewrite lookup_union_l; try assumption.
      symmetry. rewrite lookup_union_r. rewrite resolve_imports_spec Hib_addr.
      rewrite lookup_union_r. reflexivity. assumption.
      2: rewrite lookup_union_r; try assumption; rewrite lookup_union_r.
      1,3:rewrite -not_elem_of_dom resolve_imports_dom_eq; inversion Hwf_l;
          auto; rewrite not_elem_of_dom; assumption.
      rewrite resolve_imports_spec Hib_addr. reflexivity.

      destruct (imports a !! addr) as [s'|] eqn:Hia_addr.
      inversion Hwf_l. apply mk_is_Some, elem_of_dom in Hia_addr.
      specialize (Himp addr Hia_addr). rewrite elem_of_dom Ha_addr in Himp.
      contradiction (is_Some_None Himp).
      destruct (imports b !! addr) as [s'|] eqn:Hib_addr.
      inversion Hwf_r. apply mk_is_Some, elem_of_dom in Hib_addr.
      specialize (Himp addr Hib_addr). rewrite elem_of_dom Hb_addr in Himp.
      contradiction (is_Some_None Himp).
      rewrite lookup_union_None_2; try assumption.
      rewrite lookup_union_None_2; try assumption.
      rewrite lookup_union_None_2. reflexivity.
      rewrite resolve_imports_spec Hia_addr Ha_addr. reflexivity.
      rewrite resolve_imports_spec Hib_addr Hb_addr. reflexivity.

      symmetry; apply (can_link_disjoint_impls Hsep).
    Qed.
  End resolve_imports.

  (** well_formedness of [link a b] and usefull lemmas *)
  Section LinkWellFormed.
    Lemma link_segment_dom {c1 c2}:
      well_formed_comp c1 ->
      well_formed_comp c2 ->
      dom (segment c1) ∪ dom (segment c2) = dom (segment (c1 ⋈ c2)).
    Proof.
      intros wf1 wf2. rewrite (resolve_imports_link_dom wf1 wf2).
      rewrite dom_union_L. reflexivity.
    Qed.

    Lemma link_segment_dom_subseteq_l {c1 c2} :
      well_formed_comp c1 ->
      well_formed_comp c2 ->
      dom (segment c1) ⊆ dom (segment (c1 ⋈ c2)).
    Proof.
      intros wf1 wf2. rewrite (resolve_imports_link_dom wf1 wf2).
      rewrite dom_union_L. apply union_subseteq_l.
    Qed.

    Lemma link_segment_dom_subseteq_r {c1 c2} :
      well_formed_comp c1 ->
      well_formed_comp c2 ->
      dom (segment c2) ⊆ dom (segment (c1 ⋈ c2)).
    Proof.
      intros wf1 wf2.
      rewrite (resolve_imports_link_dom wf1 wf2).
      rewrite dom_union_L. apply union_subseteq_r.
    Qed.

    (** link generates a well formed component
        if its arguments are well formed and disjoint *)
    Lemma link_well_formed {comp1 comp2} :
      comp1 ##ₗ comp2 ->
      well_formed_comp (comp1 ⋈ comp2).
    Proof.
      intros disj.
      inversion disj.
      inversion Hwf_l as [Hdisj1 Himp1 Hexp1 Hwr_ms1 Har_ms1].
      inversion Hwf_r as [Hdisj2 Himp2 Hexp2 Hwr_ms2 Har_ms2].
      specialize (link_segment_dom_subseteq_l Hwf_l Hwf_r).
      specialize (link_segment_dom_subseteq_r Hwf_l Hwf_r).
      intros imp2 imp1.
      apply wf_comp_intro.
      + intros s s_in_exp s_in_imps. (* exports are disjoint from import *)
        apply elem_of_dom in s_in_exp.
        apply elem_of_img in s_in_imps.
        destruct s_in_imps as [a s_in_imps].
        apply map_filter_lookup_Some in s_in_imps.
        destruct s_in_imps as [_ is_none_s].
        rewrite is_none_s in s_in_exp.
        apply (is_Some_None s_in_exp).
      + transitivity (dom (map_union comp1.(imports) comp2.(imports))).
        apply dom_filter_subseteq.
        rewrite dom_union_L.
        rewrite union_subseteq. split.
        transitivity (dom (segment comp1)); assumption.
        transitivity (dom (segment comp2)); assumption.
      + intros w exp_w. (* exported word respect word restrictions *)
        apply elem_of_img in exp_w. destruct exp_w as [s exp_s_w].
        apply lookup_union_Some in exp_s_w. 2: assumption.
        destruct exp_s_w as [exp_s | exp_s];
        apply elem_of_img_rev in exp_s.
        exact (relation_stable2 _ _ _ imp1 (Hexp1 w exp_s)).
        exact (relation_stable2 _ _ _ imp2 (Hexp2 w exp_s)).
      + intros w ms_w. (* word in segment follow word restrictions *)
        destruct (resolve_imports_spec_simple ms_w) as [ exp_w | ms_w'].
        destruct (img_union _ _ _ exp_w) as [exp1_w | exp2_w].
        exact (relation_stable2 _ _ _ imp1 (Hexp1 w exp1_w)).
        exact (relation_stable2 _ _ _ imp2 (Hexp2 w exp2_w)).
        destruct (resolve_imports_spec_simple ms_w') as [ exp_w | ms_w''].
        destruct (img_union _ _ _ exp_w) as [exp1_w | exp2_w].
        exact (relation_stable2 _ _ _ imp1 (Hexp1 w exp1_w)).
        exact (relation_stable2 _ _ _ imp2 (Hexp2 w exp2_w)).
        destruct (img_union _ _ _ ms_w'') as [ms1_w | ms2_w].
        exact (relation_stable2 _ _ _ imp1 (Hwr_ms1 w ms1_w)).
        exact (relation_stable2 _ _ _ imp2 (Hwr_ms2 w ms2_w)).
      + rewrite (resolve_imports_link_dom Hwf_l Hwf_r).
        rewrite dom_union_L.
        apply operator_stable; assumption.
    Qed.

    Lemma is_context_is_program {context lib regs}:
      is_context context lib regs ->
      is_program (context ⋈ lib) regs.
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
        apply elem_of_img_rev in a_l.
        specialize (Hno_imps_r s a_l).
        apply elem_of_dom in Hno_imps_r.
        rewrite n_r in Hno_imps_r.
        contradiction (is_Some_None Hno_imps_r).
        apply elem_of_img_rev in a_r.
        specialize (Hno_imps_l s a_r).
        apply elem_of_dom in Hno_imps_l.
        rewrite n_l in Hno_imps_l.
        contradiction (is_Some_None Hno_imps_l).
        apply can_link_disjoint_impls. assumption.
      - intros w rw.
        inversion Hcan_link.
        apply (relation_stable2 _ _ _ (link_segment_dom_subseteq_l Hwf_l Hwf_r)).
        exact (Hwr_regs w rw).
    Qed.

  End LinkWellFormed.

  (** Lemmas on the symmetry/commutativity of links *)
  Section LinkSymmetric.
    #[global] Instance can_link_sym : Symmetric can_link.
    Proof.
      intros x y [ ].
      apply can_link_intro; try apply map_disjoint_sym; assumption.
    Qed.

    Lemma link_comm {a b}: a ##ₗ b -> a ⋈ b = b ⋈ a.
    Proof.
      intros sep. inversion sep.
      specialize (can_link_disjoint_impls sep). intros Himp_disj.
      unfold link. f_equal.
      - rewrite resolve_imports_comm.
        f_equal. apply map_union_comm.
        2: f_equal; apply map_union_comm.
        all: auto using symmetry.
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
      a ⋈ b ##ₗ c ->
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
      a ⋈ b ##ₗ c ->
      b ##ₗ c.
    Proof.
      intros a_b ab_c.
      symmetry in a_b.
      apply (@can_link_weaken_l b a). assumption.
      rewrite link_comm; assumption.
    Qed.

    Lemma can_link_assoc {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      a ⋈ b ##ₗ c.
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

    Ltac solve_can_link :=
      match goal with
      (* destruct a ##ₗ b to get a.xxx ##ₘ b.xxx
         where xxx=exports, imports or segment *)
      | H: _ |- imports ?a ##ₘ imports ?b =>
          apply can_link_disjoint_impls; solve_can_link || fail 1
      | H: _ |- exports ?a ##ₘ exports ?b =>
          let H := fresh in
          assert (H: a ##ₗ b); solve_can_link;
          inversion H; assumption || fail 1
      | H: _ |- segment ?a ##ₘ segment ?b =>
          let H := fresh in
          assert (H: a ##ₗ b); solve_can_link;
          inversion H; assumption || fail 1
      (* prove a ##ₗ b *)
      | H: ?a ##ₗ ?b |- ?a ##ₗ ?b => exact H
      | H: ?b ##ₗ ?a |- ?a ##ₗ ?b => symmetry; exact H
      | H: is_context _ _ _ |- _ =>
          inversion H; clear H; solve_can_link || fail 1
      | H: _ ⋈ _ ##ₗ _ |- _ =>
          let H1 := fresh in let H2 := fresh in
          apply can_link_weaken_l in H as H1;
          apply can_link_weaken_r in H as H2;
          clear H; solve_can_link
      | H: _ ##ₗ _ ⋈ _ |- _ => symmetry in H;
          let H1 := fresh in let H2 := fresh in
          apply can_link_weaken_l in H as H1;
          apply can_link_weaken_r in H as H2;
          clear H; solve_can_link
      | H: _ |- _ ⋈ _ ##ₗ _ =>
          apply can_link_assoc; solve_can_link
      | H: _ |- _ ##ₗ _ ⋈ _ =>
          symmetry; apply can_link_assoc; solve_can_link
      end.

    Lemma link_exports_assoc a b c :
      exports a ∪ exports (b ⋈ c) = exports (a ⋈ b) ∪ exports c.
    Proof. apply map_union_assoc. Qed.

    Lemma link_imports_rev {a b} :
      a ##ₗ b ->
      ∀ addr symbol,
        imports (a ⋈ b) !! addr = Some symbol <->
        ((imports a !! addr = Some symbol \/ imports b !! addr = Some symbol)
        /\ exports (a ⋈ b) !! symbol = None).
    Proof.
      intros sep addr symbol.
      split.
      - intros ab_addr.
        apply map_filter_lookup_Some in ab_addr.
        destruct ab_addr as [union_addr export_symbol].
        rewrite - lookup_union_Some. split; assumption.
        solve_can_link.
      - intros [imps_union exp_disj].
        rewrite map_filter_lookup_Some.
        split.
        rewrite lookup_union_Some. assumption.
        solve_can_link. assumption.
    Qed.

    Lemma link_imports_rev_no_exports {a b} :
      a ##ₗ b ->
      ∀ addr symbol,
        exports (a ⋈ b) !! symbol = None ->
        imports (a ⋈ b) !! addr = Some symbol <->
        (imports a !! addr = Some symbol \/ imports b !! addr = Some symbol).
    Proof.
      intros sep addr symbol exp.
      rewrite (link_imports_rev sep addr symbol).
      split. intros [H _]. exact H. intros H.
      split. exact H. exact exp.
    Qed.

    Lemma link_imports_none {a b}:
      ∀ addr,
        imports a !! addr = None ->
        imports b !! addr = None ->
        imports (a ⋈ b) !! addr = None.
    Proof.
      intros.
      rewrite map_filter_lookup_None.
      left. rewrite lookup_union_None.
      split; assumption.
    Qed.

    Local Lemma disjoint_segment_is_none {a b addr w} :
      a ##ₗ b -> segment b !! addr = Some w -> segment a !! addr = None.
    Proof.
      intros ab sb. inversion ab.
      destruct ((segment a) !! addr) as [w'|] eqn:sa_w'.
      exfalso. apply (map_disjoint_spec (segment a) (segment b)) with addr w' w;
      assumption. reflexivity.
    Qed.

    Lemma resolve_imports_assoc_l {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      resolve_imports
        (imports (a ⋈ b))
        (exports (a ⋈ b) ∪ exports c)
        (segment (a ⋈ b) ∪ segment c) =
      resolve_imports
        (imports a)
        (exports (a ⋈ b) ∪ exports c)
        (resolve_imports
          (imports b)
          (exports (a ⋈ b) ∪ exports c)
          (segment a ∪ segment b ∪ segment c)).
    Proof.
      intros ab ac bc.
      inversion ab. inversion Hwf_l. inversion Hwf_r.
      apply map_eq. intros addr.
      specialize (can_link_disjoint_impls ab) as iab.
      destruct (
        map_filter_lookup_None
          (fun '(_,s) => (exports (a ⋈ b)) !! s = None)
          (imports a ∪ imports b) addr) as [ _ l_none ].
      do 3 rewrite resolve_imports_spec.
      destruct (imports a !! addr) as [sa|] eqn:ia_addr;
      destruct (imports b !! addr) as [sb|] eqn:ib_addr.
      exfalso.
      apply (map_disjoint_spec (imports a) (imports b)) with addr sa sb; assumption.
      rename sa into s. 2: rename sb into s.
      destruct (exports a !! s) as [wa|] eqn:ea_s.
      apply mk_is_Some, elem_of_dom in ea_s.
      apply elem_of_img_rev in ia_addr.
      contradiction (Hdisj s ea_s ia_addr).
      2: destruct (exports b !! s) as [wb|] eqn:eb_s.
      2: apply mk_is_Some, elem_of_dom in eb_s;
         apply elem_of_img_rev in ib_addr;
         contradiction (Hdisj0 s eb_s ib_addr).
      destruct (exports b !! s) as [w|] eqn:eb_s.
      3: destruct (exports a !! s) as [w|] eqn:ea_s.

      1,3: assert (ab_s: exports (a ⋈ b) !! s = Some w).
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
              (fun '(_,s) => (exports (a ⋈ b)) !! s = None)
              (imports a ∪ imports b) addr s) as [ _ l_some ].
      1,2: rewrite (l_some (conj Hi He)).
      1,2: destruct ((exports (a ⋈ b) ∪ exports c) !! s) as [w|] eqn:Hew;
           try reflexivity.
      assert (is_Some (segment a !! addr)).
      3: assert (is_Some (segment b !! addr)).
      1,3: rewrite -elem_of_dom;
           apply Himp || apply Himp0; rewrite elem_of_dom;
           apply (mk_is_Some _ _ ia_addr) || apply (mk_is_Some _ _ ib_addr).
      1,2: destruct H as [w sa_w];
           rewrite -map_union_assoc.
      2: pose (disjoint_segment_is_none ab sa_w).
      2: symmetry; rewrite lookup_union_r; try assumption; symmetry.
      1,2:
      rewrite (lookup_union_Some_l _ _ _ _ sa_w);
      apply lookup_union_Some_l; rewrite resolve_imports_spec;
      rewrite ib_addr;
      rewrite resolve_imports_spec;
      rewrite ia_addr; rewrite He.
      apply lookup_union_Some_l. assumption.
      rewrite lookup_union_r. assumption. assumption.
      rewrite (link_imports_none _ ia_addr ib_addr).
      destruct (segment c !! addr) as [w|] eqn:sc.
      pose (disjoint_segment_is_none ac sc).
      pose (disjoint_segment_is_none bc sc).
      rewrite lookup_union_r.
      rewrite lookup_union_r. reflexivity.
      apply lookup_union_None. split; assumption.
      do 2 rewrite resolve_imports_spec.
      rewrite ib_addr. rewrite ia_addr.
      apply lookup_union_None. split; assumption.
      destruct (segment b !! addr) as [w|] eqn:sb.
      pose (disjoint_segment_is_none ab sb).
      assert (sab_w: segment (a ⋈ b) !! addr = Some w).
      do 2 rewrite resolve_imports_spec.
      rewrite ib_addr. rewrite ia_addr.
      rewrite lookup_union_r; assumption.
      rewrite (lookup_union_Some_l _ _ _ _ sab_w).
      rewrite -map_union_assoc.
      rewrite lookup_union_r. symmetry.
      apply lookup_union_Some_l.
      1,2: assumption.
      destruct (segment a !! addr) as [w|] eqn:sa.
      rewrite -map_union_assoc.
      rewrite (lookup_union_Some_l _ _ _ _ sa).
      apply lookup_union_Some_l.
      do 2 rewrite resolve_imports_spec.
      rewrite ib_addr. rewrite ia_addr.
      apply lookup_union_Some_l. apply sa.
      assert (abc_none: (segment a ∪ segment b ∪ segment c) !! addr = None).
      rewrite lookup_union_None. split; try (rewrite lookup_union_None; split); assumption.
      rewrite abc_none.
      rewrite lookup_union_None. split.
      do 2 rewrite resolve_imports_spec.
      rewrite ib_addr. rewrite ia_addr.
      rewrite lookup_union_None. split.
      all: assumption.
    Qed.

    Lemma resolve_imports_assoc_r {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      resolve_imports
        (imports (a ⋈ b))
        (exports c ∪ exports (a ⋈ b))
        (segment c ∪ segment (a ⋈ b)) =
      resolve_imports
        (imports a)
        (exports c ∪ exports (a ⋈ b))
        (resolve_imports
          (imports b)
          (exports c ∪ exports (a ⋈ b))
          (segment c ∪ segment a ∪ segment b)).
    Proof.
      intros ab ac bc.
      specialize (can_link_assoc ab ac bc) as ab_c.
      replace (exports c ∪ exports (a ⋈ b)) with (exports (a ⋈ b) ∪ exports c).
      replace (segment c ∪ segment (a ⋈ b)) with (segment (a ⋈ b) ∪ segment c).
      replace (segment c ∪ segment a ∪ segment b) with (segment a ∪ segment b ∪ segment c).
      apply resolve_imports_assoc_l; assumption.
      all: inversion ab; inversion ac; inversion bc; inversion ab_c.
      all: rewrite map_union_comm; try reflexivity; try assumption.
      rewrite map_union_assoc. reflexivity.
      apply map_disjoint_union_l. split; assumption.
    Qed.


    Lemma link_assoc {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      a ⋈ (b ⋈ c) = (a ⋈ b) ⋈ c.
    Proof.
      intros ab ac bc.
      (* assert (a_bc: a ##ₗ b ⋈ c). solve_can_link.
      { symmetry. apply can_link_assoc; auto using symmetry. }
      assert (ab_c: a ⋈ b ##ₗ c).
      { apply can_link_assoc; auto using symmetry. } *)
      specialize (link_exports_assoc a b c) as exp_eq.
      unfold link at 1. symmetry. unfold link at 1. f_equal.
      - rewrite resolve_imports_assoc_l; try auto using symmetry.
        replace (resolve_imports (imports (b ⋈ c)) (exports a ∪ exports (b ⋈ c)) (resolve_imports (imports a) (exports a ∪ exports (b ⋈ c)) (segment a ∪ segment (b ⋈ c))))
        with (resolve_imports (imports a) (exports a ∪ exports (b ⋈ c)) (resolve_imports (imports (b ⋈ c)) (exports a ∪ exports (b ⋈ c))
        (segment a ∪ segment (b ⋈ c)))).
        rewrite resolve_imports_assoc_r; try auto using symmetry.
        all: repeat rewrite resolve_imports_twice.
        f_equal. 2: symmetry; apply exp_eq.
        rewrite -map_union_assoc. rewrite -map_union_comm. reflexivity.
        6: f_equal; rewrite map_union_comm; try reflexivity.
        all: try (apply map_disjoint_union_l; split).
        all: solve_can_link.
      - apply map_filter_strong_ext.
        intros addr symbol. rewrite exp_eq.
        split;
        intros [export_symbol import_addr]; split; try assumption.
        all: apply lookup_union_None in export_symbol;
          destruct export_symbol as [export_symbol ec];
          apply lookup_union_None in export_symbol;
          destruct export_symbol as [ea eb].
        all: rewrite lookup_union_Some;
          try (apply can_link_disjoint_impls; auto using symmetry).
        rewrite (link_imports_rev_no_exports bc).
        4: rewrite (link_imports_rev_no_exports ab).
        2,5: apply lookup_union_None; split; assumption.
        all: apply lookup_union_Some in import_addr.
        all: try solve_can_link.
        all: destruct import_addr as [import_addr | import_addr].
        apply (link_imports_rev_no_exports ab) in import_addr.
        apply or_assoc. auto.
        apply lookup_union_None; split; assumption.
        auto. auto.
        apply (link_imports_rev_no_exports bc) in import_addr.
        apply or_assoc. auto.
        apply lookup_union_None; split; assumption.
      - symmetry. apply exp_eq.
    Qed.

    Lemma no_imports_assoc_l {a b c} :
      b ##ₗ c ->
      img (imports (b ⋈ c)) ⊆ dom (exports a) ->
      img (imports c) ⊆ dom (exports (a ⋈ b)).
    Proof.
      intros bc Hno_imps s ic_addr.
      rewrite dom_union_L; apply elem_of_union.
      destruct (exports (b ⋈ c) !! s) as [w'|] eqn:ebc_s.
      right.
      inversion bc. inversion Hwf_r.
      apply lookup_union_Some in ebc_s.
      destruct ebc_s as [Hexp_w' | Hexp_w'].
      apply elem_of_dom. exists w'. exact Hexp_w'.
      exfalso. apply mk_is_Some, elem_of_dom in Hexp_w'.
      apply (Hdisj s Hexp_w' ic_addr).
      assumption.
      left.
      apply elem_of_img in ic_addr. destruct ic_addr as [addr ic_addr].
      apply or_intror with (A := (imports b !! addr = Some s)) in ic_addr.
      apply (link_imports_rev_no_exports bc addr s ebc_s) in ic_addr.
      apply elem_of_img_rev in ic_addr.
      apply (Hno_imps s ic_addr).
    Qed.

    Lemma no_imports_assoc_r {a b c} :
      a ##ₗ b -> b ##ₗ c ->
      img (imports (b ⋈ c)) ⊆ dom (exports a) ->
      img (imports a) ⊆ dom (exports (b ⋈ c)) ->
      img (imports (a ⋈ b)) ⊆ dom (exports c).
    Proof.
      intros ab bc Hno_imps_l Hno_imps_r s iab_addr.
      apply elem_of_img in iab_addr. destruct iab_addr as [addr iab_addr].
      apply link_imports_rev in iab_addr. 2: exact ab.
      destruct iab_addr as [[ia_addr | ib_addr] eab_s];
      apply lookup_union_None in eab_s; destruct eab_s as [ea_s eb_s].
      apply elem_of_dom. rewrite -(lookup_union_r (exports b)).
      apply elem_of_dom. apply elem_of_img_rev in ia_addr. exact (Hno_imps_r _ ia_addr).
      exact eb_s.
      destruct (imports (b ⋈ c) !! addr) as [s'|] eqn:ibc_addr.
      replace s' with s in ibc_addr. apply elem_of_img_rev in ibc_addr.
      specialize (Hno_imps_l s ibc_addr).
      apply elem_of_dom in Hno_imps_l. rewrite ea_s in Hno_imps_l.
      contradiction (is_Some_None Hno_imps_l).
      apply link_imports_rev in ibc_addr; try exact bc.
      destruct ibc_addr as [[ib_addr' | ic_addr] _].
      rewrite ib_addr in ib_addr'. apply (Some_inj _ _ ib_addr').
      exfalso. apply (map_disjoint_spec (imports b) (imports c)) with addr s s'.
      apply (can_link_disjoint_impls bc). exact ib_addr. exact ic_addr.
      apply map_filter_lookup_None in ibc_addr.
      destruct ibc_addr as [ibc_addr | ibc_addr].
      apply lookup_union_None in ibc_addr.
      rewrite ib_addr in ibc_addr. destruct ibc_addr as [ibc_addr _].  discriminate ibc_addr.
      apply (lookup_union_Some_l _ (imports c)) in ib_addr.
      specialize (ibc_addr s ib_addr).
      apply not_eq_None_Some in ibc_addr.
      destruct ibc_addr as [w ebc_s].
      apply lookup_union_Some in ebc_s.
      destruct ebc_s as [eb_s' | ec_s].
      rewrite eb_s' in eb_s. discriminate eb_s.
      apply elem_of_dom. exists w. exact ec_s.
      inversion bc. exact Hexp_disj.
    Qed.

    Lemma is_context_move_in {a b c regs} :
      b ##ₗ c ->
      is_context a (b ⋈ c) regs -> is_context (a ⋈ b) c regs.
    Proof.
      intros bc [ ]. inversion bc.
      apply is_context_intro.
      - solve_can_link.
      - intros w rr'. inversion Hcan_link.
        apply (relation_stable2 w _ _ (link_segment_dom_subseteq_l Hwf_l0 Hwf_l)).
        apply (Hwr_regs w rr').
      - exact (no_imports_assoc_l bc Hno_imps_l).
      - apply no_imports_assoc_r; try assumption.
        solve_can_link.
    Qed.

    Lemma is_context_move_out {a b c regs} :
      a ##ₗ b ->
      (∀ w, w ∈ img regs -> word_restrictions w (dom a.(segment))) ->
      is_context (a ⋈ b) c regs -> is_context a (b ⋈ c) regs.
    Proof.
      intros ab Hregs [].
      assert (ac: a ##ₗ c). solve_can_link.
      assert (bc: b ##ₗ c). solve_can_link.
      apply is_context_intro.
      - apply can_link_sym. apply can_link_assoc;
        auto using symmetry.
      - exact Hregs.
      - apply no_imports_assoc_r; try auto using symmetry.
        apply no_imports_assoc_r; try auto using symmetry.
        apply no_imports_assoc_l; assumption.
      - apply no_imports_assoc_l. auto using symmetry.
        apply no_imports_assoc_r; auto using symmetry.
    Qed.

    Lemma is_context_remove_exportless_l {ctxt comp extra regs} :
      ctxt ##ₗ extra -> exports extra = ∅ ->
      (∀ w : Word, w ∈ img regs → word_restrictions w (dom (segment ctxt))) ->
      is_context (ctxt ⋈ extra) comp regs ->
      is_context ctxt comp regs.
    Proof.
      intros Hsep Hex_null H [ ].
      apply is_context_intro. solve_can_link.
      assumption.
      unfold link in Hno_imps_l. simpl in Hno_imps_l.
      rewrite Hex_null map_union_empty in Hno_imps_l.
      apply Hno_imps_l.
      intros s Hs. apply elem_of_img in Hs as [a Has].
      apply Hno_imps_r. unfold link. simpl. rewrite Hex_null.
      apply elem_of_img. exists a. rewrite map_filter_lookup_Some.
      split. apply (lookup_union_Some_l _ _ _ _ Has).
      rewrite map_union_empty.
      destruct (exports ctxt !! s) eqn:Hexp.
      inversion Hsep. inversion Hwf_l.
      apply elem_of_img_rev in Has.
      apply mk_is_Some, elem_of_dom in Hexp.
      contradiction (Hdisj s Hexp Has). reflexivity.
    Qed.

    Lemma is_context_remove_exportless_r {ctxt comp extra regs} :
      comp ##ₗ extra -> exports extra = ∅ ->
      is_context ctxt (comp ⋈ extra) regs ->
      is_context ctxt comp regs.
    Proof.
      intros Hsep Hex_null [ ].
      apply is_context_intro. solve_can_link.
      assumption.
      intros s Hs. apply elem_of_img in Hs as [a Has].
      apply Hno_imps_l. unfold link. simpl. rewrite Hex_null.
      apply elem_of_img. exists a. rewrite map_filter_lookup_Some.
      split. apply (lookup_union_Some_l _ _ _ _ Has).
      rewrite map_union_empty.
      destruct (exports comp !! s) eqn:Hexp.
      inversion Hsep. inversion Hwf_l.
      apply elem_of_img_rev in Has.
      apply mk_is_Some, elem_of_dom in Hexp.
      contradiction (Hdisj s Hexp Has). reflexivity.
      replace (exports comp) with (exports (comp ⋈ extra)).
      apply Hno_imps_r. unfold link. simpl. rewrite Hex_null.
      apply map_union_empty.
    Qed.
  End LinkAssociative.

  (** Linking a list of segments*)
  Section LinkList.
    Variable addr_restrictions_empty : addr_restrictions ∅.

    Instance empty_comp: Empty component := {|
      segment := ∅; exports := ∅; imports := ∅
    |}.

    Lemma empty_comp_wf : well_formed_comp ∅.
    Proof.
      apply wf_comp_intro; try set_solver.
      rewrite dom_empty_L.
      apply addr_restrictions_empty.
    Qed.

    Lemma can_link_empty_r {c}:
      well_formed_comp c -> c ##ₗ ∅.
    Proof.
      intros Hwf_c.
      apply can_link_intro.
      exact Hwf_c. exact empty_comp_wf.
      all: simpl; apply map_disjoint_empty_r.
    Qed.

    Lemma can_link_empty_l {c}:
      well_formed_comp c -> ∅ ##ₗ c.
    Proof.
      intros Hwf_c.
      apply can_link_intro.
      exact empty_comp_wf. exact Hwf_c.
      all: simpl; apply map_disjoint_empty_l.
    Qed.

    Lemma empty_left_id {c}:
      well_formed_comp c -> ∅ ⋈ c = c.
    Proof.
      destruct c as [ seg imp exp ]. intros [].
      unfold link, empty_comp. simpl.
      f_equal; repeat rewrite map_empty_union.
      rewrite resolve_imports_imports_empty.
      apply map_eq. intros a.
      rewrite resolve_imports_spec.
      destruct (imp !! a) as [s|] eqn:His.
      destruct (exp !! s) as [w|] eqn:Hes.
      apply elem_of_img_rev in His. apply mk_is_Some, elem_of_dom in Hes.
      contradiction (Hdisj s Hes His).
      all: try reflexivity.
      apply map_eq. intros a.
      rewrite map_filter_lookup.
      destruct (imp !! a) as [s|] eqn:His; simpl.
      apply option_guard_True.
      destruct (exp !! s) as [w|] eqn:Hes;
      apply elem_of_img_rev in His. apply mk_is_Some, elem_of_dom in Hes.
      contradiction (Hdisj s Hes His).
      all: reflexivity.
    Qed.

    Lemma empty_right_id {c}:
      well_formed_comp c -> c ⋈ ∅ = c.
    Proof.
      intros Hwf_c. rewrite link_comm.
      exact (empty_left_id Hwf_c).
      exact (can_link_empty_r Hwf_c).
    Qed.

    (** Required property for linking a list of component
        They must verify can_link pairwise *)
    Inductive can_link_list: list component -> Prop :=
      | can_link_nil : can_link_list []
      | can_link_cons : ∀ seg seg_list,
          well_formed_comp seg ->
          Forall (fun c => can_link seg c) seg_list ->
          can_link_list seg_list ->
          can_link_list (seg :: seg_list).

    Lemma can_link_list_pairwise_1 {l}:
      can_link_list l ->
      ∀ i j, i ≠ j ->
        ∀ a b,
          l !! i = Some a ->
          l !! j = Some b -> a ##ₗ b.
    Proof.
      induction l.
      - intros _ i j _ a b Ha.
        rewrite lookup_nil in Ha. discriminate.
      - intros H i j Hij b c Hbl Hcl. inversion H.
        rewrite lookup_cons in Hbl.
        rewrite lookup_cons in Hcl.
        rewrite Forall_forall in H3.
        destruct i as [|i]; destruct j as [|j].
        contradiction (Hij eq_refl).
        apply Some_inj in Hbl.
        rewrite Hbl in H3. apply H3.
        rewrite elem_of_list_lookup. exists j. exact Hcl.
        apply Some_inj in Hcl.
        rewrite Hcl in H3. symmetry. apply H3.
        rewrite elem_of_list_lookup. exists i. exact Hbl.
        apply (IHl H4 i j).
        intro ij. apply (f_equal S) in ij. contradiction (Hij ij).
        all: assumption.
    Qed.

    Lemma can_link_list_well_formed_all {l}:
      can_link_list l ->
      Forall well_formed_comp l.
    Proof.
      intros Hl. induction l.
      apply Forall_nil_2.
      inversion Hl.
      apply Forall_cons_2.
      apply H1. apply (IHl H3).
    Qed.

    Lemma can_link_list_pairwise_neq {l}:
      can_link_list l ->
      ∀ a b, a ∈ l -> b ∈ l -> a ≠ b -> a ##ₗ b.
    Proof.
      intros Hl a b Ha Hb Hab.
      apply elem_of_list_lookup in Ha, Hb.
      destruct Ha as [i Ha]. destruct Hb as [j Hb].
      assert (Hij: i ≠ j).
      intros Hij. rewrite Hij in Ha. rewrite Ha in Hb.
      apply Some_inj in Hb. contradiction (Hab Hb).
      exact (can_link_list_pairwise_1 Hl i j Hij a b Ha Hb).
    Qed.

    Lemma can_link_list_pairwise_2 {l}:
      (∀ i j, i ≠ j ->
      ∀ a b,
        l !! i = Some a ->
        l !! j = Some b -> a ##ₗ b) ->
      Forall well_formed_comp l ->
      can_link_list l.
    Proof.
      intros H Hf.
      induction l.
      apply can_link_nil.
      apply can_link_cons.
      rewrite Forall_forall in Hf. apply Hf.
      apply elem_of_cons. left. reflexivity.
      rewrite Forall_forall. intros x Hx.
      rewrite elem_of_list_lookup in Hx. destruct Hx as [i Hx].
      apply (H 0 (S i)).
      auto. rewrite -head_lookup. reflexivity.
      rewrite -lookup_tail. apply Hx.
      apply IHl. intros i j Hij b c Hb Hc.
      apply (H (S i) (S j)).
      intros Hij'. lia.
      1,2: rewrite -lookup_tail; assumption.
      destruct (Forall_cons_1 _ _ _ Hf) as [_ H'].
      exact H'.
    Qed.

    Lemma can_link_list_pairwise l:
      can_link_list l <->
      Forall well_formed_comp l /\
      ∀ i j, i ≠ j -> ∀ a b,
        l !! i = Some a ->
        l !! j = Some b -> a ##ₗ b.
    Proof.
      split.
      intros H. split.
      apply (can_link_list_well_formed_all H).
      apply (can_link_list_pairwise_1 H).
      intros [].
      apply can_link_list_pairwise_2;
      assumption.
    Qed.

    Lemma can_link_list_Permutation {l l'}:
      can_link_list l -> l ≡ₚ l' ->
      can_link_list l'.
    Proof.
      intros Hl Hperm.
      rewrite can_link_list_pairwise.
      split.
      rewrite -(Forall_Permutation well_formed_comp _ _ _ _ Hperm).
      apply (can_link_list_well_formed_all Hl).
      intros c. reflexivity.
      intros i j Hij a b Hl'ia Hl'jb.
      rewrite can_link_list_pairwise in Hl.
      destruct Hl as [_ Hl].
      symmetry in Hperm.
      rewrite Permutation_inj in Hperm.
      destruct Hperm as [_ [f [Hinj_f Hf]]].
      apply (Hl (f i) (f j)).
      intros Hij'. apply Hinj_f in Hij'. contradiction (Hij Hij').
      all: rewrite -Hf; assumption.
    Qed.

    Fixpoint link_list l :=
      match l with
      | [] => ∅
      | l::ls => l ⋈ (link_list ls)
      end.

    Lemma can_link_link_list {c l} :
      can_link_list (c :: l) -> c ##ₗ link_list l.
    Proof.
      generalize c. clear c.
      induction l.
      simpl. intros c H.
      inversion H. apply (can_link_empty_r H2).
      intros c H. simpl.
      symmetry.
      inversion H. inversion H4.
      apply can_link_assoc.
      apply IHl.
      apply can_link_cons; assumption.
      rewrite Forall_forall in H3.
      symmetry. apply H3. apply elem_of_cons. left. reflexivity.
      symmetry. apply IHl. apply can_link_cons; try assumption.
      destruct (Forall_cons_1 _ _ _ H3) as [_ H'].
      exact H'.
    Qed.

    Lemma link_list_well_formed {l}:
      can_link_list l ->
      well_formed_comp (link_list l).
    Proof.
      intros H.
      induction l; simpl.
      exact empty_comp_wf.
      apply link_well_formed.
      apply (can_link_link_list H).
    Qed.

    Lemma link_list_Permutation {l l'}:
      can_link_list l -> l ≡ₚ l' ->
      link_list l = link_list l'.
    Proof.
      intros Hcl Hperm.
      induction Hperm.
      - reflexivity.
      - inversion Hcl. simpl. f_equal. apply IHHperm. assumption.
      - assert (Hxy : x ##ₗ y).
        { apply (can_link_list_pairwise_1 Hcl 1 0); auto. }
        assert (Hxl : x ##ₗ link_list l).
        { inversion Hcl. apply (can_link_link_list H3). }
        assert (Hyl : y ##ₗ link_list l).
        { apply (@can_link_list_Permutation _ (x::y::l)) in Hcl.
          inversion Hcl. apply (can_link_link_list H3).
          apply perm_swap. }
        simpl.
        rewrite link_assoc; try auto using symmetry.
        rewrite link_assoc; try auto using symmetry.
        replace (y ⋈ x) with (x ⋈ y). reflexivity.
        rewrite link_comm. reflexivity. apply Hxy.
      - rewrite (IHHperm1 Hcl).
        apply IHHperm2.
        apply (can_link_list_Permutation Hcl Hperm1).
    Qed.
  End LinkList.
End Linking.

Arguments component _ {_ _}.

Notation imports_type Symbols := (gmap Addr Symbols).
Notation exports_type Symbols := (gmap Symbols Word).
Notation segment_type := (gmap Addr Word).

#[global] Infix "⋈" := link (at level 50).

(** Simple lemmas used to weaken word_restrictions
    and address_restrictions in well_formed_comp, can_link, is_program... *)
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
    all: intros w H; apply word_restrictions_weaken.
    exact (Hwr_exp w H). apply (Hwr_ms w H).
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
    intros w rr_w.
    exact (word_restrictions_weaken w _ (Hwr_regs w rr_w)).
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
    intros w rr_w.
    apply (word_restrictions_weaken w _ (Hwr_regs w rr_w)).
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

Lemma any_implies_unconstrained_addr {P}:
  ∀ a, P a -> unconstrained_addr a.
Proof. intros. unfold unconstrained_addr. auto. Qed.

Lemma any_implies_unconstrained_word {P}:
  ∀ w a, P w a -> unconstrained_word w a.
Proof. intros. unfold unconstrained_word. auto. Qed.

(** Can solve simpl can_link and well_formed_comp goals using
    symmetry, compatibility with link and weakening *)
Ltac solve_can_link :=
  match goal with
  (* destruct a ##ₗ b to get a.xxx ##ₘ b.xxx
     where xxx=exports, imports or segment *)
  | H: _ |- imports ?a ##ₘ imports ?b =>
      apply (can_link_disjoint_impls unconstrained_word unconstrained_addr);
      solve_can_link || fail 1
  | H: _ |- exports ?a ##ₘ exports ?b =>
      let H := fresh in
      assert (H: can_link unconstrained_word unconstrained_addr a b);
      solve_can_link;
      inversion H; assumption || fail 1
  | H: _ |- segment ?a ##ₘ segment ?b =>
      let H := fresh in
      assert (H: can_link unconstrained_word unconstrained_addr a b);
      solve_can_link;
      inversion H; assumption || fail 1
  (* using symmetry *)
  | H: can_link ?wr ?ar ?a ?b |- can_link ?wr ?ar ?a ?b => exact H
  | H: can_link ?wr ?ar ?a ?b |- can_link ?wr ?ar ?b ?a => symmetry; exact H
  | H: well_formed_comp ?wr ?ar ?a |- well_formed_comp ?wr ?ar ?a => exact H
  | H: can_link _ _ ?a _ |- well_formed_comp _ _ ?a => inversion H; clear H; solve_can_link
  | H: can_link _ _ _ ?a |- well_formed_comp _ _ ?a => inversion H; clear H; solve_can_link
  (* using weakening *)
  | H: can_link ?wr _ _ _ |- can_link unconstrained_word _ _ _ =>
      tryif (unify wr unconstrained_word) then fail else (
        apply (can_link_weaken_wr (@any_implies_unconstrained_word wr)) in H;
        solve_can_link)
  | H: can_link _ ?ar _ _ |- can_link _ unconstrained_addr _ _ =>
      tryif (unify ar unconstrained_addr) then fail else (
        apply (can_link_weaken_ar (@any_implies_unconstrained_addr ar)) in H;
        solve_can_link)
  | H: can_link ?wr _ _ _, H2: ∀ w a, ?wr w a -> ?wr' w a |- can_link ?wr' _ _ _ =>
      tryif (unify wr wr') then fail else (
        apply (can_link_weaken_wr H2) in H; solve_can_link)
  | H: can_link _ ?ar _ _, H2: ∀ a, ?ar a -> ?ar' a |- can_link _ ?ar _ _ =>
      tryif (unify ar ar') then fail else (
        apply (can_link_weaken_ar H2) in H; solve_can_link)
   (* using weakening for well_formed_comp *)
  | H: well_formed_comp ?wr _ _ |- well_formed_comp unconstrained_word _ _ =>
      tryif (unify wr unconstrained_word) then fail else (
        apply (wf_comp_weaken_wr (@any_implies_unconstrained_word wr)) in H;
        solve_can_link)
  | H: well_formed_comp _ ?ar _ |- well_formed_comp _ unconstrained_addr _ =>
      tryif (unify ar unconstrained_addr) then fail else (
        apply (wf_comp_weaken_ar (@any_implies_unconstrained_addr ar)) in H;
        solve_can_link)
  | H: well_formed_comp ?wr _ _, H2: ∀ w a, ?wr w a -> ?wr' w a |- well_formed_comp ?wr' _ _ =>
      tryif (unify wr wr') then fail else (
        apply (wf_comp_weaken_wr H2) in H; solve_can_link)
  | H: well_formed_comp _ ?ar _, H2: ∀ a, ?ar a -> ?ar' a |- well_formed_comp _ ?ar' _ =>
      tryif (unify ar ar') then fail else (
        apply (wf_comp_weaken_ar H2) in H; solve_can_link)
  (* get extra can_link hypotheses hidden in inductives *)
  | H: is_context _ _ _ _ _ |- _ =>
      inversion H; clear H; solve_can_link || fail 1
  | H: can_link _ _ (_ ⋈ _) _ |- can_link _ _ _ _ =>
      let H1 := fresh in let H2 := fresh in
      apply can_link_weaken_l in H as H1;
      apply can_link_weaken_r in H as H2;
      clear H; solve_can_link
  | H: can_link _ _ _ (_ ⋈ _) |- can_link _ _ _ _ => symmetry in H;
      let H1 := fresh in let H2 := fresh in
      apply can_link_weaken_l in H as H1;
      apply can_link_weaken_r in H as H2;
      clear H; solve_can_link
  | H: _ |- can_link _ _ (_ ⋈ _) _ =>
      apply (can_link_assoc _ _); solve_can_link
  | H: _ |- can_link _ _ _ (_ ⋈ _) =>
      symmetry; apply (can_link_assoc _ _); solve_can_link
  | H: _ |- well_formed_comp _ _ (_ ⋈ _) =>
      apply (link_well_formed _ _); solve_can_link
  end.
