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

  Record pre_component := {
    segment : segment_type;
    (** the component's memory segment, a map addr -> word *)

    imports : imports_type;
    (** the segment imports, a pair (symbol, address to place word) *)

    exports : exports_type;
    (** Segment exports, a map symbols -> word (often capabilities) *)
  }.

  Inductive component: Type :=
  | Lib: pre_component -> component
  | Main: pre_component -> Word -> component.

  Inductive well_formed_pre_comp: pre_component -> Prop :=
  | wf_pre_intro:
      ∀ pcomp
        (* This should be "dom pcomp.(exports) ## img pcomp.(imports)" but stdpp doesn't have img/codom... *)
        (Hdisj: ∀ s, is_Some (pcomp.(exports) !! s) -> ~ ∃ a, pcomp.(imports) !! a = Some s)
        (* We import only to addresses in our segment *)
        (Himp: dom (gset Addr) pcomp.(imports) ⊆ dom _ pcomp.(segment))
        (* Word restriction on segment and exports, again would be better expresses with img/codom... *)
        (Hwr_exp: ∀ s w, pcomp.(exports) !! s = Some w -> word_restrictions w (dom _ pcomp.(segment)))
        (Hwr_ms: ∀ a w, pcomp.(segment) !! a = Some w -> word_restrictions w (dom _ pcomp.(segment)))
        (Har_ms: addr_restrictions (dom _ pcomp.(segment))),
        well_formed_pre_comp pcomp.

  Inductive well_formed_comp: component -> Prop :=
  | wf_lib:
      forall pcomp
        (Hwf_pre: well_formed_pre_comp pcomp),
        well_formed_comp (Lib pcomp)
  | wf_main:
      forall pcomp w_main
        (Hwf_pre: well_formed_pre_comp pcomp)
        (Hw_main: word_restrictions w_main (dom _ (pcomp.(segment)))),
        well_formed_comp (Main pcomp w_main).

  Inductive is_program: component -> Prop :=
  | is_program_intro:
      forall pcomp w_main
        (Hnoimports: pcomp.(imports) = ∅)
        (Hwfcomp: well_formed_comp (Main pcomp w_main)),
        is_program (Main pcomp w_main).

  Section resolve_imports.
    (** Add values defined in exp to the segment
        at addresses specified in imp *)
    Definition resolve_imports
      (imp: imports_type) (exp: exports_type) (ms: segment_type) :=
      map_fold (fun a s m => match exp !! s with
        | Some w => <[a:=w]> m
        | None => m end) ms imp.

    Lemma resolve_imports_spec:
      forall imp exp ms a,
        match imp !! a with
        | None => (resolve_imports imp exp ms) !! a = ms !! a
        | Some s =>
            match exp !! s with
            | None => (resolve_imports imp exp ms) !! a = ms !! a
            | Some wexp => (resolve_imports imp exp ms) !! a = Some wexp
            end
        end.
    Proof.
      intros imp exp ms a.
      eapply (map_fold_ind
      (fun m imp => forall a,
        match imp !! a with
        | None => m !! a = ms !! a
        | Some s => match exp !! s with
                    | None => m !! a = ms !! a
                    | Some wexp => m !! a = Some wexp
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
        match exp !! s with
        | None => (resolve_imports imp exp ms) !! a = ms !! a
        | Some wexp => (resolve_imports imp exp ms) !! a = Some wexp
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
    Lemma resolve_imports_spec_simple :
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

  (** To form well defined links, our componements memory segments and exported
      symbols must be disjoint *)
  Inductive disjoint_pre_component: pre_component -> pre_component -> Prop :=
  | disjoint_pre_component_intro :
      ∀ pcomp1 pcomp2
        (Hms_disj: pcomp1.(segment) ##ₘ pcomp2.(segment))
        (Hexp_disj: pcomp1.(exports) ##ₘ pcomp2.(exports)),
        disjoint_pre_component pcomp1 pcomp2.

  Infix "##ₚ" := disjoint_pre_component (at level 70).

  Inductive is_link_pre_comp: pre_component -> pre_component -> pre_component -> Prop :=
  | is_link_pre_comp_intro:
      forall pcomp1 pcomp2 pcomp_link
        (Hdisj: pcomp1 ##ₚ pcomp2)
        (Hexp: pcomp_link.(exports) = pcomp1.(exports) ∪ pcomp2.(exports))
        (Himp: pcomp_link.(imports) = filter (fun '(a,s) => pcomp_link.(exports) !! s = None)
               (pcomp1.(imports) ∪ pcomp2.(imports)))
        (Hms: pcomp_link.(segment) =
              resolve_imports pcomp2.(imports) pcomp_link.(exports) (
              resolve_imports pcomp1.(imports) pcomp_link.(exports) (
                pcomp1.(segment) ∪ pcomp2.(segment)))),
        is_link_pre_comp pcomp1 pcomp2 pcomp_link.

  Inductive is_link: component -> component -> component -> Prop :=
  | is_link_lib_lib:
      forall comp1 comp2 comp
        (Hlink: is_link_pre_comp comp1 comp2 comp)
        (Hwf_l: well_formed_comp (Lib comp1))
        (Hwf_r: well_formed_comp (Lib comp2)),
        is_link (Lib comp1) (Lib comp2) (Lib comp)
  | is_link_lib_main:
      forall comp1 comp2 comp w_main
        (Hlink: is_link_pre_comp comp1 comp2 comp)
        (Hwf_l: well_formed_comp (Lib comp1))
        (Hwf_r: well_formed_comp (Main comp2 w_main)),
        is_link (Lib comp1) (Main comp2 w_main) (Main comp w_main)
  | is_link_main_lib:
      forall comp1 comp2 comp w_main
        (Hlink: is_link_pre_comp comp1 comp2 comp)
        (Hwf_l: well_formed_comp (Main comp1 w_main))
        (Hwf_r: well_formed_comp (Lib comp2)),
        is_link (Main comp1 w_main) (Lib comp2) (Main comp w_main).

  Inductive is_context (c comp p: component): Prop :=
  | is_context_intro:
      forall (His_program: is_link c comp p /\ is_program p),
      is_context c comp p.

  (** Lemmas about the uniqueness of [c] in [link a b c] and variations thereof *)
  Section LinkUnique.
    Lemma is_link_pre_comp_unique {c_left c_right c1 c2} :
      is_link_pre_comp c_left c_right c1 ->
      is_link_pre_comp c_left c_right c2 ->
      c1 = c2.
    Proof.
      intros a b.
      destruct c_left as [msl impl expl].
      destruct c_right as [msr impr expr].
      destruct c1 as [ms1 imp1 exp1].
      destruct c2 as [ms2 imp2 exp2].
      inversion a.
      inversion b.
      simpl in *.
      assert (H_exp: exp1 = exp2).
      { rewrite Hexp. rewrite Hexp0. reflexivity. }
      f_equal.
      rewrite Hms. rewrite Hms0.
      rewrite H_exp. reflexivity.
      rewrite Himp. rewrite Himp0.
      rewrite H_exp. reflexivity.
      apply H_exp.
    Qed.

    Lemma is_link_unique {c_left c_right c1 c2} :
      is_link c_left c_right c1 ->
      is_link c_left c_right c2 ->
      c1 = c2.
    Proof.
      intros a b.
      destruct c_left as [[msl impl expl] | [msl impl expl] mainl];
      destruct c_right as [[msr impr expr] | [msr impr expr] mainr];
      destruct c1 as [[ms1 imp1 exp1] | [ms1 imp1 exp1] main1];
      destruct c2 as [[ms2 imp2 exp2] | [ms2 imp2 exp2] main2].
      all: inversion a.
      all: inversion b.
      all: rewrite (is_link_pre_comp_unique Hlink Hlink0).
      reflexivity.
      all: f_equal; rewrite <- H4, H9; reflexivity.
    Qed.

    Lemma context_unique {c_left c_right c1 c2} :
      is_context c_left c_right c1 ->
      is_context c_left c_right c2 ->
      c1 = c2.
    Proof.
      intros [[link1 _]] [[link2 _]].
      apply (is_link_unique link1 link2).
    Qed.
  End LinkUnique.

  (** Functions to build a linked component and lemmas about their correctness *)
  Section LinkExists.

    (** Creates link candidate for two precomponents *)
    Definition link_pre_comp : pre_component -> pre_component -> pre_component :=
      fun pcomp1 pcomp2 =>
        (* exports is union of exports *)
        let exp := pcomp1.(exports) ∪ pcomp2.(exports) in
        {|
          exports := exp;
          (* memory segment is union of segments, with resolved imports *)
          segment :=
              resolve_imports pcomp2.(imports) exp (
              resolve_imports pcomp1.(imports) exp (
              pcomp1.(segment) ∪ pcomp2.(segment)));
          (* imports is union of imports minus symbols is export *)
          imports :=
              filter
              (fun '(_,s) => exp !! s = None)
              (pcomp1.(imports) ∪ pcomp2.(imports));
        |}.

    (** link_pre_comp forms an is_link_pre_comp with its arguments (if segments are disjoint) *)
    Lemma link_pre_comp_is_link_pre_comp
      pcomp1 pcomp2 :
      pcomp1 ##ₚ pcomp2 ->
      is_link_pre_comp pcomp1 pcomp2 (link_pre_comp pcomp1 pcomp2).
    Proof.
      intros Hdisj.
      apply is_link_pre_comp_intro.
      + apply Hdisj.
      + reflexivity.
      + reflexivity.
      + reflexivity.
    Qed.

    (** make_link_pre_comp generates a well formed component
        if its arguments are well formed and disjoint *)
    Lemma link_pre_comp_well_formed
      pcomp1 pcomp2
      (wf_1: well_formed_pre_comp pcomp1)
      (wf_2: well_formed_pre_comp pcomp2)
      (Hdisj: pcomp1 ##ₚ pcomp2) :
      well_formed_pre_comp (link_pre_comp pcomp1 pcomp2).
    Proof.
      inversion wf_1 as [pcomp1' Hdisj1 Himp1 Hexp1 Hwr_ms1 Har_ms1].
      inversion wf_2 as [pcomp2' Hdisj2 Himp2 Hexp2 Hwr_ms2 Har_ms2].
      assert (imp1: dom (gset Addr) (segment pcomp1) ⊆ dom _ (segment (link_pre_comp pcomp1 pcomp2))).
      { do 2 rewrite resolve_imports_dom_eq; rewrite dom_union_L.
        3: transitivity (dom (gset Addr) (segment pcomp2));
           assumption || apply union_subseteq_r.
        all: transitivity (dom (gset Addr) (segment pcomp1));
           assumption || apply union_subseteq_l || reflexivity. }
      assert (imp2: dom (gset Addr) (segment pcomp2) ⊆ dom _ (segment (link_pre_comp pcomp1 pcomp2))).
      { do 2 rewrite resolve_imports_dom_eq; rewrite dom_union_L.
        1,3: transitivity (dom (gset Addr) (segment pcomp2));
             assumption || apply union_subseteq_r || reflexivity.
        all: transitivity (dom (gset Addr) (segment pcomp1));
             assumption || apply union_subseteq_l. }
      inversion Hdisj.
      apply wf_pre_intro.
      + intros s is_some_s. (* exports are disjoint from import *)
        intros [a sa_in_imps].
        apply map_filter_lookup_Some in sa_in_imps.
        destruct sa_in_imps as [_ is_none_s].
        rewrite is_none_s in is_some_s.
        apply (is_Some_None is_some_s).
      + transitivity (dom (gset Addr) (map_union pcomp1.(imports) pcomp2.(imports))).
        apply dom_filter_subseteq.
        rewrite dom_union_L.
        rewrite union_subseteq. split.
        transitivity (dom (gset Addr) (segment pcomp1)); assumption.
        transitivity (dom (gset Addr) (segment pcomp2)); assumption.
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
      + rewrite resolve_imports_dom_eq; rewrite resolve_imports_dom_eq.
        rewrite dom_union_L.
        apply addr_restrictions_union_stable; assumption.
        2: transitivity (dom (gset Addr) (segment pcomp2)); assumption ||
        rewrite dom_union_L; apply union_subseteq_r.
        all: transitivity (dom (gset Addr) (segment pcomp1)); assumption ||
        rewrite dom_union_L; apply union_subseteq_l.
    Qed.

    (** mlink_main_lib forms a link from a main and a lib *)
    Definition link_main_lib main lib main_s :=
      Main (link_pre_comp main lib) main_s.

    Lemma link_main_lib_is_link pcomp1 main pcomp2 :
      pcomp1 ##ₚ pcomp2 ->
      well_formed_comp (Main pcomp1 main) ->
      well_formed_comp (Lib pcomp2) ->
      is_link
        (Main pcomp1 main)
        (Lib pcomp2)
        (link_main_lib pcomp1 pcomp2 main).
    Proof.
      intros.
      apply is_link_main_lib.
      apply link_pre_comp_is_link_pre_comp.
      all: try assumption.
    Qed.

    Lemma link_main_lib_well_formed pcomp1 main pcomp2 :
      pcomp1 ##ₚ pcomp2 ->
      well_formed_comp (Main pcomp1 main) ->
      well_formed_comp (Lib pcomp2) ->
      well_formed_comp
        (link_main_lib pcomp1 pcomp2 main).
    Proof.
      intros H wf_main' wf_lib'.
      apply wf_main.
      apply link_pre_comp_well_formed.
      inversion wf_main'. assumption.
      inversion wf_lib'. assumption. assumption.
      inversion wf_main'.
      eapply (word_restrictions_incr _ _ _ _ Hw_main).
      Unshelve.
      inversion wf_main'. inversion Hwf_pre0.
      inversion wf_lib'. inversion Hwf_pre1.
      do 2 rewrite resolve_imports_dom_eq; rewrite dom_union_L.
      3: transitivity (dom (gset Addr) (segment pcomp2));
          assumption || apply union_subseteq_r.
        all: transitivity (dom (gset Addr) (segment pcomp1));
           assumption || apply union_subseteq_l || reflexivity.
    Qed.

    Lemma link_main_lib_is_context
      pcomp1 main pcomp2
      (Hdisj: pcomp1 ##ₚ pcomp2)
      (wf_main' : well_formed_comp (Main pcomp1 main))
      (wf_lib' : well_formed_comp (Lib pcomp2))
      (no_imps: filter (λ '(_, s), (pcomp1.(exports) ∪ pcomp2.(exports)) !! s = None)
      (pcomp1.(imports) ∪ pcomp2.(imports)) = ∅) :
      is_context
        (Main pcomp1 main)
        (Lib pcomp2)
        (link_main_lib pcomp1 pcomp2 main).
    Proof.
      apply is_context_intro.
      split. apply link_main_lib_is_link; assumption.
      apply is_program_intro.
      apply no_imps.
      apply link_main_lib_well_formed; assumption.
    Qed.

  End LinkExists.
  (*
  (** Results on commutativity and associativity of links *)
  Section LinkCommutativeAssociative.
    Lemma is_link_pre_comp_commutative c1 c2 c3 :
      is_link_pre_comp c1 c2 c3 -> is_link_pre_comp c2 c1 c3.
    Proof.
      intros [ ].
      apply is_link_pre_comp_intro.
      - apply map_disjoint_sym. assumption.
      - apply map_disjoint_sym. assumption.
      - rewrite Hexp. apply map_eq. intros symbol.
        rewrite lookup_merge. rewrite lookup_merge.
        unfold opt_merge_fun.
        destruct (Some_dec (exports pcomp1 !! symbol)) as [ [w1 ep1] | ep1 ];
        destruct (Some_dec (exports pcomp2 !! symbol)) as [ [w2 ep2] | ep2 ];
        rewrite ep1; rewrite ep2; try reflexivity.
        rewrite (map_disjoint_Some_l _ _ _ _ Hexp_disj ep1) in ep2.
        discriminate ep2.
      - intros s a.
        split; rewrite (Himp s a);
        intros [ [sa1|sa2] exp ]; split; auto.
      - rewrite Hms.
        apply map_eq. intros addr.
        apply resolve_imports_spec.
      Search "map_eq".
        resolve_imports_spec
      Search map_disjoint.
      split.

    Lemma is_link_pre_comp_associative c1 c2 c3 cres :
      is_link_pre_comp (c1) (link_pre_comp c2 c3) cres <->
      is_link_pre_comp (link_pre_comp c1 c2) c3 cres.
  End LinkAssociative.*)
End Linking.

Arguments pre_component _ {_ _}.
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

  (* ==== Well formed pre comp ==== *)

  Lemma well_formed_pre_comp_weaken_word_restrictions :
    ∀ {pre_comp : pre_component Symbols},
    well_formed_pre_comp word_restrictions addr_restrictions pre_comp ->
    well_formed_pre_comp word_restrictions' addr_restrictions pre_comp.
  Proof.
    intros pre_comp [ ].
    apply wf_pre_intro.
    all: try assumption.
    intros s a H.
    apply word_restrictions_weaken.
    apply (Hwr_exp s a H).
    intros a w H.
    apply word_restrictions_weaken.
    apply (Hwr_ms a w H).
  Qed.

  Lemma well_formed_pre_comp_weaken_addr_restrictions :
    ∀ {pre_comp : pre_component Symbols},
    well_formed_pre_comp word_restrictions addr_restrictions pre_comp ->
    well_formed_pre_comp word_restrictions addr_restrictions' pre_comp.
  Proof.
    intros pre_comp [ ].
    apply wf_pre_intro.
    all: try assumption.
    apply addr_restrictions_weaken.
    assumption.
  Qed.

  (* ==== Well formed comp ==== *)

  Lemma well_formed_comp_weaken_word_restrictions :
    ∀ {comp : component Symbols},
    well_formed_comp word_restrictions addr_restrictions comp ->
    well_formed_comp word_restrictions' addr_restrictions comp.
  Proof.
    intros pcomp [].
    apply wf_lib. 2: apply wf_main.
    all: try (apply well_formed_pre_comp_weaken_word_restrictions; assumption).
    apply word_restrictions_weaken.
    assumption.
  Qed.

  Lemma well_formed_comp_weaken_addr_restrictions :
    ∀ {comp : component Symbols},
    well_formed_comp word_restrictions addr_restrictions comp ->
    well_formed_comp word_restrictions addr_restrictions' comp.
  Proof.
    intros pcomp [ ].
    apply wf_lib. 2: apply wf_main.
    all: try apply well_formed_pre_comp_weaken_addr_restrictions; assumption.
  Qed.

  (* ==== is_program ==== *)

  Lemma is_program_weaken_word_restrictions :
    ∀ {comp : component Symbols},
    is_program word_restrictions addr_restrictions comp ->
    is_program word_restrictions' addr_restrictions comp.
  Proof.
    intros pcomp [].
    apply is_program_intro.
    assumption.
    apply well_formed_comp_weaken_word_restrictions. assumption.
  Qed.

  Lemma is_program_weaken_addr_restrictions :
    ∀ {comp : component Symbols},
    is_program word_restrictions addr_restrictions comp ->
    is_program word_restrictions addr_restrictions' comp.
  Proof.
    intros pcomp [].
    apply is_program_intro.
    assumption.
    apply well_formed_comp_weaken_addr_restrictions. assumption.
  Qed.

  (* ==== is link ==== *)

  Lemma is_link_weaken_word_restrictions :
    ∀ {comp_a comp_b comp_c : component Symbols},
    is_link word_restrictions addr_restrictions comp_a comp_b comp_c ->
    is_link word_restrictions' addr_restrictions comp_a comp_b comp_c.
  Proof.
    intros comp_a comp_b comp_c [].
    3: apply is_link_main_lib.
    2: apply is_link_lib_main.
    apply is_link_lib_lib.
    all: try assumption.
    all: apply well_formed_comp_weaken_word_restrictions; assumption.
  Qed.

  Lemma is_link_weaken_addr_restrictions :
    ∀ {comp_a comp_b comp_c : component Symbols},
    is_link word_restrictions addr_restrictions comp_a comp_b comp_c ->
    is_link word_restrictions addr_restrictions' comp_a comp_b comp_c.
  Proof.
    intros comp_a comp_b comp_c [].
    3: apply is_link_main_lib.
    2: apply is_link_lib_main.
    apply is_link_lib_lib.
    all: try assumption.
    all: apply well_formed_comp_weaken_addr_restrictions; assumption.
  Qed.

  (* ==== is context ==== *)

  Lemma is_context_weaken_word_restrictions :
    ∀ {comp_a comp_b comp_c : component Symbols},
    is_context word_restrictions addr_restrictions comp_a comp_b comp_c ->
    is_context word_restrictions' addr_restrictions comp_a comp_b comp_c.
  Proof.
    intros comp_a comp_b comp_c [ [is_link' is_prog'] ].
    apply is_context_intro. split.
    apply is_link_weaken_word_restrictions. assumption.
    apply is_program_weaken_word_restrictions. assumption.
  Qed.

  Lemma is_context_weaken_addr_restrictions :
    ∀ {comp_a comp_b comp_c : component Symbols},
    is_context word_restrictions addr_restrictions comp_a comp_b comp_c ->
    is_context word_restrictions addr_restrictions' comp_a comp_b comp_c.
  Proof.
    intros comp_a comp_b comp_c [ [is_link' is_prog'] ].
    apply is_context_intro. split.
    apply is_link_weaken_addr_restrictions. assumption.
    apply is_program_weaken_addr_restrictions. assumption.
  Qed.

End LinkWeakenRestrictions.
