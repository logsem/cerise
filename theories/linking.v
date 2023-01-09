From Coq Require Import Eqdep_dec.
From iris Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps fin_sets.
From cap_machine Require Import addr_reg machine_base.

Section Linking.

  (** Symbols are used to identify imported/exported word (often capabilites)
      They can be of any type with decidable equality *)
  Variable Symbols: Type.
  Variable Symbols_eq_dec: EqDecision Symbols.
  Variable Symbols_countable: Countable Symbols.

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

  Definition imports_type := (gset (Symbols * Addr)).
  Definition exports_type := (gmap Symbols Word).
  Definition segment_type := (gmap Addr Word).

  Set Implicit Arguments.

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
        (Hdisj: ∀ s, is_Some (pcomp.(exports) !! s) -> ~ ∃ a, (s, a) ∈ pcomp.(imports))
        (Hwr_exp: ∀ s w, pcomp.(exports) !! s = Some w -> word_restrictions w (dom _ pcomp.(segment)))
        (Himp: ∀ s a, (s, a) ∈ pcomp.(imports) -> is_Some (pcomp.(segment) !! a))
        (Himpdisj: ∀ s1 s2 a, (s1, a) ∈ pcomp.(imports) -> (s2, a) ∈ pcomp.(imports) -> s1 = s2)
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
      set_fold (fun '(s, a) m => match exp !! s with
        | Some w => <[a:=w]> m
        | None => m end) ms imp.

    Lemma resolve_imports_spec:
      forall imp exp ms a
        (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2),
        ((~ exists s, (s, a) ∈ imp) ->
        (resolve_imports imp exp ms) !! a = ms !! a) /\
        (forall s, (s, a) ∈ imp ->
        (exp !! s = None /\ (resolve_imports imp exp ms) !! a = ms !! a) \/ (exists wexp, exp !! s = Some wexp /\ (resolve_imports imp exp ms) !! a = Some wexp)).
    Proof.
      intros imp exp ms a. eapply (set_fold_ind_L (fun m imp => (forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2) -> ((~ exists s, (s, a) ∈ imp) -> m !! a = ms !! a) /\ (forall s, (s, a) ∈ imp -> (exp !! s = None /\ m !! a = ms !! a) \/ (exists wexp, exp !! s = Some wexp /\ m !! a = Some wexp))) (fun '(s, a) m => match exp !! s with Some w => <[a:=w]> m | None => m end)); eauto.
      { intros. split; auto. intros.
        eapply elem_of_empty in H0; elim H0; auto. }
      intros. destruct x. split.
      { intros. destruct (exp !! s).
        - rewrite lookup_insert_ne; auto.
          + apply H0.
            * intros. eapply H1; eapply elem_of_union; right; eauto.
            * intro Y. destruct Y as [sy Hiny].
              eapply H2. exists sy. eapply elem_of_union. right; eauto.
          + intro. eapply H2. exists s.
            eapply elem_of_union. left. eapply elem_of_singleton. rewrite H3. reflexivity.
        - apply H0.
          + intros. eapply H1; eapply elem_of_union; right; eauto.
          + intro Y. destruct Y as [sy Hiny].
            eapply H2. exists sy. eapply elem_of_union. right; auto. }
      { intros; destruct (exp !! s) eqn:Hexp.
        - destruct (addr_eq_dec a f) as [eq | neq].
          + rewrite eq. rewrite lookup_insert.
            right. assert (s0 = s) as ->; eauto.
            eapply elem_of_union in H2. destruct H2.
            * generalize (proj1 (elem_of_singleton _ _) H2). inversion 1; subst; auto.
            * eapply (H1 s0 s a); [eapply elem_of_union_r; auto|eapply elem_of_union_l; eapply elem_of_singleton; eauto].
              rewrite eq. reflexivity.
          + rewrite lookup_insert_ne; auto.
            eapply elem_of_union in H2; destruct H2.
            * erewrite elem_of_singleton in H2. inversion H2; congruence.
            * eapply H0; auto.
              intros; eapply H1; eapply elem_of_union; right; eauto.
        - eapply elem_of_union in H2. destruct H2.
          + erewrite elem_of_singleton in H2. inversion H2; subst; clear H2.
            left; split; auto. eapply (proj1 (H0 ltac:(intros; eapply H1; eapply elem_of_union; right; eauto))).
            intro Y. destruct Y as [sy Hsy].
            eapply H. replace s with sy; auto.
            eapply H1; [eapply elem_of_union_r; eauto| eapply elem_of_union_l; eapply elem_of_singleton; eauto].
          + eapply H0; auto.
            intros; eapply H1; eapply elem_of_union_r; eauto. }
    Qed.

    (** Resolve imports of an address in imports is either
        - unchanged if the address are in not in the exports
        - the exported value if it is in exports *)
    Lemma resolve_imports_spec_in:
      forall imp exp ms a s
        (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2),
        (s, a) ∈ imp ->
        (exp !! s = None /\ (resolve_imports imp exp ms) !! a = ms !! a) \/
        (exists wexp, exp !! s = Some wexp /\ (resolve_imports imp exp ms) !! a = Some wexp).
    Proof.
      intros. eapply resolve_imports_spec; eauto.
    Qed.

    (** Resolve imports does not change addresses not in imports *)
    Lemma resolve_imports_spec_not_in:
      forall imp exp ms a
        (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2),
        ((~ exists s, (s, a) ∈ imp) ->
        (resolve_imports imp exp ms) !! a = ms !! a).
    Proof.
      intros. eapply resolve_imports_spec; eauto.
    Qed.

    (** A address from resolve imports contains either:
        - an added export
        - an original memory segment value *)
    Lemma resolve_imports_spec_simple :
      forall imp exp ms a w
        (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2),
        (resolve_imports imp exp ms) !! a = Some w ->
          (∃ s, exp !! s = Some w) \/ (ms !! a = Some w).
    Proof.
      intros imp exp ms a w Himpdisj.
      apply (set_fold_ind_L (
        fun ms' imp' =>
          ms' !! a = Some w ->
          (∃ s, exp !! s = Some w) \/ (ms !! a = Some w))).
      auto.
      intros [s a'] imps' ms' _ Hind.
      destruct (Some_dec (exp !! s)) as [ [w' ex_w] | ex_w ];
      rewrite ex_w.
      - destruct (decide (a' = a)) as [ aa' | aa']. rewrite <- aa'.
        + rewrite lookup_insert. intros ww'. rewrite ww' in ex_w.
          left. exists s. apply ex_w.
        + rewrite (lookup_insert_ne _ _ _ _ aa'). apply Hind.
      - apply Hind.
    Qed.

    (** Resolve imports increases the domain of the memory segment *)
    Lemma resolve_imports_dom :
      forall imp exp ms,
        dom (gset Addr) ms ⊆ dom (gset Addr) (resolve_imports imp exp ms).
    Proof.
      intros imp exp ms a a_in_ms.
      apply (set_fold_ind_L (fun ms imp => a ∈ dom _ ms)).
      - apply a_in_ms.
      - intros. destruct x as [s a0]. destruct (exp !! s).
        apply dom_insert_subseteq. apply H0.
        apply H0.
    Qed.

    Lemma resolve_imports_dom_rev :
      forall imp exp ms a,
        a ∈ dom (gset Addr) (resolve_imports imp exp ms) ->
        a ∈ dom (gset Addr) ms \/ ∃ s, (s,a) ∈ imp.
    Proof.
      intros imp exp ms a.
      apply (set_fold_ind_L (
        fun ms' imp' =>
          a ∈ dom (gset Addr) ms' ->
          a ∈ dom (gset Addr) ms \/ ∃ s, (s,a) ∈ imp')).
      auto.
      intros [s a'] imps' ms' sa'_notin_imps' Hind.
      destruct (Some_dec (exp !! s)) as [ [w' ex_w] | ex_w ];
      rewrite ex_w.
      - destruct (decide (a' = a)) as [ aa' | aa']. rewrite <- aa'.
        + right. exists s. apply elem_of_union_l, elem_of_singleton. reflexivity.
        + rewrite elem_of_dom. rewrite (lookup_insert_ne _ _ _ _ aa').
          rewrite <- elem_of_dom. intros a_in_ms'.
          destruct (Hind a_in_ms') as [H | [s' H]].
          left. apply H. right. exists s'. apply elem_of_union_r, H.
      - intros a_in_ms'. destruct (Hind a_in_ms') as [H | [s' H]].
        left. apply H. right. exists s'. apply elem_of_union_r, H.
    Qed.

    Lemma resolve_imports_dom_eq :
      forall imp exp ms,
        (∀ s a, (s,a) ∈ imp -> is_Some (ms !! a)) ->
        dom (gset Addr) (resolve_imports imp exp ms) = dom (gset Addr) ms.
    Proof.
      intros imp exp ms imp_issome.
      apply (anti_symm _).
      - intros a a_in_ri.
        destruct (resolve_imports_dom_rev imp exp ms a_in_ri) as [a_in_ms | [s sa_in_imps]].
        assumption.
        rewrite elem_of_dom.
        apply (imp_issome s a sa_in_imps).
      - apply resolve_imports_dom.
    Qed.

  End resolve_imports.

  Definition opt_merge_fun {T:Type} (o1 o2: option T) :=
    match o1 with
    | Some _ => o1
    | None => o2
    end.

  Inductive is_link_pre_comp: pre_component -> pre_component -> pre_component -> Prop :=
  | is_link_pre_comp_intro:
      forall pcomp1 pcomp2 pcomp_link
        (Hms_disj: pcomp1.(segment) ##ₘ pcomp2.(segment))
        (Hexp: pcomp_link.(exports) = merge opt_merge_fun pcomp1.(exports) pcomp2.(exports))
        (Himp: ∀ s a, (s, a) ∈ pcomp_link.(imports) <->
               (((s, a) ∈ pcomp1.(imports) \/ (s, a) ∈ pcomp2.(imports)) /\ pcomp_link.(exports) !! s = None))
        (Hms: pcomp_link.(segment) =
              resolve_imports pcomp2.(imports) pcomp_link.(exports) (
              resolve_imports pcomp1.(imports) pcomp_link.(exports) (
                map_union pcomp1.(segment) pcomp2.(segment)))),
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
      rewrite set_eq.
      intros [s addr].
      rewrite (Himp s addr).
      rewrite (Himp0 s addr).
      rewrite H_exp. auto.
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
        let exp := merge opt_merge_fun
                     pcomp1.(exports) pcomp2.(exports) in
        {|
          exports := exp;
          (* memory segment is union of segments, with resolved imports *)
          segment :=
              resolve_imports pcomp2.(imports) exp (
              resolve_imports pcomp1.(imports) exp (
              map_union pcomp1.(segment) pcomp2.(segment)));
          (* imports is union of imports minus symbols is export *)
          imports :=
              filter
              (fun '(s,_) => exp !! s = None)
              (pcomp1.(imports) ∪ pcomp2.(imports));
        |}.

    (** link_pre_comp forms an is_link_pre_comp with its arguments (if segments are disjoint) *)
    Lemma link_pre_comp_is_pre_link_comp
      pcomp1 pcomp2
      (Hms_disj: pcomp1.(segment) ##ₘ pcomp2.(segment)) :
      is_link_pre_comp pcomp1 pcomp2 (link_pre_comp pcomp1 pcomp2).
    Proof.
      apply is_link_pre_comp_intro.
      + apply Hms_disj.
      + reflexivity.
      + intros s a. rewrite elem_of_filter. rewrite elem_of_union.
        split.
        - intros [merg unio]. split. apply unio. apply merg.
        - intros [unio merg]. split. apply merg. apply unio.
      + reflexivity.
    Qed.

    Instance : @DiagNone Word Word Word opt_merge_fun. split. Defined.

    Local Lemma opt_merge_l_or_r
      {exp1 exp2:exports_type} {s w} :
      merge opt_merge_fun exp1 exp2 !! s = Some w ->
      exp1 !! s = Some w \/ exp2 !! s = Some w.
    Proof.
      rewrite lookup_merge. intros m_eq_w.
      destruct (Some_dec (exp1 !! s)) as [[x exp1_s_eq] | exp1_s_eq];
      rewrite exp1_s_eq in m_eq_w; rewrite <- m_eq_w.
      left. apply exp1_s_eq. right. reflexivity.
    Qed.

    Local Lemma resolve_imports_dom_dom1 {ms1 imp1 exp1 ms2 imp2 exp2} :
      dom (gset Addr) ms1 ⊆ dom (gset Addr)
        (resolve_imports imp2 (merge opt_merge_fun exp1 exp2)
          (resolve_imports imp1 (merge opt_merge_fun exp1 exp2) (map_union ms1 ms2))).
    Proof.
      transitivity (dom (gset Addr) (resolve_imports imp1 (merge opt_merge_fun exp1 exp2) (map_union ms1 ms2))).
      transitivity (dom (gset Addr) (map_union ms1 ms2)).
      rewrite dom_union. apply union_subseteq_l.
      all: apply resolve_imports_dom.
    Qed.

    Local Lemma resolve_imports_dom_dom2 {ms1 imp1 exp1 ms2 imp2 exp2} :
      dom (gset Addr) ms2 ⊆ dom (gset Addr)
        (resolve_imports imp2 (merge opt_merge_fun exp1 exp2)
          (resolve_imports imp1 (merge opt_merge_fun exp1 exp2) (map_union ms1 ms2))).
    Proof.
      transitivity (dom (gset Addr) (resolve_imports imp1 (merge opt_merge_fun exp1 exp2) (map_union ms1 ms2))).
      transitivity (dom (gset Addr) (map_union ms1 ms2)).
      rewrite dom_union. apply union_subseteq_r.
      all: apply resolve_imports_dom.
    Qed.

    (** make_link_pre_comp generates a well formed component
        if its arguments are well formed and disjoint *)
    Lemma link_pre_comp_well_formed
      pcomp1 pcomp2
      (wf_1: well_formed_pre_comp pcomp1)
      (wf_2: well_formed_pre_comp pcomp2)
      (Hms_disj: pcomp1.(segment) ##ₘ pcomp2.(segment)) :
      well_formed_pre_comp (link_pre_comp pcomp1 pcomp2).
    Proof.
      inversion wf_1 as [pcomp1' Hdisj1 Hexp1 Himp1 Himpdisj1 Hwr_ms1 Har_ms1].
      inversion wf_2 as [pcomp2' Hdisj2 Hexp2 Himp2 Himpdisj2 Hwr_ms2 Har_ms2].
      apply wf_pre_intro.
      + intros s is_some_s. (* exports are disjoint from import *)
        specialize (Hdisj1 s). specialize (Hdisj2 s).
        rewrite lookup_merge in is_some_s.
        intros [a sa_in_imps].
        apply elem_of_filter in sa_in_imps.
        rewrite lookup_merge in sa_in_imps.
        destruct sa_in_imps as [is_nons_s _].
        rewrite is_nons_s in is_some_s. apply (is_Some_None is_some_s).
      + intros s w exp_s_w. (* export point to addresses in the memory segment *)
        destruct (opt_merge_l_or_r exp_s_w) as [exp1_s | exp2_s].
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 (Hexp1 s w exp1_s)).
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom2 (Hexp2 s w exp2_s)).
      + intros s a sa_in_filter. (* imports are defined addresses *)
        apply elem_of_filter in sa_in_filter.
        destruct sa_in_filter as [_ sa_in_imp].
        apply elem_of_dom.
        apply resolve_imports_dom. apply resolve_imports_dom.
        rewrite dom_union. rewrite elem_of_union.
        apply elem_of_union in sa_in_imp.
        destruct sa_in_imp as [sa_in_imp | sa_in_imp].
        left. rewrite elem_of_dom. apply (Himp1 s a sa_in_imp).
        right. rewrite elem_of_dom. apply (Himp2 s a sa_in_imp).
      + intros s1 s2 a s1_a_in_imps s2_a_in_imps. (* import at most one symbol per address *)
        apply elem_of_filter in s1_a_in_imps, s2_a_in_imps.
        destruct s1_a_in_imps as [_ s1_a_in_imps].
        destruct s2_a_in_imps as [_ s2_a_in_imps].
        apply elem_of_union in s1_a_in_imps, s2_a_in_imps.
        destruct s1_a_in_imps as [s1_a_in_imp1 | s1_a_in_imp2];
        destruct s2_a_in_imps as [s2_a_in_imp1 | s2_a_in_imp2].
        - apply (Himpdisj1 s1 s2 a s1_a_in_imp1 s2_a_in_imp1).
        - apply Himp1 in s1_a_in_imp1.
          apply Himp2 in s2_a_in_imp2.
          destruct s1_a_in_imp1 as [w ms1a].
          rewrite (map_disjoint_Some_l pcomp1.(segment) pcomp2.(segment) _ _ Hms_disj ms1a) in s2_a_in_imp2.
          contradiction (is_Some_None s2_a_in_imp2).
        - apply Himp2 in s1_a_in_imp2.
          apply Himp1 in s2_a_in_imp1.
          destruct s1_a_in_imp2 as [w ms2a].
          rewrite (map_disjoint_Some_r pcomp1.(segment) pcomp2.(segment) _ _ Hms_disj ms2a) in s2_a_in_imp1.
          contradiction (is_Some_None s2_a_in_imp1).
        - apply (Himpdisj2 s1 s2 a s1_a_in_imp2 s2_a_in_imp2).
      + intros a w ms_a_w.
        specialize (Hwr_ms1 a w). specialize (Hwr_ms2 a w).
        destruct (resolve_imports_spec_simple _ _ _ Himpdisj2 ms_a_w) as [[ s exp_s_w ] | ms_a_w'].
        destruct (opt_merge_l_or_r exp_s_w) as [exp1_s | exp2_s].
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 (Hexp1 s w exp1_s)).
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom2 (Hexp2 s w exp2_s)).
        destruct (resolve_imports_spec_simple _ _ _ Himpdisj1 ms_a_w') as [[ s exp_s_w ] | ms_a_w''].
        destruct (opt_merge_l_or_r exp_s_w) as [exp1_s | exp2_s].
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 (Hexp1 s w exp1_s)).
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom2 (Hexp2 s w exp2_s)).
        apply lookup_union_Some in ms_a_w''.
        destruct ms_a_w'' as [ms1_a_w | ms2_a_w].
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 (Hwr_ms1 ms1_a_w)).
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom2 (Hwr_ms2 ms2_a_w)).
        apply Hms_disj.
      + rewrite resolve_imports_dom_eq.
        rewrite resolve_imports_dom_eq.
        assert (Hdom: dom (gset Addr) (map_union (segment pcomp1) (segment pcomp2)) = dom _ (segment pcomp1) ∪ dom _ (segment pcomp2)).
        { apply (anti_symm _); rewrite dom_union; reflexivity. }
        rewrite Hdom. clear Hdom.
        apply addr_restrictions_union_stable; assumption.
        intros s a sa_in_imps1.
        apply elem_of_dom. rewrite dom_union.
        apply elem_of_union_l. rewrite elem_of_dom.
        apply (Himp1 s a sa_in_imps1).
        intros s a sa_in_imps2.
        apply elem_of_dom.
        apply resolve_imports_dom. rewrite dom_union.
        apply elem_of_union_r. rewrite elem_of_dom.
        apply (Himp2 s a sa_in_imps2).
    Qed.

    (** mlink_main_lib forms a link from a main and a lib *)
    Definition link_main_lib main lib main_s :=
      Main (link_pre_comp main lib) main_s.

    Lemma link_main_lib_is_link
      pcomp1 main pcomp2
      (Hms_disj: pcomp1.(segment) ##ₘ pcomp2.(segment))
      (wf_main' : well_formed_comp (Main pcomp1 main))
      (wf_lib' : well_formed_comp (Lib pcomp2)) :
      is_link
        (Main pcomp1 main)
        (Lib pcomp2)
        (link_main_lib pcomp1 pcomp2 main).
    Proof.
      apply is_link_main_lib.
      apply link_pre_comp_is_pre_link_comp.
      all: try assumption.
    Qed.

    Lemma link_main_lib_well_formed
      pcomp1 main pcomp2
      (Hms_disj: pcomp1.(segment) ##ₘ pcomp2.(segment))
      (wf_main' : well_formed_comp (Main pcomp1 main))
      (wf_lib' : well_formed_comp (Lib pcomp2)) :
      well_formed_comp
        (link_main_lib pcomp1 pcomp2 main).
    Proof.
      apply wf_main.
      apply link_pre_comp_well_formed.
      inversion wf_main'. assumption.
      inversion wf_lib'. assumption. assumption.
      inversion wf_main'.
      apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 Hw_main).
    Qed.

    Lemma link_main_lib_is_context
      pcomp1 main pcomp2
      (Hms_disj: pcomp1.(segment) ##ₘ pcomp2.(segment))
      (wf_main' : well_formed_comp (Main pcomp1 main))
      (wf_lib' : well_formed_comp (Lib pcomp2))
      (no_imps: filter (λ '(s, _), merge opt_merge_fun pcomp1.(exports) pcomp2.(exports) !! s = None)
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
End Linking.

(** Simple lemmas used to weaken word_restrictions
    and address_restrictions in is_link and well_formed_xxx *)
Section LinkWeakenRestrictions.
  Context [Symbols: Type].
  Context [Symbols_eq_dec: EqDecision Symbols].
  Context [Symbols_countable: Countable Symbols].

  Variable word_restrictions: Word -> gset Addr -> Prop.
  Variable word_restrictions': Word -> gset Addr -> Prop.
  Variable word_restrictions_weaken:
    ∀ w a, word_restrictions w a -> word_restrictions' w a.

  Variable addr_restrictions: gset Addr -> Prop.
  Variable addr_restrictions': gset Addr -> Prop.
  Variable addr_restrictions_weaken:
    ∀ a, addr_restrictions a -> addr_restrictions' a.

  (* ==== Well formed pre comp ==== *)

  Lemma well_formed_pre_comp_weaken_word_restrictions :
    ∀ pre_comp : pre_component Symbols_countable,
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
    ∀ pre_comp : pre_component Symbols_countable,
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
    ∀ comp : component Symbols_countable,
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
    ∀ comp : component Symbols_countable,
    well_formed_comp word_restrictions addr_restrictions comp ->
    well_formed_comp word_restrictions addr_restrictions' comp.
  Proof.
    intros pcomp [ ].
    apply wf_lib. 2: apply wf_main.
    all: try apply well_formed_pre_comp_weaken_addr_restrictions; assumption.
  Qed.

  (* ==== is_program ==== *)

  Lemma is_program_weaken_word_restrictions :
    ∀ comp : component Symbols_countable,
    is_program word_restrictions addr_restrictions comp ->
    is_program word_restrictions' addr_restrictions comp.
  Proof.
    intros pcomp [].
    apply is_program_intro.
    assumption.
    apply well_formed_comp_weaken_word_restrictions. assumption.
  Qed.

  Lemma is_program_weaken_addr_restrictions :
    ∀ comp : component Symbols_countable,
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
    ∀ comp_a comp_b comp_c : component Symbols_countable,
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
    ∀ comp_a comp_b comp_c : component Symbols_countable,
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
    ∀ comp_a comp_b comp_c : component Symbols_countable,
    is_context word_restrictions addr_restrictions comp_a comp_b comp_c ->
    is_context word_restrictions' addr_restrictions comp_a comp_b comp_c.
  Proof.
    intros comp_a comp_b comp_c [ [is_link' is_prog'] ].
    apply is_context_intro. split.
    apply is_link_weaken_word_restrictions. assumption.
    apply is_program_weaken_word_restrictions. assumption.
  Qed.

  Lemma is_context_weaken_addr_restrictions :
    ∀ comp_a comp_b comp_c : component Symbols_countable,
    is_context word_restrictions addr_restrictions comp_a comp_b comp_c ->
    is_context word_restrictions addr_restrictions' comp_a comp_b comp_c.
  Proof.
    intros comp_a comp_b comp_c [ [is_link' is_prog'] ].
    apply is_context_intro. split.
    apply is_link_weaken_addr_restrictions. assumption.
    apply is_program_weaken_addr_restrictions. assumption.
  Qed.

End LinkWeakenRestrictions.
