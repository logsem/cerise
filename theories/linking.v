From Coq Require Import Eqdep_dec.
From iris Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps fin_sets.
From cap_machine Require Import addr_reg machine_base.

Lemma z_of_eq a1 a2 :
  z_of a1 = z_of a2 ->
  a1 = a2.
Proof.
  destruct a1, a2; cbn. intros ->.
  repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Global Instance addr_eq_dec: EqDecision Addr.
intros x y. destruct x,y. destruct (Z_eq_dec z z0).
- left. eapply z_of_eq; eauto.
- right. inversion 1. simplify_eq.
Defined.

Section Linking.

  Variable b_stk: Addr.
  Variable e_stk: Addr.
  Variable stk_pos: (b_stk < e_stk)%a.

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

  (* * any capability contained by w must point to addresses in addrs
  Definition can_address_only (w: Word) (addrs: gset Addr): Prop :=
    match w with
    | WInt _ => True
    | WCap _ b e _ =>
      forall a, (b <= a < e)%a -> a ∈ addrs
    end. *)

  Definition imports: Type := gset (Symbols * Addr).
  Definition exports: Type := gmap Symbols Word.
  Definition segment: Type := gmap Addr Word.

  Definition pre_component: Type := (segment * imports * exports).
  Inductive component: Type :=
  | Lib: pre_component -> component
  | Main: pre_component -> Word -> component.

  Inductive well_formed_pre_comp: pre_component -> Prop :=
  | wf_pre_intro:
      forall ms imp exp
        (Hdisj: forall s, is_Some (exp !! s) -> ~ exists a, (s, a) ∈ imp)
        (Hwr_exp: forall s w, exp !! s = Some w -> word_restrictions w (dom _ ms))
        (Himp: forall s a, (s, a) ∈ imp -> is_Some (ms !! a))
        (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2)
        (Hwr_ms: forall a w, ms !! a = Some w -> word_restrictions w (dom _ ms))
        (Hdisjstk: forall a, a ∈ dom (gset _) ms -> (e_stk <= a)%a), (* \/ (a < b_stk)%a *)
        well_formed_pre_comp (ms, imp, exp).

  Inductive well_formed_comp: component -> Prop :=
  | wf_lib:
      forall comp
        (Hwf_pre: well_formed_pre_comp comp),
        well_formed_comp (Lib comp)
  | wf_main:
      forall comp w_main
        (Hwf_pre: well_formed_pre_comp comp)
        (Hw_main: word_restrictions w_main (dom _ (comp.1.1))),
        well_formed_comp (Main comp w_main).

  Inductive is_program: component -> Prop :=
  | is_program_intro:
      forall ms imp exp w_main
        (Hnoimports: imp = ∅)
        (Hwfcomp: well_formed_comp (Main (ms, imp, exp) w_main)),
        is_program (Main (ms,imp, exp) w_main).

  Definition resolve_imports (imp: imports) (exp: exports) (ms: segment) :=
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

  Definition opt_merge_fun {T:Type} (o1 o2: option T) :=
    match o1 with
    | Some _ => o1
    | None => o2
    end.

  Inductive link_pre_comp: pre_component -> pre_component -> pre_component -> Prop :=
  | link_pre_comp_intro:
      forall ms1 ms2 ms imp1 imp2 imp exp1 exp2 exp
        (Hms_disj: ms1 ##ₘ ms2)
        (Hexp: exp = merge opt_merge_fun exp1 exp2)
        (Himp: forall s a, (s, a) ∈ imp <-> (((s, a) ∈ imp1 \/ (s, a) ∈ imp2) /\ exp !! s = None))
        (Hms: ms = resolve_imports imp2 exp (resolve_imports imp1 exp (map_union ms1 ms2))),
        link_pre_comp (ms1, imp1, exp1) (ms2, imp2, exp2) (ms, imp, exp).

  Inductive link: component -> component -> component -> Prop :=
  | link_lib_lib:
      forall comp1 comp2 comp
        (Hlink: link_pre_comp comp1 comp2 comp)
        (Hwf_l: well_formed_comp (Lib comp1))
        (Hwf_r: well_formed_comp (Lib comp2)),
        link (Lib comp1) (Lib comp2) (Lib comp)
  | link_lib_main:
      forall comp1 comp2 comp w_main
        (Hlink: link_pre_comp comp1 comp2 comp)
        (Hwf_l: well_formed_comp (Lib comp1))
        (Hwf_r: well_formed_comp (Main comp2 w_main)),
        link (Lib comp1) (Main comp2 w_main) (Main comp w_main)
  | link_main_lib:
      forall comp1 comp2 comp w_main
        (Hlink: link_pre_comp comp1 comp2 comp)
        (Hwf_l: well_formed_comp (Main comp1 w_main))
        (Hwf_r: well_formed_comp (Lib comp2)),
        link (Main comp1 w_main) (Lib comp2) (Main comp w_main).

  Inductive is_context (c comp p: component): Prop :=
  | is_context_intro:
      forall (His_program: link c comp p /\ is_program p),
      is_context c comp p.

  (** Lemmas about the uniqueness of [c] in [link a b c] and variations thereof *)
  Section LinkUnique.
    Lemma link_pre_comp_unique {c_left c_right c1 c2} :
      link_pre_comp c_left c_right c1 ->
      link_pre_comp c_left c_right c2 ->
      c1 = c2.
    Proof.
      intros a b.
      destruct c_left as [[msl impl] expl].
      destruct c_right as [[msr impr] expr].
      destruct c1 as [[ms1 imp1] exp1].
      destruct c2 as [[ms2 imp2] exp2].
      inversion a.
      inversion b.
      assert (H_exp: exp1 = exp2).
      { rewrite Hexp. rewrite Hexp0. reflexivity. }
      apply pair_equal_spec. split.
      apply pair_equal_spec. split.
      rewrite Hms. rewrite Hms0.
      rewrite H_exp. reflexivity.
      rewrite set_eq.
      intros [s addr].
      rewrite (Himp s addr).
      rewrite (Himp0 s addr).
      rewrite H_exp. auto.
      apply H_exp.
    Qed.

    Lemma link_unique {c_left c_right c1 c2} :
      link c_left c_right c1 ->
      link c_left c_right c2 ->
      c1 = c2.
    Proof.
      intros a b.
      destruct c_left as [[[msl impl] expl] | [[[msl impl] expl] mainl]];
      destruct c_right as [[[msr impr] expr] | [[[msr impr] expr] mainr]];
      destruct c1 as [[[ms1 imp1] exp1] | [[[ms1 imp1] exp1] main1]];
      destruct c2 as [[[ms2 imp2] exp2] | [[[ms2 imp2] exp2] main2]].
      all: inversion a.
      all: inversion b.
      all: rewrite (link_pre_comp_unique Hlink Hlink0).
      reflexivity.
      all: f_equal; rewrite <- H4, H9; reflexivity.
    Qed.

    Lemma context_unique {c_left c_right c1 c2} :
      is_context c_left c_right c1 ->
      is_context c_left c_right c2 ->
      c1 = c2.
    Proof.
      intros [[link1 _]] [[link2 _]].
      apply (link_unique link1 link2).
    Qed.
  End LinkUnique.

  (** Functions to build a linked component and lemmas about their correctness *)
  Section LinkExists.

    (** Creates link candidate for two precomponents *)
    Definition make_link_pre_comp : pre_component -> pre_component -> pre_component :=
      fun '(ms1, imp1, exp1) '(ms2, imp2, exp2) =>
        (* exports is union of exports *)
        let exp := merge opt_merge_fun exp1 exp2 in
        (* memory segment is union of segments, with resolved imports *)
        let seg := resolve_imports imp2 exp (resolve_imports imp1 exp (map_union ms1 ms2)) in
        (* imports is union of imports minus symbols is export *)
        let inp := filter (fun '(s,_) => exp !! s = None) (imp1 ∪ imp2) in
        (seg, inp, exp).

    (** make_link_pre_comp forms a link_pre_comp with its arguments (if segments are disjoint) *)
    Lemma make_link_pre_comp_is_pre_link_comp
      ms1 imp1 exp1 ms2 imp2 exp2
      (Hms_disj: ms1 ##ₘ ms2) :
      link_pre_comp (ms1, imp1, exp1) (ms2, imp2, exp2) (make_link_pre_comp (ms1, imp1, exp1) (ms2, imp2, exp2)).
    Proof.
      apply link_pre_comp_intro.
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
      {exp1 exp2:exports} {s w} :
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
    Lemma make_link_pre_comp_well_formed
      ms1 imp1 exp1 ms2 imp2 exp2
      (wf_1: well_formed_pre_comp (ms1, imp1, exp1))
      (wf_2: well_formed_pre_comp (ms2, imp2, exp2))
      (Hms_disj: ms1 ##ₘ ms2) :
      well_formed_pre_comp (make_link_pre_comp (ms1, imp1, exp1) (ms2, imp2, exp2)).
    Proof.
      inversion wf_1 as [ms1' imp1' exp1' Hdisj1 Hexp1 Himp1 Himpdisj1 Hnpwl1 Hdisjstk1].
      inversion wf_2 as [ms2' imp2' exp2' Hdisj2 Hexp2 Himp2 Himpdisj2 Hnpwl2 Hdisjstk2].
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
          rewrite (map_disjoint_Some_l ms1 ms2 _ _ Hms_disj ms1a) in s2_a_in_imp2.
          contradiction (is_Some_None s2_a_in_imp2).
        - apply Himp2 in s1_a_in_imp2.
          apply Himp1 in s2_a_in_imp1.
          destruct s1_a_in_imp2 as [w ms2a].
          rewrite (map_disjoint_Some_r ms1 ms2 _ _ Hms_disj ms2a) in s2_a_in_imp1.
          contradiction (is_Some_None s2_a_in_imp1).
        - apply (Himpdisj2 s1 s2 a s1_a_in_imp2 s2_a_in_imp2).
      + intros a w ms_a_w. (* HERE *)
        specialize (Hnpwl1 a w). specialize (Hnpwl2 a w).
        destruct (resolve_imports_spec_simple _ _ _ _ _ Himpdisj2 ms_a_w) as [[ s exp_s_w ] | ms_a_w'].
        destruct (opt_merge_l_or_r exp_s_w) as [exp1_s | exp2_s].
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 (Hexp1 s w exp1_s)).
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom2 (Hexp2 s w exp2_s)).
        destruct (resolve_imports_spec_simple _ _ _ _ _ Himpdisj1 ms_a_w') as [[ s exp_s_w ] | ms_a_w''].
        destruct (opt_merge_l_or_r exp_s_w) as [exp1_s | exp2_s].
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 (Hexp1 s w exp1_s)).
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom2 (Hexp2 s w exp2_s)).
        apply lookup_union_Some in ms_a_w''.
        destruct ms_a_w'' as [ms1_a_w | ms2_a_w].
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 (Hnpwl1 ms1_a_w)).
        apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom2 (Hnpwl2 ms2_a_w)).
        apply Hms_disj.
      + intros a a_in_ri.
        destruct (resolve_imports_dom_rev _ _ _ a a_in_ri) as [a_in_ri' | [s sa_in_imp2]].
        destruct (resolve_imports_dom_rev _ _ _ a a_in_ri') as [a_in_ri'' | [s sa_in_imp1]].
        apply dom_union, elem_of_union in a_in_ri''.
        destruct a_in_ri'' as [a_in_ms1 | a_in_ms2].
        eauto using Hdisjstk1. eauto using Hdisjstk2.
        specialize (Himp1 _ _ sa_in_imp1).
        apply elem_of_dom in Himp1.
        eauto using Hdisjstk1.
        specialize (Himp2 _ _ sa_in_imp2).
        apply elem_of_dom in Himp2.
        eauto using Hdisjstk2.
    Qed.

    Definition make_link_main_lib main lib main_s :=
      Main (make_link_pre_comp main lib) main_s.

    Lemma make_link_main_lib_is_link
      ms1 imp1 exp1 main ms2 imp2 exp2
      (Hms_disj: ms1 ##ₘ ms2)
      (wf_main' : well_formed_comp (Main (ms1, imp1, exp1) main))
      (wf_lib' : well_formed_comp (Lib (ms2, imp2, exp2))) :
      link
        (Main (ms1, imp1, exp1) main)
        (Lib (ms2, imp2, exp2))
        (make_link_main_lib (ms1, imp1, exp1) (ms2, imp2, exp2) main).
    Proof.
      apply link_main_lib.
      apply make_link_pre_comp_is_pre_link_comp.
      all: try assumption.
    Qed.

    Lemma make_link_main_lib_well_formed
      ms1 imp1 exp1 main ms2 imp2 exp2
      (Hms_disj: ms1 ##ₘ ms2)
      (wf_main' : well_formed_comp (Main (ms1, imp1, exp1) main))
      (wf_lib' : well_formed_comp (Lib (ms2, imp2, exp2))) :
      well_formed_comp
        (make_link_main_lib (ms1, imp1, exp1) (ms2, imp2, exp2) main).
    Proof.
      apply wf_main.
      apply make_link_pre_comp_well_formed.
      inversion wf_main'. assumption.
      inversion wf_lib'. assumption. assumption.
      inversion wf_main'.
      apply (word_restrictions_incr _ _ _ resolve_imports_dom_dom1 Hw_main).
    Qed.

  End LinkExists.
End Linking.
