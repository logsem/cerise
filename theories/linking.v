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

  Definition can_address_only (w: Word) (addrs: gset Addr): Prop :=
    match w with
    | WInt _ => True
    | WCap _ b e _ =>
      forall a, (b <= a < e)%a -> a ∈ addrs
    end.

  Variable pwl: Word -> bool.
  Variable is_global: Word -> bool.

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
        (Hexp: forall s w, exp !! s = Some w -> can_address_only w (dom _ ms) /\ pwl w = false /\ is_global w = true)
        (Himp: forall s a, (s, a) ∈ imp -> is_Some (ms !! a))
        (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2)
        (Hnpwl: forall a w, ms !! a = Some w -> can_address_only w (dom _ ms) /\ pwl w = false /\ is_global w = true)
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
        (Hw_main: can_address_only w_main (dom _ (comp.1.1)) /\ pwl w_main = false /\ is_global w_main = true),
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

  Lemma resolve_imports_spec_in:
    forall imp exp ms a s
      (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2),
      (s, a) ∈ imp ->
      (exp !! s = None /\ (resolve_imports imp exp ms) !! a = ms !! a) \/
      (exists wexp, exp !! s = Some wexp /\ (resolve_imports imp exp ms) !! a = Some wexp).
  Proof.
    intros. eapply resolve_imports_spec; eauto.
  Qed.

  Lemma resolve_imports_spec_not_in:
    forall imp exp ms a
      (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2),
      ((~ exists s, (s, a) ∈ imp) ->
       (resolve_imports imp exp ms) !! a = ms !! a).
  Proof.
    intros. eapply resolve_imports_spec; eauto.
  Qed.

  (** Resolve imports increases the domain of the memory segment *)
  Lemma resolve_imports_dom :
    forall imp exp ms a,
      a ∈ dom (gset Addr) ms -> a ∈ dom (gset Addr) (resolve_imports imp exp ms).
  Proof.
    intros.
    apply (set_fold_ind_L (fun ms imp => a ∈ dom _ ms)).
    - apply H.
    - intros. destruct x as [s a0]. destruct (exp !! s).
      apply dom_insert_subseteq. apply H1.
      apply H1.
  Qed.

  Definition opt_merge_fun {T:Type} (o1 o2: option T) :=
    match o1 with
    | Some _ => o1
    | None => o2
    end.

  Inductive link_pre_comp: pre_component -> pre_component -> pre_component -> Prop :=
  | link_pre_comp_intro:
      forall ms1 ms2 ms imp1 imp2 imp exp1 exp2 exp
        (Hms_disj: forall a, is_Some (ms1 !! a) -> is_Some (ms2 !! a) -> False)
        (Hexp: exp = merge opt_merge_fun exp1 exp2)
        (Himp: forall s a, (s, a) ∈ imp <-> (((s, a) ∈ imp1 \/ (s, a) ∈ imp2) /\ exp !! s = None))
        (Hms: ms = resolve_imports imp2 exp (resolve_imports imp1 exp (map_union ms1 ms2))),
        link_pre_comp (ms1, imp1, exp1) (ms2, imp2, exp2) (ms, imp, exp).

  Definition make_link_pre : pre_component -> pre_component -> pre_component :=
    fun '(ms1, imp1, exp1) '(ms2, imp2, exp2) =>
      let exp := merge opt_merge_fun exp1 exp2 in
      let seg := resolve_imports imp2 exp (resolve_imports imp1 exp (map_union ms1 ms2)) in
      let inp := filter (fun '(s,_) => exp !! s = None) (imp1 ∪ imp2) in
      (seg, inp, exp).

  Lemma make_link_pre_is_pre_link
    ms1 imp1 exp1 ms2 imp2 exp2
    (Hms_disj: forall a, is_Some (ms1 !! a) -> is_Some (ms2 !! a) -> False) :
    link_pre_comp (ms1, imp1, exp1) (ms2, imp2, exp2) (make_link_pre (ms1, imp1, exp1) (ms2, imp2, exp2)).
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
End Linking.
