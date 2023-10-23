From iris Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps fin_sets.
From cap_machine Require Import addr_reg.

Section Linking.

  Variable Symbols: Type.
  Variable Symbols_eq_dec: EqDecision Symbols.
  Variable Symbols_countable: Countable Symbols.

  Variable Word: Type.
  Variable can_address_only: Word -> (gset Addr) -> Prop.
  Variable is_main: Word -> Prop.

  Definition imports: Type := gset (Symbols * Addr).
  Definition exports: Type := gmap Symbols Word.
  Definition segment: Type := gmap Addr Word.

  Definition pre_component: Type := (segment * imports * exports).
  Inductive component: Type :=
  | Lib: pre_component -> component
  | Main: pre_component -> Word -> component.

  Inductive well_formed_pre_comp: pre_component -> Prop :=
  | wf_pre_intro:
      forall (ms : gmap Addr Word) imp (exp : gmap Symbols Word)
        (Hdisj: forall s, is_Some (exp !! s) -> ~ exists a, (s, a) ∈ imp)
        (Hexp: forall (s : Symbols) (w : Word), exp !! s = Some w -> can_address_only w (dom ms))
        (Himp: forall s a, (s, a) ∈ imp -> is_Some (ms !! a))
        (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2)
        (Hnpwl: forall (a : Addr) (w : Word), ms !! a = Some w -> can_address_only w (dom ms)),
        well_formed_pre_comp (ms, imp, exp).

  Inductive well_formed_comp: component -> Prop :=
  | wf_lib:
      forall comp
        (Hwf_pre: well_formed_pre_comp comp),
        well_formed_comp (Lib comp)
  | wf_main:
      forall comp w_main
        (Hwf_pre: well_formed_pre_comp comp)
        (Hw_main_addr: can_address_only w_main (dom (comp.1.1)))
        (Hw_main: is_main w_main),
        well_formed_comp (Main comp w_main).

  Inductive is_program: component -> Prop :=
  | is_program_intro:
      forall ms imp exp w_main
        (Hnoimports: imp = ∅)
        (Hwfcomp: well_formed_comp (Main (ms, imp, exp) w_main)),
        is_program (Main (ms,imp, exp) w_main).

  Definition resolve_imports (imp: imports) (exp: exports) (ms: segment) :=
    set_fold (fun '(s, a) m => match exp !! s with Some w => <[a:=w]> m | None => m end) ms imp.

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
        + intro; subst a. eapply H2. exists s.
          eapply elem_of_union. left. eapply elem_of_singleton. reflexivity.
      - apply H0.
        + intros. eapply H1; eapply elem_of_union; right; eauto.
        + intro Y. destruct Y as [sy Hiny].
          eapply H2. exists sy. eapply elem_of_union. right; auto. }
    { intros; destruct (exp !! s) eqn:Hexp.
      - destruct (decide (f = a)).
        + subst f; rewrite lookup_insert.
          right. assert (s0 = s) as ->; eauto.
          eapply elem_of_union in H2. destruct H2.
          * generalize (proj1 (elem_of_singleton _ _) H2). inversion 1; subst; auto.
          * eapply (H1 s0 s a); [eapply elem_of_union_r; auto|eapply elem_of_union_l; eapply elem_of_singleton; eauto].
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
      (exp !! s = None /\ (resolve_imports imp exp ms) !! a = ms !! a) \/ (exists wexp, exp !! s = Some wexp /\ (resolve_imports imp exp ms) !! a = Some wexp).
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

  Inductive link_pre_comp: pre_component -> pre_component -> pre_component -> Prop :=
  | link_pre_comp_intro:
      forall ms1 ms2 ms imp1 imp2 imp exp1 exp2 exp
        (Hms_disj: forall a, is_Some (ms1 !! a) -> is_Some (ms2 !! a) -> False)
        (Hexp: exp = merge (fun o1 o2 => match o1 with | Some _ => o1 | None => o2 end) exp1 exp2)
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

End Linking.
