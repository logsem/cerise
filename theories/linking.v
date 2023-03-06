From Coq Require Import Eqdep_dec.
From iris Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps fin_sets.
From cap_machine Require Import stdpp_img stdpp_comp addr_reg machine_base.

Global Instance g_img `{FinMap K M, Countable A} : Img (M A) (gset A) :=
fin_map_img K A (M A) (gset A).


(** Definition of components, condition for well_formedness and linking,
    the linking process, and properties (associativity, commutativity) *)
Section Linking.

  (** Symbols are used to identify imported/exported word (often capabilites)
      They can be of any type with decidable equality *)
  Context {Symbols: Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  (** Word Restrictions, A predicate that must hold on all word of our segments
      Typically that if it is a capability, it only points into the segment
      (given as second argument)
      This should remain true if the segment increases *)
  Variable WR: Word -> gset Addr -> Prop.
  Context {WR_stable: ∀ w, Proper ((⊆) ==> impl) (WR w)}.

  (** Various examples of WR predicates *)
  Section WR.
    (** Example of a WR, ensures all capabilites point
        into the given segment *)
    Example can_address_only word (addr_set: gset Addr) :=
      match word with
      | WSealable (SCap _ b e _)
      | WSealed _ (SCap _ b e _) => ∀ a, (b <= a < e)%a -> a ∈ addr_set
      | WSealable (SSealRange _ _ _ _)
      | WSealed _ (SSealRange _ _ _ _)
      | WInt _ => True
      end.
    #[global] Instance can_address_only_subseteq_stable w: Proper ((⊆) ==> impl) (can_address_only w).
    Proof.
      intros dom1 dom2 dom1_dom2. unfold impl.
      destruct w; try auto;
      [ destruct sb | destruct s]; try auto.
      all: intros ca_dom1 addr addr_in_be;
      apply dom1_dom2; apply (ca_dom1 addr addr_in_be).
    Qed.

    (** Example of a WR, ensures all capabilites point
        into the given segment *)
    Example can_address_only_no_seals word (addr_set: gset Addr) :=
        match word with
        | WSealable (SCap _ b e _) => ∀ a, (b <= a < e)%a -> a ∈ addr_set
        | WSealed _ (SCap _ _ _ _)
        | WSealable (SSealRange _ _ _ _)
        | WSealed _ (SSealRange _ _ _ _) => False
        | WInt _ => True
        end.
    #[global] Instance can_address_only_no_seals_subseteq_stable w: Proper ((⊆) ==> impl) (can_address_only_no_seals w).
    Proof.
      intros dom1 dom2 dom1_dom2. unfold impl.
      destruct w; auto.
      destruct sb; [intros ca_dom1 addr addr_in_be | auto];
      apply dom1_dom2; apply (ca_dom1 addr addr_in_be).
    Qed.

    Lemma can_address_only_no_seals_weaken {w a} :
      can_address_only_no_seals w a -> can_address_only w a.
    Proof.
      unfold can_address_only_no_seals, can_address_only.
      destruct w; [auto | destruct sb | destruct s]; auto.
      intros H. contradiction H.
    Qed.

    (** Another WR, not a seal *)
    Example is_not_seal word :=
      match word with
      | WInt _
      | WSealable (SCap _ _ _ _) => True
      | WSealed _ (SCap _ _ _ _)
      | WSealable (SSealRange _ _ _ _)
      | WSealed _ (SSealRange _ _ _ _) => False
      end.

    (** Another possible WR, only allow words/intructions *)
    Example is_word word := is_z word = true.

    (** Another example, no constraints on words at all *)
    Example unconstrained_word: Word -> gset Addr -> Prop := fun _ _ => True.

    Lemma any_implies_unconstrained_word {P}:
      ∀ w a, P w a -> unconstrained_word w a.
    Proof. intros. unfold unconstrained_word. auto. Qed.
  End WR.

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

    exports : exports_type;
    (** Segment exports, a map symbols -> word (often capabilities) *)
  }.

  Section alt_def.
    Record component_alt := {
      segment_alt : gmap Addr (Word + Symbols);
      exports_alt : exports_type;
    }.

    Definition alt2comp alt := {|
      segment := omap (fun v => match v with
        | inl w => Some w
        | _ => None
        end) (segment_alt alt);
      imports := omap (fun v => match v with
        | inr s => Some s
        | _ => None
        end) (segment_alt alt);
      exports := exports_alt alt;
    |}.

    Definition comp2alt comp := {|
      segment_alt := fmap inr (imports comp) ∪ fmap inl (segment comp);
      exports_alt := exports comp
    |}.

    Lemma comp2alt2comp {c} : comp2alt (alt2comp c) = c.
    Proof.
      destruct c as [s e]. unfold comp2alt, alt2comp. simpl. f_equal.
      rewrite !map_fmap_omap. apply map_eq. intros a.
      destruct (s!!a) as [[w|symb] |] eqn:Ha.
      by rewrite lookup_union_r lookup_omap Ha /=.
      by rewrite lookup_union_l lookup_omap Ha /=.
      by rewrite lookup_union_None !lookup_omap !Ha /=.
    Qed.
  End alt_def.

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

  (* Notation img x := (img x : gset _). *)

  Inductive well_formed_comp (comp : component) : Prop :=
  | wf_comp_intro: forall
      (* the exported symbols and the imported symbols are disjoint *)
      (Hdisj: dom comp.(exports) ## img comp.(imports))
      (* We import only to addresses in our segment *)
      (Himp: dom comp.(imports) ⊆ dom comp.(segment))
      (* Word restriction on segment and exports *)
      (Hwr_exp: ∀ w, w ∈ img comp.(exports) -> WR w (dom comp.(segment)))
      (Hwr_ms: ∀ w, w ∈ img comp.(segment) -> WR w (dom comp.(segment))),
      well_formed_comp comp.

  (** A program is a segment without imports and some register allocations *)
  Inductive is_program (comp:component) (regs:Reg) : Prop :=
  | is_program_intro: forall
      (Hwf_comp: well_formed_comp comp)
      (Hno_imports: comp.(imports) = ∅)
      (Hwr_regs: ∀ w, w ∈ img regs -> WR w (dom comp.(segment)))
      (Hall_regs: ∀ r, is_Some (regs !! r)),
      is_program comp regs.

  (** To form well defined links, our components must be well-formed
      and have separates memory segments and exported symbols *)
  Inductive can_link (comp_l comp_r : component) : Prop :=
  | can_link_intro: forall
      (Hwf_l: well_formed_comp comp_l)
      (Hwf_r: well_formed_comp comp_r)
      (Hms_disj: comp_l.(segment) ##ₘ comp_r.(segment))
      (Hexp_disj: comp_l.(exports) ##ₘ comp_r.(exports)),
      can_link comp_l comp_r.

  Definition resolve_imports (imp: imports_type) (exp: exports_type) (ms: segment_type) :=
    map_compose exp imp ∪ ms.

  (** Creates link for two components
      the arguments should satisfy can_link *)
  Definition link comp_l comp_r :=
    (* exports is union of exports *)
    let exp := comp_l.(exports) ∪ comp_r.(exports) in
    {|
      exports := exp;
      (* memory segment is union of segments, with resolved imports *)
      segment :=
        resolve_imports (imports comp_l) (exports comp_r) (segment comp_l) ∪
        resolve_imports (imports comp_r) (exports comp_l) (segment comp_r);
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
      (Hwr_regs: ∀ w, w ∈ img regs -> WR w (dom context.(segment)))
      (Hall_regs: ∀ r, is_Some (regs !! r))
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
    apply map_disjoint_dom. apply map_disjoint_dom in Hms_disj.
    intros a Hal Har. apply (Hms_disj a (Himp a Hal) (Himp0 a Har)).
  Qed.

  (** Lemmas about resolve_imports: specification and utilities *)
  Section resolve_imports.
    Lemma resolve_imports_spec imp exp ms a :
      resolve_imports imp exp ms !! a =
        match imp !! a with
        | None => ms !! a
        | Some s =>
            match exp !! s with
            | None => ms !! a
            | Some wexp => Some wexp
            end
        end.
    Proof.
      unfold resolve_imports.
      destruct (imp !! a) as [s|] eqn:Himp.
      destruct (exp !! s) as [w|] eqn:Hexp.
      apply lookup_union_Some_l. rewrite map_compose_lookup Himp /= Hexp. reflexivity.
      all: apply lookup_union_r.
      apply (map_compose_lookup_None_2r _ _ _ _ Himp Hexp).
      by apply map_compose_lookup_None_2l.
    Qed.

    Lemma resolve_imports_dom {exp imp ms} :
      dom imp ⊆ dom ms ->
      dom (resolve_imports imp exp ms) = dom ms.
    Proof.
      intros Hd. rewrite dom_union_L.
      specialize (map_compose_dom_subseteq exp imp) as Hc.
      set_solver.
    Qed.

    Lemma resolve_imports_imports_empty exp ms : resolve_imports ∅ exp ms = ms.
    Proof. unfold resolve_imports. rewrite map_compose_empty_r. apply map_empty_union. Qed.
    Lemma resolve_imports_exports_empty imp ms : resolve_imports imp ∅ ms = ms.
    Proof. unfold resolve_imports. rewrite map_compose_empty_l. apply map_empty_union. Qed.
  End resolve_imports.

  (** well_formedness of [link a b] and usefull lemmas *)
  Section LinkWellFormed.
    Lemma link_img x y :
      img (segment (x ⋈ y)) ⊆
      img (segment x) ∪ img (segment y) ∪
      img (exports x) ∪ img (exports y).
    Proof.
      unfold link, resolve_imports. simpl.
      specialize (map_compose_img_subseteq (D:=gset _) (exports y) (imports x)) as Hm1.
      specialize (map_compose_img_subseteq (D:=gset _) (exports x) (imports y)) as Hm2.
      transitivity (img (map_compose (exports y) (imports x)) ∪ img (segment x) ∪
                    img (map_compose (exports x) (imports y)) ∪ img (segment y)).
      intros w Hw. apply (img_union_subseteq _ _ w) in Hw.
      apply elem_of_union in Hw as [Hw|Hw]; apply (img_union_subseteq _ _ w) in Hw.
      all: set_solver.
    Qed.

    Lemma link_segment_dom {a b}:
      dom (imports a) ⊆ dom (segment a) ->
      dom (imports b) ⊆ dom (segment b) ->
      dom (segment a) ∪ dom (segment b) = dom (segment (a ⋈ b)).
    Proof.
      intros Ha Hb. unfold link. simpl.
      by rewrite dom_union_L !resolve_imports_dom.
    Qed.

    Lemma link_segment_dom_subseteq_l a b : dom (segment a) ⊆ dom (segment (a ⋈ b)).
    Proof. unfold link, resolve_imports. simpl. set_solver. Qed.

    Lemma link_segment_dom_subseteq_r a b : dom (segment b) ⊆ dom (segment (a ⋈ b)).
    Proof. unfold link, resolve_imports. simpl. set_solver. Qed.

    (** link generates a well formed component
        if its arguments are well formed and disjoint *)
    Lemma link_well_formed {x y} : x ##ₗ y -> well_formed_comp (x ⋈ y).
    Proof.
      intros [].
      inversion Hwf_l as [Hdisj1 Himp1 Hwr_exp1 Hwr_ms1].
      inversion Hwf_r as [Hdisj2 Himp2 Hwr_exp2 Hwr_ms2].
      specialize (link_segment_dom_subseteq_l x y) as Hseg1.
      specialize (link_segment_dom_subseteq_r x y) as Hseg2.
      apply wf_comp_intro.
      + intros s s_in_exp s_in_imps. (* exports are disjoint from import *)
        apply elem_of_dom in s_in_exp.
        apply elem_of_img in s_in_imps.
        destruct s_in_imps as [a s_in_imps].
        apply map_filter_lookup_Some in s_in_imps.
        destruct s_in_imps as [_ is_none_s].
        rewrite is_none_s in s_in_exp.
        apply (is_Some_None s_in_exp).
      + transitivity (dom (x.(imports) ∪ y.(imports))).
        apply dom_filter_subseteq.
        rewrite dom_union_L union_subseteq. split.
        by transitivity (dom (segment x)).
        by transitivity (dom (segment y)).
      + intros w exp_w. (* exported word respect word restrictions *)
        apply elem_of_img in exp_w. destruct exp_w as [s exp_s_w].
        apply lookup_union_Some in exp_s_w. 2: assumption.
        destruct exp_s_w as [exp_s | exp_s];
        apply (elem_of_img_2 (D:=gset _)) in exp_s.
        exact (WR_stable _ _ _ Hseg1 (Hwr_exp1 w exp_s)).
        exact (WR_stable _ _ _ Hseg2 (Hwr_exp2 w exp_s)).
      + intros w ms_w.
        apply link_img in ms_w.
        repeat apply elem_of_union in ms_w as [ms_w | ms_w].
        exact (WR_stable _ _ _ Hseg1 (Hwr_ms1 w ms_w)).
        exact (WR_stable _ _ _ Hseg2 (Hwr_ms2 w ms_w)).
        exact (WR_stable _ _ _ Hseg1 (Hwr_exp1 w ms_w)).
        exact (WR_stable _ _ _ Hseg2 (Hwr_exp2 w ms_w)).
    Qed.

    Lemma is_context_is_program {context lib regs}:
      is_context context lib regs ->
      is_program (context ⋈ lib) regs.
    Proof.
      intros [ ]. apply is_program_intro.
      - by apply link_well_formed.
      - apply map_eq. intros a.
        rewrite lookup_empty.
        apply map_filter_lookup_None.
        right. intros s a_imps.
        apply lookup_union_Some in a_imps.
        intros none.
        apply lookup_union_None in none.
        destruct none as [n_l n_r].
        destruct a_imps as [a_l | a_r].
        apply (elem_of_img_2 (D:=gset _)) in a_l.
        specialize (Hno_imps_r s a_l).
        apply elem_of_dom in Hno_imps_r.
        rewrite n_r in Hno_imps_r.
        contradiction (is_Some_None Hno_imps_r).
        apply (elem_of_img_2 (D:=gset _)) in a_r.
        specialize (Hno_imps_l s a_r).
        apply elem_of_dom in Hno_imps_l.
        rewrite n_l in Hno_imps_l.
        contradiction (is_Some_None Hno_imps_l).
        apply can_link_disjoint_impls. assumption.
      - intros w rw.
        inversion Hcan_link.
        apply (WR_stable _ _ _ (link_segment_dom_subseteq_l _ _)).
        exact (Hwr_regs w rw).
      - apply Hall_regs.
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
      - apply map_union_comm. rewrite map_disjoint_dom !resolve_imports_dom.
        by rewrite -map_disjoint_dom.
        by inversion Hwf_r. by inversion Hwf_l.
      - rewrite map_union_comm.
        f_equal. apply map_union_comm.
        all: assumption.
      - apply map_union_comm; assumption.
    Qed.

    Lemma link_segment_lookup_l {x y a} :
      x ##ₗ y -> a ∈ dom (segment x) ->
      segment (x ⋈ y) !! a = resolve_imports x.(imports) y.(exports) x.(segment) !! a.
    Proof.
      intros [_ []] Ha.
      apply lookup_union_l.
      rewrite -not_elem_of_dom resolve_imports_dom.
      intros Hb. rewrite map_disjoint_dom in Hms_disj.
      apply (Hms_disj a Ha Hb). done.
    Qed.

    Lemma link_img_l {x y a w} :
      x ##ₗ y -> a ∈ dom (segment x) ->
      segment (x ⋈ y) !! a = Some w ->
      w ∈ img (exports y) \/ segment x !! a = Some w.
    Proof.
      intros Hsep Hdom Haddr.
      rewrite (link_segment_lookup_l Hsep Hdom) in Haddr.
      rewrite resolve_imports_spec in Haddr.
      destruct (imports x !! a) as [s|].
      destruct (exports y !! s) as [wexp|] eqn:Hb.
      left. apply elem_of_img. exists s. by rewrite Hb.
      all: by right.
    Qed.

    Lemma link_segment_lookup_r {x y a} :
      x ##ₗ y -> a ∈ dom (segment y) ->
      segment (x ⋈ y) !! a = resolve_imports y.(imports) x.(exports) y.(segment) !! a.
    Proof.
      intros Hsep Ha.
      rewrite (link_comm Hsep). symmetry in Hsep.
      apply (link_segment_lookup_l Hsep Ha).
    Qed.

    Lemma link_img_r {x y a w} :
      x ##ₗ y -> a ∈ dom (segment y) ->
      segment (x ⋈ y) !! a = Some w ->
      w ∈ img (exports x) \/ segment y !! a = Some w.
    Proof.
      intros Hsep Ha Hs. rewrite (link_comm Hsep) in Hs.
      symmetry in Hsep. apply (link_img_l Hsep Ha Hs).
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
      rewrite map_disjoint_dom. intros a' Ha Hc.
      rewrite map_disjoint_dom in Hms_disj0. apply (Hms_disj0 a').
      rewrite -link_segment_dom. set_solver.
      by inversion Hwf_l. by inversion Hwf_r. done.
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
      by rewrite link_comm.
    Qed.

    Lemma can_link_assoc {a b c} :
      a ##ₗ b -> a ##ₗ c -> b ##ₗ c ->
      a ⋈ b ##ₗ c.
    Proof.
      intros ab ac bc.
      inversion ab. inversion ac. inversion bc.
      apply can_link_intro.
      - by apply link_well_formed.
      - assumption.
      - rewrite map_disjoint_dom -link_segment_dom.
        rewrite disjoint_union_l. split; by rewrite <- map_disjoint_dom.
        by inversion Hwf_l. by inversion Hwf_r.
      - by rewrite map_disjoint_union_l.
    Qed.

    Ltac solve_can_link :=
      match goal with
      (* destruct a ##ₗ b to get a.xxx ##ₘ b.xxx
         where xxx=exports, imports or segment *)
      | |- imports ?a ##ₘ imports ?b =>
          apply can_link_disjoint_impls; solve_can_link || fail 1
      | |- exports ?a ##ₘ exports ?b =>
          let H := fresh in
          assert (H: a ##ₗ b);
          [ solve_can_link | (inversion H; assumption) ] || fail 1
      | |- segment ?a ##ₘ segment ?b =>
          let H := fresh in
          assert (H: a ##ₗ b);
          [ solve_can_link | (inversion H; assumption) ] || fail 1
      (* | |- map_compose (exports a) (imports c) ##ₘ segment b *)
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
      | |- _ ⋈ _ ##ₗ _ =>
          apply can_link_assoc; solve_can_link
      | |- _ ##ₗ _ ⋈ _ =>
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
        split. rewrite lookup_union_Some. done. solve_can_link. done.
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

    Lemma map_compose_imports {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      map_compose (exports c)
        (filter (λ '(_, s), (exports a ∪ exports b) !! s = None)
          (imports a ∪ imports b)) =
      map_compose (exports c) (imports a) ∪ map_compose (exports c) (imports b).
    Proof.
      intros Hab Hac Hbc.
      rewrite map_compose_min_r map_filter_filter_l.
      rewrite -map_compose_min_r. apply map_compose_union_r. solve_can_link.
      intros _ s _ Hs.
      rewrite lookup_union_None. apply elem_of_dom in Hs as [w Hs].
      split.
      destruct (exports a !! s) eqn:Ha.
      inversion Hac. rewrite map_disjoint_spec in Hexp_disj.
      contradiction (Hexp_disj _ _ _ Ha Hs). done.
      destruct (exports b !! s) eqn:Hb.
      inversion Hbc. rewrite map_disjoint_spec in Hexp_disj.
      contradiction (Hexp_disj _ _ _ Hb Hs). done.
    Qed.

    Local Ltac link_assoc_helper :=
      match goal with
      | H: ?a ##ₗ ?b, H1: ?x ∈ dom (segment ?a), H2: ?x ∈ dom (segment ?b) |- _ =>
            let H' := fresh in
            inversion H as [_ _ H' _]; rewrite map_disjoint_dom in H';
            apply (H' x H1 H2)
      | H: ?a ##ₗ ?b, H1: ?x ∈ dom (exports ?a), H2: ?x ∈ dom (exports ?b) |- _ =>
            let H' := fresh in
            inversion H as [_ _ _ H']; rewrite map_disjoint_dom in H';
            apply (H' x H1 H2)
      | H: ?a ##ₗ ?b,  H1: ?x ∈ dom (imports ?a) |- _ =>
            let H' := fresh in
            inversion H as [[_ H' _ _] _ _ _];
            apply (H' x) in H1; link_assoc_helper
      | H: ?b ##ₗ ?a,  H1: ?x ∈ dom (imports ?a) |- _ =>
            symmetry in H; link_assoc_helper
      end.

    Lemma link_assoc {a b c} :
      a ##ₗ b ->
      a ##ₗ c ->
      b ##ₗ c ->
      a ⋈ (b ⋈ c) = (a ⋈ b) ⋈ c.
    Proof.
      intros ab ac bc.
      specialize (link_exports_assoc a b c) as exp_eq.
      unfold link at 1. symmetry. unfold link at 1. f_equal.
      - repeat unfold resolve_imports, link. simpl.
        rewrite !map_compose_union_l.
        rewrite !map_compose_imports; try solve_can_link.
        repeat rewrite -map_union_assoc.
        (* repeat use of associativity/reflexivity *)
        repeat match goal with
        | |- ?d ∪ (?a ∪ ?c) = ?a ∪ ?a' =>
              rewrite map_union_assoc; replace (d ∪ a) with (a ∪ d);
              [(rewrite -map_union_assoc;f_equal)|apply map_union_comm]
        | |- ?a ∪ ?a' = ?d ∪ (?a ∪ ?c) =>
              symmetry; rewrite map_union_assoc; replace (d ∪ a) with (a ∪ d);
              [(rewrite -map_union_assoc;f_equal)|apply map_union_comm]
        end.
        symmetry. inversion ab.
        3,6: apply map_compose_disjoint.
        all: rewrite map_disjoint_dom; intros x Hx1 Hx2;
             try apply map_compose_dom_subseteq in Hx1;
             try apply map_compose_dom_subseteq in Hx2.
        all: link_assoc_helper.
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
      apply (elem_of_img_2 (D:=gset _)) in ic_addr.
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
      apply elem_of_dom. apply (elem_of_img_2 (D:=gset _)) in ia_addr. exact (Hno_imps_r _ ia_addr).
      exact eb_s.
      destruct (imports (b ⋈ c) !! addr) as [s'|] eqn:ibc_addr.
      replace s' with s in ibc_addr. apply (elem_of_img_2 (D:=gset _)) in ibc_addr.
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
        apply (WR_stable w _ _ (link_segment_dom_subseteq_l _ _)).
        apply (Hwr_regs w rr').
      - apply Hall_regs.
      - exact (no_imports_assoc_l bc Hno_imps_l).
      - apply no_imports_assoc_r; try assumption.
        solve_can_link.
    Qed.

    Lemma is_context_move_out {a b c regs} :
      a ##ₗ b ->
      (∀ w, w ∈ img regs -> WR w (dom a.(segment))) ->
      is_context (a ⋈ b) c regs -> is_context a (b ⋈ c) regs.
    Proof.
      intros ab Hregs [].
      assert (ac: a ##ₗ c). solve_can_link.
      assert (bc: b ##ₗ c). solve_can_link.
      apply is_context_intro.
      - apply can_link_sym. apply can_link_assoc;
        auto using symmetry.
      - exact Hregs.
      - exact Hall_regs.
      - apply no_imports_assoc_r; try auto using symmetry.
        apply no_imports_assoc_r; try auto using symmetry.
        apply no_imports_assoc_l; assumption.
      - apply no_imports_assoc_l. auto using symmetry.
        apply no_imports_assoc_r; auto using symmetry.
    Qed.

    Lemma is_context_remove_exportless_l {ctxt comp extra regs} :
      ctxt ##ₗ extra -> exports extra = ∅ ->
      (∀ w : Word, w ∈ img regs → WR w (dom (segment ctxt))) ->
      is_context (ctxt ⋈ extra) comp regs ->
      is_context ctxt comp regs.
    Proof.
      intros Hsep Hex_null Himg [ ].
      apply is_context_intro; [solve_can_link|done|done|..].
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
      apply (elem_of_img_2 (D:=gset _)) in Has.
      apply mk_is_Some, elem_of_dom in Hexp.
      contradiction (Hdisj s Hexp Has). reflexivity.
    Qed.

    Lemma is_context_remove_exportless_r {ctxt comp extra regs} :
      comp ##ₗ extra -> exports extra = ∅ ->
      is_context ctxt (comp ⋈ extra) regs ->
      is_context ctxt comp regs.
    Proof.
      intros Hsep Hex_null [ ].
      apply is_context_intro; [solve_can_link|done|done|..].
      intros s Hs. apply elem_of_img in Hs as [a Has].
      apply Hno_imps_l. unfold link. simpl. rewrite Hex_null.
      apply elem_of_img. exists a. rewrite map_filter_lookup_Some.
      split. apply (lookup_union_Some_l _ _ _ _ Has).
      rewrite map_union_empty.
      destruct (exports comp !! s) eqn:Hexp.
      inversion Hsep. inversion Hwf_l.
      apply (elem_of_img_2 (D:=gset _)) in Has.
      apply mk_is_Some, elem_of_dom in Hexp.
      contradiction (Hdisj s Hexp Has). reflexivity.
      replace (exports comp) with (exports (comp ⋈ extra)).
      apply Hno_imps_r. unfold link. simpl. rewrite Hex_null.
      apply map_union_empty.
    Qed.

    Lemma is_context_add_importless_l {ctxt comp extra regs} :
      ctxt ##ₗ extra -> comp ##ₗ extra -> imports extra = ∅ ->
      is_context ctxt comp regs ->
      is_context (ctxt ⋈ extra) comp regs.
    Proof.
      intros Hsep1 Hsep2 Him_null [ ].
      apply is_context_intro; [solve_can_link| |done|..].
      intros w Hw. apply (WR_stable w _ _ (link_segment_dom_subseteq_l _ _) (Hwr_regs w Hw)).
      rewrite dom_union_L. set_solver.
      transitivity (img (imports ctxt ∪ imports extra)).
      unfold link. simpl. apply img_filter_subseteq.
      by rewrite Him_null map_union_empty.
    Qed.

    Lemma is_context_add_importless_r {ctxt comp extra regs} :
      ctxt ##ₗ extra -> comp ##ₗ extra -> imports extra = ∅ ->
      is_context ctxt comp regs ->
      is_context ctxt (comp ⋈ extra) regs.
    Proof.
      intros Hsep1 Hsep2 Him_null [ ].
      apply is_context_intro; [solve_can_link|done|done|..].
      transitivity (img (imports comp ∪ imports extra)).
      unfold link. simpl. apply img_filter_subseteq.
      by rewrite Him_null map_union_empty.
      rewrite dom_union_L. set_solver.
    Qed.
  End LinkAssociative.

  (** Linking a list of segments*)
  Section LinkList.
    Global Instance empty_comp: Empty component := {|
      segment := ∅; exports := ∅; imports := ∅
    |}.

    Lemma empty_comp_wf : well_formed_comp ∅.
    Proof. apply wf_comp_intro; try set_solver. Qed.

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
      rewrite resolve_imports_imports_empty resolve_imports_exports_empty.
      apply map_empty_union.
      apply map_eq. intros a.
      rewrite map_filter_lookup.
      destruct (imp !! a) as [s|] eqn:His; simpl.
      apply option_guard_True.
      destruct (exp !! s) as [w|] eqn:Hes;
      apply (elem_of_img_2 (D:=gset _)) in His. apply mk_is_Some, elem_of_dom in Hes.
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

    Lemma can_link_link_list_1 {c l} :
      can_link_list (c :: l) -> c ##ₗ link_list l.
    Proof.
      revert c. induction l; simpl; intros c H.
      - inversion H. apply (can_link_empty_r H2).
      - symmetry. inversion H. inversion H4.
        apply can_link_assoc. apply IHl.
        by apply can_link_cons.
        by destruct (Forall_cons_1 _ _ _ H3) as [H3' _].
        symmetry. apply IHl. apply can_link_cons; try assumption.
        by destruct (Forall_cons_1 _ _ _ H3) as [_ H'].
    Qed.

    Lemma link_list_well_formed {l}:
      can_link_list l ->
      well_formed_comp (link_list l).
    Proof.
      intros H.
      induction l; simpl.
      exact empty_comp_wf.
      apply link_well_formed.
      apply (can_link_link_list_1 H).
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
        { inversion Hcl. apply (can_link_link_list_1 H3). }
        assert (Hyl : y ##ₗ link_list l).
        { apply (@can_link_list_Permutation _ (x::y::l)) in Hcl.
          inversion Hcl. apply (can_link_link_list_1 H3).
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

    Lemma can_link_link_list_2 {c l} :
      can_link_list l -> c ##ₗ link_list l -> can_link_list (c :: l).
    Proof.
      destruct l as [| a l ]; simpl; intros Hl Hc; inversion Hc.
      - by apply can_link_cons.
      - apply can_link_cons; [done| |done].
        apply Forall_cons_2.
        symmetry. symmetry in Hc. apply can_link_weaken_l in Hc. done.
        apply (can_link_link_list_1 Hl).
        rewrite Forall_forall. intros x Hx.
        apply elem_of_Permutation in Hx as [l' Hl'].
        inversion Hl.
        rewrite (link_list_Permutation H3 Hl') in Hc.
        simpl in Hc. symmetry in Hc.
        apply can_link_weaken_r in Hc.
        apply can_link_weaken_l in Hc. by symmetry.
        apply (can_link_list_Permutation H3) in Hl'.
        apply (can_link_link_list_1 Hl').
        replace (x ⋈ link_list l') with (link_list (x :: l')).
        apply can_link_link_list_1.
        apply (can_link_list_Permutation Hl).
        by apply Permutation_cons. done.
    Qed.
  End LinkList.

  Section ComponentSize.
    Global Instance component_size : Size component :=
      fun c => size (segment c) + size (exports c).

    Lemma link_size a b : a ##ₗ b -> size (a ⋈ b) = size a + size b.
    Proof.
      intros Hsep.
      unfold link, size, component_size. simpl.
      rewrite -!size_dom -link_segment_dom.
      rewrite !dom_union_L !size_union. lia.
      1,2: rewrite -map_disjoint_dom.
      all: by inversion Hsep as [[] []].
    Qed.

    Lemma component_size_empty : size (∅ : component) = 0.
    Proof. unfold size, component_size. rewrite !map_size_empty. lia. Qed.

    Lemma component_size_empty_iff (c:component) :
      dom (imports c) ⊆ dom (segment c) -> size c = 0 <-> c = ∅.
    Proof.
      intros Hd. unfold size, component_size. simpl.
      rewrite Nat.eq_add_0 !map_size_empty_iff. destruct c as [s i e]; simpl.
      split; unfold empty, empty_comp.
      - intros [Hs He]. f_equal; try done.
        simpl in Hd. rewrite Hs in Hd. apply (equiv_empty_L (H3:=gset_semi_set)) in Hd.
        by rewrite dom_empty_iff_L in Hd.
      - intros Hs. by inversion Hs.
    Qed.

    Lemma component_ind (P: component -> Prop) :
      (∀ n, (∀ c, size c < n -> P c) -> ∀ c, size c = n -> P c) ->
      ∀ c, P c.
    Proof.
      intros HI c.
      specialize (Nat.le_refl (size c)).
      apply (nat_ind (λ n, ∀ c, size c <= n -> P c)).
      intros c' Hc'. apply (HI 0). intros c'' Hc''. lia. lia.
      intros n Hn c' Hc'.
      destruct (decide (size c'=S n)).
      apply (HI (S n)). intros c'' Hc''. apply Hn. lia. done.
      apply Hn. lia.
    Qed.

    (** For any property [P],
        if any component [c] either verifies [P] or can be split into
        smaller components [c1 ⋈ c2] where [c1] verifies [P], then it can
        be split in a list where all components verify [P] *)
    Lemma component_decomposition (P : component -> Prop) :
      (∀ c,
        well_formed_comp c ->
        (P c \/ ∃ c1 c2, c1 ##ₗ c2 /\ P c1 /\ size c1 > 0 /\ c = c1 ⋈ c2)) ->
      ∀ c, well_formed_comp c ->
        ∃ l, can_link_list l /\ Forall P l /\ c = link_list l.
    Proof.
      intros HPrec.
      induction c using component_ind. intros Hwfc.
      specialize (HPrec c Hwfc) as [Hr | (c1 & c2 & Hc12 & Hc1 & Hdecr & Hlink)].
      - exists [c]. split.
        apply can_link_cons. done. done. apply can_link_nil.
        split. by apply Forall_cons_2. simpl.
        symmetry. by apply empty_right_id.
      - edestruct (H c2) as (l & Hcl & Hfl & Hc2).
        specialize (link_size c1 c2 Hc12) as Hsize.
        rewrite <-Hlink in Hsize. lia. by inversion Hc12.
        exists (c1::l). repeat split.
        apply can_link_link_list_2. done. by rewrite <- Hc2.
        by apply Forall_cons_2. simpl. by rewrite <- Hc2.
    Qed.
  End ComponentSize.

  (** An induction on a component's exports map *)
  Lemma exports_ind (P: component -> Prop) c :
    P {| segment := segment c; imports := imports c; exports := ∅ |} ->
    (∀ s w exp,
      exports c !! s = Some w ->
      exp !! s = None ->
      exp ⊆ exports c ->
      P {| segment := segment c; imports := imports c; exports := exp |} ->
      P {| segment := segment c; imports := imports c; exports := <[s := w]> exp |}
    ) ->
    P c.
  Proof.
    intros Hinit Hind.
    destruct c as [s i e]. simpl in *.
    apply (map_ind (fun exp =>
      exp ⊆ e -> P {| segment := s; imports := i; exports := exp |}
    )).
    intros _. apply Hinit.
    intros s' w exp Hexp Hi Hsubset.
    assert (Hs: exp ⊆ e).
    { apply map_subseteq_spec. intros j x Hj. rewrite map_subseteq_spec in Hsubset.
      destruct (decide (s'=j)) as [Heq|Heq]. simplify_eq.
      apply Hsubset. rewrite (lookup_insert_ne _ _ _ _ Heq).
      apply Hj. }
    apply Hind.
    rewrite map_subseteq_spec in Hsubset. apply Hsubset. apply lookup_insert.
    apply Hexp. apply Hs.
    apply (Hi Hs). reflexivity.
  Qed.
End Linking.

Arguments component _ {_ _}.

Notation imports_type Symbols := (gmap Addr Symbols).
Notation exports_type Symbols := (gmap Symbols Word).
Notation segment_type := (gmap Addr Word).

Infix "⋈" := link (at level 50).

(** Simple lemmas used to weaken WR
    and address_restrictions in well_formed_comp, can_link, is_program... *)
Section LinkWeakenRestrictions.
  Context {Symbols: Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Context {WR: Word -> gset Addr -> Prop}.
  Context {WR': Word -> gset Addr -> Prop}.
  Variable WR_weaken: ∀ w a, WR w a -> WR' w a.

  Lemma wf_comp_weaken_wr :
    ∀ {comp : component Symbols},
    well_formed_comp WR comp ->
    well_formed_comp WR' comp.
  Proof.
    intros comp [ ].
    apply wf_comp_intro.
    all: try assumption.
    all: intros w H; apply WR_weaken.
    exact (Hwr_exp w H). apply (Hwr_ms w H).
  Qed.

  Lemma can_link_weaken_wr :
    ∀ {a b : component Symbols},
    can_link WR a b ->
    can_link WR' a b.
  Proof.
    intros a b [ ].
    apply can_link_intro; try apply wf_comp_weaken_wr; assumption.
  Qed.

  Lemma is_program_weaken_wr :
    ∀ {comp : component Symbols} {regs},
    is_program WR comp regs ->
    is_program WR' comp regs.
  Proof.
    intros comp regs [].
    apply is_program_intro.
    apply wf_comp_weaken_wr. assumption.
    assumption.
    intros w rr_w.
    exact (WR_weaken w _ (Hwr_regs w rr_w)).
    assumption.
  Qed.

  Lemma is_context_weaken_wr :
    ∀ {context lib : component Symbols} {regs},
    is_context WR context lib regs ->
    is_context WR' context lib regs.
  Proof.
    intros context lib regs [].
    apply is_context_intro.
    apply can_link_weaken_wr. assumption.
    intros w rr_w.
    apply (WR_weaken w _ (Hwr_regs w rr_w)).
    all: assumption.
  Qed.
End LinkWeakenRestrictions.

(** Can solve simpl can_link and well_formed_comp goals using
    symmetry, compatibility with link and weakening *)
Ltac solve_can_link :=
  match goal with
  (* destruct a ##ₗ b to get a.xxx ##ₘ b.xxx
     where xxx=exports, imports or segment *)
  | |- imports ?a ##ₘ imports ?b =>
      apply (can_link_disjoint_impls unconstrained_word);
      solve_can_link || fail 1
  | |- exports ?a ##ₘ exports ?b =>
      let H := fresh in
      assert (H: can_link unconstrained_word a b);
      [ solve_can_link | by inversion H ] || fail 1
  | |- segment ?a ##ₘ segment ?b =>
      let H := fresh in
      assert (H: can_link unconstrained_word a b);
      [ solve_can_link | by inversion H ] || fail 1
  | |- dom (imports ?a) ⊆ dom (segment ?a) =>
      let H := fresh in
      assert (H: well_formed_comp unconstrained_word a);
      [ solve_can_link | by inversion H ] || fail 1
  (* using symmetry *)
  | H: can_link ?wr ?a ?b |- can_link ?wr ?a ?b => exact H
  | H: can_link ?wr ?a ?b |- can_link ?wr ?b ?a => symmetry; exact H
  | H: well_formed_comp ?wr ?a |- well_formed_comp ?wr ?a => exact H
  | H: can_link _ ?a _ |- well_formed_comp _ ?a => inversion H; clear H; solve_can_link
  | H: can_link _ _ ?a |- well_formed_comp _ ?a => inversion H; clear H; solve_can_link
  (* using weakening *)
  | H: can_link ?wr _ _ |- can_link unconstrained_word _ _ =>
      tryif (unify wr unconstrained_word) then fail else (
        apply (can_link_weaken_wr (@any_implies_unconstrained_word wr)) in H;
        solve_can_link)
  | H: can_link ?wr _ _, H2: ∀ w a, ?wr w a -> ?wr' w a |- can_link ?wr' _ _ =>
      tryif (unify wr wr') then fail else (
        apply (can_link_weaken_wr H2) in H; solve_can_link)
  (* using weakening for well_formed_comp *)
  | H: well_formed_comp ?wr _ |- well_formed_comp unconstrained_word _ =>
      tryif (unify wr unconstrained_word) then fail else (
        apply (wf_comp_weaken_wr (@any_implies_unconstrained_word wr)) in H;
        solve_can_link)
  | H: well_formed_comp ?wr _, H2: ∀ w a, ?wr w a -> ?wr' w a |- well_formed_comp ?wr' _ =>
      tryif (unify wr wr') then fail else (
        apply (wf_comp_weaken_wr H2) in H; solve_can_link)
  (* get extra can_link hypotheses hidden in inductives *)
  | H: is_context _ _ _ _ |- _ =>
      inversion H; clear H; solve_can_link || fail 1
  | H: can_link _ (_ ⋈ _) _ |- can_link _ _ _ =>
      let H1 := fresh in let H2 := fresh in
      apply (can_link_weaken_l _) in H as H1;
      apply (can_link_weaken_r _) in H as H2;
      clear H; solve_can_link
  | H: can_link _ _ (_ ⋈ _) |- can_link _ _ _ => symmetry in H;
      let H1 := fresh in let H2 := fresh in
      apply (can_link_weaken_l _) in H as H1;
      apply (can_link_weaken_r _) in H as H2;
      clear H; solve_can_link
  | |- can_link _ (_ ⋈ _) _ =>
      apply (can_link_assoc _); solve_can_link
  | |- can_link _ _ (_ ⋈ _) =>
      symmetry; apply (can_link_assoc _ _); solve_can_link
  | |- well_formed_comp _ (_ ⋈ _) =>
      apply (link_well_formed _); solve_can_link
  end.


#[global] Hint Extern 5 (can_link _ _ _) => solve_can_link : core.
#[global] Hint Extern 5 (well_formed_comp _ _) => solve_can_link : core.
