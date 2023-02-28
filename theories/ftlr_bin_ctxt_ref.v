From iris.proofmode Require Import proofmode environments.
From iris.program_logic Require Export weakestpre.
From iris Require Import adequacy.
From cap_machine Require Import linking logrel_binary.
From cap_machine Require Import stdpp_restrict stdpp_img iris_extra.
From cap_machine Require Import fundamental_binary contextual_refinement.
From cap_machine Require Import machine_run.

Section logrel.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          {MP:MachineParameters}.

  Context {Symbols:Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Local Coercion segment : component >-> segment_type.

  Notation "b |ᵣ a" := (restrict_map (a : gmap _ _) (b: gmap _ _)) (at level 80).
  Infix "##ₗ" := (can_link can_address_only_no_seals) (at level 70).

  (** Lifting the interp binary value relation from words to components
      This implies dom (exports y) ⊆ dom (exports x) *)
  Definition interp_exports (x y: component Symbols) : iProp Σ :=
    [∗ map] s ↦ wy ∈ exports y,
        match exports x !! s with
        | None => False (* values exported by y must also be exported by x *)
        | Some wx =>
          (* ([∗ map] a ↦ w ∈ segment x, a ↦ₐ w) ∗
          ([∗ map] a ↦ w ∈ segment y, a ↣ₐ w) -∗ *)
            interp (wx, wy)
        end.

  (** Allocates invariants for segment c in links (x ⋈ c) and (y ⋈ c)
      assuming the exports of x and y are valid. *)
  Lemma interp_exports_inv_alloc E {x y c: component Symbols} :
    (∀ w, w ∈ img (segment c) -> is_word w) ->
    x ##ₗ c -> y ##ₗ c ->
    dom (exports x) ⊆ dom (exports y) ->
    ([∗ map] a ↦ w ∈ x ⋈ c |ᵣ c, a ↦ₐ w) ∗
    ([∗ map] a ↦ w ∈ y ⋈ c |ᵣ c, a ↣ₐ w) ∗
    interp_exports x y ={E}=∗
      ([∗ map] a ↦ _ ∈ c, inv (logN.@a) (interp_ref_inv a interp)).
  Proof.
    iIntros (Hno_caps Hsep1 Hsep2 Hexp) "[Hpx [Hpy #Hexp]]".
    rewrite big_sepM_dom.
    assert (Hdc:
      dom (segment c) =
      dom (map_zip (x ⋈ c : segment_type) (y ⋈ c: segment_type) |ᵣ c)).
    { rewrite dom_restrict_map_L dom_map_zip_with_L -!(link_segment_dom can_address_only_no_seals).
      set_solver. all: solve_can_link. }
    rewrite Hdc -big_sepM_dom.
    (* rewrite -(big_sepM_filter (fun '(a,_) => a ∈ _)). *)
    rewrite (big_sepM_big_sepL2_map_to_list (fun a _ => inv _ _)).
    iApply region_inv_alloc.
    rewrite -(big_sepM_big_sepL2_map_to_list (fun a v => (a ↦ₐ v.1 ∗ a ↣ₐ v.2 ∗ interp v)%I)).
    iApply (big_sepM_mono (fun a w =>
      interp_exports x y ∗
      (⌜ (x ⋈ c |ᵣ c) !! a = Some w.1 ⌝ ∗ a ↦ₐ w.1) ∗
      (⌜ (y ⋈ c |ᵣ c) !! a = Some w.2 ⌝ ∗ a ↣ₐ w.2))%I).
    iIntros (a [w w'] Hzip) "[#Hexp [[%Hxca Hw] [%Hyca Hw']]]".
    simpl. iFrame.
    (* assert validity of w,w' by case disjunction *)
    apply map_filter_lookup_Some in Hxca as [Hxca Ha].
    apply map_filter_lookup_Some in Hyca as [Hyca _]. apply elem_of_dom in Ha.
    rewrite (link_segment_lookup_r _ Hsep1 Ha) in Hxca.
    rewrite (link_segment_lookup_r _ Hsep2 Ha) in Hyca.
    rewrite !resolve_imports_spec /= in Hxca, Hyca.
    destruct (imports c !! a) as [s|] eqn:Hic.
    destruct (exports y !! s) as [wy|] eqn:Hey;
    destruct (exports x !! s) as [wx|] eqn:Hex.
    apply Some_inj in Hxca, Hyca.
    (* if they are exports from x,y, validity comes from the hypothese *)
    1,2: iPoseProof (big_sepM_lookup _ _ _ _ Hey with "Hexp") as "H".
    rewrite Hex Hxca Hyca. iApply "H".
    rewrite Hex. done.
    apply mk_is_Some, elem_of_dom in Hex.
    apply not_elem_of_dom in Hey.
    contradiction (Hey (Hexp _ Hex)).
    (* else we know they are only words, and thus valid *)
    1,2: rewrite Hxca in Hyca; apply Some_inj in Hyca; rewrite -Hyca.
    1,2: apply (elem_of_img_2 (D:=gset _)) in Hxca; apply Hno_caps in Hxca; unfold is_word in Hxca.
    1,2: destruct w as [z | sb | z sb];
         [ (rewrite fixpoint_interp1_eq; done) | | ];
         destruct sb; simpl in Hxca; discriminate Hxca.

    rewrite (big_sepM_sep (fun _ _ => interp_exports x y)).
    iSplitR.
    iApply big_sepM_dup. iModIntro. iIntros "H".
    iFrame. done. done. unfold restrict_map.
    rewrite restrict_map_zip_with.
    iApply (big_sepM_sep_zip_affine
      (fun a v => a ↦ₐ v)%I
      (fun a v => a ↣ₐ v)%I).
    iFrame.

    Unshelve. typeclasses eauto.
  Qed.

  Lemma interp_link_exports {x y c:component Symbols}:
    x ##ₗ c -> y ##ₗ c ->
    spec_ctx ∗ interp_exports x y ∗
    ([∗ map] a ↦ _ ∈ c, inv (logN.@a) (interp_ref_inv a interp)) -∗
    interp_exports (x ⋈ c) (y ⋈ c).
  Proof.
    iIntros (Hsep1 Hsep2) "[#Hspec [#Hexp #Hinv]]".
    (* weird induction scheme: essentially an induction on the exports of c
       but keeping our persistent hypotheses out of the induction *)
    apply (exports_ind (fun c' => envs_entails
    (Envs
    (Esnoc _ "Hinv"
       ([∗ map] a ↦ _ ∈ c, inv _ (interp_ref_inv a interp)))
    _ _)
    _)%I c).
    (* For exports from x,y this is a direct result of our hypothese *)
    - iApply big_sepM_intro. iModIntro.
      rewrite /= !map_union_empty. iIntros (s w) "%Hey".
      iPoseProof (big_sepM_lookup _ _ _ _ Hey with "Hexp") as "H'".
      destruct (exports x !! s); done.
    (* For exports of c we need to do a bit of work.
       First, prove they are indeed exports of c and not x or y *)
    - iIntros (s w exp Hec Hexp Hexp_sub IH).
      inversion Hsep1. inversion Hsep2. inversion Hwf_r.
      destruct (exports y !! s) as [ey|] eqn:Hey.
      rewrite map_disjoint_dom in Hexp_disj0.
      apply mk_is_Some, elem_of_dom in Hec, Hey.
      contradiction (Hexp_disj0 _ Hey Hec).
      destruct (exports x !! s) as [ex|] eqn:Hex.
      rewrite map_disjoint_dom in Hexp_disj.
      apply mk_is_Some, elem_of_dom in Hec, Hex.
      contradiction (Hexp_disj _ Hex Hec).
      unfold interp_exports. iSimpl.
      replace (exports y ∪ <[s:=w]> exp) with (<[s:=w]> (exports y ∪ exp)).
      iApply big_sepM_insert. apply lookup_union_None. split; assumption.
      iSplitR.
      (* Now use the invariants to prove the validity of these exports *)
      + rewrite (lookup_union_r _ _ _ Hex) lookup_insert.
        rewrite fixpoint_interp1_eq.
        destruct w. done.
        destruct sb.
        2,3: specialize (Hwr_exp _ (elem_of_img_2 _ _ _ Hec));
             destruct s0; contradiction Hwr_exp.
        destruct p. done.
        all: iSplitR; [done|].
        (* Use fundamental theorem to change interp_expr into interp *)
        4: iIntros (r); do 2 iModIntro; iApply fundamental_binary;
           done || rewrite fixpoint_interp1_eq; iSimpl; iSplitR; try done.
        (* add the hypothese a ∈ dom (segment c) which we need to access our invariants *)
        all: iApply (big_sepL_mono (fun _ a => ⌜a ∈ dom (segment c)⌝ -∗ _)%I);
             [ (iIntros (k y' Hk) "Hl"; iApply "Hl"; iPureIntro;
                apply (Hwr_exp _ (elem_of_img_2 _ _ _ Hec)), elem_of_finz_seq_between, elem_of_list_lookup;
                exists k; apply Hk) | ].
        all: induction (finz.seq_between f f0);
             [ (iApply big_sepL_nil; done) |].
        all: iApply big_sepL_cons; iSplitR; [ | apply IHl].
        all: iIntros "%Ha"; iExists interp.
        (* read_cond and write_cond boil down to interp -> interp,
           so they are trivial *)
        all: iSplitL;
             [ | (try iSplitL; iSimpl; do 2 iModIntro; iIntros (ww ww') "H"; done)].
        (* others results come from the invariants *)
        all: apply elem_of_dom in Ha as [z Ha].
        all: iPoseProof (big_sepM_lookup _ _ a _ Ha with "Hinv") as "Ha0".
        all: iApply "Ha0"; iPureIntro; exact Ha.
      + unfold interp_exports in IH. simpl in IH.
        iApply (big_sepM_mono (fun k wy =>
          interp_exports x y ∗ match (exports x ∪ exp) !! k with
            | Some wx => interp (wx, wy)
            | None => False%I
          end)%I (fun k wy =>
          match (exports x ∪ <[s:=w]> exp) !! k with
            | Some wx => interp (wx, wy)
            | None => False%I
          end) (exports y ∪ exp)).
        iIntros (s' wy Hwy) "[#Hexp #H]".
        apply lookup_union_Some_raw in Hwy as [Hwy | [Hwy Hexp_y] ].
        iPoseProof (big_sepM_lookup _ _ _ _ Hwy with "Hexp") as "H'".
        destruct (exports x !! s') eqn:Hx.
        rewrite !(lookup_union_Some_l _ _ _ _ Hx). done. done.
        destruct (exports x !! s') eqn:Hx.
        rewrite map_subseteq_spec in Hexp_sub.
        rewrite map_disjoint_spec in Hexp_disj.
        contradiction (Hexp_disj s' _ _ Hx (Hexp_sub s' _ Hexp_y)).
        destruct (decide (s=s')) as [Heq|Heq].
        rewrite Heq in Hexp. rewrite Hexp in Hexp_y. discriminate.
        rewrite !(lookup_union_r _ _ _ Hx).
        rewrite (lookup_insert_ne _ _ _ _ Heq). done.
        iApply big_sepM_sep. iSplitR.
        iApply big_sepM_intro. iModIntro. iIntros (k x0) "_". done.
        apply IH.
      + apply insert_union_r. assumption.

    Unshelve. all: typeclasses eauto.
  Qed.

  Lemma interp_link E {x y c: component Symbols} :
    (∀ w, w ∈ img (segment c) -> is_word w) ->
    x ##ₗ c -> y ##ₗ c ->
    dom (exports x) ⊆ dom (exports y) ->
    spec_ctx ∗ interp_exports x y ∗
    ([∗ map] a ↦ w ∈ x ⋈ c |ᵣ c, a ↦ₐ w) ∗
    ([∗ map] a ↦ w ∈ y ⋈ c |ᵣ c, a ↣ₐ w) ={E}=∗
    interp_exports (x ⋈ c) (y ⋈ c).
  Proof.
    iIntros (Hno_caps Hsep1 Hsep2 Hdom_incl) "(#Hspec & #Hxy & Hx & Hy)".
    iApply (interp_link_exports Hsep1 Hsep2).
    iSplitR. done. iSplitR. done.
    iApply (interp_exports_inv_alloc E Hno_caps Hsep1 Hsep2 Hdom_incl).
    iFrame. done.
  Qed.

End logrel.
