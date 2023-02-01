From iris.proofmode Require Import proofmode environments.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Import linking logrel_binary.
From cap_machine Require Import stdpp_img iris_extra.
From cap_machine Require Import fundamental_binary.

Section logrel.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          {MP:MachineParameters}.

  Context {Symbols:Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Infix "##ₗ" := (can_link can_address_only) (at level 70).

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
    (∀ w, w ∈ img (segment c) -> no_capability w (dom (segment c))) ->
    x ##ₗ c -> y ##ₗ c ->
    dom (exports x) ⊆ dom (exports y) ->
    ([∗ map] a ↦ w ∈ segment (x ⋈ c), a ↦ₐ w) ∗
    ([∗ map] a ↦ w ∈ segment (y ⋈ c), a ↣ₐ w) ∗
    interp_exports x y ={E}=∗
      ([∗ map] a ↦ _ ∈ map_zip (segment (x ⋈ c)) (segment (y ⋈ c)),
        ⌜a ∈ dom (segment c)⌝ →
          inv (logN.@a)
          (∃ w w' : Word, a ↦ₐ w ∗ a ↣ₐ w' ∗ interp (w, w'))).
  Proof.
    iIntros (Hno_caps Hsep1 Hsep2 Hexp) "[Hpx [Hpy #Hexp]]".
    rewrite -(big_sepM_filter (fun '(a,_) => a ∈ _)).
    rewrite (big_sepM_big_sepL2_map_to_list (fun a _ => inv _ _)).
    iApply region_inv_alloc.
    rewrite -(big_sepM_big_sepL2_map_to_list (fun a v => (a ↦ₐ v.1 ∗ a ↣ₐ v.2 ∗ interp v)%I)).
    rewrite big_sepM_filter.
    iApply (big_sepM_mono (fun a w =>
      interp_exports x y ∗
      (⌜ segment (x ⋈ c) !! a = Some w.1 ⌝ ∗ a ↦ₐ w.1) ∗
      (⌜ segment (y ⋈ c) !! a = Some w.2 ⌝ ∗ a ↣ₐ w.2))%I).
    iIntros (a [w w'] Hzip) "[#Hexp [[%Hxca Hw] [%Hyca Hw']]] %Ha".
    simpl. iFrame.
    (* assert validity of w,w' by case disjunction *)
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
    1,2: apply elem_of_img_rev in Hxca; apply Hno_caps in Hxca.
    1,2: destruct w; try contradiction Hxca.
    1,2: rewrite fixpoint_interp1_eq; done.

    rewrite (big_sepM_sep (fun _ _ => interp_exports x y)).
    iSplitR.
    iApply big_sepM_dup. iModIntro. iIntros "H".
    iFrame. done. done.
    iApply (big_sepM_sep_zip_affine
      (fun a v => a ↦ₐ v)%I
      (fun a v => a ↣ₐ v)%I).
    iFrame.

    Unshelve. apply TCOr_l. unfold Affine.
    iIntros (j z) "#H". done.
  Qed.



  Lemma interp_link {x y c:component Symbols}:
    (∀ w, w ∈ img (segment c) -> no_capability w (dom (segment c))) ->
    x ##ₗ c -> y ##ₗ c ->
    imports x = ∅ -> imports y = ∅ ->
    spec_ctx ∗ interp_exports x y ∗
    ([∗ map] a ↦ _ ∈ map_zip (segment (x ⋈ c)) (segment (y ⋈ c)),
    ⌜a ∈ dom (segment c)⌝ →
      inv (logN.@a)
      (∃ w w' : Word, a ↦ₐ w ∗ a ↣ₐ w' ∗ interp (w, w'))) -∗
    interp_exports (x ⋈ c) (y ⋈ c).
  Proof.
    iIntros (Hno_caps Hsep1 Hsep2 Hno_imps_x Hno_imps_y) "[#Hspec [#Hexp #Hinv]]".
    (* weird induction scheme: essentially an induction on the exports of c
       but keeping our persistent hypotheses out of the induction *)
    apply (exports_ind (fun c' => envs_entails
    (Envs
    (Esnoc _ "Hinv"
       ([∗ map] a ↦ _ ∈ map_zip (segment (x ⋈ c)) (segment (y ⋈ c)),
        ⌜a ∈ dom (segment c)⌝ →
         inv _
         (∃ w w' : Word, a ↦ₐ w ∗ a ↣ₐ w' ∗ interp (w, w'))))
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
      inversion Hsep1. inversion Hsep2.
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
        destruct p. done.
        all: iSplitR; try done.
        (* Use fundamental theorem to change interp_expr into interp *)
        4: iIntros (r); do 2 iModIntro; iApply fundamental_binary;
           done || rewrite fixpoint_interp1_eq; iSimpl; iSplitR; try done.
        (* add the hypothese a ∈ dom (segment c) which we need to access our invariants *)
        all: iApply (big_sepL_mono (fun _ a => ⌜a ∈ dom (segment c)⌝ -∗ _)%I).
        1,3,5,7,9:
          iIntros (k y' Hk) "Hl"; iApply "Hl"; iPureIntro;
          inversion Hwf_r;
          apply (Hwr_exp _ (elem_of_img_rev _ _ _ Hec)), elem_of_finz_seq_between, elem_of_list_lookup;
          exists k; apply Hk.
        all: induction (finz.seq_between b e);
             try (iApply big_sepL_nil; done).
        all: iApply big_sepL_cons; iSplitR; try apply IHl.
        all: iIntros "%Ha"; iExists interp.
        all: iSplitL.
        (* read_cond and write_cond boil down to interp -> interp,
           so they are trivial *)
        4,10: iSplitL.
        2,4,5,6,7,9,11: iSimpl; do 2 iModIntro; iIntros (ww ww') "H"; done.
        (* others results come from the invariants *)
        all: assert (Ha': a0 ∈ dom (map_zip (segment (x ⋈ c)) (segment (y ⋈ c)))).
        1,3,5,7,9:
          rewrite map_zip_dom_L !(resolve_imports_link_dom can_address_only);
          (rewrite !dom_union_L -union_intersection_r_L; apply (union_subseteq_r _ _ a0 Ha))
          || solve_can_link.
        all: apply elem_of_dom in Ha' as [z Ha'].
        all: iPoseProof (big_sepM_lookup _ _ a0 _ Ha' with "Hinv") as "Ha0".
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

    Unshelve. all: apply TCOr_l; unfold Affine;
    iIntros (j t) "#H"; done.
  Qed.
End logrel.
