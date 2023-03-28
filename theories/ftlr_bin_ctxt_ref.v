From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import proofmode environments.
From iris.program_logic Require Export weakestpre.
From iris Require Import adequacy.

From cap_machine Require Import iris_extra linking machine_run logrel_binary.
From cap_machine Require Import fundamental_binary contextual_refinement.

Section logrel.
  Context {Symbols:Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Context {Σ: gFunctors}.
  Context {MP: MachineParameters}.

  (** Asserts a segment only contains integers *)
  Definition code_all_ints (c : component Symbols) :=
    ∀ w, w ∈ img (segment c) -> is_int w.

  Local Coercion segment : component >-> segment_type.

  Infix "##ₗ" := (can_link can_address_only_no_seals) (at level 70).

  Section interp_exports.
    Context {memg:memG Σ}.
    Context {regg:regG Σ}.
    Context {nainv: logrel_na_invs Σ}.
    Context {cfgsg: cfgSG Σ}.

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
      code_all_ints c ->
      x ##ₗ c -> y ##ₗ c ->
      dom (exports x) ⊆ dom (exports y) ->
      ([∗ map] a ↦ w ∈ x ⋈ᵣ c, a ↦ₐ w) ∗
      ([∗ map] a ↦ w ∈ y ⋈ᵣ c, a ↣ₐ w) ∗
      interp_exports x y ={E}=∗
        ([∗ map] a ↦ _ ∈ c, inv (logN.@a) (interp_ref_inv a interp)).
    Proof.
      iIntros (Hno_caps Hsep1 Hsep2 Hexp) "[Hpx [Hpy #Hexp]]".
      rewrite big_sepM_dom.
      assert (Hdc:
        dom (segment c) =
        dom (map_zip (x ⋈ᵣ c) (y ⋈ᵣ c))).
      { rewrite dom_map_zip_with_L !resolve_imports_dom. set_solver.
        all: solve_can_link. }
      rewrite Hdc -big_sepM_dom.
      (* rewrite -(big_sepM_filter (fun '(a,_) => a ∈ _)). *)
      rewrite (big_sepM_big_sepL2_map_to_list (fun a _ => inv _ _)).
      iApply region_inv_alloc.
      rewrite -(big_sepM_big_sepL2_map_to_list (fun a v => (a ↦ₐ v.1 ∗ a ↣ₐ v.2 ∗ interp v)%I)).
      iApply (big_sepM_mono (fun a w =>
        interp_exports x y ∗
        (⌜ (x ⋈ᵣ c) !! a = Some w.1 ⌝ ∗ a ↦ₐ w.1) ∗
        (⌜ (y ⋈ᵣ c) !! a = Some w.2 ⌝ ∗ a ↣ₐ w.2))%I).
      iIntros (a [w w'] Hzip) "[#Hexp [[%Hxca Hw] [%Hyca Hw']]]".
      simpl. iFrame.
      (* assert validity of w,w' by case disjunction *)
      simpl in Hxca, Hyca.
      apply mk_is_Some in Hxca as Ha. apply elem_of_dom in Ha.
      rewrite resolve_imports_dom in Ha; [|solve_can_link].
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
      1,2: apply (elem_of_map_img_2 (SA:=gset _)) in Hxca; apply Hno_caps in Hxca; unfold is_int in Hxca.
      1,2: destruct w as [z | sb | z sb];
          [ (rewrite fixpoint_interp1_eq; done) | | ];
          destruct sb; simpl in Hxca; discriminate Hxca.

      rewrite (big_sepM_sep (fun _ _ => interp_exports x y)).
      iSplitR.
      iApply big_sepM_dup. iModIntro. iIntros "H".
      iFrame. done. done.
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
          2,3: specialize (Hwr_exp _ (elem_of_map_img_2 _ _ _ Hec));
              destruct s0; contradiction Hwr_exp.
          destruct p. done.
          all: iSplitR; [done|].
          (* Use fundamental theorem to change interp_expr into interp *)
          4: iIntros (r); do 2 iModIntro; iApply fundamental_binary;
            done || rewrite fixpoint_interp1_eq; iSimpl; iSplitR; try done.
          (* add the hypothese a ∈ dom (segment c) which we need to access our invariants *)
          all: iApply (big_sepL_mono (fun _ a => ⌜a ∈ dom (segment c)⌝ -∗ _)%I);
              [ (iIntros (k y' Hk) "Hl"; iApply "Hl"; iPureIntro;
                  apply (Hwr_exp _ (elem_of_map_img_2 _ _ _ Hec)), elem_of_finz_seq_between, elem_of_list_lookup;
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
      code_all_ints c ->
      x ##ₗ c -> y ##ₗ c ->
      dom (exports x) ⊆ dom (exports y) ->
      spec_ctx ∗ interp_exports x y ∗
      ([∗ map] a ↦ w ∈ x ⋈ᵣ c, a ↦ₐ w) ∗
      ([∗ map] a ↦ w ∈ y ⋈ᵣ c, a ↣ₐ w) ={E}=∗
      interp_exports (x ⋈ c) (y ⋈ c).
    Proof.
      iIntros (Hno_caps Hsep1 Hsep2 Hdom_incl) "(#Hspec & #Hxy & Hx & Hy)".
      iApply (interp_link_exports Hsep1 Hsep2).
      iSplitR. done. iSplitR. done.
      iApply (interp_exports_inv_alloc E Hno_caps Hsep1 Hsep2 Hdom_incl).
      iFrame. done.
    Qed.

    Definition stuff_to_prove γc (l_comp r_comp : component Symbols) (reg : Reg) : iProp Σ :=
      spec_ctx ∗
      ([∗ map] a↦w ∈ l_comp, a ↦ₐ w) ∗
      ([∗ map] a↦w ∈ r_comp, a ↣ₐ w) ∗
      ([∗ map] r↦w ∈ reg, r ↦ᵣ w) ∗
      ([∗ map] r↦w ∈ reg, r ↣ᵣ w) ∗
      na_own logrel_nais ⊤ ∗
      own γc (◯ ((Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅)) : cfgUR)) ={⊤}=∗
      WP Seq (Instr Executable)
      {{ v,
         ⌜v = HaltedV⌝
         → ∃ r0 : Reg * Reg, ⤇
             of_val HaltedV ∗
             full_map r0
             ∧ registers_mapsto r0.1 ∗
             spec_registers_mapsto r0.2 ∗
             na_own logrel.logrel_nais ⊤ }}.

    (* Lemma interp_link_adequacy γc (l_comp r_comp ctxt : component Symbols) reg :
      (∀ w, w ∈ img reg -> is_int w ∨ w ∈ img (exports ctxt)) ->
      code_all_ints ctxt ->
      l_comp ##ₗ ctxt -> r_comp ##ₗ ctxt ->
      dom (exports l_comp) ⊆ dom (exports r_comp) -> (
        spec_ctx ∗
        na_own logrel_nais ⊤ ∗
        ([∗ map] a↦w ∈ l_comp ⋈ₗ ctxt, a ↦ₐ w) ∗
        ([∗ map] a↦w ∈ r_comp ⋈ₗ ctxt, a ↣ₐ w) ={⊤}=∗
        interp_exports l_comp r_comp)
      -∗ stuff_to_prove γc (l_comp ⋈ ctxt) (r_comp ⋈ ctxt) reg.
    Proof.
      iIntros (Hreg Hints Hsep_l Hsep_r Hdom) "Hinterp (#Hspec & Hmem_l & Hmem_r & Hreg_l & Hreg_r & Hna & Hcfg)".
      iPoseProof (interp_link _ Hints Hsep_l Hsep_r Hdom) as "Hlink_exp".
      iSpecialize ("Hinterp" with "[Hspec Hna]").
      iModIntro. *)

  End interp_exports.

  Section refinement.
    Context {inv_preg: invGpreS Σ}.
    Context {mem_preg: gen_heapGpreS Addr Word Σ}.
    Context {reg_preg: gen_heapGpreS RegName Word Σ}.
    Context {seal_store_preg: sealStorePreG Σ}.
    Context {na_invg: na_invG Σ}.

    (** Lemmas to allocate memory and register map *)
    Lemma regspec_mapsto_alloc `{cfgSG Σ} e (σ : gmap RegName Word * gmap Addr Word) r (w : Word) :
      σ.1 !! r = None →
      spec_res e σ ==∗ spec_res e (<[r:=w]> σ.1,σ.2) ∗ r ↣ᵣ w.
    Proof.
      iIntros (Hnone) "Hσ".
      rewrite /spec_res /regspec_mapsto.
      iMod (own_update with "Hσ") as "[Hσ Hr]".
      { eapply auth_update_alloc,prod_local_update_2,prod_local_update_1.
        eapply (alloc_singleton_local_update (to_spec_map σ.1) r (1%Qp, to_agree w)).
        by rewrite lookup_fmap Hnone. done. }
      iModIntro. iFrame "Hr". rewrite -fmap_insert. iFrame.
    Qed.
    Lemma memspec_mapsto_alloc `{cfgSG Σ} e (σ : gmap RegName Word * gmap Addr Word) a (w : Word) :
      σ.2 !! a = None →
      spec_res e σ ==∗ spec_res e (σ.1,<[a:=w]> σ.2) ∗ a ↣ₐ w.
    Proof.
      iIntros (Hnone) "Hσ".
      rewrite /spec_res /memspec_mapsto.
      iMod (own_update with "Hσ") as "[Hσ Hr]".
      { eapply auth_update_alloc,prod_local_update_2,prod_local_update_2.
        eapply (alloc_singleton_local_update (to_spec_map σ.2) a (1%Qp, to_agree w)).
        by rewrite lookup_fmap Hnone. done. }
      iModIntro. iFrame "Hr". rewrite -fmap_insert. iFrame.
    Qed.
    Lemma regspec_alloc_big `{cfgSG Σ} e σ σ' σs :
      σ' ##ₘ σ →
      spec_res e (σ,σs) ==∗
      spec_res e (σ' ∪ σ,σs) ∗ ([∗ map] l ↦ v ∈ σ', l ↣ᵣ v).
    Proof.
      revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
      { rewrite left_id_L. auto. }
      iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
      decompose_map_disjoint.
      rewrite !big_opM_insert // -insert_union_l //.
      iMod (regspec_mapsto_alloc with "Hσ'σ") as "($ & $)".
        by apply lookup_union_None. done.
    Qed.
    Lemma memspec_alloc_big `{cfgSG Σ} e σ σ' σr :
      σ' ##ₘ σ →
      spec_res e (σr, σ) ==∗
      spec_res e (σr, map_union σ' σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↣ₐ v).
    Proof.
      revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
      { rewrite left_id_L. auto. }
      iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
      decompose_map_disjoint.
      rewrite !big_opM_insert //.
      assert (map_union (<[l:=v]> σ') σ = <[l:=v]> (map_union σ' σ)) as ->.
      { rewrite insert_union_l. auto. }
      iMod (memspec_mapsto_alloc with "Hσ'σ") as "($ & $)".
      simpl. rewrite lookup_union_None//. done.
    Qed.

    Context {cfgg : inG Σ (authR cfgUR)}.

    Definition fat_hypothesis (l_comp r_comp : component Symbols) r :=
      ∀ Hinv mem_heapg reg_heapg γc logrel_nais,
      let memg := MemG Σ Hinv mem_heapg in
      let regg := RegG Σ Hinv reg_heapg in
      let logrel_na_invs := Build_logrel_na_invs Σ na_invg logrel_nais  in
      let Hcfg := CFGSG Σ cfgg γc in
      ⊢ @stuff_to_prove memg regg logrel_na_invs Hcfg γc l_comp r_comp r.

      (* @interp_exports memg regg logrel_na_invs Hcfg l_comp r_comp. *)

    Lemma interp_adequacy_from_WP (comp_l comp_r : component Symbols) r conf (es: list cap_lang.expr) :
      fat_hypothesis comp_l comp_r r ->
      rtc erased_step (initial_state comp_l r) (of_val HaltedV :: es, conf) ->
      (∃ conf', rtc erased_step (initial_state comp_r r) ([of_val HaltedV], conf')).
    Proof.
      intros Hfat Hstep.
      cut (@adequate cap_lang NotStuck
              (Seq (Instr Executable))
              (r, segment comp_l)
              (λ v _, v = HaltedV → ∃ conf',
                rtc erased_step
                  (initial_state comp_r r)
                  ([of_val HaltedV], conf'))).
      { intros [adequate_result _]. apply adequate_result in Hstep; [ apply Hstep | done ]. }
      eapply (wp_adequacy Σ _).
      iIntros (Hinv κs).

      iMod (gen_heap_init (segment comp_l:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
      iMod (gen_heap_init (r:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
      iMod (seal_store_init) as (seal_storeg) "Hseal_store".
      iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

      iMod (own_alloc (● (Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅))
                        ⋅ ◯ ((Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅)) : cfgUR)))
        as (γc) "[Hcfg1 Hcfg2]".
      { apply auth_both_valid_discrete. split=>//. }

      pose memg := MemG Σ Hinv mem_heapg.
      pose regg := RegG Σ Hinv reg_heapg.
      pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
      pose Hcfg := CFGSG _ _ γc.

      (* Allocate the memory points tos *)
      iMod (regspec_alloc_big _ ∅ r ∅ with "[Hcfg1]") as "(Hcfg1 & Hregspec)".
        by apply map_disjoint_empty_r.
        rewrite /spec_res /= !/to_spec_map !fmap_empty //.
      rewrite right_id_L.
      iMod (memspec_alloc_big _ ∅ (segment comp_r) r with "[Hcfg1]") as "(Hcfg1 & Hmemspec)".
        by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
      rewrite right_id_L.

      specialize (Hfat Hinv mem_heapg reg_heapg γc logrel_nais).
      simpl in Hfat.

      (* Allocate the spec invariant *)
      iMod (inv_alloc specN _ (spec_inv ([Seq (Instr Executable)],(r,segment comp_r)) ) with "[Hcfg1]") as "#Hspec_∅".
      { iNext. iExists _,_. iFrame. iPureIntro. left. }
      iAssert (spec_ctx)%I as "#Hspec".
      { iExists _. iFrame "#". }

      iPoseProof (Hfat with "[Hmem Hmemspec Hreg Hregspec Hna Hcfg2]") as ">Hfat".
      { iFrame. iApply "Hspec". }

      iModIntro.
      iExists (fun σ κs => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
      iExists (fun _ => True)%I. iFrame.
      iApply wp_fupd. iApply wp_wand_r. iFrame.

      iIntros (v) "Hcond".
      destruct v;[|iModIntro;iIntros (Hcontr);done..].
      iDestruct ("Hcond" $! eq_refl) as (r') "(Hj & Hcond)".
      iInv specN as ">Hres" "Hcls". iDestruct "Hres" as (e' σ') "[Hown Hsteps]".
      iDestruct "Hsteps" as %Hsteps.
      iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
      iMod ("Hcls" with "[Hown]") as "_".
      { iNext. iExists _,_. eauto. }
      iModIntro.
      apply auth_both_valid_discrete in Hvalid as [Hincl Hvalid].
      iIntros (_).
      apply prod_included in Hincl as [Hincl Hincl']. simpl in *.
      revert Hincl; rewrite Excl_included =>Hincl.
      apply leibniz_equiv in Hincl as <-.
      iExists σ'. iPureIntro. apply Hsteps.
    Qed.
  End refinement.
End logrel.
