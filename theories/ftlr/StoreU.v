From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel monotone.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_StoreU.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* TODO: move somewhere *)
  Lemma isU_inv:
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality),
      (b ≤ a' < min a e)%Z
      → isU p = true
      → ((interp W) (inr (p, g, b, e, a))
         → ∃ p' : Perm, ⌜PermFlows (promote_perm p) p'⌝ ∗ read_write_cond a' p' interp
                        ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                                               ∧ ρ ≠ Revoked /\ (∀ g, ρ ≠ Static g))⌝)%I.
  Proof.
    intros. rewrite /interp fixpoint_interp1_eq /=. iIntros "H".
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]";try (iExists p'; iFrame; auto);[solve_addr|].
        iSplit;auto. iPureIntro; auto. eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H2; eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
      iPureIntro; eauto.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto; [solve_addr|].
        iSplit;auto. iPureIntro; auto. eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H1; eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto.
      iSplit;auto. iPureIntro; simpl in H1; eauto.
  Qed.

  (* Lemma region_open_next_perm' W ls l p : *)
  (*   l ∉ ls → (std_sta W) !! (countable.encode l) = Some (countable.encode Permanent) ->  *)
  (*   open_region_many ls W ∗ sts_full_world sts_std W ∗ uninitialized_cond l p -∗ *)
  (*                    ∃ v, sts_full_world sts_std W *)
  (*                         ∗ sts_state_std (countable.encode l) Permanent *)
  (*                         ∗ open_region_many (l :: ls) W *)
  (*                         ∗ l ↦ₐ[p] v *)
  (*                         ∗ ⌜p ≠ O⌝. *)
  (* Proof. *)
  (*   rewrite open_region_many_eq .  *)
  (*   iIntros (Hnin Htemp) "(Hopen & Hfull & Hun)". *)
  (*   rewrite /open_region_many_def /= /region_map_def. *)
  (*   rewrite /region_def /region. *)
  (*   iDestruct "Hopen" as (M) "(HM & % & Hpreds)". *)
  (*   destruct (proj1 (H3 (countable.encode l)) ltac:(eauto)) as [l' [X1 X2] ]. *)
  (*   eapply encode_inj in X1; subst l'. destruct X2 as [γp HX]. *)
  (*   iDestruct "Hun" as (γrel) "Hγpred". rewrite RELS_eq /RELS_def REL_eq /REL_def. *)
  (*   iDestruct (reg_in with "[$HM $Hγpred]") as %HMeq. *)
  (*   rewrite HMeq delete_list_insert; auto. *)
  (*   rewrite delete_list_delete; auto. *)
  (*   rewrite big_sepM_insert; [|by rewrite lookup_delete]. *)
  (*   iDestruct "Hpreds" as "[Hl Hpreds]". *)
  (*   iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. *)
  (*   1,3,4: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr. *)
  (*   1,2,3: rewrite Htemp in Hcontr; inversion Hcontr; apply countable.encode_inj in H5; done.     iDestruct "Hl" as (γpred' v p' ϕ) "(% & % & Hl & HX & HY & HZ)". *)
  (*   inversion H4; subst. *)
  (*   iExists v. iFrame. *)
  (*   iSplitL; auto. *)
  (*   iExists _. iFrame "∗ #". rewrite <- HMeq. auto. *)
  (* Qed. *)

  (* Lemma region_open_next_temp' W ls l p : *)
  (*   l ∉ ls → (std_sta W) !! (countable.encode l) = Some (countable.encode Temporary) ->  *)
  (*   open_region_many ls W ∗ sts_full_world sts_std W ∗ uninitialized_cond l p -∗ *)
  (*                    ∃ v, sts_full_world sts_std W *)
  (*                         ∗ sts_state_std (countable.encode l) Temporary *)
  (*                         ∗ open_region_many (l :: ls) W *)
  (*                         ∗ l ↦ₐ[p] v *)
  (*                         ∗ ⌜p ≠ O⌝. *)
  (* Proof. *)
  (*   rewrite open_region_many_eq .  *)
  (*   iIntros (Hnin Htemp) "(Hopen & Hfull & Hun)". *)
  (*   rewrite /open_region_many_def /= /region_map_def. *)
  (*   rewrite /region_def /region. *)
  (*   iDestruct "Hopen" as (M) "(HM & % & Hpreds)". *)
  (*   destruct (proj1 (H3 (countable.encode l)) ltac:(eauto)) as [l' [X1 X2] ]. *)
  (*   eapply encode_inj in X1; subst l'. destruct X2 as [γp HX]. *)
  (*   iDestruct "Hun" as (γrel) "Hγpred". rewrite RELS_eq /RELS_def REL_eq /REL_def. *)
  (*   iDestruct (reg_in with "[$HM $Hγpred]") as %HMeq. *)
  (*   rewrite HMeq delete_list_insert; auto. *)
  (*   rewrite delete_list_delete; auto. *)
  (*   rewrite big_sepM_insert; [|by rewrite lookup_delete]. *)
  (*   iDestruct "Hpreds" as "[Hl Hpreds]". *)
  (*   iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. *)
  (*   2,3,4: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr. *)
  (*   2,3,4: rewrite Htemp in Hcontr; inversion Hcontr; apply countable.encode_inj in H5; done.     iDestruct "Hl" as (γpred' v p' ϕ) "(% & % & Hl & HX & HY & HZ)". *)
  (*   inversion H4; subst. *)
  (*   iExists v. iFrame. *)
  (*   iSplitL; auto. *)
  (*   iExists _. iFrame "∗ #". rewrite <- HMeq. auto. *)
  (* Qed. *)

  Lemma region_open_next_uninit' W ls l p w :
    l ∉ ls → (std W) !! l = Some (Static {[l:=w]}) ->
    open_region_many ls W ∗ sts_full_world W ∗ read_write_cond l p interp -∗
                            sts_full_world W
                          ∗ sts_state_std l (Static {[l:=w]})
                          ∗ open_region_many (l :: ls) W
                          ∗ l ↦ₐ[p] w
                          ∗ ⌜p ≠ O⌝.
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp) "(Hopen & Hfull & Hun)".
    rewrite /open_region_many_def /= /region_map_def.
    rewrite /region_def /region.
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)".
    assert (is_Some (M !! l)) as [γp HX].
    { apply elem_of_gmap_dom. rewrite -H. apply elem_of_gmap_dom. eauto. }
    rewrite /read_write_cond rel_eq /rel_def.
    iDestruct "Hun" as (γrel) "[Hγpred BB]". rewrite RELS_eq /RELS_def REL_eq /REL_def.
    iDestruct (reg_in with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[ % [Hstate Hl] ]". destruct ρ.
    1,2,3,4,5: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
    1,2,3,4,5: try (rewrite Htemp in Hcontr; by inversion Hcontr). 
    iDestruct "Hl" as (γpred p0 φ Heq Hpers) "[#Hsaved Hl]". inversion Heq.
    iDestruct "Hl" as (v Hlookup Hneq) "[Hl _]". rewrite Htemp in Hcontr. inversion Hcontr. subst g.
    rewrite lookup_insert in Hlookup. inversion Hlookup. 
    iFrame. 
    repeat iSplitL; auto.
    iExists _,Mρ. iFrame "∗ #". subst. rewrite -HMeq.
    repeat iSplit;auto.
    iApply (region_map_delete_singleton with "Hpreds");eauto.
  Qed.

  Lemma region_open_next' W ls l ρ p:
    ρ <> Revoked ∧ (forall m, ρ = Static m -> (∃ w, m = {[l:=w]})) ->
    l ∉ ls → (std W) !! l = Some ρ ->
    open_region_many ls W ∗ sts_full_world W ∗ read_write_cond l p interp -∗
                     ∃ v, sts_full_world W
                          ∗ sts_state_std l ρ
                          ∗ open_region_many (l :: ls) W
                          ∗ l ↦ₐ[p] v
                          ∗ ⌜p ≠ O⌝.
  Proof.
    iIntros ([Hnotrevoked Hnotstatic] Hnotin Hstd) "[A [B C]]". destruct ρ; try congruence.
    - destruct (pwl p) eqn:Hpwl.
      + iDestruct (region_open_next_temp_pwl with "[$A $B $C]") as "X"; auto.
        iDestruct "X" as (v) "[A [B [C [D [E F]]]]]".
        iExists v. iFrame.
      + iDestruct (region_open_next_temp_nwl with "[$A $B $C]") as "X"; auto.
        iDestruct "X" as (v) "[A [B [C [D [E F]]]]]".
        iExists v. iFrame.
    - iDestruct (region_open_next_perm with "[$A $B $C]") as "X"; auto.
      iDestruct "X" as (v) "[A [B [C [D [E F]]]]]".
      iExists v. iFrame.
    - destruct Hnotstatic with g as [w Hw];auto. subst g. iExists w.
      iApply region_open_next_uninit'; eauto; iFrame.
  Qed.

  Lemma isU_limit_inv:
    ∀ (W : leibnizO WORLD) (a b e : Addr) (p : Perm) (g : Locality),
      (b ≤ a < e)%Z ->
      isU p = true ->
      ((interp W) (inr (p, g, b, e, a)) -∗
        ∃ p' : Perm,
          ⌜PermFlows (promote_perm p) p'⌝ ∗
          read_write_cond a p' interp ∧
          ⌜(∃ ρ : region_type, std W !! a = Some ρ
                               ∧ ρ ≠ Revoked ∧ (forall m, ρ = Static m -> (∃ w, m = {[a:=w]})))⌝)%I.
  Proof.
    intros. rewrite /interp fixpoint_interp1_eq /=. iIntros "H".
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]"; eauto.
        iExists p'. iSplit;auto. simpl. iFrame. iPureIntro. eexists. repeat split;eauto. done. 
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iSplit;auto;iFrame); eauto.
        split;auto;solve_addr.
        iPureIntro; destruct H2 as [-> | [-> | [ ? -> ] ] ]; eexists;repeat split;eauto; try done. 
        intros m Hm. inversion Hm. exists x. auto. 
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iSplit;auto;iFrame); eauto.
      split; eauto; solve_addr.
      iPureIntro; eauto. destruct H2 as [-> | [? ->] ]; eexists;repeat split;eauto;try done.
      intros m Hm; inversion Hm. eauto. 
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[D %]"; try (iExists p'; iSplit;auto;iFrame);auto.
        iPureIntro. eexists;repeat split;eauto; try done.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' ?) "[E %]"; try (iExists p'; iSplit;auto;iFrame);auto.
        split; eauto; solve_addr.
        iPureIntro; auto. destruct H2 as [-> | [-> | [? ->] ] ]; eexists;repeat split;eauto; try done.
        intros m Hm; inversion Hm;eauto. 
    - destruct g; auto.
      iDestruct "H" as "[B D]".
      iDestruct (extract_from_region_inv with "D") as (p' ?) "[E %]"; try (iExists p'; iSplit;auto;iFrame); eauto.
      split; eauto; solve_addr.
      iPureIntro; auto. destruct H2 as [-> | [? ->] ]; eexists;repeat split;eauto; try done.
      intros m Hm; inversion Hm;eauto. 
  Qed.

  Definition region_open_resources W l ls p φ v (bl : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std l ρ
    ∗ ⌜ρ ≠ Revoked ∧ (forall m, ρ ≠ Static m)⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ (if bl then monotonicity_guarantees_region ρ v p φ ∗ φ (W, v)
       else ▷ monotonicity_guarantees_region ρ v p φ ∗  ▷ φ (W, v) )
    ∗ rel l p φ)%I.

  Definition region_open_resources_uninit W l ls p (bl : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std l ρ
    ∗ ⌜ρ ≠ Revoked ∧ (forall m, ρ = Static m -> (∃ w, m = {[l:=w]}))⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ read_write_cond l p interp)%I.

  (* TODO: move upstream to Iris ?*)
  Instance if_persistent {PROP:bi} P Q (b: bool):
    Persistent P ->
    Persistent Q ->
    Persistent (PROP := PROP) (if b then P else Q).
  Proof.
    intros; destruct b; auto.
  Qed.

  (* TODO: move into logrel.v *)
  (* Quality of life lemma *)
  Global Instance future_world_pure g W W':
    IntoPure (@future_world Σ g W W')
             (match g with Global => related_sts_priv_world W W' | Local => related_sts_pub_world W W' end).
  Proof. red; intros. destruct g; auto. Qed.

  Lemma region_close_next_uninit_pwl W ls l φ p w v `{forall Wv, Persistent (φ Wv)}:
    l ∉ ls ->
    pwl p = true →
    sts_state_std l (Static {[l:=w]})
    ∗ open_region_many (l::ls) W
    ∗ l ↦ₐ[p] v
    ∗ ⌜p ≠ O⌝
    ∗ future_pub_mono φ v
    ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *)
    ∗ rel l p φ
    ∗ sts_full_world W
    ==∗ open_region_many ls (<s[ l := Temporary ]s> W) ∗ sts_full_world (<s[ l := Temporary ]s> W).
  Proof.
    rewrite open_region_many_eq rel_eq /open_region_many_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel & Hfull)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (sts_full_state_std with "Hfull Hstate") as "%".
    iDestruct (sts_update_std with "Hfull Hstate") as ">[Hfull Hstate]".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    iModIntro. iSplitR "Hfull".
    { iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "Hmap_def";
        first by rewrite lookup_delete.
      { simpl.
        iDestruct (region_map_insert_nonstatic Temporary with "Hpreds") as "Hpreds";auto. 
        iFrame. iExists Temporary. iFrame.
        iSplit;[iPureIntro;apply lookup_insert|]. 
        iExists γpred, p, _. iFrame "∗ #". repeat iSplitR; auto.
        iExists v. rewrite Hpwl. auto. }
      assert (Hpub: related_sts_pub_world W (<s[l:=Temporary]s>W)).
      { eapply (uninitialized_related_sts_pub_world l W); eauto. }
      iDestruct (region_map_monotone $! Hpub with "Hmap_def") as "HMdef"; eauto.
      iExists M,(<[l:=Temporary]>Mρ); iFrame.
      assert (l ∈ dom (gset Addr) M) as Hin.
      { rewrite -H1. apply elem_of_gmap_dom. eauto. }
      repeat rewrite dom_insert_L. 
      repeat iSplit;[iPureIntro..|];[rewrite H1;set_solver|rewrite H2;set_solver|].
      rewrite -delete_list_delete;auto. rewrite -delete_list_insert; auto. rewrite -HMeq. 
      rewrite delete_list_insert; auto. }
    iFrame. 
  Qed.

  Lemma region_close_next_uninit_nwl W ls l φ p w v `{forall Wv, Persistent (φ Wv)}:
    l ∉ ls ->
    pwl p = false →
    sts_state_std l (Static {[l:=w]})
    ∗ open_region_many (l::ls) W
    ∗ l ↦ₐ[p] v
    ∗ ⌜p ≠ O⌝
    ∗ future_priv_mono φ v
    ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *)
    ∗ rel l p φ
    ∗ sts_full_world W
    ==∗ open_region_many ls (<s[ l := Temporary ]s> W) ∗ sts_full_world (<s[ l := Temporary ]s> W).
  Proof.
    rewrite open_region_many_eq rel_eq /open_region_many_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel & Hfull)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (sts_full_state_std with "Hfull Hstate") as "%".
    iDestruct (sts_update_std with "Hfull Hstate") as ">[Hfull Hstate]".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    iModIntro. iSplitR "Hfull".
    { iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "Hmap_def";
        first by rewrite lookup_delete.
      { simpl.
        iDestruct (region_map_insert_nonstatic Temporary with "Hpreds") as "Hpreds";auto. 
        iFrame. iExists Temporary. iFrame.
        iSplit;[iPureIntro;apply lookup_insert|]. 
        iExists γpred, p, _. iFrame "∗ #". repeat iSplitR; auto.
        iExists v. rewrite Hpwl. auto. }
      assert (Hpub: related_sts_pub_world W (<s[l:=Temporary]s>W)).
      { eapply (uninitialized_related_sts_pub_world l W); eauto. }
      iDestruct (region_map_monotone $! Hpub with "Hmap_def") as "HMdef"; eauto.
      iExists M,(<[l:=Temporary]>Mρ); iFrame.
      assert (l ∈ dom (gset Addr) M) as Hin.
      { rewrite -H1. apply elem_of_gmap_dom. eauto. }
      repeat rewrite dom_insert_L. 
      repeat iSplit;[iPureIntro..|];[rewrite H1;set_solver|rewrite H2;set_solver|].
      rewrite -delete_list_delete;auto. rewrite -delete_list_insert; auto. rewrite -HMeq. 
      rewrite delete_list_insert; auto. }
    iFrame. 
  Qed.

  Lemma region_close_next_uninit W ls l φ p w v `{forall Wv, Persistent (φ Wv)}:
    l ∉ ls ->
    sts_state_std l (Static {[l:=w]})
    ∗ open_region_many (l::ls) W
    ∗ l ↦ₐ[p] v
    ∗ ⌜p ≠ O⌝
    ∗ (if pwl p then future_pub_mono else future_priv_mono) φ v 
    ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *)
    ∗ rel l p φ
    ∗ sts_full_world W
    ==∗ open_region_many ls (<s[ l := Temporary ]s> W) ∗ sts_full_world (<s[ l := Temporary ]s> W).
  Proof.
    intros Hnotin. destruct (pwl p) eqn:Hpwl.
    - iApply region_close_next_uninit_pwl; auto.
    - iApply region_close_next_uninit_nwl; auto.
  Qed.

  Global Instance exi_uninit_eqdec l : Decision (∃ w : leibnizO Word, ρ' = Static {[l:=w]}).
  Proof. destruct 0;[right|right|right|];[intros [? ?];done..|].
         destruct (g !! l) eqn:Hsome;[|right];[|intros [? ?];simplify_map_eq].
         destruct (decide (g = {[l:=w]}));[left|right];subst;eauto. intros [? ?]. simplify_map_eq. 
  Qed. 

  Lemma storeU_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (rdst : RegName) (offs rsrc : Z + RegName):
    ftlr_instr W r p p' g b e a w (StoreU rdst offs rsrc) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion [Hnotrevoked Hnotstatic] HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    assert (Hsome': forall x, is_Some (<[PC:=inr (p, g, b, e, a)]> r !! x)).
    { intros. destruct (reg_eq_dec x PC).
      - subst x. rewrite lookup_insert; eauto.
      - rewrite lookup_insert_ne; auto. }
    destruct (Hsome' rdst) as [wdst Hrdst].
    iDestruct (region_open_prepare with "Hr") as "Hr".
    assert (Hwsrc: exists wsrc, word_of_argument (<[PC:=inr (p, g, b, e, a)]> r) rsrc = Some wsrc).
    { destruct rsrc; eauto.
      simpl; eapply Hsome'. }
    destruct Hwsrc as [wsrc Hwsrc].

    iAssert (∃ (mem: gmap Addr (Perm * Word)),
                ⌜let wx := <[PC:=inr (p, g, b, e, a)]> r !! rdst in
                match wx with
                | Some (inr (px, gx, bx, ex, ax)) =>
                  if isU px && canStoreU px wsrc
                  then let moffs := z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs in
                       match moffs with
                       | Some zoffs =>
                         let ma' := verify_access (StoreU_access bx ex ax zoffs) in
                         match ma' with
                         | Some a' =>
                           let mpw := mem !! a' in
                           match mpw with
                           | Some (p'', w') => PermFlows (promote_perm px) p''
                           | None => False
                           end
                         | None => True
                         end
                       | None => True
                       end
                  else True
                | _ => True
                end⌝ ∗
                (▷ let wx := <[PC:=inr (p, g, b, e, a)]> r !! rdst in
                match wx with
                | Some (inr (px, gx, bx, ex, ax)) =>
                  if isU px && canStoreU px wsrc
                  then let moffs := z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs in
                       match moffs with
                       | Some zoffs =>
                         let ma' := verify_access (StoreU_access bx ex ax zoffs) in
                         match ma' with
                         | Some a' =>
                           if addr_eq_dec ax a' then
                             let mpw := mem !! a' in
                             match mpw with
                             | Some (p'', w') =>
                               ⌜mem = if addr_eq_dec a a' then (<[a:=(p'',w)]> ∅) else <[a:=(p',w)]> (<[a':=(p'',w')]> ∅)⌝ ∗ sts_full_world W ∗ if addr_eq_dec a a' then open_region_many [a] W else region_open_resources_uninit W a' [a] p'' true
                             | None => ⌜False⌝
                             end
                           else
                             let mpw := mem !! a' in
                             match mpw with
                             | Some (p'', w') =>
                               ⌜mem = if addr_eq_dec a a' then (<[a:=(p'',w)]> ∅) else <[a:=(p',w)]> (<[a':=(p'',w')]> ∅)⌝ ∗ sts_full_world W ∗ if addr_eq_dec a a' then open_region_many [a] W else region_open_resources W a' [a] p'' interpC w' true
                             | None => ⌜False⌝
                             end
                         | None => True
                         end
                       | None => True
                       end
                  else True
                | _ => True
                end) ∗ ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗ ⌜mem !! a = Some (p', w)⌝)%I
        with "[Ha Hsts Hr]" as "H".
    { rewrite Hrdst. destruct wdst; auto.
      - iDestruct (memMap_resource_1 with "Ha") as "H".
        iExists _; iFrame; auto. rewrite lookup_insert; auto.
      - destruct_cap c. destruct (isU c && canStoreU c wsrc) eqn:HisU.
        + destruct (z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs) eqn:Hzof.
          * destruct (verify_access (StoreU_access c2 c1 c0 z)) eqn:Hver.
            -- apply andb_true_iff in HisU. destruct HisU as [HisU Hcan].
               assert (Hdstne: rdst <> PC).
               { red; intros; subst rdst.
                 rewrite lookup_insert in Hrdst. inv Hrdst.
                 destruct Hp as [-> | [-> | [-> ->] ] ]; simpl in HisU; inv HisU. }
               iDestruct ("Hreg" $! rdst Hdstne) as "Hinvdst"; auto.
               rewrite lookup_insert_ne in Hrdst; auto.
               rewrite /RegLocate Hrdst.
               eapply verify_access_spec in Hver.
               destruct Hver as [HA [HB [HC HD] ] ].
               destruct (addr_eq_dec c0 a0).
               ++ (* Uninitialized stuff, HERE BE DRAGONS *)
                  subst c0. destruct (addr_eq_dec a a0).
                  ** subst a0. iDestruct (memMap_resource_1 with "Ha") as "H".
                     iExists _; iFrame; auto.
                     rewrite lookup_insert; auto.
                     iSplitR; iFrame; auto.
                     iDestruct (isU_limit_inv _ a with "Hinvdst") as "H"; auto.
                     iDestruct "H" as (p'') "[% [Hun %]]".
                     iAssert (⌜p' = p''⌝%I) as "%".
                     { iDestruct (rel_agree with "[Hinva Hun]") as "[% A]".
                       iSplit; [iExact "Hinva"| iExact "Hun"]. auto. }
                     subst p'. iPureIntro. auto.
                  ** iDestruct (isU_limit_inv _ a0 with "Hinvdst") as "H"; auto.
                     iDestruct "H" as (p'') "[% [Hun %]]".
                     destruct H0 as [ρ' [X [Y Z] ] ].
                     iDestruct (region_open_next' with "[$Hsts $Hr]") as "HH"; eauto.
                     { apply not_elem_of_cons. split; eauto.
                       apply not_elem_of_nil. }
                     iDestruct "HH" as (wa0) "(Hsts & Hstate & Hr & Ha0 & %)".
                     iDestruct (memMap_resource_2ne with "[$Ha $Ha0]") as "H"; auto.
                     iExists (<[a:=(p', w)]> (<[a0:=(_, wa0)]> ∅)).
                     rewrite lookup_insert_ne; auto. rewrite lookup_insert.
                     
                     iFrame. iSplitR; auto.
                     iSplitL; [iSplitR;auto|].
                     iExists _. iFrame. repeat iSplit;auto.  
                     iFrame "∗ #"; auto. rewrite lookup_insert; auto.
               ++ iDestruct (isU_inv _ a0 with "Hinvdst") as "H"; auto.
                  { split; solve_addr. }
                  iDestruct "H" as (p'') "[% [X %]]".
                  destruct (addr_eq_dec a a0).
                  ** subst a0. iDestruct (memMap_resource_1 with "Ha") as "H".
                     iExists _; iFrame; auto.
                     rewrite lookup_insert; auto.
                     iFrame. iSplitR; auto.
                     iAssert (⌜p' = p''⌝)%I as %Hpeq.
                     { rewrite /read_write_cond.
                       iDestruct (rel_agree a p' p'' with "[$Hinva $X]") as "[$ A]". }
                     subst p'. iPureIntro. auto.
                  ** destruct H0 as [ρ' [X [Y Z ] ] ].
                     iDestruct (region_open_next with "[$Hsts $Hr]") as "HH"; eauto.
                     { intros [g' Hcontr]. subst. specialize (Z g'). contradiction. }
                     { apply not_elem_of_cons. split; auto.
                       apply not_elem_of_nil. }
                     iDestruct "HH" as (w') "(Hsts & Hstate & Hr & Ha' & % & Hmono & HX)".
                     iDestruct (memMap_resource_2ne with "[$Ha $Ha']") as "H"; auto.
                     iExists (<[a:=(p', w)]> (<[a0:=(p'', w')]> ∅)).
                     rewrite lookup_insert_ne; auto. rewrite lookup_insert.
                     iFrame. iSplitR; auto.
                     iSplitL; auto. iNext. iSplitR; auto.
                     iExists ρ'. iFrame; auto. rewrite lookup_insert; auto.
            -- iDestruct (memMap_resource_1 with "Ha") as "H".
               iExists _; iFrame; auto. rewrite lookup_insert; auto.
          * iDestruct (memMap_resource_1 with "Ha") as "H".
            iExists _; iFrame; auto. rewrite lookup_insert; auto.
        + iDestruct (memMap_resource_1 with "Ha") as "H".
          iExists _; iFrame; auto. rewrite lookup_insert; auto. }
    
    iDestruct "H" as (mem) "[% [A [B %]]]".
    iApply (wp_storeU with "[Hmap B]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. }
    { rewrite Hrdst. rewrite Hrdst in H. destruct wdst; auto.
      destruct_cap c. destruct (isU c && canStoreU c wsrc); auto.
      destruct (z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs); auto.
      destruct (verify_access (StoreU_access c2 c1 c0 z)); auto.
      destruct (mem !! a0); auto. destruct p0.
      eapply PermFlows_trans; eauto. destruct c; econstructor. }
    { iFrame. }
    iNext. iIntros (r' mem' v) "[% [B C]]".
    inv H1.

    { rewrite Hrdst in H2. inv H2. rewrite Hwsrc in H3; inv H3.
      rewrite Hrdst H4 H5 H6 H7 /=.
      rewrite Hrdst H4 H5 H6 H7 /= in H.
      iAssert (((fixpoint interp1) W) w0) as "#Hw0".
      { rewrite /word_of_argument in Hwsrc.
        destruct rsrc; inv Hwsrc.
        - rewrite !fixpoint_interp1_eq /=; auto.
        - destruct (reg_eq_dec PC r0).
          + subst r0. rewrite lookup_insert in H2; inv H2.
            rewrite (fixpoint_interp1_eq W (inr _)) /=.
            iAssert (□ exec_cond W b e g p (fixpoint interp1))%I as "HinvPC".
            { iAlways. rewrite /exec_cond.
              iIntros (a'' r'' W'' Hin) "#Hfuture".
              iNext. rewrite /interp_expr /=.
              iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
              iSplitR; eauto.
              iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
              iAlways. (* iExists p'. iSplitR; auto. *) simpl.
              iDestruct "Hfuture" as %Hfuture.
              iApply (big_sepL_mono with "Hinv"); intros; simpl.
              iIntros "H". iDestruct "H" as (? ?) "[HA %]". iExists _; iSplit;eauto. iFrame. iPureIntro. 
              destruct (pwl p) eqn:Hpwlp.
              - eapply region_state_pwl_monotone; eauto.
                destruct Hp as [-> | [-> | [-> ->] ] ]; simpl in Hpwlp; try congruence.
              - destruct g; [eapply region_state_nwl_monotone_nl; eauto| eapply region_state_nwl_monotone; eauto].
            }  
            destruct Hp as [-> | [-> | [-> ->] ] ]; iFrame "#"; auto.
          + rewrite lookup_insert_ne in H2; auto.
            iDestruct ("Hreg" $! r0 ltac:(auto)) as "HX"; auto.
            rewrite /RegLocate H2. auto. }
      assert (Hnedst: rdst <> PC).
      { red; intro; subst rdst. rewrite lookup_insert in Hrdst.
        inv Hrdst. destruct Hp as [-> | [-> | [-> ->] ] ]; simpl in H4; inv H4. }
      iDestruct ("Hreg" $! rdst Hnedst) as "Hwdst".
      rewrite lookup_insert_ne in Hrdst; auto.
      rewrite /RegLocate Hrdst.
      iAssert (|==> ∃ W', region W' ∗ ⌜related_sts_pub_world W W'⌝ ∗ sts_full_world W' ∗ if addr_eq_dec a0 a' then match (a0 + 1)%a with | Some a'' => ((fixpoint interp1) W') (inr (p0, g0, b0, e0, a'')) | None => True end else True)%I with "[A B Hmono Hstate]" as ">HW".
      { destruct (addr_eq_dec a0 a').
        - subst a0. destruct (a' + 1)%a as [a''|] eqn:Hap1; try tauto.
          destruct (mem !! a') as [(p'', w'')|]; auto.
          iDestruct "A" as "[% [Hsts A]]".
          destruct (addr_eq_dec a a').
          + iModIntro; subst a'; subst mem.
            iDestruct (region_open_prepare with "A") as "A".
            rewrite insert_insert.
            iDestruct (memMap_resource_1 with "B") as "B".
            rewrite lookup_insert in H8; inv H8.
            rewrite lookup_insert in H0; inv H0.
            iDestruct (region_close _ _ (λ Wv : (WORLD * Word), interp Wv.1 Wv.2)
                         with "[$A $B $Hstate Hmono]") as "B"; eauto.
            { destruct ρ; auto; congruence. }
            { iFrame "#". iSplitR; auto.
              destruct (decide (ρ = Temporary ∧ pwl p' = true)).
              - rewrite /future_pub_mono /=. iAlways.
                iIntros (W1 W2) "% #A".
                iApply interp_monotone; auto.
              - rewrite /future_priv_mono /=. iAlways.
                iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                destruct w0; auto.
                eapply not_and_r in n. destruct_cap c.
                simpl. destruct c3; auto. simpl in H5.
                destruct (pwlU p0) eqn:HwplU; intros; try congruence.
                destruct n.
                * iAssert (⌜g0 = Local⌝)%I as %->.
                  { rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                    destruct p0; simpl in HwplU; try congruence; destruct g0; simpl; auto. }
                  rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                  iAssert (⌜region_state_U_pwl W a⌝)%I as %Hρ.
                  { destruct p0; simpl in H,H4,H5,H6,HwplU; try congruence.
                    - simpl. iDestruct "Hwdst" as "[YA YB]".
                      destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                      iDestruct (extract_from_region_inv with "YB") as (pp ?) "[E %]"; auto.
                      split; try solve_addr. rewrite /max; destruct (Addr_le_dec b0 a); solve_addr.
                    - simpl. iDestruct "Hwdst" as "[YA YC]".
                      destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                      iDestruct (extract_from_region_inv with "YC") as (pp ?) "[E %]"; auto.
                      split; try solve_addr. rewrite /max; destruct (Addr_le_dec b0 a); solve_addr. }
                  destruct Hρ as [Hρ | Hρ]; rewrite Hregion in Hρ; inversion Hρ; try subst ρ; congruence.
                * assert (HpwlU2: pwlU p' = true).
                  { destruct p0; simpl in H6; simpl in HwplU; try congruence; destruct p'; rewrite /PermFlows in H; inv H; simpl in H0; try congruence; reflexivity. }
                  destruct Hp as [-> | [-> | [-> ->] ] ]; destruct p'; simpl in HpwlU2; simpl in H0; try congruence; inv Hfp. }
            iExists W. iFrame. iSplitR.
            * iPureIntro.
              rewrite /related_sts_pub_world; eapply related_sts_pub_refl_world.
            * rewrite !(fixpoint_interp1_eq W (inr (p0,_,_,_,_))) !interp1_eq.
              destruct (perm_eq_dec p0 O); [subst p0; simpl in H4; congruence|].
              destruct (perm_eq_dec p0 E); [subst p0; simpl in H4; congruence|].
              iDestruct "Hwdst" as "[A1 [% A4]]".
              rewrite H4. iFrame "%".
              destruct g0; simpl; iFrame "#". eapply verify_access_spec in H7.
              destruct H7 as [A1 [A2 [A3 A4] ] ].
              replace (max b0 a) with a by solve_addr.
              replace (min a e0) with a by solve_addr.
              replace (min a'' e0) with a'' by solve_addr.
              iSplit.
              { rewrite (isWithin_region_addrs_decomposition a a'' b0 a''); [|solve_addr].
                iApply big_sepL_app. iFrame "#".
                iApply big_sepL_app.
                replace (region_addrs a'' a'') with (@nil Addr) by (rewrite /region_addrs region_size_0 /=; auto; solve_addr).
                iSplitL.
                - replace (region_addrs a a'') with (a::nil).
                  + iApply big_sepL_cons. iSplitL; [|iApply big_sepL_nil; auto].
                    iDestruct (extract_from_region_inv a e0 a with "A4") as (pp ?) "[X1 %]"; [solve_addr|].
                    iExists pp. iSplit;auto. iSplitL; auto.
                    iPureIntro; auto. 
                    destruct (pwlU p0) eqn:Hp0.
                    { rewrite /region_state_U_pwl in H2. destruct H2; auto. 
                      destruct H2. 
                      eelim Hnotstatic. congruence. }
                    { rewrite /region_state_U_pwl in H2. destruct H2; auto.
                      destruct H2; auto. destruct H2. eelim Hnotstatic. congruence. }
                  + rewrite /region_addrs /region_size /=.
                    replace (a'' - a)%Z with 1%Z by solve_addr.
                    simpl. auto.
                - iApply big_sepL_nil; auto. }
              { replace (max b0 a'') with a'' by solve_addr.
                iApply (big_sepL_submseteq with "A4").
                rewrite (region_addrs_decomposition a a e0); [|solve_addr].
                replace ^(a + 1)%a with a'' by solve_addr.
                eapply submseteq_inserts_l.
                eapply submseteq_cons. auto. }
          + subst mem. iDestruct "A" as (ρ') "[A1 [ [% %] [A2 [% #A3]]]]".
            iDestruct (sts_full_state_std with "[$Hsts] [$A1]") as "%".
            (* destruct (region_type_EqDecision ρ' Uninitialized). *)
            destruct (decide (exists w, ρ' = Static {[a':=w]})). 
            * destruct e1 as [? e1]. subst ρ'. rewrite -(insert_delete _ a' (p'0, w0)).
              rewrite delete_insert_ne; auto. rewrite delete_insert; auto.
              iDestruct (memMap_resource_2ne with "B") as "[B1 B2]"; auto.
              rewrite lookup_insert_ne in H8; auto.
              rewrite lookup_insert in H8; inv H8.
              iDestruct (region_close_next_uninit with "[$A1 $A2 $B1 $A3 $Hw0 $Hsts]") as "HX".
              { eapply not_elem_of_cons; split; auto.
                eapply not_elem_of_nil. }
              { iSplitR; auto. simpl. destruct (pwl p'0) eqn:Hpwl'.
                - rewrite /future_pub_mono /=. iAlways.
                  iIntros (W1 W2) "% #A".
                  iApply interp_monotone; auto.
                - rewrite /future_priv_mono /=. iAlways.
                  iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                  destruct w0; auto.
                  destruct_cap c. simpl. destruct c3; auto.
                  simpl in H5. destruct (pwlU p0) eqn:HpwlU; try congruence.
                  exfalso. destruct p0; simpl in H,H4,HpwlU; try congruence; 
                  destruct p'0; simpl in *; inv H; congruence. } 
              iDestruct "HX" as ">[Hregion Hfull]".
              iDestruct (region_open_prepare with "Hregion") as "Hregion".
              assert (related_sts_pub_world W (<s[a':=Temporary]s>W)).
              { eapply (uninitialized_related_sts_pub_world); eauto. }
              iDestruct (region_close with "[$Hregion $B2 $Hstate $Hmono]") as "HH"; eauto.
              { destruct ρ;auto; congruence. }
              { iSplitR; auto. iFrame "∗ #". iNext.
                iApply interp_monotone; auto. }
              iModIntro. iExists _. iFrame "∗ %".
              iDestruct (interp_monotone with "[] [$Hwdst]") as "#Hwdst'"; [iPureIntro; eauto|].
              rewrite !(fixpoint_interp1_eq (<s[a':=_]s> W)) !interp1_eq.
              destruct (perm_eq_dec p0 O); [subst p0; simpl in H8; discriminate|].
              destruct (perm_eq_dec p0 E); [subst p0; simpl in H8; discriminate|].
              iDestruct "Hwdst'" as "[A1 [% A4]]".
              rewrite H4. iFrame "%".
              destruct g0; simpl; iFrame "#". eapply verify_access_spec in H7.
              destruct H7 as [A1 [A2 [A3 A4] ] ].
              replace (max b0 a') with a' by solve_addr.
              replace (min a' e0) with a' by solve_addr.
              replace (min a'' e0) with a'' by solve_addr.
              iSplit.
              { rewrite (isWithin_region_addrs_decomposition a' a'' b0 a''); [|solve_addr].
                iApply big_sepL_app. iFrame "#".
                iApply big_sepL_app.
                replace (region_addrs a'' a'') with (@nil Addr) by (rewrite /region_addrs region_size_0 /=; auto; solve_addr).
                iSplitL.
                - replace (region_addrs a' a'') with (a'::nil).
                  + iApply big_sepL_cons. iSplitL; [|iApply big_sepL_nil; auto].
                    iDestruct (extract_from_region_inv a' e0 a' with "A4") as (pp ?) "[X1 %]"; [solve_addr|].
                    iExists pp; iSplit;auto. iSplitL; auto.
                    iPureIntro; auto. 
                    destruct (pwlU p0) eqn:Hp0; auto.
                    { rewrite /region_state_pwl /std_update /std /=.
                      rewrite lookup_insert. reflexivity. }
                    { rewrite /region_state_pwl /std_update /std /=.
                      rewrite lookup_insert. auto. }
                  + rewrite /region_addrs /region_size /=.
                    replace (a'' - a')%Z with 1%Z by solve_addr.
                    simpl. auto.
                - iApply big_sepL_nil; auto. }
              { replace (max b0 a'') with a'' by solve_addr.
                iApply (big_sepL_submseteq with "A4").
                rewrite (region_addrs_decomposition a' a' e0); [|solve_addr].
                replace ^(a' + 1)%a with a'' by solve_addr.
                eapply submseteq_inserts_l.
                eapply submseteq_cons. auto. }
            * rewrite -(insert_delete _ a' (p'0, w0)).
              rewrite delete_insert_ne; auto. rewrite delete_insert; auto.
              iDestruct (memMap_resource_2ne with "B") as "[B1 B2]"; auto.
              rewrite lookup_insert_ne in H8; auto.
              rewrite lookup_insert in H8; inv H8.
              iDestruct (region_close_next with "[$A1 $A2 $B1 $A3 $Hw0]") as "HX"; auto.
              { intros [g' Hcontr]. specialize (H2 g'). apply H2 in Hcontr as Hcontr'. destruct Hcontr'. subst g'.
                simplify_map_eq.
                assert (∃ w : leibnizO Word, Static {[a' := x]} = Static {[a' := w]});eauto. }
              { eapply not_elem_of_cons; split; auto.
                eapply not_elem_of_nil. }
              { iSplitR; auto. rewrite /monotonicity_guarantees_region.
                destruct ρ'; auto.
                - destruct (pwl p'0) eqn:Hpwl'.
                  + rewrite /future_pub_mono /=. iAlways.
                    iIntros (W1 W2) "% #A".
                    iApply interp_monotone; auto.
                  + rewrite /future_priv_mono /=. iAlways.
                    iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                    destruct w0; auto.
                    destruct_cap c. simpl. destruct c3; auto.
                    simpl in H7. destruct (pwlU p0) eqn:HpwlU; try congruence; exfalso;
                    destruct p0; simpl in H,H4,HpwlU; try congruence; 
                      destruct p'0; simpl in *; inv H; congruence.
                - simpl. rewrite /future_priv_mono /=. iAlways.
                  iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                  destruct w0; auto. destruct_cap c. simpl. destruct c3; auto.
                  simpl in H5. destruct p0; simpl in H4, H5; try (inv H4; inv H5; fail).
                  + rewrite (fixpoint_interp1_eq W (inr (URWL,_,_,_,_))) /=.
                    destruct g0; auto. iDestruct "Hwdst" as "[Y1 Y2]".
                    iDestruct (extract_from_region_inv _ _ a' with "Y2") as (pp ?) "[Y3 %]".
                    { eapply verify_access_spec in H7.
                      destruct H7 as [X1 [X2 [X3 X4] ] ].
                      solve_addr. }
                    destruct H11;[|destruct H11]; rewrite H11 in H9; discriminate. 
                  + rewrite (fixpoint_interp1_eq W (inr (URWLX,_,_,_,_))) /=.
                    destruct g0; auto. iDestruct "Hwdst" as "[Y1 Y3]".
                    iDestruct (extract_from_region_inv _ _ a' with "Y3") as (pp ?) "[Y4 %]".
                    { eapply verify_access_spec in H7.
                      destruct H7 as [X1 [X2 [X3 X4] ] ].
                      solve_addr. }
                    destruct H11;[|destruct H11]; rewrite H11 in H9; discriminate. }
              iDestruct (region_open_prepare with "HX") as "Hregion".
              iDestruct (region_close with "[$Hregion $B2 $Hstate $Hmono]") as "HH"; eauto.
              { destruct ρ;auto;congruence. }
              iModIntro. iExists _. iFrame "∗ %". iSplit.
              { iPureIntro. rewrite /related_sts_pub_world; eapply related_sts_pub_refl_world. }
              { rewrite !(fixpoint_interp1_eq W (inr (p0,_,_,_,_))) !interp1_eq.
                destruct (perm_eq_dec p0 O); [subst p0; simpl in *; congruence|].
                destruct (perm_eq_dec p0 E); [subst p0; simpl in *; congruence|].
                iDestruct "Hwdst" as "[A1 [% A4]]".
                rewrite H4. iFrame "%".
                destruct g0; simpl; iFrame "#". eapply verify_access_spec in H7.
                destruct H7 as [A1 [A2 [A3 A4] ] ].
                replace (max b0 a') with a' by solve_addr.
                replace (min a' e0) with a' by solve_addr.
                replace (min a'' e0) with a'' by solve_addr.
                iSplit.
                { rewrite (isWithin_region_addrs_decomposition a' a'' b0 a''); [|solve_addr].
                  iApply big_sepL_app. iFrame "#".
                  iApply big_sepL_app.
                  replace (region_addrs a'' a'') with (@nil Addr) by (rewrite /region_addrs region_size_0 /=; auto; solve_addr).
                  iSplitL.
                  - replace (region_addrs a' a'') with (a'::nil).
                    + iApply big_sepL_cons. iSplitL; [|iApply big_sepL_nil; auto].
                      iDestruct (extract_from_region_inv a' e0 a' with "A4") as (pp Hflowspp) "[X1 %]"; [solve_addr|].
                      iExists pp; iSplit;auto. iSplitL; auto.
                      iPureIntro;auto.
                      destruct (pwlU p0) eqn:Hp0; auto.
                      { destruct H7; auto. elim n0.
                        rewrite H9 in H7; inv H7. exists x. inversion H11. eauto. }
                      { destruct H7; auto. destruct H7; auto. elim n0. destruct H7. 
                        rewrite H7 in H9; inv H9. eauto. }
                    + rewrite /region_addrs /region_size /=.
                      replace (a'' - a')%Z with 1%Z by solve_addr.
                      simpl. auto.
                  - iApply big_sepL_nil; auto. }
                { replace (max b0 a'') with a'' by solve_addr.
                  iApply (big_sepL_submseteq with "A4").
                  rewrite (region_addrs_decomposition a' a' e0); [|solve_addr].
                  replace ^(a' + 1)%a with a'' by solve_addr.
                  eapply submseteq_inserts_l.
                  eapply submseteq_cons. auto. } }
        - iModIntro. destruct (mem !! a') as [(p'', w'')|]; auto.
          iDestruct "A" as "[% [Hsts A]]".
          destruct (addr_eq_dec a a').
          + subst a'. subst mem.
            iDestruct (region_open_prepare with "A") as "A".
            rewrite insert_insert.
            iDestruct (memMap_resource_1 with "B") as "B".
            rewrite lookup_insert in H8,H0.
            inversion H8; inversion H0. subst p'' w p'0.
            iDestruct (region_close _ _ (λ Wv : WORLD * Word, interp Wv.1 Wv.2) with "[$A $B $Hstate Hmono]") as "B"; eauto.
            { destruct ρ;auto;congruence. }
            { iSplitR;auto. iFrame "#". simpl.
              destruct (decide (ρ = Temporary ∧ pwl p' = true)).
              - rewrite /future_pub_mono /=. iAlways.
                 iIntros (W1 W2) "% #A".
                 iApply interp_monotone; auto.
              - rewrite /future_priv_mono /=. iAlways.
                 iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                 destruct w0; auto.
                 eapply not_and_r in n0. destruct_cap c.
                 simpl. destruct c3; auto. simpl in H5.
                 destruct (pwlU p0) eqn:HwplU; intros; try congruence.
                 destruct n0.
                 * iAssert (⌜g0 = Local⌝)%I as %->.
                    { rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                      destruct p0; simpl in HwplU; try congruence; destruct g0; simpl; auto. }
                    rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                    iAssert (⌜region_state_U_pwl W a⌝)%I as %Hρ.
                    { destruct p0; simpl in H4; simpl in HwplU; try congruence.
                      - simpl. iDestruct "Hwdst" as "[YA YB]".
                        destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                        iDestruct (extract_from_region_inv _ _ a with "YA") as (pp ?) "[E %]"; auto.
                        split; try solve_addr. rewrite /min; destruct (Addr_le_dec a0 e0); solve_addr.
                        iPureIntro. rewrite /region_state_U_pwl.
                        rewrite /region_state_pwl in H6; auto.
                      - simpl. iDestruct "Hwdst" as "[YA YB]".
                        destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                        iDestruct (extract_from_region_inv _ _ a with "YA") as (pp ?) "[E %]"; auto.
                        split; try solve_addr. rewrite /min; destruct (Addr_le_dec a0 e0); solve_addr.
                        iPureIntro. rewrite /region_state_U_pwl.
                        rewrite /region_state_pwl in H6; auto. }
                    destruct Hρ as [Hρ | Hρ]; rewrite Hregion in Hρ; inversion Hρ; try subst ρ; congruence.
                  * assert (HpwlU2: pwlU p' = true).
                    { destruct p0; simpl in H5; simpl in HwplU; try congruence; destruct p'; rewrite /PermFlows in H; inv H; simpl in H0; try congruence; reflexivity. }
                    exfalso. destruct Hp as [-> | [-> | [-> ->] ] ]; destruct p'; simpl in HpwlU2; simpl in *; try congruence; inv Hfp. }
            
            iExists W. iFrame. iPureIntro. apply related_sts_pub_refl_world.
          + subst mem. rewrite insert_commute; auto.
            rewrite insert_insert.
            iDestruct (memMap_resource_2ne with "B") as "[B C]"; auto.
            rewrite /region_open_resources.
            iDestruct "A" as (ρ') "[A1 [ [% %] [A2 [% [[A3 #Hw'] #A4]]]]]".
            rewrite lookup_insert_ne in H8; auto.
            rewrite lookup_insert in H8. inv H8.
            iDestruct (sts_full_state_std with "[$Hsts] [$A1]") as "%".
            iDestruct (region_close_next with "[$A1 $A2 A3 $A4 $B]") as "A"; auto.
            { intros [g' Hcontr]. specialize (H2 g'). congruence. }
            { eapply not_elem_of_cons; split; auto. eapply not_elem_of_nil. }
            { iSplitR; auto. simpl. iSplit; auto.
              rewrite !switch_monotonicity_formulation; auto.
              rewrite /monotonicity_guarantees_decide.
              destruct (decide (ρ' = Temporary ∧ pwl p'0 = true)).
              + rewrite /future_pub_mono /=. iAlways.
                iIntros (W1 W2) "% #A".
                iApply interp_monotone; auto.
              + rewrite /future_priv_mono /=. iAlways.
                iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                destruct w0; auto.
                eapply not_and_r in n1. destruct_cap c.
                simpl. destruct c3; auto. simpl in H4,H5.
                destruct (pwlU p0) eqn:HwplU; intros; try congruence.
                destruct n1.
                * iAssert (⌜g0 = Local⌝)%I as %->.
                  { rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                    destruct p0; simpl in HwplU; try congruence; destruct g0; simpl; auto. }
                  rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                  iAssert (⌜region_state_U_pwl W a'⌝)%I as %Hρ.
                  { destruct p0; simpl in H4; simpl in HwplU; try congruence.
                    - simpl. iDestruct "Hwdst" as "[YA YB]".
                      destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                      iDestruct (extract_from_region_inv b0 _ a' with "YA") as (pp ?) "[E %]"; auto.
                      split; try solve_addr. rewrite /min; destruct (Addr_le_dec a0 e0); solve_addr.
                      iPureIntro. left; auto.
                    - simpl. iDestruct "Hwdst" as "[YA YC]".
                      destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                      iDestruct (extract_from_region_inv b0 _ a' with "YA") as (pp ?) "[E %]"; auto.
                      split; try solve_addr. rewrite /min; destruct (Addr_le_dec a0 e0); solve_addr.
                      iPureIntro. left; auto. }
                  destruct Hρ as [Hρ | Hρ]; rewrite H8 in Hρ; inversion Hρ; try subst ρ'; congruence.
                * assert (HpwlU2: pwlU p'0 = true).
                  { destruct p0; simpl in H5; simpl in HwplU; try congruence; destruct p'0; rewrite /PermFlows in H; inv H; simpl in H0; try congruence; reflexivity. }
                  exfalso. destruct p0; destruct p'0; simpl in H5, HwplU, HpwlU2, H10; try congruence; inv H; auto. }
            iDestruct (region_open_prepare with "A") as "A".
            iDestruct (region_close with "[$A $C $Hmono $Hstate]") as "B"; auto.
            { destruct ρ;auto;congruence. }
            iExists W. iFrame. iPureIntro. apply related_sts_pub_refl_world. }
      iDestruct "HW" as (W') "[Hregion [% [Hfull HX]]]".
      iDestruct ("IH" $! W' r' with "[] [HX] [C] [$Hregion] [$Hfull] [$Hown] [] []") as "H"; auto.
      { iPureIntro. simpl; intros.
        destruct (addr_eq_dec a0 a').
        - subst a0. destruct (a' + 1)%a as [a''|] eqn:Ha'; try tauto.
          eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. destruct (reg_eq_dec PC x).
          * subst x; rewrite lookup_insert; eauto.
          * rewrite lookup_insert_ne; auto.
            destruct (reg_eq_dec rdst x).
            { subst x. rewrite lookup_insert; eauto. }
            { rewrite !lookup_insert_ne; auto. }
        - eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. destruct (reg_eq_dec PC x).
          + subst x; rewrite lookup_insert; eauto.
          + rewrite !lookup_insert_ne; auto. }
      { iIntros (x) "%".
        destruct (addr_eq_dec a0 a').
        - subst a0. destruct (a' + 1)%a as [a''|] eqn:Ha'; try tauto.
          eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. rewrite lookup_insert_ne; auto.
          destruct (reg_eq_dec rdst x).
          * subst x. rewrite lookup_insert. auto.
          * rewrite !lookup_insert_ne; auto.
            iApply interp_monotone; auto.
            iApply "Hreg"; auto.
        - eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. rewrite !lookup_insert_ne; auto.
          iApply interp_monotone; auto.
          iApply "Hreg"; auto. }
      { instantiate (3 := b).
        instantiate (2 := e).
        instantiate (1 := match (a + 1)%a with Some a' => a' | None => a end).
        destruct (addr_eq_dec a0 a').
        - subst a0. destruct (a' + 1)%a as [a''|] eqn:Ha'; try tauto.
          eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. rewrite insert_insert.
          simplify_map_eq. auto. 
        - eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. rewrite insert_insert.
          simplify_map_eq. rewrite insert_insert;auto. }
      { iAlways. (* iExists p'; iSplitR; auto. *)
        iApply (big_sepL_mono with "Hinv"); auto.
        intros. simpl. iIntros "Hw". iDestruct "Hw" as (pp ?) "Hw".
        iExists pp; iSplit;auto. 
        iDestruct "Hw" as "[$ %]".
        destruct (pwl p);iPureIntro.
        + eapply region_state_pwl_monotone; eauto.
        + eapply region_state_nwl_monotone; eauto.
      }
      iApply wp_pure_step_later; auto. iNext.
      iApply (wp_mono with "H"). simpl.
      iIntros (v) "H %". iDestruct ("H" $! a1) as (rx Wx) "[A [B [% [C [D E]]]]]".
      iExists rx, Wx; iFrame.
      iPureIntro. eapply related_sts_priv_trans_world; eauto.
      eapply related_sts_pub_priv_world; auto. }
    { iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: eauto; try exact {[a:=x]}. 
  Qed.
  
End fundamental.
