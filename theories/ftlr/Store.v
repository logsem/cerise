From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel monotone.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_Store.
Import uPred.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma execcPC_implies_interp W p p' g b e a0:
    PermFlows p p' → p = RX ∨ p = RWX ∨ p = RWLX ∧ g = Local →
    □ exec_cond W b e g p (fixpoint interp1) -∗
      ([∗ list] a ∈ region_addrs b e,
       read_write_cond a p' interp
       ∧ ⌜if pwl p
          then region_state_pwl W a
          else region_state_nwl W a g⌝
               ∧ ⌜region_std W a⌝) -∗
      ((fixpoint interp1) W) (inr (p, g, b, e, a0)).
  Proof.
    iIntros (Hpf Hp) "#HEC #HR".
    rewrite (fixpoint_interp1_eq _ (inr _)).
    (do 2 try destruct Hp as [ | Hp]). 3:destruct Hp.
    all:subst; iExists p' ; by do 2 (iSplit; [auto | ]).
  Qed.

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  Definition region_open_resources W l ls p φ (v : Word): iProp Σ :=
    (∃ ρ,
        sts_state_std (countable.encode l) ρ
    ∗ ⌜std_sta W !! countable.encode l = Some (countable.encode ρ)⌝
    ∗ ⌜ρ ≠ Revoked ∧ (∀ g, ρ ≠ Static g)⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ rel l p φ)%I.

  Lemma store_inr_eq {regs r p0 g0 b0 e0 a0 p1 g1 b1 e1 a1 storev}:
    reg_allows_store regs r p0 g0 b0 e0 a0 storev →
    read_reg_inr regs r p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). destruct H3 as [Hinr1 | Hinl1].
      * rewrite Hinr0 in Hinr1. inversion Hinr1.
        rewrite H4 H5 H6 H7 H8 in Hrar; auto.
      * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
  Qed.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_store_res W r1 r2 (regs : Reg) pc_a (pc_p : Perm) :=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝ ∗ ⌜word_of_argument regs r2 = Some storev⌝ ∗
    if decide (reg_allows_store regs r1 p g b e a storev ) then
      (if decide (a ≠ pc_a) then
         ∃ p' w, a ↦ₐ [p'] w  ∗ ⌜PermFlows p p'⌝ ∗ (region_open_resources W a [pc_a] p' interpC w)
         else open_region pc_a W ∗ ⌜PermFlows p pc_p⌝ )
      else open_region pc_a W)%I.

  Definition allow_store_mem W r1 r2 (regs : Reg) pc_a pc_p pc_w (mem : PermMem):=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝ ∗ ⌜word_of_argument regs r2 = Some storev⌝ ∗
    if decide (reg_allows_store regs r1 p g b e a storev) then
      (if decide (a ≠ pc_a) then
         ∃ p' w, ⌜mem = <[a:=(p',w)]> (<[pc_a:=(pc_p,pc_w)]> ∅)⌝ ∗
            ⌜PermFlows p p'⌝ ∗ (region_open_resources W a [pc_a] p' interpC w)
         else  ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ open_region pc_a W ∗ ⌜PermFlows p pc_p⌝ )
    else  ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ open_region pc_a W)%I.

  Lemma interp_hpf_eq (W : leibnizO (STS * STS)) (r : leibnizO Reg) (r1 : RegName)
        p g b e a pc_p pc_g pc_b pc_e pc_p' w storev:
    reg_allows_store (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, a)]> r) r1 p g b e a storev
    → PermFlows pc_p pc_p'
    → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
        -∗ read_write_cond a pc_p' interp
        -∗ ⌜PermFlows p pc_p'⌝.
  Proof.
    destruct (decide (r1 = PC)).
    - subst r1. iIntros. destruct H3 as (H3 & _). simplify_map_eq; auto.
    - iIntros ((Hsomer1 & Hwa & Hwb & Hloc) Hfl) "Hreg Hinva".
      iDestruct ("Hreg" $! r1 n) as "Hr1". simplify_map_eq. rewrite /RegLocate Hsomer1.
      iDestruct (read_allowed_inv _ a with "Hr1") as (p'' Hfl') "#Harel'"; auto.
      { apply andb_true_iff in Hwb as [Hle Hge].
        split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
      { by apply writeA_implies_readA in Hwa as ->. }
      rewrite /read_write_cond.
      iDestruct (rel_agree a p'' pc_p' with "[$Hinva $Harel']") as "[-> _]".
      done.
  Qed.

  Lemma create_store_res:
    ∀ (W : leibnizO (STS * STS)) (r : leibnizO Reg) (p p' : Perm)
      (g : Locality) (b e a : Addr) (r1 : RegName) (r2 : Z + RegName) (p0 : Perm)
      (g0 : Locality) (b0 e0 a0 : Addr)(storev : Word),
      read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) r1 p0 g0 b0 e0 a0
      → PermFlows p p'
      → word_of_argument (<[PC:=inr (p, g, b, e, a)]> r) r2 = Some storev
      → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
          -∗ read_write_cond a p' interp
          -∗ open_region a W
          -∗ sts_full_world sts_std W
          -∗ allow_store_res W r1 r2 (<[PC:=inr (p, g, b, e, a)]> r) a p'
          ∗ sts_full_world sts_std W.
  Proof.
    intros W r p p' g b e a r1 r2 p0 g0 b0 e0 a0 storev HVr1 Hfl Hwoa.
    iIntros "#Hreg #Hinva Hr Hsts".
    do 6 (iApply sep_exist_r; iExists _). iFrame "%".
    case_decide as Hallows.
    -  case_decide as Haeq.
       * destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
         apply andb_prop in Hwb as [Hle Hge].
         rewrite /leb_addr in Hle,Hge.
         assert (r1 ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.

         iDestruct ("Hreg" $! r1 n) as "Hvsrc".
         rewrite lookup_insert_ne in Hrinr; last by congruence.
         rewrite /RegLocate Hrinr.
         iDestruct (read_allowed_inv _ a0 with "Hvsrc") as (p0' Hfl') "Hrel'".
         { split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
         { by apply writeA_implies_readA in Hra as ->. }
         rewrite /read_write_cond.

         iDestruct (region_open_prepare with "Hr") as "Hr".
         iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as "%"; eauto.
         { by apply writeA_implies_readA. }
         { rewrite /withinBounds /leb_addr Hle Hge. auto. }
         destruct H3 as [Hregion' [ρ' [Hstd' [Hnotrevoked' Hnotstatic'] ] ] ].
         (* We can finally frame off Hsts here, since it is no longer needed after opening the region*)
         iDestruct (region_open_next _ _ _ a0 p0' ρ' with "[$Hrel' $Hr $Hsts]") as (w0) "($ & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
         { intros [g1 Hcontr]. specialize (Hnotstatic' g1); contradiction. }
         { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
         iExists p0', w0. iSplitL "Ha0"; auto. iSplitR; auto. unfold region_open_resources.
         iExists ρ'. iFrame "%". iFrame. by iFrame "#".
      * subst a0. iFrame. iApply interp_hpf_eq; eauto.
    - iFrame.
  Qed.

  Lemma store_res_implies_mem_map:
    ∀ (W : leibnizO (STS * STS)) (r : leibnizO Reg) (p' : Perm)
       (a : Addr) (w : Word) (r1 : RegName) (r2 : Z + RegName),
      allow_store_res W r1 r2 r a p'
      -∗ a ↦ₐ[p'] w
      -∗ ∃ mem0 : PermMem,
          allow_store_mem W r1 r2 r a p' w mem0
            ∗ ▷ ([∗ map] a0↦pw ∈ mem0, ∃ (p0 : Perm) (w0 : leibnizO Word),
                ⌜pw = (p0, w0)⌝ ∗ a0 ↦ₐ[p0] w0).
  Proof.
    intros W r p' a w r1 r2.
    iIntros "HStoreRes Ha".
    iDestruct "HStoreRes" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".

    case_decide as Hallows.
    - case_decide as Haeq.
      ++ pose(Hallows' := Hallows). destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
         iDestruct "HStoreRes" as (p'0 w0) "[HStoreCh HStoreRest]".
         iExists _.
         iSplitL "HStoreRest".
        + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
          case_decide; last by exfalso. case_decide; last by exfalso.
          iExists p'0,w0. iSplitR; auto.
        + iNext.
          iApply memMap_resource_2ne; auto; iFrame.
      ++ iExists _.
         iSplitL "HStoreRes".
        + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
          case_decide; last by exfalso. case_decide; first by exfalso.
          iFrame. auto.
        + iNext. by iApply memMap_resource_1.
    - iExists _.
      iSplitL "HStoreRes".
      + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
        case_decide; first by exfalso. iFrame. auto.
      + iNext. by iApply memMap_resource_1.
    Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (W : leibnizO (STS * STS)) (r : leibnizO Reg) (p p' : Perm)
      (g : Locality) (b e a : Addr) (w : Word) (r1 : RegName) (r2 : Z + RegName)
      (mem0 : PermMem),
        p' ≠ O →
        allow_store_mem W r1 r2 r a p' w mem0
        -∗ ⌜mem0 !! a = Some (p', w)⌝
          ∗ ⌜allow_store_map_or_true r1 r2 r mem0⌝.
  Proof.
    iIntros (W r p p' g b e a w r1 r2 mem0 Hp'O) "HStoreMem".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".
    case_decide as Hallows.
    - case_decide as Haeq.
      + pose(Hallows' := Hallows). destruct Hallows' as (Hrinr & Hra & Hwb & HLoc).
        (* case_decide as Haeq. *)
        iDestruct "HStoreRes" as (p'0 w0 ->) "[% _]".
        iSplitR. rewrite lookup_insert_ne; auto. by rewrite lookup_insert.
        iExists p1,g1,b1,e1,a1,storev.
        iPureIntro. repeat split; auto.
        case_decide; last by exfalso.
        exists p'0,w0. by simplify_map_eq.
      + subst a. iDestruct "HStoreRes" as "[-> [HStoreRes % ] ]".
         iSplitR. by rewrite lookup_insert.
         iExists p1,g1,b1,e1,a1,storev. repeat iSplitR; auto.
         case_decide as Hdec1; last by done.
         iExists p',w.  by rewrite lookup_insert.
    - iDestruct "HStoreRes" as "[-> HStoreRes ]".
      iSplitR. by rewrite lookup_insert.
      iExists p1,g1,b1,e1,a1,storev. repeat iSplitR; auto.
      case_decide as Hdec1; last by done. by exfalso.
  Qed.

   Lemma storev_interp_mono W (r : Reg) (r1 : RegName) (r2 : Z + RegName) p g b e a p' ρ storev:
     PermFlows p p'
     → word_of_argument r r2 = Some storev
     → reg_allows_store r r1 p g b e a storev
     → std_sta W !! countable.encode a = Some (countable.encode ρ)
     → ((fixpoint interp1) W) (inr (p,g,b,e,a))
       -∗ monotonicity_guarantees_region ρ storev p' interpC.
   Proof.
     iIntros (Hpf Hwoa Hras Hststd) "HInt".
     destruct Hras as (Hrir & Hwa & Hwb & Hloc).
     destruct storev as [z | cap].
     - iApply (interp_monotone_generalZ with "[HInt]" ); eauto.
     - destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
       destruct_cap cap. cbn in Hwoa.
       destruct (r !! r0); inversion Hwoa; clear Hwoa; subst w.
       iApply (interp_monotone_generalW with "[HInt]" ); eauto.
       apply orb_true_iff. destruct Hloc.
       *  cbn in H3. left. by apply negb_true_iff.
       *  right. apply pwl_implies_RWL_RWLX in H3. by destruct H3 as [-> | ->].
  Qed.

  (* Note that we turn in all information that we might have on the monotonicity of the current PC value, so that in the proof of the ftlr case itself, we do not have to worry about whether the PC was written to or not when we close the last location pc_a in the region *)
   Lemma mem_map_recover_res:
    ∀ (W : leibnizO (STS * STS)) (r : Reg) (p' : Perm)
       (pc_w : Word) (r1 : RegName) (r2 : Z + RegName) (p0 p'0 pc_p pc_p' : Perm)
       (g0 pc_g : Locality) (b0 e0 a0 pc_b pc_e pc_a : Addr) (mem0 : PermMem) (oldv storev : Word) (ρ : region_type),
      word_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) r2 = Some storev
      → reg_allows_store (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) r1 p0 g0 b0 e0 a0 storev
      → std_sta W !! countable.encode pc_a = Some (countable.encode ρ)
      → mem0 !! a0 = Some (p'0, oldv) (*?*)
      → allow_store_mem W r1 r2 (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) pc_a pc_p' pc_w mem0
        -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
        -∗ ((fixpoint interp1) W) (inr(pc_p, pc_g, pc_b, pc_e, pc_a))
        -∗ ((fixpoint interp1) W) pc_w
        -∗ monotonicity_guarantees_region ρ pc_w pc_p' interpC
        -∗ ([∗ map] a0↦pw ∈ <[a0 := (p'0, storev)]> mem0, ∃ (p0 : Perm) (w0 : Word),
                ⌜pw = (p0, w0)⌝ ∗ a0 ↦ₐ[p0] w0)
        -∗ ∃ v, open_region pc_a W ∗ pc_a ↦ₐ[pc_p'] v ∗ ((fixpoint interp1) W) v ∗ monotonicity_guarantees_region ρ v pc_p' interpC.
   Proof.
    intros W r p' pc_w r1 r2 p0 p'0 pc_p pc_p' g0 pc_g b0 e0 a0 pc_b pc_e pc_a mem0 oldv storev ρ Hwoa Hras Hstdst Ha0.
    iIntros "HStoreMem #Hreg #HVPCr #Hpc_w Hpcmono Hmem".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev1) "[% [% HStoreRes] ]".
    destruct (store_inr_eq Hras H3) as (<- & <- &<- &<- &<-).
    rewrite Hwoa in H4; inversion H4; simplify_eq.
    case_decide as Hallows.
    - iAssert (((fixpoint interp1) W) (inr (p0,g0,b0,e0,a0)))%I with "[HVPCr Hreg]" as "#HVr1".
      { destruct Hras as [Hreg _]. destruct (decide (r1 = PC)).
        - subst r1. rewrite lookup_insert in Hreg; by inversion Hreg.
        - iSpecialize ("Hreg" $! r1 n). rewrite lookup_insert_ne in Hreg; last congruence. by rewrite /RegLocate Hreg.
      }
      iAssert (((fixpoint interp1) W) storev1)%I with "[HVPCr Hreg]" as "#HVstorev1".
      { destruct storev1.
        - repeat rewrite fixpoint_interp1_eq. by cbn.
        - destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
          destruct_cap c. cbn in Hwoa.
          destruct (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r !! r0) eqn:Hrr0; inversion Hwoa; clear Hwoa; subst w.
          destruct (decide (r0 = PC)).
          + subst r0. rewrite lookup_insert in Hrr0. by inversion Hrr0.
          + iSpecialize ("Hreg" $! r0 n).  rewrite lookup_insert_ne in Hrr0; last congruence. by rewrite /RegLocate Hrr0.
      }
      case_decide as Haeq.
      + iExists pc_w.
        destruct Hallows as [Hrinr [Hwa [Hwb Hloc] ] ].
        iDestruct "HStoreRes" as (p'1 w') "[-> [% HLoadRes] ]".
        rewrite lookup_insert in Ha0; inversion Ha0; clear Ha0; subst.
        iDestruct "HLoadRes" as (ρ1) "(Hstate' & % & #Hrev & Hr & % & Hrel')".
        iDestruct "Hrev" as %[Hnotrevoked Hnotstatic]. 
        rewrite insert_insert memMap_resource_2ne; last auto. iDestruct "Hmem" as  "[Ha1 $]".
        iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
        iDestruct (region_close_next with "[$Hr $Ha1 $Hrel' $Hstate' $HVstorev1 $Hr1Mono]") as "Hr"; eauto.
        { intros [g Hcontr]. specialize (Hnotstatic g); contradiction. }
        { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
        iDestruct (region_open_prepare with "Hr") as "$". by iFrame.
       + subst a0. iDestruct "HStoreRes" as "[-> [HStoreRes % ] ]".
         rewrite insert_insert -memMap_resource_1.
         rewrite lookup_insert in Ha0; inversion Ha0; simplify_eq.
         iExists storev1. iFrame.
         iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
    - by exfalso.
   Qed.

  Lemma store_case(W : WORLD) (r : leibnizO Reg) (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) :
    ftlr_instr W r p p' g b e a w (Store dst src) ρ.

  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd [Hnotrevoked Hnotstatic] HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=inr (p, g, b, e, a)]> r !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
        by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 g0 b0 e0 a0 , read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) dst p0 g0 b0 e0 a0) as [p0 [g0 [b0 [e0 [a0 HVdst] ] ] ] ].
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. destruct wdst. 2: destruct_cap c. all: repeat eexists.
      right. by exists z. by left.
    }

     assert (∃ storev, word_of_argument (<[PC:=inr (p, g, b, e, a)]> r) src = Some storev) as [storev Hwoa].
    { destruct src; cbn.
      - by exists (inl z).
      - specialize Hsome' with r0 as Hr0.
        destruct Hr0 as [wsrc Hsomer0].
        exists wsrc. by rewrite Hsomer0.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_store_res with "Hreg Hinva Hr Hsts") as "[HStoreRes Hsts]"; eauto.
    (* Clear helper values; they exist in the existential now *)
    clear HVdst p0 g0 b0 e0 a0 Hwoa storev.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iDestruct (store_res_implies_mem_map W  with "HStoreRes Ha") as (mem) "[HStoreMem HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iApply (wp_store with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [* ? ? ? -> Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto. iNext.

      (* Derive the fact that the execution condition holds for PC *)
      iAssert (□ exec_cond W b e g p (fixpoint interp1))%I as "HexeccPC".
      {  iAlways;rewrite /exec_cond;iIntros (a' r' W' Hin) "#Hfuture".
         iNext; rewrite /interp_expr /=.
         iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
         iSplitR; eauto.
         iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
         iAlways. iExists p'. iSplitR; auto.
         unfold future_world; destruct g; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "Hinv"); intros; simpl.
         (*g is global*)
         - iIntros "[HA [% %]]". iSplitL "HA"; auto.
           iPureIntro; split.
           + destruct (pwl p) eqn:Hppwl.
             * (do 2 try destruct Hp as [ | Hp]); last by (destruct Hp; exfalso).
               all: (rewrite H12 in Hppwl; simpl in Hppwl; by exfalso).
             * by apply (region_state_nwl_monotone_nl _ _ y H11 Hfuture H10).
           + eapply related_sts_rel_std; eauto.
         (*g is local*)
         - iIntros "[HA [% %]]". iSplitL "HA"; auto.
           iPureIntro; split.
           +  destruct (pwl p).
              * apply (region_state_pwl_monotone _ _ y H11 Hfuture H10); auto.
              * apply (region_state_nwl_monotone _ _ y Local H11 Hfuture H10); auto.
           + apply related_sts_pub_priv_world in Hfuture.
             eapply related_sts_rel_std; eauto.
      }

      (* From this, derive value relation for the current PC*)
      iDestruct (execcPC_implies_interp _ _ _ _ _ _ a  with "HexeccPC Hinv") as "HVPC"; eauto.

      iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; auto.
      
      (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res with "HStoreMem Hreg HVPC Hw Hmono Hmem") as (w') "(Hr & Ha & #HSVInterp & Hmono)"; eauto.

      iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; auto.

      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotstatic g1)];contradiction. }
      simplify_map_eq.

      iApply ("IH" with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); auto.
      { cbn. auto. }
      { rewrite insert_insert. iApply "Hmap". }
    }
    { iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

End fundamental.
