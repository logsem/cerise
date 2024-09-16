From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Store.
Import uPred.


Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).


  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  (* Since we will store a new word into a, we do not need to remember its validity *)
  Definition region_open_resources (la pc_la : LAddr) (pc_lw : LWord) : iProp Σ :=
    (▷ interp pc_lw ∗ ((▷ ∃ lw, la ↦ₐ lw ∗ interp lw)
                       ={⊤ ∖ ↑logN.@pc_la ∖ ↑logN.@la,⊤ ∖ ↑logN.@pc_la}=∗ emp))%I.

  Lemma store_inr_eq {regs r p0 b0 e0 a0 v0 p1 b1 e1 a1 v1}:
    reg_allows_store regs r p0 b0 e0 a0 v0 →
    read_reg_inr regs r p1 b1 e1 a1 v1 →
    p0 = p1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1 ∧ v0 = v1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). rewrite /read_reg_inr Hinr0 in H3.
        by inversion H3.
  Qed.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_store_res (lregs : LReg) r pc_a pca_v p b e a v :=
    (⌜read_reg_inr lregs r p b e a v⌝ ∗
      if decide (reg_allows_store lregs r p b e a v ∧ (a,v) ≠ (pc_a, pca_v)) then
          |={⊤ ∖ ↑logN.@(pc_a, pca_v),⊤ ∖ ↑logN.@(pc_a, pca_v) ∖ ↑logN.@(a,v)}=>
            ∃ lw, (a,v) ↦ₐ lw ∗ region_open_resources (a,v) (pc_a, pca_v) lw
    else True)%I.

  Definition allow_store_mem (lregs : LReg) r
    (pc_a : Addr) (pca_v : Version) pc_lw (lmem : LMem) p b e a v :=
    (⌜read_reg_inr lregs r p b e a v⌝ ∗
    if decide (reg_allows_store lregs r p b e a v ∧ (a,v) ≠ (pc_a, pca_v))
    then ∃ lw, ⌜lmem = <[(a,v):=lw]> (<[(pc_a, pca_v):=pc_lw]> ∅)⌝
                                       ∗ region_open_resources (a,v) (pc_a, pca_v) lw
    else ⌜lmem = <[(pc_a, pca_v):=pc_lw]> ∅⌝)%I.


  Lemma create_store_res:
    ∀ (lregs : leibnizO LReg) (p : Perm)
      (b e a : Addr) (v : Version) (r : RegName) (p0 : Perm)
      (b0 e0 a0 : Addr) (v0 : Version),
      read_reg_inr (<[PC:=LCap p b e a v]> lregs) r p0 b0 e0 a0 v0
      → (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜lregs !! r1 = Some v⌝ → (fixpoint interp1) v)
          -∗ allow_store_res (<[PC:=LCap p b e a v]> lregs) r a v p0 b0 e0 a0 v0.
  Proof.
    intros lregs p b e a v r p0 b0 e0 a0 v0 HVr1.
    iIntros "#Hreg".
    iFrame "%".
    case_decide as Hallows.
    - destruct Hallows as ((Hrinr & Hra & Hwb) & Hlaeq).
      apply andb_prop in Hwb as [Hle Hge].
      revert Hle Hge. rewrite !Z.leb_le Z.ltb_lt =>Hle Hge.
      assert (r ≠ PC) as n. refine (laddr_ne_reg_ne Hrinr _ Hlaeq); by simplify_map_eq.
      simplify_map_eq.
      iDestruct ("Hreg" $! r _ n Hrinr) as "Hvsrc".
      iAssert (inv (logN.@(a0, v0)) ((interp_ref_inv a0 v0) interp))%I as "#Hinva".
      { iApply (write_allowed_inv with "Hvsrc"); auto. }
      iFrame "∗ #".
      iMod (inv_acc with "Hinva") as "[Hinv Hcls']";[solve_ndisj|].
      iDestruct "Hinv" as (lw) "[>Ha0 #Hinv]".
      iExists lw. by iFrame.
    - done.
  Qed.


  Lemma store_res_implies_mem_map:
    ∀ (lregs : leibnizO LReg)
       (a a0 : Addr) (v v0 : Version) (lw : LWord) (r : RegName) p1 b1 e1,
      allow_store_res lregs r a v p1 b1 e1 a0 v0
      -∗ (a, v) ↦ₐ lw
      ={⊤ ∖ ↑logN.@(a, v),
        if decide (reg_allows_store lregs r p1 b1 e1 a0 v0 ∧ (a0, v0) ≠ (a,v))
        then ⊤ ∖ ↑logN.@(a, v) ∖ ↑logN.@(a0, v0)
        else ⊤ ∖ ↑logN.@(a, v)}=∗
         ∃ lmem : LMem,
          allow_store_mem lregs r a v lw lmem p1 b1 e1 a0 v0
            ∗ ▷ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw).
  Proof.
    intros lregs a a0 v v0 lw r p1 b1 e1.
    iIntros "HStoreRes Ha".
    iDestruct "HStoreRes" as "(% & HStoreRes)".

    case_decide as Hallows.
    - iMod "HStoreRes" as (lw0) "[Ha0 HStoreRest]".
      iExists _.
      iSplitL "HStoreRest".
      * iFrame "%".
        case_decide; last by exfalso.
        iExists lw0. iSplitR; auto.
      * iModIntro. iNext.
        destruct Hallows as ((Hrinr & Hra & Hwb) & Hne).
        iApply memMap_resource_2ne; auto; iFrame.
    - iExists _.
      iSplitR "Ha".
      + iFrame "%".
        case_decide; first by exfalso. auto.
      + iModIntro. iNext. by iApply memMap_resource_1.
  Qed.


  Lemma mem_map_implies_pure_conds:
    ∀ (lregs : leibnizO LReg)
      (a a0 : Addr) (v v0 : Version) (lw : LWord) (r : RegName)
      (lmem : LMem) p b e,
        allow_store_mem lregs r a v lw lmem p b e a0 v0
        -∗ ⌜lmem !! (a,v) = Some lw⌝
          ∗ ⌜allow_store_map_or_true r lregs lmem⌝.
  Proof.
    iIntros (lregs a a0 v v0 lw r lmem p b e) "HStoreMem".
    iDestruct "HStoreMem" as "(% & HStoreRes)".
    case_decide as Hallows.
    - pose(Hallows' := Hallows).
      destruct Hallows' as ((Hrinr & Hra & Hwb) & Hne).
      iDestruct "HStoreRes" as (lw0 ->) "HStoreRest".
      iSplitR. by simplify_map_eq.
      iExists p,b,e,a0,v0. iSplit;auto.
      iPureIntro. case_decide;auto.
      exists lw0. by simplify_map_eq.
    - iDestruct "HStoreRes" as "->".
      iSplitR. by simplify_map_eq.
      iExists p,b,e,a0,v0. repeat iSplitR; auto.
      case_decide as Hdec1; last by done.
      apply not_and_l in Hallows as [Hallows | Hallows]; try contradiction.
      assert ((a0, v0) = (a, v)) as ->.
      { f_equal; [apply finz_to_z_eq, Z.eq_dne | apply Nat.eq_dne]
        ; intros Hcontr
        ; apply Hallows
        ; intro ; simplify_eq.
      }
      simplify_map_eq. eauto.
  Qed.

   Lemma mem_map_recover_res:
    ∀ (lregs : leibnizO LReg)
       (a : Addr) (v : Version) (lw : LWord) (src : RegName)
       p0 (b0 e0 a0 : Addr) (v0 : Version)
       (lmem : LMem) storev loadv,
      reg_allows_store lregs src p0 b0 e0 a0 v0
      → lmem !! (a0,v0) = Some loadv
      → allow_store_mem lregs src a v lw lmem p0 b0 e0 a0 v0
        -∗ ([∗ map] la↦lw ∈ (<[(a0,v0):=storev]> lmem), la ↦ₐ lw)
        -∗ interp storev
        ={if decide (reg_allows_store lregs src p0 b0 e0 a0 v0 ∧ (a0,v0) ≠ (a,v))
          then ⊤ ∖ ↑logN.@(a,v) ∖ ↑logN.@(a0,v0)
          else ⊤ ∖ ↑logN.@(a,v),⊤ ∖ ↑logN.@(a,v)}=∗
            if decide (reg_allows_store lregs src p0 b0 e0 a0 v0 ∧ (a0,v0) = (a,v))
            then (a,v) ↦ₐ storev else (a,v) ↦ₐ lw.
  Proof.
    intros lregs a v lw src p0 b0 e0 a0 v0 lmem storev loadv Hrar Hloadv.
    iIntros "HLoadMem Hmem Hvalid".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (lw0) "[-> [Hval Hcls] ]".
       simplify_map_eq. rewrite insert_insert.
       rewrite memMap_resource_2ne; last auto. iDestruct "Hmem" as  "[Ha1 Haw]".
       iMod ("Hcls" with "[Ha1 Hvalid]") as "_";[iNext;iExists storev;iFrame|]. iModIntro.
       rewrite decide_False; [done|]. apply not_and_r. right. auto.
    - apply not_and_r in Hdec as [| <-%dec_stable].
      * by exfalso.
      * iDestruct "HLoadRes" as "->".
        rewrite insert_insert.
        rewrite -memMap_resource_1. simplify_map_eq.
        by iFrame.
  Qed.

  Lemma store_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst : RegName) (src : Z + RegName) P :
    ftlr_instr lregs p b e a v lw (Store dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #(Hread & Hwrite & %HpersP) Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=LCap p b e a v]> lregs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
        by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0 v0, read_reg_inr (<[PC:=LCap p b e a v]> lregs) dst p0 b0 e0 a0 v0)
      as (p0 & b0 & e0 & a0 & v0 & HVdst).
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. rewrite Hsomedst.
      destruct wdst as [|[ p0 b0 e0 a0 v0|] | ]; try done.
      by repeat eexists.
    }

     assert (∃ storev, word_of_argumentL (<[PC:=LCap p b e a v]> lregs) src = Some storev)
       as [storev Hwoa].
    { destruct src; cbn.
      - by exists (LInt z).
      - specialize Hsome' with r as Hr.
        destruct Hr as [wsrc Hsomer].
        exists wsrc. by rewrite Hsomer.
    }

    (* Step 1: open the region, if necessary,
       and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_store_res with "Hreg") as "HStoreRes"; eauto.

    (* Step2: derive the concrete map of memory we need,
       and any spatial predicates holding over it *)
    iMod (store_res_implies_mem_map with "HStoreRes Ha") as (mem) "[HStoreMem >HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iApply (wp_store with "[Hmap HMemRes]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [* ? ? ? -> Hincr|* -> Hincr].
    { apply incrementLPC_Some_inv in Hincr as (p''&b''&e''&a''& v''&? & HPC & Z & Hregs') .
      iApply wp_pure_step_later; auto.
      specialize (store_inr_eq H1 HVdst) as (-> & -> & -> & -> & ->).

      (* The stored value is valid *)
      iAssert (interp storev0) as "#Hvalidstore".
      { destruct src; inversion H0. rewrite !fixpoint_interp1_eq. done.
        simplify_map_eq.
        destruct (<[PC:=LCap p'' b'' e'' a'' v'']> lregs !! r) eqn:Hsomer0; simplify_map_eq.
        2 : { rewrite Hsomer0 in Hwoa. done. }
        destruct (decide (r = PC)).
        - subst. simplify_map_eq. iFrame "Hinv".
        - simplify_map_eq. iSpecialize ("Hreg" $! _ _ n Hsomer0).
           iFrame "Hreg".
      }

      (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iMod (mem_map_recover_res with "HStoreMem Hmem Hvalidstore") as "Ha";[eauto|eauto|iModIntro].

      iMod ("Hcls" with "[HP Ha]").
      { simplify_map_eq.
        case_decide as Hwrite.
        - case_decide.
          + iNext. iExists storev.
            iDestruct ("Hwrite" with "Hvalidstore") as "HPstore".
            iFrame "∗ #".
          + iNext. iExists lw. iFrame.
        - rewrite decide_False. iNext. iExists lw. iFrame.
          intros [Hcontr Heq].
          apply Hwrite. exists dst.
          destruct Hcontr as (Hlookup & Hwa & Hwb). simplify_map_eq.
          apply andb_prop in Hwb.
          revert Hwb. rewrite Z.leb_le Z.ltb_lt. intros. eexists _.
          split_and!; try done.
      }

      simplify_map_eq.
      rewrite insert_insert.

      iModIntro; iNext; iIntros "_".
      iApply ("IH" with "[%] [] Hmap [$Hown]");auto.
      { rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->]; by iFrame "#". }
    }
    { rewrite /allow_store_res /allow_store_mem.
      destruct (decide (reg_allows_store (<[PC:=LCap p b e a v]> lregs) dst p0 b0 e0 a0 v0
                        ∧ (a0,v0) ≠ (a,v))).
      - iDestruct "HStoreMem" as "(%&H)".
        iDestruct "H" as (lw') "(->&[Hres Hcls'])". rewrite /region_open_resources.
        destruct a1. simplify_map_eq. rewrite memMap_resource_2ne; last auto.
        iDestruct "Hmem" as "[Ha0 Ha]".
        iMod ("Hcls'" with "[Ha0 Hres]");[iExists lw';iFrame|iModIntro].
        iMod ("Hcls" with "[Ha HP]");[iExists lw;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
      - iModIntro. iDestruct "HStoreMem" as "(_&->)". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
