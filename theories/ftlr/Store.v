From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Store.
Import uPred.


Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  (* Since we will store a new word into a, we do not need to remember its validity *)
  Definition region_open_resources (a pc_a : Addr) (pc_w : Word) : iProp Σ :=
    (▷ interp pc_w
       ∗ ((▷ ∃ w0, a ↦ₐ w0 ∗ interp w0) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a,⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Lemma store_inr_eq {regs r p0 b0 e0 a0 p1 b1 e1 a1}:
    reg_allows_store regs r p0 b0 e0 a0 →
    read_reg_inr regs r p1 b1 e1 a1 →
    p0 = p1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). rewrite /read_reg_inr Hinr0 in H3.
        by inversion H3.
  Qed.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_store_res (regs : Reg) (r : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr) :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
       if decide (reg_allows_store regs r p b e a ∧ a ≠ pc_a)
       then (|={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a}=>
              ∃ w, a ↦ₐ w ∗ region_open_resources a pc_a w)
       else True)%I.

  Definition allow_store_mem (regs : Reg) (mem : Mem) (r : RegName)
    (pc_a : Addr) (pc_w : Word) (p : Perm) (b e a : Addr) :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
    if decide (reg_allows_store regs r p b e a ∧ a ≠ pc_a)
    then ∃ w, ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources a pc_a w
    else ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma create_store_res:
    ∀ (regs : leibnizO Reg) (r : RegName)
      (pc_p : Perm) (pc_b pc_e pc_a : Addr)
      (widc : Word)
      (p : Perm) (b e a : Addr) ,
      read_reg_inr (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:=widc]> regs)) r p b e a
      → (∀ (r : RegName) (w : Word), ⌜r ≠ PC⌝ → ⌜r ≠ idc⌝ →  ⌜regs !! r = Some w⌝ → (fixpoint interp1) w)
        -∗ interp widc
        -∗ allow_store_res
           (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:=widc]> regs))
           r pc_a p b e a.
  Proof.
    intros regs r pc_p pc_b pc_e pc_a widc p b e a HVr.
    iIntros "#Hreg #Hwidc".
    iFrame "%".
    case_decide as Hallows; last done.
    destruct Hallows as ((Hrinr & Hra & Hwb) & Haeq).
    apply andb_prop in Hwb as [Hle Hge].
    revert Hle Hge. rewrite !Z.leb_le Z.ltb_lt =>Hle Hge.
    assert (r ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.
    rewrite lookup_insert_ne in Hrinr; last by congruence.
    destruct (decide (r = idc)) as [|Hneq]; simplify_map_eq.
    - (* r = idc *)
      iDestruct (write_allowed_inv _ a with "Hwidc") as "Hinva"
      ; auto; first (split; eauto).
      iFrame "∗ #".
      iMod (inv_acc with "Hinva") as "[Hinv Hcls']";[solve_ndisj|].
      iDestruct "Hinv" as (w) "[>Ha #Hinv]".
      iExists w.
      by iFrame "∗ #".
    - (* r ≠ idc *)
      iDestruct ("Hreg" $! r _ n Hneq Hrinr) as "Hvsrc".
      iAssert (inv (logN.@a) ((interp_ref_inv a) interp))%I as "#Hinva".
      { iApply (write_allowed_inv with "Hvsrc"); auto. }
      iFrame "∗ #".
      iMod (inv_acc with "Hinva") as "[Hinv Hcls']";[solve_ndisj|].
      iDestruct "Hinv" as (w) "[>Ha #Hinv]".
      iExists w. by iFrame "∗ #".
  Qed.

  Definition allow_store_mask (regs : Reg) (r : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr) : coPset :=
    if decide (reg_allows_store regs r p b e a ∧ a ≠ pc_a)
    then ⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a
    else ⊤ ∖ ↑logN.@pc_a.

  Lemma store_res_implies_mem_map:
    ∀ (regs : leibnizO Reg) (r : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a: Addr),
      allow_store_res regs r pc_a p b e a
      -∗ pc_a ↦ₐ pc_w
      ={⊤ ∖ ↑logN.@pc_a, allow_store_mask regs r pc_a p b e a}=∗ ∃ mem : Mem,
          allow_store_mem regs mem r pc_a pc_w p b e a
            ∗ ▷ ([∗ map] a0↦w ∈ mem, a0 ↦ₐ w).
  Proof.
    intros regs r pc_a pc_w p b e a.
    iIntros "HStoreRes Ha".
    iDestruct "HStoreRes" as "(% & HStoreRes)".
    rewrite /allow_store_mask.

    case_decide as Hallows.
    - iMod "HStoreRes" as (w0) "[Ha0 HStoreRest]".
      iExists _.
      iSplitL "HStoreRest".
      * iFrame "%".
        case_decide; last by exfalso.
        iExists w0. iSplitR; auto.
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
    ∀ (regs : leibnizO Reg) (mem : Mem) (r : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr),
      allow_store_mem regs mem r pc_a pc_w p b e a
        -∗ ⌜mem !! pc_a = Some pc_w⌝
          ∗ ⌜allow_store_map_or_true r regs mem⌝.
  Proof.
    iIntros (regs mem r pc_a pc_w p b e a) "HStoreMem".
    iDestruct "HStoreMem" as "(% & HStoreRes)".
    case_decide as Hallows.
    - pose(Hallows' := Hallows).
      destruct Hallows' as ((Hrinr & Hra & Hwb) & Hne).
      iDestruct "HStoreRes" as (w0 ->) "HStoreRest".
      iSplitR. rewrite lookup_insert_ne; auto. by rewrite lookup_insert.
      iExists p,b,e,a. iSplit;auto.
      iPureIntro. case_decide;auto.
      exists w0. by simplify_map_eq.
    - iDestruct "HStoreRes" as "->".
      iSplitR. by rewrite lookup_insert.
      iExists p,b,e,a. repeat iSplitR; auto.
      case_decide as Hdec1; last by done.
      apply not_and_l in Hallows as [Hallows | Hallows]; try contradiction.
      assert (a = pc_a) as ->.
      { apply finz_to_z_eq, Z.eq_dne. intros Hcontr. apply Hallows. by intros ->. }
      simplify_map_eq. eauto.
  Qed.

   Lemma mem_map_recover_res:
    ∀ (regs : leibnizO Reg) (mem : Mem) (r : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr) (storev loadv : Word),
      reg_allows_store regs r p b e a
      → mem !! a = Some loadv
      → allow_store_mem regs mem r pc_a pc_w p b e a
        -∗ ([∗ map] a'↦w ∈ (<[a:=storev]> mem), a' ↦ₐ w)
        -∗ interp storev
        ={allow_store_mask regs r pc_a p b e a, ⊤ ∖ ↑logN.@pc_a}=∗
            if decide (reg_allows_store regs r p b e a ∧ a = pc_a)
            then pc_a ↦ₐ storev
            else pc_a ↦ₐ pc_w.
  Proof.
    intros regs mem r pc_a pc_w p b e a storev loadv Hrar Hloadv.
    iIntros "HLoadMem Hmem Hvalid".
    rewrite /allow_store_mask.
    iDestruct "HLoadMem" as "[% HLoadRes]".
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0) "[-> [Hval Hcls] ]".
       simplify_map_eq. rewrite insert_insert.
       rewrite memMap_resource_2ne; last auto. iDestruct "Hmem" as  "[Ha1 Haw]".
       iMod ("Hcls" with "[Ha1 Hvalid]") as "_";[iNext;iExists storev;iFrame|]. iModIntro.
       rewrite decide_False; [done|]. apply not_and_r. right. auto.
    - apply not_and_r in Hdec as [| <-%dec_stable].
      * by exfalso.
      * iDestruct "HLoadRes" as "->".
        rewrite insert_insert.
        rewrite -memMap_resource_1. simplify_map_eq. by iFrame.
  Qed.

  Lemma store_case (regs : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst : RegName)
        (src : Z + RegName) (P : D):
    ftlr_instr regs p b e a widc w (Store dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p b e a]> (<[idc:=widc]> regs) !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      destruct (decide (x = idc)).
      rewrite lookup_insert_ne; auto.
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      by rewrite! lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0 , read_reg_inr (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) dst p0 b0 e0 a0)
      as [p0 [b0 [e0 [a0 HVdst] ] ] ].
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. rewrite Hsomedst.
      destruct wdst as [|[ p0 b0 e0 a0|] | ]; try done.
      by repeat eexists.
    }

    assert (∃ storev, word_of_argument (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) src = Some storev)
      as [storev Hwoa].
    { destruct src; cbn.
      - by exists (WInt z).
      - specialize Hsome' with r as Hr.
        destruct Hr as [wsrc Hsomer].
        exists wsrc. by rewrite Hsomer.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_store_res with "Hreg Hinv_idc") as "HStoreRes"; eauto.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iMod (store_res_implies_mem_map with "HStoreRes Ha") as (mem) "[HStoreMem >HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iApply (wp_store with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [* ? ? ? -> Hincr|* -> Hincr].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto.
      specialize (store_inr_eq H1 HVdst) as (-> & -> & -> & ->).

      (* The stored value is valid *)
      iAssert (interp storev0) as "#Hvalidstore".
      { destruct src; inversion H0. rewrite !fixpoint_interp1_eq. done.
        simplify_map_eq.
        destruct ((<[PC:=WCap x x0 x1 x2]> (<[idc:=widc]> regs)) !! r) eqn:Hsomer;simplify_map_eq.
        2 : { rewrite Hsomer in Hwoa. done. }
        destruct (decide (r = PC)).
        - subst. simplify_map_eq. iFrame "Hinv_pc".
        - simplify_map_eq.
          destruct (decide (r = idc)) as [?|Hneq]; simplify_map_eq; auto.
          iSpecialize ("Hreg" $! _ _ n Hneq Hsomer).
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
          + iNext. iExists w. iFrame.
        - rewrite decide_False. iNext. iExists w. iFrame.
          intros [Hcontr ->].
          apply Hwrite. exists dst.
          destruct Hcontr as (Hlookup & Hwa & Hwb). simplify_map_eq.
          apply andb_prop in Hwb.
          revert Hwb. rewrite Z.leb_le Z.ltb_lt. intros. eexists _.
          rewrite insert_commute //=.
      }

      simplify_map_eq.
      rewrite insert_insert.

      iModIntro; iNext; iIntros "_".
      set (widc' := if (decide (dst = idc))
                    then storev
                    else widc).
      rewrite (insert_commute _ _ _ (WCap _ _ _ x3)) //= .
      iApply ("IH" $! regs _ _ _ _ widc with "[%] [] [$Hmap] [$Hown]"); auto.
      { rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->]; by iFrame "#". }
    }
    { rewrite /allow_store_res /allow_store_mem /allow_store_mask.
      destruct
        (decide (reg_allows_store (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) dst p0 b0 e0 a0 ∧ a0 ≠ a)).
      - iDestruct "HStoreMem" as "(%&H)".
        iDestruct "H" as (w') "(->&[Hres Hcls'])". rewrite /region_open_resources.
        destruct a1. simplify_map_eq. rewrite memMap_resource_2ne; last auto.
        iDestruct "Hmem" as "[Ha0 Ha]".
        iMod ("Hcls'" with "[Ha0 Hres]");[iExists w';iFrame|iModIntro].
        iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
      - iModIntro. iDestruct "HStoreMem" as "(_&->)". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }
  Qed.

End fundamental.
