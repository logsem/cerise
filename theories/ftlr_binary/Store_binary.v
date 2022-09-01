From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel_binary.
From cap_machine Require Import ftlr_base_binary.
From cap_machine.rules_binary Require Import rules_binary_base rules_binary_Store.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma Store_spec_determ r dst src regs regs' mem0 mem0' mem0'' retv retv' :
    Store_spec r dst src regs mem0 mem0' retv →
    Store_spec r dst src regs' mem0 mem0'' retv' →
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv' /\ mem0' = mem0''.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; repeat split; auto; try congruence.
    - destruct H1. inv H7; try congruence.
    - destruct H1. inv H7; try congruence.
      rewrite H5 in H1; inv H1. destruct H3; destruct H6; congruence.
    - destruct H1. inv H7; try congruence.
      rewrite H5 in H1; inv H1.
      destruct H3; destruct H6; congruence.
    - destruct H1. inv H7; try congruence.
      rewrite H5 in H1; inv H1. destruct H3; destruct H6; congruence.
    - destruct H4; inv H1; try congruence.
      rewrite H4 in H0; inv H0. destruct H2; destruct H6; congruence.
    - destruct H4; inv H1; try congruence.
      rewrite H4 in H0; inv H0. destruct H2; destruct H6; congruence.
  Qed.

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  (* Since we will store a new word into a, we do not need to remember its validity *)
  Definition region_open_resources (a pc_a : Addr) pc_w : iProp Σ :=
    (▷ interp (pc_w, pc_w) ∗ ((▷ ∃ w0 w1, a ↦ₐ w0 ∗ a ↣ₐ w1 ∗ interp (w0,w1)) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a,⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Lemma store_inr_eq {regs r p0 b0 e0 a0 p1 b1 e1 a1}:
    reg_allows_store regs r p0 b0 e0 a0 →
    read_reg_inr regs r p1 b1 e1 a1 →
    p0 = p1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). destruct H3 as [Hinr1 | Hinl1].
      * rewrite Hinr0 in Hinr1. inversion Hinr1.
        subst;auto.
      * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
  Qed.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_store_res r1 (regs : Reg) pc_a a p b e :=
    (⌜read_reg_inr regs r1 p b e a⌝ ∗
      if decide (reg_allows_store regs r1 p b e a ∧ a ≠ pc_a) then
          |={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a}=> ∃ w, a ↦ₐ w ∗ a ↣ₐ w ∗  region_open_resources a pc_a w
    else True)%I.

  Definition allow_store_mem r1 (regs : Reg) pc_a pc_w (mem : gmap Addr Word) p b e a :=
    (⌜read_reg_inr regs r1 p b e a⌝ ∗
    if decide (reg_allows_store regs r1 p b e a ∧ a ≠ pc_a) then
         ∃ w, ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝ ∗ region_open_resources a pc_a w
    else ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma create_store_res:
    ∀ (r : leibnizO Reg) (p : Perm)
      (b e a : Addr) (r1 : RegName) (p0 : Perm)
      (b0 e0 a0 : Addr),
      read_reg_inr (<[PC:=WCap p b e a]> r) r1 p0 b0 e0 a0
      → (∀ (r0 : RegName) v1 v2, (⌜r0 ≠ PC⌝  → ⌜r !! r0 = Some v1⌝ → ⌜r !! r0 = Some v2⌝ → (fixpoint interp1) (v1, v2)))
          -∗ allow_store_res r1 (<[PC:=WCap p b e a]> r) a a0 p0 b0 e0.
  Proof.
    intros r p b e a r1 p0 b0 e0 a0 HVr1.
    iIntros "#Hreg".
    iFrame "%".
    case_decide as Hallows.
    - destruct Hallows as ((Hrinr & Hra & Hwb) & Haeq).
      apply andb_prop in Hwb as [Hle Hge].
      revert Hle Hge. rewrite !Z.leb_le Z.ltb_lt =>Hle Hge.
      assert (r1 ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.

      rewrite lookup_insert_ne in Hrinr; last by congruence.
      iDestruct ("Hreg" $! r1 _ _ n Hrinr Hrinr) as "Hvsrc".
      iAssert (inv (logN.@a0) ((interp_ref_inv a0) interp))%I as "#Hinva".
      { iApply (write_allowed_inv with "Hvsrc"); auto. }
      iFrame "∗ #".
      iMod (inv_acc with "Hinva") as "[Hinv Hcls']";[solve_ndisj|].
      iDestruct "Hinv" as (w w') "[>Ha [>Ha' #Hinv] ]".
      iExists w. iFrame. iDestruct (interp_eq with "Hinv") as ">%". subst w'.
      iModIntro. iFrame "∗ #".
    - done.
  Qed.

  Lemma store_res_implies_mem_map:
    ∀ (r : leibnizO Reg)
       (a a0 : Addr) (w : Word) (r1 : RegName) p1 b1 e1,
      allow_store_res r1 r a a0 p1 b1 e1
      -∗ a ↦ₐ w -∗ a ↣ₐ w
      ={⊤ ∖ ↑logN.@a, if decide (reg_allows_store r r1 p1 b1 e1 a0 ∧ a0 ≠ a) then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0
                      else ⊤ ∖ ↑logN.@a}=∗ ∃ mem0 : gmap Addr Word,
          allow_store_mem r1 r a w mem0 p1 b1 e1 a0
            ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w) ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↣ₐ w).
  Proof.
    intros r a a0 w r1 p1 b1 e1.
    iIntros "HStoreRes Ha Ha'".
    iDestruct "HStoreRes" as "(% & HStoreRes)".

    case_decide as Hallows.
    - iMod "HStoreRes" as (w0) "[Ha0 [Ha0' HStoreRest] ]".
      iExists _.
      iSplitL "HStoreRest".
      * iFrame "%".
        case_decide; last by exfalso.
        iExists w0. iSplitR; auto.
      * iModIntro. iSplitL "Ha Ha0"; iNext.
        { destruct Hallows as ((Hrinr & Hra & Hwb) & Hne).
          iApply memMap_resource_2ne; auto; iFrame. }
        { destruct Hallows as ((Hrinr & Hra & Hwb) & Hne).
          iApply rules_binary_base.memMap_resource_2ne; auto; iFrame. }
    - iExists _.
      iSplitR "Ha Ha'".
      + iFrame "%".
        case_decide; first by exfalso. auto.
      + iModIntro. iSplitL "Ha"; iNext.
        * by iApply memMap_resource_1.
        * iApply big_sepM_insert; auto.
  Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (r : leibnizO Reg)
      (a a0 : Addr) (w : Word) (r1 : RegName)
      (mem0 : gmap Addr Word) p b e,
        allow_store_mem r1 r a w mem0 p b e a0
        -∗ ⌜mem0 !! a = Some w⌝
          ∗ ⌜allow_store_map_or_true r1 r mem0⌝.
  Proof.
    iIntros (r a a0 w r1 mem0 p b e) "HStoreMem".
    iDestruct "HStoreMem" as "(% & HStoreRes)".
    case_decide as Hallows.
    - pose(Hallows' := Hallows).
      destruct Hallows' as ((Hrinr & Hra & Hwb) & Hne).
      iDestruct "HStoreRes" as (w0 ->) "HStoreRest".
      iSplitR. rewrite lookup_insert_ne; auto. by rewrite lookup_insert.
      iExists p,b,e,a0. iSplit;auto.
      iPureIntro. case_decide;auto.
      exists w0. by simplify_map_eq.
    - iDestruct "HStoreRes" as "->".
      iSplitR. by rewrite lookup_insert.
      iExists p,b,e,a0. repeat iSplitR; auto.
      case_decide as Hdec1; last by done.
      apply not_and_l in Hallows as [Hallows | Hallows]; try contradiction.
      assert (a0 = a) as ->.
      { apply finz_to_z_eq, Z.eq_dne. intros Hcontr. apply Hallows. by intros ->. }
      simplify_map_eq. eauto.
  Qed.

  Lemma mem_map_recover_res:
    ∀ (r : leibnizO Reg)
      (a : Addr) (w : Word) (src : RegName) p0
      (b0 e0 a0 : Addr) (mem0 : gmap Addr Word) storev loadv,
      reg_allows_store r src p0 b0 e0 a0
      → mem0 !! a0 = Some loadv
      → allow_store_mem src r a w mem0 p0 b0 e0 a0
                        -∗ ([∗ map] a1↦w ∈ (<[a0:=storev]> mem0), a1 ↦ₐ w ∗ a1 ↣ₐ w)
                        -∗ interp (storev,storev)
        ={if decide (reg_allows_store r src p0 b0 e0 a0 ∧ a0 ≠ a) then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0 else ⊤ ∖ ↑logN.@a,⊤ ∖ ↑logN.@a}=∗                                                                                                                               if decide (reg_allows_store r src p0 b0 e0 a0 ∧ a0 = a) then a ↦ₐ storev ∗ a ↣ₐ storev else a ↦ₐ w ∗ a ↣ₐ w.
  Proof.
    intros r a w src p0 b0 e0 a0 mem0 storev loadv Hrar Hloadv.
    iIntros "HLoadMem Hmem Hvalid".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    (* destruct (load_inr_eq Hrar H0) as (<- & <- &<- &<- &<-). *)
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0) "[-> [Hval Hcls] ]".
       simplify_map_eq. rewrite insert_insert.
       iDestruct (big_sepM_sep with "Hmem") as "[Hmem1 Hmem2]".
       rewrite memMap_resource_2ne; last auto.
       rewrite rules_binary_base.memMap_resource_2ne; last auto.
       iDestruct "Hmem1" as  "[Ha1 Haw]".
       iDestruct "Hmem2" as  "[Ha1' Haw']".
       iMod ("Hcls" with "[Ha1 Ha1' Hvalid]") as "_";[iNext;iExists storev;iExists storev; iFrame|]. iModIntro.
       rewrite decide_False; [iFrame|]. apply not_and_r. right. auto.
    - apply not_and_r in Hdec as [| <-%dec_stable].
      * by exfalso.
      * iDestruct "HLoadRes" as "->".
        rewrite insert_insert.
       iDestruct (big_sepM_sep with "Hmem") as "[Hmem1 Hmem2]".
       rewrite -memMap_resource_1. simplify_map_eq. iFrame.
       iDestruct (big_sepM_insert with "Hmem2") as "[A B]"; auto.
  Qed.

  Lemma store_case (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (b e a : Addr) (w w' : Word) (dst : RegName) (src : Z + RegName) (P : D):
    ftlr_instr r p b e a w w' (Store dst src) P.
  Proof.
    intros Hp Hsome HisCorrect Hbae Hi.
    iIntros "#IH #Hspec #Hinv #Hreg #Hinva #Hread Hsmap Hown Hs Ha Ha' HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p b e a]> r.1 !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 !lookup_insert; unfold is_Some. eexists; eauto.
      rewrite !lookup_insert_ne; auto. destruct (Hsome x); auto.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0 , read_reg_inr (<[PC:=WCap p b e a]> r.1) dst p0 b0 e0 a0) as [p0 [b0 [e0 [a0 HVdst] ] ] ].
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. destruct wdst. all: repeat eexists.
      right. by exists z. by left.
    }

    assert (∃ storev, word_of_argument (<[PC:=WCap p b e a]> r.1) src = Some storev) as [storev Hwoa].
    { destruct src; cbn.
      - by exists (WInt z).
             - specialize Hsome' with r0 as Hr0.
               destruct Hr0 as [wsrc Hsomer0].
               exists wsrc. by rewrite Hsomer0.
    }

    iDestruct (interp_reg_dupl with "[Hreg]") as "[_ #Hreg']";[iSplit;[iPureIntro;apply Hsome|iFrame "Hreg"]|].
    simpl.

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_store_res with "Hreg'") as "HStoreRes"; eauto.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iAssert (▷ ⌜w = w'⌝)%I with "[HP]" as "#>%";[|subst w'].
    { iDestruct "Hread" as "[Hread _]". iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
    iMod (store_res_implies_mem_map with "HStoreRes Ha Ha'") as (mem) "[HStoreMem [>HMemRes >HMemRes'] ]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iApply (wp_store with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto.
      right; destruct (Hsome rr); auto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct r as [r1 r2]. simpl in *.
    iDestruct (interp_reg_eq r1 r2 (WCap p b e a) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.

    (* we take a step in the specification code *)
    iMod (step_store _ [SeqCtx] with "[$HMemRes' $Hsmap $Hs $Hspec]") as (retv' regs'' mem'') "(Hs & Hs' & Hsmem & Hsmap) /=";eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. destruct (decide (PC = rr));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne //].
      destruct Hsome with rr;eauto. }
    { destruct (decide (reg_allows_store (<[PC:=WCap p b e a]> r1) dst p0 b0 e0 a0 ∧ a0 ≠ a)); solve_ndisj. }
    iDestruct "Hs" as %HSpec'.

    specialize (Store_spec_determ _ _ _ _ _ _ _ _ _ _ HSpec HSpec') as [Hregs [<- <-] ].

    destruct HSpec as [* ? ? ? -> Hincr|* -> Hincr ].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto.
      specialize (store_inr_eq H1 HVdst) as (-> & -> & -> & ->).

      (* The stored value is valid *)
      iAssert (interp (storev0, storev0)) as "#Hvalidstore".
      { destruct src; inversion H0. rewrite !fixpoint_interp1_eq. done.
        rewrite lookup_insert in H3; inv H3.
        simplify_map_eq. destruct (Hsome' r) as [xx Hsomer0].
        destruct (decide (r = PC)).
        - subst. rewrite lookup_insert in Hsomer0; inv Hsomer0.
          simplify_map_eq. rewrite lookup_insert in Hwoa; inv Hwoa; iFrame "Hinv".
        - rewrite lookup_insert_ne in Hwoa; auto.
          simplify_map_eq.
            by iSpecialize ("Hreg'" $! _ _ _ n Hwoa Hwoa).
      }

      (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      destruct Hregs as [<- |]; [|congruence].
      iMod (mem_map_recover_res with "[$HStoreMem] [Hmem Hsmem] [$Hvalidstore]") as "Ha"; eauto.
      { iApply (big_sepM_sep with "[$Hmem $Hsmem]"). }

      iModIntro. iMod ("Hcls" with "[HP Ha]").
      { simplify_map_eq.
        case_decide as Hwrite.
        - case_decide.
          + iNext. iExists storev. iExists storev.
            iDestruct "Hread" as "[Hread1 Hread2]".
            iDestruct ("Hread2" with "Hvalidstore") as "HPstore".
            iFrame "∗ #". iExact "Ha".
          + iNext. iExists w. iExists w. iFrame. iExact "Ha".
        - rewrite decide_False. iNext. iExists w. iExists w. iFrame. iExact "Ha".
          intros [Hcontr ->].
          apply Hwrite. exists dst.
          destruct Hcontr as (Hlookup & Hwa & Hwb). simplify_map_eq.
          apply andb_prop in Hwb.
          eexists _. split; first eassumption. cbn.
          revert Hwb. rewrite Z.leb_le Z.ltb_lt. auto.
      }

      simplify_map_eq.
      rewrite insert_insert.

      iMod (do_step_pure _ [] with "[$Hspec $Hs']") as "Hs /=". solve_ndisj.
      iModIntro;iNext;iIntros "_".
      iApply ("IH" $! (r1, r1) with "[] [] Hmap Hsmap Hown Hs Hspec");auto.
      { iPureIntro. simpl. intros.  destruct (Hsome x4) as [A _]. auto. }
      { iModIntro. rewrite lookup_insert in H3; inv H3.
        rewrite /interp !fixpoint_interp1_eq /=. destruct Hp as [-> | ->]; iDestruct "Hinv" as "[_ $]";auto. }
    }
    { rewrite /allow_store_res /allow_store_mem.
      destruct (decide (reg_allows_store (<[PC:=WCap p b e a]> r1) dst p0 b0 e0 a0 ∧ a0 ≠ a)).
      - iDestruct "HStoreMem" as "(%&H)".
        iDestruct "H" as (w') "(->&[Hres Hcls'])". rewrite /region_open_resources.
        destruct a1. simplify_map_eq. rewrite memMap_resource_2ne; last auto.
        rewrite rules_binary_base.memMap_resource_2ne; last auto.
        iDestruct "Hmem" as "[Ha0 Ha]".
        iDestruct "Hsmem" as "[Hsa0 Hsa]".
        iMod ("Hcls'" with "[Ha0 Hsa0 Hres]");[iExists w';iExists w'; iFrame|iModIntro].
        iMod ("Hcls" with "[Ha Hsa HP]");[iExists w; iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext;iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
      - iModIntro. iDestruct "HStoreMem" as "(_&->)". rewrite -memMap_resource_1.
        iDestruct (big_sepM_insert with "Hsmem") as "[Hsmem _]"; auto.
        iMod ("Hcls" with "[Hmem Hsmem HP]");[iExists w;iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext;iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
