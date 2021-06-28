From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Store.
Import uPred.


Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  (* Since we will store a new word into a, we do not need to remember its validity *)
  Definition region_open_resources (a pc_a : Addr) pc_w : iProp Σ :=
    (▷ interp pc_w ∗ ((▷ ∃ w0, a ↦ₐ w0 ∗ interp w0) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a,⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

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
          |={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a}=> ∃ w, a ↦ₐ w ∗ region_open_resources a pc_a w 
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
      → (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜r !! r1 = Some v⌝ → (fixpoint interp1) v)
          -∗ allow_store_res r1 (<[PC:=WCap p b e a]> r) a a0 p0 b0 e0.
  Proof.
    intros r p b e a r1 p0 b0 e0 a0 HVr1.
    iIntros "#Hreg".
    iFrame "%".
    case_decide as Hallows.
    - destruct Hallows as ((Hrinr & Hra & Hwb) & Haeq).
      apply andb_prop in Hwb as [Hle Hge].
      revert Hle Hge. rewrite !/leb_addr !Z.leb_le Z.ltb_lt =>Hle Hge.
      assert (r1 ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.
      rewrite lookup_insert_ne in Hrinr; last by congruence.
      iDestruct ("Hreg" $! r1 _ n Hrinr) as "Hvsrc".
      iAssert (inv (logN.@a0) ((interp_ref_inv a0) interp))%I as "#Hinva".
      { iApply (write_allowed_inv with "Hvsrc"); auto. }
      iFrame "∗ #". 
      iMod (inv_acc with "Hinva") as "[Hinv Hcls']";[solve_ndisj|].
      iDestruct "Hinv" as (w) "[>Ha0 #Hinv]". 
      iExists w. iFrame. done.
    - done.  
  Qed.


  Lemma store_res_implies_mem_map:
    ∀ (r : leibnizO Reg)
       (a a0 : Addr) (w : Word) (r1 : RegName) p1 b1 e1,
      allow_store_res r1 r a a0 p1 b1 e1
      -∗ a ↦ₐ w
      ={⊤ ∖ ↑logN.@a, if decide (reg_allows_store r r1 p1 b1 e1 a0 ∧ a0 ≠ a) then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0
                      else ⊤ ∖ ↑logN.@a}=∗ ∃ mem0 : gmap Addr Word,
          allow_store_mem r1 r a w mem0 p1 b1 e1 a0
            ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w).
  Proof.
    intros r a a0 w r1 p1 b1 e1.
    iIntros "HStoreRes Ha".
    iDestruct "HStoreRes" as "(% & HStoreRes)".

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
      { apply z_of_eq, Z.eq_dne. intros Hcontr. apply Hallows. by intros ->. } 
      simplify_map_eq. eauto. 
  Qed.

   Lemma mem_map_recover_res:
    ∀ (r : leibnizO Reg)
       (a : Addr) (w : Word) (src : RegName) p0
       (b0 e0 a0 : Addr) (mem0 : gmap Addr Word) storev loadv,
      reg_allows_store r src p0 b0 e0 a0
      → mem0 !! a0 = Some loadv
      → allow_store_mem src r a w mem0 p0 b0 e0 a0
        -∗ ([∗ map] a1↦w ∈ (<[a0:=storev]> mem0), a1 ↦ₐ w)
        -∗ interp storev                
        ={if decide (reg_allows_store r src p0 b0 e0 a0 ∧ a0 ≠ a) then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0 else ⊤ ∖ ↑logN.@a,⊤ ∖ ↑logN.@a}=∗
            if decide (reg_allows_store r src p0 b0 e0 a0 ∧ a0 = a) then a ↦ₐ storev else a ↦ₐ w. 
  Proof.
    intros r a w src p0 b0 e0 a0 mem0 storev loadv Hrar Hloadv.
    iIntros "HLoadMem Hmem Hvalid".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    (* destruct (load_inr_eq Hrar H0) as (<- & <- &<- &<- &<-). *)
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

  Lemma store_case (r : leibnizO Reg) (p : Perm) (b e a : Addr) (w : Word) (dst : RegName) (src : Z + RegName) P :
    ftlr_instr r p b e a w (Store dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p b e a]> r !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
        by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0 , read_reg_inr (<[PC:=WCap p b e a]> r) dst p0 b0 e0 a0) as [p0 [b0 [e0 [a0 HVdst] ] ] ].
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. destruct wdst. all: repeat eexists.
      right. by exists z. by left.
    }

     assert (∃ storev, word_of_argument (<[PC:=WCap p b e a]> r) src = Some storev) as [storev Hwoa].
    { destruct src; cbn.
      - by exists (WInt z).
      - specialize Hsome' with r0 as Hr0.
        destruct Hr0 as [wsrc Hsomer0].
        exists wsrc. by rewrite Hsomer0.
    }
    
    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_store_res with "Hreg") as "HStoreRes"; eauto.

    
    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iMod (store_res_implies_mem_map with "HStoreRes Ha") as (mem) "[HStoreMem >HMemRes]".
    
    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iApply (wp_store with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. }
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
        simplify_map_eq. destruct (<[PC:=WCap x x0 x1 x2]> r !! r0) eqn:Hsomer0;simplify_map_eq.
        2 : { rewrite Hsomer0 in Hwoa. done. }
        destruct (decide (r0 = PC)).
        - subst. simplify_map_eq. iFrame "Hinv".
        - simplify_map_eq. iSpecialize ("Hreg" $! _ _ n Hwoa).
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
          split_and!; done.
      }
      
      simplify_map_eq.
      rewrite insert_insert.
      
      iApply ("IH" with "[%] [] Hmap [$Hown]");auto.
      { rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->]; by iFrame "#". }
    }
    { rewrite /allow_store_res /allow_store_mem.
      destruct (decide (reg_allows_store (<[PC:=WCap p b e a]> r) dst p0 b0 e0 a0 ∧ a0 ≠ a)).
      - iDestruct "HStoreMem" as "(%&H)".
        iDestruct "H" as (w') "(->&[Hres Hcls'])". rewrite /region_open_resources.
        destruct a1. simplify_map_eq. rewrite memMap_resource_2ne; last auto.
        iDestruct "Hmem" as "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Ha0 Hres]");[iExists w';iFrame|iModIntro].
        iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. 
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto. iNext. iIntros; discriminate.
      - iModIntro. iDestruct "HStoreMem" as "(_&->)". rewrite -memMap_resource_1. 
        iMod ("Hcls" with "[Hmem HP]");[iExists w;iFrame|iModIntro]. 
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto. iNext. iIntros; discriminate.
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
