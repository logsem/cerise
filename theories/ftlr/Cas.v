From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_CAS.
Import uPred.


Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  Definition region_open_resources (a pc_a : Addr) w : iProp Σ :=
    (▷ interp w ∗ ((▷ ∃ w0, a ↦ₐ w0 ∗ interp w0) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a,⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Lemma store_inr_eq {regs i r p0 b0 e0 a0 p1 b1 e1 a1}:
    reg_allows_store i regs r p0 b0 e0 a0 →
    read_reg_inr regs i r p1 b1 e1 a1 →
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
  Definition allow_store_res r1 (regs : Reg) i pc_a a p b e :=
    (⌜read_reg_inr regs i r1 p b e a⌝ ∗
      if decide (reg_allows_store i regs r1 p b e a ∧ a ≠ pc_a)
      (* r1 -> WCap p b e a , is a valid capability that allows to write in a *)
      then |={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a}=>
             ∃ w, a ↦ₐ w
                  ∗ region_open_resources a pc_a w ∗ ▷ interp w
      else True)%I.

  Definition allow_store_mem i r1 (regs : Reg) pc_a pc_w (mem : gmap Addr Word)
    p b e a (f:bool)  :=
    (⌜read_reg_inr regs i r1 p b e a⌝ ∗
    if decide (reg_allows_store i regs r1 p b e a ∧ a ≠ pc_a)
    (* r1 -> WCap p b e a , is a valid capability that allows to write in a *)
    then ∃ w, ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝
              ∗ region_open_resources a pc_a w ∗ (if f then ▷ interp w else interp w)
    else ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I. (* if not allowed to write, the memory doesn't change *)

  Lemma create_store_res:
    ∀ (r : leibnizO Reg) (i: CoreN) (p : Perm)
      (b e a : Addr) (r1 : RegName) (p0 : Perm)
      (b0 e0 a0 : Addr),
      read_reg_inr (<[(i, PC):=WCap p b e a]> r) i r1 p0 b0 e0 a0
      → (∀ (r1 : RegName) v, ⌜(i, r1) ≠ (i, PC)⌝ → ⌜r !! (i, r1) = Some v⌝ → (fixpoint interp1) v)
          -∗ allow_store_res r1 (<[(i, PC):=WCap p b e a]> r) i a a0 p0 b0 e0.
  Proof.
    intros r i p b e a src p0 b0 e0 a0 HVsrc.
    iIntros "#Hreg". rewrite /allow_store_res.
    iFrame "%".
    case_decide as Hdec. 1: destruct Hdec as [Hallows Haeq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
         apply andb_prop in Hwb as [Hle Hge].
         revert Hle Hge. rewrite !Z.leb_le Z.ltb_lt =>Hle Hge.

         assert (src ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.

         rewrite lookup_insert_ne in Hrinr; last by congruence.
         assert ((i,src) ≠ (i,PC)) by simplify_pair_eq.
         iDestruct ("Hreg" $! src _ H0 Hrinr) as "Hvsrc".
         iAssert (inv (logN.@a0) ((interp_ref_inv a0) interp))%I as "#Hinv".
         { iApply (write_allowed_inv with "Hvsrc"); auto. }
         iMod (inv_acc (⊤ ∖ ↑logN.@a) with "Hinv") as "[Hrefinv Hcls]";[solve_ndisj|].
         rewrite /interp_ref_inv /=. iDestruct "Hrefinv" as (w) "[>Ha #HP]".
         iExists w.
         iAssert (▷ interp w)%I as "#Hw".
         { iNext. iFrame "HP". }
         iFrame "∗ #". iModIntro. rewrite /region_open_resources. done.
    - done.
  Qed.

  Lemma store_res_implies_mem_map:
    ∀ (r : leibnizO Reg) (i: CoreN)
       (a a0 : Addr) (w : Word) (r1 : RegName) p1 b1 e1,
      allow_store_res r1 r i a a0 p1 b1 e1
      -∗ a ↦ₐ w
      ={⊤ ∖ ↑logN.@a,
      if decide (reg_allows_store i r r1 p1 b1 e1 a0 ∧ a0 ≠ a)
      then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0
      else ⊤ ∖ ↑logN.@a}=∗ ∃ mem0 : gmap Addr Word,
          allow_store_mem i r1 r a w mem0 p1 b1 e1 a0 true
          ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w).
  Proof.
       intros r i a a0 w src p1 b1 e1.
    iIntros "HLoadRes Ha".
    iDestruct "HLoadRes" as "[% HLoadRes]".

    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       iMod "HLoadRes" as (w0) "[Ha0 [HLoadRest #Hval] ]".
       iExists _.
       iSplitL "HLoadRest".
       + iSplitR; first auto.

         case_decide as Hdec1.
         2: apply not_and_r in Hdec1 as [|]; by exfalso.
         iExists w0. iSplitR; auto.
       + iModIntro. iNext.
         rewrite memMap_resource_2ne; auto; iFrame.
    - rewrite /read_reg_inr in H0.
      iExists _.
      iSplitL "HLoadRes".
      + iModIntro. rewrite /allow_store_mem. iSplitR; auto.
        case_decide; first by exfalso. auto.
      + iModIntro. iNext. by iApply memMap_resource_1.
  Qed.


  Lemma mem_map_implies_pure_conds:
    ∀ (r : leibnizO Reg) (i: CoreN)
      (a a0 : Addr) (w : Word) (r1 : RegName)
      (mem0 : gmap Addr Word) p b e,
        allow_store_mem i r1 r a w mem0 p b e a0 true
        -∗ ⌜mem0 !! a = Some w⌝
          ∗ ⌜allow_store_map_or_true i r1 r mem0⌝.
  Proof.
    iIntros (r i a a0 w r1 mem0 p b e) "HStoreMem".
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

  Lemma allow_store_mem_later:
    ∀ (r : leibnizO Reg) (i: CoreN) (p : Perm)
      (b e a a0 : Addr) (w : Word) (src : RegName)
      (mem0 : gmap Addr Word) p0 b0 e0,
    allow_store_mem i src r a w mem0 p0 b0 e0 a0 true
    -∗ ▷ allow_store_mem i src r a w mem0 p0 b0 e0 a0 false.
  Proof.
    intros.
    iIntros "HLoadMem".
    iDestruct "HLoadMem" as "[% HLoadMem]".
    rewrite !/allow_store_mem /=. iSplit;[auto|].
    destruct (decide (reg_allows_store i r src p0 b0 e0 a0 ∧ a0 ≠ a)).
    - iApply later_exist_2. iDestruct "HLoadMem" as (w0) "(?&HP&?)".
      iExists w0. iNext. iDestruct "HP" as "(?&?)". iFrame.
    - iNext. iFrame.
  Qed.

  Instance if_Persistent i p b e a r loc p0 b0 e0 a0 loadv : Persistent
                                                               (if decide
                                                                     (reg_allows_store i (<[(i, PC):=WCap p b e a]> r) loc p0 b0 e0 a0 ∧ a0 ≠ a)
                                                                then interp loadv
                                                                else emp)%I.
  Proof. intros. destruct (decide (reg_allows_store i (<[(i, PC):=WCap p b e a]> r) loc p0 b0 e0 a0 ∧ a0 ≠ a));apply _. Qed.


  Lemma mem_map_recover_res:
    ∀ (r : leibnizO Reg) (i: CoreN)
      (a : Addr) (w : Word) (src : RegName) p0
      (b0 e0 a0 : Addr) (mem0 : gmap Addr Word) storev loadv,
    reg_allows_store i r src p0 b0 e0 a0
    → mem0 !! a0 = Some loadv
    → allow_store_mem i src r a w mem0 p0 b0 e0 a0 false
      -∗ ([∗ map] a1↦w ∈ (<[a0:=storev]> mem0), a1 ↦ₐ w)
      -∗ interp storev
      ={if decide (reg_allows_store i r src p0 b0 e0 a0 ∧ a0 ≠ a)
        then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0
        else ⊤ ∖ ↑logN.@a,⊤ ∖ ↑logN.@a}=∗
                                          if decide (reg_allows_store i r src p0 b0 e0 a0 ∧ a0 = a)
                                          then a ↦ₐ storev
                                          else a ↦ₐ w.
  Proof.
    intros r i a w src p0 b0 e0 a0 mem0 storev loadv Hrar Hloadv.
    iIntros "HLoadMem Hmem Hvalid".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0) "[-> [[Hval Hcls] Hv]]".
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


  Lemma mem_map_recover_res2:
    ∀ (r : leibnizO Reg) (i: CoreN)
      (a : Addr) (w : Word) (src : RegName) p0
      (b0 e0 a0 : Addr) (mem0 : gmap Addr Word) loadv,
    reg_allows_store i r src p0 b0 e0 a0
    → mem0 !! a0 = Some loadv
    → allow_store_mem i src r a w mem0 p0 b0 e0 a0 false
      -∗ ([∗ map] a1↦w ∈ mem0, a1 ↦ₐ w)
      ={if decide (reg_allows_store i r src p0 b0 e0 a0 ∧ a0 ≠ a)
        then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0
        else ⊤ ∖ ↑logN.@a,⊤ ∖ ↑logN.@a}=∗ a ↦ₐ w ∗
                                          if decide (reg_allows_store i r src p0 b0 e0 a0 ∧ a0 ≠ a)
                                          then interp loadv
                                          else emp.
  Proof.
    intros r i a w src p0 b0 e0 a0 mem0 loadv Hrar Hloadv.
    iIntros "HLoadMem Hmem".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0) "[-> [[Hval Hcls] #Hv]]".
       simplify_map_eq.
       rewrite memMap_resource_2ne; last auto. iDestruct "Hmem" as  "[Ha1 Haw]".
       iMod ("Hcls" with "[Ha1 Hv]") as "_";[iNext;iExists _;iFrame "#∗"|]. iModIntro .
       iFrame "#∗".
    - apply not_and_r in Hdec as [| <-%dec_stable].
      * by exfalso.
      * iDestruct "HLoadRes" as "->".
        rewrite -memMap_resource_1. simplify_map_eq.
        iFrame.
        done.
  Qed.


  Lemma cas_case (r : leibnizO Reg) (p : Perm) (b e a : Addr) (w : Word)
    (loc cond newvalue: RegName) (i: CoreN) P :
    ftlr_instr r p b e a w (CAS loc cond newvalue) i P.
  Proof.
    intros Hp Hsome i' Hbae Hi.
    apply forall_and_distr in Hsome ; destruct Hsome as [Hsome Hnone].
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Ha HP Hcls HPC Hmap".


    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_cas *)
    assert(∀ x : RegName, is_Some (<[(i, PC):=WCap p b e a]> r !! (i, x))) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
        by rewrite lookup_insert_ne ; simplify_pair_eq.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0 , read_reg_inr (<[(i,PC):=WCap p b e a]> r) i loc p0 b0 e0 a0) as [p0 [b0 [e0 [a0 HVloc] ] ] ].
    {
      specialize Hsome' with loc as Hloc.
      destruct Hloc as [wloc Hsomeloc].
      unfold read_reg_inr. destruct wloc. all: repeat eexists.
      right. by exists z. by left.
    }

     assert (∃ oldv, (<[(i, PC):=WCap p b e a]> r) !! (i, newvalue) = Some oldv) as [oldv Hwoa].
    { specialize Hsome' with newvalue as Hnewvalue.
      destruct Hnewvalue as [wnewv Hsomenewvalue].
      exists wnewv. by rewrite Hsomenewvalue.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_store_res with "Hreg") as "HStoreRes"; eauto.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iMod (store_res_implies_mem_map with "HStoreRes Ha") as (mem) "[HStoreMem >HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HStoreMem") as %(HReadPC & HStoreAP); auto.
    (* Step 3.5: move the later outside, so that we can remove it after applying wp_cas *)
    iDestruct (allow_store_mem_later with "HStoreMem") as "HStoreMem"; auto.

    iApply (wp_Cas with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /regs_of_core /subseteq /map_subseteq /set_subseteq_instance. intros rr ?.
      apply elem_of_gmap_dom. set_solver. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    iDestruct ("Hread" with "HP") as "#Hw".

    destruct HSpec as [ * -> -> Hfail | * ? ? ? ? -> Hincr|* ? ? ? -> ? ? Hincr].
    - (* Failure *)
      rewrite /allow_store_res /allow_store_mem.
      destruct (decide (reg_allows_store i regs' loc p0 b0 e0 a0 ∧ a0 ≠ a)).
      + iDestruct "HStoreMem" as "(%&H)".
        iDestruct "H" as (w') "(->&[Hres Hcls'] & Hv)". rewrite /region_open_resources.
        destruct a1. simplify_map_eq. rewrite memMap_resource_2ne; last auto.
        iDestruct "Hmem" as "[Ha0 Ha]".
        iMod ("Hcls'" with "[Ha0 Hres]");[iExists w';iFrame|iModIntro].
        iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto.
      + iModIntro. iDestruct "HStoreMem" as "(_&->)". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto.

    - (* Success - Equality  *)
      apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto.
      specialize (store_inr_eq H0 HVloc) as (-> & -> & -> & ->).

    {  (* The stored value is valid *)
      iAssert (interp newv) as "#Hvalidnewv".
      { destruct (<[(i, PC):=WCap p b e a]> r !! (i, newvalue)) eqn:Hsomenewvalue
        ;simplify_map_eq by simplify_pair_eq.
        destruct (decide (newvalue = PC)).
        - subst. simplify_map_eq by simplify_pair_eq. iFrame "Hinv".
        - simplify_map_eq by simplify_pair_eq.
          assert ((i,newvalue) ≠ (i,PC)) by simplify_pair_eq.
          iSpecialize ("Hreg" $! _ _ H3 Hsomenewvalue).
          iFrame "Hreg".
      }

      (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iMod (mem_map_recover_res with "HStoreMem Hmem Hvalidnewv") as "Ha";[eauto|eauto|iModIntro].

      iMod ("Hcls" with "[HP Ha]").
      { simplify_map_eq.
        case_decide as Hwrite.
        - case_decide.
          + iNext. iExists oldv.
            iDestruct ("Hwrite" with "Hvalidnewv") as "HPstore".
            iFrame "∗ #".
          + iNext. iExists w. iFrame.
        - rewrite decide_False. iNext. iExists w. iFrame.
          intros [Hcontr ->].
          apply Hwrite. exists loc.
          destruct Hcontr as (Hlookup & Hwa & Hwb). simplify_map_eq.
          apply andb_prop in Hwb.
          revert Hwb. rewrite Z.leb_le Z.ltb_lt. intros. eexists _.
          split_and!; done.
      }

      simplify_map_eq  by simplify_pair_eq.
      (* rewrite insert_insert. *)

      iApply ("IH" with "[%] [] Hmap");auto.
      { intros; cbn.
        destruct (decide ( cond = x4 )) ; subst.
        split ; simplify_map_eq ; [by eexists|].
        intros j Hneq. repeat (rewrite lookup_insert_ne ; simplify_pair_eq).
        by apply Hnone.
        split ; simplify_map_eq.
        2: { intros j Hneq. repeat (rewrite lookup_insert_ne ; simplify_pair_eq).
        by apply Hnone. }

        rewrite lookup_insert_ne ; simplify_map_eq by simplify_pair_eq.
        destruct (decide ( PC = x4 )) ; subst.
        simplify_map_eq ; by eexists.
        rewrite lookup_insert_ne ; simplify_map_eq by simplify_pair_eq.
        by apply Hsome. }
      { iIntros (ri v Hri Hvs).
        destruct (decide ((i, ri) = (i, cond))).
        { simplify_pair_eq.
          rewrite lookup_insert in Hvs; auto. inversion Hvs.
          destruct (decide (a = a0)).
          - simplify_eq. iFrame "Hw".
          - simplify_eq.
            rewrite lookup_insert_ne in H4
            ; simplify_map_eq by simplify_pair_eq.
            rewrite lookup_insert_ne in H2
            ; simplify_map_eq by simplify_pair_eq.
            iApply "Hreg"; eauto.
            all: by apply pair_neq_inv'; apply not_eq_sym.
        }
        rewrite lookup_insert_ne in Hvs ; simplify_map_eq by simplify_pair_eq.
        iApply "Hreg" ; eauto.
        rewrite lookup_insert_ne in Hvs. done.
        simplify_pair_eq. 
        all: apply pair_neq_inv' ; by apply not_eq_sym.
      }
      { destruct ( decide (cond = PC))
        ; subst
        ; [|rewrite lookup_insert_ne in H4]
        ; simplify_map_eq by simplify_pair_eq
        ; do 3 iModIntro
        ; iApply interp_cap_range ; eauto
        ; destruct Hp ; subst ; auto.
      }
    }

    - (* Success - Non Equality  *)
      apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto.
      specialize (store_inr_eq H0 HVloc) as (-> & -> & -> & ->).


    {  (* The stored value is valid *)
      iAssert (interp newv) as "#Hvalidnewv".
      { destruct (<[(i, PC):=WCap p b e a]> r !! (i, newvalue)) eqn:Hsomenewvalue
        ;simplify_map_eq by simplify_pair_eq.
        destruct (decide (newvalue = PC)).
        - subst. simplify_map_eq by simplify_pair_eq. iFrame "Hinv".
        - simplify_map_eq by simplify_pair_eq.
          assert ((i,newvalue) ≠ (i,PC)) by simplify_pair_eq.
          iSpecialize ("Hreg" $! _ _ H4 Hsomenewvalue).
          iFrame "Hreg".
      }

      (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iMod (mem_map_recover_res2 with "HStoreMem Hmem") as "[Ha #Hinterp]"
      ; try eauto.
      (* {(* modify the definition of the lemma and don't store the new value *) } *)
      iModIntro.

      iMod ("Hcls" with "[HP Ha]").
      { simplify_map_eq.
        case_decide as Hwrite.
        - case_decide.
          iNext. iExists w.
              iFrame "∗ #".
          + iNext. iExists w. iFrame.
        - iNext. iExists w. iFrame.
      }

      simplify_map_eq  by simplify_pair_eq.

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC *)
      destruct (decide (x = RX ∨ x = RWX)).
      2 : {
        assert (x ≠ RX ∧ x ≠ RWX). split; by auto.
        iDestruct ((big_sepM_delete _ _ (i, PC)) with "Hmap") as "[HPC Hmap]".
        { subst. by rewrite lookup_insert. }
        iApply (wp_bind (fill [SeqCtx]) _ _ (_,_)).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext. iApply wp_value.
        iIntros (a1); inversion a1.
      }

      iApply ("IH" with "[%] [] Hmap");auto.
      { intros; cbn.
        destruct (decide ( cond = x4 )) ; subst.
        split ; simplify_map_eq ; [by eexists|].
        intros j Hneq. repeat (rewrite lookup_insert_ne ; simplify_pair_eq).
        by apply Hnone.
        split ; simplify_map_eq.
        2: { intros j Hneq. repeat (rewrite lookup_insert_ne ; simplify_pair_eq).
        by apply Hnone. }

        rewrite lookup_insert_ne ; simplify_map_eq by simplify_pair_eq.
        destruct (decide ( PC = x4 )) ; subst.
        simplify_map_eq ; by eexists.
        rewrite lookup_insert_ne ; simplify_map_eq by simplify_pair_eq.
        by apply Hsome. }
      { iIntros (ri v Hri Hvs).
        destruct (decide ((i, ri) = (i, cond))).
        { simplify_pair_eq.
          rewrite lookup_insert in Hvs; auto. inversion Hvs.
          destruct (decide (a = a0)).
          - simplify_eq. iFrame "Hw".
          - iClear "Hwrite". rewrite decide_True. iFrame "#". auto.
        }
        rewrite lookup_insert_ne in Hvs ; simplify_map_eq by simplify_pair_eq.
        iApply "Hreg" ; eauto.
        rewrite lookup_insert_ne in Hvs. done.
        simplify_pair_eq.
        all: apply pair_neq_inv' ; by apply not_eq_sym.
      }
      { iModIntro.
        destruct (decide (PC = cond)); simplify_eq.
        - simplify_map_eq. rewrite (fixpoint_interp1_eq).
          destruct (decide (a = a0)).
          + simplify_map_eq.
          + iClear "Hwrite". rewrite decide_True;auto. iModIntro.
            rewrite !fixpoint_interp1_eq.
            destruct o as [-> | ->]; iFrame "Hinterp".
        - assert ((i, cond) ≠ (i, PC)) by simplify_pair_eq.
          simplify_map_eq.
          iModIntro. iClear "Hw Hinterp Hwrite".
          rewrite !fixpoint_interp1_eq /=.
          destruct o as [-> | ->]; iFrame "Hinv".
      }
    Unshelve. all: auto.
    }
  Qed.
End fundamental.
