From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Load.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately
   The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources (P : D) (w : Word) (a pc_a : Addr) (f:bool) : iProp Σ :=
    ((if f then ▷ P w else P w)
       ∗ read_cond P interp
       ∗ ((▷ ∃ w0, a ↦ₐ w0 ∗ P w0) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a,⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Lemma load_inr_eq {regs r p0 b0 e0 a0 p1 b1 e1 a1}:
    reg_allows_load regs r p0 b0 e0 a0 →
    read_reg_inr regs r p1 b1 e1 a1 →
    p0 = p1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). rewrite /read_reg_inr Hinr0 in H3. by inversion H3.
  Qed.


  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_load_res (regs : Reg) (r : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr) (P : D) :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
       if decide (reg_allows_load regs r p b e a ∧ a ≠ pc_a )
       then (|={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a}=>
              ∃ w, a ↦ₐ w ∗ region_open_resources P w a pc_a true ∗ ▷ interp w)
       else True)%I.

  Definition allow_load_mem (regs : Reg) (mem : Mem) (r : RegName)
    (pc_a : Addr) (pc_w : Word)
    (p : Perm) (b e a : Addr)
    (P:D) (f:bool) :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
       if decide (reg_allows_load regs r p b e a ∧ a ≠ pc_a)
       then ∃ (w : Word),
           ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝
           ∗ (region_open_resources P w a pc_a f)
           ∗ if f then ▷ interp w else interp w
       else  ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma create_load_res:
    ∀ (regs : leibnizO Reg) (src : RegName)
      (pc_p : Perm) (pc_b pc_e pc_a : Addr)
      (widc : Word)
      (p : Perm) (b e a : Addr) ,
      read_reg_inr (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:=widc]> regs)) src p b e a
      → (∀ (r : RegName) (w : Word), ⌜r ≠ PC⌝ → ⌜r ≠ idc⌝ → ⌜regs !! r = Some w⌝ → (fixpoint interp1) w)
          -∗ interp widc
          -∗ ∃ P, allow_load_res
                    (<[PC:=WCap pc_p pc_b pc_e pc_a]> (<[idc:=widc]> regs))
                    src pc_a p b e a P.
  Proof.
    intros regs src pc_p pc_b pc_e pc_a widc p b e a HVsrc.
    iIntros "#Hreg #Hwidc". rewrite /allow_load_res.
    (* do 5 (iApply sep_exist_r; iExists _). *) (* do 3 (iExists _). *) iFrame "%".
    case_decide as Hdec. 1: destruct Hdec as [Hallows Haeq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
         apply andb_prop in Hwb as [Hle Hge].

         (* Unlike in the old proof, we now go the other way around,
            and prove that the source register could not have been the PC,
            since both addresses differ. This saves us some cases.*)
         assert (src ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.

         rewrite lookup_insert_ne in Hrinr; last by congruence.
         destruct (decide (src = idc)) as [|Hneq]; simplify_map_eq.
         + (* src = idc *)
           iDestruct (read_allowed_inv _ a with "Hwidc") as (P) "[Hinv [Hpers [Hconds _]] ]"; auto;
             first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
           iExists P.
           iMod (inv_acc (⊤ ∖ ↑logN.@pc_a) with "Hinv") as "[Hrefinv Hcls]";[solve_ndisj|].
           rewrite /interp_ref_inv /=. iDestruct "Hrefinv" as (w) "[>Ha HP]".
           iExists w.

           iAssert (▷ interp w)%I as "#Hw".
           { iNext. iApply "Hconds". iFrame. }
           by iFrame "∗ #".

         + (* src ≠ idc *)
         iDestruct ("Hreg" $! src _ n Hneq Hrinr) as "Hvsrc".
         iDestruct (read_allowed_inv _ a with "Hvsrc") as (P) "[Hinv [Hpers [Hconds _]] ]"; auto;
           first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
         iExists P.
         iMod (inv_acc (⊤ ∖ ↑logN.@pc_a) with "Hinv") as "[Hrefinv Hcls]";[solve_ndisj|].
         rewrite /interp_ref_inv /=. iDestruct "Hrefinv" as (w) "[>Ha HP]".
         iExists w.

         iAssert (▷ interp w)%I as "#Hw".
         { iNext. iApply "Hconds". iFrame. }
         iFrame.
         by iFrame "∗ #".
    - by iExists (λne _, True%I).
  Qed.

  Definition allow_load_mask (regs : Reg) (r : RegName)
    (pc_a : Addr) (p : Perm) (b e a : Addr) : coPset :=
    if decide (reg_allows_load regs r p b e a ∧ a ≠ pc_a)
    then ⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a
    else ⊤ ∖ ↑logN.@pc_a.

  Lemma load_res_implies_mem_map:
    ∀ (regs : leibnizO Reg) (src : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a: Addr)  (P:D),
      allow_load_res regs src pc_a p b e a P
      -∗ pc_a ↦ₐ pc_w
      ={⊤ ∖ ↑logN.@pc_a, allow_load_mask regs src pc_a p b e a}=∗ ∃ mem : Mem,
          allow_load_mem regs mem src pc_a pc_w p b e a P true
            ∗ ▷ ([∗ map] a0↦w ∈ mem, a0 ↦ₐ w).
  Proof.
    intros regs src pc_a pc_w p b e a P.
    iIntros "HLoadRes Ha".
    iDestruct "HLoadRes" as "[% HLoadRes]".
    rewrite /allow_load_mask.

    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows).
       destruct Hallows' as [Hrinr [Hra Hwb] ].
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
      + iModIntro. rewrite /allow_load_mem. iSplitR; auto.
        case_decide; first by exfalso. auto.
      + iModIntro. iNext. by iApply memMap_resource_1.
  Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (regs : leibnizO Reg) (mem : Mem) (src : RegName)
      (pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr) (P : D) (f : bool),
      allow_load_mem regs mem src pc_a pc_w p b e a P f
        -∗ ⌜mem !! pc_a = Some pc_w⌝
          ∗ ⌜allow_load_map_or_true src regs mem⌝.
  Proof.
    iIntros (regs mem src pc_a pc_w p b e a P f) "HLoadMem".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0) "[%Hmem _]".
       iSplitR. rewrite Hmem lookup_insert_ne; auto. by rewrite lookup_insert.
       iExists p,b,e,a. iSplitR; auto.
       case_decide; last by exfalso.
       iExists w0. rewrite Hmem. by rewrite lookup_insert.
    - iDestruct "HLoadRes" as "->".
      iSplitR. by rewrite lookup_insert.
      iExists p,b,e,a. iSplitR; auto.
      case_decide as Hdec1; last by done.
      apply not_and_r in Hdec as [| <-%dec_stable]; first by exfalso.
      iExists pc_w. by rewrite lookup_insert.
  Qed.

  Lemma allow_load_mem_later:
    ∀ (regs : leibnizO Reg) (mem : Mem) (src : RegName)
      (pc_p : Perm) (pc_b pc_e pc_a : Addr) (pc_w : Word)
      (p : Perm) (b e a : Addr) (P : D),
      allow_load_mem regs mem src pc_a pc_w p b e a P true
      -∗ ▷ allow_load_mem regs mem src pc_a pc_w p b e a P false.
  Proof.
    iIntros (regs mem src pc_p pc_b pc_e pc_a pc_w p b e a P) "HLoadMem".
    iDestruct "HLoadMem" as "[% HLoadMem]".
    rewrite !/allow_load_mem /=. iSplit;[auto|].
    destruct (decide (reg_allows_load regs src p b e a ∧ a ≠ pc_a)).
    - iApply later_exist_2. iDestruct "HLoadMem" as (w0) "(?&HP&?)".
      iExists w0. iNext. iDestruct "HP" as "(?&?&?)". iFrame.
    - iNext. iFrame.
  Qed.

  Instance if_Persistent
    (regs : Reg) (src : RegName)
    (pc_p : Perm) (pc_b pc_e pc_a : Addr)
    (p : Perm) (b e a : Addr) (loadv : Word) :
    Persistent
      (if decide (reg_allows_load (<[PC:=WCap pc_p pc_b pc_e pc_a]> regs) src p b e a ∧ a ≠ pc_a)
       then interp loadv
       else emp)%I.
  Proof. intros.
         destruct (decide (reg_allows_load (<[PC:=WCap pc_p pc_b pc_e pc_a]> regs)
                             src p b e a ∧ a ≠ pc_a)); apply _.
  Qed.

  Lemma mem_map_recover_res:
    ∀ (regs : leibnizO Reg) (mem : Mem) (src : RegName)
       (pc_a : Addr) (pc_w : Word)
       (p : Perm) (b e a : Addr) (loadv : Word) (P : D),
      mem !! a = Some loadv
      -> reg_allows_load regs src p b e a
      → allow_load_mem regs mem src pc_a pc_w p b e a P false
        -∗ ([∗ map] a↦w ∈ mem, a ↦ₐ w)
        ={allow_load_mask regs src pc_a p b e a,⊤ ∖ ↑logN.@pc_a}=∗
        pc_a ↦ₐ pc_w ∗
        if decide (reg_allows_load regs src p b e a ∧ a ≠ pc_a)
        then interp loadv
        else emp.
  Proof.
    intros regs mem src pc_a pc_w p b e a loadv P Hloadv Hrar.
    iIntros "HLoadMem Hmem".
    rewrite /allow_load_mask.
    iDestruct "HLoadMem" as "[% HLoadRes]".
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0) "[-> [ [HP [#Hcond Hcls] ] Hinterp] ]".
       simplify_map_eq.
       rewrite memMap_resource_2ne; last auto. iDestruct "Hmem" as  "[Ha1 $]".
       iMod ("Hcls" with "[Ha1 HP]") as "_";[iNext;iExists loadv;iFrame|]. iModIntro. done.
    - apply not_and_r in Hdec as [| <-%dec_stable].
      * by exfalso.
      * iDestruct "HLoadRes" as "->".
        rewrite -memMap_resource_1. by iFrame.
  Qed.

  Lemma load_case (regs : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst src : RegName) (P : D):
    ftlr_instr regs p b e a widc w (Load dst src) P.
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
    assert (∃ p0 b0 e0 a0, read_reg_inr (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) src p0 b0 e0 a0)
      as [p0 [b0 [e0 [a0 HVsrc] ] ] ].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p0 b0 e0 a0|] | ]; try done.
      by repeat eexists.
    }

    (* Step 1: open the region, if necessary, and store all the resources
       obtained from the region in allow_load_res *)
    iDestruct (create_load_res with "Hreg Hinv_idc") as (P') "HLoadRes"; eauto.

    (* Step2: derive the concrete map of memory we need, and any spatial
       predicates holding over it *)
    iMod (load_res_implies_mem_map with "HLoadRes Ha") as (mem0) "[HLoadMem HLoadRest]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HLoadMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iDestruct (allow_load_mem_later with "HLoadMem") as "HLoadMem"; auto.

    iApply (wp_load with "[Hmap HLoadRest]");eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw".

    destruct HSpec as [* Hrallows Hmem HincrPC|].
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .
      iApply wp_pure_step_later; auto.
      specialize (load_inr_eq Hrallows HVsrc) as (-> & -> & -> & ->).
      rewrite /allow_load_res.
      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iMod (mem_map_recover_res with "HLoadMem Hmem") as "[Ha #Hinterp]";[eauto|auto|iModIntro].
      iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro].

      (* Exceptional success case: we do not apply the induction hypothesis in case
         we have a faulty PC *)
      destruct (decide (p'' = RX ∨ p'' = RWX)).
      2 : {
        assert (p'' ≠ RX ∧ p'' ≠ RWX). split; by auto.
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { subst. by rewrite lookup_insert. }
        iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value.
        iIntros (a1); inversion a1.
      }

      set (widc' := if (decide (dst = idc))
                    then loadv
                    else widc).
      iNext; iIntros "_".
      iApply ("IH" $! regs' _ _ _ _ widc' with "[%] [Hinterp] [Hmap] [$Hown]"); subst regs'.
      { intro; cbn; by repeat (rewrite lookup_insert_is_Some'; right). }
      (* Prove in the general case that the value relation holds for the register
         that was loaded to - unless it was the PC.*)
      { iIntros (ri v Hri Hri' Hvs).
        destruct (decide (ri = dst)); simplify_map_eq.
        { destruct (decide (a0 = a'')); simplify_eq.
          - rewrite HReadPC in Hmem; simplify_eq. iFrame "Hw".
          - iClear "HLoadRes Hwrite". rewrite decide_True; auto.
        }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. }
      }
      { subst widc'.
        iClear "Hwrite Hinterp".
        destruct (decide (dst = idc)); simplify_map_eq.
        + rewrite
            (insert_commute _ idc _ loadv) //=
            !insert_insert
            (insert_commute _ idc _ loadv) //=
            !insert_insert ; iFrame.
        + destruct (decide (dst = PC)); simplify_map_eq.
          * rewrite
              !insert_insert
              (insert_commute _ idc _ ) //=
              insert_insert; iFrame.
          * rewrite
              (insert_commute _ PC _ ) //=
              !insert_insert
              (insert_commute _ idc) //=
              (insert_commute _ idc) //=
              (insert_commute _ idc) //=
              (insert_commute _ idc) //=
              insert_insert; iFrame.
      }
      { iModIntro.
        destruct (decide (PC = dst)); simplify_eq.
        - simplify_map_eq. rewrite (fixpoint_interp1_eq).
          destruct (decide (a0 = a)); simplify_eq.
          + rewrite HReadPC in Hmem; simplify_eq.
          + iClear "HLoadRes Hwrite". rewrite decide_True;auto.
            rewrite !fixpoint_interp1_eq.
            destruct o as [-> | ->]; iFrame "Hinterp".
        - simplify_map_eq.
          iClear "Hw Hinterp Hwrite".
          rewrite !fixpoint_interp1_eq /=.
          destruct o as [-> | ->]; iFrame "Hinv_pc".
      }
      { iClear "Hwrite".
        subst widc'. destruct (decide (dst = idc)); auto; simplify_map_eq.
        destruct (decide (a0 = a'')); simplify_eq.
        + by rewrite HReadPC in Hmem; simplify_eq.
        + case_decide as Hcontra; auto.
          exfalso ; apply Hcontra ; split; auto.
      }
    }

    { rewrite /allow_load_res /allow_load_mem /allow_load_mask.
      destruct (decide (reg_allows_load (<[PC:=WCap p b e a]> (<[idc:=widc]> regs)) src p0 b0 e0 a0 ∧ a0 ≠ a)).
      - iDestruct "HLoadMem" as "(_&H)".
        iDestruct "H" as (w') "(->&Hres&Hinterp)". rewrite /region_open_resources.
        destruct a1. rewrite memMap_resource_2ne; last auto.
        iDestruct "Hmem" as "[Ha0 Ha]". iDestruct "Hres" as "(HP' & Hread' & Hcls')".
        iMod ("Hcls'" with "[HP' Ha0]");[iExists w';iFrame|iModIntro].
        iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
      - iModIntro. iDestruct "HLoadMem" as "(_&->)". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
