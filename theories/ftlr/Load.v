From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_Load.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately
   The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources (P : D) (w : Word) (a pc_a : Addr) (f:bool) : iProp Σ :=
    ((if f then ▷ P w else P w) ∗ read_cond P interp ∗ ((▷ ∃ w0, a ↦ₐ w0 ∗ P w0) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a,⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

  Lemma load_inr_eq {regs r p0 b0 e0 a0 p1 b1 e1 a1}:
    reg_allows_load regs r p0 b0 e0 a0 →
    read_reg_inr regs r p1 b1 e1 a1 →
    p0 = p1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). destruct H3 as [Hinr1 | Hinl1].
      * rewrite Hinr0 in Hinr1. inversion Hinr1.
        subst. auto. 
      * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
  Qed.

  
  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_load_res r (regs : Reg) pc_a a p b e (P : D) :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
    if decide (reg_allows_load regs r p b e a ∧ a ≠ pc_a ) then
         |={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a}=> ∃ w, a ↦ₐ w ∗ region_open_resources P w a pc_a true ∗ ▷ interp w
     else True)%I.


  Definition allow_load_mem r (regs : Reg) (pc_a : Addr) (pc_w : Word) (mem : gmap Addr Word) (a : Addr) p b e (P:D) (f:bool) :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
    if decide (reg_allows_load regs r p b e a ∧ a ≠ pc_a) then
         ∃ (w : Word), ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝ ∗
            (region_open_resources P w a pc_a f) ∗ if f then ▷ interp w else interp w
    else  ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma create_load_res:
    ∀ (r : leibnizO Reg) (p : Perm)
      (b e a : Addr) (src : RegName) (p0 : Perm)
      (b0 e0 a0 : Addr),
      read_reg_inr (<[PC:=inr (p, b, e, a)]> r) src p0 b0 e0 a0
      → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) (r !r! r1))
          -∗ ∃ P, allow_load_res src (<[PC:=inr (p, b, e, a)]> r) a a0 p0 b0 e0 P.
  Proof.
    intros r p b e a src p0 b0 e0 a0 HVsrc. 
    iIntros "#Hreg". rewrite /allow_load_res. 
    (* do 5 (iApply sep_exist_r; iExists _). *) (* do 3 (iExists _). *) iFrame "%".
    case_decide as Hdec. 1: destruct Hdec as [Hallows Haeq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
         apply andb_prop in Hwb as [Hle Hge].
         rewrite /leb_addr in Hle,Hge.
         
         (* Unlike in the old proof, we now go the other way around, and prove that the source register could not have been the PC, since both addresses differ. This saves us some cases.*)
         assert (src ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.

         iDestruct ("Hreg" $! src n) as "Hvsrc".
         rewrite lookup_insert_ne in Hrinr; last by congruence.
         rewrite /RegLocate Hrinr.
         iDestruct (read_allowed_inv _ a0 with "Hvsrc") as (P) "[Hinv [Hconds _] ]"; auto;
           first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
         iExists P. 
         iMod (inv_open (⊤ ∖ ↑logN.@a) with "Hinv") as "[Hrefinv Hcls]";[solve_ndisj|].
         rewrite /interp_ref_inv /=. iDestruct "Hrefinv" as (w) "[>Ha HP]".
         iExists w.
         iAssert (▷ interp w)%I as "#Hw".
         { iNext. iApply "Hconds". iFrame. }
         iFrame "∗ #". iModIntro. rewrite /region_open_resources. done. 
    - iExists (λne _, True%I). done.  
  Qed.

  (* Definition allow_load_mask (a a0 : Addr) : namespace := *)
  (*   if decide (a = a0) then ⊤ ∖ ↑logN.@a else ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0.  *)
  
  Lemma load_res_implies_mem_map:
    ∀ (r : leibnizO Reg)
       (a a0 : Addr) (w : Word) (src : RegName) p1 b1 e1 (P:D),
      allow_load_res src r a a0 p1 b1 e1 P
      -∗ a ↦ₐ w
      ={⊤ ∖ ↑logN.@a,if decide (reg_allows_load r src p1 b1 e1 a0 ∧ a0 ≠ a) then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0 else ⊤ ∖ ↑logN.@a}=∗ ∃ mem0 : gmap Addr Word,
          allow_load_mem src r a w mem0 a0 p1 b1 e1 P true
            ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w).
  Proof.
    intros r a a0 w src p1 b1 e1 P.
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
      + iModIntro. rewrite /allow_load_mem. iSplitR; auto.
        case_decide; first by exfalso. auto.
      + iModIntro. iNext. by iApply memMap_resource_1.
  Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (r : leibnizO Reg)
       (a a0 : Addr) (w : Word) (src : RegName)
      (mem0 : gmap Addr Word) p b e P f,
        allow_load_mem src r a w mem0 a0 p b e P f
        -∗ ⌜mem0 !! a = Some w⌝
          ∗ ⌜allow_load_map_or_true src r mem0⌝.
  Proof.
    iIntros (r a a0 w src mem0 p b e P f) "HLoadMem".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       (* case_decide as Haeq. *)
       iDestruct "HLoadRes" as (w0) "[% _]".
       iSplitR. rewrite H1 lookup_insert_ne; auto. by rewrite lookup_insert.
       iExists p,b,e,a0. iSplitR; auto. 
       case_decide; last by exfalso.
       iExists w0. rewrite H1. 
         by rewrite lookup_insert.
    - iDestruct "HLoadRes" as "->".
      iSplitR. by rewrite lookup_insert.
      iExists p,b,e,a0. iSplitR; auto.
      case_decide as Hdec1; last by done.
      apply not_and_r in Hdec as [| <-%dec_stable]; first by exfalso.
      iExists w. by rewrite lookup_insert.
  Qed.

  Lemma allow_load_mem_later:
    ∀ (r : leibnizO Reg) (p : Perm)
      (b e a a0 : Addr) (w : Word) (src : RegName)
      (mem0 : gmap Addr Word) p0 b0 e0 P,
      allow_load_mem src r a w mem0 a0 p0 b0 e0 P true
      -∗ ▷ allow_load_mem src r a w mem0 a0 p0 b0 e0 P false.
  Proof.
    iIntros (r p b e a a0 w src mem0 p0 b0 e0 P) "HLoadMem".
    iDestruct "HLoadMem" as "[% HLoadMem]".
    rewrite !/allow_load_mem /=. iSplit;[auto|].
    destruct (decide (reg_allows_load r src p0 b0 e0 a0 ∧ a0 ≠ a)).
    - iApply later_exist_2. iDestruct "HLoadMem" as (w0) "(?&HP&?)".
      iExists w0. iNext. iDestruct "HP" as "(?&?&?)". iFrame. 
    - iNext. iFrame. 
  Qed.

  Instance if_Persistent : Persistent (if decide (reg_allows_load (<[PC:=inr (p, b, e, a)]> r) src p0 b0 e0 a0 ∧ a0 ≠ a) then interp loadv else emp)%I.
  Proof. intros. destruct (decide (reg_allows_load (<[PC:=inr (p, b, e, a)]> r) src p0 b0 e0 a0 ∧ a0 ≠ a));apply _. Qed. 
  
  Lemma mem_map_recover_res:
    ∀ (r : leibnizO Reg)
       (a : Addr) (w : Word) (src : RegName) p0
       (b0 e0 a0 : Addr) (mem0 : gmap Addr Word) loadv P,
      mem0 !! a0 = Some loadv
      -> reg_allows_load r src p0 b0 e0 a0 
      → allow_load_mem src r a w mem0 a0 p0 b0 e0 P false
        -∗ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w)
        ={if decide (reg_allows_load r src p0 b0 e0 a0 ∧ a0 ≠ a) then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0 else ⊤ ∖ ↑logN.@a,⊤ ∖ ↑logN.@a}=∗ a ↦ₐ w
                  ∗ if decide (reg_allows_load r src p0 b0 e0 a0 ∧ a0 ≠ a) then interp loadv else emp.
  Proof.
    intros r a w src p0 b0 e0 a0 mem0 loadv P Hloadv Hrar.
    iIntros "HLoadMem Hmem".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    (* destruct (load_inr_eq Hrar H0) as (<- & <- &<- &<- &<-). *)
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


  Lemma load_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst src : RegName) (P : D):
    ftlr_instr r p b e a w (Load dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=inr (p, b, e, a)]> r !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }
    
    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0, read_reg_inr (<[PC:=inr (p, b, e, a)]> r) src p0 b0 e0 a0) as [p0 [b0 [e0 [a0 HVsrc] ] ] ].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. destruct wsrc. 2: destruct c,p0,p0. all: repeat eexists.
      right. by exists z. by left.
    }
    
    
    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_load_res with "Hreg") as (P') "HLoadRes"; eauto.
    
    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iMod (load_res_implies_mem_map with "HLoadRes Ha") as (mem0) "[HLoadMem HLoadRest]".  
    
    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HLoadMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iDestruct (allow_load_mem_later with "HLoadMem") as "HLoadMem"; auto.
    
    iApply (wp_load with "[Hmap HLoadRest]");eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw". 
    
    destruct HSpec as [* ? ? Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto.
      specialize (load_inr_eq H0 HVsrc) as (-> & -> & -> & ->).
      rewrite /allow_load_res. 
      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iMod (mem_map_recover_res with "HLoadMem Hmem") as "[Ha #Hinterp]";[eauto|auto|iModIntro]. 
      iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. 
      
      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC*)
      destruct (decide (x = RX ∨ x = RWX)).
      2 : {
        assert (x ≠ RX ∧ x ≠ RWX). split; by auto.
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { subst. by rewrite lookup_insert. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext. iApply wp_value.
        iIntros (a1); inversion a1.
      }
      
      iApply ("IH" $! regs' with "[%] [Hinterp] [Hmap] [$Hown]").
      { cbn. intros. subst regs'.
        rewrite lookup_insert_is_Some.
        destruct (decide (PC = x4)); [ auto | right; split; auto].
        rewrite lookup_insert_is_Some.
        destruct (decide (dst = x4)); [ auto | right; split; auto]. }
      (* Prove in the general case that the value relation holds for the register that was loaded to - unless it was the PC.*)
       { iIntros (ri Hri).
        subst regs'.
        erewrite locate_ne_reg; [ | | reflexivity]; auto.
        destruct (decide (ri = dst)).
        { subst ri.
          erewrite locate_eq_reg; [ | reflexivity]; auto.
          destruct (decide (a = a0)).
          - simplify_eq. iFrame "Hw".
          - iClear "HLoadRes". iClear "Hwrite". rewrite decide_True. iFrame "#". auto.
        }
        { repeat (erewrite locate_ne_reg; [ | | reflexivity]; auto).
          iApply "Hreg"; auto. }
       }
       { subst regs'. rewrite insert_insert. iApply "Hmap". }
       { destruct (decide (PC = dst)); simplify_eq.
         - destruct o as [HRX | HRWX]; auto.
         - simplify_map_eq. iPureIntro. naive_solver.
       }
       { iAlways.
         destruct (decide (PC = dst)); simplify_eq.
         - simplify_map_eq. rewrite (fixpoint_interp1_eq).
           destruct (decide (a = a0)).
           + simplify_map_eq. 
           + iClear "HLoadRes Hwrite". rewrite decide_True;auto. iAlways.
             rewrite !fixpoint_interp1_eq. 
             destruct o as [-> | ->]; iFrame "Hinterp". 
         - (* iExists p'. *) simplify_map_eq.
           iAlways. iClear "Hw Hinterp Hwrite". 
           rewrite !fixpoint_interp1_eq /=. 
           destruct o as [-> | ->]; iFrame "Hinv". 
       }
    }
    { rewrite /allow_load_res /allow_load_mem.
      destruct (decide (reg_allows_load (<[PC:=inr (p, b, e, a)]> r) src p0 b0 e0 a0 ∧ a0 ≠ a)).
      - iDestruct "HLoadMem" as "(_&H)".
        iDestruct "H" as (w') "(->&Hres&Hinterp)". rewrite /region_open_resources.
        destruct a1. rewrite memMap_resource_2ne; last auto.
        iDestruct "Hmem" as "[Ha0 Ha]". iDestruct "Hres" as "(HP' & Hread' & Hcls')".
        iMod ("Hcls'" with "[HP' Ha0]");[iExists w';iFrame|iModIntro].
        iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. 
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto. iNext. iIntros; discriminate.
      - iModIntro. iDestruct "HLoadMem" as "(_&->)". rewrite -memMap_resource_1. 
        iMod ("Hcls" with "[Hmem HP]");[iExists w;iFrame|iModIntro]. 
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto. iNext. iIntros; discriminate.
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
