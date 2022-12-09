From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel_binary.
From cap_machine Require Import ftlr_base_binary.
From cap_machine.rules_binary Require Import rules_binary_base rules_binary_Load.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately
   The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources (P : D) (w w' : Word) (a pc_a : Addr) (f:bool) : iProp Σ :=
    ((if f then ▷ P (w,w') else P (w,w')) ∗ read_cond P interp ∗ ((▷ ∃ w0 w1, a ↦ₐ w0 ∗ a ↣ₐ w1 ∗ P (w0,w1)) ={⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a,⊤ ∖ ↑logN.@pc_a}=∗ emp))%I.

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
  Definition allow_load_res r (regs : Reg) pc_a a p b e (P : D) :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
    if decide (reg_allows_load regs r p b e a ∧ a ≠ pc_a ) then
         |={⊤ ∖ ↑logN.@pc_a,⊤ ∖ ↑logN.@pc_a ∖ ↑logN.@a}=> ∃ w w', a ↦ₐ w ∗ a ↣ₐ w' ∗ region_open_resources P w w' a pc_a true ∗ ▷ interp (w,w')
     else True)%I.


  Definition allow_load_mem r (regs : Reg) (pc_a : Addr) (pc_w : Word) (mem : gmap Addr Word) (a : Addr) p b e (P:D) (f:bool) :=
    (⌜read_reg_inr regs r p b e a⌝ ∗
    if decide (reg_allows_load regs r p b e a ∧ a ≠ pc_a) then
         ∃ (w w' : Word), ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝ ∗
            (region_open_resources P w w' a pc_a f) ∗ if f then ▷ interp (w,w') else interp (w,w')
    else  ⌜mem = <[pc_a:=pc_w]> ∅⌝)%I.

  Lemma create_load_res:
    ∀ (r : leibnizO Reg) (p : Perm)
      (b e a : Addr) (src : RegName) (p0 : Perm)
      (b0 e0 a0 : Addr),
      read_reg_inr (<[PC:=WCap p b e a]> r) src p0 b0 e0 a0

      → (∀ (r0 : RegName) v1 v2, (⌜r0 ≠ PC⌝  → ⌜r !! r0 = Some v1⌝ → ⌜r !! r0 = Some v2⌝ → (fixpoint interp1) (v1, v2)))
          -∗ ∃ P, allow_load_res src (<[PC:=WCap p b e a]> r) a a0 p0 b0 e0 P.
  Proof.
    intros r p b e a src p0 b0 e0 a0 HVsrc.
    iIntros "#Hreg". rewrite /allow_load_res.
    (* do 5 (iApply sep_exist_r; iExists _). *) (* do 3 (iExists _). *) iFrame "%".
    case_decide as Hdec. 1: destruct Hdec as [Hallows Haeq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
         apply andb_prop in Hwb as [Hle Hge].

         (* Unlike in the old proof, we now go the other way around, and prove that the source register could not have been the PC, since both addresses differ. This saves us some cases.*)
         assert (src ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.

         rewrite lookup_insert_ne in Hrinr; last by congruence.
         iDestruct ("Hreg" $! src _ _ n Hrinr Hrinr) as "Hvsrc".
         iDestruct (read_allowed_inv _ a0 with "Hvsrc") as (P) "[Hinv [Hconds _] ]"; auto;
           first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
         iExists P.
         iMod (inv_acc (⊤ ∖ ↑logN.@a) with "Hinv") as "[Hrefinv Hcls]";[solve_ndisj|].
         rewrite /interp_ref_inv /=. iDestruct "Hrefinv" as (w w') "[>Ha [>Ha' HP] ]".
         iExists w,w'.
         iAssert (▷ interp (w,w'))%I as "#Hw".
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
      -∗ a ↦ₐ w -∗ a ↣ₐ w
      ={⊤ ∖ ↑logN.@a,if decide (reg_allows_load r src p1 b1 e1 a0 ∧ a0 ≠ a) then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0 else ⊤ ∖ ↑logN.@a}=∗ ∃ mem0 : gmap Addr Word,
          allow_load_mem src r a w mem0 a0 p1 b1 e1 P true
            ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w) ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↣ₐ w).
  Proof.
    intros r a a0 w src p1 b1 e1 P.
    iIntros "HLoadRes Ha Ha'".
    iDestruct "HLoadRes" as "[% HLoadRes]".

    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       iMod "HLoadRes" as (w0 w1) "[Ha0 [Ha1 [HLoadRest #Hval] ] ]".
       iExists _.
       iSplitL "HLoadRest".
       + iSplitR; first auto.

         case_decide as Hdec1.
         2: apply not_and_r in Hdec1 as [|]; by exfalso.
         iExists w0,w1. iSplitR; auto.
       + iSplitL "Ha0 Ha".
         { iModIntro. iNext. rewrite rules_base.memMap_resource_2ne; auto; iFrame. }
         { iModIntro. iNext. rewrite memMap_resource_2ne; auto. iDestruct (interp_eq with "Hval") as %->. iFrame. }
    - rewrite /read_reg_inr in H0.
      iExists _.
      iSplitL "HLoadRes".
      + iModIntro. rewrite /allow_load_mem. iSplitR; auto.
        case_decide; first by exfalso. auto.
      + iModIntro. iSplitL "Ha"; iNext. by iApply memMap_resource_1.
        iApply big_sepM_insert;[|iFrame];[by simplify_map_eq|]. done.
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
       iDestruct "HLoadRes" as (w0 w1) "[% _]".
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
    - iApply bi.later_exist_2. iDestruct "HLoadMem" as (w0 w1) "(?&HP&?)".
      iExists w0. iApply bi.later_exist_2. iExists w1. iNext. iDestruct "HP" as "(?&?&?)". iFrame.
    - iNext. iFrame.
  Qed.

  Instance if_Persistent p b e a r src p0 b0 e0 a0 loadv: Persistent (if decide (reg_allows_load (<[PC:=WCap p b e a]> r) src p0 b0 e0 a0 ∧ a0 ≠ a) then interp loadv else emp)%I.
  Proof. intros. destruct (decide (reg_allows_load (<[PC:=WCap p b e a]> r) src p0 b0 e0 a0 ∧ a0 ≠ a));apply _. Qed.

  Lemma mem_map_recover_res:
    ∀ (r : leibnizO Reg)
       (a : Addr) (w : Word) (src : RegName) p0
       (b0 e0 a0 : Addr) (mem0 : gmap Addr Word) loadv P,
      mem0 !! a0 = Some loadv
      -> reg_allows_load r src p0 b0 e0 a0
      → allow_load_mem src r a w mem0 a0 p0 b0 e0 P false
        -∗ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w ∗ a0 ↣ₐ w)
        ={if decide (reg_allows_load r src p0 b0 e0 a0 ∧ a0 ≠ a) then ⊤ ∖ ↑logN.@a ∖ ↑logN.@a0 else ⊤ ∖ ↑logN.@a,⊤ ∖ ↑logN.@a}=∗ a ↦ₐ w ∗ a ↣ₐ w
                  ∗ if decide (reg_allows_load r src p0 b0 e0 a0 ∧ a0 ≠ a) then interp (loadv,loadv) else emp.
  Proof.
    intros r a w src p0 b0 e0 a0 mem0 loadv P Hloadv Hrar.
    iIntros "HLoadMem Hmem".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    (* destruct (load_inr_eq Hrar H0) as (<- & <- &<- &<- &<-). *)
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0 w1) "[-> [ [HP [#Hcond Hcls] ] Hinterp] ]".
       simplify_map_eq.
       iAssert (⌜loadv = w1⌝)%I as %<-.
       { iApply interp_eq. iFrame. }
       iDestruct (big_sepM_delete _ _ a0 with "Hmem") as "[Ha1 Hmem]";[simplify_map_eq;eauto|rewrite delete_insert;[|by simplify_map_eq] ].
       iDestruct (big_sepM_delete _ _ a with "Hmem") as "[Ha0 Hmem]";[simplify_map_eq;eauto|rewrite delete_insert;[|by simplify_map_eq] ].
       iFrame.
       iMod ("Hcls" with "[Ha1 HP]") as "_";[iNext;iExists _,_;iFrame|]. iModIntro. done.
    - apply not_and_r in Hdec as [| <-%dec_stable].
      * by exfalso.
      * iDestruct "HLoadRes" as "->".
        iDestruct (big_sepM_delete _ _ a0 with "Hmem") as "[ [? ?] Hmem]";[simplify_map_eq;eauto|].
        iFrame. simplify_map_eq. by iFrame.
  Qed.


  Lemma Load_spec_determ r dst src regs regs' mem0 retv retv' :
    Load_spec r dst src regs mem0 retv →
    Load_spec r dst src regs' mem0 retv' →
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2;subst; simplify_eq;
      repeat match goal with
        | H : reg_allows_load _ _ _ _ _ _ |- _ => inversion H; clear H
        | H : Load_failure _ _ _ _ |- _ => inversion H; clear H
        end;
      split_and?; auto;
      simplify_map_eq;
      destruct_and?; destruct_or?; try congruence; auto.
  Qed.

  Lemma load_case (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (b e a : Addr) (w w' : Word) (dst src : RegName) (P : D):
    ftlr_instr r p b e a w w' (Load dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hspec #Hinv #Hreg #Hinva #[Hread Hwrite] Hsmap Hown Hs Ha Ha' HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.


    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p b e a]> r.1 !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      rewrite lookup_insert_ne//. destruct Hsome with x;auto.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 b0 e0 a0, read_reg_inr (<[PC:=WCap p b e a]> r.1) src p0 b0 e0 a0) as [p0 [b0 [e0 [a0 HVsrc] ] ] ].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p0 b0 e0 a0|] | ]; try done.
      by repeat eexists.
    }

    iDestruct (interp_reg_dupl with "[Hreg]") as "[_ #Hreg']";[iSplit;[iPureIntro;apply Hsome|iFrame "Hreg"]|].

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_load_res with "Hreg'") as (P') "HLoadRes /="; eauto.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iAssert (▷ ⌜w = w'⌝)%I with "[HP]" as "#>%";[|subst w'].
    { iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
    iMod (load_res_implies_mem_map with "HLoadRes Ha Ha'") as (mem0) "[HLoadMem [HLoadRest HLoadRest'] ]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HLoadMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iDestruct (allow_load_mem_later with "HLoadMem") as "HLoadMem"; auto.

    iApply (wp_load with "[Hmap HLoadRest]");eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. destruct Hsome with rr; eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct r as [r1 r2]. simpl in *.
    iDestruct (interp_reg_eq r1 r2 (WCap p b e a) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.

    (* we take a step in the specification code *)
    iMod (step_Load _ [SeqCtx] with "[$HLoadRest' $Hsmap $Hs $Hspec]") as (retv' regs'') "(Hs & #Hmovspec & Ha' & Hsmap) /=";eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. destruct (decide (PC = rr));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne //].
      destruct Hsome with rr;eauto. }
    { destruct (decide (reg_allows_load (<[PC:=WCap p b e a]> r1) src p0 b0 e0 a0 ∧ a0 ≠ a)); solve_ndisj. }
    iDestruct "Hmovspec" as %HSpec'.

    specialize (Load_spec_determ _ _ _ _ _ _ _ _ HSpec HSpec') as [Hregs <-].

    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw".

    destruct HSpec as [* ? ? Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto.
      iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=".
      { destruct (decide (reg_allows_load (<[PC:=WCap p b e a]> r1) src p0 b0 e0 a0 ∧ a0 ≠ a)); solve_ndisj. }
      specialize (load_inr_eq H0 HVsrc) as (-> & -> & -> & ->).
      rewrite /allow_load_res.
      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iMod (mem_map_recover_res with "HLoadMem [Hmem Ha']") as "[Ha [Ha' #Hinterp] ]";[eauto|auto| |iModIntro].
      { iDestruct (big_sepM_sep with "[$Hmem $Ha']") as "Hmem". iFrame. }
      iMod ("Hcls" with "[Ha Ha' HP]");[iExists w,w;iFrame|iModIntro].

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC *)
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

      destruct Hregs as [<- | Hcontr];[|inversion Hcontr]. iNext.

      iApply ("IH" $! (regs',regs') with "[%] [Hinterp] [Hmap] [Hsmap] Hown Hs Hspec").
      { cbn. intros. subst regs'.
        rewrite lookup_insert_is_Some.
        destruct (decide (PC = x4)); [ auto | split; (right; split; auto)];
        rewrite lookup_insert_is_Some;
        (destruct (decide (dst = x4)); [ auto | right; split; auto]). }
        (* Prove in the general case that the value relation holds for the register that was loaded to - unless it was the PC.*)
       { iIntros (ri v1 v2 Hri Hv1s Hv2s).
        subst regs'. simpl.
        rewrite lookup_insert_ne in Hv1s, Hv2s; auto.
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert in Hv1s, Hv2s; auto. inversion Hv1s. inversion Hv2s.
          simplify_eq.
          destruct (decide (a = a0)).
          - simplify_eq. iFrame "Hw".
          - iClear "HLoadRes Hwrite". rewrite decide_True. iFrame "#". auto.
        }
        { repeat (rewrite lookup_insert_ne in Hv1s,Hv2s); auto.
          simplify_eq.
          iApply "Hreg'"; auto. }
       }
      { subst regs'. rewrite insert_insert. iApply "Hmap". }
      { subst regs'. rewrite insert_insert. iApply "Hsmap". }
      { iModIntro.
        destruct (decide (PC = dst)); simplify_eq.
        - simplify_map_eq. rewrite /interp. rewrite !(fixpoint_interp1_eq). iApply fixpoint_interp1_eq.
          destruct (decide (a = a0)).
          + subst a. rewrite HReadPC in H1; inversion H1.
            destruct o as [-> | ->]; iDestruct "Hw" as "[% Hw]"; iSplit;auto.
          + iClear "HLoadRes Hwrite". rewrite decide_True;auto.
            rewrite !fixpoint_interp1_eq.
            destruct o as [-> | ->]; iDestruct "Hinterp" as "[% Hinterp]"; iSplit;auto.
        - rewrite lookup_insert_ne// lookup_insert in H2; inversion H2.
          iClear "Hw Hinterp Hwrite".
          rewrite !fixpoint_interp1_eq /=.
          destruct o as [-> | ->]; iDestruct "Hinv" as "[% Hw]"; iSplit;auto.
      }
    }
    { rewrite /allow_load_res /allow_load_mem.
      destruct (decide (reg_allows_load (<[PC:=WCap p b e a]> r1) src p0 b0 e0 a0 ∧ a0 ≠ a)).
      - iDestruct "HLoadMem" as "(_&H)".
        iDestruct "H" as (w' w'') "(->&Hres&Hinterp)". rewrite /region_open_resources.
        destruct a1. rewrite memMap_resource_2ne// rules_base.memMap_resource_2ne//.
        iDestruct "Hmem" as "[Ha0 Ha]". iDestruct "Hres" as "(HP' & Hread' & Hcls')".
        iDestruct "Ha'" as "[Ha0' Ha']".
        iAssert (▷ ⌜w' = w''⌝)%I with "[HP' Hread']" as "#>%";[|subst w''].
        { rewrite /read_cond /=. iNext. iSpecialize ("Hread'" with "HP'"). by iApply interp_eq. }
        iMod ("Hcls'" with "[HP' Ha0 Ha0']");[iExists w',w';iFrame|iModIntro].
        iMod ("Hcls" with "[Ha Ha' HP]");[iExists w,w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto. iNext. iIntros; discriminate.
      - iModIntro. iDestruct "HLoadMem" as "(_&->)". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem Ha' HP]");[iExists w,w;iFrame|iModIntro].
        { iDestruct (big_sepM_insert with "Ha'") as "[$ _]". auto. }
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto. iNext. iIntros; discriminate.
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
