From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_IsUnique.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Definition compute_mask_range (E : coPset) (b e : Addr) (v : Version) :=
    (compute_mask E (list_to_set ((λ a, (a,v)) <$> (finz.seq_between b e)))).

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately
   The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources (P : D)
    (lws : list LWord) (pc_la : LAddr) (b e : Addr) (v : Version) (f:bool)
    : iProp Σ :=
    (
      ([∗ list] w ∈ lws, (if f then ▷ P w else P w))
       ∗ read_cond P interp
       ∗ ((▷ ∃ (lws : list LWord),
               ⌜ length lws = length (finz.seq_between b e) ⌝
               ∗ ([∗ list] w ∈ lws, P w)
               ∗ [[ b , e ]] ↦ₐ{ v } [[ lws ]])
          ={compute_mask_range (⊤ ∖ ↑logN.@pc_la) b e v, ⊤ ∖ ↑logN.@pc_la}=∗ emp))%I.

  (* Definition reg_allows_sweep (lregs : LReg) (r : RegName) p b e a v := *)
  (*   lregs !! r = Some (LCap p b e a v) ∧ withinBounds b e a = true. *)

  (* Lemma sweep_inr_eq {regs r p0 b0 e0 a0 v0 p1 b1 e1 a1 v1}: *)
  (*   reg_allows_load regs r p0 b0 e0 a0 v0 → *)
  (*   read_reg_inr regs r p1 b1 e1 a1 v1 → *)
  (*   p0 = p1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1 /\ v0 = v1. *)
  (* Proof. *)
  (*     intros Hrar H3. *)
  (*     pose (Hrar' := Hrar). *)
  (*     destruct Hrar' as (Hinr0 & _). rewrite /read_reg_inr Hinr0 in H3. by inversion H3. *)
  (* Qed. *)


  (* Description of what the resources are supposed to look like
     after opening the region, if we need to,
     but before closing the region up again*)
  Definition allow_sweep_res (P : D)
    (lregs : LReg) (r : RegName)
    (pc_a : Addr) (pc_v : Version)
    (p : Perm) (b e a : Addr) (v : Version) :=
    (⌜read_reg_inr lregs r p b e a v⌝ ∗
       if (decide (lregs !! r = Some (LCap p b e a v) /\ pc_a ∉ finz.seq_between b e))
       then
         (|={⊤ ∖ ↑logN.@(pc_a, pc_v), compute_mask_range (⊤ ∖ ↑logN.@(pc_a, pc_v)) b e v}=>
            (∃ (lws : list LWord),
                ⌜length lws = length (finz.seq_between b e) ⌝
                ∗ [[ b , e ]] ↦ₐ{ v } [[ lws ]]
                ∗ region_open_resources P lws (pc_a, pc_v) b e v true
                ∗ ([∗ list] w ∈ lws, ▷ interp w))
         )
       else True)%I.

  (* TODO what is the state of the memory if we open a full region.
     We need a way to map the insertion of the full region.
   *)

  (* Definition allow_sweep_mem (lregs : LReg) (r : RegName) *)
  (*   (pc_a : Addr) (pca_v : Version) (pc_lw : LWord) *)
  (*   (lmem : LMem) p b e (a : Addr) (v : Version) (P:D) (f:bool) := *)
  (*   (⌜read_reg_inr lregs r p b e a v⌝ ∗ *)
  (*   if decide (reg_allows_load lregs r p b e a v ∧ (a,v) ≠ (pc_a,pca_v) ) then *)
  (*        ∃ (lw : LWord), ⌜lmem = <[(a,v):=lw]> (<[(pc_a, pca_v):=pc_lw]> ∅)⌝ ∗ *)
  (*           (region_open_resources P lw (a,v) (pc_a, pca_v) f) ∗ if f then ▷ interp lw else interp lw *)
  (*   else  ⌜lmem = <[(pc_a, pca_v):=pc_lw]> ∅⌝)%I. *)

  Set Nested Proofs Allowed.
  Lemma read_allowed_region_inv (p : Perm) (b e a: Addr) (v : Version):
    readAllowed p →
    ⊢ (interp (LCap p b e a v) →
       [∗ list] a' ∈ (finz.seq_between b e),
        ∃ P, inv (logN .@ (a',v)) (interp_ref_inv a' v P)
               ∗ read_cond P interp
               ∗ if writeAllowed p then write_cond P interp else emp)%I.
  Proof.
    iIntros (Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction;
      try (iDestruct "Hinterp" as "[Hinterp Hinterpe]"); cbn
    ; iFrame.
    all:
      iApply (big_sepL_impl with "Hinterp"); iModIntro; iIntros (k a') "_".
    all: iIntros "H"; iDestruct "H" as (P) "[H1 H2]"; iExists P; iFrame.
  Qed.

  Lemma create_sweep_res:
    ∀ (lregs : leibnizO LReg) (src : RegName)
      (pc_p : Perm) (pc_b pc_e pc_a : Addr) (pc_v : Version)
      (p : Perm) (b e a : Addr) (v : Version),
      read_reg_inr (<[PC:=LCap pc_p pc_b pc_e pc_a pc_v]> lregs) src p b e a v
      → (∀ (r1 : RegName) lv, ⌜r1 ≠ PC⌝ → ⌜lregs !! r1 = Some lv⌝ → (fixpoint interp1) lv)
          -∗ ∃ P, allow_sweep_res P (<[PC:=LCap pc_p pc_b pc_e pc_a pc_v]> lregs)
                    src pc_a pc_v p b e a v.
  Proof.
    intros * HVsrc.
    iIntros "#Hreg". rewrite /allow_sweep_res.
    iFrame "%".
    case_decide as Hdec; cycle 1.
    - by iExists (λne _, True%I).
    - (* Unlike in the old proof, we now go the other way around,
         and prove that the source register could not have been the PC,
         since both addresses differ.
         This saves us some cases.*)
      destruct Hdec as [Hrinr Hdec].
      assert (Hlaeq : (a, v) ≠ (pc_a, pc_v)).
      {
        intro; simplify_eq.
        rewrite /read_reg_inr in HVsrc.
        destruct (decide (src = PC)); simplify_map_eq.
        (* TODO we need some more information *)
        admit.
        admit.
      }
      assert (src ≠ PC) as n ; simplify_map_eq; eauto.
      refine (laddr_ne_reg_ne Hrinr _ Hlaeq); simplify_map_eq; eauto.

      iDestruct ("Hreg" $! src _ n Hrinr) as "Hvsrc".
      iDestruct (read_allowed_region_inv with "Hvsrc") as "H"; auto.
      admit. (* TODO should be part of the hypothesis *)
      (* TODO I should generalize the problem at this point,
         with any NoDup list of address instead of seq_between(b,e),
         and proceed by induction over it.
       *)
      (* iExists _. (* TODO here should be a list of P, not the same for all *) *)
      (* rewrite /compute_mask_range. *)
      (* iMod (inv_acc (⊤ ∖ ↑logN.@(a,v)) with "Hinv") as "[Hrefinv Hcls]";[solve_ndisj|]. *)
      (* rewrite /interp_ref_inv /=. iDestruct "Hrefinv" as (w) "[>Ha HP]". *)
      (* iExists w. *)
      (* iAssert (▷ interp w)%I as "#Hw". *)
      (* { iNext. iApply "Hconds". iFrame. } *)
      (* iFrame "∗ #". iModIntro. rewrite /region_open_resources. done. *)
  Admitted.


  Lemma sweep_res_implies_mem_map:
    ∀ (lregs : leibnizO LReg)
      (a a0 : Addr) (v v0 : Version) (lw : LWord) (src : RegName) p1 b1 e1 (P:D),
      allow_load_res lregs src a v p1 b1 e1 a0 v0 P
      -∗ (a, v) ↦ₐ lw
      ={⊤ ∖ ↑logN.@(a,v),
        if decide (reg_allows_load lregs src p1 b1 e1 a0 v0 ∧ (a0,v0) ≠ (a,v))
        then ⊤ ∖ ↑logN.@(a,v) ∖ ↑logN.@(a0,v0)
        else ⊤ ∖ ↑logN.@(a,v)}=∗
         ∃ lmem : LMem,
           allow_load_mem lregs src a v lw lmem p1 b1 e1 a0 v0 P true
             ∗ ▷ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw).
  Proof.
    intros lregs a a0 v v0 w src p1 b1 e1 P.
    iIntros "HLoadRes Ha".
    iDestruct "HLoadRes" as "[% HLoadRes]".

    case_decide as Hdec. 1: destruct Hdec as [ Hallows Hlaeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       iMod "HLoadRes" as (lw0) "[Ha0 [HLoadRest #Hval] ]".
       iExists _.
       iSplitL "HLoadRest".
       + iSplitR; first auto.

         case_decide as Hdec1.
         2: { apply not_and_r in Hdec1 as [| Hdec1] ; by exfalso. }
         iExists lw0. iSplitR; auto.
       + iModIntro. iNext.
         rewrite memMap_resource_2ne; first iFrame.
         intro ; simplify_eq.
    - rewrite /read_reg_inr in H0.
      iExists _.
      iSplitL "HLoadRes".
      + iModIntro. rewrite /allow_load_mem. iSplitR; auto.
        case_decide; first by exfalso. auto.
      + iModIntro. iNext. by iApply memMap_resource_1.
  Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (lregs : leibnizO LReg)
       (a a0 : Addr) (v v0 : Version) (lw : LWord) (src : RegName)
       (lmem : LMem) p b e P f,
        allow_load_mem lregs src a v lw lmem p b e a0 v0 P f
        -∗ ⌜lmem !! (a,v) = Some lw⌝
          ∗ ⌜allow_load_map_or_true src lregs lmem⌝.
  Proof.
    iIntros (lregs a a0 v v0 lw src lmem p b e P f) "HLoadMem".
    iDestruct "HLoadMem" as "[% HLoadRes]".
    case_decide as Hdec. 1: destruct Hdec as [ Hallows Hlaeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       (* case_decide as Haeq. *)
       iDestruct "HLoadRes" as (lw0) "[% _]".
       iSplitR. by simplify_map_eq.
       iExists p,b,e,a0,v0. iSplitR; auto.
       case_decide; last by exfalso.
       iExists lw0. rewrite H1.
         by rewrite lookup_insert.
    - iDestruct "HLoadRes" as "->".
      iSplitR. by simplify_map_eq.
      iExists p,b,e,a0,v0. iSplitR; auto.
      case_decide as Hdec1; last by done.
      apply not_and_r in Hdec as [| <-%dec_stable]; first by exfalso.
      iExists lw; by simplify_map_eq.
  Qed.

  Lemma allow_sweep_mem_later:
    ∀ (lregs : leibnizO LReg)
      (p : Perm) (b e a a0 : Addr) (v v0 : Version)
      (lw : LWord) (src : RegName)
      (lmem : LMem) p0 b0 e0 P,
      allow_sweep_mem lregs src a v lw lmem p0 b0 e0 a0 v0 P true
      -∗ ▷ allow_sweep_mem lregs src a v lw lmem p0 b0 e0 a0 v0 P false.
  Proof.
    iIntros (lregs p b e a a0 v v0 lw src lmem p0 b0 e0 P) "HLoadMem".
    iDestruct "HLoadMem" as "[% HLoadMem]".
    rewrite !/allow_load_mem /=. iSplit;[auto|].
    destruct (decide (reg_allows_load lregs src p0 b0 e0 a0 v0 ∧ (a0,v0) ≠ (a,v))).
    - iApply later_exist_2. iDestruct "HLoadMem" as (lw0) "(?&HP&?)".
      iExists lw0. iNext. iDestruct "HP" as "(?&?&?)". iFrame.
    - iNext. iFrame.
  Qed.

  Instance if_Persistent p b e a v lregs src p0 b0 e0 a0 v0 loadv :
    Persistent (if decide (reg_allows_load (<[PC:=LCap p b e a v]> lregs) src p0 b0 e0 a0 v0 ∧ (a0, v0) ≠ (a,v))
                then interp loadv
                else emp)%I.
  Proof. intros. destruct (decide (reg_allows_load (<[PC:=LCap p b e a v]> lregs) src p0 b0 e0 a0 v0 ∧ (a0, v0) ≠ (a,v)));apply _. Qed.

  Lemma mem_map_recover_res:
    ∀ (lregs : leibnizO LReg)
       (a : Addr) (v : Version) (lw : LWord) (src : RegName) p0
       (b0 e0 a0 : Addr) (v0 : Version) (lmem : LMem) loadv P,
      lmem !! (a0, v0) = Some loadv
      -> reg_allows_load lregs src p0 b0 e0 a0 v0
      → allow_load_mem lregs src  a v lw lmem p0 b0 e0 a0 v0 P false
        -∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw)
        ={if decide (reg_allows_load lregs src p0 b0 e0 a0 v0 ∧ (a0, v0) ≠ (a,v))
          then ⊤ ∖ ↑logN.@(a,v) ∖ ↑logN.@(a0,v0)
          else ⊤ ∖ ↑logN.@(a,v),⊤ ∖ ↑logN.@(a,v)}=∗
           (a,v) ↦ₐ lw
           ∗ if decide (reg_allows_load lregs src p0 b0 e0 a0 v0 ∧ (a0, v0) ≠ (a,v))
           then interp loadv
           else emp.
  Proof.
    intros lregs a v lw src p0 b0 e0 a0 v0 lmem loadv P Hloadv Hrar.
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


  Lemma isunique_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst src : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (IsUnique dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
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
    assert (∃ p0 b0 e0 a0 v0, read_reg_inr (<[PC:=LCap p b e a v]> lregs) src p0 b0 e0 a0 v0)
      as (p0 & b0 & e0 & a0 & v0 & HVsrc).
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p0 b0 e0 a0 v0|] | ]; try done.
      by repeat eexists.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_load_res with "Hreg") as (P') "HLoadRes"; eauto.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iMod (load_res_implies_mem_map with "HLoadRes Ha") as (lmem) "[HLoadMem HLoadRest]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HLoadMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iDestruct (allow_load_mem_later with "HLoadMem") as "HLoadMem"; auto.

    iApply (wp_load with "[Hmap HLoadRest]");eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    (* Infer that if P holds at w, then w must be valid (read condition) *)
    iDestruct ("Hread" with "HP") as "#Hw".

    destruct HSpec as [* HregLoad Hmem Hincr|].
    { apply incrementLPC_Some_inv in Hincr as (p''&b''&e''&a''&v''&? & HPC & Z & Hregs') .
      iApply wp_pure_step_later; auto.
      specialize (load_inr_eq HregLoad HVsrc) as (-> & -> & -> & -> & ->).
      rewrite /allow_load_res.
      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iMod (mem_map_recover_res with "HLoadMem Hmem") as "[Ha #Hinterp]";[eauto|auto|iModIntro].
      iMod ("Hcls" with "[Ha HP]");[iExists lw;iFrame|iModIntro].

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC *)
      destruct (decide (p'' = RX ∨ p'' = RWX)).
      2 : {
        assert (p'' ≠ RX ∧ p'' ≠ RWX). split; by auto.
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { by simplify_map_eq. }
        iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value.
        iIntros (a1); inversion a1.
      }

      iNext; iIntros "_".
      iApply ("IH" $! regs' with "[%] [Hinterp] [Hmap] [$Hown]").
      { cbn. intros rx. subst regs'.
        rewrite lookup_insert_is_Some.
        destruct (decide (PC = rx)); [ auto | right; split; auto].
        rewrite lookup_insert_is_Some.
        destruct (decide (dst = rx)); [ auto | right; split; auto]. }
      (* Prove in the general case that the value relation holds for the register that was loaded to - unless it was the PC.*)
       { iIntros (ri ? Hri Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)).
        { subst ri. simplify_map_eq.
          destruct (decide ((a0, v0) = (a'', v''))).
          - simplify_eq; iFrame "Hw".
          - iClear "HLoadRes Hwrite". rewrite decide_True; auto.
        }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. }
       }
       { subst regs'. rewrite insert_insert. iApply "Hmap". }
       { iModIntro.
         destruct (decide (PC = dst)); simplify_eq.
         - simplify_map_eq. rewrite (fixpoint_interp1_eq).
           destruct (decide ((a0, v0) = (a, v))).
           + simplify_map_eq.
           + iClear "HLoadRes Hwrite". rewrite decide_True;auto.
             rewrite !fixpoint_interp1_eq.
             destruct o as [-> | ->]; iFrame "Hinterp".
         - (* iExists p'. *) simplify_map_eq.
           iClear "Hw Hinterp Hwrite".
           rewrite !fixpoint_interp1_eq /=.
           destruct o as [-> | ->]; iFrame "Hinv".
       }
    }
    { rewrite /allow_load_res /allow_load_mem.
      destruct (decide (reg_allows_load (<[PC:=LCap p b e a v]> lregs) src p0 b0 e0 a0 v0 ∧ (a0, v0) ≠ (a, v))).
      - iDestruct "HLoadMem" as "(_&H)".
        iDestruct "H" as (lw') "(->&Hres&Hinterp)". rewrite /region_open_resources.
        destruct a1. rewrite memMap_resource_2ne; last auto.
        iDestruct "Hmem" as "[Ha0 Ha]". iDestruct "Hres" as "(HP' & Hread' & Hcls')".
        iMod ("Hcls'" with "[HP' Ha0]");[iExists lw';iFrame|iModIntro].
        iMod ("Hcls" with "[Ha HP]");[iExists lw;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
      - iModIntro. iDestruct "HLoadMem" as "(_&->)". rewrite -memMap_resource_1.
        iMod ("Hcls" with "[Hmem HP]");[iExists lw;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
