From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
Require Import Coq.Logic.Decidable.
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

  Definition incrementPC (regs: Reg) :=
    match regs !! PC with
    | Some (inr ((p, g), b, e, a)) =>
      match (a + 1)%a with
      | Some a' => Some (<[ PC := inr ((p, g), b, e, a') ]> regs)
      | None => None
      end
    | _ => None
    end.

  Lemma incrementPC_Some_inv regs regs' :
    incrementPC regs = Some regs' ->
    exists p g b e a a',
      (* todo: consistency, use !r! ? *)
      regs !! PC = Some (inr ((p, g), b, e, a)) ∧
      (a + 1)%a = Some a' ∧
      regs' = <[ PC := inr ((p, g), b, e, a') ]> regs.
  Proof.
    unfold incrementPC.
    destruct (regs !! PC) as [ [| [ [ [ [? ?] ?] ?] u] ] |];
      try congruence.
    case_eq (u+1)%a; try congruence. intros ? ?. inversion 1.
    do 6 eexists. split; eauto.
  Qed.

  Lemma incrementPC_None_inv regs p g b e a :
    incrementPC regs = None ->
    (* !r! ? *)
    regs !! PC = Some (inr ((p, g), b, e, a)) ->
    (a + 1)%a = None.
  Proof.
    unfold incrementPC.
    destruct (regs !! PC) as [ [| [ [ [ [? ?] ?] ?] u] ] |];
      try congruence.
    case_eq (u+1)%a; congruence.
  Qed.

  Lemma incrementPC_fail_updatePC regs m :
     incrementPC regs = None ->
     updatePC (regs, m) = (Failed, (regs, m)).
   Proof.
     rewrite /incrementPC /updatePC /RegLocate /=.
     destruct (regs !! PC) as [X|]; auto.
     destruct X as [| [ [ [ [? ?] ?] ?] a'] ]; auto.
     destruct (a' + 1)%a; auto. congruence.
   Qed.

  (* Permission-carrying memory type, used for the map of locations below *)
  Definition PermMem := gmap Addr (Perm * Word).

  Inductive Load_failure (regs: Reg) (r1 r2: RegName) (mem : PermMem):=
  | Load_fail_bounds p g b e a:
     regs !r! r2 = inr ((p, g), b, e, a) ->
     (readAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false) →
     Load_failure regs r1 r2 mem
  | Load_fail_const z:
     regs !r! r2 = inl z ->
     Load_failure regs r1 r2 mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC p p' g b e a loadv:
     regs !r! r2 = inr ((p, g), b, e, a) ->
     mem !! a = Some(p', loadv) →
     incrementPC (<[ r1 := loadv ]> regs) = None ->
     Load_failure regs r1 r2 mem
  .

  (* TODO; delete these here*)
  Instance addr_dec_eq (a a' : Addr) : Decision (a = a') := _.
  Instance perm_dec_eq (p p' : Perm) : Decision (p = p') := _. Proof. solve_decision. Qed.
  Instance local_dec_eq (l l' : Locality) : Decision (l = l') := _.  Proof. solve_decision. Qed.
  Instance cap_dec_eq (c c' : Cap) : Decision (c = c').
  Proof.
         repeat (refine (prod_eq_dec _ _); unfold EqDecision; intros); solve_decision. Qed.
  Instance option_dec_eq `(A_dec : ∀ x y : B, Decision (x = y)) (o o': option B) : Decision (o = o').
  Proof. solve_decision. Qed.

  (* Conditionally unify on the read register value *)
  Definition read_reg_inr  (regs : Reg) (r : RegName) p g b e a :=
    regs !! r = Some (inr ((p, g), b, e, a)) ∨ ∃ z, regs !! r = Some(inl z).

 Definition reg_allows_load (regs : Reg) (r : RegName) p g b e a  :=
    regs !! r = Some (inr ((p, g), b, e, a)) ∧
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true.

  Instance reg_allows_load_dec_eq  (regs : Reg) (r : RegName) p g b e a : Decision (reg_allows_load regs r p g b e a).
  Proof.
    unfold reg_allows_load. destruct (regs !! r). destruct s.
    - right. intros Hfalse; destruct Hfalse; by exfalso.
    - assert (Decision (Some (inr (A:=Z) p0) = Some (inr (p, g, b, e, a)))) as Edec.
      refine (option_dec_eq _ _ _). intros.
      refine (sum_eq_dec _ _); unfold EqDecision; intros. refine (cap_dec_eq x0 y0).
      solve_decision.
    - solve_decision.
 Qed.

  Inductive Load_spec
            (regs: Reg) (r1 r2: RegName)
            (regs': Reg) (retv: cap_lang.val) (mem : PermMem) : Prop
    :=
    | Load_spec_success p p' g b e a loadv :
        retv = NextIV ->
        reg_allows_load regs r2 p g b e a →
        mem !! a = Some(p', loadv) →
        incrementPC
          (<[ r1 := loadv ]> regs) = Some regs' ->
        Load_spec regs r1 r2 regs' retv mem

    | Load_spec_failure :
        retv = FailedV ->
        Load_failure regs r1 r2 mem ->
        Load_spec regs r1 r2 regs' retv mem.

  Instance ne_interpC : NonExpansive
                           (λ Wv : prodO (leibnizO (STS * STS)) (leibnizO Word), (interp Wv.1) Wv.2).
  Proof. intros. solve_proper. Qed.

  Notation interpC :=
    (λne Wv : prodO (leibnizO (STS * STS)) (leibnizO Word), (interp Wv.1) Wv.2).

  (* TODO: remove - defined elsewhere *)
  Notation monotonicity_guarantees_region ρ v p φ :=
      (match ρ with
      | Temporary => if pwl p then future_pub_mono else future_priv_mono
      | Permanent => future_priv_mono
      | Revoked => λ (_ : prodO STS STS * Word → iProp Σ) (_ : Word), True
      end φ v)%I.

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately
   Note how the boolean bl is used to keep track of whether or not we have applied the wp lemma yet *)
  Definition region_open_resources W l ls p φ v (bl : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std (countable.encode l) ρ
    ∗ ⌜ρ ≠ Revoked⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ (if bl then monotonicity_guarantees_region ρ v p φ ∗ φ (W, v)
       else ▷ monotonicity_guarantees_region ρ v p φ ∗  ▷ φ (W, v) )
    ∗ rel l p φ)%I.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_load_res_or_true W r (regs : Reg) pc_a pc_p:=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a ) then
       if decide (a ≠ pc_a) then
         ∃ p' w, a ↦ₐ [p'] w  ∗ ⌜PermFlows p p'⌝ ∗ (region_open_resources W a [pc_a] p' interpC w false)
       else ⌜PermFlows p pc_p⌝ ∗ open_region pc_a W
      else open_region pc_a W)%I.

  Definition allow_load_mem_or_true W r (regs : Reg) pc_a pc_p pc_w (mem : PermMem) (bl: bool):=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a) then
       if decide (a ≠ pc_a) then
         ∃ p' w, ⌜mem = <[a:=(p',w)]> (<[pc_a:=(pc_p,pc_w)]> ∅)⌝ ∗
            ⌜PermFlows p p'⌝ ∗ (region_open_resources W a [pc_a] p' interpC w bl)
       else  ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ ⌜PermFlows p pc_p⌝ ∗ open_region pc_a W     else  ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ open_region pc_a W)%I.

  Definition allow_load_map_or_true r (regs : Reg) (mem : PermMem):=
    ∃ p g b e a, read_reg_inr regs r p g b e a ∧
      if decide (reg_allows_load regs r p g b e a) then
        ∃ p' w, mem !! a = Some (p', w) ∧ PermFlows p p'
      else True.

 (* Special wp-subcases: failure due to an incorrect pc *)
  Lemma wp_notCorrectPC_perm E pc_p pc_g pc_b pc_e pc_a :
      pc_p ≠ RX ∧ pc_p ≠ RWX ∧ pc_p ≠ RWLX →
      {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");
      [apply not_isCorrectPC_perm;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* This should go to Lang *)
  Lemma not_isCorrectPC_bounds p g b e a :
   ¬ (b <= a < e)%a → ¬ isCorrectPC (inr ((p,g),b,e,a)).
  Proof.
    intros Hbounds.
    intros Hvpc. inversion Hvpc.
    by exfalso.
  Qed.

  Lemma wp_notCorrectPC_range E pc_p pc_g pc_b pc_e pc_a :
       ¬ (pc_b <= pc_a < pc_e)%a →
      {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");
      [apply not_isCorrectPC_bounds;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* TODO: update this inside logrel.v *)
 Lemma writeLocalAllowed_implies_local W p l b e a:
    pwl p = true ->
    interp W (inr (p, l, b, e, a)) -∗ ⌜isLocal l = true⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H3; try congruence; destruct l; eauto.
  Qed.

  (* TODO: move this somewhere appropriate - logrel or fundamental *)
  Definition PC_condition W p g b e:=
  (∃ p', ⌜PermFlows p p'⌝ ∧
           ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p' interp)
                                             ∧ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝
                                             ∧ ⌜region_std W a⌝))%I.
  (*TODO: move to logrel *)
  Lemma readAllowed_implies_PC_condition W p l b e a:
    readAllowed p = true ->
    interp W (inr (p, l, b, e, a)) -∗ PC_condition W p l b e.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    unfold PC_condition.
    destruct p; simpl in H3; try congruence; destruct l; auto.
    all: iDestruct "Hvalid" as (p) "[% Hvalid]"; iExists p; iSplitR; auto.
    all: iDestruct "Hvalid" as "[Hvalid _]"; auto.
  Qed.

   Lemma wp_load Ep
     pc_p pc_g pc_b pc_e pc_a pc_p'
     r1 r2 w mem regs :
   cap_lang.decode w = Load r1 r2 →
   PermFlows pc_p pc_p' →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   (∀ (ri: RegName), is_Some (regs !! ri)) →
   mem !! pc_a = Some (pc_p', w) →
   allow_load_map_or_true r2 regs mem →

   {{{ (▷ [∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 regs' retv mem⌝ ∗
         ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∧ a ↦ₐ[p] w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Admitted.



  Lemma load_case'(W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst src : RegName) :
    ftlr_instr W r p p' g b e a w (Load dst src) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* Handy to read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=inr (p, g, b, e, a)]> r !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1*)
    specialize Hsome' with src as Hsrc.
    destruct Hsrc as [wsrc Hsomesrc].
    assert (∃ p0 g0 b0 e0 a0 , read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) src p0 g0 b0 e0 a0) as [p0 [g0 [b0 [e0 [a0 HVsrc] ] ] ] ].
    {
      unfold read_reg_inr. destruct wsrc. 2: destruct c,p0,p0,p0. all: repeat eexists.
      right. by exists z.
      by left.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res_or_true *)
    iAssert (allow_load_res_or_true W src (<[PC:=inr (p, g, b, e, a)]> r) a p' ∗ sts_full_world sts_std W)%I with "[Hr Hsts]" as "[HLoadRes Hsts]".
    {
      unfold allow_load_res_or_true.
      do 5 (iApply sep_exist_r; iExists _). iFrame "%".
      destruct (decide (reg_allows_load (<[PC:=inr (p, g, b, e, a)]> r) src p0 g0 b0 e0 a0)). 1: rename r0 into Hallows.

      -  destruct Hallows as [Hrinr [Hra Hwb] ].
         destruct (decide (a0 ≠ a)); rename n into Haeq.
         * apply andb_prop in Hwb as [Hle Hge].
           rewrite /leb_addr in Hle,Hge.

           (* Unlike in the old proof, we now go the other way around, and prove that the source register could not have been the PC, since both addresses differ. This saves us some cases.*)
           assert (src ≠ PC) as n.
           {
             intros contra. rewrite contra in Hrinr.
             rewrite lookup_insert in Hrinr. inversion Hrinr. congruence.
           }

           iDestruct ("Hreg" $! src n) as "Hvsrc".
           rewrite lookup_insert_ne in Hrinr; last by congruence.
           rewrite /RegLocate Hrinr.
           iDestruct (read_allowed_inv _ a0 with "Hvsrc") as "Hconds"; auto;
            first (split; by apply Z.leb_le).

          rewrite /read_write_cond.
          iDestruct "Hconds" as (p0' Hfl') "Hrel'".
          iDestruct (region_open_prepare with "Hr") as "Hr".
          iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as "%"; eauto.
          { rewrite /withinBounds /leb_addr Hle Hge. auto. }
          destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
          (*We can finally frame off Hsts here, since it is no longer needed after opening the region*)
          iDestruct (region_open_next _ _ _ a0 p0' ρ' with "[$Hrel' $Hr $Hsts]") as (w0) "($ & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists p0', w0. iSplitL "Ha0"; auto. iSplitR; auto. unfold region_open_resources.
          iExists ρ'. iFrame "%". iFrame. by iFrame "#".
        * iFrame.
          destruct (decide (src = PC)) ; simplify_eq.
          + rewrite lookup_insert in Hrinr.
            inversion Hrinr. rewrite -H4. auto.
          +  iDestruct ("Hreg" $! src n) as "Hsrcv".
             rewrite lookup_insert_ne in Hrinr; last by congruence.
             rewrite /RegLocate Hrinr.
             iDestruct (read_allowed_inv _ a0 with "Hsrcv") as (p'' Hfl') "#Harel'".
             { apply andb_true_iff in Hwb as [Hle Hge].
               split; apply Zle_is_le_bool; auto. }
             { destruct p0; inversion Hra; auto. }
             rewrite /read_write_cond.
             assert (a0 = a). by apply dec_stable.
             rewrite -H3.
             by iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
      - iFrame.
    }
    (* Clear helper values; they exist in the existential now *)
    clear HVsrc p0 g0 b0 e0 a0.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iAssert (∃mem, allow_load_mem_or_true W src (<[PC:=inr (p, g, b, e, a)]> r) a p' w mem false ∗ (▷ [∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) )%I with "[HLoadRes Ha]" as (mem) "[HLoadMem HMemRes]".
    {
      unfold allow_load_res_or_true. iDestruct "HLoadRes" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
      unfold allow_load_mem_or_true.
      iAssert (∃ (p1 : Perm) (w1 : leibnizO Word), ⌜(p',w) = (p1, w1)⌝ ∗ a ↦ₐ[p1] w1)%I with "[Ha]" as "Ha". iExists p',w. auto.

      case_decide as Hallows.
      -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
         case_decide as Haeq.
         * iDestruct "HLoadRes" as (p'0 w0) "[HLoadCh HLoadRest]".
           iExists (<[a1:=(p'0, w0)]> (<[a:=(p', w)]> ∅)).

           iSplitL "HLoadRest".
           + iExists p1,g1,b1,e1,a1. iSplitR; first auto.
             do 2 (case_decide; last by exfalso).
             iExists p'0,w0. iSplitR; auto.
           + iNext.
             iAssert (∃ (p1 : Perm) (w1 : leibnizO Word), ⌜(p'0,w0) = (p1, w1)⌝ ∗ a1 ↦ₐ[p1] w1)%I with "[HLoadCh]" as "HLoadCh". iExists p'0,w0. by iSplitR.

             rewrite (big_sepM_insert _ _).
             rewrite (big_sepM_insert _ _).
             iFrame. rewrite (big_opM_empty). auto.
             ++ auto.
             ++ rewrite lookup_insert_ne; auto.
         * iExists ( <[a:=(p', w)]> ∅).
           iSplitL "HLoadRes".
           + iExists p1,g1,b1,e1,a1. iSplitR; auto.
             case_decide; last by exfalso. case_decide; first by exfalso.
             iDestruct "HLoadRes" as (HPF) "HLoadRes". iSplitR; auto.
           + iNext. rewrite (big_sepM_insert _ _ a (p',w)).
             iFrame.  rewrite (big_opM_empty). all: auto.
      - iExists ( <[a:=(p', w)]> ∅).
        iSplitL "HLoadRes".
        + iExists p1,g1,b1,e1,a1. iSplitR; auto.
          case_decide; first by exfalso. auto.
        + iNext. rewrite (big_sepM_insert _ _ a (p',w)).
          iFrame. rewrite (big_opM_empty). all: auto.
    }

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iAssert (⌜mem !! a = Some (p', w)⌝ ∗ ⌜allow_load_map_or_true src (<[PC:=inr (p, g, b, e, a)]> r) mem⌝)%I with "[HLoadMem]" as %(HReadPC & HLoadAP).
    {
      unfold allow_load_mem_or_true.
      iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
      unfold allow_load_map_or_true.
      case_decide as Hallows.
      -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
         case_decide as Haeq.
         * iDestruct "HLoadRes" as (p'0 w0 ->) "[% _]".
           iSplitR. rewrite lookup_insert_ne; auto. by rewrite lookup_insert.
           iExists p1,g1,b1,e1,a1. iSplitR; auto.
           case_decide; last by exfalso.
           iExists p'0,w0. iSplitR; auto.
           by rewrite lookup_insert.
         * iDestruct "HLoadRes" as "[-> [% HLoadRes] ]".
           iSplitR. by rewrite lookup_insert.
           iExists p1,g1,b1,e1,a1. iSplitR; auto.
           case_decide; last by exfalso.
           iExists p',w. by rewrite Haeq lookup_insert.
      - iDestruct "HLoadRes" as "[-> HLoadRes]".
        iSplitR. by rewrite lookup_insert.
        iExists p1,g1,b1,e1,a1. iSplitR; auto.
        case_decide; first by exfalso. auto.
    }

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iAssert (▷ allow_load_mem_or_true W src (<[PC:=inr (p, g, b, e, a)]> r) a p' w mem true)%I with "[HLoadMem]" as "HLoadMem".
    {
      unfold allow_load_mem_or_true.
      iDestruct "HLoadMem" as (p0 g0 b0 e0 a0) "[% HLoadMem]".
      do 5 (iApply later_exist_2; iExists _). iApply later_sep_2; iSplitR; auto.
      case_decide.
      - case_decide.
        * iDestruct "HLoadMem" as (p'0 w0) "[-> [% HLoadMem] ]".
        do 2 (iApply later_exist_2; iExists _).
        do 2 (iApply later_sep_2; iSplitR; auto).
        * iFrame.
      - iFrame.
    }

    iApply (wp_load with "[Hmap HMemRes]"); eauto.
    {by rewrite lookup_insert. }
    {iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[>Hmem Hmap]".

    destruct HSpec as [|].
    { subst retv.
      apply incrementPC_Some_inv in H6.
      destruct H6 as (?&?&?&?&?&?&?&?&?).

      iApply wp_pure_step_later; auto. iNext.

      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iAssert (open_region a W ∗ a ↦ₐ[p'] w ∗ ((fixpoint interp1) W) loadv)%I with "[HLoadMem Hmem]" as "[Hr [Ha #HLVInterp ] ]".
      {
        unfold allow_load_mem_or_true.
        iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
        destruct (decide (reg_allows_load (<[PC:=inr (p, g, b, e, a)]> r) src p1 g1 b1 e1 a1)). 1: rename r0 into Hallows.
        -  destruct Hallows as [Hrinr [Hra Hwb] ].
           destruct (decide (a1 ≠ a)); rename n into Haeq.
           * iDestruct "HLoadRes" as (p'1 w0) "[-> [% HLoadRes] ]".
             iDestruct "HLoadRes" as (ρ1) "(Hstate' & % & Hr & % & (Hfuture & #HV) & Hrel')".
             iAssert ( a ↦ₐ[p'] w ∗ a1 ↦ₐ[p'1] w0)%I  with "[Hmem]" as "[$ Ha1]".
             {
               rewrite (big_sepM_insert); last by rewrite lookup_insert_ne.
               rewrite (big_sepM_insert); last by auto.
               iDestruct "Hmem" as "[Ha1 [Ha _] ]".
               iSplitL "Ha".
               * iDestruct "Ha" as (p2 w1 Hpair) "Ha".
                   by inversion Hpair.
               * iDestruct "Ha1" as (p2 w1 Hpair) "Ha".
                   by inversion Hpair.
             }
             iDestruct (region_close_next with "[$Hr $Ha1 $Hrel' $Hstate' $Hfuture]") as "Hr"; eauto.
             { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
             iDestruct (region_open_prepare with "Hr") as "$".
             destruct H4 as (Hrinr0 & _ & _). rewrite Hrinr0 in Hrinr; inversion Hrinr.
             rewrite H16 lookup_insert in H5; inversion H5. done.
           * apply dec_stable in Haeq.
             iDestruct "HLoadRes" as "[-> [% $ ] ]".
             iAssert ( a ↦ₐ[p'] w)%I  with "[Hmem]" as "$".
             {
               rewrite (big_sepM_insert); last by auto.
               iDestruct "Hmem" as "[Ha _]".
               iDestruct "Ha" as (p2 w1 Hpair) "Ha".
                 by inversion Hpair.
             }
             destruct H4 as (Hrinr0 & _ & _). rewrite Hrinr0 in Hrinr; inversion Hrinr.
             rewrite H14 Haeq lookup_insert in H5; inversion H5. done.
        - pose (H4' := H4).
          destruct H4' as (Hinr0 & _ & _). destruct H8 as [Hinr1 | Hinl1].
          * rewrite Hinr0 in Hinr1. inversion Hinr1.
            rewrite H9 H10 H11 H12 H13 in H4. by exfalso.
          * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
      }

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC*)
      destruct (decide (x = RX ∨ x = RWX ∨ x = RWLX)).
      2 : {
        assert (x ≠ RX ∧ x ≠ RWX ∧ x ≠ RWLX). split; last split; by auto.
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { rewrite H7. by rewrite lookup_insert. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext. iApply wp_value.
        iIntros (a1); inversion a1.
      }

      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      iApply ("IH" $! _ regs' with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]").
      { cbn. intros. subst regs'.
        rewrite lookup_insert_is_Some.
        destruct (decide (PC = x5)); [ auto | right; split; auto].
        rewrite lookup_insert_is_Some.
        destruct (decide (dst = x5)); [ auto | right; split; auto]. }
      (* Prove in the general case that the value relation holds for the register that was loaded to - unless it was the PC.*)
       { iIntros (ri Hri).
        subst regs'.
        erewrite locate_ne_reg; [ | | reflexivity]; auto.
        destruct (decide (ri = dst)).
        { subst ri.
          erewrite locate_eq_reg; [ | reflexivity]; auto.
        }
        { repeat (erewrite locate_ne_reg; [ | | reflexivity]; auto).
          iApply "Hreg"; auto. }
       }
       { subst regs'. rewrite insert_insert. iApply "Hmap". }
       { destruct (decide (PC = dst)); simplify_eq.
         - destruct o as [HRX | [HRWX | HRWLX] ]; auto.
           rewrite lookup_insert in H3; inversion H3. rewrite HRWLX.
           iDestruct (writeLocalAllowed_implies_local _ RWLX with "[HLVInterp]") as "%"; auto.
           destruct x0; unfold isLocal in H7; first by congruence.
           iPureIntro; do 2 right; auto.
         - rewrite lookup_insert_ne in H3; last by auto. rewrite lookup_insert in H3; inversion H3.
           by rewrite -H8 -H9.
       }
       { iAlways. auto.
         destruct (decide (PC = dst)); simplify_eq.
         - rewrite lookup_insert in H3; inversion H3. rewrite (fixpoint_interp1_eq W).
           iApply readAllowed_implies_PC_condition; auto.
           { destruct o as [o | [o | o] ]; rewrite o; auto . }
         - iExists p'. rewrite lookup_insert_ne in H3; last by auto. rewrite lookup_insert in H3; inversion H3. iSplitR; first by rewrite -H8. auto.
       }
    }
    { subst retv.
      iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

  Lemma load_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst src : RegName) :
    ftlr_instr W r p p' g b e a w (Load dst src) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    destruct (decide (PC = dst)),(decide (PC = src)); simplify_eq.
    * (* Load PC PC ==> fail *)
      iApply (wp_load_fail3 with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      iApply wp_value.
      iNext. iIntros "%"; inversion a0.
    * (* Load PC src ==> success if src ↦ inr, fail o/w *)
      specialize Hsome with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      assert ((delete PC r !! src) = Some wsrc) as Hsomesrc'.
      { rewrite -Hsomesrc. apply (lookup_delete_ne r PC src). eauto. }
      rewrite delete_insert_delete.
      iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
      destruct wsrc.
      { (* src ↦ inl z ==> fail *)
        iApply (wp_load_fail2 with "[HPC Ha Hsrc]"); eauto; iFrame.
        iNext. iIntros "[HPC [Ha Hsrc]] /=".
        iApply wp_pure_step_later; auto. iApply wp_value.
        iNext. iIntros "%"; inversion a0.
      }
      (* src ↦ inr c ==> need to open invariant *)
      destruct c. do 3 destruct p0.
      (* if p is not ra or a0 is not within bounds: fail *)
      destruct (decide ((readAllowed p0 && withinBounds ((p0,l),a2,a1,a0)) = false)).
      { (* Capability fail *)
        iApply (wp_load_fail1 with "[HPC Ha Hsrc]"); eauto.
        - split; eauto. apply andb_false_iff. eauto.
        - iFrame.
        - iNext. iIntros "[HPC [Ha Hsrc]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros "%"; inversion a3.
      }
      (* readAllowed p && withinBounds ((p,l),a2,a1,a0) *)
      apply (not_false_is_true (_ && _)),andb_prop in n0
        as [Hra Hwb]. apply andb_prop in Hwb as [Hle Hge].
      rewrite /leb_addr in Hle,Hge.
      (* get validity of capability in src from Hreg *)
      apply reg_eq_sym in n.
      iDestruct ("Hreg" $! src n) as "Hvsrc".
      rewrite /RegLocate Hsomesrc.
      iDestruct (read_allowed_inv _ a0 with "Hvsrc") as "Hconds"; auto;
        first (split; by apply Z.leb_le).
      (* Each condition in Hconds take a step in similar fashion *)
      destruct (decide (a = a0)).
      {
        subst.
        (* no need to open any invariant, in this case we need to do cases on
           a = a0. if a = a0, then the program should crash, since we will not
           be able to increment w once loaded into PC. *)
        iApply (wp_load_fail5 with "[HPC Ha Hsrc]"); try iFrame; auto.
        - apply PermFlows_refl.
        - split;auto. apply andb_true_iff. split; auto.
        - destruct (a0 =? a0)%a eqn:Hcontr; first done.
          rewrite /eqb_addr Z.eqb_refl in Hcontr; inversion Hcontr.
        - iNext. iIntros "(_ & _ & _ & _) /=".
          iApply wp_pure_step_later;[auto|]. iNext.
          iApply wp_value. iIntros (Hcontr); inversion Hcontr.
      }
      rewrite /read_write_cond.
      iDestruct "Hconds" as (p0' Hfl') "Hrel'".
      iDestruct (region_open_prepare with "Hr") as "Hr".
      iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as "%"; eauto.
      { rewrite /withinBounds /leb_addr Hle Hge. auto. }
      destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
      iDestruct (region_open_next _ _ _ a0 p0' ρ' with "[$Hrel' $Hr $Hsts]") as (w0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
      { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
      iAssert (∀ w1 w2, full_map (<[PC:=w1]> (<[src:=w2]> r)))%I as "#Hfull'".
      { iIntros (w1 w2 r0).
        iPureIntro.
        destruct (decide (PC = r0)); [simplify_eq; rewrite lookup_insert; eauto|].
        rewrite lookup_insert_ne.
        destruct (decide (src = r0)); [simplify_eq; rewrite lookup_insert; eauto|].
        rewrite lookup_insert_ne. apply Hsome. done. done.
      }
      destruct w0.
      { iApply (wp_load_fail5 with "[HPC Ha Hsrc Ha0]")
        ;[eauto|apply Hfp|apply Hfl'| | | | |]; eauto.
        - split; [eauto|]. apply Is_true_eq_true; eauto.
          apply andb_prop_intro.
          split; apply Is_true_eq_left; [apply Hle|apply Hge].
        - destruct (a0 =? a)%a; iFrame.
        - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros "%"; inversion a3.
      }
      destruct c,p1,p1,p1.
      destruct ((a3 + 1)%a) eqn:Ha0.
      2: { (* If src points to top address, load crashes *)
        iApply (wp_load_fail4 with "[HPC Hsrc Ha Ha0]")
        ;[eauto|apply Hfp|apply Hfl'| | | | | |]; eauto.
        - split; [eauto|]. apply Is_true_eq_true; eauto.
          apply andb_prop_intro.
          split; apply Is_true_eq_left; [apply Hle|apply Hge].
        - destruct (a0 =? a)%a; iFrame.
        - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros (Hcontr); inversion Hcontr.
      }
      (* successful load into PC *)
      iApply (wp_load_success_PC with "[$HPC $Ha $Hsrc Ha0]")
      ;[eauto|apply Hfp|apply Hfl'| | | | |]; eauto.
      { split; [eauto|]. apply Is_true_eq_true; eauto.
        apply andb_prop_intro.
        split; apply Is_true_eq_left; [apply Hle|apply Hge].  }
      iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
      iApply wp_pure_step_later; auto. iNext.
      iAssert (⌜p1 ≠ RX⌝ ∧ ⌜p1 ≠ RWX⌝ ∧ ⌜p1 ≠ RWLX⌝ →
               PC ↦ᵣ inr (p1, l0, a5, a4, a6) -∗
                  WP Seq (Instr Executable) {{ w, ⌜w = FailedV⌝
                    ∗ PC ↦ᵣ inr (p1, l0, a5, a4, a6) }})%I
            as "Hfail".
      { iIntros "(% & % & %) HPC".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "[HPC]");
              [apply not_isCorrectPC_perm;eauto|iFrame|].
        iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iFrame. done.
      }
      (* The new register state is valid *)
      iAssert (interp_registers W (<[src:=inr (p0, l, a2, a1, a0)]> r)) as "[#Hfull'' #Hreg'']".
      { iSplitL.
        { iIntros (r0). iPureIntro.
          destruct (decide (src = r0)); simplify_eq;
            [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
        iIntros (r0) "%".
        destruct (decide (src = r0)); simplify_eq.
        + by rewrite /RegLocate lookup_insert.
        + rewrite /RegLocate lookup_insert_ne; auto.
          iDestruct ("Hreg" $! (r0) a7) as "Hr0".
          specialize Hsome with r0.
          destruct Hsome as [c Hsome].
          rewrite Hsome. iApply "Hr0"; auto.
      }
      (* close region *)
      iDestruct (region_close_next with "[$Hr $Ha0 $Hrel' $Hstate' $Hfuture]") as "Hr"; eauto.
      { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
      iDestruct (region_open_prepare with "Hr") as "Hr".
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      destruct (perm_eq_dec p1 RX).
      { iClear "Hfail".
        iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
          rewrite -delete_insert_ne; auto;
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
        (* apply IH *)
        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
        iAlways. subst p1.
        rewrite (fixpoint_interp1_eq _ (inr (RX, l0, a5, a4, a3))) /=.
        iDestruct "Hval" as (q Hq) "[Hb0e0 Hexec]".
        iExists q. iSplit; auto. }
      destruct (perm_eq_dec p1 RWX).
      { subst p1. iClear "Hfail".
        iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
          rewrite -delete_insert_ne; auto;
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
        (* apply IH *)
        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
        iAlways.
        rewrite (fixpoint_interp1_eq _ (inr (RWX, l0, a5, a4, a3))) /=.
        iDestruct "Hval" as (q Hq) "[Hb0e0 Hexec]".
        iExists q. iSplit; auto. }
      destruct (perm_eq_dec p1 RWLX).
      { subst p1. iClear "Hfail".
        iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
          rewrite -delete_insert_ne; auto;
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
        rewrite (fixpoint_interp1_eq _ (inr (RWLX, l0, a5, a4, a3))) /=.
        destruct l0; auto.
        (* apply IH *)
        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
        iAlways.
        iDestruct "Hval" as (q Hq) "[Hb0e0 Hexec]".
        iExists q. iSplit; auto. }
      iDestruct ("Hfail" with "[%] [HPC]") as "Hfail"; auto.
      iApply (wp_wand with "Hfail"). iIntros (v) "[-> HPC]".
      iIntros. discriminate.
    * destruct (Hsome dst) as [wdst Hsomedst].
      rewrite delete_insert_delete.
      assert ((delete PC r !! dst) = Some wdst) as Hsomedst'.
      { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
      destruct (a + 1)%a eqn:Ha'.
      2: { (* if PC cannot be incremented ==> dst is updated, then program crashes *)
          iApply (wp_load_fail6 with "[HPC Hdst Ha]"); eauto.
          iFrame. iNext. iIntros "[HPC [Ha Hdst]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value; auto.
          iNext.
          iIntros (Hcontr); inversion Hcontr.
        }
        (* if PC can be incremented, load succeeds ==> apply IH *)
        iApply (wp_load_success_fromPC with "[HPC Hdst Ha]"); eauto.
        iFrame.
        iNext. iIntros "[HPC [Ha Hdst]] /=".
        iApply wp_pure_step_later; auto.
        (* we want to apply IH on the updated register state *)
        iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                 [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                 rewrite -delete_insert_ne; auto;
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                 [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
        (* apply IH *)
        iAssert (▷ interp_registers _ (<[dst:=w]> r))%I
          as "#[Hfull' Hreg']".
        { iNext. iSplitL.
          { iIntros (r0). iPureIntro.
            destruct (decide (dst = r0)); simplify_eq;
              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
          iIntros (r0) "%".
          destruct (decide (dst = r0)); simplify_eq.
              + by rewrite /RegLocate lookup_insert.
              + rewrite /RegLocate lookup_insert_ne; auto.
                iDestruct ("Hreg" $! (r0) a1) as "Hr0".
                specialize Hsome with r0.
                destruct Hsome as [c Hsome].
                rewrite Hsome. iApply "Hr0"; auto.
        }
        iNext.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto; iFrame "#".
    * destruct (Hsome src) as [wsrc Hsomesrc].
      assert ((delete PC r !! src) = Some wsrc) as Hsomesrc'.
      { rewrite -Hsomesrc. apply (lookup_delete_ne r PC src). eauto. }
      rewrite delete_insert_delete.
      iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
      destruct wsrc.
      { (* src ↦ inl z ==> fail *)
        iApply (wp_load_fail2 with "[HPC Ha Hsrc]"); eauto; iFrame.
        iNext. iIntros "[HPC [Ha Hsrc]] /=".
        iApply wp_pure_step_later; auto. iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr.
      }
      (* src ↦ inr c ==> need to open invariant *)
      destruct c. do 3 destruct p0.
       (* if p is not ra or a0 is not within bounds: fail *)
      destruct (decide ((readAllowed p0 && withinBounds ((p0,l),a2,a1,a0)) = false)).
      { (* Capability fail *)
        iApply (wp_load_fail1 with "[HPC Ha Hsrc]"); eauto.
        - split; eauto. apply andb_false_iff. eauto.
        - iFrame.
        - iNext. iIntros "[HPC [Ha Hsrc]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value. iNext.
          iIntros (Hcontr); inversion Hcontr.
      }
      (* readAllowed p && withinBounds ((p,l),a2,a1,a0) *)
      apply (not_false_is_true (_ && _)),andb_prop in n1
        as [Hra Hwb]. apply andb_prop in Hwb as [Hle Hge].
      rewrite /leb_addr in Hle,Hge.
      (* the contents of src is valid *)
      iAssert ((fixpoint interp1) _ (inr (p0, l, a2, a1, a0))) as "#Hvsrc".
      { apply reg_eq_sym in n0. iDestruct ("Hreg" $! src n0) as "Hvsrc".
        rewrite /RegLocate Hsomesrc /=. by iApply "Hvsrc". }
      iDestruct (read_allowed_inv _ a0 with "Hvsrc") as "Hconds"; auto;
        first (split; by apply Z.leb_le).
      (* Each condition in Hconds take a step in similar fashion *)
      iAssert ((∃ w' p'', ▷ ((if (a0 =? a)%a then emp else a0 ↦ₐ[p''] w') -∗ open_region a W)
                            ∗ (if (a0 =? a)%a then emp else ▷ a0 ↦ₐ[p''] w')
                            ∗ ▷ ▷ (fixpoint interp1) W w' ∗ ⌜PermFlows p0 p''⌝
               (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
        ∗ sts_full_world sts_std W
        -∗ WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (W' : leibnizO (STS * STS)),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv_world W W'⌝
                                           ∗ na_own logrel_nais ⊤ ∗ sts_full_world sts_std W' ∗ region W' }} }} )%I
        with "[Ha HPC Hsrc Hmap Hown Hstate Hmono]" as "Hstep".
      { iIntros "[Hres Hsts]".
        iDestruct "Hres" as (w0 p'') "[Hr [Ha0 [#Hw0 %]]]".
        (* if PC cannot be incremented ==> dst is updated, then program crashes *)
        destruct (a + 1)%a eqn:Ha'; simplify_eq.
        2: { destruct (decide (src = dst)); simplify_eq.
             - iApply (wp_load_fail8 with "[HPC Hsrc Ha Ha0]");
                 [eauto|eauto|apply Hfp|apply H3| | | | | | ]; eauto.
               { split; apply Is_true_eq_true; [eauto|].
                 apply andb_prop_intro.
                 split; apply Is_true_eq_left; [apply Hle|apply Hge].
               }
               iFrame. iNext. iIntros "[HPC [Ha [Hdst Ha0]]] /=".
               iApply wp_pure_step_later; auto.
               iApply wp_value. iNext.
               iIntros (Hcontr); inversion Hcontr.
             - destruct (Hsome dst) as [wdst Hsomedst].
               assert (delete PC r !! dst = Some wdst) as Hsomedst'.
               { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
               assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
               { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
                 eauto. }
               iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
                 eauto.
               iApply (wp_load_fail7 with "[HPC Hsrc Hdst Ha Ha0]");
                 [eauto|apply Hfp|apply H3| | | | | | ]; eauto.
               { split; apply Is_true_eq_true; [eauto|].
                 apply andb_prop_intro.
                 split; apply Is_true_eq_left; [apply Hle|apply Hge].
               }
               iFrame. iNext. iIntros "(HPC & Ha & Hsrc & Ha0 & Hdst) /=".
               iApply wp_pure_step_later; auto.
               iApply wp_value. iNext.
               iIntros (Hcontr); inversion Hcontr.
            }
        (* two successful steps: loading to a fresh dst, and loading to src *)
        destruct (decide (src = dst)); simplify_eq.
        - iApply (wp_load_success_same with "[HPC Hsrc Ha Ha0]");
                 [eauto|eauto|apply Hfp|apply H3| | | | | | ]; eauto.
          { split; apply Is_true_eq_true; [eauto|].
            apply andb_prop_intro.
            split; apply Is_true_eq_left; [apply Hle|apply Hge].
          }
          iFrame. iNext. iIntros "(HPC & Hdst & Ha & Ha0) /=".
          iApply wp_pure_step_later; auto.
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                 [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                 rewrite -delete_insert_ne; auto;
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                 [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
          (* apply IH *)
          (* we will apply the IH on an updated register state *)
          (* we can only prove the following once we have taken a step *)
          iAssert (▷ interp_registers W (<[dst:=if (a0 =? a)%a then w else w0]> r))%I as "#[Hfull' Hreg']".
          { iNext. iSplitR.
            - iIntros (r0).
              iPureIntro.
              destruct (Hsome r0) as [c Hsomec].
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0) "% /=".
              iDestruct ("Hreg" $! (r0)) as "Hv".
              destruct (Hsome r0) as [c Hsomec].
              destruct (decide (dst = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert.
                destruct (a0 =? a)%a;[iApply "Hw"|iApply "Hw0"].
              + rewrite /RegLocate lookup_insert_ne; auto.
                rewrite Hsomec. iApply "Hv"; auto.
          }
          iNext.
          iSpecialize ("Hr" with "Ha0").
          iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto; iFrame "#".
        - destruct (Hsome dst) as [wdst Hsomedst].
          assert (delete PC r !! dst = Some wdst) as Hsomedst'.
          { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
          assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
          { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
            eauto. }
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
            eauto.
          iApply (wp_load_success with "[HPC Hsrc Hdst Ha Ha0]");
                 [eauto|apply Hfp|apply H3| | | | | | ]; eauto.
          { split; apply Is_true_eq_true; [eauto|].
            apply andb_prop_intro.
            split; apply Is_true_eq_left; [apply Hle|apply Hge].
          }
          destruct (a0 =? a)%a; iFrame.
          iNext. iIntros "(HPC & Hdst & Ha & Hsrc & Ha0) /=".
          iApply wp_pure_step_later; auto.
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete|].
          rewrite -delete_insert_ne; auto. iFrame.
          (* apply IH *)
          (* we will apply the IH on an updated register state *)
          (* we can only prove the following once we have taken a step *)
          iAssert (▷ interp_registers _ (<[src:=inr (p0, l, a2, a1, a0)]>
                                         (<[dst:=if (a0 =? a)%a then w else w0]> r)))%I
                    as "#[Hfull' Hreg']".
          { iNext. iSplitR.
            - iIntros (r0).
              destruct (Hsome r0) as [c Hsomec].
              iPureIntro.
              destruct (decide (src = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0) "%".
              destruct (Hsome r0) as [c Hsomec].
              iDestruct ("Hreg" $! (r0)) as "Hv".
              destruct (decide (src = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert.
                iApply "Hvsrc".
              + rewrite /RegLocate lookup_insert_ne; auto.
                rewrite Hsomec. destruct (decide (dst = r0)); simplify_eq.
                * rewrite lookup_insert. destruct (a0 =? a)%a; auto.
                * rewrite lookup_insert_ne. rewrite Hsomec. iApply "Hv"; auto.
                  auto.
          }
          iNext.
          iSpecialize ("Hr" with "Ha0").
          iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto; iFrame "#".
      }
      destruct (decide (a = a0)).
      { iApply "Hstep". iFrame "Hsts".
        iExists w,p0.
        destruct (a0 =? a)%a eqn:Ha0; [|apply Z.eqb_neq in Ha0;congruence].
        iFrame "#". iSplitL.
        - iIntros "_". iFrame.
        - iPureIntro. apply PermFlows_refl.
      }
      iDestruct "Hconds" as (p'' Hp'') "Hinv0".
      iDestruct (region_open_prepare with "Hr") as "Hr".
      iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as "%"; eauto.
      { rewrite /withinBounds /leb_addr Hle Hge. auto. }
      destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
      rewrite /read_write_cond.
      iDestruct (region_open_next _ _ _ a0 p'' ρ' with "[$Hinv0 $Hr $Hsts]") as (w0) "(Hsts & Hstate' & Hr & Ha0 & % & Hmono' & #Hw0)"; eauto.
      { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
      iApply "Hstep". iFrame.
      iExists w0,p''.
      destruct (a0 =? a)%a eqn:Ha0; [apply Z.eqb_eq,z_of_eq in Ha0;congruence|].
      iFrame "∗ #".
      iSplitL; auto. iNext.
      iIntros "Ha0".
      iDestruct (region_close_next with "[$Hr $Ha0 $Hinv0 $Hstate' $Hmono']") as "Hr"; eauto.
      { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
      iDestruct (region_open_prepare with "Hr") as "$".
      Unshelve. exact 0.
  Qed.

End fundamental.
