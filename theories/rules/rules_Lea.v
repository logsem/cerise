From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{reservedaddresses : ReservedAddresses}.
  Context `{MP: MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Inductive Lea_failure (lregs: LReg) (r1: RegName) (rv: Z + RegName) :=
  | Lea_fail_rv_nonconst :
     z_of_argumentL lregs rv = None ->
     Lea_failure lregs r1 rv
  | Lea_fail_allowed : forall lw,
     lregs !! r1 = Some lw ->
     is_mutable_rangeL lw = false →
     Lea_failure lregs r1 rv
  | Lea_fail_overflow_cap : forall p b e a v z,
     lregs !! r1 = Some (LCap p b e a v) ->
     z_of_argumentL lregs rv = Some z ->
     (a + z)%a = None ->
     Lea_failure lregs r1 rv
  | Lea_fail_overflow_PC_cap : forall p b e a v z a',
     lregs !! r1 = Some (LCap p b e a v) ->
     z_of_argumentL lregs rv = Some z ->
     (a + z)%a = Some a' ->
     incrementLPC (<[ r1 := LCap p b e a' v ]> lregs) = None ->
     Lea_failure lregs r1 rv
  | Lea_fail_overflow_sr : forall p (b e a : OType) z,
     lregs !! r1 = Some (LSealRange p b e a) ->
     z_of_argumentL lregs rv = Some z ->
     (a + z)%ot = None ->
     Lea_failure lregs r1 rv
  | Lea_fail_overflow_PC_sr : forall p (b e a : OType) z (a' : OType),
     lregs !! r1 = Some (LSealRange p b e a) ->
     z_of_argumentL lregs rv = Some z ->
     (a + z)%ot = Some a' ->
     incrementLPC (<[ r1 := LSealRange p b e a' ]> lregs) = None ->
     Lea_failure lregs r1 rv
  .

  Inductive Lea_spec
    (lregs: LReg) (r1: RegName) (rv: Z + RegName)
    (lregs': LReg) : cap_lang.val → Prop
  :=
  | Lea_spec_success_cap: forall p b e a z a' v,
    lregs !! r1 = Some (LCap p b e a v) ->
    p ≠ E ->
    z_of_argumentL lregs rv = Some z ->
    (a + z)%a = Some a' ->
    incrementLPC
      (<[ r1 := LCap p b e a' v ]> lregs) = Some lregs' ->
    Lea_spec lregs r1 rv lregs' NextIV
  | Lea_spec_success_sr: forall p (b e a : OType) z (a' : OType),
    lregs !! r1 = Some (LSealRange p b e a) ->
    z_of_argumentL lregs rv = Some z ->
    (a + z)%ot = Some a' ->
    incrementLPC
      (<[ r1 := LSealRange p b e a' ]> lregs) = Some lregs' ->
    Lea_spec lregs r1 rv lregs' NextIV
  | Lea_spec_failure :
    Lea_failure lregs r1 rv ->
    Lea_spec lregs r1 rv lregs' FailedV.

  Definition exec_optL_Lea
    (lregs : LReg) (dst: RegName) (src: Z + RegName) : option LReg :=
    n ← z_of_argumentL lregs src;
    lwdst ← lregs !! dst ;
    match lwdst with
    | LCap p b e a v =>
        match p with
        | E => None
        | _ => match (a + n)%a with
              | Some a' =>
                  lregs' ← incrementLPC (<[dst := (LCap p b e a' v) ]> lregs);
                  Some lregs'
              | None => None
              end
        end
    | LSealRange p b e a =>
        match (a + n)%ot with
        | Some a' =>
                  lregs' ← incrementLPC (<[dst := (LSealRange p b e a' ) ]> lregs);
                  Some lregs'
        | None => None
        end
    | _ => None
    end.

  Lemma wp_lea Ep pc_p pc_b pc_e pc_a pc_v dst lw src (lregs: LReg) :
    decodeInstrWL lw = Lea dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Lea dst src) ⊆ dom lregs →
    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' retv, RET retv;
          ⌜ Lea_spec lregs dst src lregs' retv ⌝ ∗
          (pc_a, pc_v) ↦ₐ lw ∗
          [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
     iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
     cbn in Dregs.
     iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpc_a $Hmap Hφ]").
     iModIntro.
     iIntros (σ1) "(Hσ1 & Hmap &Hpc_a)".
     iModIntro.
     iIntros (wa) "(%Hrpc & %Hmema & %Hcorrpc & %Hdecode) Hcred".

     iApply (wp_wp2 (φ1 := exec_optL_Lea lregs dst src)).

     iDestruct (state_interp_transient_intro (lm:= ∅) with "[$Hmap $Hσ1]") as "Hσ".
     { by rewrite big_sepM_empty. }

     iApply wp_opt2_bind.
     iApply wp_opt2_eqn_both.
     iApply (wp2_z_of_argument with "[Hφ Hpc_a Hcred $Hσ]"); first set_solver.
     iSplit.
     { iIntros "Hσ %Heqn1 %Heqn2".
       iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
       iApply ("Hφ" with "[$Hpc_a $Hregs]").
       iPureIntro.
       eapply Lea_spec_failure.
       by constructor.
     }
     iIntros ( z ) "Hσ %HsrcL %Hsrc".

     iApply wp_opt2_bind.
     iApply wp_opt2_eqn_both.
     iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
     iIntros (lwdst) "Hσ %HdstL %Hdst".

     destruct (decide (is_mutable_rangeL lwdst = true)) as [HmutRange|HmutRange]
     ; cycle 1.
     (* case LInt or LSealed : fail *)
     {
       rewrite not_true_iff_false in HmutRange.
       destruct_lword lwdst ; [ |  destruct p | | |] ; cbn in * ; simplify_eq.
       all: iModIntro.
       all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
       all: iApply ("Hφ" with "[$Hpc_a $Hregs]").
       all: iPureIntro; econstructor; by eapply Lea_fail_allowed.
     }

     destruct_lword lwdst ; cbn in * ; simplify_eq.
     - (* case LCap *)
       destruct (decide (p = E)) as [HpE|HnpE]; subst; first done.
       rewrite !rewrite_invert_match_E //=.
       destruct (a + z)%a eqn:Ha ; cycle 1.
       {
         destruct p ; cbn in * ; simplify_eq.
         all: iModIntro.
         all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
         all: iApply ("Hφ" with "[$Hpc_a $Hregs]").
         all: iPureIntro; econstructor; by eapply Lea_fail_overflow_cap.
       }

       iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LCap p b e f v) with "Hσ") as "Hσ".
       { now set_solver. }
       { intros.
         eapply is_cur_lword_lea; eauto; eauto.
         apply isWithin_refl.
       }

      rewrite updatePC_incrementPC.
      iApply (wp_opt2_bind (k1 := fun x => Some x)).
      iApply wp_opt2_eqn_both.
      iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := <[ dst := LCap p b e f v]> lregs)).
      { now rewrite elem_of_dom (lookup_insert_dec HPC). }
      iFrame "Hσ".
      iSplit; cbn.
      + iIntros "Hσ %Hlin %Hin".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; constructor ; by eapply Lea_fail_overflow_PC_cap.
      + iIntros (lrt' rs') "Hσ %Hlis %His".
        cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro.
        by eapply Lea_spec_success_cap.

    - (* case LSealable *)
      destruct (a + z)%f eqn:Ha ; cycle 1.
      {
        destruct p ; cbn in * ; simplify_eq.
        all: iModIntro.
        all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        all: iApply ("Hφ" with "[$Hpc_a $Hregs]").
        all: iPureIntro; econstructor; by eapply Lea_fail_overflow_sr.
      }

      iDestruct (update_state_interp_transient_from_regs_mod (dst := dst)
                   (lw2 := LSealRange p b e f) with "Hσ") as "Hσ".
      { now set_solver. }
      { by intros; cbn. }

      rewrite updatePC_incrementPC.
      iApply (wp_opt2_bind (k1 := fun x => Some x)).
      iApply wp_opt2_eqn_both.
      iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := <[ dst := LSealRange p b e f]> lregs)).
      { now rewrite elem_of_dom (lookup_insert_dec HPC). }
      iFrame "Hσ".
      iSplit; cbn.
      + iIntros "Hσ %Hlin %Hin".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; constructor ; by eapply Lea_fail_overflow_PC_sr.
      + iIntros (lrt' rs') "Hσ %Hlis %His".
        cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro.
        by eapply Lea_spec_success_sr.
  Qed.

  Lemma wp_lea_success_reg_PC Ep pc_p pc_b pc_e pc_a pc_v pc_a' lw rv z a' :
    decodeInstrWL lw = Lea PC (inr rv) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (a' + 1)%a = Some pc_a' →
    (pc_a + z)%a = Some a' →
    pc_p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lw
              ∗ rv ↦ᵣ LInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep φ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       rewrite !insert_insert. (* TODO: add to simplify_map_eq via simpl_map? *)
       iApply (regs_of_map_2 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct pc_p; congruence.
       congruence.
     }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_success_reg Ep pc_p pc_b pc_e pc_a pc_a' pc_v lw r1 rv p b e a v z a' :
     decodeInstrWL lw = Lea r1 (inr rv) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LCap p b e a v
           ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lw
              ∗ rv ↦ᵣ LInt z
              ∗ r1 ↦ᵣ LCap p b e a' v}}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite (insert_commute _ PC r1) // insert_insert.
       rewrite (insert_commute _ r1 PC) // (insert_commute _ r1 rv) // insert_insert.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct p; congruence.
       congruence.
     }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_success_z_PC Ep pc_p pc_b pc_e pc_a pc_a' pc_v lw z a' :
     decodeInstrWL lw = Lea PC (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     pc_p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
            ∗ (pc_a, pc_v) ↦ₐ lw }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       rewrite !insert_insert. iApply (regs_of_map_1 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct pc_p; congruence.
       congruence.
     }
     Unshelve. all: auto.
   Qed.

   Lemma wp_lea_success_z Ep pc_p pc_b pc_e pc_a pc_a' pc_v lw r1 p b e a v z a' :
     decodeInstrWL lw = Lea r1 (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LCap p b e a v }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
            ∗ (pc_a, pc_v) ↦ₐ lw
            ∗ r1 ↦ᵣ LCap p b e a' v }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite insert_commute // insert_insert insert_commute // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct p; congruence.
       congruence.
     }
     Unshelve. all:auto.
   Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

   Lemma wp_lea_success_reg_sr Ep pc_p pc_b pc_e pc_a pc_a' pc_v lw r1 rv p (b e a : OType) z (a': OType) :
     decodeInstrWL lw = Lea r1 (inr rv) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LSealRange p b e a
           ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lw
              ∗ rv ↦ᵣ LInt z
              ∗ r1 ↦ᵣ LSealRange p b e a' }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | * Hfail ].
     { (* Success with WSealCap (contradiction) *)
       simplify_map_eq. }
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite (insert_commute _ PC r1) // insert_insert.
       rewrite (insert_commute _ r1 PC) // (insert_commute _ r1 rv) // insert_insert.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       congruence.
     }
    Unshelve. all: auto.
   Qed.

  Lemma wp_lea_success_z_sr Ep pc_p pc_b pc_e pc_a pc_a' pc_v lw r1 p (b e a : OType) z (a': OType) :
     decodeInstrWL lw = Lea r1 (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LSealRange p b e a }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
            ∗ (pc_a, pc_v) ↦ₐ lw
            ∗ r1 ↦ᵣ LSealRange p b e a' }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | * Hfail ].
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Success *)
       iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite insert_commute // insert_insert insert_commute // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       congruence.
     }
     Unshelve. all:auto.
   Qed.

   Lemma wp_Lea_fail_none Ep pc_p pc_b pc_e pc_a pc_v lw r1 rv p b e a v z :
     decodeInstrWL lw = Lea r1 (inr rv) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (a + z)%a = None ->

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LCap p b e a v
           ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     iIntros (Hdecode Hvpc Hz φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [* Hsucc | * Hsucc |].
     { (* Success (contradiction) *) simplify_map_eq. }
     { (* Success (contradiction) *) simplify_map_eq. }
     { (* Failure, done *) by iApply "Hφ". }
   Qed.

End cap_lang_rules.
