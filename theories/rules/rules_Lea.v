From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{HM: memG Σ, HR: regG Σ}.
  Context `{MachineParameters}.
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

   Lemma wp_lea Ep pc_p pc_b pc_e pc_a pc_v pca_v r1 lw arg (lregs: LReg) :
     decodeInstrWL lw = Lea r1 arg →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
     regs_of (Lea r1 arg) ⊆ dom lregs →
     {{{ ▷ (pc_a, pca_v) ↦ₐ lw ∗
         ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
       Instr Executable @ Ep
     {{{ lregs' retv, RET retv;
         ⌜ Lea_spec lregs r1 arg lregs' retv ⌝ ∗
         (pc_a, pca_v) ↦ₐ lw ∗
         [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
   Proof.
   (*   iIntros (Hinstr Hvpc HPC Dlregs φ) "(>Hpc_a & >Hmap) Hφ". *)
   (*   iApply wp_lift_atomic_head_step_no_fork; auto. *)
   (*   iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl. *)
   (*   iDestruct "Hσ1" as "[Hr Hm]". *)
   (*   iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hlregs. *)
   (*   pose proof (lookup_weaken _ _ _ _ HPC Hlregs). *)
   (*   iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto. *)
   (*   iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
   (*   iNext. iIntros (e2 σ2 efs Hpstep). *)
   (*   apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)). *)
   (*   iIntros "_". *)
   (*   iSplitR; auto. eapply step_exec_inv in Hstep; eauto. *)
   (*   unfold exec in Hstep; simpl in Hstep. *)

   (*   specialize (indom_lregs_incl _ _ _ Dlregs Hlregs) as Hri. unfold lregs_of in Hri. *)

   (*   feed destruct (Hri r1) as [r1v [Hr'1 Hr1]]. by set_solver+. *)
   (*   rewrite Hr1 /= in Hstep. *)

   (*   destruct (z_of_argument lregs arg) as [ argz |] eqn:Harg; *)
   (*     pose proof Harg as Harg'; cycle 1. *)
   (*   { (* Failure: argument is not a constant (z_of_argument lregs arg = None) *) *)
   (*     unfold z_of_argument in Harg, Hstep. destruct arg as [| r0]; [ congruence |]. *)
   (*     feed destruct (Hri r0) as [r0v [Hr'0 Hr0]]. *)
   (*     { unfold lregs_of_argument. set_solver+. } *)
   (*     rewrite Hr0 Hr'0 in Harg Hstep. *)
   (*     assert (c = Failed ∧ *)
   (*               σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) *)
   (*       as (-> & ->). *)
   (*     { destruct_word r0v; cbn in Hstep; try congruence; by simplify_pair_eq. } *)
   (*     iFailWP "Hφ" Lea_fail_rv_nonconst. } *)
   (*   apply (z_of_arg_mono _ reg) in Harg; auto. rewrite Harg in Hstep; cbn in Hstep. *)

   (*   destruct (is_mutable_range r1v) eqn:Hr1v. *)
   (*   2: { (* Failure: r1v is not of the right type *) *)
   (*     unfold is_mutable_range in Hr1v. *)
   (*     assert (c = Failed ∧ *)
   (*               σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) *)
   (*       as (-> & ->). *)
   (*     { destruct r1v as [ | [p b e a | ] | ]; try by inversion Hr1v. *)
   (*       all: try by simplify_pair_eq. *)
   (*       destruct p; try congruence. *)
   (*       simplify_pair_eq; auto. } *)
   (*     iFailWP "Hφ" Lea_fail_allowed. } *)

   (*   (* Now the proof splits depending on the type of value in r1v *) *)
   (*   destruct r1v as [ | [p b e a | p b e a] | ]. *)
   (*   1,4: inversion Hr1v. *)

   (*   (* First, the case where r1v is a capability *) *)
   (*   + destruct (perm_eq_dec p E); [ subst p |]. *)
   (*     { rewrite /is_mutable_range in Hr1v; congruence. } *)

   (*     destruct (a + argz)%a as [ a' |] eqn:Hoffset; cycle 1. *)
   (*     { (* Failure: offset is too large *) *)
   (*       assert (c = Failed ∧ *)
   (*                 σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) *)
   (*         as (-> & ->) *)
   (*           by (destruct p; inversion Hstep; auto). *)
   (*       iFailWP "Hφ" Lea_fail_overflow_cap. } *)

   (*     rewrite /update_reg /= in Hstep. *)
   (*     destruct (incrementPC (<[ r1 := WCap p b e a' ]> lregs)) as [ lregs' |] eqn:Hlregs'; *)
   (*       pose proof Hlregs' as Hlregs'2; cycle 1. *)
   (*     { (* Failure: incrementing PC overflows *) *)
   (*       assert (incrementPC (<[ r1 := WCap p b e a' ]> reg) = None) as HH. *)
   (*       { eapply incrementPC_overflow_mono; first eapply Hlregs'. *)
   (*           by rewrite lookup_insert_is_Some'; eauto. *)
   (*             by apply insert_mono; eauto. } *)
   (*       apply (incrementPC_fail_updatePC _ mem etable enumcur) in HH. rewrite HH in Hstep. *)
   (*       assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->) *)
   (*           by (destruct p; inversion Hstep; auto). *)
   (*       iFailWP "Hφ" Lea_fail_overflow_PC_cap. } *)

   (*     (* Success *) *)
   (*     eapply (incrementPC_success_updatePC _ mem) in Hlregs' *)
   (*       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->). *)
   (*     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto. *)
   (*     rewrite HuPC in Hstep; clear HuPC. *)
   (*     eassert ((c, σ2) = (NextI, _)) as HH. *)
   (*     { destruct p; cbn in Hstep; eauto. congruence. } *)
   (*     simplify_pair_eq. *)

   (*     iFrame. *)
   (*     iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
   (*     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
   (*     iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. *)
   (*     eapply Lea_spec_success_cap; eauto. *)
   (*  (* Now, the case where r1v is a sealrange *) *)
   (*   + destruct (a + argz)%ot as [ a' |] eqn:Hoffset; cycle 1. *)
   (*     { (* Failure: offset is too large *) *)
   (*       assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->) *)
   (*           by (destruct p; inversion Hstep; auto). *)
   (*       iFailWP "Hφ" Lea_fail_overflow_sr. } *)

   (*     rewrite /update_reg /= in Hstep. *)
   (*     destruct (incrementPC (<[ r1 := WSealRange p b e a' ]> lregs)) as [ lregs' |] eqn:Hlregs'; *)
   (*       pose proof Hlregs' as Hlregs'2; cycle 1. *)
   (*     { (* Failure: incrementing PC overflows *) *)
   (*       assert (incrementPC (<[ r1 := WSealRange p b e a' ]> reg) = None) as HH. *)
   (*       { eapply incrementPC_overflow_mono; first eapply Hlregs'. *)
   (*           by rewrite lookup_insert_is_Some'; eauto. *)
   (*             by apply insert_mono; eauto. } *)
   (*       eapply (incrementPC_fail_updatePC _ mem) in HH. rewrite HH in Hstep. *)
   (*       assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->) *)
   (*           by (destruct p; inversion Hstep; auto). *)
   (*       iFailWP "Hφ" Lea_fail_overflow_PC_sr. } *)

   (*     (* Success *) *)
   (*     eapply (incrementPC_success_updatePC _ mem) in Hlregs' *)
   (*       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->). *)
   (*     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto. *)
   (*     rewrite HuPC in Hstep; clear HuPC. *)
   (*     eassert ((c, σ2) = (NextI, _)) as HH. *)
   (*     { destruct p; cbn in Hstep; eauto. } *)
   (*     simplify_pair_eq. *)

   (*     iFrame. *)
   (*     iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
   (*     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
   (*     iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. *)
   (*     eapply Lea_spec_success_sr; eauto. *)
   (* Unshelve. all: auto. *)
   (* Qed. *)
   Admitted.

   Lemma wp_lea_success_reg_PC Ep pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw rv z a' :
     decodeInstrWL lw = Lea PC (inr rv) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     pc_p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lw
              ∗ rv ↦ᵣ LInt z }}}.
   Proof.
   (*   iIntros (Hinstr Hvpc Hpca' Ha' Hnep φ) "(>HPC & >Hpc_a & >Hrv) Hφ". *)
   (*   iDestruct (map_of_lregs_2 with "HPC Hrv") as "[Hmap %]". *)
   (*   iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
   (*   by rewrite !dom_insert; set_solver+. *)
   (*   iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)". *)
   (*   iDestruct "Hspec" as %Hspec. *)

   (*   destruct Hspec as [ | | * Hfail ]. *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
   (*     rewrite !insert_insert. (* TODO: add to simplify_map_eq via simpl_map? *) *)
   (*     iApply (lregs_of_map_2 with "Hmap"); eauto. } *)
   (*   { (* Success with WSealRange (contradiction) *) *)
   (*     simplify_map_eq. } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
   (*     destruct pc_p; congruence. *)
   (*     congruence. *)
   (*   } *)
   (*  Unshelve. all: auto. *)
   (* Qed. *)
   Admitted.

   Lemma wp_lea_success_reg Ep pc_p pc_b pc_e pc_a pc_a' pc_v pca_v lw r1 rv p b e a v z a' :
     decodeInstrWL lw = Lea r1 (inr rv) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →
     
     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LCap p b e a v
           ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lw
              ∗ rv ↦ᵣ LInt z
              ∗ r1 ↦ᵣ LCap p b e a' v}}}.
   Proof.
   (*   iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ". *)
   (*   iDestruct (map_of_lregs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]". *)
   (*   iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
   (*   by rewrite !dom_insert; set_solver+. *)
   (*   iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)". *)
   (*   iDestruct "Hspec" as %Hspec. *)

   (*   destruct Hspec as [ | | * Hfail ]. *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
   (*     (* FIXME: tedious *) *)
   (*     rewrite (insert_commute _ PC r1) // insert_insert. *)
   (*     rewrite (insert_commute _ r1 PC) // (insert_commute _ r1 rv) // insert_insert. *)
   (*     iApply (lregs_of_map_3 with "Hmap"); eauto. } *)
   (*   { (* Success with WSealRange (contradiction) *) *)
   (*     simplify_map_eq. } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
   (*     destruct p; congruence. *)
   (*     congruence. *)
   (*   } *)
   (*  Unshelve. all: auto. *)
   (* Qed. *)
   Admitted.

   Lemma wp_lea_success_z_PC Ep pc_p pc_b pc_e pc_a pc_a' pc_v pca_v lw z a' :
     decodeInstrWL lw = Lea PC (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     pc_p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
            ∗ (pc_a, pca_v) ↦ₐ lw }}}.
   Proof.
     (* iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a) Hφ". *)
     (* iDestruct (map_of_lregs_1 with "HPC") as "Hmap". *)
     (* iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
     (* by rewrite !dom_insert; set_solver+. *)
     (* iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)". *)
     (* iDestruct "Hspec" as %Hspec. *)

     (* destruct Hspec as [ | | * Hfail ]. *)
     (* { (* Success *) *)
     (*   iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
     (*   rewrite !insert_insert. iApply (lregs_of_map_1 with "Hmap"); eauto. } *)
     (* { (* Success with WSealRange (contradiction) *) *)
     (*   simplify_map_eq. } *)
     (* { (* Failure (contradiction) *) *)
     (*   destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
     (*   destruct pc_p; congruence. *)
     (*   congruence. *)
     (* } *)
     (* Unshelve. all: auto. *)
   (* Qed. *)
   Admitted.

   Lemma wp_lea_success_z Ep pc_p pc_b pc_e pc_a pc_a' pc_v pca_v lw r1 p b e a v z a' :
     decodeInstrWL lw = Lea r1 (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LCap p b e a v }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
            ∗ (pc_a, pca_v) ↦ₐ lw
            ∗ r1 ↦ᵣ LCap p b e a' v }}}.
   Proof.
   (*   iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ". *)
   (*   iDestruct (map_of_lregs_2 with "HPC Hr1") as "[Hmap %]". *)
   (*   iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
   (*   by rewrite !dom_insert; set_solver+. *)
   (*   iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)". *)
   (*   iDestruct "Hspec" as %Hspec. *)

   (*   destruct Hspec as [ | | * Hfail ]. *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
   (*     (* FIXME: tedious *) *)
   (*     rewrite insert_commute // insert_insert insert_commute // insert_insert. *)
   (*     iDestruct (lregs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. } *)
   (*   { (* Success with WSealRange (contradiction) *) *)
   (*     simplify_map_eq. } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
   (*     destruct p; congruence. *)
   (*     congruence. *)
   (*   } *)
   (*   Unshelve. all:auto. *)
   (* Qed. *)
   Admitted.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

   Lemma wp_lea_success_reg_sr Ep pc_p pc_b pc_e pc_a pc_a' pc_v pca_v lw r1 rv p (b e a : OType) z (a': OType) :
     decodeInstrWL lw = Lea r1 (inr rv) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LSealRange p b e a
           ∗ ▷ rv ↦ᵣ LInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lw
              ∗ rv ↦ᵣ LInt z
              ∗ r1 ↦ᵣ LSealRange p b e a' }}}.
   Proof.
    (*  iIntros (Hinstr Hvpc Hpca' Ha' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ". *)
    (*  iDestruct (map_of_lregs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]". *)
    (*  iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
    (*  by rewrite !dom_insert; set_solver+. *)
    (*  iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)". *)
    (*  iDestruct "Hspec" as %Hspec. *)

    (*  destruct Hspec as [ | | * Hfail ]. *)
    (*  { (* Success with WSealCap (contradiction) *) *)
    (*    simplify_map_eq. } *)
    (*  { (* Success *) *)
    (*    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
    (*    (* FIXME: tedious *) *)
    (*    rewrite (insert_commute _ PC r1) // insert_insert. *)
    (*    rewrite (insert_commute _ r1 PC) // (insert_commute _ r1 rv) // insert_insert. *)
    (*    iApply (lregs_of_map_3 with "Hmap"); eauto. } *)
    (*  { (* Failure (contradiction) *) *)
    (*    destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
    (*    congruence. *)
    (*  } *)
    (* Unshelve. all: auto. *)
   (* Qed. *)
   Admitted.

  Lemma wp_lea_success_z_sr Ep pc_p pc_b pc_e pc_a pc_a' pc_v pca_v lw r1 p (b e a : OType) z (a': OType) :
     decodeInstrWL lw = Lea r1 (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ r1 ↦ᵣ LSealRange p b e a }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
            ∗ (pc_a, pca_v) ↦ₐ lw
            ∗ r1 ↦ᵣ LSealRange p b e a' }}}.
   Proof.
   (*   iIntros (Hinstr Hvpc Hpca' Ha' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ". *)
   (*   iDestruct (map_of_lregs_2 with "HPC Hr1") as "[Hmap %]". *)
   (*   iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
   (*   by rewrite !dom_insert; set_solver+. *)
   (*   iNext. iIntros (lregs' retv) "(#Hspec & Hpc_a & Hmap)". *)
   (*   iDestruct "Hspec" as %Hspec. *)

   (*   destruct Hspec as [ | | * Hfail ]. *)
   (*   { (* Success with WSealRange (contradiction) *) *)
   (*     simplify_map_eq. } *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
   (*     (* FIXME: tedious *) *)
   (*     rewrite insert_commute // insert_insert insert_commute // insert_insert. *)
   (*     iDestruct (lregs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
   (*     congruence. *)
   (*   } *)
   (*   Unshelve. all:auto. *)
   (* Qed. *)
   Admitted.

End cap_lang_rules.
