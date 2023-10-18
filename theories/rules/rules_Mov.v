From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
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

  Inductive Mov_spec (lregs: LReg) (dst: RegName) (src: Z + RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | Mov_spec_success lw:
      word_of_argumentL lregs src = Some lw →
      incrementLPC (<[ dst := lw ]> lregs) = Some lregs' →
      Mov_spec lregs dst src lregs' NextIV
  | Mov_spec_failure lw:
      word_of_argumentL lregs src = Some lw →
      incrementLPC (<[ dst := lw ]> lregs) = None →
      Mov_spec lregs dst src lregs' FailedV.

  Lemma wp_Mov Ep pc_p pc_b pc_e pc_a pc_v pca_v lw dst src lregs :
    decodeInstrWL lw = Mov dst src ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Mov dst src) ⊆ dom lregs →
    {{{ ▷ (pc_a, pca_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ Mov_spec lregs dst src lregs' retv ⌝ ∗
        (pc_a, pca_v) ↦ₐ lw ∗
        [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ". *)
  (*   iApply wp_lift_atomic_head_step_no_fork; auto. *)
  (*   iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl. *)
  (*   iDestruct "Hσ1" as "[Hr Hm]". *)
  (*   iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs. *)
  (*   have ? := lookup_weaken _ _ _ _ HPC Hregs. *)
  (*   iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto. *)
  (*   iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
  (*   iNext. iIntros (e2 σ2 efs Hpstep). *)
  (*   apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)). *)
  (*   iIntros "_". *)
  (*   iSplitR; auto. eapply step_exec_inv in Hstep; eauto. *)
  (*   unfold exec in Hstep. *)

  (*   specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri. *)
  (*   destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+. *)

  (*   assert (exists w, word_of_argument regs src = Some w) as [wsrc Hwsrc]. *)
  (*   { destruct src as [| r0]; eauto; cbn. *)
  (*     destruct (Hri r0) as [? [? ?]]. set_solver+. eauto. } *)

  (*   pose proof Hwsrc as Hwsrc'. eapply word_of_argument_Some_inv' in Hwsrc; eauto. *)

  (*   assert (exec_opt (Mov dst src) *)
  (*                    {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |} *)
  (*           = updatePC (update_reg {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |} dst wsrc)) *)
  (*     as HH. *)
  (*   { destruct Hwsrc as [ [? [? ?] ] | [? (? & ? & Hr') ] ]; simplify_eq; eauto. *)
  (*     cbn. by rewrite /= Hr'. } *)
  (*   rewrite HH in Hstep. rewrite /update_reg /= in Hstep. *)

  (*   destruct (incrementPC (<[ dst := wsrc ]> regs)) as [regs'|] eqn:Hregs'; *)
  (*     pose proof Hregs' as H'regs'; cycle 1. *)
  (*   { apply incrementPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hregs'. *)
  (*     eapply updatePC_fail_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in Hregs'. *)
  (*     2: by apply lookup_insert_is_Some'; eauto. *)
  (*     2: by apply insert_mono; eauto. *)
  (*     rewrite Hregs' in Hstep. simplify_pair_eq. *)
  (*     iFrame. iApply "Hφ"; iFrame. iPureIntro. econstructor; eauto. } *)

  (*   eapply (incrementPC_success_updatePC _ mem etable enumcur) in Hregs' *)
  (*     as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->). *)
  (*   eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC. *)
  (*   2: by eapply insert_mono; eauto. *)
  (*   rewrite HuPC in Hstep. simplify_pair_eq. iFrame. *)
  (*   iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*   iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*   iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto. *)
  (* Qed. *)
  Admitted.

  Lemma wp_move_success_z E pc_p pc_b pc_e pc_a pc_a' pc_v pca_v lw r1 lwr1 z :
    decodeInstrWL lw = Mov r1 (inl z) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pca_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lwr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pca_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt z }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]". *)
  (*   iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [|]. *)
  (*   { (* Success *) *)
  (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
  (*     rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert. *)
  (*     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
  (*   { (* Failure (contradiction) *) *)
  (*     incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
  (* Qed. *)
  Admitted.

  Lemma wp_move_success_reg E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw r1 lwr1 rv lwrv :
    decodeInstrWL lw = Mov r1 (inr rv) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pca_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lwr1
        ∗ ▷ rv ↦ᵣ lwrv }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pca_v) ↦ₐ lw
          ∗ r1 ↦ᵣ lwrv
          ∗ rv ↦ᵣ lwrv }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ". *)
  (*   iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]". *)
  (*   iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [|]. *)
  (*   { (* Success *) *)
  (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
  (*     rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ PC r1) // insert_insert. *)
  (*     iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. } *)
  (*   { (* Failure (contradiction) *) *)
  (*     incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
  (* Qed. *)
  Admitted.

  Lemma wp_move_success_reg_same E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw r1 lwr1 :
    decodeInstrWL lw = Mov r1 (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pca_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lwr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pca_v) ↦ₐ lw
          ∗ r1 ↦ᵣ lwr1 }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]". *)
  (*   iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [|]. *)
  (*   { (* Success *) *)
  (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
  (*     rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert. *)
  (*     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
  (*   { (* Failure (contradiction) *) *)
  (*     incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
  (* Qed. *)
  Admitted.

  Lemma wp_move_success_reg_samePC E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw :
    decodeInstrWL lw = Mov PC (inr PC) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pca_v) ↦ₐ lw }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pca_v) ↦ₐ lw }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hφ". *)
  (*   iDestruct (map_of_regs_1 with "HPC") as "Hmap". *)
  (*   iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [|]. *)
  (*   { (* Success *) *)
  (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
  (*     rewrite !insert_insert. *)
  (*     iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. } *)
  (*   { (* Failure (contradiction) *) *)
  (*     incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
  (* Qed. *)
  Admitted.

  Lemma wp_move_success_reg_toPC E pc_p pc_b pc_e pc_a pc_v pca_v lw r1 p b e a v a':
    decodeInstrWL lw = Mov PC (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (a + 1)%a = Some a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pca_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LCap p b e a v }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap p b e a' v
          ∗ (pc_a, pca_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LCap p b e a v }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]". *)
  (*   iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [|]. *)
  (*   { (* Success *) *)
  (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
  (*     rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert. *)
  (*     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
  (*   { (* Failure (contradiction) *) *)
  (*     incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
  (* Qed. *)
  Admitted.

  Lemma wp_move_success_reg_fromPC E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw r1 lwr1 :
    decodeInstrWL lw = Mov r1 (inr PC) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pca_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lwr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pca_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]". *)
  (*   iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [|]. *)
  (*   { (* Success *) *)
  (*     iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
  (*     rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert. *)
  (*     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
  (*   { (* Failure (contradiction) *) *)
  (*     incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
  (* Qed. *)
  Admitted.

End cap_lang_rules.
