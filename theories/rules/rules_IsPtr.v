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

  Inductive IsPtr_spec (lregs: LReg) (dst src: RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | IsPtr_spec_success (lw: LWord):
      lregs !! src = Some lw →
      incrementLPC (<[ dst := LInt (if is_log_cap lw then 1%Z else 0%Z) ]> lregs) = Some lregs' ->
      IsPtr_spec lregs dst src lregs' NextIV
  | IsPtr_spec_failure (lw: LWord):
      lregs !! src = Some lw →
      incrementLPC (<[ dst := LInt (if is_log_cap lw then 1%Z else 0%Z) ]> lregs) = None ->
      IsPtr_spec lregs dst src lregs' FailedV.

  Lemma wp_IsPtr Ep pc_p pc_b pc_e pc_a pc_v pca_v lw dst src lregs :
    decodeInstrWL lw = IsPtr dst src ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (IsPtr dst src) ⊆ dom lregs →

    {{{ ▷ (pc_a, pca_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ IsPtr_spec lregs dst src lregs' retv ⌝ ∗
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
  (*   rewrite /exec in Hstep. *)

  (*   specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri. *)
  (*   destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+. *)
  (*   destruct (Hri src) as [wsrc [H'src Hsrc]]. by set_solver+. *)

  (*   assert (exec_opt (IsPtr dst src) *)
  (*                    {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |} = *)
  (*             updatePC (update_reg {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |} *)
  (*                         dst (WInt (if is_cap wsrc then 1%Z else 0%Z)))) as HH. *)
  (*   {  rewrite /= Hsrc. unfold is_cap; destruct_word wsrc; auto. } *)
  (*   rewrite HH in Hstep. rewrite /update_reg /= in Hstep. *)

  (*   destruct (incrementPC (<[ dst := WInt (if is_cap wsrc then 1%Z else 0%Z) ]> regs)) *)
  (*     as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1. *)
  (*   { eapply incrementPC_fail_updatePC with (m:=mem) in Hregs'. *)
  (*     eapply updatePC_fail_incl with (m':=mem) in Hregs'. *)
  (*     2: by apply lookup_insert_is_Some'; eauto. *)
  (*     2: by apply insert_mono; eauto. *)
  (*     simplify_pair_eq. *)
  (*     rewrite Hregs' in Hstep. inversion Hstep. *)
  (*     iFrame. iApply "Hφ"; iFrame. iPureIntro. econstructor; eauto. } *)

  (*   (* Success *) *)

  (*   eapply (incrementPC_success_updatePC _ mem) in Hregs' *)
  (*     as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->). *)
  (*   eapply updatePC_success_incl with (m':=mem) in HuPC. *)
  (*   2: by eapply insert_mono; eauto. rewrite HuPC in Hstep. *)

  (*   simplify_pair_eq. iFrame. *)
  (*   iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*   iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*   iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto. *)
  (*   Unshelve. all: auto. *)
  (* Qed. *)
   Admitted.

  Lemma wp_IsPtr_successPC E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst lw' :
    decodeInstrWL lw = IsPtr dst PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pca_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ lw'
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pca_v) ↦ₐ lw
          ∗ dst ↦ᵣ LInt 1%Z }}}.
   Proof.
   (*   iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ". *)
   (*   iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
   (*   iApply (wp_IsPtr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
   (*   by rewrite !dom_insert; set_solver+. *)
   (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

   (*   destruct Hspec as [|]. *)
   (*   { iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
   (*     rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert. *)
   (*     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
   (*   { incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
   (* Qed. *)
   Admitted.

   Lemma wp_IsPtr_success E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst r lwr lw' :
     decodeInstrWL lw = IsPtr dst r →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →

       {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
             ∗ ▷ (pc_a, pca_v) ↦ₐ lw
             ∗ ▷ r ↦ᵣ lwr
             ∗ ▷ dst ↦ᵣ lw'
       }}}
         Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
           ∗ (pc_a, pca_v) ↦ₐ lw
           ∗ r ↦ᵣ lwr
           ∗ dst ↦ᵣ LInt (if is_log_cap lwr then 1%Z else 0%Z) }}}.
   Proof.
   (*  iIntros (Hinstr Hvpc Hpc_a ϕ) "(>HPC & >Hpc_a & >Hr & >Hdst) Hφ". *)
   (*  iDestruct (map_of_regs_3 with "HPC Hr Hdst") as "[Hmap (%&%&%)]". *)
   (*  iApply (wp_IsPtr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
   (*  by rewrite !dom_insert; set_solver+. *)
   (*  iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

   (*  destruct Hspec as [|]. *)
   (*  { (* Success *) *)
   (*    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
   (*    rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r dst) // *)
   (*            (insert_commute _ dst PC) // insert_insert. *)
   (*    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. } *)
   (*  { (* Failure (contradiction) *) *)
   (*    incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
   (* Qed. *)
   Admitted.

   Lemma wp_IsPtr_success_dst E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst lw' :
     decodeInstrWL lw = IsPtr dst dst →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     
       {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
             ∗ ▷ (pc_a, pca_v) ↦ₐ lw
             ∗ ▷ dst ↦ᵣ lw'
       }}}
         Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
           ∗ (pc_a, pca_v) ↦ₐ lw
           ∗ dst ↦ᵣ LInt (if is_log_cap lw' then 1%Z else 0%Z) }}}.
   Proof.
   (*   iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ". *)
   (*   iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
   (*   iApply (wp_IsPtr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
   (*   by rewrite !dom_insert; set_solver+. *)
   (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

   (*   destruct Hspec as [|]. *)
   (*   { iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq. *)
   (*     rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert. *)
   (*     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
   (*   { incrementPC_inv; simplify_map_eq; eauto. congruence. } *)
   (* Qed. *)
   Admitted.

End cap_lang_rules.
