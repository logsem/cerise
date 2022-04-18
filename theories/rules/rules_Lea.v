From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
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
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap (CoreN * RegName) Word.
  Implicit Types ms : gmap Addr Word.

  Inductive Lea_failure (i: CoreN) (regs: Reg) (r1: RegName) (rv: Z + RegName) :=
  | Lea_fail_rv_nonconst :
     z_of_argument regs i rv = None ->
     Lea_failure i regs r1 rv
  | Lea_fail_p_E : forall p b e a,
     regs !! (i, r1) = Some (WCap p b e a) ->
     p = E ->
     Lea_failure i regs r1 rv
  | Lea_fail_r1_noncap : forall n,
     regs !! (i, r1) = Some (WInt n) ->
     Lea_failure i regs r1 rv
  | Lea_fail_overflow : forall p b e a z,
     regs !! (i, r1) = Some (WCap p b e a) ->
     z_of_argument regs i rv = Some z ->
     (a + z)%a = None ->
     Lea_failure i regs r1 rv
  | Lea_fail_overflow_PC : forall p b e a z a',
     regs !! (i, r1) = Some (WCap p b e a) ->
     z_of_argument regs i rv = Some z ->
     (a + z)%a = Some a' ->
     incrementPC (<[ (i, r1) := WCap p b e a' ]> regs) i = None ->
     Lea_failure i regs r1 rv
   .

  Inductive Lea_spec
    (i : CoreN)
    (regs: Reg) (r1: RegName) (rv: Z + RegName)
    (regs': Reg) : cap_lang.val → Prop
  :=
  | Lea_spec_success : forall p b e a z a',
    regs !! (i, r1) = Some (WCap p b e a) ->
    p ≠ E ->
    z_of_argument regs i rv = Some z ->
    (a + z)%a = Some a' ->
    incrementPC
      (<[ (i, r1) := WCap p b e a' ]> regs) i = Some regs' ->
    Lea_spec i regs r1 rv regs' (i, NextIV)

  | Lea_spec_failure :
    Lea_failure i regs r1 rv ->
    Lea_spec i regs r1 rv regs' (i, FailedV).

   Lemma wp_lea Ep i pc_p pc_b pc_e pc_a r1 w arg (regs: Reg) :
     decodeInstrW w = Lea r1 arg →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
     regs_of_core (Lea r1 arg) i ⊆ dom _ regs →
     {{{ ▷ pc_a ↦ₐ w ∗
         ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
       (i, Instr Executable) @ Ep
     {{{ regs' retv, RET retv;
         ⌜ Lea_spec i regs r1 arg regs' retv ⌝ ∗
         pc_a ↦ₐ w ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
     iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply core_step_exec_inv in Hstep; eauto.
     unfold exec in Hstep; simpl in Hstep.

     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of_core in Hri.

     feed destruct (Hri i r1) as [r1v [Hr'1 Hr1]]. by set_solver+.
     rewrite Hr1 in Hstep.

     destruct (z_of_argument regs i arg) as [ argz |] eqn:Harg;
       pose proof Harg as Harg'; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Harg, Hstep. destruct arg as [| r0]; [ congruence |].
       feed destruct (Hri i r0) as [r0v [Hr'0 Hr0]].
       { unfold regs_of_argument. set_solver+. }
       rewrite Hr0 Hr'0 in Harg Hstep.
       destruct r0v; [ congruence |].
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
         by (destruct p; inversion Hstep; eauto).
       iFailWP "Hφ" Lea_fail_rv_nonconst. }
    apply (z_of_arg_mono _ r) in Harg. rewrite Harg in Hstep; cbn in Hstep.


     destruct r1v as [| p b e a ] eqn:Hr1v.
     { (* Failure: r1 is not a capability *)
       inversion Hstep.
       iFailWP "Hφ" Lea_fail_r1_noncap. }

     destruct (perm_eq_dec p E); [ subst p |].
     { (* Failure: r1.p is Enter *)
       inversion Hstep.
       iFailWP "Hφ" Lea_fail_p_E. }

     destruct (a + argz)%a as [ a' |] eqn:Hoffset; cycle 1.
     { (* Failure: offset is too large *)
         assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" Lea_fail_overflow. }

     rewrite /update_reg /= in Hstep.
     destruct (incrementPC (<[ (i, r1) := WCap p b e a' ]> regs) i) as [ regs' |] eqn:Hregs';
       pose proof Hregs' as Hregs'2; cycle 1.
     { (* Failure: incrementing PC overflows *)
       assert (incrementPC (<[ (i , r1) := WCap p b e a' ]> r) i = None) as HH.
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         by rewrite lookup_insert_is_Some'; eauto.
         by apply insert_mono; eauto. }
       apply (incrementPC_fail_updatePC _ i m) in HH. rewrite HH in Hstep.
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
       iFailWP "Hφ" Lea_fail_overflow_PC. }

     (* Success *)
     eapply (incrementPC_success_updatePC _ i m) in Hregs'
       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
     rewrite HuPC in Hstep; clear HuPC.
     eassert ((c, σ2) = (NextI, _)) as HH.
     { destruct p; cbn in Hstep; eauto. congruence. }
     simplify_pair_eq.

     iFrame.
     iMod ((gen_heap_update_inSepM _ _ (i, r1)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
     eapply Lea_spec_success; eauto.

     Unshelve. all: auto.
   Qed.

   Lemma wp_lea_success_reg_PC Ep i pc_p pc_b pc_e pc_a pc_a' w rv z a' :
     decodeInstrW w = Lea PC (inr rv) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     pc_p ≠ E →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, rv) ↦ᵣ WInt z }}}
       (i, Instr Executable) @ Ep
       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ (i, rv) ↦ᵣ WInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep φ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto
     ; simplify_map_eq by simplify_pair_eq; eauto.
     { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
       ; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       rewrite !insert_insert. (* TODO: add to simplify_map_eq by simplify_pair_eq via simpl_map? *)
       iApply (regs_of_map_2 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence.
     }
   Qed.

   Lemma wp_lea_success_reg Ep i pc_p pc_b pc_e pc_a pc_a' w r1 rv p b e a z a' :
     decodeInstrW w = Lea r1 (inr rv) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →
     
     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, r1) ↦ᵣ WCap p b e a
           ∗ ▷ (i, rv) ↦ᵣ WInt z }}}
       (i, Instr Executable) @ Ep
       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ (i, rv) ↦ᵣ WInt z
              ∗ (i, r1) ↦ᵣ WCap p b e a' }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
       ; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [| * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       (* FIXME: tedious *)
       rewrite (insert_commute _ (i, PC) (i, r1)) ; simplify_pair_eq.
       rewrite insert_insert (insert_commute _ (i, r1) (i, PC)); simplify_pair_eq.
       rewrite (insert_commute _ (i, r1) (i, rv)); simplify_pair_eq.
       rewrite insert_insert.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence.
     }
   Qed.

   Lemma wp_lea_success_z_PC Ep i pc_p pc_b pc_e pc_a pc_a' w z a' :
     decodeInstrW w = Lea PC (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     pc_p ≠ E →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       (i, Instr Executable) @ Ep
     {{{ RET (i, NextIV);
         (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
            ∗ pc_a ↦ₐ w }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       rewrite !insert_insert. iApply (regs_of_map_1 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence.
     }
   Qed.

   Lemma wp_lea_success_z Ep i pc_p pc_b pc_e pc_a pc_a' w r1 p b e a z a' :
     decodeInstrW w = Lea r1 (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     p ≠ E →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, r1) ↦ᵣ WCap p b e a }}}
       (i, Instr Executable) @ Ep
     {{{ RET (i, NextIV);
         (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
            ∗ pc_a ↦ₐ w
            ∗ (i, r1) ↦ᵣ WCap p b e a' }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       (* FIXME: tedious *)
       rewrite (insert_commute _ (i, PC) (i, r1)) ; simplify_pair_eq
       ; rewrite insert_insert.
       rewrite (insert_commute _ (i, r1) (i, PC)) ; simplify_pair_eq
       ; rewrite insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence.
     }
   Qed.

End cap_lang_rules.
