From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{HM: memG Σ, HR: regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive Lea_failure (regs: Reg) (r1: RegName) (rv: Z + RegName) :=
  | Lea_fail_rv_nonconst :
     z_of_argument regs rv = None ->
     Lea_failure regs r1 rv
  | Lea_fail_p_E : forall p g b e a,
     regs !! r1 = Some (inr ((p, g), b, e, a)) ->
     p = E ->
     Lea_failure regs r1 rv
  | Lea_fail_r1_noncap : forall n,
     regs !! r1 = Some (inl n) ->
     Lea_failure regs r1 rv
  | Lea_fail_overflow : forall p g b e a z,
     regs !! r1 = Some (inr ((p, g), b, e, a)) ->
     z_of_argument regs rv = Some z ->
     (a + z)%a = None ->
     Lea_failure regs r1 rv
  | Lea_fail_overflow_PC : forall p g b e a z a',
     regs !! r1 = Some (inr ((p, g), b, e, a)) ->
     z_of_argument regs rv = Some z ->
     (a + z)%a = Some a' ->
     incrementPC (<[ r1 := inr ((p, g), b, e, a') ]> regs) = None ->
     Lea_failure regs r1 rv
  | Lea_fail_overflow_U : forall p g b e a z a',
      regs !! r1 = Some (inr ((p, g), b, e, a)) ->
      z_of_argument regs rv = Some z ->
      (a + z)%a = Some a' ->
      (match p with
       | URW | URWL | URWX | URWLX => not (a' <= a)%a
       | _ => False
       end) ->
      Lea_failure regs r1 rv
   .

  Inductive Lea_spec
    (regs: Reg) (r1: RegName) (rv: Z + RegName)
    (regs': Reg) : cap_lang.val → Prop
  :=
  | Lea_spec_success : forall p g b e a z a',
    regs !! r1 = Some (inr ((p, g), b, e, a)) ->
    p ≠ E ->
    z_of_argument regs rv = Some z ->
    (a + z)%a = Some a' ->
    (match p with
     | URW | URWL | URWX | URWLX => (a' <= a)%a
     | _ => True
     end) ->
    incrementPC
      (<[ r1 := inr ((p, g), b, e, a') ]> regs) = Some regs' ->
    Lea_spec regs r1 rv regs' NextIV

  | Lea_spec_failure :
    Lea_failure regs r1 rv ->
    Lea_spec regs r1 rv regs' FailedV.

   Lemma wp_lea Ep pc_p pc_g pc_b pc_e pc_a pc_p' r1 w arg (regs: Reg) :
     decodeInstrW w = Lea r1 arg →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
     regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
     regs_of (Lea r1 arg) ⊆ dom _ regs →
     {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
         ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
       Instr Executable @ Ep
     {{{ regs' retv, RET retv;
         ⌜ Lea_spec regs r1 arg regs' retv ⌝ ∗
         pc_a ↦ₐ[pc_p'] w ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     assert (pc_p' ≠ O).
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; naive_solver. }
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
     pose proof (regs_lookup_eq _ _ _ HPC) as HPC'.
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %Hpc_a; auto.
     iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.

     feed destruct (Hri r1) as [r1v [Hr'1 Hr1]]. by set_solver+.
     pose proof (regs_lookup_eq _ _ _ Hr1) as Hr1'.
     cbn in Hstep. rewrite Hr1' in Hstep.
     destruct r1v as [| (([[p g] b] & e) & a) ] eqn:Hr1v.
     { (* Failure: r1 is not a capability *)
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
         by (destruct arg; inversion Hstep; auto).
       iFailWP "Hφ" Lea_fail_r1_noncap. }

     destruct (perm_eq_dec p E); [ subst p |].
     { (* Failure: r1.p is Enter *)
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
       { destruct arg; inversion Hstep; subst; eauto. }
       iFailWP "Hφ" Lea_fail_p_E. }

     destruct (z_of_argument regs arg) as [ argz |] eqn:Harg;
       pose proof Harg as Harg'; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Harg. destruct arg as [| r0]; [ congruence |].
       feed destruct (Hri r0) as [r0v [Hr'0 Hr0]].
       { unfold regs_of_argument. set_solver+. }
       rewrite /RegLocate Hr0 Hr'0 in Harg Hstep.
       destruct r0v; [ congruence |].
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
         by (destruct p; inversion Hstep; eauto).
       iFailWP "Hφ" Lea_fail_rv_nonconst. }

     destruct (a + argz)%a as [ a' |] eqn:Hoffset; cycle 1.
     { (* Failure: offset is too large *)
       unfold z_of_argument in Harg. destruct arg as [ z | r0].
       { inversion Harg; subst z. rewrite Hoffset in Hstep.
         assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" Lea_fail_overflow. }
       { feed destruct (Hri r0) as [r0v [Hr'0 Hr0]].
         by unfold regs_of_argument; set_solver+.
         rewrite /RegLocate Hr'0 Hr0 in Harg Hstep.
         destruct r0v; [| congruence]. inversion Harg; subst z.
         rewrite Hoffset in Hstep.
         assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" Lea_fail_overflow. } }

     assert (HU: match p with | URW | URWL | URWX | URWLX => not (a' <= a)%a | _ => False end \/ match p with | URW | URWL | URWX | URWLX => (a' <= a)%a | _ => True end) by (destruct (Addr_le_dec a' a); destruct p; auto).

     destruct HU as [HU | HU].
     { (* Failure: permission is uninitialized and try to increase reading bound *)
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
       { unfold z_of_argument in Harg. destruct arg as [ z | r0 ].
         - inversion Harg; subst z. rewrite Hoffset in Hstep.
           destruct (Addr_le_dec a' a); destruct p; auto; try tauto; try congruence; inv Hstep; auto.
         - destruct (Hri r0) as [r0v [Hr'0 Hr0]].
           by unfold regs_of_argument; set_solver+.
           rewrite /RegLocate Hr'0 Hr0 in Harg Hstep.
           destruct r0v; [| congruence]. inversion Harg; subst z.
           rewrite Hoffset in Hstep.
           destruct (Addr_le_dec a' a); destruct p; auto; try tauto; try congruence; inv Hstep; auto. }
       iFailWP "Hφ" Lea_fail_overflow_U. }

     assert ((c, σ2) = updatePC (update_reg (r, m) r1 (inr (p, g, b, e, a')))) as HH.
     { unfold z_of_argument in Harg. destruct arg as [ z | r0 ].
       { inversion Harg; subst z. rewrite Hoffset in Hstep.
         destruct p; auto; try congruence; destruct (Addr_le_dec a' a); try congruence; auto; solve_addr. }
       { feed destruct (Hri r0) as [r0v [Hr'0 Hr0]].
         by unfold regs_of_argument; set_solver+.
         rewrite /RegLocate Hr'0 Hr0 in Harg Hstep.
         destruct r0v; [| congruence]. inversion Harg; subst z.
         rewrite Hoffset in Hstep.
         destruct p; auto; try congruence; destruct (Addr_le_dec a' a); try congruence; auto; solve_addr. } }
     clear Hstep. rewrite /update_reg /= in HH.

     destruct (incrementPC (<[ r1 := inr ((p, g), b, e, a') ]> regs)) as [ regs' |] eqn:Hregs';
       pose proof Hregs' as Hregs'2; cycle 1.
     { (* Failure: incrementing PC overflows *)
       assert (incrementPC (<[ r1 := inr ((p, g, b, e, a'))]> r) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         by rewrite lookup_insert_is_Some'; eauto.
         by apply insert_mono; eauto. }
       rewrite incrementPC_fail_updatePC //= in HH; inversion HH; subst.
       iMod (@gen_heap_update_inSepM with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFailWP "Hφ" Lea_fail_overflow_PC. }

     (* Success *)

     eapply (incrementPC_success_updatePC _ m) in Hregs'
       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
     rewrite HuPC in HH; clear HuPC; inversion HH; clear HH; subst c σ2. cbn.
     iFrame.
     iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
     eapply Lea_spec_success; eauto.

     Unshelve. all: assumption.
   Qed.

   Lemma wp_lea_success_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w rv z a' pc_p' :
     decodeInstrW w = Lea PC (inr rv) →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     pc_p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ rv ↦ᵣ inl z }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Ha' Hnep φ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert. (* TODO: add to simplify_map_eq via simpl_map? *)
       iApply (regs_of_map_2 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence.
       inv Hvpc. naive_solver. }
   Qed.

   Lemma wp_lea_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv p g b e a z a' pc_p' :
     decodeInstrW w = Lea r1 (inr rv) →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ PC → p ≠ E →
     (match p with
      | URW | URWL | URWX | URWLX => (a' <= a)%a
      | _ => True
      end) ->
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ rv ↦ᵣ inl z
              ∗ r1 ↦ᵣ inr ((p,g),b,e,a') }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Ha' Hne1 Hnep HU ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [| * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite (insert_commute _ PC r1) // insert_insert.
       rewrite (insert_commute _ r1 PC) // (insert_commute _ r1 rv) // insert_insert.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence.
       destruct p0; tauto. }
   Qed.

   Lemma wp_lea_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w z a' pc_p' :
     decodeInstrW w = Lea PC (inl z) →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     pc_p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ[pc_p'] w }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Ha' Hnep ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert. iApply (regs_of_map_1 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence.
       inv Hvpc. naive_solver. }
   Qed.

   Lemma wp_lea_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 p g b e a z a' pc_p' :
     decodeInstrW w = Lea r1 (inl z) →
     PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ PC → p ≠ E →
     (match p with
      | URW | URWL | URWX | URWLX => (a' <= a)%a
      | _ => True
      end) ->

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
            ∗ pc_a ↦ₐ[pc_p'] w
            ∗ r1 ↦ᵣ inr ((p,g),b,e,a') }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Ha' Hne1 Hnep HU ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite insert_commute // insert_insert insert_commute // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence.
       destruct p0; tauto. }
   Qed.

End cap_lang_rules.
