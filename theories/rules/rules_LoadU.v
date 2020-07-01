From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
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

  Inductive LoadU_failure (regs: Reg) (rdst rsrc: RegName) (offs: Z + RegName) (mem : PermMem):=
  | LoadU_fail_const z:
      regs !! rsrc = Some (inl z) ->
      LoadU_failure regs rdst rsrc offs mem
  | LoadU_fail_perm p g b e a:
      regs !! rsrc = Some (inr ((p, g), b, e, a)) ->
      isU p = false ->
      LoadU_failure regs rdst rsrc offs mem
  | LoadU_fail_offs_arg p g b e a:
      regs !! rsrc = Some (inr ((p, g), b, e, a)) ->
      isU p = true ->
      z_of_argument regs offs = None ->
      LoadU_failure regs rdst rsrc offs mem
  | LoadU_fail_verify_access p g b e a noffs:
      regs !! rsrc = Some (inr ((p, g), b, e, a)) ->
      isU p = true ->
      z_of_argument regs offs = Some noffs ->
      verify_access (LoadU_access b e a noffs) = None ->
      LoadU_failure regs rdst rsrc offs mem
  | LoadU_fail_incrementPC p g b e a noffs a' p' w:
      regs !! rsrc = Some (inr ((p, g), b, e, a)) ->
      isU p = true ->
      z_of_argument regs offs = Some noffs ->
      verify_access (LoadU_access b e a noffs) = Some a' ->
      mem !! a' = Some(p', w) →
      incrementPC (<[ rdst := w ]> regs) = None ->
      LoadU_failure regs rdst rsrc offs mem.

  Inductive LoadU_spec
    (regs: Reg) (rdst rsrc: RegName) (offs: Z + RegName)
    (regs': Reg) (mem : PermMem) : cap_lang.val → Prop
  :=
  | LoadU_spec_success p p' g b e a a' noffs w :
      regs !! rsrc = Some (inr ((p, g), b, e, a)) ->
      isU p = true ->
      z_of_argument regs offs = Some noffs ->
      verify_access (LoadU_access b e a noffs) = Some a' ->
      mem !! a' = Some(p', w) →
      incrementPC (<[ rdst := w ]> regs) = Some regs' ->
      LoadU_spec regs rdst rsrc offs regs' mem NextIV
  | LoadU_spec_failure :
    LoadU_failure regs rdst rsrc offs mem ->
    LoadU_spec regs rdst rsrc offs regs' mem FailedV.
  
  Lemma wp_loadU Ep
     pc_p pc_g pc_b pc_e pc_a pc_p'
     rdst rsrc offs w mem regs :
   decodeInstrW w = LoadU rdst rsrc offs →
   pc_p' ≠ O →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (LoadU rdst rsrc offs) ⊆ dom _ regs →
   mem !! pc_a = Some (pc_p', w) →
   match regs !! rsrc with
   | None => True
   | Some (inl _) => True
   | Some (inr (p, g, b, e, a)) =>
     if isU p then
       match z_of_argument regs offs with
       | None => True
       | Some zoffs => match verify_access (LoadU_access b e a zoffs) with
                      | None => True
                      | Some a' => match mem !! a' with
                                  | None => False
                                  | Some (p', w) => p' <> O
                                  end
                      end
       end
     else True
   end ->

   {{{ (▷ [∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ LoadU_spec regs rdst rsrc offs regs' mem retv⌝ ∗
         ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc HPC Dregs Hmem_pc HaLoad φ) "(>Hmem & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "[Hr Hm] /=". destruct σ1; simpl.
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     feed destruct (Hri rsrc) as [rsrcv [Hrsrc' Hrsrc]]. by set_solver+.
     feed destruct (Hri rdst) as [rdstv [Hrdst' _]]. by set_solver+.
     pose proof (regs_lookup_eq _ _ _ Hrsrc') as Hrsrc''.
     pose proof (regs_lookup_eq _ _ _ Hrdst') as Hrdst''.
     (* Derive the PC in memory *)
     iDestruct (gen_mem_valid_inSepM pc_a _ _ _ _ mem _ m with "Hm Hmem") as %Hma; eauto.
     
     iModIntro.
     iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

     option_locate_mr m r.
     rewrite /exec in Hstep. rewrite Hrrsrc in Hstep.

     destruct rsrcv as [| [[[[p g] b] e] a] ].
     { inv Hstep. iFailWP "Hφ" LoadU_fail_const. }

     destruct (isU p) eqn:HisU; cycle 1.
     { inv Hstep. iFailWP "Hφ" LoadU_fail_perm. }

     assert (Hzofargeq: z_of_argument r offs = z_of_argument regs offs).
     { rewrite /z_of_argument; destruct offs; auto.
       feed destruct (Hri r0) as [? [?]]. by set_solver+.
       rewrite H2 H3; auto. }
     rewrite Hzofargeq in Hstep.

     destruct (z_of_argument regs offs) as [zoffs|] eqn:Hoffs; cycle 1.
     { inv Hstep. iFailWP "Hφ" LoadU_fail_offs_arg. }

     destruct (verify_access (LoadU_access b e a zoffs)) as [a'|] eqn:Hverify; cycle 1.
     { inv Hstep. iFailWP "Hφ" LoadU_fail_verify_access. }
     simpl in Hstep. rewrite Hrsrc' HisU Hverify in HaLoad.
     rewrite /MemLocate in Hstep. destruct (mem !! a') as [(p', wa)|] eqn:Ha'; cycle 1.
     { inv HaLoad. }
     iDestruct (gen_mem_valid_inSepM a' _ _ _ _ mem _ m with "Hm Hmem") as %Hma'; eauto.
     rewrite Hma' in Hstep. destruct (incrementPC (<[rdst:=wa]> regs)) eqn:Hincr; cycle 1.
     { assert _ as Hincr' by (eapply (incrementPC_overflow_mono (<[rdst:=wa]> regs) (<[rdst:=wa]> r) _ _ _)).
       rewrite incrementPC_fail_updatePC in Hstep; eauto.
       inv Hstep. simpl.
       iMod ((gen_heap_update_inSepM _ _ rdst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFailWP "Hφ" LoadU_fail_incrementPC. }

     destruct (incrementPC_success_updatePC _ m _ Hincr) as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iMod ((gen_heap_update_inSepM _ _ rdst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. econstructor; eauto.
     Unshelve. all: eauto.
     { destruct (reg_eq_dec PC rdst).
       - subst rdst. rewrite lookup_insert. eauto.
       - rewrite lookup_insert_ne; eauto. }
     { eapply insert_mono; eauto. }
   Qed.

End cap_lang_rules.
