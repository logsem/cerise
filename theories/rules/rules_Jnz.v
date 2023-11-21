From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base rules_Jmp register_tactics.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
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

  Inductive Jnz_failure (regs: Reg) (dst src: RegName) (mem : gmap Addr Word) :=
  | Jnz_fail_cond w:
    regs !! src = Some w →
    nonZero w = false →
    incrementPC regs = None →
    Jnz_failure regs dst src mem
  | Jnz_fail_bounds w b e a:
    regs !! src = Some w →
    nonZero w = true →
    regs !! dst = Some (WCap IE b e a) ->
    not (withinBounds b e a /\ withinBounds b e (a^+1)%a) →
    Jnz_failure regs dst src mem
  .

  Inductive Jnz_spec (regs: Reg) (dst src: RegName)
    (regs' : Reg) (mem : gmap Addr Word) : cap_lang.val → Prop :=
  | Jnz_spec_failure :
    Jnz_failure regs dst src mem ->
    Jnz_spec regs dst src regs' mem FailedV

  | Jnz_spec_success_IE_t wcond b e a wpc widc:
    regs !! src = Some wcond →
    regs !! dst = Some (WCap IE b e a) →
    nonZero wcond = true →
    withinBounds b e a ->
    withinBounds b e (a^+1)%a ->
    mem !! a = Some wpc ->
    mem !! (a^+1)%a = Some widc ->
    regs' = ( <[ idc := widc ]> (<[ PC := wpc ]> regs)) ->
    Jnz_spec regs dst src regs' mem NextIV

  | Jnz_spec_success_t w w':
    regs !! src = Some w →
    regs !! dst = Some w' →
    nonZero w = true →
    is_ie_cap w' = false ->
    regs' = <[PC := updatePcPerm w' ]> regs ->
    Jnz_spec regs dst src regs' mem NextIV

  | Jnz_spec_success_f w:
    regs !! src = Some w →
    nonZero w = false →
    incrementPC regs = Some regs' →
    Jnz_spec regs dst src regs' mem NextIV.

  Definition allow_jnz_mmap_or_true (dst src : RegName) (regs : Reg) (mem : Mem) :=
    forall wsrc,
      regs !! src = Some wsrc ->
      nonZero wsrc ->
      allow_jmp_mmap_or_true dst regs mem.

  Definition allow_jnz_rmap_or_true (dst src : RegName) (regs : Reg) :=
    forall wsrc,
      regs !! src = Some wsrc ->
      nonZero wsrc ->
      allow_jmp_rmap_or_true dst regs.

  Lemma wp_Jnz Ep pc_p pc_b pc_e pc_a w dst src regs mem :
    decodeInstrW w = Jnz dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    allow_jnz_mmap_or_true dst src regs mem ->
    allow_jnz_rmap_or_true dst src regs ->
    regs_of (Jnz dst src) ⊆ dom regs →
    mem !! pc_a = Some w →

    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
          ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ regs' retv, RET retv;
          ⌜ Jnz_spec regs dst src regs' mem retv ⌝ ∗
            ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
            [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hmmap Hrmap Dregs Hmem_pc φ) "(>Hmem & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[Hr Hm] /=". destruct σ1; simpl.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

    (* Derive necessary register values in dst and src *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri src) as [wsrc [H'src Hsrc]]; first set_solver+.
    odestruct (Hri dst) as [wdst [H'dst Hdst]]; first set_solver+.
    clear Hri.
    (* Derive the PC in memory *)
    iDestruct (gen_mem_valid_inSepM mem m with "Hm Hmem") as %Hma; eauto.

    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= in Hstep.

    (* Now we start splitting on the different cases in the Jnz spec, and prove them one at a time *)
    destruct (nonZero wsrc) eqn:Hnz; pose proof Hnz as H'nz;
      cbn in Hstep; rewrite Hsrc Hdst /= Hnz in Hstep.
    { (* wsrc is non-zero, destruct on the dst *)
      destruct (is_ie_cap wdst) eqn:Hwdst.
      - (* wdst is an IE-cap *)
        destruct wdst ; cbn in Hwdst; try discriminate.
        destruct sb as [ p b e a |]; cbn in Hwdst; try discriminate.
        destruct p; try discriminate ; clear Hwdst.

        (* destruct the bounds *)
        destruct (decide (withinBounds b e a && withinBounds b e (a ^+ 1)%a)) as
          [Hbounds%Is_true_true | Hbounds%Is_true_false]
        ; (rewrite Hbounds /= in Hstep).
        apply Is_true_true_2, andb_True in Hbounds.
        destruct Hbounds as [Hbounds_a Hbounds_a'].

        * (* in bounds, success *)
          pose proof H'dst as H'dst'.
          apply Is_true_true_2 in Hnz.
          destruct (Hmmap _ H'src Hnz) as (p'&b'&e'&a'& Hrinr & HallowLoad).
          destruct (Hrmap _ H'src Hnz) as (p''&b''&e''&a''& Hrinr' & HallowLoad').
          rewrite /read_reg_inr in Hrinr, Hrinr'.
          rewrite H'dst in Hrinr, Hrinr'; symmetry in Hrinr, Hrinr' ; simplify_eq.
          case_decide as Hdec ; last simplify_map_eq.
          2: { exfalso; apply Hdec. repeat (split ; auto). }
          destruct Hdec as (Hreg & _ & _ & _).
          destruct HallowLoad as (wpc & widc & HaLoad & Ha'Load).
          destruct HallowLoad' as (w' & Hidc).

          iDestruct (gen_mem_valid_inSepM mem m a wpc with "Hm Hmem" ) as %Hma'
          ; eauto.
          iDestruct (gen_mem_valid_inSepM mem m (a^+1)%a widc with "Hm Hmem" ) as %Hma''
          ; eauto.
          rewrite Hma' Hma'' /= in Hstep; simplify_pair_eq; simpl.
          iMod ((gen_heap_update_inSepM _ _ PC wpc) with "Hr Hmap") as "[Hr Hmap]"; eauto.
          iMod ((gen_heap_update_inSepM _ _ idc widc) with "Hr Hmap") as
            "[Hr Hmp]" ; eauto.
          { apply lookup_insert_is_Some'; by right. }
          iFrame; try iApply "Hφ"; iFrame.
          iPureIntro; econstructor; eauto.
        * (* in bounds, failure *)
          simplify_pair_eq ; iFrame ; iApply "Hφ"; iFrame.
          iPureIntro; eapply Jnz_spec_failure ; eapply Jnz_fail_bounds ; eauto.
          apply andb_false_iff in Hbounds. intro Hcontra.
          destruct Hcontra as [Hcontra1%Is_true_true_1 Hcontra2%Is_true_true_1].
          destruct Hbounds; congruence.

      - (* wdst is not an IE-cap *)

        (* TODO use =match goal with= instead *)
        rewrite (_ :
            match wdst with
            | WCap IE b e a =>
                if withinBounds b e a && withinBounds b e (a ^+ 1)%a
                then
                 m !! a
                 ≫= (λ wpc : Word,
                       m !! (a ^+ 1)%a
                       ≫= (λ widc : Word,
                             Some (NextI, update_reg (update_reg (r, m) PC wpc) idc widc)))
                else None
            | _ => Some (NextI, update_reg (r, m) PC (updatePcPerm wdst))
            end = Some (NextI, update_reg (r, m) PC (updatePcPerm wdst))) in
          Hstep.
        2: {
        destruct wdst ; cbn in Hwdst; try discriminate; auto.
        destruct sb as [ p b e a |]; cbn in Hwdst; try discriminate; auto.
        destruct p; try discriminate ; auto.
        }

      simplify_pair_eq; simpl.
      iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame.
      iApply "Hφ". iFrame. iPureIntro; econstructor 3; eauto.
    }

    (* wsrc is zero, destruct on the dst *)
    destruct (incrementPC regs) eqn:HX; pose proof HX as H'X; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=m) in HX.
      eapply updatePC_fail_incl with (m':=m) in HX; eauto.
      rewrite HX in Hstep. inv Hstep.
      iFrame. iApply "Hφ". iFrame. iPureIntro; econstructor ; econstructor; eauto. }

    destruct (incrementPC_success_updatePC _ m _ HX)
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC; eauto. rewrite HuPC in Hstep.
    simplify_pair_eq.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iApply "Hφ". iFrame. iPureIntro; econstructor 4; eauto.
  Qed.

  Lemma wp_jnz_success_jmp E r1 r2 pc_p pc_b pc_e pc_a w w1 w2 :
    decodeInstrW w = Jnz r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    w2 ≠ WInt 0%Z →
    is_ie_cap w1 = false ->

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w1
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne Hdst ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".

    iApply (wp_Jnz with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    (* TODO should be a lemma *)
    {
      intros wsrc _ _.
      destruct_word w1; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: try destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    {
      intros wsrc _ _.
      destruct_word w1; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: try destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    { by rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hreg)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

   destruct Hspec as [ X | | | ]
   ; [destruct X | | | ]
   ; try (exfalso; simplify_map_eq; congruence).
    subst regs'; simplify_map_eq.
    iApply "Hφ".
    iExtractList "Hreg" [PC; r1; r2] as ["HPC"; "Hr1"; "Hr2"]; iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a _]"; auto.
    Unshelve. all: eauto.
  Qed.

  (* TODO we need to do more cases where:
       - r = idc
       - pc_a = a
       - pc_a = a+1
   *)
  Lemma wp_jnz_success_jmp_IE E r1 r2 pc_p pc_b pc_e pc_a w w' w2 b e a wpc widc :
    decodeInstrW w = Jnz r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    withinBounds b e a ->
    withinBounds b e (a^+1)%a ->
    w2 ≠ WInt 0%Z →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ idc ↦ᵣ w'
          ∗ ▷ r1 ↦ᵣ WCap IE b e a
          ∗ ▷ r2 ↦ᵣ w2
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ a ↦ₐ wpc
          ∗ ▷ (a^+1)%a ↦ₐ widc
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ wpc
          ∗ ▷ idc ↦ᵣ widc
          ∗ ▷ r1 ↦ᵣ WCap IE b e a
          ∗ r2 ↦ᵣ w2
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ a ↦ₐ wpc
          ∗ ▷ (a^+1)%a ↦ₐ widc
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hbound_a Hbound_a' Hne ϕ)
      "(>HPC & >HIDC & >Hr1 & >Hr2 & >Hpc_a & >Ha & >Ha') Hφ".
    iDestruct (map_of_regs_4 with "HPC HIDC Hr1 Hr2") as "[Hmap (%&%&%&%&%&%)]".

    iDestruct (address_neq with "Ha' Hpc_a") as "%Ha'".
    iDestruct (address_neq with "Ha Ha'") as "%Hneqa".
    iDestruct (memMap_resource_2ne_apply with "Hpc_a Ha") as "[Hmem %Ha]".
    iDestruct (big_sepM_insert with "[Ha' Hmem]") as "Hmem" ; [| iFrame |].
    by simplify_map_eq.

    iApply (wp_Jnz with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { intros wsrc _ _.
      apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      by exists wpc, widc.
    }
    { intros wsrc _ _.
      apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      by exists w'.
    }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hreg)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

    destruct Hspec as [ X | | | ]
    ; [ (destruct X as [ | ? ? ? ? ? ? ? Hcontra ]) | | | ]
    ; try (exfalso; simplify_map_eq; congruence)
    ; simplify_map_eq.
    { exfalso ; by apply Hcontra. }
    iApply "Hφ".
    iExtractList "Hreg" [PC; idc ; r1; r2] as ["HPC"; "HIDC" ;"Hr1"; "Hr2"]; iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Ha' Hmem]"; auto ; [ by simplify_map_eq|].
    iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a Hmem]"; auto ; [ by simplify_map_eq|].
    iDestruct (big_sepM_insert with "Hmem") as "[Ha _]"; auto.
    iFrame.
  Qed.

  (* TODO version fail with IE *)
  Lemma wp_jnz_success_jmp_same E r2 pc_p pc_b pc_e pc_a w w2 :
    decodeInstrW w = Jnz r2 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    w2 ≠ WInt 0%Z →
    is_ie_cap w2 = false ->

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w2
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne Hdst ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".

    iApply (wp_Jnz with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { intros wsrc _ _.
      destruct_word w2; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: try destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    { intros wsrc _ _.
      destruct_word w2; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: try destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
   }
   { by rewrite !dom_insert; set_solver+. }

   iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hreg)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

    destruct Hspec as [ X | | | ]
    ; [destruct X | | | ]
    ; try (exfalso; simplify_map_eq; congruence).
    subst regs'; simplify_map_eq.
    iApply "Hφ".
    iExtractList "Hreg" [PC; r2] as ["HPC"; "Hr2"]; iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a _]"; auto.
    Unshelve. all: eauto.
  Qed.

  Lemma wp_jnz_success_jmpPC E pc_p pc_b pc_e pc_a w :
    decodeInstrW w = Jnz PC PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm (WCap pc_p pc_b pc_e pc_a)
          ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".
    iApply (wp_Jnz with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { intros wsrc _ _.
      apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      case_decide as Heq; [destruct Heq as (_ & -> & _)|]; done.
    }
    { intros wsrc _ _.
      apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      case_decide as Heq; [destruct Heq as (_ & -> & _)|]; done.
    }

    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hreg)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ X | | | ]
    ; [destruct X | | | ]
    ; try (exfalso; simplify_map_eq; congruence)
    ; try (simplify_map_eq; apply isCorrectPC_not_ie_cap in Hvpc ; cbn in Hvpc ; congruence).
    subst regs'; simplify_map_eq.
    iApply "Hφ".
    iExtractList "Hreg" [PC] as ["HPC"]; iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a _]"; auto.
  Qed.

  Lemma wp_jnz_success_jmpPC1 E r2 pc_p pc_b pc_e pc_a w w2 :
    decodeInstrW w = Jnz PC r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    w2 ≠ WInt 0%Z →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm (WCap pc_p pc_b pc_e pc_a)
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".
    iApply (wp_Jnz with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { intros wsrc _ _.
      apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      case_decide as Heq; [destruct Heq as (_ & -> & _)|]; done.
    }
    { intros wsrc _ _.
      apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      case_decide as Heq; [destruct Heq as (_ & -> & _)|]; done.
    }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hreg)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }


    destruct Hspec as [ X | | | ]
    ; [destruct X | | | ]
    ; try (exfalso; simplify_map_eq; congruence)
    ; try (simplify_map_eq; apply isCorrectPC_not_ie_cap in Hvpc ; cbn in Hvpc ; congruence).
    subst regs'; simplify_map_eq.
    iApply "Hφ".
    iExtractList "Hreg" [PC; r2] as ["HPC";"Hr2"]; iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a _]"; auto.
  Qed.

  Lemma wp_jnz_success_jmpPC2 E r1 pc_p pc_b pc_e pc_a w w1 :
    decodeInstrW w = Jnz r1 PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    is_ie_cap w1 = false ->

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w1
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hdst ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".
    iApply (wp_Jnz with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { intros wsrc _ _.
      destruct_word w1; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: try destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    { intros wsrc _ _.
      destruct_word w1; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: try destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hreg)". iDestruct "Hspec" as %Hspec.


    destruct Hspec as [ X | | | ]
    ; [destruct X | | | ]
    ; try (exfalso; simplify_map_eq; congruence).
    subst regs'; simplify_map_eq.
    iApply "Hφ".
    iExtractList "Hreg" [PC; r1] as ["HPC";"Hr1"]; iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a _]"; auto.
    Unshelve. all: auto.
  Qed.

  Lemma wp_jnz_success_jmpPC2_IE E r1 pc_p pc_b pc_e pc_a w w' b e a wpc widc :
    decodeInstrW w = Jnz r1 PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    withinBounds b e a ->
    withinBounds b e (a^+1)%a ->

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ idc ↦ᵣ w'
          ∗ ▷ r1 ↦ᵣ WCap IE b e a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ a ↦ₐ wpc
          ∗ ▷ (a^+1)%a ↦ₐ widc
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ wpc
          ∗ ▷ idc ↦ᵣ widc
          ∗ ▷ r1 ↦ᵣ WCap IE b e a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ a ↦ₐ wpc
          ∗ ▷ (a^+1)%a ↦ₐ widc
      }}}.
  Proof.

    iIntros (Hinstr Hvpc Hbound_a Hbound_a' ϕ)
      "(>HPC & >HIDC & >Hr1 & >Hpc_a & >Ha & >Ha') Hφ".
    iDestruct (map_of_regs_3 with "HPC HIDC Hr1") as "[Hmap (%&%&%)]".

    iDestruct (address_neq with "Ha' Hpc_a") as "%Ha'".
    iDestruct (address_neq with "Ha Ha'") as "%Hneqa".
    iDestruct (memMap_resource_2ne_apply with "Hpc_a Ha") as "[Hmem %Ha]".
    iDestruct (big_sepM_insert with "[Ha' Hmem]") as "Hmem" ; [| iFrame |].
    by simplify_map_eq.

    iApply (wp_Jnz with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { intros wsrc _ _.
      apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      by exists wpc, widc.
    }
    { intros wsrc _ _.
      apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      by exists w'.
    }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hreg)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ X | | | ]
    ; [ (destruct X as [ | ? ? ? ? ? ? ? Hcontra ]) | | | ]
    ; try (exfalso; simplify_map_eq; congruence)
    ; simplify_map_eq.
    { exfalso ; by apply Hcontra. }
    iApply "Hφ".
    iExtractList "Hreg" [PC; idc ; r1] as ["HPC"; "HIDC" ;"Hr1"]; iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Ha' Hmem]"; auto ; [ by simplify_map_eq|].
    iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a Hmem]"; auto ; [ by simplify_map_eq|].
    iDestruct (big_sepM_insert with "Hmem") as "[Ha _]"; auto.
    iFrame.
  Qed.

  Lemma wp_jnz_success_next E r1 r2 pc_p pc_b pc_e pc_a pc_a' w w1 :
    decodeInstrW w = Jnz r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ WInt 0%Z }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".
    iApply (wp_Jnz with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { intros wsrc Hsrc Hneq.
      destruct_word w1; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
    }
    { intros wsrc Hsrc Hneq.
      destruct_word w1; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
    }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hreg)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ X | | | ]
    ; [destruct X | | | ]
    ; try (exfalso; simplify_map_eq; congruence)
    ; match goal with | H: context[incrementPC _] |- _ => unfold incrementPC in H end
    ; simplify_map_eq.
    iApply "Hφ".
    iExtractList "Hreg" [PC; r1;r2] as ["HPC";"Hr1";"Hr2"]; iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a _]"; auto.
    Unshelve. all: auto.
  Qed.

End cap_lang_rules.
