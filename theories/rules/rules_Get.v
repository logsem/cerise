From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base stdpp_extra.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{reservedaddresses : ReservedAddresses}.
  Context `{MP: MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types o : OType.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  (* Generalized denote function, since multiple cases result in similar success *)
  Definition denote (i: instr) (w : Word): option Z :=
    match w with
    | WCap p b e a =>
        match i with
        | GetP _ _ => Some (encodePerm p)
        | GetB _ _ => Some (b:Z)
        | GetE _ _ => Some (e:Z)
        | GetA _ _ => Some (a:Z)
        | GetOType _ _ => Some (-1)%Z
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
    | WSealRange p b e a =>
        match i with
        | GetP _ _ => Some (encodeSealPerms p)
        | GetB _ _ => Some (b:Z)
        | GetE _ _ => Some (e:Z)
        | GetA _ _ => Some (a:Z)
        | GetOType _ _ => Some (-1)%Z
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
    | WSealed o _ =>
        match i with
        | GetOType _ _ => Some (o:Z)
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
    | WInt _ =>
        match i with
        | GetOType _ _ => Some (-1)%Z
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
    end.

  Global Arguments denote : simpl nomatch.

  Definition is_Get (i: instr) (dst src: RegName) :=
    i = GetP dst src ∨
    i = GetB dst src ∨
    i = GetE dst src ∨
    i = GetA dst src \/
    i = GetOType dst src \/
    i = GetWType dst src
  .

  Lemma regs_of_is_Get i dst src :
    is_Get i dst src →
    regs_of i = {[ dst; src ]}.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  (* Simpler definition, easier to use when proving wp-rules *)
  Definition denote_cap (i: instr) (p : Perm) (b e a : Addr): Z :=
      match i with
      | GetP _ _ => (encodePerm p)
      | GetB _ _ => b
      | GetE _ _ => e
      | GetA _ _ => a
      | GetOType _ _ => (-1)%Z
      | GetWType _ _ => (encodeWordType (WCap p b e a))
      | _ => 0%Z
      end.
  Lemma denote_cap_denote i p b e a z src dst: is_Get i src dst → denote_cap i p b e a = z → denote i (WCap p b e a) = Some z.
  Proof. unfold denote_cap, denote, is_Get. intros [-> | [-> | [-> | [-> | [-> |  ->]]]]] ->; done. Qed.

  Definition denote_seal (i: instr) (p : SealPerms) (b e a : OType): Z :=
      match i with
      | GetP _ _ => (encodeSealPerms p)
      | GetB _ _ => b
      | GetE _ _ => e
      | GetA _ _ => a
      | GetOType _ _ => (-1)%Z
      | GetWType _ _ => (encodeWordType (WSealRange p b e a))
      | _ => 0%Z
      end.
  Lemma denote_seal_denote i (p : SealPerms) (b e a : OType) z src dst: is_Get i src dst → denote_seal i p b e a = z → denote i (WSealRange p b e a) = Some z.
  Proof. unfold denote_seal, denote, is_Get. intros [-> | [-> | [-> | [-> | [-> |  ->]]]]] ->; done. Qed.


  Inductive Get_failure (i: instr) (regs: LReg) (dst src: RegName) :=
    | Get_fail_src_denote (w : LWord):
        regs !! src = Some w →
        denote i (lword_get_word w) = None →
        Get_failure i regs dst src
    | Get_fail_overflow_PC (w : LWord) z:
        regs !! src = Some w →
        denote i (lword_get_word w) = Some z →
        incrementLPC (<[ dst := LInt z ]> regs) = None →
        Get_failure i regs dst src.

  Inductive Get_spec (i: instr) (regs: LReg) (dst src: RegName) (regs': LReg): cap_lang.val -> Prop :=
    | Get_spec_success (w : LWord) z:
        regs !! src = Some w →
        denote i (lword_get_word w) = Some z →
        incrementLPC (<[ dst := LInt z ]> regs) = Some regs' →
        Get_spec i regs dst src regs' NextIV
    | Get_spec_failure:
        Get_failure i regs dst src →
        Get_spec i regs dst src regs' FailedV.

  Lemma exec_opt_Get_denote {dst instr src φ} :
    is_Get instr dst src ->
    exec_opt instr φ =
      w ← reg φ !! src ;
      w2 ← denote instr w;
      updatePC (update_reg φ dst (WInt w2)).
  Proof.
    intros Hinstr.
    destruct_or! Hinstr; subst; cbn;
      destruct (reg φ !! src); cbn; try done;
      destruct w; try done;
      now destruct sb.
  Qed.


  Lemma wp_Get Ep pc_p pc_b pc_e pc_a pc_v lw get_i dst src regs :
    decodeInstrWL lw = get_i →
    is_Get get_i dst src →

    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of get_i ⊆ dom regs →

    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Get_spec (decodeInstrWL lw) regs dst src regs' retv ⌝ ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_exec_opt Hvpc HPC Hdecode Dregs with "[$Hpc_a $Hmap Hφ]").
    erewrite regs_of_is_Get in Dregs; eauto.
    iModIntro.
    iIntros (σ) "(Hσ & Hregs &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) Hcred".

    rewrite (exec_opt_Get_denote Hinstr); cbn.
    rewrite Hdecode.

    iApply wp_wp2.
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.
    iPoseProof (state_interp_transient_intro (lm:= ∅) with "[$Hregs $Hσ]") as "Hσ". set_solver.
    iApply (wp2_reg_lookup (lrt := regs)); first by set_solver.
    iModIntro.
    iFrame "Hσ".
    iIntros (lwr) "Hσ %Hlrs %Hrs".
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply wp2_diag_univ.
    iSplit.
    { iIntros "%Hldn %Hdn".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "(Hσ & Hregs & _)".
      iFrame.
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro. constructor.
      now eapply (Get_fail_src_denote _ _ _ _ _ Hlrs). }

    iIntros (z Hdz _).

    iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LInt z) with "Hσ") as "Hσ".
    { now set_solver. }
    { now intros. }

    rewrite updatePC_incrementPC.
    iApply (wp_opt2_bind (φ1 := incrementLPC (<[ dst := LInt z]> regs)) (k1 := (fun x => Some x))).
    iApply wp_opt2_eqn_both.
    iApply (wp2_opt_incrementPC with "[$Hσ Hpc_a Hφ]").
    { rewrite dom_insert. apply elem_of_union_r. now rewrite elem_of_dom HPC. }
    iSplit.
    - iIntros "Hσ %Hlin %Hin".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "(Hσ & Hregs & _)".
      iFrame.
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply Get_spec_failure; try eassumption.
      eapply Get_fail_overflow_PC; eassumption.
    - iIntros (regs' φt') "Hσ %Hlis %His".
      iApply wp2_val.
      cbn.
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply Get_spec_success; try eassumption.
  Qed.

  (* Note that other cases than WCap in the PC are irrelevant, as that will result in having an incorrect PC *)
  Lemma wp_Get_PC_success Ep get_i dst pc_p pc_b pc_e pc_a pc_v lw wdst pc_a' z :
    decodeInstrWL lw = get_i →
    is_Get get_i dst PC →

    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)) = Some z →

    {{{ ▷ PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v)
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a' pc_v)
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame.
      incrementLPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_same_success Ep get_i r pc_p pc_b pc_e pc_a pc_v lw lwr pc_a' z:
    decodeInstrWL lw = get_i →
    is_Get get_i r r →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (lword_get_word lwr) = Some z →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r ↦ᵣ lwr }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
            ∗ ▷ (pc_a, pc_v) ↦ₐ lw
            ∗ r ↦ᵣ LInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_success Ep get_i dst src pc_p pc_b pc_e pc_a pc_v lw lwsrc lwdst pc_a' z :
    decodeInstrWL lw = get_i →
    is_Get get_i dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (lword_get_word lwsrc) = Some z →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ src ↦ᵣ lwsrc
        ∗ ▷ dst ↦ᵣ lwdst }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ src ↦ᵣ lwsrc
          ∗ dst ↦ᵣ LInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_fail Ep get_i dst src pc_p pc_b pc_e pc_a pc_v lw zsrc lwdst :
    decodeInstrWL lw = get_i →
    is_Get get_i dst src →
    (forall dst' src', get_i <> GetOType dst' src') ->
    (forall dst' src', get_i <> GetWType dst' src') ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
      ∗ ▷ (pc_a, pc_v) ↦ₐ lw
      ∗ ▷ dst ↦ᵣ lwdst
      ∗ ▷ src ↦ᵣ LInt zsrc }}}
      Instr Executable @ Ep
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hinstr Hnot_otype Hnot_wtype Hvpc φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)
      destruct (decodeInstrWL lw); simplify_map_eq
        ; specialize (Hnot_otype dst0 r)
        ; specialize (Hnot_wtype dst0 r)
      ; try contradiction.
    }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

End cap_lang_rules.

(* Hints to automate proofs of is_Get *)

Lemma is_Get_GetP dst src : is_Get (GetP dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetB dst src : is_Get (GetB dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetE dst src : is_Get (GetE dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetA dst src : is_Get (GetA dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetOType dst src : is_Get (GetOType dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetWType dst src : is_Get (GetWType dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma getwtype_denote `{MachineParameters} r1 r2 w : denote (GetWType r1 r2) w = Some (encodeWordType w).
Proof. by destruct_word w ; cbn. Qed.

Global Hint Resolve is_Get_GetP : core.
Global Hint Resolve is_Get_GetB : core.
Global Hint Resolve is_Get_GetE : core.
Global Hint Resolve is_Get_GetA : core.
Global Hint Resolve is_Get_GetOType : core.
Global Hint Resolve is_Get_GetWType : core.
Global Hint Resolve getwtype_denote : core.
