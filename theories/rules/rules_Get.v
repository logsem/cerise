From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base stdpp_extra.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Context `{MachineParameters}.
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
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_instr_exec.
    iIntros (σ1) "Hσ1".
    destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hmap") as "#H".
    iDestruct "H" as %Hregs.
    have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hlpc_a; auto.
    do 2 iModIntro.
    iIntros (c σ2 Hstep) "_".
    eapply step_exec_inv in Hstep; eauto.
    2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)))
    ; eapply state_corresponds_reg_get_word ; eauto.
    2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto.

    unfold exec in Hstep.

    specialize (indom_lregs_incl _ regs lr Dregs Hregs) as Hri.
    erewrite regs_of_is_Get in Hri; eauto.
    destruct (Hri src) as [lwsrc [H'lsrc Hlsrc]]; first by set_solver+.
    destruct (Hri dst) as [lwdst [H'ldst Hldst]]; first by set_solver+.

    (* Extract information about physical words in src and dst *)
    set (wsrc := lword_get_word lwsrc).
    set (wdst := lword_get_word lwdst).
    assert ( reg !! src = Some wsrc ) as Hsrc by (eapply state_corresponds_reg_get_word ; eauto).
    assert ( reg !! dst = Some wdst ) as Hdst by (eapply state_corresponds_reg_get_word ; eauto).

    destruct (denote get_i wsrc) as [z | ] eqn:Hwsrc.
    2 : { (* Failure: src is not of the right word type *)
      assert
        (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |})
      as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr in Hstep; cbn in Hstep.
        all: rewrite Hsrc /= in Hstep.
        all : destruct wsrc as [ | [  |  ] | ]; try (inversion Hstep; auto);
          rewrite /denote /= in Hwsrc; rewrite Hinstr in Hwsrc; congruence. }
      rewrite Hdecode.

    (* TODO replace the iFail tactic -> modify the tactic to fit the new pattern *)
    iSplitR "Hφ Hmap Hpc_a"
    ; [ iExists lr, lm, cur_map; iFrame; auto
      | iApply "Hφ" ; iFrame ; iFailCore Get_fail_src_denote
      ].
    }

    assert (exec_opt get_i {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}
            = updatePC (update_reg {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}
                          dst (WInt z))) as HH.
    { destruct_or! Hinstr; clear Hdecode; subst get_i; cbn in Hstep |- *.
      all: rewrite /update_reg Hsrc /= in Hstep |-*; auto.
      all : destruct wsrc as [ | [  |  ] | ]; inversion Hwsrc; auto.
    }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    (* TODO is there a way to use incrementPC instead of incrementLPC ? *)
    destruct (incrementLPC (<[ dst := LInt z ]> regs)) as [regs'|] eqn:Hregs'
    ; pose proof Hregs' as H'regs'; cycle 1.
    { (* Failure: incrementing PC overflows *)
      cbn in Hregs'.

      apply incrementLPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hregs'.
      eapply updatePC_fail_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in Hregs'.
      2: {
        rewrite /lreg_strip lookup_fmap.
        apply fmap_is_Some.
        destruct (decide (dst = PC)) ; simplify_map_eq; auto.
      }
      2: by apply map_fmap_mono; apply insert_mono ; eauto.
      simplify_pair_eq.
      rewrite ( _ :
         (λ lw : LWord, lword_get_word lw) <$> <[dst:=LInt z]> lr = <[dst:=WInt z]> reg
        ) in Hregs'; cycle 1.
      { destruct HLinv as [[Hstrips Hcurreg] _].
        rewrite -Hstrips fmap_insert -/(lreg_strip lr); auto.
      }

      rewrite Hregs' in Hstep. inversion Hstep.
      iSplitR "Hφ Hmap Hpc_a"
      ; [ iExists lr, lm, cur_map; iFrame; auto
        | iApply "Hφ" ; iFrame ; iFailCore Get_fail_overflow_PC
        ].
    }



    (* Success *)
    eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hregs'
        as (p' & b' & e' & a'' & a_pc' & v' & HPC'' & Hpc_a' & HuPC & ->).

    assert ( dst <> PC ) as Hneq by (intro ; simplify_map_eq).
    rewrite lookup_insert_ne in HPC''; auto.
    rewrite HPC'' in HPC; simplify_eq.

    eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC.
    2: by apply map_fmap_mono; apply insert_mono ; eauto.
    rewrite ( _ :
              (λ lw : LWord, lword_get_word lw) <$> <[dst:=LInt z]> lr = <[dst:=WInt z]> reg
            ) in HuPC; cycle 1.
    { destruct HLinv as [[Hstrips Hcurreg] _].
      rewrite -Hstrips fmap_insert -/(lreg_strip lr); auto. }

    rewrite HuPC in Hstep; simplify_pair_eq.

    iMod ((gen_heap_update_inSepM _ _ dst (LInt z)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC (LCap pc_p pc_b pc_e a_pc' pc_v)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { destruct (decide (dst = PC)) ; simplify_map_eq; auto. }
    iFrame. iModIntro.

    iSplitR "Hφ Hmap Hpc_a"; cycle 1.
    - iApply "Hφ" ; iFrame ; iPureIntro; econstructor; eauto.
    - iExists _, lm, cur_map; iFrame; auto.
      destruct HLinv as [[Hstrips Hcur_reg] HmemInv]; cbn in *.
      iPureIntro; econstructor; eauto.
      split.
      by rewrite -Hstrips /lreg_strip 2!fmap_insert /= .
      clear HuPC HH Hri Hwsrc Hsrc Hlsrc.
      apply map_Forall_insert_2 ; [ | apply map_Forall_insert_2; cbn ; auto].

      cbn.
      eapply map_Forall_lookup_1 with (i := PC) in Hcur_reg; eauto.
      rewrite /is_cur_word in Hcur_reg.
      eapply Hcur_reg.
  Qed.

  (* Note that other cases than WCap in the PC are irrelevant, as that will result in having an incorrect PC *)
  Lemma wp_Get_PC_success E get_i dst pc_p pc_b pc_e pc_a pc_v lw wdst pc_a' z :
    decodeInstrWL lw = get_i →
    is_Get get_i dst PC →

    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)) = Some z →

    {{{ ▷ PC ↦ᵣ (LCap pc_p pc_b pc_e pc_a pc_v)
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
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

  Lemma wp_Get_same_success E get_i r pc_p pc_b pc_e pc_a pc_v lw lwr pc_a' z:
    decodeInstrWL lw = get_i →
    is_Get get_i r r →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (lword_get_word lwr) = Some z →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r ↦ᵣ lwr }}}
      Instr Executable @ E
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

  Lemma wp_Get_success E get_i dst src pc_p pc_b pc_e pc_a pc_v lw lwsrc lwdst pc_a' z :
    decodeInstrWL lw = get_i →
    is_Get get_i dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (lword_get_word lwsrc) = Some z →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ src ↦ᵣ lwsrc
        ∗ ▷ dst ↦ᵣ lwdst }}}
      Instr Executable @ E
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

  Lemma wp_Get_fail E get_i dst src pc_p pc_b pc_e pc_a pc_v lw zsrc lwdst :
    decodeInstrWL lw = get_i →
    is_Get get_i dst src →
    (forall dst' src', get_i <> GetOType dst' src') ->
    (forall dst' src', get_i <> GetWType dst' src') ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
      ∗ ▷ (pc_a, pc_v) ↦ₐ lw
      ∗ ▷ dst ↦ᵣ lwdst
      ∗ ▷ src ↦ᵣ LInt zsrc }}}
      Instr Executable @ E
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
