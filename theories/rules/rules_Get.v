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
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  (* Generalized denote function, since multiple cases result in similar success *)
  Definition denote (i: instr) (w : Word): option Z :=
    match w with
    | WCap p b e a =>
      match i with
      | GetP _ _ => Some (encodePerm p)
      | GetB _ _ => Some (b:Z)
      | GetE _ _ => Some (e:Z)
      | GetA _ _ => Some (a:Z)
      | _ => None
      end
    | WSealRange p b e a =>
      match i with
      | GetP _ _ => Some (encodeSealPerms p)
      | GetB _ _ => Some (b:Z)
      | GetE _ _ => Some (e:Z)
      | GetA _ _ => Some (a:Z)
      | _ => None
      end
    | _ => None end.

  Global Arguments denote : simpl nomatch.

  Definition is_Get (i: instr) (dst src: RegName) :=
    i = GetP dst src ∨
    i = GetB dst src ∨
    i = GetE dst src ∨
    i = GetA dst src.

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
      | _ => 0%Z
      end.
  Lemma denote_cap_denote i p b e a z src dst: is_Get i src dst → denote_cap i p b e a = z → denote i (WCap p b e a) = Some z.
  Proof. unfold denote_cap, denote, is_Get. intros [-> | [-> | [-> | ->]]] ->; done. Qed.

  Definition denote_seal (i: instr) (p : SealPerms) (b e a : OType): Z :=
      match i with
      | GetP _ _ => (encodeSealPerms p)
      | GetB _ _ => b
      | GetE _ _ => e
      | GetA _ _ => a
      | _ => 0%Z
      end.
  Lemma denote_seal_denote i (p : SealPerms) (b e a : OType) z src dst: is_Get i src dst → denote_seal i p b e a = z → denote i (WSealRange p b e a) = Some z.
  Proof. unfold denote_seal, denote, is_Get. intros [-> | [-> | [-> | ->]]] ->; done. Qed.

  (* TODO move in logical_mapsto *)
  Definition lz z : LWord := LWNoCap (WInt z) eq_refl.

  Inductive Get_failure (i: instr) (regs: LReg) (dst src: RegName) :=
    | Get_fail_src_denote (w : LWord):
        regs !! src = Some w →
        denote i (lword_get_word w) = None →
        Get_failure i regs dst src
    | Get_fail_overflow_PC (w : LWord) z:
        regs !! src = Some w →
        denote i (lword_get_word w) = Some z →
        incrementPC (lreg_strip (<[ dst := lz z ]> regs)) = None →
        Get_failure i regs dst src.

  Inductive Get_spec (i: instr) (regs: LReg) (dst src: RegName) (regs': LReg): cap_lang.val -> Prop :=
    | Get_spec_success (w : LWord) z:
        regs !! src = Some w →
        denote i (lword_get_word w) = Some z →
        incrementPC (lreg_strip (<[ dst := lz z ]> regs)) =
          Some (lreg_strip regs') →
        Get_spec i regs dst src regs' NextIV
    | Get_spec_failure:
        Get_failure i regs dst src →
        Get_spec i regs dst src regs' FailedV.

  (* TODO move in logical_mapsto or rules_bases *)
  Lemma indom_lregs_incl D (lregs lregs': LReg) :
    D ⊆ dom lregs →
    lregs ⊆ lregs' →
    ∀ r, r ∈ D →
         ∃ (w:LWord), (lregs !! r = Some w) ∧ (lregs' !! r = Some w).
  Proof.
    intros * HD Hincl rr Hr.
    assert (is_Some (lregs !! rr)) as [w Hw].
    { eapply @elem_of_dom with (D := gset RegName). typeclasses eauto.
      eapply elem_of_subseteq; eauto. }
    exists w. split; auto. eapply lookup_weaken; eauto.
  Qed.

  Lemma wp_Get Ep lpc pc_p pc_b pc_e pc_a lpc_a lw w get_i dst src regs :
    lword_get_word lpc = WCap pc_p pc_b pc_e pc_a ->
    lword_get_word lw = w ->
    laddr_get_addr lpc_a = pc_a ->
    lword_get_version lpc = Some (laddr_get_version lpc_a) ->

    decodeInstrW w = get_i →
    is_Get get_i dst src →

    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some lpc →
    regs_of get_i ⊆ dom regs →

    {{{ ▷ lpc_a ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Get_spec (decodeInstrW w) regs dst src regs' retv ⌝ ∗
        lpc_a ↦ₐ lw ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hlpc Hlw Hpc_a Hversions Hdecode Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hmap") as "#H".
    iDestruct "H" as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hlpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    2: eapply state_phys_corresponds_reg; eauto.
    2: {
      eapply state_phys_corresponds_mem; eauto.
      destruct HLinv as [HregInv _]; simpl in *.
      apply isCorrectPC_withinBounds in Hvpc.
      eapply reg_corresponds_cap_cur_addr; eauto.
    }
    unfold exec in Hstep.

    specialize (indom_lregs_incl _ regs lr Dregs Hregs) as Hri.
    erewrite regs_of_is_Get in Hri; eauto.
    destruct (Hri src) as [lwsrc [H'lsrc Hlsrc]]; first by set_solver+.
    destruct (Hri dst) as [lwdst [H'ldst Hldst]]; first by set_solver+.

    (* Extract information about physical words in src and dst *)
    set (wsrc := lword_get_word lwsrc).
    set (wdst := lword_get_word lwdst).
    (* TODO could be a lemma *)
    assert ( reg !! src = Some wsrc ) as Hsrc.
    { destruct HLinv as [[Hstrips Hcurreg] _].
      rewrite <- Hstrips.
      unfold lreg_strip.
      apply lookup_fmap_Some. eexists; eauto.
    }
    assert ( reg !! dst = Some wdst ) as Hdst.
    { destruct HLinv as [[Hstrips Hcurreg] _].
      rewrite <- Hstrips.
      unfold lreg_strip.
      apply lookup_fmap_Some. eexists; eauto.
    }

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

    destruct (incrementPC (lreg_strip (<[ dst := lz z ]> regs)))
      as [regs'|] eqn:Hregs'
    ; pose proof Hregs' as H'regs'; cycle 1.
    { (* Failure: incrementing PC overflows *)
      apply incrementPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hregs'.
      eapply updatePC_fail_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in Hregs'.
      2: { admit.
        (* apply lookup_insert_is_Some'. ; eauto. *)
        }
      2: by apply map_fmap_mono; apply insert_mono ; eauto.
      simplify_pair_eq.
      rewrite ( _ :
         (λ lw : LWord, lword_get_word lw) <$> <[dst:=lz z]> lr = <[dst:=WInt z]> reg
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

    eapply (incrementPC_success_updatePC _ mem etable enumcur) in Hregs'
        as (p' & b' & e' & a'' & a_pc' & HPC'' & Hpc_a' & HuPC & ->).
    eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC.
    2: by apply map_fmap_mono; apply insert_mono ; eauto.
    rewrite ( _ :
              (λ lw : LWord, lword_get_word lw) <$> <[dst:=lz z]> lr = <[dst:=WInt z]> reg
            ) in HuPC; cycle 1.
    { destruct HLinv as [[Hstrips Hcurreg] _].
      rewrite -Hstrips fmap_insert -/(lreg_strip lr); auto. }

    rewrite HuPC in Hstep.
    simplify_pair_eq. iFrame.

    assert (exists (v : Version), lword_get_version lpc = Some v) as [v_lpc Hv_lpc].
    { admit. }
    set (lpc' := (LWCap (WCap p' b' e' a_pc') p' b' e' a_pc' eq_refl v_lpc)).
    iMod ((gen_heap_update_inSepM _ _ dst (lz z)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC lpc') with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { admit. }
    iFrame. iModIntro.
    iSplitR "Hφ Hmap Hpc_a"; cycle 1.
    - iApply "Hφ" ; iFrame ; iPureIntro; econstructor; eauto.
      rewrite /incrementPC HPC'' Hpc_a' /lreg_strip fmap_insert; eauto.

    - iExists _, lm, cur_map; iFrame; auto.
      destruct HLinv as [[Hstrips Hcur_reg] HmemInv]; cbn in *.
      iPureIntro; econstructor; eauto.
      split.
      by rewrite -Hstrips /lreg_strip 2!fmap_insert /= .
      clear HuPC HH Hri Hwsrc Hsrc Hlsrc.
      apply map_Forall_insert_2 ; [ | apply map_Forall_insert_2; auto].
      subst lpc'; cbn.
      (* TODO Tt misses an information here: in cur_map, I don't know
         whether a_pc'' = a'' + 1 is valid, so i'm stuck *)
  Abort.

  (* Note that other cases than WCap in the PC are irrelevant, as that will result in having an incorrect PC *)
  Lemma wp_Get_PC_success E get_i dst pc_p pc_b pc_e pc_a w wdst pc_a' z :
    decodeInstrW w = get_i →
    is_Get get_i dst PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (WCap pc_p pc_b pc_e pc_a) = Some z →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_same_success E get_i r pc_p pc_b pc_e pc_a w wr pc_a' z:
    decodeInstrW w = get_i →
    is_Get get_i r r →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wr = Some z →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_success E get_i dst src pc_p pc_b pc_e pc_a w wsrc wdst pc_a' z :
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wsrc = Some z →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
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

Global Hint Resolve is_Get_GetP : core.
Global Hint Resolve is_Get_GetB : core.
Global Hint Resolve is_Get_GetE : core.
Global Hint Resolve is_Get_GetA : core.
