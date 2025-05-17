From cap_machine Require Export logrel.
From cap_machine.rules Require Export rules_AddSubLt.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import machine_base.
From cap_machine.rules Require Import rules_base.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}
          {contract_enclaves : CustomEnclavesMap}
  .

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).


  Lemma add_sub_lt_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst : RegName) (r1 r2: Z + RegName) (P : D):
    p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (lregs !! x))
    → isCorrectLPC (LCap p b e a v)
    → (b <= a)%a ∧ (a < e)%a
    → (decodeInstrWL lw = Add dst r1 r2 \/
       decodeInstrWL lw = Sub dst r1 r2 \/
       decodeInstrWL lw = Mod dst r1 r2 \/
       decodeInstrWL lw = HashConcat dst r1 r2 \/
       decodeInstrWL lw = Lt dst r1 r2)
    → custom_enclave_inv custom_enclaves
    -∗ (□ ▷ (∀ lregs' p' b' e' a' v',
             full_map lregs'
               -∗ (∀ (r1 : RegName) (lv : LWord),
                   ⌜r1 ≠ PC⌝ → ⌜lregs' !! r1 = Some lv⌝ → (fixpoint interp1) lv)
               -∗ registers_mapsto (<[PC:=LCap p' b' e' a' v']> lregs')
               -∗ na_own logrel_nais ⊤
               -∗ □ (fixpoint interp1) (LCap p' b' e' a' v') -∗ interp_conf))
    -∗ (fixpoint interp1) (LCap p b e a v)
    -∗ inv (logN.@(a,v)) (∃ lw0 : leibnizO LWord, (a,v) ↦ₐ lw0 ∗ P lw0)
    -∗ (∀ (r1 : RegName) lv, ⌜r1 ≠ PC⌝ → ⌜lregs !! r1 = Some lv⌝ → (fixpoint interp1) lv)
    -∗ ▷ □ (∀ lw : LWord, P lw -∗ (fixpoint interp1) lw)
            ∗ (if decide (writeAllowed_in_r_av (<[PC:=LCap p b e a v]> lregs) a v)
               then ▷ □ (∀ lw : LWord, (fixpoint interp1) lw -∗ P lw)
               else emp) ∗ persistent_cond P
    -∗ na_own logrel_nais ⊤
    -∗ (a,v) ↦ₐ lw
    -∗ ▷ P lw
    -∗ (▷ (∃ lw0 : leibnizO LWord, (a,v) ↦ₐ lw0 ∗ P lw0) ={⊤ ∖ ↑logN.@(a,v),⊤}=∗ emp)
    -∗ PC ↦ᵣ LCap p b e a v
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=LCap p b e a v]> lregs), k ↦ᵣ y)
    -∗ WP Instr Executable
        @ ⊤ ∖ ↑logN.@(a,v)
        {{ v0, |={⊤ ∖ ↑logN.@(a,v),⊤}=>
             WP Seq (of_val v0)
               {{ v1, ⌜v1 = HaltedV⌝ →
                      ∃ lregs0 : LReg,
                        full_map lregs0 ∧ registers_mapsto lregs0 ∗ na_own logrel_nais ⊤
               }}
        }}.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#HsysInv #IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_AddSubLt with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ n1 n2 Harg1 Harg2 Hincr | Hfail  ]; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementLPC_inv as (p''&b''&e''&a''&v''& ? & HPC & Z & Hregs'); simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro]. iNext;iIntros "_".
      assert (dst <> PC) as HdstPC by (intros ->; by simplify_map_eq).
      simplify_map_eq.
      iApply ("IH" $! (<[dst:=_]> (<[PC:=_]> lregs)) with "[%] [] [Hmap] [$Hown]");
        try iClear "IH"; eauto.
      { intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right). }
      iIntros (ri v Hri Hsv).
      rewrite insert_commute // lookup_insert_ne // in Hsv; [].
      destruct (decide (ri = dst)); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { by iApply "Hreg". }
      { iModIntro. rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
    }
  Qed.

End fundamental.
