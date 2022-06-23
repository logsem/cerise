From cap_machine Require Export logrel.
From cap_machine.rules Require Export rules_AddSubLt.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import machine_base.
From cap_machine.rules Require Import rules_base.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma add_sub_lt_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst : RegName) (r1 r2: Z + RegName) (P : D):
    p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (WCap p b e a)
    → (b <= a)%a ∧ (a < e)%a
    → (decodeInstrW w = Add dst r1 r2 \/
       decodeInstrW w = Sub dst r1 r2 \/
       decodeInstrW w = Lt dst r1 r2)
    -> □ ▷ (∀ a0 a1 a2 a3 a4,
             full_map a0
          -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜a0 !! r1 = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[PC:=WCap a1 a2 a3 a4]> a0)
          -∗ na_own logrel_nais ⊤
          -∗ □ (fixpoint interp1) (WCap a1 a2 a3 a4) -∗ interp_conf)
    -∗ (fixpoint interp1) (WCap p b e a)
    -∗ inv (logN.@a) (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0)
    -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜r !! r1 = Some v⌝ → (fixpoint interp1) v)
    -∗ ▷ □ (∀ w : Word, P w -∗ (fixpoint interp1) w)
            ∗ (if decide (writeAllowed_in_r_a (<[PC:=WCap p b e a]> r) a) then ▷ □ (∀ w : Word, (fixpoint interp1) w -∗ P w) else emp)
    -∗ na_own logrel_nais ⊤
    -∗ a ↦ₐ w
    -∗ ▷ P w
    -∗ (▷ (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0) ={⊤ ∖ ↑logN.@a,⊤}=∗ emp)
    -∗ PC ↦ᵣ WCap p b e a
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=WCap p b e a]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        @ ⊤ ∖ ↑logN.@a {{ v, |={⊤ ∖ ↑logN.@a,⊤}=> WP Seq (of_val v)
                                                    {{ v0, ⌜v0 = HaltedV⌝
                                                           → ∃ r1 : Reg, full_map r1 ∧ registers_mapsto r1
                                                                                                        ∗ na_own logrel_nais ⊤ }} }}.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_AddSubLt with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.
      iApply ("IH" $! (<[dst:=_]> (<[PC:=_]> r)) with "[%] [] [Hmap] [$Hown]");
        try iClear "IH"; eauto.
      { intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right). }
      iIntros (ri v Hri Hsv). rewrite insert_commute // lookup_insert_ne // in Hsv; [].
      destruct (decide (ri = dst)); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { by iApply "Hreg". }
      { iModIntro. rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
    }
  Qed.

End fundamental.
