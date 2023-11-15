From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export machine_base logrel register_tactics.
From cap_machine.rules Require Export rules_base rules_AddSubLt.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma add_sub_lt_case (regs : leibnizO Reg) (p : Perm)
    (b e a : Addr) (widc w : Word) (dst : RegName) (r1 r2: Z + RegName) (P : D):
    p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (WCap p b e a)
    → (b <= a)%a ∧ (a < e)%a
    → (decodeInstrW w = Add dst r1 r2 \/
         decodeInstrW w = Sub dst r1 r2 \/
         decodeInstrW w = Lt dst r1 r2)
    -> □ ▷ (∀ regs' p' b' e' a' widc',
            full_map regs'
            -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜r ≠ idc⌝ → ⌜regs' !! r = Some v⌝ → (fixpoint interp1) v)
            -∗ registers_mapsto (<[idc:=widc']> (<[PC:=WCap p' b' e' a']> regs'))
            -∗ na_own logrel_nais ⊤
            -∗ □ (fixpoint interp1) (WCap p' b' e' a') -∗ □ fixpoint interp1 widc' -∗ interp_conf)
      -∗ (fixpoint interp1) (WCap p b e a)
      -∗ (fixpoint interp1) widc
      -∗ inv (logN.@a) (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0)
      -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜r1 ≠ idc⌝ → ⌜regs !! r1 = Some v⌝ → (fixpoint interp1) v)
      -∗ ▷ □ (∀ w : Word, P w -∗ (fixpoint interp1) w)
         ∗ (if decide (writeAllowed_in_r_a (<[idc:=widc]> (<[PC:=WCap p b e a]> regs)) a)
            then ▷ □ (∀ w : Word, (fixpoint interp1) w -∗ P w)
            else emp)
      -∗ na_own logrel_nais ⊤
      -∗ a ↦ₐ w
      -∗ ▷ P w
      -∗ (▷ (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0) ={⊤ ∖ ↑logN.@a,⊤}=∗ emp)
      -∗ PC ↦ᵣ WCap p b e a
      -∗ idc ↦ᵣ widc
      -∗ ([∗ map] k↦y ∈ (delete idc (delete PC regs)), k ↦ᵣ y)
      -∗
         WP Instr Executable
         @ ⊤ ∖ ↑logN.@a {{ v, |={⊤ ∖ ↑logN.@a,⊤}=>
                             WP Seq (of_val v)
                               {{ v0, ⌜v0 = HaltedV⌝ →
                                      ∃ r1 : Reg, full_map r1 ∧ registers_mapsto r1
                                                                  ∗ na_own logrel_nais ⊤
                               }}
                       }}.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].
    iApply (wp_AddSubLt with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. repeat (rewrite lookup_insert_is_Some'; right); eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv as (p''&b''&e''&a''& ? & HPC & Z & Hregs') ; simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext;iIntros "_".
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.


      set (wres := WInt (denote (decodeInstrW w) n1 n2)).
      set (widc' := if (decide (dst = idc)) then wres else widc).
      set (regs' := <[PC:=WCap p'' b'' e'' a'']> (<[dst:=wres]> (<[idc:=widc]> regs))).
      iApply ("IH" $! regs' _ _ _ _ widc' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { intro; cbn; by repeat (rewrite lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hsv).
        destruct (decide (ri = dst)); simplify_map_eq.
        * by rewrite !fixpoint_interp1_eq.
        * iApply "Hreg"; auto.
      }
     { iClear "Hwrite".
        subst widc'. case_decide as Heq; simplify_map_eq.
        + rewrite
            !insert_insert
              (insert_commute _ idc _) //=
              !insert_insert
              (insert_commute _ idc _) //=
              !insert_insert
          ; iFrame.
        + rewrite
            !insert_insert
              (insert_commute _ idc _) //=
              (insert_commute _ idc _) //=
              (insert_commute _ _ PC) //=
              !insert_insert ; iFrame.
      }
      rewrite !fixpoint_interp1_eq //=; destruct Hp as [-> | ->] ;iFrame "Hinv_pc".
      subst widc'.
      destruct (decide (dst = idc)) ; simplify_map_eq; auto.
      by rewrite !fixpoint_interp1_eq.
    }
  Qed.

End fundamental.
