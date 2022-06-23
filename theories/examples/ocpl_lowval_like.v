From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers macros fundamental malloc.

(* Show that we can have rules similar to the ones for OCPL's high and low
   locations.

   Our rules are not exactly quite the same: we have some additional noise
   because our definition of lowloc is not primitive but relies on an
   invariants.

   But this shows that there is quite a close connection between OCPL
   lowval/lowloc and our logical relation.
*)

Section rules.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Definition highloc ℓ v :=
    (ℓ ↦ₐ v)%I.

  (* Notice how this corresponds to the definition of [interp] for an RWX
     capability. In other words, [lowloc l] corresponds to the validity of an
     RWX capability pointing to address l. *)
  Definition lowloc ℓ :=
    inv (logN .@ ℓ) (∃ v, ℓ ↦ₐ v ∗ interp v)%I.

  Definition lowval v :=
    interp v.

  Instance lowval_persistent v : Persistent (lowval v).
  Proof. typeclasses eauto. Qed.

  Instance lowloc_persistent ℓ : Persistent (lowloc ℓ).
  Proof. typeclasses eauto. Qed.

  Lemma pointsto_exclusive ℓ v w :
    highloc ℓ v -∗ highloc ℓ w -∗ False.
  Proof. apply addr_dupl_false. Qed.

  Lemma high_not_low ℓ v E :
    ↑logN.@ℓ ⊆ E →
    highloc ℓ v ∗ lowloc ℓ ={E}=∗ False.
  Proof.
    rewrite /highloc /lowloc. iIntros (?) "[H1 H2]".
    unshelve iMod (inv_acc _ _ _ _ with "H2") as "[H ?]". done.
    iDestruct "H" as (?) "[>Ha ?]".
    iDestruct (addr_dupl_false with "H1 Ha") as "%F". done.
  Qed.

  (* alloc_low *)

  (* to be combined with the specification for malloc to obtain alloc_low from
     OCPL *)
  Lemma alloc_low_from_high ℓ v E :
    highloc ℓ v ∗ lowval v ={E}=∗ lowloc ℓ.
  Proof.
    iIntros "[Hl #Hv]".
    iDestruct (inv_alloc (logN .@ ℓ) E (∃ v, ℓ ↦ₐ v ∗ interp v) with "[Hl]")%I as "H".
    { iModIntro. iExists _. iFrame "Hv ∗". }
    iMod "H". iModIntro. done.
  Qed.

  (* load_low *)

  Lemma wp_load_success_same_notinstr_low E r1 pc_p pc_b pc_e pc_a w p b e a pc_a' dq :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    ↑(logN .@ a) ⊆ E →

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WCap p b e a
        ∗ lowloc a }}}
      Instr Executable @ E
      {{{ RET NextIV; ∃ w',
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ r1 ↦ᵣ w'
          ∗ pc_a ↦ₐ{dq} w
          ∗ lowval w' }}}.
  Proof.
    intros. iIntros "(HPC & Hpc_a & Hr1 & #HaI) Hφ".
    rewrite /lowloc.

    iMod (inv_acc with "HaI") as "[Ha Hclose]". done.
    iDestruct "Ha" as (?) "[>Ha #Hva]".
    iApply (wp_load_success_same_notinstr with "[$HPC $Hpc_a $Hr1 $Ha]"); eauto.
    iIntros "!> (HPC & Hr1 & Hpc_a & Ha)".
    iMod ("Hclose" with "[Ha Hva]"). { iModIntro. iExists _. iFrame "Hva ∗". }
    iModIntro. iApply "Hφ". iExists _. iFrame "Hva ∗".
  Qed.

  (* store_low *)

  Lemma wp_store_success_reg_low E pc_p pc_b pc_e pc_a pc_a' w dst src
        p b e a w'' :
     decodeInstrW w = Store dst (inr src) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e a = true →
    ↑(logN .@ a) ⊆ E →

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ src ↦ᵣ w''
        ∗ lowval w''
        ∗ dst ↦ᵣ WCap p b e a
        ∗ lowloc a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ src ↦ᵣ w''
          ∗ dst ↦ᵣ WCap p b e a }}}.
  Proof.
    intros. iIntros "(HPC & Hpc_a & Hsrc & #Hlow & Hdst & #HaI) Hφ".
    rewrite /lowloc /lowval.
    iMod (inv_acc with "HaI") as "[Ha Hclose]". done.
    iDestruct "Ha" as (?) "[>Ha #Hva]".
    iApply (wp_store_success_reg with "[$HPC $Hpc_a $Hsrc $Hdst $Ha]"); eauto.
    iIntros "!> (HPC & Hpc_a & Hsrc & Hdst & Ha)".
    iMod ("Hclose" with "[Ha Hva]"). { iModIntro. iExists _. iFrame "Hlow ∗". }
    iModIntro. iApply "Hφ". iFrame.
  Qed.

End rules.
