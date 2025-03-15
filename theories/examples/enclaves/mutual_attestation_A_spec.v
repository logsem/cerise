From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import mutual_attestation_code.

Section mutual_attest_A.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context {MA: MutualAttestation}.

  Ltac iHide0 irisH coqH :=
    let coqH := fresh coqH in
    match goal with
    | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
        set (coqH := prop)
    end.

  Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
    iHide0 irisH coqH.


  (* -------------------------------------------------- *)
  (* ------------------ ENCLAVE A---------------------- *)
  (* -------------------------------------------------- *)

  Lemma mutual_attest_A_contract
    v b' e' a' v'
    enclave_data ot :
    let e := (length mutual_attest_enclave_A_code + 1)%Z in
    (ot + 2)%f = Some (ot ^+ 2)%f ->
    (b' < e')%a ->
    (ma_addr_A + e)%a =
    Some (ma_addr_A ^+ e)%a ->
    custom_enclave_inv ma_enclaves_map
    ∗ na_inv logrel_nais (custom_enclaveN.@hash_mutual_attest_A)
        ([[ma_addr_A,(ma_addr_A ^+ e)%a]]↦ₐ{v}
           [[LCap RW b' e' a' v' :: mutual_attest_enclave_A_code]]
         ∗ [[b',e']]↦ₐ{v'}[[LSealRange (true, true) ot (ot ^+ 2)%f ot :: enclave_data]])
    ∗ seal_pred (ot ^+ 1)%f sealed_enclaveA
      -∗ interp (LCap E ma_addr_A
                   (ma_addr_A ^+ e)%a
                   (ma_addr_A ^+ 1)%a v).
  Proof.
    intro e ; subst e.
    iIntros (Hot Hb' He) "#(Henclaves_inv & Hma_inv & HPsign)".
    rewrite fixpoint_interp1_eq /=.
    iIntros (lregs); iNext ; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    rewrite /interp_conf.
    iMod (na_inv_acc with "Hma_inv Hna") as "(>[Hma_code Hma_data]  & Hna & Hclose)"; [solve_ndisj ..|].
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".
    remember ma_addr_A as pc_b in |- * at 7.
    (* remember (ma_addr_A ^+ (91%nat + 1))%a as pc_e in |- * at 4. *)
    (* assert (SubBounds pc_b pc_e ma_addr_A (ma_addr_A ^+ (91%nat + 1))%a) by (subst; solve_addr). *)
  Admitted.

End mutual_attest_A.
