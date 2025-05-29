(* From iris.algebra Require Import frac. *)
(* From iris.proofmode Require Import proofmode. *)
(* Require Import Eqdep_dec List. *)
(* From cap_machine Require Import rules seal_store. *)
(* From cap_machine Require Import logrel fundamental. *)
(* From cap_machine Require Import proofmode. *)
(* From cap_machine Require Import macros_new. *)
(* Open Scope Z_scope. *)
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import assert macros_new.
From cap_machine Require Import attestation_adequacy_template.
From cap_machine Require Import
  trusted_compute_code
  trusted_compute_enclave_spec
  trusted_compute_spec
.
(* From cap_machine Require Import attestation_adequacy_template. *)

(* Instance DisjointList_list_Addr : DisjointList (list Addr). *)
(* Proof. exact (@disjoint_list_default _ _ app []). Defined. *)

Import assert_lib.
Class memory_layout `{MachineParameters} := {
  (* Verifier code *)
  verifier_region_start : Addr;
  verifier_start : Addr;
  verifier_end : Addr;
  verifier_size: (verifier_start + trusted_compute_main_len = Some verifier_end)%a;
  verifier_region_start_offset: (verifier_region_start + 0)%a = Some verifier_start;
  verifier_region: list Addr;
  verifier_region_correct:
    verifier_region = (finz.seq_between verifier_region_start verifier_end);

  (* Adversary code *)
  adv_region_start : Addr;
  adv_start : Addr;
  adv_end : Addr;
  adv_instrs : list Word;
  adv_size : (adv_start + (length adv_instrs) = Some adv_end)%a ;
  adv_region_start_offset: (adv_region_start + 0)%a = Some adv_start;
  adv_region: list Addr;
  adv_region_correct:
    adv_region = (finz.seq_between adv_region_start adv_end);

  (* Assert routine *)
  l_assert_start : Addr;
  l_assert_cap : Addr;
  l_assert_flag : Addr;
  l_assert_end : Addr;

  l_assert_code_size :
    (l_assert_start + length assert_subroutine_instrs)%a = Some l_assert_cap;
  l_assert_cap_size :
    (l_assert_cap + 1)%a = Some l_assert_flag;
  l_assert_flag_size :
    (l_assert_flag + 1)%a = Some l_assert_end;
  l_assert_region: list Addr;
  l_assert_region_correct:
    l_assert_region = (finz.seq_between l_assert_start l_assert_end);

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 1)%a = Some link_table_end;
  link_table_region: list Addr;
  link_table_region_correct:
    link_table_region = (finz.seq_between l_assert_start l_assert_end);

  (* TC enclave *)
  tc_enclave_start : Addr;
  tc_enclave_end : Addr;
  tc_enclave_size : (tc_enclave_start + (length trusted_compute_enclave_instrs + 1))%a =  Some tc_enclave_end;

  regions_disjoints :
  verifier_region ## adv_region ∧
  verifier_region ## l_assert_region ∧
  verifier_region ## link_table_region ∧
  adv_region ## l_assert_region ∧
  adv_region ## link_table_region ∧
  l_assert_region ## link_table_region;
}.

Local Instance trusted_compute_concrete `{memory_layout} : TrustedCompute.
Proof. apply (Build_TrustedCompute tc_enclave_start). Defined.

Program Definition tc_verifier_prog `{memory_layout} : prog :=
  let link_cap := WCap RO link_table_start link_table_end link_table_start in
  let a_data := (verifier_start ^+ trusted_compute_main_code_len)%a in
  let data_cap := WCap RWX verifier_start verifier_end a_data  in
  {| prog_start := verifier_start ;
     prog_end := verifier_end ;
     prog_instrs :=
      (lword_get_word <$> (trusted_compute_main_code 0))
       ++ [link_cap ; data_cap];
     prog_size := _ |}.
Next Obligation.
  intros MP ML *.
  rewrite -verifier_size.
  rewrite app_length.
  rewrite fmap_length.
  by cbn.
Qed.

Definition adv_prog `{memory_layout} : prog :=
  {| prog_start := adv_start ;
     prog_end := adv_end ;
     prog_instrs := adv_instrs ;
     prog_size := adv_size |}.

Program Definition layout `{memory_layout} : assert_library :=
  {| (* assertion fail library *)
     assert_start := l_assert_start;
     assert_cap := l_assert_cap;
     assert_flag := l_assert_flag;
     assert_end := l_assert_end;

     assert_code_size := l_assert_code_size;
     assert_cap_size := l_assert_cap_size;
     assert_flag_size := l_assert_flag_size;
  |}.
Definition AssertLibrary `{memory_layout} := library layout.

(* Program Definition tc_link_table `{memory_layout} : @tbl_priv tc_verifier_prog AssertLibrary := *)
(*   {| prog_lower_bound := verifier_region_start ; *)
(*      tbl_start := link_table_start ; *)
(*      tbl_end := link_table_end ; *)
(*      tbl_size := link_table_size ; *)
(*      tbl_prog_link := verifier_region_start_offset ; *)
(*      tbl_disj := _ *)
(*   |}. *)
(* Next Obligation. *)
(*   intros. simpl. *)
(*   pose proof (regions_disjoint) as Hdisjoint. *)
(*   rewrite !disjoint_list_cons in Hdisjoint |- *. *)
(*   disjoint_map_to_list. set_solver. *)
(* Qed. *)

(* Program Definition adv_table `{memory_layout} : @tbl_pub adv_prog AssertLibrary := *)
(*   {| prog_lower_bound := adv_region_start ; *)
(*      tbl_start := adv_link_table_start ; *)
(*      tbl_end := adv_link_table_end ; *)
(*      tbl_size := adv_link_table_size ; *)
(*      tbl_prog_link := adv_region_start_offset ; *)
(*      tbl_disj := _ *)
(*   |}. *)
(* Next Obligation. *)
(*   intros. simpl. *)
(*   pose proof (regions_disjoint) as Hdisjoint. *)
(*   rewrite !disjoint_list_cons in Hdisjoint |- *. *)
(*   disjoint_map_to_list. set_solver. *)
(* Qed. *)
