From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample.
From cap_machine.examples Require Export mkregion_helpers disjoint_regions_tactics.

(* TODO simplify prog and adv_prog, it should be only one record *)
Record prog := MkProg {
  prog_start: Addr;
  prog_end: Addr;
  prog_instrs: list Word;

  prog_size:
    (prog_start + length prog_instrs)%a = Some prog_end;
}.

Definition prog_region (P: prog): gmap Addr Word :=
  mkregion (prog_start P) (prog_end P) (prog_instrs P).

Definition can_address_only (w: Word) (addrs: gset Addr): Prop :=
  match w with
  | WInt _ => True
  | WCap _ b e _ =>
      forall a, (b <= a < e)%a -> a ∈ addrs
end.

Record adv_prog :=
  MkAdvProg {
      adv_start: Addr;
      adv_end: Addr;
      adv_instrs: list Word;

      adv_size:
      (adv_start + length adv_instrs)%a = Some adv_end;
      adv_valid:
      Forall (fun w => is_cap w = false) adv_instrs;
      (* TODO relax the property into the following one *)
      (* Forall *)
      (*   (fun w => can_address_only w *)
      (*            (dom _ (mkregion adv_start adv_end adv_instrs))) *)
      (*   adv_instrs; *)
    }.

Definition adv_region (P: adv_prog): gmap Addr Word :=
  mkregion (adv_start P) (adv_end P) (adv_instrs P).

Lemma prog_region_dom (P: prog):
  dom (gset Addr) (prog_region P) =
  list_to_set (finz.seq_between (prog_start P) (prog_end P)).
Proof.
  rewrite /prog_region /mkregion dom_list_to_map_L fst_zip //.
  rewrite finz_seq_between_length /finz.dist.
  pose proof (prog_size P). solve_addr.
Qed.

Lemma filter_dom_is_dom (m: gmap Addr Word) (d: gset Addr):
  d ⊆ dom (gset Addr) m →
  dom (gset Addr) (filter (λ '(a, _), a ∈ d) m) = d.
Proof.
  intros Hd. eapply set_eq. intros a.
  rewrite (dom_filter_L _ _ d); auto.
  intros. split; intros H.
  { rewrite elem_of_subseteq in Hd |- * => Hd. specialize (Hd _ H).
    eapply elem_of_gmap_dom in Hd as [? ?]. eexists. split; eauto. }
  { destruct H as [? [? ?] ]; auto. }
Qed.

Program Definition all_cores :=
  finz.seq
    (@finz.FinZ machine_base.CoreNum 0 _ _)
    (BinIntDef.Z.to_nat machine_base.CoreNum).
Next Obligation.
  pose machine_base.CorePos. lia.
Qed.
Next Obligation. lia. Qed.

Definition init_cores : list cap_lang.expr :=
  map (fun (i : CoreN) => (i, Seq (Instr Executable))) all_cores.

Definition core_zero := (finz.FinZ 0
                           all_cores_obligation_1
                           all_cores_obligation_2).
Module with_adv.
Definition is_initial_memory
  (mem_frags : list prog) (adv_frags : list adv_prog) (m: gmap Addr Word) :=
  let prog_list := map (fun f => prog_region f) mem_frags in
  let adv_list := map (fun f => adv_region f) adv_frags in
  let region_list := prog_list ∪ adv_list in
  ⋃ region_list ⊆ m /\ disjoint_list_map region_list.

Definition is_initial_registers
  (P : prog) (reg: gmap (CoreN * RegName) Word) (i:CoreN) :=
  reg !! (i, PC) = Some (WCap RWX (prog_start P) (prog_end P) (prog_start P))  (* PC *)
  /\ (∀ (r: RegName), (i, r) ∉ ({[ (i, PC) ]} : gset (CoreN * RegName)) →
                     ∃ (w:Word), reg !! (i, r) = Some w ∧ is_cap w = false).

Definition is_initial_registers_with_adv
  (P A : prog) (r_adv : RegName) (reg: gmap (CoreN * RegName) Word) (i:CoreN) :=
  is_initial_registers P reg i
  /\ reg !! (i, r_adv) = Some (WCap RWX (prog_start A) (prog_end A) (prog_start A)) (* adversary *)
  /\ PC ≠ r_adv.

Definition is_initial_registers_adv
  (P : adv_prog) (reg: gmap (CoreN * RegName) Word) (i:CoreN) :=
  reg !! (i, PC) = Some (WCap RWX (adv_start P) (adv_end P) (adv_start P))  (* PC *)
  /\ (∀ (r: RegName), (i, r) ∉ ({[ (i, PC) ]} : gset (CoreN * RegName)) →
                     ∃ (w:Word), reg !! (i, r) = Some w ∧ is_cap w = false).
End with_adv.


Record lib_entry := MkLibEntry {
  lib_start : Addr;
  lib_end : Addr;
  lib_entrypoint : Addr;
  lib_full_content : gmap Addr Word
}.

Definition entry_points (l: list lib_entry) : list Word :=
  (map (λ entry, WCap E (lib_start entry) (lib_end entry) (lib_entrypoint entry)) l).

Record lib := MkLib {
  pub_libs : list lib_entry;
  priv_libs : list lib_entry
}.

Record tbl {p : prog} {l : list lib_entry} := MkTbl {
  prog_lower_bound : Addr ;
  tbl_start : Addr ;
  tbl_end : Addr ;
  tbl_size : (tbl_start + length l)%a = Some tbl_end ;
  tbl_prog_link : (prog_lower_bound + 1)%a = Some (prog_start p) ;

  tbl_disj : mkregion tbl_start tbl_end (entry_points l) ##ₘ
             mkregion prog_lower_bound (prog_end p) ((WCap RO tbl_start tbl_end tbl_start) :: (prog_instrs p))
}.

Definition tbl_region {p l} (t : @tbl p l) : gmap Addr Word :=
  mkregion (tbl_start t) (tbl_end t) (entry_points l).
Definition prog_lower_bound_region {l} (p : prog) (t : @tbl p l) : gmap Addr Word :=
  mkregion (prog_lower_bound t) (prog_end p) ((WCap RO (tbl_start t) (tbl_end t) (tbl_start t)) :: (prog_instrs p)).
Definition prog_tbl_region {l} (p : prog) (t : @tbl p l) : gmap Addr Word :=
  prog_lower_bound_region p t ∪ tbl_region t.

Lemma prog_lower_bound_region_cons {l} (p : prog) (t : @tbl p l) :
  prog_lower_bound_region p t = <[(prog_lower_bound t):=WCap RO (tbl_start t) (tbl_end t) (tbl_start t)]> (prog_region p)
  ∧ (prog_region p) !! (prog_lower_bound t) = None.
Proof.
  rewrite /prog_lower_bound_region /mkregion.
  pose proof (tbl_prog_link t) as Ht.
  destruct (decide (prog_start p = prog_end p)).
  - rewrite e in Ht. rewrite /prog_region /mkregion finz_seq_between_singleton// e finz_seq_between_empty /=.
    split;auto. solve_addr.
  - pose proof (prog_size p).
    assert (prog_start p <= prog_end p)%a.
    { solve_addr. }
    rewrite (finz_seq_between_cons (prog_lower_bound t));[|solve_addr].
    simpl. rewrite (addr_incr_eq Ht) /=. split;auto.
    rewrite /prog_region /mkregion.
    apply not_elem_of_list_to_map.
    rewrite fst_zip. apply not_elem_of_finz_seq_between. solve_addr.
    rewrite finz_seq_between_length /finz.dist. solve_addr.
Qed.

Fixpoint lib_region (l : list lib_entry) : gmap Addr Word :=
  match l with
  | [] => ∅
  | e :: l => (lib_full_content e) ∪ (lib_region l)
  end.

Lemma lib_region_app l1 l2 :
  lib_region (l1 ++ l2) = lib_region l1 ∪ lib_region l2.
Proof.
  induction l1. by rewrite app_nil_l map_empty_union.
  by rewrite /= IHl1 map_union_assoc.
Qed.

Definition tbl_pub (p : prog) (l : lib) := @tbl p (pub_libs l).
Definition tbl_priv (p : prog) (l : lib) := @tbl p ((pub_libs l) ++ (priv_libs l)).

Module with_lib.

  Definition is_initial_registers
    (P : prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (reg: gmap (CoreN * RegName) Word) (i:CoreN):=
    reg !! (i, PC) = Some (WCap RWX (prog_lower_bound P_tbl) (prog_end P) (prog_start P))
    /\ (∀ (r: RegName), (i, r) ∉ ({[ (i, PC) ]} : gset (CoreN * RegName)) →
                       ∃ (w:Word), reg !! (i, r) = Some w ∧ is_cap w = false).
  
  Definition is_initial_registers_adv (Adv: prog) (Lib : lib)
    (Adv_tbl : tbl_pub Adv Lib) (reg: gmap (CoreN * RegName) Word) (i:CoreN):=
    reg !! (i, PC) = Some (WCap RWX (prog_lower_bound Adv_tbl) (prog_end Adv) (prog_start Adv))
    /\ (∀ (r: RegName), (i, r) ∉ ({[ (i, PC) ]} : gset (CoreN * RegName)) →
                       ∃ (w:Word), reg !! (i, r) = Some w ∧ is_cap w = false).

  (* Definition is_initial_registers_adv *)
  (*   (P : adv_prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (reg: gmap (CoreN * RegName) Word) (i:CoreN):= *)
  (*   reg !! (i, PC) = Some (WCap RWX (prog_lower_bound P_tbl) (prog_end P) (prog_start P)) *)
  (*   /\ (∀ (r: RegName), (i, r) ∉ ({[ (i, PC) ]} : gset (CoreN * RegName)) → *)
  (*                      ∃ (w:Word), reg !! (i, r) = Some w ∧ is_cap w = false). *)

  Definition is_initial_registers_with_adv
    (P Adv: prog) (Lib : lib) (P_tbl : tbl_priv P Lib)
    (Adv_tbl : tbl_pub Adv Lib) (reg: gmap (CoreN*RegName) Word)
    (r_adv: RegName) (i:CoreN) :=
    reg !! (i, PC) = Some (WCap RWX (prog_lower_bound P_tbl) (prog_end P) (prog_start P))
    ∧ reg !! (i, r_adv) = Some (WCap RWX (prog_lower_bound Adv_tbl) (prog_end Adv) (prog_start Adv))
    ∧ PC ≠ r_adv
    ∧ (∀ (r: RegName), (i,r) ∉ ({[ (i,PC) ; (i,r_adv) ]} : gset (CoreN*RegName)) →
                       ∃ (w:Word), reg !! (i,r) = Some w ∧ is_cap w = false).

  Lemma initial_registers_full_map (P : prog) (Lib : lib)
    (P_tbl : tbl_priv P Lib) reg (i:CoreN) :
    is_initial_registers P Lib P_tbl reg  i →
    (∀ r, is_Some (reg !! (i,r))).
  Proof.
    intros (HPC & Hothers) r.
    destruct (decide (r = PC)) as [->|]. by eauto.
    destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
  Qed.

  Lemma initial_registers_adv_full_map (P : prog) (Lib : lib)
    (P_tbl : tbl_pub P Lib) reg (i:CoreN) :
    is_initial_registers_adv P Lib P_tbl reg  i →
    (∀ r, is_Some (reg !! (i,r))).
  Proof.
    intros (HPC & Hothers) r.
    destruct (decide (r = PC)) as [->|]. by eauto.
    destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
  Qed.

  Definition is_initial_memory (P : prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (m: gmap Addr Word) :=
    prog_tbl_region P P_tbl ⊆ m
    ∧ lib_region ((pub_libs Lib) ++ (priv_libs Lib)) ⊆ m
    ∧ prog_tbl_region P P_tbl ##ₘlib_region ((pub_libs Lib) ++ (priv_libs Lib))
    ∧ lib_region (pub_libs Lib) ##ₘlib_region (priv_libs Lib).

  Definition is_initial_memory_with_adv (P Adv: prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (Adv_tbl : tbl_pub Adv Lib) (m: gmap Addr Word) :=
    (prog_tbl_region P P_tbl
       ∪ prog_tbl_region Adv Adv_tbl
       ∪ lib_region ((pub_libs Lib) ++ (priv_libs Lib)))
      ⊆ m
    ∧ prog_tbl_region P P_tbl ##ₘprog_tbl_region Adv Adv_tbl
    ∧ prog_tbl_region P P_tbl ##ₘlib_region ((pub_libs Lib) ++ (priv_libs Lib))
    ∧ prog_tbl_region Adv Adv_tbl ##ₘlib_region ((pub_libs Lib) ++ (priv_libs Lib))
    ∧ lib_region (pub_libs Lib) ##ₘlib_region (priv_libs Lib).

  Definition initial_memory_domain (P : prog) (Lib : lib) (P_tbl : tbl_priv P Lib) : gset Addr :=
    dom (gset Addr) (prog_tbl_region P P_tbl)
      ∪ dom (gset Addr) (lib_region ((pub_libs Lib) ++ (priv_libs Lib))).

  Definition initial_memory_domain_with_adv (P Adv: prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (Adv_tbl : tbl_pub Adv Lib) : gset Addr :=
    dom (gset Addr) (prog_tbl_region P P_tbl)
      ∪ dom (gset Addr) (prog_tbl_region Adv Adv_tbl)
      ∪ dom (gset Addr) (lib_region ((pub_libs Lib) ++ (priv_libs Lib))).

End with_lib.
