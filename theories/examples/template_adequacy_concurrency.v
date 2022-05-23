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
  ∧ dom (gset (CoreN*RegName)) reg ⊆ (set_map (fun r => (i,r)) all_registers_s)
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
  ∧ dom (gset (CoreN*RegName)) reg ⊆ (set_map (fun r => (i,r)) all_registers_s)
  /\ (∀ (r: RegName), (i, r) ∉ ({[ (i, PC) ]} : gset (CoreN * RegName)) →
                     ∃ (w:Word), reg !! (i, r) = Some w ∧ is_cap w = false).
End with_adv.
