From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_EInit.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Local Hint Resolve finz_seq_between_NoDup list_remove_elem_NoDup : core.

  (** Predicate that defines when the contents of a register can be swept;
      i.e. when the register contains a capability with at least R permissions... *)
  Definition reg_allows_einit
    (lregs : LReg) (lmem : LMem) (r : RegName)
    (b e a : Addr) (v : Version)
    (b' e' a' : Addr) (v' : Version):=
    lregs !! r = Some (LCap RX b e a v)
    ∧ lmem !! (a,v) = Some (LCap RW b' e' a' v').

  (* TODO move stdpp_extra *)
  Fixpoint list_remove_elem_list `{A : Type} `{EqDecision A} (la' la : list A) : list A :=
    match la' with
    | [] => la
    | h::t => list_remove_elem h (list_remove_elem_list t la)
    end.

  Definition code_addresses (a_pc : Addr) (code_la : list Addr)
    := (list_remove_elem a_pc code_la).

  Definition allow_einit_mask_code
    (a_pc : Addr) (v_pc : Version)
    (code_la : list Addr) (code_v : Version)
    : coPset :=
    let pc_mask := (⊤ ∖ ↑logN.@(a_pc, v_pc)) in
    compute_mask_region pc_mask (code_addresses a_pc code_la) code_v.

  Definition data_addresses (a_pc : Addr) (code_la data_la : list Addr)
    := (list_remove_elem_list (a_pc::code_la) data_la).

  Definition allow_einit_mask_data
    (a_pc : Addr) (v_pc : Version)
    (code_la : list Addr) (code_v : Version)
    (data_la : list Addr) (data_v : Version)
    : coPset :=
    let code_mask := allow_einit_mask_code a_pc v_pc code_la code_v in
    compute_mask_region code_mask (data_addresses a_pc code_la data_la) data_v.

  (* Lemma allow_einit_mask_remove_nodup *)
  (*   (a_pc : Addr) (v_pc : Version) (code_la data_la : list Addr) (v : Version) : *)
  (*   NoDup code_la -> *)
  (*   NoDup data_la -> *)
  (*   allow_sweep_mask a_pc v_pc (list_remove_elem a_pc la) v = *)
  (*   allow_sweep_mask a_pc v_pc la v. *)
  (* Proof. *)
  (*   intros HNoDup. *)
  (*   by rewrite /allow_sweep_mask list_remove_elem_idem. *)
  (* Qed. *)

  (* this will help us close the invariant again... *)
  (* it states which properties are enforced on all the lws *)


  Definition region_open_resources
    (a_pc : Addr) (v_pc : Version)
    (code_la : list Addr) (code_v : Version)
    (code_lws : list LWord) (code_Ps : list D)
    (data_la : list Addr) (data_v : Version)
    (data_lws : list LWord) (data_Ps : list D)
    (has_later : bool)
    : iProp Σ :=

    let E := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E1 := allow_einit_mask_code a_pc v_pc code_la code_v in
    let E2 := allow_einit_mask_data a_pc v_pc code_la code_v data_la data_v in

    ([∗ list] lw;Pw ∈ code_lws;code_Ps, (if has_later then ▷ (Pw : D) lw else (Pw : D) lw))
    ∗ ([∗ list] lw;Pw ∈ data_lws;data_Ps, (if has_later then ▷▷ (Pw : D) lw else (Pw : D) lw))

    ∗ ( ⌜ Persistent ([∗ list] lw;Pw ∈ code_lws;code_Ps, (Pw : D) lw) ⌝ ) (* All properties P are persistent *)
    ∗ ( ⌜ Persistent ([∗ list] lw;Pw ∈ data_lws;data_Ps, (Pw : D) lw) ⌝ ) (* All properties P are persistent *)

    ∗ ( if has_later
        then ([∗ list] Pa ∈ code_Ps, read_cond Pa interp)
             ∗ ([∗ list] Pa ∈ data_Ps, ▷ read_cond Pa interp)
               (* the read cond holds *)
        else ([∗ list] Pa ∈ code_Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw))
               ∗ ([∗ list] Pa ∈ data_Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw))
      )%I

    ∗ (▷▷ ([∗ list] a_Pa ∈ zip data_la code_Ps, (interp_ref_inv a_Pa.1 data_v a_Pa.2)) ={E2, E1 }=∗ True)
    ∗ (▷ ([∗ list] a_Pa ∈ zip code_la data_Ps, (interp_ref_inv a_Pa.1 code_v a_Pa.2)) ={E1, E }=∗ True).

  Definition einit_mask_cond
    (lregs : LReg) (lmem : LMem)
    (src : RegName) (b_src e_src a_src : Addr) (v_src : Version)
    (b' e' a' : Addr) (v' : Version)
    (a_pc : Addr) (v_pc : Version) :=
    (* TODO it misses something here: we need conditions over a_pc and b' e' *)
    decide (reg_allows_einit lregs lmem src b_src e_src a_src v_src b' e' a' v'
            /\ (src = PC \/ a_pc ∉ (finz.seq_between b_src e_src))
      ).

  (* Description of what the resources are supposed to look like after opening the region *)
  (*    if we need to, but before closing the region up again*)

  Definition allow_einit_res
    (lregs : LReg) (lmem : LMem)
    (src : RegName)
    (a_pc : Addr) (v_pc : Version)
    (b_code e_code a_code : Addr) (v_code : Version) (code_Ps : list D)
    (b_data e_data a_data : Addr) (v_data : Version) (data_Ps : list D)
    :=

    let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in
    let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in
    let E   := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E1 := allow_einit_mask_code a_pc v_pc code_la v_code in
    let E2 := allow_einit_mask_data a_pc v_pc code_la v_code data_la v_data in

    (⌜read_reg_inr lregs src RX b_code e_code a_code v_code⌝ ∗
     ⌜allows_einit lregs lmem src⌝ ∗
     if einit_mask_cond lregs lmem
          src b_code e_code a_code v_code
          b_data e_data a_data v_data
          a_pc v_pc
     then
      (|={E, E2}=> (* we open this invariant with all the points-tos from b to e *)
         ∃ (code_lws : list LWord) (data_lws : list LWord),
         ⌜ length code_lws = length code_la ⌝
         ∗ ⌜ length data_lws = length data_la ⌝
         ∗ ([∗ map] la↦lw ∈ (logical_region_map code_la code_lws v_code), la ↦ₐ lw) (* here you get all the points-tos *)
         ∗ ([∗ map] la↦lw ∈ (logical_region_map data_la data_lws v_data), la ↦ₐ lw)
         ∗ region_open_resources a_pc v_pc
             code_la v_code code_lws code_Ps
             data_la v_data data_lws data_Ps
             true)%I
     else True)%I.

  (* this does not yet open the invariant *)
  Lemma create_einit_res
    (lregs : LReg) (lmem : LMem)
    (src : RegName)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version)
    (b_code e_code a_code : Addr) (v_code : Version)
    (b_data e_data a_data : Addr) (v_data : Version) :

    let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in
    let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in

    read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src RX b_code e_code a_code v_code
    -> a_pc ∈ finz.seq_between b_pc e_pc
    → (∀ (r : RegName) lw, ⌜r ≠ PC⌝ → ⌜lregs !! r = Some lw⌝ → (fixpoint interp1) lw)
    -∗ interp (LCap p_pc b_pc e_pc a_pc v_pc)
    -∗ (∃ (code_Ps : list D) (data_Ps  : list D),
           ⌜ length code_la = length code_Ps ⌝
           ∗ ⌜length data_la = length data_Ps ⌝
           ∗ allow_einit_res
               (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) lmem src
               a_pc v_pc
               b_code e_code a_code v_code code_Ps
               b_data e_data a_data v_data data_Ps
       ).
  Proof.
  Admitted.

  Definition allow_einit_mem
    (lmem : LMem) (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)

    (b_code e_code a_code : Addr) (v_code : Version) (code_Ps : list D)
    (b_data e_data a_data : Addr) (v_data : Version) (data_Ps : list D)

    (has_later : bool) :=

    let code_la  := code_addresses a_pc (finz.seq_between b_code e_code) in
    let data_la  := data_addresses a_pc code_la (finz.seq_between b_data e_data) in

    (⌜read_reg_inr lregs src RX b_code e_code a_code v_code⌝ ∗
     if einit_mask_cond lregs lmem
          src b_code e_code a_code v_code
          b_data e_data a_data v_data
          a_pc v_pc
     then (∃ (code_lws : list LWord) (data_lws : list LWord),
           ⌜ length code_la = length code_lws ⌝
           ∗ ⌜length data_la = length data_lws ⌝
           ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]>
                       (logical_region_map code_la code_lws v_code
                          ∪ logical_region_map data_la data_lws v_data)⌝
              ∗ region_open_resources a_pc v_pc
                  code_la v_code code_lws code_Ps
                  data_la v_data data_lws data_Ps
                  has_later)
     else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I.

  Lemma einit_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (r : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (EInit r) P.
  Proof.
  Admitted.

End fundamental.
