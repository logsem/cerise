From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
(* From iris.algebra Require Import frac auth. *)
From cap_machine Require Export cap_lang iris_extra.

Definition Version := nat.

Definition is_scap (w : Word) :=
  match w with
    | WCap p b e a => true
    | WSealed _ (SCap p b e a) => true
    | _ => false end.
Definition get_scap (w : Word) : option Sealable :=
  match w with
    | WCap p b e a => Some (SCap p b e a)
    | WSealed _ (SCap p b e a) => Some (SCap p b e a)
    | _ => None end.
Lemma get_is_scap w sb : get_scap w = Some sb → is_scap w = true.
Proof. unfold get_scap, is_scap. repeat (case_match); auto. all: intro; by exfalso. Qed.

Definition LAddr : Type := Addr * Version.
Inductive LWord :=
| LWCap w p b e a: (get_scap w = Some (SCap p b e a)) → Version → LWord (* Note: add in VMap here if multiple versions are desired *)
| LWNoCap w : (get_scap w = None) → LWord.
Definition lword_get_word (lw : LWord) :=
  match lw with | LWCap w _ _ _ _ _ _ => w | LWNoCap w _ => w end.

Definition VMap : Type := gmap Addr Version.
Definition LReg := gmap RegName LWord.
Definition LMem := gmap LAddr LWord.

Definition lreg_strip (lr : LReg) : Reg :=
 (fun lw : LWord => lword_get_word lw) <$> lr.
Definition is_cur_addr (la : LAddr) (cur_map : gmap Addr Version) : Prop :=
  cur_map !! la.1 = Some la.2.
Definition is_cur_word (lw : LWord) (cur_map : gmap Addr Version) : Prop :=
  match lw with
  | LWCap w _ _ _ a _ v => cur_map !! a = Some v
  | LWNoCap _ _ => True end.

Definition reg_phys_log_corresponds (phr : Reg) (lr : LReg) (cur_map : gmap Addr Version) :=
    lreg_strip lr = phr ∧ map_Forall (λ _ lw, is_cur_word lw cur_map) lr.
Definition mem_phys_log_corresponds (phm : Mem) (lm : LMem) (cur_map : gmap Addr Version) :=
    map_Forall (λ la _ , exists v, cur_map !! la.1 = Some v ) lm (* domain of `lm` is subset of `cur_map`*)
     ∧ map_Forall (λ a v, ∃ lw, lm !! (a,v) = Some lw ∧ phm !! a = Some (lword_get_word lw) ∧ is_cur_word lw cur_map) cur_map (* subset in other direction, and every current address is gc root *).

Definition state_phys_log_corresponds (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (cur_map : gmap Addr Version):=
    reg_phys_log_corresponds phr lr cur_map ∧ mem_phys_log_corresponds phm lm cur_map.

Lemma lreg_insert_respects_corresponds (phr : Reg) (lr : LReg) (cur_map : gmap Addr Version) (r : RegName) (lw : LWord):
  reg_phys_log_corresponds phr lr cur_map → is_cur_word lw cur_map → reg_phys_log_corresponds (<[r := lword_get_word lw]> phr) (<[r := lw]> lr) cur_map.
Admitted.

Lemma lmem_insert_respects_corresponds (phm : Mem) (lm : LMem) (cur_map : gmap Addr Version) (la : LAddr) (lw : LWord):
  mem_phys_log_corresponds phm lm cur_map → is_cur_addr la cur_map → is_cur_word lw cur_map → mem_phys_log_corresponds (<[la.1 := lword_get_word lw]> phm) (<[la := lw]> lm) cur_map.
Admitted.

Lemma lreg_read_iscur (phr : Reg) (lr : LReg) (cur_map : gmap Addr Version) (r : RegName) (lw : LWord):
  reg_phys_log_corresponds phr lr cur_map → lr !! r = Some lw → is_cur_word lw cur_map.
Admitted.

Lemma lmem_read_iscur (phm : Mem) (lm : LMem) (cur_map : gmap Addr Version) (la : LAddr) (lw : LWord):
  mem_phys_log_corresponds phm lm cur_map → is_cur_addr la cur_map → lm !! la = Some lw → is_cur_word lw cur_map.
Admitted.

Lemma cur_word_cur_addr (w : Word) p b e a ne (v : Version) (cur_map : gmap Addr Version):
  is_cur_word (LWCap w p b e a ne v) cur_map → withinBounds a b e = true → is_cur_addr (a,v) cur_map.
Admitted.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invGS Σ;
  mem_gen_memG :> gen_heapGS LAddr LWord Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invGS Σ;
  reg_gen_regG :> gen_heapGS RegName LWord Σ; }.

Definition state_interp_logical (σ : cap_lang.state) `{!memG Σ, !regG Σ} : iProp Σ := ∃ lr lm cur_map , gen_heap_interp lr ∗ gen_heap_interp lm ∗ ⌜state_phys_log_corresponds σ.1 σ.2 lr lm cur_map⌝.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{MachineParameters} `{!memG Σ, !regG Σ} : irisGS cap_lang Σ := {
  iris_invGS := mem_invG;
  state_interp σ _ κs _ := state_interp_logical σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(* Points to predicates for logical registers *)
Notation "r ↦ᵣ{ q } lw" := (mapsto (L:=RegName) (V:=LWord) r q lw)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q } lw") : bi_scope.
Notation "r ↦ᵣ lw" := (mapsto (L:=RegName) (V:=LWord) r (DfracOwn 1) lw) (at level 20) : bi_scope.

(* Points to predicates for logical memory *)
Notation "la ↦ₐ{ q } lw" := (mapsto (L:=LAddr) (V:=LWord) la q lw)
  (at level 20, q at level 50, format "la  ↦ₐ{ q }  lw") : bi_scope.
Notation "la ↦ₐ lw" := (mapsto (L:=LAddr) (V:=LWord) la (DfracOwn 1) lw) (at level 20) : bi_scope.
