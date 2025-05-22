From Coq Require Import ZArith.
From stdpp Require Import base.
From cap_machine Require Export machine_base.
From iris.proofmode Require Import proofmode.

Class MachineParameters := {
    decodeInstr : Z → instr;
    encodeInstr : instr → Z;

    decode_encode_instr_inv :
    forall (i: instr), decodeInstr (encodeInstr i) = i;

    encodePerm : Perm → Z;
    encodePerm_inj : Inj eq eq encodePerm;
    decodePerm : Z → Perm;

    decode_encode_perm_inv :
    forall pl, decodePerm (encodePerm pl) = pl;

    encodeSealPerms : SealPerms → Z;
    encodeSealPerms_inj : Inj eq eq encodeSealPerms;
    decodeSealPerms : Z → SealPerms;

    decode_encode_seal_perms_inv :
    forall pl, decodeSealPerms (encodeSealPerms pl) = pl;

    encodeWordType : Word -> Z;
    encodeWordType_correct :
    forall w w', match w,w' with
            | WCap _ _ _ _, WCap _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealRange _ _ _ _, WSealRange _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealed _ _, WSealed _ _ => encodeWordType w = encodeWordType w'
            | WInt _, WInt _ => encodeWordType w = encodeWordType w'
            | _, _ => encodeWordType w <> encodeWordType w'
            end;

    hash {A : Type} : A ->  Z;
    hash_concat : Z -> Z -> Z;

    hash_inj `{A : Type} : @Inj A Z eq eq hash;
    hash_concat_inj: Inj2 eq eq eq hash_concat;
  }.

(* Lift the encoding / decoding between Z and instructions on Words: simplify
   fail on capabilities. *)

Definition decodeInstrW `{MachineParameters} : Word → instr :=
  fun w =>
    match w with
    | WInt z => decodeInstr z
    | _ => Fail
    end.

Definition encodeInstrW `{MachineParameters} : instr → Word :=
  fun i => WInt (encodeInstr i).

Lemma decode_encode_instrW_inv `{MachineParameters} (i: instr):
  decodeInstrW (encodeInstrW i) = i.
Proof. apply decode_encode_instr_inv. Qed.

Definition encodeInstrsW `{MachineParameters} : list instr → list Word :=
  map encodeInstrW.

Lemma hash_concat_inj' `{MachineParameters} {A: Type} {B: Type} (a a' : A) (b b' : B) :
  hash_concat (hash a) (hash b) = hash_concat (hash a') (hash b') ->
  a =  a' /\ b = b'.
Proof.
  intros Heq.
  destruct (hash_concat_inj (hash a) (hash b) (hash a') (hash b')) as [HeqA HeqB]; eauto.
  edestruct (hash_inj a a'); eauto.
  edestruct (hash_inj b b'); eauto.
Qed.

Section word_type_encoding.
  Definition wt_cap := WCap O 0%a 0%a 0%a.
  Definition wt_sealrange := WSealRange (false, false) 0%ot 0%ot 0%ot.
  Definition wt_sealed := WSealed 0%ot (SCap O 0%a 0%a 0%a).
  Definition wt_int := WInt 0.
End word_type_encoding.

Ltac solve_encodeWordType :=
  match goal with
  | H: _ |- encodeWordType ?x = encodeWordType ?y =>
      try reflexivity
      ; pose proof (encodeWordType_correct x y) as Heq
      ; unfold wt_cap, wt_int, wt_sealrange, wt_cap; simpl in Heq
      ; auto
  end.

Ltac simpl_encodeWordType :=
  match goal with
  | H: _ |- context G [encodeWordType (WCap ?p ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WCap p b e a) = encodeWordType wt_cap) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSealRange ?p ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WSealRange p b e a) = encodeWordType wt_sealrange) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WInt ?n)] =>
      rewrite (_: encodeWordType (WInt n) = encodeWordType wt_int) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSealed ?o ?s)] =>
      rewrite (_: encodeWordType (WSealed o s) = encodeWordType wt_sealed) ; last solve_encodeWordType
  end.

Lemma encodeWordType_correct_cap `{MachineParameters} : forall p b e a p' b' e' a',
  encodeWordType (WCap p b e a) = encodeWordType (WCap p' b' e' a').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_int `{MachineParameters} : forall z z',
  encodeWordType (WInt z) = encodeWordType (WInt z').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sealrange `{MachineParameters} : forall p b e a p' b' e' a',
  encodeWordType (WSealRange p b e a) = encodeWordType (WSealRange p' b' e' a').
Proof.
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sealed `{MachineParameters} : forall o s o' s',
  encodeWordType (WSealed o s) = encodeWordType (WSealed o' s').
  intros; solve_encodeWordType.
Qed.
