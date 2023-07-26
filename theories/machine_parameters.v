From Coq Require Import ZArith.
From stdpp Require Import base.
From cap_machine Require Export machine_base.

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
    decodeWordType : Z -> Word;
    encodeWordType_correct :
    forall w w', match w,w' with
            | WCap _ _ _ _, WCap _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealRange _ _ _ _, WSealRange _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealed _ _, WSealed _ _ => encodeWordType w = encodeWordType w'
            | WInt _, WInt _ => encodeWordType w = encodeWordType w'
            | _, _ =>encodeWordType w <> encodeWordType w'
            end;
    decode_encode_word_type_inv :
    forall w, decodeWordType (encodeWordType w) = w;
    (* TODO I think that we need more hypetheses about the encoding/decoding of
     word type: we do need some sort injectivity, modulo word type *)
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

(* TODO solve_encodeWordType tactic ?*)
Lemma encodeWordType_correct_cap `{MachineParameters} : forall p b e a p' b' e' a',
  encodeWordType (WCap p b e a) = encodeWordType (WCap p' b' e' a').
  intros
  ; match goal with
    | H: _ |- encodeWordType ?x = encodeWordType ?y =>
        pose proof (encodeWordType_correct x y) as Heq ; simpl in Heq ; auto
    end.
Qed.

Lemma encodeWordType_correct_int `{MachineParameters} : forall z z',
  encodeWordType (WInt z) = encodeWordType (WInt z').
  intros
  ; match goal with
    | H: _ |- encodeWordType ?x = encodeWordType ?y =>
        pose proof (encodeWordType_correct x y) as Heq ; simpl in Heq ; auto
    end.
Qed.

Lemma encodeWordType_correct_sealrange `{MachineParameters} : forall p b e a p' b' e' a',
  encodeWordType (WSealRange p b e a) = encodeWordType (WSealRange p' b' e' a').
Proof.
  intros
  ; match goal with
    | H: _ |- encodeWordType ?x = encodeWordType ?y =>
        pose proof (encodeWordType_correct x y) as Heq ; simpl in Heq ; auto
    end.
Qed.

Lemma encodeWordType_correct_sealed `{MachineParameters} : forall o s o' s',
  encodeWordType (WSealed o s) = encodeWordType (WSealed o' s').
  intros
  ; match goal with
    | H: _ |- encodeWordType ?x = encodeWordType ?y =>
        pose proof (encodeWordType_correct x y) as Heq ; simpl in Heq ; auto
    end.
Qed.
