(* Type definitions for the syntax AST *)
type regname = PC | Reg of int
and perm = O | E | RO | RX | RW | RWX
and reg_or_const = Register of regname | Const of int | Perm of perm
and machine_op
  = Jmp of regname
  | Jnz of regname * regname
  | Move of regname * reg_or_const
  | Load of regname * regname
  | Store of regname * reg_or_const
  | Add of regname * reg_or_const * reg_or_const
  | Sub of regname * reg_or_const * reg_or_const
  | Lt of regname * reg_or_const * reg_or_const
  | Lea of regname * reg_or_const
  | Restrict of regname * reg_or_const
  | SubSeg of regname * reg_or_const * reg_or_const
  | IsPtr of regname * regname
  | GetP of regname * regname
  | GetB of regname * regname
  | GetE of regname * regname
  | GetA of regname * regname
  | Fail
  | Halt
and statement = machine_op (* TODO: PseudoOp and LabelDefs *)

type t = statement list
