(* Type definitions for the syntax AST *)
type regname = PC | Reg of int
type perm = O | E | RO | RX | RW | RWX | RWL | RWLX
type locality = Global | Local
type const_perm = Const of int | Perm of perm * locality
type reg_or_const = Register of regname | CP of const_perm (* TODO: separate into two types *)
type machine_op
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
  | GetL of regname * regname
  | GetP of regname * regname
  | GetB of regname * regname
  | GetE of regname * regname
  | GetA of regname * regname
  | Fail
  | Halt
type statement = machine_op (* TODO: PseudoOp and LabelDefs *)

type t = statement list

let compare_regname (r1 : regname) (r2: regname) : int =
  match r1, r2 with
  | PC, PC -> 0
  | PC, Reg _ -> -1
  | Reg _, PC -> 1
  | Reg i, Reg j -> Int.compare i j
