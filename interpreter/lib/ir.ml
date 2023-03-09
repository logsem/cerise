(* Type definitions for the syntax AST *)

exception UnknownLabelException of string

type regname = PC | STK | Reg of int
type expr
  = IntLit of int
  | Label of string
  | AddOp of expr * expr
  | SubOp of expr * expr

type perm = O | E | RO | RX | RW | RWX | RWL | RWLX | URW | URWL | URWX | URWLX
type locality = Global | Local | Directed
type const_perm = Const of expr | Perm of perm * locality
type reg_or_const = Register of regname | CP of const_perm (* TODO: separate into two types *)
type machine_op
  =
  | Nop
  | Jmp of regname
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
  | LoadU of regname * regname * reg_or_const
  | StoreU of regname * reg_or_const * reg_or_const
  | PromoteU of regname
  | Fail
  | Halt
  | Lbl of string
type statement = machine_op (* TODO: PseudoOp and LabelDefs *)

type t = statement list
type env = (string * int) list

let rec compute_env (i : int) (prog : t) (envr : env) : env =
  match prog with
  | [] -> envr
  | (Lbl s) :: p -> compute_env (i+1) p ((s, i - (List.length envr)) :: envr)
  | _ :: p -> compute_env (i+1) p envr

let rec eval_expr (envr : env) (e : expr) : Z.t =
  match e with
  | IntLit i -> (Z.of_int i)
  | Label s -> begin
      match List.find_opt (fun p -> (fst p) = s) envr with
      | Some (_,i) -> (Z.of_int i)
      | None -> raise (UnknownLabelException s)
    end
  | AddOp (e1, e2) -> Z.((eval_expr envr e1) + (eval_expr envr e2))
  | SubOp (e1, e2) -> Z.((eval_expr envr e1) - (eval_expr envr e2))

let translate_perm (p : perm) : Ast.perm =
  match p with
  | O -> Ast.O
  | E -> Ast.E
  | RO -> Ast.RO
  | RX -> Ast.RX
  | RW -> Ast.RW
  | RWX -> Ast.RWX
  | RWL -> Ast.RWL
  | RWLX -> Ast.RWLX
  | URW -> Ast.URW
  | URWL -> Ast.URWL
  | URWX -> Ast.URWX
  | URWLX -> Ast.URWLX

let translate_locality (g : locality) : Ast.locality =
  match g with
  | Local -> Ast.Local
  | Global -> Ast.Global
  | Directed -> Ast.Directed

let translate_regname (r : regname) : Ast.regname =
  match r with
  | PC -> Ast.PC
  | STK -> Ast.STK
  | Reg i -> Ast.Reg i

let translate_const_perm (envr : env) (cp : const_perm) : Ast.const_perm =
  match cp with
  | Const e -> Ast.Const (eval_expr envr e)
  | Perm (p,g) -> Ast.Perm (translate_perm p, translate_locality g)

let translate_reg_or_const (envr : env) (roc : reg_or_const) : Ast.reg_or_const =
  match roc with
  | Register r -> Ast.Register (translate_regname r)
  | CP cp -> Ast.CP (translate_const_perm envr cp)

let translate_instr (envr : env) (instr : machine_op) : Ast.machine_op =
  match instr with
  | Jmp r -> Ast.Jmp (translate_regname r)
  | Jnz (r1, r2) -> Ast.Jnz (translate_regname r1, translate_regname r2)
  | Move (r, c) -> Ast.Move (translate_regname r,
                             translate_reg_or_const envr c)
  | Load (r1, r2) -> Ast.Load (translate_regname r1,
                               translate_regname r2)
  | Store (r, c) -> Ast.Store (translate_regname r,
                               translate_reg_or_const envr c)
  | Add (r, c1, c2) -> Ast.Add (translate_regname r,
                                translate_reg_or_const envr c1,
                                translate_reg_or_const envr c2)
  | Sub (r, c1, c2) -> Ast.Sub (translate_regname r,
                                translate_reg_or_const envr c1,
                                translate_reg_or_const envr c2)
  | Lt (r, c1, c2) -> Ast.Lt (translate_regname r,
                              translate_reg_or_const envr c1,
                              translate_reg_or_const envr c2)
  | Lea (r, c) -> Ast.Lea (translate_regname r, translate_reg_or_const envr c)
  | Restrict (r, c) -> Ast.Restrict (translate_regname r,
                                     translate_reg_or_const envr c)
  | SubSeg (r, c1, c2) -> Ast.SubSeg (translate_regname r,
                                      translate_reg_or_const envr c1,
                                      translate_reg_or_const envr c2)
  | IsPtr (r1, r2) -> Ast.IsPtr (translate_regname r1, translate_regname r2)
  | GetL (r1, r2) -> Ast.GetL (translate_regname r1, translate_regname r2)
  | GetP (r1, r2) -> Ast.GetP (translate_regname r1, translate_regname r2)
  | GetB (r1, r2) -> Ast.GetB (translate_regname r1, translate_regname r2)
  | GetE (r1, r2) -> Ast.GetE (translate_regname r1, translate_regname r2)
  | GetA (r1, r2) -> Ast.GetA (translate_regname r1, translate_regname r2)
  | LoadU (r1, r2, c) -> Ast.LoadU (translate_regname r1,
                                    translate_regname r2,
                                    translate_reg_or_const envr c)
  | StoreU (r, c1, c2) -> Ast.StoreU (translate_regname r,
                                      translate_reg_or_const envr c1,
                                      translate_reg_or_const envr c2)
  | PromoteU r -> Ast.PromoteU (translate_regname r)
  | Fail -> Ast.Fail
  | Halt -> Ast.Halt
  | Nop -> Ast.Nop
  | Lbl s -> raise (UnknownLabelException s)

let rec translate_prog_aux (envr : env) (prog : t) : Ast.t =
  match prog with
  | [] -> []
  | (Lbl _) :: p -> translate_prog_aux envr p
  | instr :: p -> (translate_instr envr instr) :: (translate_prog_aux envr p)

let translate_prog (prog : t) : Ast.t =
  let envr = compute_env 0 prog [] in
  translate_prog_aux envr prog
