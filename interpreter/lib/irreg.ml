(* Type definitions for the registers init *)


type regname = PC | STK | Reg of int
type expr
  = IntLit of int
  | AddOp of expr * expr
  | SubOp of expr * expr
  | MaxAddr
  | StkAddr

type perm = O | E | RO | RX | RW | RWX | RWL | RWLX | URW | URWL | URWX | URWLX
type locality = Global | Local | Directed

(* TODO special addresses: min_addr, max_addr, stk_addr ... *)
type addr = Addr of expr

type word = WI of expr | WCap of perm * locality * addr * addr * addr

type t = (regname * word) list


let rec eval_expr  (e : expr) (max_addr : int) (stk_addr : int) : int =
  match e with
  | IntLit i -> i
  | MaxAddr -> max_addr
  | StkAddr -> stk_addr
  | AddOp (e1, e2) -> (eval_expr e1 max_addr stk_addr) + (eval_expr e2 max_addr stk_addr)
  | SubOp (e1, e2) -> (eval_expr e1 max_addr stk_addr) - (eval_expr e2 max_addr stk_addr)

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

let translate_addr (a : addr) (max_addr : int) (stk_addr : int): int =
  match a with
  | Addr e -> (eval_expr e max_addr stk_addr)


let translate_word (w : word) (max_addr : int) (stk_addr : int): Machine.word =
  match w with
  | WI e -> Machine.I (Z.of_int (eval_expr e max_addr stk_addr))
  | WCap (p,g,b,e,a) ->
    let p = translate_perm p in
    let g = translate_locality g in
    let b = translate_addr b max_addr stk_addr in
    let e = translate_addr e max_addr stk_addr in
    let a = translate_addr a max_addr stk_addr in
    Machine.Cap (p,g,b,e,a)

let rec translate_regfile (regfile : t) (max_addr : int) (stk_addr : int):
  (Machine.word Machine.RegMap.t) =
  let init_regfile =
    Machine.RegMap.empty in
  match regfile with
  | [] -> init_regfile
  | (r,w)::rf ->
    let nrf = translate_regfile rf max_addr stk_addr in
      (Machine.RegMap.add (translate_regname r) (translate_word w max_addr stk_addr) nrf)
