open Ast

type exec_state = Running | Halted | Failed
type word = I of Z.t | Cap of Z.t * Z.t * Z.t * Z.t
type reg_state = word list (* could have been array but lists are immutable which might be beneficial for later features *)
type mem_state = word array (* starting with the list but is subject to change *)
type exec_conf = reg_state * mem_state
type mchn = exec_conf * exec_state

let init_reg_state (addr_max : Z.t) : reg_state =
  let l = List.init 32 (fun _ -> I Z.zero) in
  (* The PC register starts with full permission over the entire memory *)
  let pc_init = Cap ((Encode.encode_perm RWX), Z.zero, addr_max, Z.zero) in
  pc_init :: l

let get_reg (rs : reg_state) (r : regname) : word =
  match r with
  | PC -> List.nth rs 0
  | Reg i -> List.nth rs (i+1)

let upd_reg (rs : reg_state) (r : regname) (w : word) : reg_state =
  let replace i x = List.mapi (fun i' x' -> if i = i' then x else x') rs in
  match r with
  | PC -> replace 0 w
  | Reg i -> replace (i+1) w

let init_mem_state (addr_max : Z.t) (prog : t) : mem_state =
  let a = Array.make (Z.(to_int addr_max)) (I Z.zero) in
  let enc_prog = List.map Encode.encode_statement prog in
  List.iteri (fun i s -> a.(i) <- I s) enc_prog; a

let init_mchn (addr_max : Z.t) (prog : t) : mchn =
  let regs = init_reg_state addr_max in
  let mems = init_mem_state addr_max prog in
  ((regs, mems), Running)
