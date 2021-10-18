open Ast

module MemMap = Map.Make(Int)
module RegMap =
  Map.Make(struct
    type t = regname
    let compare (r1 : t) (r2: t) : int =
      match r1, r2 with
      | PC, PC -> 0
      | PC, Reg _ -> -1
      | Reg _, PC -> 1
      | Reg i, Reg j -> Int.compare i j
  end)
    
type exec_state = Running | Halted | Failed
type word = I of Z.t | Cap of Z.t * Z.t * Z.t * Z.t
type reg_state = word RegMap.t
type mem_state = word MemMap.t
type exec_conf = { reg : reg_state; mem : mem_state } (* using a record to have notation similar to the paper *)
type mchn = exec_conf * exec_state

let init_reg_state (addr_max : Z.t) : reg_state =
  let l = List.init 32 (fun i -> Reg i, I Z.zero) in
  (* The PC register starts with full permission over the entire memory *)
  let pc_init = (PC, Cap ((Encode.encode_perm RWX), Z.zero, addr_max, Z.zero)) in
  let seq = List.to_seq (pc_init :: l) in
  RegMap.of_seq seq

let get_reg (r : regname) (rs : reg_state) : word = RegMap.find r rs

let upd_reg (r : regname) (w : word) (rs : reg_state) : reg_state = RegMap.add r w rs
    
let init_mem_state (prog : t) : mem_state =
  let enc_prog = List.to_seq @@ List.mapi (fun i x -> i, I (Encode.encode_statement x)) prog in
  MemMap.add_seq enc_prog MemMap.empty

let init_mchn (addr_max : Z.t) (prog : t) : mchn =
  let regs = init_reg_state addr_max in
  let mems = init_mem_state prog in
  ({reg = regs; mem = mems} , Running)

(*let get_word (conf : exec_conf) (roc : reg_or_const) : word *)
