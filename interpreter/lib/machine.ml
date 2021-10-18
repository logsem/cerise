open Ast

exception RuntimeException
exception NotYetImplemented

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
(* Undecided on the structure of the capability. This makes the code easier to read,
   but might not be as true to the model as doing: Cap of Z.t * Z.t * Z.t * Z.t *)
type word = I of Z.t | Cap of perm * int * int * int 
type reg_state = word RegMap.t
type mem_state = Z.t MemMap.t
type exec_conf = { reg : reg_state; mem : mem_state } (* using a record to have notation similar to the paper *)
type mchn = exec_state * exec_conf

let init_reg_state (addr_max : int) : reg_state =
  let l = List.init 32 (fun i -> Reg i, I Z.zero) in
  (* The PC register starts with full permission over the entire memory *)
  let pc_init = (PC, Cap (RWX, 0, addr_max, 0)) in
  let seq = List.to_seq (pc_init :: l) in
  RegMap.of_seq seq

let get_reg (r : regname) ({reg ; _} : exec_conf) : word = RegMap.find r reg

let upd_reg (r : regname) (w : word) ({reg ; mem} : exec_conf) : exec_conf =
  {reg = RegMap.add r w reg ; mem}
    
let init_mem_state (prog : t) : mem_state =
  let enc_prog = List.to_seq @@ List.mapi (fun i x -> i, (Encode.encode_statement x)) prog in
  MemMap.add_seq enc_prog MemMap.empty

let get_mem (addr : int) (conf : exec_conf) : Z.t option = MemMap.find_opt addr conf.mem

let upd_mem (addr : int) (i : Z.t) ({reg ; mem} : exec_conf) : exec_conf = {reg ; mem = MemMap.add addr i mem}

let init_mchn (addr_max : int) (prog : t) : mchn =
  let regs = init_reg_state addr_max in
  let mems = init_mem_state prog in
  (Running, {reg = regs; mem = mems})

let get_word (conf : exec_conf) (roc : reg_or_const) : word =
  match roc with
  | Register r -> get_reg r conf
  | CP (Const i) -> I Z.(of_int i)
  | CP (Perm p) -> I (Encode.encode_perm p) (* A permission is just an integer in the model *)

let upd_pc (conf : exec_conf) : mchn =
  match get_reg PC conf with
  | Cap (p, b, e, a) -> (Running, upd_reg PC (Cap (p, b, e, a+1)) conf)
  | _ -> (Failed, conf)

let upd_pc_perm (w : word) =
  match w with
  | Cap (E, b, e, a) -> Cap (RX, b, e, a)
  | _ -> w

let fetch_decode (conf : exec_conf) : statement =
  let addr =
    match get_reg PC conf with
    | Cap (_, _, _, a) -> a
    | _ -> raise RuntimeException
  in
  match get_mem addr conf with
  | Some enc -> Encode.decode_statement enc
  | _ -> raise RuntimeException

let is_pc_valid (conf : exec_conf) : bool =
  match get_reg PC conf with
  | Cap ((RX|RWX), b, e, a) -> begin
      if b <= a && a < e
      then Option.is_some @@ get_mem a conf
      else false
    end
  | _ -> false

let exec_single (conf : exec_conf) : mchn =
  if is_pc_valid conf
  then begin
    let instr = fetch_decode conf in
    match instr with
    | Fail -> (Failed, conf)
    | Halt -> (Halted, conf)
    | Move (r, c) -> begin
        let w = get_word conf c in
        upd_pc @@ upd_reg r w conf
      end
    | _ -> raise NotYetImplemented        
  end  
  else raise RuntimeException

let rec run (st, conf : mchn) : mchn =
  match st with
  | Running -> let step = exec_single conf in run step
  | Failed
  | Halted -> (st, conf)
