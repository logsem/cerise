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
type mem_state = word MemMap.t
type exec_conf = { reg : reg_state; mem : mem_state } (* using a record to have notation similar to the paper *)
type mchn = exec_state * exec_conf

let init_reg_state (addr_max : int) : reg_state =
  let l = List.init 32 (fun i -> Reg i, I Z.zero) in
  (* The PC register starts with full permission over the entire memory *)
  let pc_init = (PC, Cap (RWX, 0, addr_max, 0)) in
  let seq = List.to_seq (pc_init :: l) in
  RegMap.of_seq seq

let get_reg (r : regname) ({reg ; _} : exec_conf) : word = RegMap.find r reg
let (@!) x y = get_reg x y
  
let upd_reg (r : regname) (w : word) ({reg ; mem} : exec_conf) : exec_conf =
  {reg = RegMap.add r w reg ; mem}


let init_mem_state (prog : t) : mem_state =
  let enc_prog = List.to_seq @@ List.mapi (fun i x -> i, I (Encode.encode_statement x)) prog in
  MemMap.add_seq enc_prog MemMap.empty

let get_mem (addr : int) (conf : exec_conf) : word option = MemMap.find_opt addr conf.mem
let (@?) x y = get_mem x y

let upd_mem (addr : int) (w : word) ({reg ; mem} : exec_conf) : exec_conf = {reg ; mem = MemMap.add addr w mem}

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
  match PC @! conf with
  | Cap (p, b, e, a) -> (Running, upd_reg PC (Cap (p, b, e, a+1)) conf)
  | _ -> (Failed, conf)
let (!>) conf = upd_pc conf

let upd_pc_perm (w : word) =
  match w with
  | Cap (E, b, e, a) -> Cap (RX, b, e, a)
  | _ -> w

let fetch_decode (conf : exec_conf) : statement option =
  let addr =
    match PC @! conf with
    | Cap (_, _, _, a) -> a
    | _ -> raise RuntimeException (* TODO: Fix this ugliness *)
  in
  match get_mem addr conf with
  | Some (I enc) -> Some (Encode.decode_statement enc)
  | _ -> None

let is_pc_valid (conf : exec_conf) : bool =
  match PC @! conf with
  | Cap ((RX|RWX), b, e, a) -> begin
      if b <= a && a < e
      then Option.is_some @@ a @? conf
      else false
    end
  | _ -> false

(* Might change this later since it is a bit too dependent
   on the encode implementation *)
let flowsto (p1 : perm) (p2 : perm) : bool =
  let open Encode in
  let enc1 = encode_perm p1 in
  let enc2 = encode_perm p2 in
  Z.(equal (enc1 lor enc2) enc2)

let exec_single (conf : exec_conf) : mchn =
  let fail_state = (Failed, conf) in
  if is_pc_valid conf 
  then match fetch_decode conf with
    | None -> fail_state
    | Some instr -> begin
        match instr with
        | Fail -> (Failed, conf)
        | Halt -> (Halted, conf)
        | Move (r, c) -> begin
            let w = get_word conf c in
            upd_pc @@ upd_reg r w conf
          end
        | Load (r1, r2) -> begin
            match r2 @! conf with
            | Cap ((RO|RX|RW|RWX), b, e, a) -> begin
                match a @? conf with
                | Some w when (b <= a && a < e) -> !> (upd_reg r1 w conf)
                | _ -> fail_state
              end
            | _ -> fail_state
          end
        | Store (r, c) -> begin
            match r @! conf with
            | Cap ((RW|RWX), b, e, a) when (b <= a && a < e) -> begin
                let w = get_word conf c in
                let c' = upd_mem a w conf in begin
                  match a @? c' with
                  | Some (I z) -> Z.print z; print_newline()
                  | _ -> ()
                end;
                !> (upd_mem a w conf)
              end
            | _ -> fail_state
          end
        | Jmp r -> begin
            let new_pc = upd_pc_perm (r @! conf) in
            (Running, upd_reg PC new_pc conf)
          end
        | Jnz (r1, r2) -> begin
            match r2 @! conf with
            | I i when Z.(equal i zero) -> !> conf
            | _ -> begin
                let new_pc = upd_pc_perm (r1 @! conf) in
                (Running, upd_reg PC new_pc conf)
              end
          end
        | Restrict (r, c) -> begin
            match r @! conf with
            | Cap (p, b, e, a) -> begin
                match get_word conf c with
                | I i -> begin
                    let p' = Encode.decode_perm i in
                    if flowsto p' p
                    then !> (upd_reg r (Cap (p', b, e, a)) conf)
                    else fail_state
                  end
                | _ -> fail_state
              end
            | _ -> fail_state
          end
        | SubSeg (r, c1, c2) -> begin
            match r @! conf with
            | Cap (p, b, e, a) -> begin
                let w1 = get_word conf c1 in
                let w2 = get_word conf c2 in
                match w1, w2 with
                | I i1, I i2 ->
                  let z1 = Z.to_int i1 in
                  let z2 = Z.to_int i2 in
                  if b <= z1 && 0 <= z2 && z2 <= e && p <> E
                  then
                    let w = Cap (p, z1, z2, a) in
                    !> (upd_reg r w conf)
                  else fail_state
                | _ -> fail_state
              end
            | _ -> fail_state
          end
        | Lea (r, c) -> begin
            match r @! conf with
            | Cap (p, b, e, a) -> begin
                let w = get_word conf c in
                match w with
                | I z -> !> (upd_reg r (Cap (p, b, e, a + Z.(to_int z))) conf)
                | _ -> fail_state
              end
            | _ -> fail_state
          end
        | Add (r, c1, c2) -> begin
            let w1 = get_word conf c1 in
            let w2 = get_word conf c2 in
            match w1,w2 with
            | I z1, I z2 -> !> (upd_reg r (I Z.(z1 + z2)) conf)
            | _ -> fail_state
          end
        | Sub (r, c1, c2) -> begin
            let w1 = get_word conf c1 in
            let w2 = get_word conf c2 in
            match w1,w2 with
            | I z1, I z2 -> !> (upd_reg r (I Z.(z1 - z2)) conf)
            | _ -> fail_state
          end
        | GetP (r1, r2) -> begin
            match r2 @! conf with
            | Cap (p, _, _, _) -> !> (upd_reg r1 (I (Encode.encode_perm p)) conf)
            | _ -> fail_state
          end
        | GetB (r1, r2) -> begin
            match r2 @! conf with
            | Cap (_, b, _, _) -> !> (upd_reg r1 (I Z.(~$b)) conf)
            | _ -> fail_state
          end
        | GetE (r1, r2) -> begin
            match r2 @! conf with
            | Cap (_, _, e, _) -> !> (upd_reg r1 (I Z.(~$e)) conf)
            | _ -> fail_state
          end
        | GetA (r1, r2) -> begin
            match r2 @! conf with
            | Cap (_, _, _, a) -> !> (upd_reg r1 (I Z.(~$a)) conf)
            | _ -> fail_state
          end
        | _ -> fail_state       
      end
  else fail_state

let rec run (st, conf : mchn) : mchn =
  match st with
  | Running -> let step = exec_single conf in run step
  | Failed
  | Halted -> (st, conf)
