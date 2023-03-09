open Ast

exception NotYetImplemented

module MemMap = Map.Make(Int)
module RegMap =
  Map.Make(struct
    type t = regname
    let compare = compare_regname
  end)
    
type exec_state = Running | Halted | Failed
type word = I of Z.t | Cap of perm * locality * int * int * int
type reg_state = word RegMap.t
type mem_state = word MemMap.t
type exec_conf = { reg : reg_state; mem : mem_state } (* using a record to have notation similar to the paper *)
type mchn = exec_state * exec_conf

let init_reg_state (addr_max : int) (stack_opt : bool) (stk_locality : locality) : reg_state =
  let max_heap_addr = addr_max/2 in
  let l = List.init 32 (fun i -> Reg i, I Z.zero) in
  (* The PC register starts with full permission over the entire "heap" segment *)
  let pc_init = (PC, Cap (RWX, Global, 0, max_heap_addr, 0)) in
  (* The stk register starts with full permission over the entire "stack" segment *)
  let stk_init =
    if stack_opt
    then (STK, Cap (URWLX, stk_locality, max_heap_addr, addr_max, max_heap_addr))
    else (STK, I Z.zero)
  in
  let seq = List.to_seq (pc_init :: stk_init :: l) in
  RegMap.of_seq seq

let get_reg (r : regname) ({reg ; _} : exec_conf) : word = RegMap.find r reg
let (@!) x y = get_reg x y
  
let upd_reg (r : regname) (w : word) ({reg ; mem} : exec_conf) : exec_conf =
  {reg = RegMap.add r w reg ; mem}


let init_mem_state (addr_max : int) (prog : t) : mem_state =
  let zeroed_mem =
    (* NB: addr_max is not addressable *)
    let rec loop i m =
      if i >= addr_max then m else loop (i+1) (MemMap.add i (I Z.zero) m) in
    loop 0 MemMap.empty
  in
  let enc_prog =
    List.to_seq @@ List.mapi (fun i x -> i, I (Encode.encode_statement x)) prog in
  MemMap.add_seq enc_prog zeroed_mem

let get_mem (addr : int) (conf : exec_conf) : word option = MemMap.find_opt addr conf.mem
let (@?) x y = get_mem x y

let upd_mem (addr : int) (w : word) ({reg ; mem} : exec_conf) : exec_conf = {reg ; mem = MemMap.add addr w mem}

let init
    (initial_regs : word RegMap.t)
    (initial_mems : word MemMap.t) =
  (Running, {reg = initial_regs; mem = initial_mems})

let get_word (conf : exec_conf) (roc : reg_or_const) : word =
  match roc with
  | Register r -> get_reg r conf
  | CP (Const i) -> I i
  | CP (Perm (p,g)) -> I (Encode.encode_perm_pair p g)
  (* A pair permission-locality is just an integer in the model *)

let upd_pc (conf : exec_conf) : mchn =
  match PC @! conf with
  | Cap (p, g, b, e, a) -> (Running, upd_reg PC (Cap (p, g, b, e, a+1)) conf)
  | _ -> (Failed, conf)
let (!>) conf = upd_pc conf

let upd_pc_perm (w : word) =
  match w with
  | Cap (E, g, b, e, a) -> Cap (RX, g, b, e, a)
  | _ -> w

let fetch_decode (conf : exec_conf) : statement option =
  match PC @! conf with
  | I _ -> None
  | Cap (_, _, _, _, addr) ->
    match get_mem addr conf with
    | Some (I enc) ->
      (try Some (Encode.decode_statement enc)
        with Encode.DecodeException _ -> None)
    | _ -> None

let is_pc_valid (conf : exec_conf) : bool =
  match PC @! conf with
  | Cap ((RX|RWX|RWLX), _, b, e, a) -> begin
      if b <= a && a < e
      then Option.is_some @@ a @? conf
      else false
    end
  | _ -> false

let perm_flowsto (p1 : perm) (p2 : perm) : bool =
  match p1 with
  | O -> true
  | E ->
    (match p2 with
    | E | RX | RWX | RWLX -> true
    | _ -> false)
  | RX ->
    (match p2 with
    | RX | RWX | RWLX -> true
    | _ -> false)
  | RWX ->
    (match p2 with
    | RWX | RWLX -> true
    | _ -> false)
  | RWLX ->
    (match p2 with
    | RWLX -> true
    | _ -> false)
  | RO ->
    (match p2 with
    | E | O | URW | URWL | URWX | URWLX -> false
    | _ -> true)
  | RW ->
    (match p2 with
    | RW | RWX | RWL | RWLX -> true
    | _ -> false)
  | RWL ->
    (match p2 with
     | RWL | RWLX -> true
     | _ -> false)
  | URW ->
    (match p2 with
     | URW | URWL | URWX | URWLX | RW | RWX | RWL | RWLX -> true
     | _ -> false)
  | URWL ->
    (match p2 with
     | URWL | RWL | RWLX | URWLX -> true
     | _ -> false)
  | URWX ->
    (match p2 with
     | URWX | RWX | RWLX | URWLX -> true
     | _ -> false)
  | URWLX ->
    (match p2 with
     | URWLX | RWLX -> true
     | _ -> false)


let locality_flowsto (g1 : locality) (g2 : locality) : bool =
  match g1 with
  | Directed -> true
  | Local ->
    (match g2 with
     | Directed -> false
     | _ -> true)
  | Global ->
    (match g2 with
     | Global -> true
     | _ -> false)

let promote_uperm (p : perm) : perm =
  match p with
  | URW -> RW
  | URWL -> RWL
  | URWX -> RWX
  | URWLX -> RWLX
  | _ -> p

let is_uperm (p : perm) : bool =
  match p with
  | URW | URWL | URWX | URWLX -> true
  | _ -> false

let is_WLperm (p : perm) : bool =
  match p with
  | RWL | RWLX | URWL | URWLX -> true
  | _ -> false

let can_write (p : perm) : bool =
  match p with
  | RW | RWX | RWL | RWLX -> true
  | _ -> false

let can_read (p : perm) : bool =
  match p with
  | RO|RX|RW|RWX|RWL|RWLX-> true
  | _ -> false

let can_read_upto (w : word) =
  match w with
  | I _ -> (Z.to_int Z.zero)
  | Cap (p,_,_,e,a) ->
    if is_uperm p then min a e else e

let exec_single (conf : exec_conf) : mchn =
  let fail_state = (Failed, conf) in
  if is_pc_valid conf 
  then match fetch_decode conf with
    | None -> fail_state
    | Some instr -> begin
        match instr with
        | Fail -> (Failed, conf)
        | Halt -> (Halted, conf)
        | Nop -> begin !> conf end
        | Move (r, c) -> begin
            let w = get_word conf c in
            !> (upd_reg r w conf)
          end
        | Load (r1, r2) -> begin
            match r2 @! conf with
            | Cap (p, _, b, e, a) ->
              if can_read p then
                match a @? conf with
                | Some w when (b <= a && a < e) -> !> (upd_reg r1 w conf)
                | _ -> fail_state
              else fail_state
            | _ -> fail_state
          end
        | Store (r, c) -> begin
            let w = get_word conf c in
            match r @! conf with
            | Cap (p, _, b, e, a) when (b <= a && a < e) ->
              if can_write p then
              (match w with
               | Cap (_, Local,_,_,_) ->
                 if is_WLperm p
                 then !> (upd_mem a w conf)
                 else fail_state
               | Cap (_, Directed,_,_,_) ->
                 if (is_WLperm p && (can_read_upto w <= a))
                 then !> (upd_mem a w conf)
                 else fail_state
               | _ -> !> (upd_mem a w conf))
              else fail_state
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
            | Cap (p, g, b, e, a) -> begin
                match get_word conf c with
                | I i -> begin
                    let (p',g') = Encode.decode_perm_pair i in
                    if (perm_flowsto p' p) && (locality_flowsto g' g)
                    then !> (upd_reg r (Cap (p', g', b, e, a)) conf)
                    else fail_state
                  end
                | _ -> fail_state
              end
            | _ -> fail_state
          end
        | SubSeg (r, c1, c2) -> begin
            match r @! conf with
            | Cap (p, g, b, e, a) -> begin
                let w1 = get_word conf c1 in
                let w2 = get_word conf c2 in
                match w1, w2 with
                | I i1, I i2 ->
                  let z1 = Z.to_int i1 in
                  let z2 = Z.to_int i2 in
                  if b <= z1 && 0 <= z2 && z2 <= e && p <> E
                  then
                    let w = Cap (p, g, z1, z2, a) in
                    !> (upd_reg r w conf)
                  else fail_state
                | _ -> fail_state
              end
            | _ -> fail_state
          end
        | Lea (r, c) -> begin
            match r @! conf with
            | Cap (p, g, b, e, a) -> begin
                let w = get_word conf c in
                match w with
                | I z when p <> E -> !> (upd_reg r (Cap (p, g, b, e, a + Z.(to_int z))) conf)
                | _ -> fail_state
              end
            | _ -> fail_state
          end
        | Add (r, c1, c2) -> begin
            let w1 = get_word conf c1 in
            let w2 = get_word conf c2 in
            match w1, w2 with
            | I z1, I z2 -> !> (upd_reg r (I Z.(z1 + z2)) conf)
            | _ -> fail_state
          end
        | Sub (r, c1, c2) -> begin
            let w1 = get_word conf c1 in
            let w2 = get_word conf c2 in
            match w1, w2 with
            | I z1, I z2 -> !> (upd_reg r (I Z.(z1 - z2)) conf)
            | _ -> fail_state
          end
        | Lt (r, c1, c2) -> begin
            let w1 = get_word conf c1 in
            let w2 = get_word conf c2 in
            match w1, w2 with
            | I z1, I z2 when Z.(lt z1 z2) -> !> (upd_reg r (I Z.one) conf)
            | I _, I _ -> !> (upd_reg r (I Z.zero) conf)
            | _ -> fail_state
          end
        | GetL (r1, r2) -> begin
            match r2 @! conf with
            | Cap (_, g, _, _, _) -> !> (upd_reg r1 (I (Encode.encode_locality g)) conf)
            | _ -> fail_state
          end
        | GetP (r1, r2) -> begin
            match r2 @! conf with
            | Cap (p, _, _, _, _) -> !> (upd_reg r1 (I (Encode.encode_perm p)) conf)
            | _ -> fail_state
          end
        | GetB (r1, r2) -> begin
            match r2 @! conf with
            | Cap (_, _, b, _, _) -> !> (upd_reg r1 (I Z.(~$b)) conf)
            | _ -> fail_state
          end
        | GetE (r1, r2) -> begin
            match r2 @! conf with
            | Cap (_, _, _, e, _) -> !> (upd_reg r1 (I Z.(~$e)) conf)
            | _ -> fail_state
          end
        | GetA (r1, r2) -> begin
            match r2 @! conf with
            | Cap (_, _, _, _, a) -> !> (upd_reg r1 (I Z.(~$a)) conf)
            | _ -> fail_state
          end
        | IsPtr (r1, r2) -> begin
            match r2 @! conf with
            | Cap (_, _, _, _, _) -> !> (upd_reg r1 (I Z.one) conf)
            | _ -> !> (upd_reg r1 (I Z.zero) conf)
          end    
        | LoadU (r1, r2, c) -> begin
            match r2 @! conf with
            | Cap (p, _, b, e, a) ->
              if is_uperm p then
              (match (get_word conf c) with
               | I off when
                   let off = Z.to_int off in
                   (b <= a + off) &&
                   (a + off < a) &&
                   (a <= e)
                 -> (match (a+Z.to_int off) @? conf with
                     | Some w -> !> (upd_reg r1 w conf)
                     | _ -> fail_state)
               | _ -> fail_state)
              else fail_state
            | _ -> fail_state
          end

        | StoreU (r, c1, c2) -> begin
            let woff = get_word conf c1 in
            let w = get_word conf c2 in
            match woff with
            | I off ->
              let off = Z.to_int off in
              (match r @! conf with
               | Cap (p, g, b, e, a) when
                   (b <= a + off) &&
                   (a + off <= a) &&
                   (a <= e) ->
                 if is_uperm p then
                   (match w with
                    | Cap (_, g,_,_,_) when g != Global && (not (is_WLperm p)) ->
                      fail_state
                    | Cap (_, Directed,_,_,_) when (not (can_read_upto w <= a + off)) ->
                      fail_state
                    | _ ->
                        let conf' =
                          if off = 0
                          then (upd_reg r (Cap (p, g, b, e, a+1)) conf)
                          else conf (* if non zero, no increment *)
                        in !> (upd_mem (a+off) w conf'))
                 else fail_state
               | _ -> fail_state)
            | _ -> fail_state
          end

        | PromoteU r ->
          match r @! conf with
          | Cap (p,g,b,e,a) ->
            (match p with
              | URW | URWL | URWX | URWLX ->
                let p' = promote_uperm p in
                let e' = min e a in
                !> (upd_reg r (Cap (p',g,b,e',a)) conf)
                | _ -> fail_state)
          | _ -> fail_state
      end
  else fail_state

let step (m: mchn): mchn option =
  match m with
  | Running, conf -> Some (exec_single conf)
  | (Failed | Halted), _ -> None

let rec run (m : mchn) : mchn =
  match step m with
  | Some m' -> run m'
  | None -> m
