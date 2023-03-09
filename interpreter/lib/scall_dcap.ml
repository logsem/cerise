open Ast

let in_list (e :'a) (l : 'a list) : bool =
  match (List.find_opt (fun x -> x = e) l) with
  | None -> false
  | Some _ -> true

let all_registers : regname list =
  [PC; STK] @ List.init 32 (fun i -> Reg i)

let rec rclear (regs : regname list) : (statement list) =
  match regs with
  | [] -> []
  | r::regs' -> (Move (r, const 0))::(rclear regs')

let reg_diff (regs : regname list) : regname list=
  (List.filter (fun r -> not (in_list r regs)) all_registers)

let rclear_inv (regs : regname list) : statement list =
  (rclear (reg_diff regs))


let mclearU : statement list =
  let mclear_off_end = 9 in
  let mclear_off_iter = 2 in
  [
    Move (Reg 4, Register STK);
    GetB (Reg 1, Reg 4);
    GetB (Reg 2, Reg 4);
    Sub (Reg 2, Register (Reg 1), Register (Reg 2));
    Lea (Reg 4, Register (Reg 2));
    GetE (Reg 5, Reg 4);
    Sub (Reg 5, Register (Reg 5), CP (Const Z.one));
    Move (Reg 2, Register PC);
    Lea (Reg 2, const mclear_off_end);
    Move (Reg 3, Register PC);
    Lea (Reg 3, const mclear_off_iter);
    (* iter *)
    Lt (Reg 6, Register (Reg 5), Register (Reg 1));
    Jnz (Reg 2, Reg 6);
    StoreU (Reg 4, const 0, const 0);
    Add (Reg 1, Register (Reg 1), const 1);
    Jmp (Reg 3);
    (* end *)
  ] @ rclear [Reg 1; Reg 2; Reg 3; Reg 4; Reg 5; Reg 6]

let pushU r = StoreU (STK, const 0, r)
let popU r =
  [ LoadU (r, STK, const (-1));
    Sub (Reg 1, const 1, const 1);
    Lea (STK, (Register (Reg 1)))
  ]

let reqglob_instrs r =
  [ GetL (Reg 1, r);
    Sub (Reg 1, Register (Reg 1),
         CP (Const (Encode.encode_locality Global)));
    Move (Reg 2, Register PC);
    Lea (Reg 2, Register (Reg 1));
    Jnz (Reg 2, Reg 1);
    Move (Reg 2, Register PC);
    Lea (Reg 2, const 4);
    Jmp (Reg 2);
    Fail;
    Move (Reg 1, const 0);
    Move (Reg 2, const 0);
  ]

let reqperm r (p : Z.t) =
  [ GetP (Reg 1, r);
    Sub (Reg 1, Register (Reg 1), CP (Const p));
    Move (Reg 2, Register PC);
    Lea (Reg 2, const 6);
    Jnz (Reg 2, Reg 1);
    Move (Reg 2, Register PC);
    Lea (Reg 2, const 4);
    Jmp (Reg 2);
    Fail;
    Move (Reg 1, const 0);
    Move (Reg 1, const 0)
  ]

let reqsize r s =
  [ GetP (Reg 1, r);
    GetE (Reg 2, r);
    Sub (Reg 1, Register (Reg 2), Register (Reg 1));
    Lt (Reg 1, CP (Const s), Register (Reg 1));
    Move (Reg 2, Register PC);
    Lea (Reg 2, const 4);
    Jnz (Reg 2, Reg 1);
    Fail
  ]


let prepstack r minsize paramsize =
  reqperm r (Encode.encode_perm URWLX) @
  reqsize r Z.(minsize+paramsize) @
  [ GetB (Reg 1, r);
    GetA (Reg 2, r);
    Sub (Reg 2, Register (Reg 2), CP (Const paramsize));
    Sub (Reg 1, Register (Reg 1), Register (Reg 2));
    Lea (r, Register (Reg 1));
    Move (Reg 1, const 0);
    Move (Reg 2, const 0);
  ]


let scall_prologue radv params : (statement list) =
  let w1 = Encode.encode_statement (Move (Reg 1, Register PC)) in
  let w2 = Encode.encode_statement (Lea (Reg 1, const 6)) in
  let w3 = Encode.encode_statement (Load (STK, Reg 1)) in
  let w4a = Encode.encode_statement (Sub (Reg 1, const 0, const 1)) in
  let w4b = Encode.encode_statement (LoadU (PC, STK, Register (Reg 1))) in
  let epilogue_b =
  [
    (* Push activation record *)
    pushU (CP (Const w1));
    pushU (CP (Const w2));
    pushU (CP (Const w3));
    pushU (CP (Const w4a));
    pushU (CP (Const w4b));
  ] in

  let rdiff = reg_diff (params @ [PC;STK;Reg 0;radv]) in
  let epilogue_e =
    (* push old pc *)
    [
      Move (Reg 1, Register PC) ;
      Lea (Reg 1, const (List.length rdiff + 11 + (2 + (2 * (List.length params))))) ;
      pushU (Register (Reg 1));

      (* push stack pointer *)
      (* Note that the stored r_stk will not be able to read itself, *)
      (*  but that should not be a problem. *)
      pushU (Register STK);
      (* set up protected return pointer *)
      (* since a URWLX capability cannot be made into an E, we have to promote r_t0 first *)
      Move (Reg 0, Register STK);
      PromoteU (Reg 0);
      Lea (Reg 0, const (-7));
      Restrict (Reg 0, CP (Perm  (E, Directed)));
      (* restrict stack capability *)
      GetA (Reg 1, STK);
      GetE (Reg 2, STK);
      SubSeg (STK, Register (Reg 1), Register (Reg 2))
    ] @ rclear_inv (params @ [PC;STK;Reg 0;radv])
  in
  epilogue_b @ epilogue_e


let awkward_example radv =

  let renv = Reg 30 in
  (* let awkward_epilogue_off = 40 in *)

  reqglob_instrs radv @
  prepstack STK (Z.of_int 10) (Z.of_int 10) @
  [ Store (renv, const 0);
    (* Local encapsulation *)
    pushU (Register renv);
    pushU (Register radv)
  ]
  @ scall_prologue radv []
  @ [
    pushU (Register (Reg 0));
    Move (Reg 0, const 0);
    Jmp radv;
    Lea (STK, const (-6))
  ]
  @ popU radv
  @ popU renv
  @ [Store (renv, const 1);
     pushU (Register renv);
    ]
  @ scall_prologue radv []
  @ [
    pushU (Register (Reg 0));
    Jmp radv;
    Lea (STK, const (-6))
  ]
  @ popU renv
    (* Skip the assert *)
  @ rclear_inv [PC; (Reg 0)]
  @ [Jmp (Reg 0)]

let adv_instr = [LoadU (Reg 0, STK, const (-1)); Jmp (Reg 0)]
let ret_instr = [Halt]

(* TODO Well, we don't have the return capability to the caller anymore... Ask Aina *)
(* Also, it sounds that this is not exactly the CC used for the overlay *)
(*  semantic, cf
    https://github.com/logsem/cerise-stack-monotone/blob/master/theories/overlay/call.v *)
