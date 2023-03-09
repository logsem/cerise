open Extract

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

let translate_regname (r : regName) : Ast.regname =
  match r with
  | PC -> Ast.PC
  | R n -> Ast.Reg (Z.to_int n)

let translate_sum (s : (z, regName) sum) : Ast.reg_or_const =
match s with
| Inr r -> Ast.Register (translate_regname r)
| Inl z -> Ast.CP (Const z)

let translate_instr (i : instr) : Ast.machine_op =
  match i with
  | Jmp r -> Ast.Jmp (translate_regname r)
  | Jnz (r1, r2) -> Ast.Jnz (translate_regname r1, translate_regname r2)
  | Mov (r, c) -> Ast.Move (translate_regname r,
                             translate_sum c)
  | Load (r1, r2) -> Ast.Load (translate_regname r1,
                               translate_regname r2)
  | Store (r, c) -> Ast.Store (translate_regname r,
                               translate_sum c)
  | Add (r, c1, c2) -> Ast.Add (translate_regname r,
                                translate_sum c1,
                                translate_sum c2)
  | Sub (r, c1, c2) -> Ast.Sub (translate_regname r,
                                translate_sum c1,
                                translate_sum c2)
  | Lt (r, c1, c2) -> Ast.Lt (translate_regname r,
                              translate_sum c1,
                              translate_sum c2)
  | Lea (r, c) -> Ast.Lea (translate_regname r, translate_sum c)
  | Restrict (r, c) -> Ast.Restrict (translate_regname r,
                                     translate_sum c)
  | Subseg (r, c1, c2) -> Ast.SubSeg (translate_regname r,
                                      translate_sum c1,
                                      translate_sum c2)
  | IsPtr (r1, r2) -> Ast.IsPtr (translate_regname r1, translate_regname r2)
  | GetL (r1, r2) -> Ast.GetL (translate_regname r1, translate_regname r2)
  | GetP (r1, r2) -> Ast.GetP (translate_regname r1, translate_regname r2)
  | GetB (r1, r2) -> Ast.GetB (translate_regname r1, translate_regname r2)
  | GetE (r1, r2) -> Ast.GetE (translate_regname r1, translate_regname r2)
  | GetA (r1, r2) -> Ast.GetA (translate_regname r1, translate_regname r2)
  | LoadU (r1, r2, c) -> Ast.LoadU (translate_regname r1,
                                    translate_regname r2,
                                    translate_sum c)
  | StoreU (r, c1, c2) -> Ast.StoreU (translate_regname r,
                                      translate_sum c1,
                                      translate_sum c2)
  | PromoteU r -> Ast.PromoteU (translate_regname r)
  | Fail -> Ast.Fail
  | Halt -> Ast.Halt
  | Nop -> Ast.Nop

let tr_reg (r : Ast.regname) : regName =
  match r with
  | Ast.PC -> PC
  | Ast.STK -> (R (Z.of_int 0))
  | Ast.Reg n -> R (Z.of_int n)

let tr_sum (c : Ast.reg_or_const) : (z, regName) sum =
  match c with
  | Register r -> Inr (tr_reg r)
  | CP cp ->
    match cp with
    | Const n -> Inl n
    | Perm (p,g)->
      let n = Encode.encode_perm_pair p g in
      Inl n

let tr_statement (s : Ast.machine_op) : instr =
  match s with
  | Ast.Jmp r -> Jmp (tr_reg r)
  | Ast.Jnz (r1, r2) -> Jnz (tr_reg r1, tr_reg r2)
  | Ast.Move (r, c) -> Mov (tr_reg r, tr_sum c)
  | Ast.Load (r1, r2) -> Load (tr_reg r1, tr_reg r2)
  | Ast.Store (r, c) -> Store (tr_reg r, tr_sum c)
  | Ast.Add (r, c1, c2) -> Add (tr_reg r, tr_sum c1, tr_sum c2)
  | Ast.Sub (r, c1, c2) -> Sub (tr_reg r, tr_sum c1, tr_sum c2)
  | Ast.Lt (r, c1, c2) -> Lt (tr_reg r, tr_sum c1, tr_sum c2)
  | Ast.Lea (r, c) -> Lea (tr_reg r, tr_sum c)
  | Ast.Restrict (r, c) -> Restrict (tr_reg r, tr_sum c)
  | Ast.SubSeg (r, c1, c2) -> Subseg (tr_reg r, tr_sum c1, tr_sum c2)
  | Ast.IsPtr (r1, r2) -> IsPtr (tr_reg r1, tr_reg r2)
  | Ast.GetL (r1, r2) -> GetL (tr_reg r1, tr_reg r2)
  | Ast.GetP (r1, r2) -> GetP (tr_reg r1, tr_reg r2)
  | Ast.GetB (r1, r2) -> GetB (tr_reg r1, tr_reg r2)
  | Ast.GetE (r1, r2) -> GetE (tr_reg r1, tr_reg r2)
  | Ast.GetA (r1, r2) -> GetA (tr_reg r1, tr_reg r2)
  | Ast.LoadU (r1, r2, c) -> LoadU (tr_reg r1, tr_reg r2, tr_sum c)
  | Ast.StoreU (r, c1, c2) -> StoreU (tr_reg r, tr_sum c1, tr_sum c2)
  | Ast.PromoteU r -> PromoteU (tr_reg r)
  | Ast.Fail -> Fail
  | Ast.Halt -> Halt
  | Ast.Nop -> Nop

let tr_perm (p : Ast.perm) : perm =
  match p with
  | Ast.O -> O
  | Ast.E -> E
  | Ast.RO -> RO
  | Ast.RX -> RX
  | Ast.RW -> RW
  | Ast.RWX -> RWX
  | Ast.RWL -> RWL
  | Ast.RWLX -> RWLX
  | Ast.URW -> URW
  | Ast.URWL -> URWL
  | Ast.URWX -> URWX
  | Ast.URWLX -> URWLX

let tr_loc (g : Ast.locality) : locality =
  match g with
  | Ast.Local -> Local
  | Ast.Global -> Global
  | Ast.Directed -> Directed

let driver = { decodeInstr = (function z ->
tr_statement (Encode.decode_statement z));
  encodeInstr = (function i -> Encode.encode_statement (translate_instr i));
  encodePerm = (function p -> Encode.encode_perm (translate_perm p));
  encodeLoc = (function g -> Encode.encode_locality (translate_locality g));
  decodePermPair = (function z ->
      let (p,g) = Encode.decode_perm_pair z in
      (tr_perm p, tr_loc g));
  encodePermPair = (function p ->
    let (p,g) = p in Encode.encode_perm_pair (translate_perm p) (translate_locality g));
}



let r_stk0 =
  R Z.zero

(** val r_mem : regName **)

let r_mem =
  R (Z.succ Z.zero)

(** val r_fun : regName **)

let r_fun =
  R (Z.succ (Z.succ Z.zero))

(** val compile_value : value -> (z, regName) sum **)

let compile_value = function
| Val_int n -> Inl n
| Val_handle _ -> Inl Z.zero

(** val compile_basic_instr :
    machineParameters -> basic_instruction -> Z.t -> instr list * Z.t **)

let compile_basic_instr h i n =
  match i with
  | I_nop -> ((Nop :: []), n)
  | I_drop -> ([], (sub n (Z.succ Z.zero)))
  | I_const v ->
    let res = R n in
    (((Mov (res, (compile_value v))) :: []), (add n (Z.succ Z.zero)))
  | I_binop (_, b) ->
    let v1 = sub n (Z.succ Z.zero) in
    let v2 = sub n (Z.succ (Z.succ Z.zero)) in
    let res = sub n (Z.succ (Z.succ Z.zero)) in
    ((match b with
      | BOI_add -> (Add ((R res), (r v1), (r v2))) :: []
      | BOI_sub -> (Sub ((R res), (r v2), (r v1))) :: []),
    (sub n (Z.succ Z.zero)))
  | I_get_local i0 ->
    let off = add n (Z.succ Z.zero) in
    (((GetB ((R n), r_stk0)) :: ((Add ((R n), (r n), (Inl
    i0))) :: ((GetA ((R off), r_stk0)) :: ((Sub ((R off),
    (r n), (r off))) :: ((LoadU ((R n), r_stk0, (r off))) :: []))))),
    (add n (Z.succ Z.zero)))
  | I_set_local i0 ->
    let v = sub n (Z.succ Z.zero) in
    let off = add n (Z.succ Z.zero) in
    (((GetB ((R n), r_stk0)) :: ((Add ((R n), (r n), (Inl
    i0))) :: ((GetA ((R off), r_stk0)) :: ((Sub ((R off),
    (r n), (r off))) :: ((StoreU (r_stk0, (r off), (r v))) :: []))))),
    (sub n (Z.succ Z.zero)))
  | I_load _ ->
    let a = sub n (Z.succ Z.zero) in
    let res = sub n (Z.succ Z.zero) in
    (((Lea (r_mem, (r a))) :: ((Load ((R n), r_mem)) :: ((Sub ((R a), (Inl
    Z.zero), (r a))) :: ((Lea (r_mem, (r a))) :: ((Mov ((R res),
    (r n))) :: []))))), n)
  | I_store _ ->
    let v = sub n (Z.succ Z.zero) in
    let a = sub n (Z.succ (Z.succ Z.zero)) in
    (((Lea (r_mem, (r a))) :: ((Store (r_mem, (r v))) :: ((Sub ((R a), (Inl
    Z.zero), (r a))) :: ((Lea (r_mem, (r a))) :: [])))),
    (sub n (Z.succ (Z.succ Z.zero))))
  | I_call i0 ->
    let call_instrs _ r rargs =
      List.map tr_statement
         (Call.scall (translate_regname r) (List.map translate_regname rargs))
    in
    ((app ((Lea (r_fun, (Inl i0))) :: ((Load ((R n), r_fun)) :: []))
        (call_instrs h (R n) [])), n)
  | I_return ->
    let tmp2 = add n (Z.succ Z.zero) in
    let jaddr = add n (Z.succ Z.zero) in
    (((GetB ((R n), r_stk0)) :: ((GetA ((R tmp2), r_stk0)) :: ((Sub ((R n),
    (r n), (r tmp2))) :: ((LoadU ((R jaddr), r_stk0, (r tmp2))) :: ((Jmp (R
    jaddr)) :: []))))), n)
  | I_segload _ ->
    let h0 = sub n (Z.succ Z.zero) in
    let res = sub n (Z.succ Z.zero) in (((Load ((R res), (R h0))) :: []), n)
  | I_segstore _ ->
    let h0 = sub n (Z.succ (Z.succ Z.zero)) in
    let v = sub n (Z.succ Z.zero) in
    (((Store ((R h0), (r v))) :: []), (sub n (Z.succ (Z.succ Z.zero))))
  | I_slice ->
    let h0 = sub n (Z.succ (Z.succ (Z.succ Z.zero))) in
    let o1 = sub n (Z.succ (Z.succ Z.zero)) in
    let o2 = sub n (Z.succ Z.zero) in
    let tmp2 = add n (Z.succ Z.zero) in
    let res = sub n (Z.succ (Z.succ (Z.succ Z.zero))) in
    (((GetB ((R n), (R h0))) :: ((Add ((R o1), (r o1), (r n))) :: ((GetE ((R
    tmp2), (R h0))) :: ((Sub ((R o2), (r tmp2), (r o2))) :: ((Subseg ((R h0),
    (r o1), (r o2))) :: ((Mov ((R res), (r h0))) :: [])))))),
    (sub n (Z.succ (Z.succ Z.zero))))
  | I_handleadd ->
    let h0 = sub n (Z.succ (Z.succ Z.zero)) in
    let off = sub n (Z.succ Z.zero) in
    (((Lea ((R h0), (r off))) :: []), (sub n (Z.succ Z.zero)))
  | _ -> ((Fail :: []), n)

(** val compile :
    machineParameters -> basic_instruction list -> Z.t -> instr list **)

let rec compile h il n =
  match il with
  | [] -> []
  | i :: l ->
    let (ci, cn) = compile_basic_instr h i n in app ci (compile h l cn)
