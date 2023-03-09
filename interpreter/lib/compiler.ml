open Extract
open Convert

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
