open Notty
open Notty.Infix

type side = Left | Right
(* ui components *)

module type MachineConfig = sig val addr_max : int end

module MkUi (Cfg: MachineConfig) = struct

  module Perm = struct
    let width = 5
    let ui ?(attr = A.empty) (p: Ast.perm) =
      I.hsnap ~align:`Left width
        (I.string attr (Pretty_printer.string_of_perm p))
  end

  module Locality = struct
    let width = 6
    let ui ?(attr = A.empty) (g: Ast.locality) =
      I.hsnap ~align:`Left width
        (I.string attr (Pretty_printer.string_of_locality g))
    end

  module Addr = struct
    (* width of an address as a number of hex digits *)
    let width =
      1 + int_of_float (floor @@ log (float Cfg.addr_max) /. log 16.)

    let to_hex (a: int): string =
      (* pad on the left with zeroes up to [width] chars *)
      Printf.sprintf "%0*X" width a

    let ui ?(attr = A.empty) (a: int) =
      I.string attr (to_hex a)
  end

  module Addr_range = struct
    (* an address range is printed as either:
           XXXX-XXXX
       or  XX[XX-XX]   (in case of common higher-bits),
       whichever is shortest *)
    let width =
      2 * Addr.width + 1

    let ui ?(attr = A.empty) (b, e) =
      let bs = Addr.to_hex b in
      let es = Addr.to_hex e in
      (* determine whether we should use the XXXX-XXXX or XX[XX-XX] format *)
      let rec find_prefix i =
        if i = String.length bs then
          (* b = e, default to the default printing scheme *)
          None
        else if bs.[i] = es.[i] then
          find_prefix (i+1)
        else if i >= 2 then
          Some i
        else None in
      I.hsnap ~align:`Left width @@
      match find_prefix 0 with
      | None ->
        Addr.ui ~attr b <|> I.string attr "-" <|> Addr.ui ~attr e
      | Some i ->
        let prefix = String.sub bs 0 i in
        let bs = String.sub bs i (Addr.width - i) in
        let es = String.sub es i (Addr.width - i) in
        I.string attr (prefix ^ "[" ^ bs ^ "-" ^ es ^ "]")
  end

  module Int = struct
    (* those can be of arbitrary size in principle. We ask for a max width and
       add an ellipsis (..) in the middle of the number if its representation
       would exceed [max_width]. *)
    let ui max_width (z: Z.t) =
      assert (max_width >= 4);
      let s = Z.format "%X" z in
      if String.length s > max_width then (
        let ndigits = max_width - 2 (* ".." *) in
        let ndigits_l = ndigits / 2 and ndigits_r = ndigits / 2 + ndigits mod 2 in
        String.sub s 0 ndigits_l ^ ".." ^
        String.sub s (ndigits_l + 2) ndigits_r
      ) else s
  end

  module Word = struct
    (* a word is printed as:
       - <perm> <range> <addr> if it's a capability
         (with padding after the range to right-align <addr>)
       - <int> if it's an integer
    *)
    let width =
      Perm.width + 1 (* space *) +
      Locality.width + 1 (* space *) +
      Addr_range.width + 1 (* space *) +
      Addr.width

    let ui ?(attr = A.empty) (w: Machine.word) (s : side) =
      match w with
      | I z ->
        (match s with
        | Left -> I.hsnap ~align:`Right width (I.string attr (Int.ui width z))
        | Right -> I.hsnap ~align:`Left width (I.string attr (Int.ui width z))
        )
      | Cap (p, g, b, e, a) ->
        match s with
        | Left ->
          (I.hsnap ~align:`Left width
             (Perm.ui ~attr p
              <|> I.string A.empty " "
              <|> Locality.ui ~attr g
              <|> I.string A.empty " "
              <|> Addr_range.ui ~attr (b, e))
           </>
           I.hsnap ~align:`Right width (Addr.ui a))
        | Right ->
          (I.hsnap ~align:`Right width
             (Perm.ui ~attr p
              <|> I.string A.empty " "
              <|> Locality.ui ~attr g
              <|> I.string A.empty " "
              <|> Addr_range.ui ~attr (b, e))
           </>
           I.hsnap ~align:`Left width (Addr.ui a))
  end

  module Regname = struct
    (* pc or rNN *)
    let width = 3
    let ui (r: Ast.regname) =
      I.hsnap ~align:`Right width
        (I.string A.empty (Pretty_printer.string_of_regname r))
  end

  module Regs_panel = struct
    (* <reg>: <word>  <reg>: <word>  <reg>: <word>
       <reg>: <word>  <reg>: <word>
    *)
    let ui width (regs: Machine.reg_state) =
      let reg_width = Regname.width + 2 + Word.width + 2 in
      let ncols = max 1 (width / reg_width) in
      let nregs_per_col = 33. (* nregs *) /. float ncols |> ceil |> int_of_float in
      let rec loop fst_col regs =
        if regs = [] then I.empty else (
          let col, regs = CCList.take_drop nregs_per_col regs in
          List.fold_left (fun img (r, w) ->
            img
            <->
            ((if not fst_col then I.string A.empty "  " else I.empty) <|>
             Regname.ui r <|> I.string A.empty ": " <|> Word.ui w Left)) I.empty col
          <|>
          loop false regs
        ) in
      loop true (Machine.RegMap.to_seq regs |> List.of_seq)
      |> I.hsnap ~align:`Left width
  end

  module Instr = struct
    let ui (i: Ast.machine_op) =
      I.string A.(fg green) (Pretty_printer.string_of_statement i)
  end

  module Program_panel = struct
    (* TODO: associate a color to each permission and make the color of the
       range (+pointer?) match the permission of PC *)
    (*    <addr>  <word>  <decoded instr>
      ┏   <addr>  <word>  <decoded instr>
      ┃ ▶ <addr>  <word>  <decoded instr>
      ┗   <addr>  <word>  <decoded instr>
    *)
    let ui height width
        (mem: Machine.mem_state)
        (pc: Machine.word)
        (stk: Machine.word)
        (start_prog: int)
        (start_stk: int)
      =

      let start_prog =
        match pc with
        | I _ -> start_prog
        | Cap (_, _, _, _, pc) ->
          if pc <= start_prog && start_prog > 0 then
            (* switch to previous page *)
            (* start_prog - height + 2 *)
            pc - 2
          else if pc >= start_prog + height - 1 && start_prog + height < Cfg.addr_max then
            (* switch to next page *)
            (* start_prog + height - 2 *)
            pc - 2
          else
            start_prog
      in


      let start_stk =
        match stk with
        | I _ -> start_stk
        | Cap (_, _, _, _, stk) ->
          if stk <= start_stk && start_stk > 0 then
            (* switch to previous page *)
            (* start_stk - height + 2 *)
            stk - 2
          else if stk >= start_stk + height - 1 && start_stk + height < Cfg.addr_max then
            (* switch to next page *)
            (* start_stk + height - 2 *)
            stk - 2
          else
            start_stk
      in


      let at_reg r a = match r with Machine.I _ -> false | Cap (_, _, _, _, r) -> a = r in
      let at_pc a = at_reg pc a in
      let at_stk a = at_reg stk a in

      let is_in_r_range r a =
        match r with
        | Machine.I _ -> `No
        | Cap (_, _, b, e, _) ->
          if a >= b && a < e then (
            if a = b then `AtStart
            else if a = e-1 then `AtLast
            else `InRange
          ) else `No
      in

      let is_in_pc_range a = is_in_r_range pc a in
      let is_in_stk_range a = is_in_r_range stk a in

      let data =
        CCList.(start_prog --^ (start_prog+height))
        |> List.filter (fun a -> a >= 0 && a < Cfg.addr_max)
        |> List.map (fun a -> a, Machine.MemMap.find a mem) in

      let stack =
        CCList.(start_stk --^ (start_stk+height))
        |> List.filter (fun a -> a >= 0 && a < Cfg.addr_max)
        |> List.map (fun a -> a, Machine.MemMap.find a mem) in

      let img_of_dataline a w =
        (match is_in_pc_range a with
         | `No -> I.string A.empty " "
         | `AtStart -> I.string A.(fg red) "┏"
         | `InRange -> I.string A.(fg red) "┃"
         | `AtLast -> I.string A.(fg red) "┗")
        <|> (if at_pc a then I.string A.(fg red) "▶ " else I.string A.empty "  ")
        <|> Addr.ui ~attr:A.(fg yellow) a
        <|> I.string A.empty "  "
        <|> Word.ui w Right
        <|> I.string A.empty "  "
        <|>
        (match w with
         | I z when is_in_pc_range a <> `No ->
           begin match Encode.decode_statement z with
             | i -> Instr.ui i
             | exception Encode.DecodeException _ -> I.string A.(fg green) "???"
           end
         | _ -> I.empty)
        |> I.hsnap ~align:`Left width
      in

      let img_of_stack a w =
        let color_indicator = A.lightmagenta in
        (match w with
         | Machine.I z when is_in_stk_range a <> `No ->
           begin match Encode.decode_statement z with
             | i -> Instr.ui i
             | exception Encode.DecodeException _ -> I.string A.(fg green) "???"
           end
         | _ -> I.empty)
        <|> I.string A.empty "  "
        <|> Word.ui w Left
        <|> I.string A.empty "  "
        <|> Addr.ui ~attr:A.(fg yellow) a
        <|> (if at_stk a then I.string A.(fg color_indicator) " ◀" else I.string A.empty "  ")
        <|>
        (match is_in_stk_range a with
         | `No -> I.string A.empty " "
         | `AtStart -> I.string A.(fg color_indicator) "┓"
         | `InRange -> I.string A.(fg color_indicator) "┃"
         | `AtLast -> I.string A.(fg color_indicator) "┛")
        |> I.hsnap ~align:`Right width
      in
      (List.fold_left (fun img (a, w) -> img <-> img_of_dataline a w)
         I.empty data)
      </>
      (List.fold_left (fun img (a, w) -> img <-> img_of_stack a w)
         I.empty stack),
      start_prog,
      start_stk
  end

  module Exec_state = struct
    let width = 7
    let ui (s: Machine.exec_state) =
      I.hsnap ~align:`Left width @@
      match s with
      | Running -> I.string A.empty "Running"
      | Halted -> I.string A.(st bold) "Halted"
      | Failed -> I.string A.(st bold ++ fg red) "Failed"
  end
end
