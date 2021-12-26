open Libinterp
open Notty
open Notty.Infix
open Notty_unix

(* ui components *)

module type MachineConfig = sig val addr_max : int end

module MkUi (Cfg: MachineConfig) = struct

  module Perm = struct
    let width = 3
    let ui (p: Ast.perm) =
      I.hsnap ~align:`Left width
        (I.string A.empty (Pretty_printer.string_of_perm p))
  end

  module Addr = struct
    (* width of an address as a number of hex digits *)
    let width =
      1 + int_of_float (floor @@ log (float Cfg.addr_max) /. log 16.)

    let to_hex (a: int): string =
      (* pad on the left with zeroes up to [width] chars *)
      Printf.sprintf "%0*X" width a

    let ui (a: int) =
      I.string A.empty (to_hex a)
  end

  module Addr_range = struct
    (* an address range is printed as either:
           XXXX-XXXX
       or  XX[XX-XX]   (in case of common higher-bits),
       whichever is shortest *)
    let width =
      2 * Addr.width + 1

    let ui (b, e) =
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
        Addr.ui b <|> I.string A.empty "-" <|> Addr.ui e
      | Some i ->
        let prefix = String.sub bs 0 i in
        let bs = String.sub bs i (Addr.width - i) in
        let es = String.sub es i (Addr.width - i) in
        I.string A.empty (prefix ^ "[" ^ bs ^ "-" ^ es ^ "]")
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
      Addr_range.width + 1 (* space *) +
      Addr.width

    let ui (w: Machine.word) =
      match w with
      | I z -> I.hsnap ~align:`Right width (I.string A.empty (Int.ui width z))
      | Cap (p, b, e, a) ->
        I.hsnap ~align:`Left width
          (Perm.ui p <|> I.string A.empty " " <|> Addr_range.ui (b, e))
        </>
        I.hsnap ~align:`Right width (Addr.ui a)
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
    let ui width (regs: Machine.word Machine.RegMap.t) =
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
             Regname.ui r <|> I.string A.empty ": " <|> Word.ui w)
          ) I.empty col
          <|>
          loop false regs
        ) in
      loop true (Machine.RegMap.to_seq regs |> List.of_seq)
      |> I.hsnap ~align:`Left width
  end
end

(* main loop *)

module Ui = MkUi (struct let addr_max = 512 end)

let () =
  let filename =
    match Sys.argv |> Array.to_list |> List.tl with
    | [filename] -> filename
    | _ ->
      Printf.eprintf "usage: %s <input filename>\n" Sys.argv.(0);
      exit 1
  in
  let prog =
    match Program.parse filename with
    | Ok prog -> prog
    | Error msg ->
      Printf.eprintf "Parse error: %s\n" msg;
      exit 1
  in
  let m_init = Program.init_machine prog None in

  let term = Term.create () in

  let rec loop m =
    let term_width = fst @@ Term.size term in
    let img = Ui.Regs_panel.ui term_width (snd m).Machine.reg in
    Term.image term img;
    (* watch for a relevant event *)
    let rec process_events () =
      match Term.event term with
      | `End | `Key (`Escape, _) -> Term.release term
      | `Key (`ASCII ' ', _) ->
        begin match Machine.step m with
        | Some m' -> loop m'
        | None -> (* XX *) loop m
        end
      | `Resize (_, _) -> loop m
      | _ -> process_events ()
    in
    process_events ()
  in
  loop m_init
