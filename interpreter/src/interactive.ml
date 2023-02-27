open Libinterp
open Notty
open Notty.Infix
open Notty_unix

(* main loop *)
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

  (* let addr_max = List.length prog in *)
  let addr_max = (Int32.to_int Int32.max_int)/4096 in
  let module Cfg = struct let addr_max = addr_max end in
  let module Ui = Interactive.MkUi (Cfg) in

  let term = Term.create () in
  let m_init = Program.init_machine prog (Some Cfg.addr_max) in

  (* let term = Term.create () in *)

  let prog_panel_start = ref 0 in
  let stk_panel_start = ref (Cfg.addr_max) in

  let rec loop m =
    let term_width, term_height = Term.size term in
    let reg = (snd m).Machine.reg in
    let mem = (snd m).Machine.mem in
    let regs_img =
      Ui.Regs_panel.ui term_width (snd m).Machine.reg in
    let prog_img, panel_start, panel_stk =
      Ui.Program_panel.ui (term_height - 1 - I.height regs_img) term_width mem
        (Machine.RegMap.find Ast.PC reg)
        (Machine.RegMap.find Ast.STK reg)
        !prog_panel_start
        !stk_panel_start
    in
    prog_panel_start := panel_start;
    stk_panel_start := panel_stk;
    let mach_state_img =
      I.hsnap ~align:`Right term_width
        (I.string A.empty "machine state: " <|> Ui.Exec_state.ui (fst m))
    in
    let img =
      regs_img
      <-> mach_state_img
      <-> prog_img
    in
    Term.image term img;
    (* watch for a relevant event *)
    let rec process_events () =
      match Term.event term with
      | `End | `Key (`Escape, _) | `Key (`ASCII 'q', _) -> Term.release term
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
