open Libinterp

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
  let module Ui = Interactive_ui.MkUi (Cfg) in

  let m_init = Program.init_machine prog (Some Cfg.addr_max) in

  (* let term = Term.create () in *)

  let prog_panel_start = ref 0 in
  let stk_panel_start = ref ((Cfg.addr_max)/2) in

  Ui.render_loop prog_panel_start stk_panel_start m_init
