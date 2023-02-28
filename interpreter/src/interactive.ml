open Libinterp

(* main loop *)
let () =
  let addr_max = (Int32.to_int Int32.max_int)/4096 in

  let usage_msg = "interactive [--no-stack] [--mem-size size] <file>" in
  let no_stack_option = ref false in
  let mem_size_option = ref addr_max in
  let input_files = ref [] in

  let anon_fun filename = input_files := filename :: !input_files in
  let speclist =
    [
      ("--no-stack", Arg.Set no_stack_option, "Disable the stack");
      ("--mem-size", Arg.Set_int mem_size_option, "Size of the memory, as an integer");
    ] in
  Arg.parse speclist anon_fun usage_msg;

  let filename =
    match !input_files with
    | [filename] -> filename
    | _ ->
      Printf.eprintf "%s\n" usage_msg;
      exit 1
  in

  let prog =
    match Program.parse filename with
    | Ok prog -> prog
    | Error msg ->
      Printf.eprintf "Parse error: %s\n" msg;
      exit 1
  in
  let size_mem =
    let s = !mem_size_option in
    if s < 0
    then (Printf.eprintf "Size of memory must be positive (%d)" s; exit 1)
    else s
  in

  let module Cfg = struct let addr_max = size_mem end in
  let module Ui = Interactive_ui.MkUi (Cfg) in

  let stack_opt = not !no_stack_option in

  let m_init = Program.init_machine prog (Some Cfg.addr_max) stack_opt in

  (* let term = Term.create () in *)

  let prog_panel_start = ref 0 in
  let stk_panel_start = ref (if stack_opt then ((Cfg.addr_max)/2) else 0) in

  Ui.render_loop ~show_stack:stack_opt prog_panel_start stk_panel_start m_init
