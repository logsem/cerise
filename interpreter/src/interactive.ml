open Libinterp

(* main loop *)
let () =
  let addr_max = (Int32.to_int Int32.max_int)/4096 in

  let usage_msg = "interactive [--no-stack] [--mem-size size] <file>" in
  let no_stack_option = ref false in
  let mem_size_option = ref addr_max in
  let regfile_name_option = ref "" in
  let input_files = ref [] in

  let anon_fun filename = input_files := filename :: !input_files in
  let speclist =
    [
      ("--no-stack", Arg.Set no_stack_option, "Disable the stack");
      ("--mem-size", Arg.Set_int mem_size_option, "Size of the memory, as an integer");
      ("--regfile", Arg.Set_string regfile_name_option, "Initial state of the registers");
    ] in
  Arg.parse speclist anon_fun usage_msg;

  let filename_prog =
    match !input_files with
    | [filename] -> filename
    | _ ->
      Printf.eprintf "%s\n" usage_msg;
      exit 1
  in

  let prog =
    match Program.parse_prog filename_prog with
    | Ok prog -> prog
    | Error msg ->
      Printf.eprintf "Program parse error: %s\n" msg;
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
  (* let stk_locality = Ast.Directed in *)
  (* TODO add an option in the CLI to choose the stack locality *)

  let prog_panel_start = ref 0 in
  let stk_panel_start = ref (if stack_opt then ((Cfg.addr_max)/2) else 0) in

  let regfile =
    let stk_locality = Ast.Local in
    let init_regfile =
      (Machine.init_reg_state Cfg.addr_max stack_opt stk_locality) in
    if !regfile_name_option = ""
    then
      init_regfile
    else
      (match Program.parse_regfile !regfile_name_option Cfg.addr_max !stk_panel_start with
       | Ok regs ->
         (Machine.RegMap.fold
            (fun r w rf -> Machine.RegMap.add r w rf) regs) init_regfile
       | Error msg ->
         Printf.eprintf "Regfile parse error: %s\n" msg;
         exit 1)
  in


  let m_init =
    Program.init_machine prog (Some Cfg.addr_max) regfile in

  (* let term = Term.create () in *)


  Ui.render_loop ~show_stack:stack_opt prog_panel_start stk_panel_start m_init
