open Libinterp

let () =
  let radv = (Ast.Reg 28) in
  let renv = (Ast.Reg 30) in
  let prog = Call.awkward_example radv @ Call.adv_instr @ Call.ret_instr in

  (* let addr_max = List.length prog in *)
  (* let addr_max = (Int32.to_int Int32.max_int)/4096 in *)
  let addr_max = (Int32.to_int Int32.max_int)/32768 in
  let module Cfg = struct let addr_max = addr_max end in
  let module Ui = Interactive.MkUi (Cfg) in

  let m_init_state, m_init_conf = Program.init_machine prog (Some Cfg.addr_max) in
  let adv_upd radv conf =
    let addr_adv= (List.length (Call.awkward_example radv)) in
      Machine.upd_reg radv
        (Machine.Cap (E, Global, addr_adv, addr_adv + (List.length Call.adv_instr), addr_adv))
        conf
  in
  let ret_upd rret conf =
    let addr_ret= (List.length (Call.awkward_example radv @ Call.adv_instr)) in
      Machine.upd_reg rret
        (Machine.Cap (E, Global, addr_ret, addr_ret + (List.length Call.ret_instr), addr_ret))
        conf
  in
  let env_upd renv conf =
    let addr_data= (List.length prog) in
      Machine.upd_reg renv
        (Machine.Cap (RW, Global, addr_data, addr_data + 1, addr_data))
        conf
  in
  let m_init_conf = env_upd renv (ret_upd (Reg 0) (adv_upd radv m_init_conf)) in
  let m_init = ( m_init_state, m_init_conf) in

  (* let term = Term.create () in *)

  let prog_panel_start = ref 0 in
  let stk_panel_start = ref ((Cfg.addr_max)/2) in

  Ui.render_loop prog_panel_start stk_panel_start m_init
