let parse_prog (filename: string): (Ast.t, string) Result.t =
  let input = open_in filename in
  try
    let filebuf = Lexing.from_channel input in
    let parse_res = Ir.translate_prog @@ Parser.main Lexer.token filebuf in
    close_in input; Result.Ok parse_res
  with Failure _ -> close_in input; Result.Error "Parsing Failed"

let parse_regfile (filename: string) (max_addr : int) (stk_addr : int)
  : (Machine.word Machine.RegMap.t, string) Result.t =
  let input = open_in filename in
  try
    let filebuf = Lexing.from_channel input in
    let parse_res =
      Irreg.translate_regfile @@
      Parser_regfile.main Lexer_regfile.token filebuf
    in
    close_in input; Result.Ok (parse_res max_addr stk_addr)
  with Failure _ -> close_in input; Result.Error "Parsing Failed"

let init_machine
    (prog : Ast.t)
    (addr_max : int option)
    (init_regs : Machine.word Machine.RegMap.t)
  : Machine.mchn =
  let addr_max =
    match addr_max with
    | Some a_max -> a_max
    | None -> List.length prog in
  (* let init_regs = Machine.init_reg_state addr_max stack_opt stk_locality in *)
  let init_mems = Machine.init_mem_state addr_max prog in
  Machine.init init_regs init_mems
