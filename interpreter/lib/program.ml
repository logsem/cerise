let parse (filename: string): (Ast.t, string) Result.t =
  let input = open_in filename in
  try
    let filebuf = Lexing.from_channel input in
    let parse_res = Ir.translate_prog @@ Parser.main Lexer.token filebuf in
    close_in input; Result.Ok parse_res
  with Failure _ -> close_in input; Result.Error "Parsing Failed"
    
let init_machine (prog : Ast.t)  (addr_max : int option) (stack_opt : bool) : Machine.mchn =
  let addr_max =
    match addr_max with
    | Some a_max -> a_max
    | None -> List.length prog in
  Machine.init addr_max prog stack_opt
