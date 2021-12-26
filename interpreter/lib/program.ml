let parse (filename: string): (Ast.t, string) Result.t =
  let input = open_in filename in
  try
    let filebuf = Lexing.from_channel input in
    let parse_res = Ir.translate_prog @@ Parser.main Lexer.token filebuf in
    close_in input; Result.Ok parse_res
  with Failure _ -> close_in input; Result.Error "Parsing Failed"
    
let run_program (prog : Ast.t) (addr_max : int option) : Machine.mchn =
  let addr_max =
    match addr_max with
    | Some a_max -> a_max
    | None -> List.length prog in
  let m = Machine.init addr_max prog in
  Machine.run m

let print_exec_state (m : Machine.mchn) =
  print_endline @@ Pretty_printer.string_of_exec_state (fst m)

let print_reg_state (m : Machine.mchn) =
  let open Pretty_printer in
  let rs = (snd m).reg in
  print_endline "+-----------------------";
  Machine.RegMap.iter (fun r w ->
    print_endline @@ string_of_reg_word r w) rs;
  print_endline "+-----------------------"
