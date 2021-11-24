open Machine

let parse (filename: string): (Ast.t, string) Result.t =
  let input = open_in filename in
  try
    let filebuf = Lexing.from_channel input in
    let parse_res = Ir.translate_prog @@ Parser.main Lexer.token filebuf in
    close_in input; Result.Ok parse_res
  with Failure _ -> close_in input; Result.Error "Parsing Failed"
    
let run_program (prog : Ast.t) (addr_max : int option) : Machine.mchn =
  let prog_length = List.length prog in
  let m = begin
    match addr_max with
    | Some a_max when prog_length <= a_max -> init_mchn a_max prog
    | _ -> init_mchn prog_length prog
  end in
  run m

let print_exec_state (m : mchn) = print_endline @@ Pretty_printer.string_of_exec_state (fst m)

let print_reg_state (m : mchn) =
  let open Pretty_printer in
  let rs = (snd m).reg in
  print_endline "+-----------------------";
  RegMap.iter (fun r w ->
      print_endline @@ string_of_reg_word r w) rs; print_endline "+-----------------------"
