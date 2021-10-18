let parse (_filename: string): unit (*(Ast.t, string) Result.t*) =
  let input = open_in _filename in
  let filebuf = Lexing.from_channel input in
  let parse_res = Parser.main Lexer.token filebuf in
  close_in input;
  List.iter (fun s -> print_endline @@ Pretty_printer.string_of_statement s) parse_res
