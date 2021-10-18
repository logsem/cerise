open Libinterp

let make_test_list (dir : string) : string array =
  try Sys.readdir dir
  with Failure _ -> raise Sys.Break

let pos_test (filename : string) (_ept : string): unit  =
  let input = open_in filename in
  let filebuf = Lexing.from_channel input in
  let _parse_res = Parser.main Lexer.token filebuf in
  close_in input;
  ()
