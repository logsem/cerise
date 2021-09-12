open Ast

let printer (s: statement): unit =
  match s with
  | Jmp r -> begin
      match r with
      | PC -> print_string "jmp pc\n"
      | Reg i -> print_string "jmp r"; print_int i; print_newline ()
    end
  | _ -> failwith "todo"

let parse (_filename: string): unit (*(Ast.t, string) Result.t*) =
  let input = open_in _filename in
  let filebuf = Lexing.from_channel input in
  let parse_res = Parser.main Lexer.token filebuf in
  close_in input; List.iter printer parse_res
