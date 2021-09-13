open Ast

let print_register (r: regname) : unit =
  match r with
  | PC -> print_string "pc "
  | Reg i -> print_string "r"; print_int i; print_char ' '

let print_const (c: reg_or_const) : unit =
  match c with
  | Register r -> print_register r
  | Const c -> print_int c; print_char ' '
  | Perm p -> print_string (begin
      match p with
      | O -> "O "
      | E -> "E "
      | RO -> "RO "
      | RX -> "RX "
      | RW -> "RW "
      | RWX -> "RWX "
    end)

let printer (s: statement): unit =
  (match s with
   | Jmp r -> print_string "jmp "; print_register r
   | Jnz (r1, r2) -> print_string "jnz "; print_register r1; print_register r2
   | Move (r, c) -> print_string "mov "; print_register r; print_const c
   | Load (r1, r2) -> print_string "load "; print_register r1; print_register r2
   | Store (r, c) -> print_string "store "; print_register r; print_const c
   | Add (r, c1, c2) -> print_string "add "; print_register r; print_const c1; print_const c2
   | Sub (r, c1, c2) -> print_string "sub "; print_register r; print_const c1; print_const c2
   | Lt (r, c1, c2) -> print_string "lt "; print_register r; print_const c1; print_const c2
   | Lea (r, c) -> print_string "lea "; print_register r; print_const c
   | Restrict (r, c) -> print_string "restrict "; print_register r; print_const c
   | SubSeg (r, c1, c2) -> print_string "subseg "; print_register r; print_const c1; print_const c2
   | IsPtr (r1, r2) -> print_string "isptr "; print_register r1; print_register r2
   | GetP (r1, r2) -> print_string "getp "; print_register r1; print_register r2
   | GetB (r1, r2) -> print_string "getb "; print_register r1; print_register r2
   | GetE (r1, r2) -> print_string "gete "; print_register r1; print_register r2
   | GetA (r1, r2) -> print_string "geta "; print_register r1; print_register r2
   | Fail -> print_string "fail "
   | Halt -> print_string "halt "
  ); print_newline()
      
let parse (_filename: string): unit (*(Ast.t, string) Result.t*) =
  let input = open_in _filename in
  let filebuf = Lexing.from_channel input in
  let parse_res = Parser.main Lexer.token filebuf in
  close_in input; List.iter printer parse_res
