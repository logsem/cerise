{
  open Parser_regfile
  exception Error of string
  let error lexbuf msg =
    let position = Lexing.lexeme_start_p lexbuf in
    let err_str = Printf.sprintf "Lexing error in file %s at position %d:%d\n"
                  position.pos_fname position.pos_lnum (position.pos_cnum - position.pos_bol + 1)
                  ^ msg ^ "\n" in
    raise (Error err_str)
}

let digit = ['0'-'9']
let hex = (digit | ['a'-'f'] | ['A'-'F'])
let reg_num = ((digit) | ('1' digit) | ('2' digit) | "30" | "31")
let perm = ('O' | 'E' | "RO" | "RW" | "RWX")
let addr = ("MAX_ADDR" | "STK_ADDR")
let locality = ("LOCAL" | "GLOBAL" | "DIRECTED" | "Local" | "Global" | "Directed")
let letter = ['a'-'z' 'A'-'Z']

rule token = parse
| eof { EOF }
| [' ' '\t'] { token lexbuf }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| ';' { comment lexbuf }
| ((digit+) | ("0x" hex+)) as i { try INT (int_of_string i)
                                  with Failure _ -> error lexbuf ("Invalid integer '" ^ i ^ "'.")}

(* registers *)
| ['p' 'P'] ['c' 'C'] { PC }
| ['s' 'S'] ['t' 'T'] ['k' 'K'] { STK }
| ['r' 'R'] (reg_num as n) { try REG (int_of_string n)
                             with Failure _ -> error lexbuf ("Invalid register id '" ^ n ^ "'.")}
(* addresses *)
| "MAX_ADDR" { MAX_ADDR }
| "STK_ADDR" { STK_ADDR }

(* single-character tokens *)
| '(' { LPAREN }
| ')' { RPAREN }
| '+' { PLUS }
| '-' { MINUS }
| ',' { COMMA }
| ":=" { AFFECT }

(* locality *)
| "LOCAL"    | "Local" { LOCAL }
| "GLOBAL"   | "Global"  { GLOBAL }
| "DIRECTED" | "Directed"  { DIRECTED }

(* permissions *)
| 'O' { O }
| 'E' { E }
| "RO" { RO }
| "RX" { RX }
| "RW" { RW }
| "RWX" { RWX }
| "RWL" { RWL }
| "RWLX" { RWLX }
| "URW" { URW }
| "URWX" { URWX }
| "URWL" { URWL }
| "URWLX" { URWLX }

and comment = parse
| eof { EOF }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| _ { comment lexbuf }
