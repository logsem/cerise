{
  open Parser
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
let locality = ("LOCAL" | "GLOBAL")
let letter = ['a'-'z' 'A'-'Z']
let label = ('_' | letter) (letter | '_' | digit)*

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

(* machine_op *)
| "jmp" { JMP }
| "jnz" { JNZ }
| "mov" { MOVE }
| "load" { LOAD }
| "store" { STORE }
| "add" { ADD }
| "sub" { SUB }
| "lt" { LT }
| "lea" { LEA }
| "restrict" { RESTRICT }
| "subseg" { SUBSEG }
| "isptr" { ISPTR }
| "getl" { GETL }
| "getp" { GETP }
| "getb" { GETB }
| "gete" { GETE }
| "geta" { GETA }
| "load" ['u' 'U'] { LOADU }
| "store" ['u' 'U'] { STOREU }
| "promote" ['u' 'U'] { PROMOTEU }
| "fail" { FAIL }
| "halt" { HALT }

(* single-character tokens *)
| '(' { LPAREN }
| ')' { RPAREN }
| '+' { PLUS }
| '-' { MINUS }

(* locality *)
| "LOCAL" { LOCAL }
| "GLOBAL" { GLOBAL }

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

(* labels *)
| label as lbl ':' { LABELDEF (lbl) }
| label as lbl { LABEL (lbl) }

and comment = parse
| eof { EOF }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| _ { comment lexbuf }
