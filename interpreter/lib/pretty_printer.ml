open Ast

let (^-) s1 s2 = s1 ^ " " ^ s2

let string_of_regname (r: regname) : string =
  match r with
  | PC -> "pc"
  | Reg i -> "r" ^ (string_of_int i)

let string_of_perm (p: perm): string =
  match p with
  | O -> "O"
  | E -> "E"
  | RO -> "RO"
  | RX -> "RX"
  | RW -> "RW"
  | RWX -> "RWX"

let string_of_reg_or_const (c: reg_or_const) : string =
  match c with
  | Register r -> string_of_regname r
  | CP (Const c) -> string_of_int c
  | CP (Perm p) -> string_of_perm p

let string_of_statement (s: statement): string =
  let string_of_rr r1 r2 =
    string_of_regname r1 ^- string_of_regname r2
  and string_of_rc r c =
    string_of_regname r ^- string_of_reg_or_const c
  and string_of_rcc r c1 c2  =
    string_of_regname r ^- string_of_reg_or_const c1 ^- string_of_reg_or_const c2
  in match s with
  | Jmp r -> "jmp" ^- string_of_regname r
  | Jnz (r1, r2) -> "jnz" ^- string_of_rr r1 r2
  | Move (r, c) -> "mov" ^- string_of_rc r c
  | Load (r1, r2) -> "load" ^- string_of_rr r1 r2
  | Store (r, c) -> "store" ^- string_of_rc r c
  | Add (r, c1, c2) -> "add" ^- string_of_rcc r c1 c2
  | Sub (r, c1, c2) -> "sub" ^- string_of_rcc r c1 c2
  | Lt (r, c1, c2) -> "lt" ^- string_of_rcc r c1 c2
  | Lea (r, c) -> "lea" ^- string_of_rc r c
  | Restrict (r, c) -> "restrict" ^- string_of_rc r c
  | SubSeg (r, c1, c2) -> "subseg" ^- string_of_rcc r c1 c2
  | IsPtr (r1, r2) -> "isptr" ^- string_of_rr r1 r2
  | GetP (r1, r2) -> "getp" ^- string_of_rr r1 r2
  | GetB (r1, r2) -> "getb" ^- string_of_rr r1 r2
  | GetE (r1, r2) -> "gete" ^- string_of_rr r1 r2
  | GetA (r1, r2) -> "geta" ^- string_of_rr r1 r2
  | Fail -> "fail"
  | Halt -> "halt"
