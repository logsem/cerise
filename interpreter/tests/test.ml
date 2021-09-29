open Libinterp
open Libinterp.Pretty_printer
open Libinterp.Ast

(* TODO add a testable for statement list *)



let statement_eq (a : statement) (b : statement) = (a = b)
let pprint_statement = Fmt.of_to_string string_of_statement

let statement_tst = Alcotest.testable pprint_statement statement_eq

module To_test = struct
  let lex_parse = fun x ->
    List.hd @@ Parser.main Lexer.token @@ Lexing.from_string x
end

let make_op_test ((input, expect) : string * statement) =
  Alcotest.test_case input `Quick
  (fun _ -> Alcotest.(check statement_tst)
      (Format.sprintf "Checking Lex/Parse of: %s" input)
      expect
      (To_test.lex_parse input))

let instr_tests = [
  ("jmp pc", Jmp PC);
  ("jmp r21", Jmp (Reg 21));
  ("jnz r11 r9", Jnz (Reg 11, Reg 9));
  ("mov pc -25", Move (PC, Const (-25)));
  ("load r0 r1", Load (Reg 0, Reg 1));
  ("store r2 r3", Store (Reg 2, Register (Reg 3)));
  ("add r4 (10-15) (-37)", Add (Reg 4, Const (-5), Const (-37)));
  ("sub r5 6 28", Sub (Reg 5, Const 6, Const 28));
  ("lt r6 496 8128 ; perfect numbers are cool!", Lt (Reg 6, Const 496, Const 8128));
  ("lea r7 r8", Lea (Reg 7, Register (Reg 8)));
  ("restrict r9 RX", Restrict (Reg 9, Perm RX));
  ("subseg r10 pc r11", SubSeg (Reg 10, Register PC, Register (Reg 11)));
  ("isptr r12 r13", IsPtr (Reg 12, Reg 13));
  ("getp r14 r15", GetP (Reg 14, Reg 15));
  ("getb r16 r17", GetB (Reg 16, Reg 17));
  ("gete r18 r19", GetE (Reg 18, Reg 19));
  ("geta r20 r21", GetA (Reg 20, Reg 21));
  ("fail", Fail);
  ("halt", Halt);
]

let () =
  let open Alcotest in
  run "Lex/Pars" [
    "single instructions",
    List.map make_op_test instr_tests
  ]
