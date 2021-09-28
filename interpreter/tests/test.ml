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
  Alcotest.test_case (Format.sprintf "Testing: %s" input) `Quick
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
]

let () =
  let open Alcotest in
  run "Lex/Pars" [
    "single instructions",
    List.map make_op_test instr_tests
  ]
