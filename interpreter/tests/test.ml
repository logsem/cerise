open Libinterp
open Libinterp.Pretty_printer
open Libinterp.Ast

let statement_eq (a : statement) (b : statement) = (a = b)
let pprint_statement = Fmt.of_to_string string_of_statement

let statement_tst = Alcotest.testable pprint_statement statement_eq

module To_test = struct
  let lex_parse = fun x ->
    List.hd @@ Ir.translate_prog @@ Parser.main Lexer.token @@ Lexing.from_string x
  let enc_interleave a b = Encode.interleave_int (Z.of_string a) (Z.of_string b)
  let enc_int a b = Encode.encode_int_int a b
  let enc_split = Encode.split_int
  let enc_dec_int a b = Encode.decode_int @@ Encode.encode_int_int a b
  let enc_dec_stm s = Encode.decode_statement @@ Encode.encode_statement s
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
  ("mov pc -25", Move (PC, const (-25)));
  ("mov r30 stk", Move (Reg 30, Register STK));
  ("load r0 r1", Load (Reg 0, Reg 1));
  ("store r2 r3", Store (Reg 2, Register (Reg 3)));
  ("add r4 (10-15) (-37)", Add (Reg 4, const (-5), const (-37)));
  ("sub r5 6 28", Sub (Reg 5, const 6, const 28));
  ("lt r6 496 8128 ; perfect numbers are cool!", Lt (Reg 6, const 496, const 8128));
  ("lea r7 r8", Lea (Reg 7, Register (Reg 8)));
  ("restrict r9 RX Global", Restrict (Reg 9, CP (Perm (RX, Global))));
  ("restrict r25 RWL LOCAL", Restrict (Reg 25, CP (Perm (RWL, Local))));
  ("restrict r26 RWL DIRECTED", Restrict (Reg 26, CP (Perm (RWL, Directed))));
  ("subseg r10 pc r11", SubSeg (Reg 10, Register PC, Register (Reg 11)));
  ("isptr r12 r13", IsPtr (Reg 12, Reg 13));
  ("getp r14 r15", GetP (Reg 14, Reg 15));
  ("getb r16 r17", GetB (Reg 16, Reg 17));
  ("gete r18 r19", GetE (Reg 18, Reg 19));
  ("geta r20 r21", GetA (Reg 20, Reg 21));
  ("getl r22 r23", GetL (Reg 22, Reg 23));
  ("loadU r24 r25 3", LoadU (Reg 24, Reg 25, const 3));
  ("storeu r26 r27 r28", StoreU (Reg 26, Register (Reg 27), Register (Reg 28)));
  ("promoteu r29", PromoteU (Reg 29));
  ("fail", Fail);
  ("halt", Halt);
  ("nop", Nop);
]

let z_tst =
  let open Z in
  let pprint_z = Fmt.of_to_string (format "%b") in
  let z_eq (a : t) (b : t) = (a = b) in
  Alcotest.testable pprint_z z_eq

let test_encode_interleave () =
  Alcotest.(check z_tst)
    "interleaves as expected"
    (Z.of_string "0b111001")
    (To_test.enc_interleave "0b101" "0b110") 

let test_encode_pos_pos_int () =
  Alcotest.(check z_tst)
    "positive integers"
    (Z.of_string "0b11100100")
    (To_test.enc_int (Z.of_string "0b101") (Z.of_string "0b110"))

let test_encode_pos_neg_int () =
  Alcotest.(check z_tst)
    "positive first integer and negative second"
    (Z.of_string "0b11100110")
    (To_test.enc_int (Z.of_string "0b101") (Z.neg @@ Z.of_string "0b110"))

let test_encode_neg_pos_int () =
  Alcotest.(check z_tst)
    "positive first integer and negative second"
    (Z.of_string "0b11100101")
    (To_test.enc_int (Z.neg @@ Z.of_string "0b101") (Z.of_string "0b110"))

let test_encode_neg_neg_int () =
  Alcotest.(check z_tst)
    "positive first integer and negative second"
    (Z.of_string "0b11100111")
    (To_test.enc_int (Z.neg @@ Z.of_string "0b101") (Z.neg @@ Z.of_string "0b110"))

let test_encode_split_int () =
  Alcotest.(check (pair z_tst z_tst))
    "splitting as expected"
    ((Z.of_string "0b101"), (Z.of_string "0b110"))
    (To_test.enc_split @@ Z.of_string "0b111001")

let test_encode_decode_pos_pos_int () =
  Alcotest.(check (pair z_tst z_tst))
    "decoding an encoded number should retrieve the encoded numbers"
    (Z.of_string "0b101", Z.of_string "0b110")
    (To_test.enc_dec_int (Z.of_string "0b101") (Z.of_string "0b110"))

let test_encode_decode_int_bulk ((a,b) : int * int) =
  let x = Z.of_int a
  and y = Z.of_int b in
  Alcotest.test_case
    (Format.sprintf "testing encode-decode of: %d, %d" a b) `Quick
    (fun _ -> Alcotest.(check (pair z_tst z_tst))
        "same output as input"
        (x,y)
        (To_test.enc_dec_int x y))

let test_int_pair_list = [
  (6, 28);
  (496, 8128);
  (-3, 10);
  (809281, -182884);
  (-554433, -9182);
]

let make_enc_dec_stm_tests (stm, test_name) =
  Alcotest.test_case
    test_name
    `Quick
    (fun _ ->
       Alcotest.(check statement_tst)
         "same statement"
         stm
         (To_test.enc_dec_stm stm))

let test_enc_dec_stm_list = [
  (Jmp PC, "encode-decode Jmp PC");
  (Jmp (Reg 28), "encode-decode Jmp R28");
  (Jnz (Reg 6, Reg 28), "encode-decode Jnz R6 R28");
  (Move (PC, Register (Reg 7)), "encode-decode Move PC R7");
  (Move (PC, const (-35)), "encode-decode Move PC (-35)");
  (Move (PC, CP (Perm (E, Global))), "encode-decode Move PC E");
  (Move (Reg 0, Register STK), "encode-decode Move R0 STK");
  (Load (Reg 9, PC), "encode-decode Load R9 PC");
  (Store (PC, Register (Reg 7)), "encode-decode Store PC R7");
  (Store (PC, const (-35)), "encode-decode Store PC (-35)");
  (Store (PC, CP (Perm (E, Global))), "encode-decode Store PC E");
  (Add (Reg 5, Register (Reg 6), Register PC), "encode-decode Add R5 R6 PC");
  (Add (Reg 5, Register (Reg 6), const 8128), "encode-decode Add R5 R6 8128");
  (Add (Reg 5, Register (Reg 6), CP (Perm (RO, Global))), "encode-decode Add R5 R6 RO");
  (Add (Reg 5, const (-549), Register PC), "encode-decode Add R5 (-549) PC");
  (Add (Reg 5, const (102), const 8128), "encode-decode Add R5 102 8128");
  (Add (Reg 5, const (83), CP (Perm (RO, Global))), "encode-decode Add R5 83 RO");
  (Add (Reg 5, CP (Perm (E, Global)), Register PC), "encode-decode Add R5 E PC");
  (Add (Reg 5, CP (Perm (O, Global)), const 8128), "encode-decode Add R5 O 8128");
  (Add (Reg 5, CP (Perm (RWX, Global)), CP (Perm (RO, Global))), "encode-decode Add R5 RWX RO");
  (Sub (Reg 5, Register (Reg 6), Register PC), "encode-decode Sub R5 R6 PC");
  (Sub (Reg 5, Register (Reg 6), const 8128), "encode-decode Sub R5 R6 8128");
  (Sub (Reg 5, Register (Reg 6), CP (Perm (RO, Global))), "encode-decode Sub R5 R6 RO");
  (Sub (Reg 5, const (-549), Register PC), "encode-decode Sub R5 (-549) PC");
  (Sub (Reg 5, const (102), const 8128), "encode-decode Sub R5 102 8128");
  (Sub (Reg 5, const (83), CP (Perm (RO, Global))), "encode-decode Sub R5 83 RO");
  (Sub (Reg 5, CP (Perm (E, Global)), Register PC), "encode-decode Sub R5 E PC");
  (Sub (Reg 5, CP (Perm (O, Global)), const 8128), "encode-decode Sub R5 O 8128");
  (Sub (Reg 5, CP (Perm (RWX, Global)), CP (Perm (RO, Global))), "encode-decode Sub R5 RWX RO");
  (Lt (Reg 5, Register (Reg 6), Register PC), "encode-decode Lt R5 R6 PC");
  (Lt (Reg 5, Register (Reg 6), const 8128), "encode-decode Lt R5 R6 8128");
  (Lt (Reg 5, Register (Reg 6), CP (Perm (RO, Global))), "encode-decode Lt R5 R6 RO");
  (Lt (Reg 5, const (-549), Register PC), "encode-decode Lt R5 (-549) PC");
  (Lt (Reg 5, const (102), const 8128), "encode-decode Lt R5 102 8128");
  (Lt (Reg 5, const (83), CP (Perm (RO, Global))), "encode-decode Lt R5 83 RO");
  (Lt (Reg 5, CP (Perm (E, Global)), Register PC), "encode-decode Lt R5 E PC");
  (Lt (Reg 5, CP (Perm (O, Global)), const 8128), "encode-decode Lt R5 O 8128");
  (Lt (Reg 5, CP (Perm (RWX, Global)), CP (Perm (RO, Global))), "encode-decode Lt R5 RWX RO");
  (Lea (PC, Register (Reg 7)), "encode-decode Lea PC R7");
  (Lea (PC, const (-35)), "encode-decode Lea PC (-35)");
  (Lea (PC, CP (Perm (E, Global))), "encode-decode Lea PC E");
  (Restrict (PC, Register (Reg 7)), "encode-decode Restrict PC R7");
  (Restrict (PC, const (-35)), "encode-decode Restrict PC (-35)");
  (Restrict (PC, CP (Perm (E, Global))), "encode-decode Restrict PC E Global");
  (Restrict (Reg 30, CP (Perm (RWL, Global))), "encode-decode Restrict R30 RWL Global");
  (Restrict (Reg 30, CP (Perm (RWL, Local))), "encode-decode Restrict R30 RWL Local");
  (Restrict (Reg 1, CP (Perm (URWL, Local))), "encode-decode Restrict R1 URWL Local");
  (Restrict (Reg 1, CP (Perm (URWL, Directed))), "encode-decode Restrict R1 URWL Directed");
  (SubSeg (Reg 5, Register (Reg 6), Register PC), "encode-decode SubSeg R5 R6 PC");
  (SubSeg (Reg 5, Register (Reg 6), const 8128), "encode-decode SubSeg R5 R6 8128");
  (SubSeg (Reg 5, Register (Reg 6), CP (Perm (RO, Global))),
   "encode-decode SubSeg R5 R6 RO Global");
  (SubSeg (Reg 5, const (-549), Register PC), "encode-decode SubSeg R5 (-549) PC");
  (SubSeg (Reg 5, const (102), const 8128), "encode-decode SubSeg R5 102 8128");
  (SubSeg (Reg 5, const (83), CP (Perm (RO, Local))), "encode-decode SubSeg R5 83 RO Local");
  (SubSeg (Reg 5, CP (Perm (E, Global)), Register PC), "encode-decode SubSeg R5 E PC");
  (SubSeg (Reg 5, CP (Perm (O, Global)), const 8128), "encode-decode SubSeg R5 O 8128");
  (SubSeg (Reg 5, CP (Perm (RWX, Global)), CP (Perm (RO, Global))), "encode-decode SubSeg R5 RWX RO");
  (IsPtr (Reg 6, Reg 28), "encode-decode IsPtr R6 R28");
  (GetP (Reg 6, Reg 28), "encode-decode GetP R6 R28");
  (GetB (Reg 6, Reg 28), "encode-decode GetB R6 R28");
  (GetE (Reg 6, Reg 28), "encode-decode GetE R6 R28");
  (GetA (Reg 6, Reg 28), "encode-decode GetA R6 R28");
  (GetL (Reg 6, Reg 28), "encode-decode GetL R6 R28");
  (StoreU (Reg 5, Register (Reg 6), const 8128), "encode-decode StoreU R5 R6 8128");
  (StoreU (Reg 5, Register (Reg 6), CP (Perm (RO, Global))), "encode-decode StoreU R5 R6 RO");
  (StoreU (Reg 5, Register (Reg 6), Register STK), "encode-decode StoreU R5 R6 STK");
  (StoreU (Reg 5, const (-549), Register STK), "encode-decode StoreU R5 (-549) STK");
  (StoreU (Reg 5, const (102), const 8128), "encode-decode StoreU R5 102 8128");
  (StoreU (Reg 5, const (83), CP (Perm (RO, Global))), "encode-decode StoreU R5 83 RO");
  (StoreU (Reg 5, CP (Perm (E, Global)), Register STK), "encode-decode StoreU R5 E STK");
  (StoreU (Reg 5, CP (Perm (O, Global)), const 8128), "encode-decode StoreU R5 O 8128");
  (StoreU (Reg 5, CP (Perm (RWX, Global)), CP (Perm (RO, Global))), "encode-decode StoreU R5 RWX RO");
  (LoadU (Reg 30, STK, Register (Reg 31)), "encore-decode LoadU R30 STK R31");
  (LoadU (Reg 30, STK, const 8129), "encore-decode LoadU R30 STK 8129");
  (LoadU (Reg 30, STK, CP (Perm (URWL, Local))), "encore-decode LoadU R30 STK URWL Local");
  (LoadU (Reg 31, STK, CP (Perm (URWLX, Directed))), "encore-decode LoadU R31 STK URWLX Directed");
  (PromoteU STK, "encore-decode PromoteU STK");
  (Fail, "encode-decode Fail");
  (Halt, "encode-decode Halt");
  (Nop, "encode-decode Nop");
]

let () =
  let open Alcotest in
  run "Lib" [
    "Lex/Pars",
      List.map make_op_test instr_tests;
    "Encode/Decode Integer", 
      (test_case "interleave int" `Quick test_encode_interleave)::
      (test_case "encode pos/pos int" `Quick test_encode_pos_pos_int)::
      (test_case "encode pos/neg int" `Quick test_encode_pos_neg_int)::
      (test_case "encode neg/pos int" `Quick test_encode_neg_pos_int)::
      (test_case "encode neg/neg int" `Quick test_encode_neg_neg_int)::
      (test_case "splitting of int" `Quick test_encode_split_int)::
      (test_case "encode-decode pos/pos int" `Quick test_encode_decode_pos_pos_int)::
      (List.map test_encode_decode_int_bulk test_int_pair_list);
    "Encode/Decode Statement",
      List.map make_enc_dec_stm_tests test_enc_dec_stm_list
  ]
