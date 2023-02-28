open Libinterp
open Libinterp.Machine
open Libinterp.Ast


let make_test_list (dir : string) : string array =
  try Sys.readdir dir
  with Failure _ -> raise Sys.Break

let z_tst = Alcotest.testable Z.pp_print Z.equal

let state_tst = Alcotest.testable
    (Fmt.of_to_string (
        fun (st : exec_state) ->
          match st with
          | Running -> "Running"
          | Failed -> "Failed"
          | Halted -> "Halted"))
    (fun a b -> a = b)
         
let perm_tst = Alcotest.testable
    (Fmt.of_to_string @@ Pretty_printer.string_of_perm)
    (fun a b -> a = b)

let run_prog (filename : string) : mchn  =
  let input = open_in filename in
  let filebuf = Lexing.from_channel input in
  let parse_res = Ir.translate_prog @@ Parser.main Lexer.token filebuf in
  let _ = close_in input in
  let m = Machine.init 10000 parse_res true in
  run m

let test_const_word expected actual = fun _ ->
  Alcotest.(check z_tst) "Integers match" expected actual

let test_state expected actual = fun _ ->
  Alcotest.(check state_tst) "States match" expected actual

let test_perm expected actual = fun _ ->
  Alcotest.(check perm_tst) "Permission match" expected actual

let get_reg_int_word (r : Ast.regname) (m : mchn) (d : Z.t) =
  match r @! snd m with
  | I z -> z
  | _ -> d

let get_reg_cap_perm (r : regname) (m : mchn) (d : perm) =
  match r @! snd m with
  | Cap (p, _, _, _, _) -> p
  | _ -> d

let test_negatives =
  let open Alcotest in
  let path = "../../../tests/test_files/neg/" in
  let test_names = make_test_list path in
  Array.to_list @@ Array.map (fun t ->
      test_case
        (Printf.sprintf "%s should end in Failed state" t)
        `Quick (test_state Failed (fst @@ run_prog (path ^ t)))
    ) test_names

let test_mov_test =
  let open Alcotest in
  let m = run_prog "../../../tests/test_files/pos/mov_test.s" in
  let pc_a = begin
    match get_reg PC @@ snd m with
    | Cap (_, _, _, _, a) -> a
    | _ -> -1
  end in
  let r2_res = begin
    match Reg 2 @! snd m with
    | I z -> z
    | _ -> Z.zero
  end in
  let r5_res = begin
    match Reg 5 @! snd m with
    | I z -> z
    | _ -> Z.zero
  end
  in [
    test_case
      "mov_test.s should end in halted state"
      `Quick (test_state Halted (fst m));
    test_case
      "mov_test.s PC should point to address 2"
      `Quick (fun _ -> check int "Ints match" 2 pc_a);
    test_case
      "mov_test.s R2 should contain 28"
      `Quick (test_const_word Z.(~$28) r2_res);
    test_case
      "mov_test.s R5 should contain -30"
      `Quick (test_const_word Z.(~$(-30)) r5_res);
  ]

let test_jmper =
  let open Alcotest in
  let m = run_prog "../../../tests/test_files/pos/jmper.s" in [
    test_case
      "jmper.s should end in halted state"
      `Quick (test_state Halted (fst m));
    test_case
      "jmper.s should end with r2 containing 12"
      `Quick (test_const_word Z.(~$12) (get_reg_int_word (Ast.Reg 2) m (Z.zero)));
    test_case
      "jmper.s should contain E permission in r1"
      `Quick (test_perm E (get_reg_cap_perm (Reg 1) m O));
  ]

let test_promote =
  let open Alcotest in
  let m = run_prog "../../../tests/test_files/pos/ucap_promote.s" in [
    test_case
      "ucap_promote.s should end in halted state"
      `Quick (test_state Halted (fst m));
    test_case
      "ucap_promote.s should contain RWLX permission in r0"
      `Quick (test_perm RWLX (get_reg_cap_perm (Reg 0) m O));
    test_case
      "ucap_promote.s should contain RWL permission in r1"
      `Quick (test_perm RWL (get_reg_cap_perm (Reg 1) m O));
    test_case
      "ucap_promote.s should contain RWX permission in r2"
      `Quick (test_perm RWX (get_reg_cap_perm (Reg 2) m O));
    test_case
      "ucap_promote.s should contain RW permission in r3"
      `Quick (test_perm RW (get_reg_cap_perm (Reg 3) m O));
  ]

let () =
  let open Alcotest in
  run "Run" [
    "Pos", test_mov_test @ test_jmper @ test_promote;
    "Neg", test_negatives;
  ]
