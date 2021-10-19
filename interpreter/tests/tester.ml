open Libinterp
open Libinterp.Machine

(*
let make_test_list (dir : string) : string array =
  try Sys.readdir dir
  with Failure _ -> raise Sys.Break
*)
let z_tst = Alcotest.testable Z.pp_print Z.equal

let state_tst = Alcotest.testable
    (Fmt.of_to_string (
        fun (st : exec_state) ->
          match st with
          | Running -> "Running"
          | Failed -> "Failed"
          | Halted -> "Halted"))
    (fun a b -> a = b)
         


let run_prog (filename : string) : mchn  =
  let input = open_in filename in
  let filebuf = Lexing.from_channel input in
  let parse_res = Parser.main Lexer.token filebuf in
  let _ = close_in input in
  let m = init_mchn 10000 parse_res in
  run m

let test_const_word expected actual = fun _ ->
  Alcotest.(check z_tst) "Integers match" expected actual

let test_state expected actual = fun _ ->
  Alcotest.(check state_tst) "States match" expected actual

let test_mov_test =
  let open Alcotest in
  let m = run_prog "../../../tests/test_files/pos/mov_test.s" in
  let pc_a = begin
    match get_reg PC @@ snd m with
    | Cap (_, _, _, a) -> a
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
  
let () =
  let open Alcotest in
  run "Run" [
    "Pos", test_mov_test;
  ]
