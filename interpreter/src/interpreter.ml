open Libinterp

let () =
  (* very basic commandline argument parsing (to be improved) *)
  let filename =
    match Sys.argv |> Array.to_list |> List.tl with
    | [filename] -> filename
    | _ ->
      Printf.eprintf "usage: %s <input filename>\n" Sys.argv.(0);
      exit 1
  in
  match Program.parse filename with
  | Ok prog -> let res = Program.run_program prog None in
    Program.print_reg_state res;
    Printf.printf "Final execution state: %s\n" @@ Pretty_printer.string_of_exec_state (fst res);
    exit 0
  | Error msg ->
    Printf.eprintf "Error: %s\n" msg;
    exit 1
