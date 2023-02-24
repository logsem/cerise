open Libinterp

let print_exec_state (m : Machine.mchn) =
  print_endline @@ Pretty_printer.string_of_exec_state (fst m)

let print_reg_state (m : Machine.mchn) =
  let open Pretty_printer in
  let rs = (snd m).reg in
  print_endline "+-----------------------";
  Machine.RegMap.iter (fun r w ->
    print_endline @@ string_of_reg_word r w) rs;
  print_endline "+-----------------------"

let () =
  (* very basic commandline argument parsing (to be improved) *)
  let filename =
    match Sys.argv |> Array.to_list |> List.tl with
    | [filename] -> filename
    | _ ->
      Printf.eprintf "usage: %s <input filename>\n" Sys.argv.(0);
      exit 1
  in
  let prog =
    match Program.parse filename with
    | Ok prog -> prog
    | Error msg ->
      Printf.eprintf "Parse error: %s\n" msg;
      exit 1
  in
  let addr_max = (Int32.to_int Int32.max_int)/4096 in
  let m_init = Program.init_machine prog (Some addr_max) in
  let m_final = Machine.run m_init in
  print_reg_state m_final;
  Printf.printf "Final execution state: %s\n"
    (Pretty_printer.string_of_exec_state (fst m_final))
