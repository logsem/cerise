open Libinterp

let rec pp_of_instrs l =
  match l with
  | [] -> Printf.printf ""
  | i::l' ->
  Printf.printf "%s\n%!" (Pretty_printer.string_of_statement (Convert.translate_instr i));
  pp_of_instrs l'

let () =
  pp_of_instrs (Convert.compile Convert.driver Extract.bank_example (Z.of_int 3))
