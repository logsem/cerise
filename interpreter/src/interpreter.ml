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
  | Ok _ast -> ()
  | Error msg ->
    Printf.eprintf "Error: %s\n" msg;
    exit 1
