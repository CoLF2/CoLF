

open Core


let process_single_file fname = 
  try
  let content = In_channel.read_all fname in
let _ = print_endline "Read OK" in
let processed = Lexer.lex_string content in
let _ = print_endline "Lexed OK" in
let rawparsed = Parse.rawparse processed in
let _ = print_endline "Parsed OK" in
let elaborated = Elborate.elaborateDecTopLevel rawparsed in
let _ = print_endline "Elaborated OK" in
let type_reconstructed = TypeReconstruct.typecheckSigTopLevel elaborated in
let _ = print_endline "TypeChecked OK" in
let command_checked = CommandChecking.commandCheckSignatureTopLevel type_reconstructed in
let _ = print_endline "CommandChecked OK" in
let _ = print_endline (PrettyPrint.pp_ssig command_checked) in
let _ =  print_endline "%% OK %%" in
let _ =  print_endline "====================================" in
let _ =  print_endline "** CoLF₂ Logic2 Programming Engine **" in
let _ =  print_endline "====================================" in
let _ =  print_string "Please select mode 1: Depth LP, 2: Lazy LP. (Default: 2) > " in
let _ =  Stdlib.flush Stdlib.stdout in
let input = Stdlib.input_line Stdlib.stdin in
match input with
| "1" -> 
    let _ = print_endline "Picked Depth LP" in
    DepthLogicProgramming.loop_top command_checked
| "3" -> 
    let _ = print_endline "Picked Depth LP" in
    SatSolve.loop_top command_checked
| _ -> 
    let _ = print_endline "Picked Lazy LP" in
    LazyLogicProgramming.loop_top command_checked


  with Failure s -> 
    (let s = s in
    print_endline ("FAILED: " ^ s); failwith "Exception Printed"
    )

let input_files : string list ref = ref []


let v1_entry (args : string list) = 
  let rec process_args r_args = 
    match r_args with
    | [] -> ()
    | "--debug-print-add"::debug_name::rest -> 
      (Flags.add_c_debug_flag debug_name; process_args rest)
    | "--ddlp"::rest -> 
      (Flags.add_c_debug_flag "dlp"; process_args rest)
    | "--trace"::rest -> 
      (Flags.add_c_debug_flag "trace"; process_args rest)
    | fname :: rest -> 
      (
        input_files := fname :: !input_files;
        process_args rest
      )
    in
  let _ = process_args args in
  match !input_files with
  | [] -> print_endline "No file provided"
  | [fname] -> process_single_file fname
  | _ -> print_endline ("Multiple files provided, only one file is allowed: " ^ (String.concat ~sep:" " !input_files))
  
let entry (args : string list) : unit = 
  if Stdlib.List.mem "--v1" args  then 
    v1_entry args
  else
    Lftest08_v2.Start.entry args