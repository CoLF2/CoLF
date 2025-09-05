let () =
  Sys.set_signal Sys.sigusr1 (Sys.Signal_handle (fun _ ->
    Printexc.print_backtrace stdout;
    flush stdout
  ))
let process_single_file fname = 
  (* let content = In_channel.read_all fname in *)
  let _ = print_endline "Read OK" in
  let char_stream = CharStream.CharStream.new_file fname in
  let ast = MixfixParser.CoLFParser.parse char_stream in
  let signature = CoLFSignature.CoLFSignature.new_signature ast in
  (* let _ = print_endline (CoLFSignature.CoLFSignature.debug_show_signature_raw signature) in *)
  (* let _ = print_endline (CoLFSignature.CoLFSignature.debug_show_signature signature) in *)
  let _ = print_endline (CoLFSignature.CoLFSignature.show_signature signature) in
  let _ = CompiledExec.compiled_exec_top_level fname signature in

  ()

  (* print_endline (CoLFAbt.CoLFAbt.show_raw (List.hd ast));
  print_endline (CoLFAbt.CoLFAbt.show_view (List.hd ast)) *)
  (* try
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
      ) *)

let prelude () =   
  (
  (* Enable backtraces *)
  Printexc.record_backtrace true;

  (* Custom handler for Ctrl-C (SIGINT) *)
  let handle_sigint _ =
    Printf.eprintf "Interrupted! Stack trace:\n";
    Printexc.print_backtrace stderr;
    exit 1
  in

  (* Set the signal handler *)
  Sys.set_signal Sys.sigint (Sys.Signal_handle handle_sigint);
)

let input_files : string list ref = ref []



let entry (args : string list) : unit = 
  let _ = prelude () in
  let rec process_args r_args = 
    match r_args with
    | [] -> ()
    | "--v2" :: rest -> 
      (
        print_endline "Using v2 CoLF";
        process_args rest
      )
    | fname :: rest -> 
      (
        if String.starts_with ~prefix:"--" fname then
          Flags.add_c_debug_flag (String.sub fname 2 (String.length fname - 2))
        else
        input_files := fname :: !input_files;
        process_args rest
      )
    in
  let _ = process_args args in
  match !input_files with
  | [] -> print_endline "No file provided"
  | [fname] -> 
    (try (process_single_file fname
    ) with Failure s -> 
      (let s = s in
      print_endline ("FAILED: " ^ s); 
      Printexc.print_backtrace Stdlib.stdout;
      failwith "Exception Printed";
      )
      | Errors.Errors.CoLFError (ext, s) -> 
        (
          let source_loc = match ext with | None -> "<unknown>" | Some ext -> AbtLib.Extent.show_extent ext in
          print_endline (source_loc ^ ":Error: " ^ s);
          Printexc.print_backtrace Stdlib.stdout;
          failwith "Exception Printed";
        )
    )
  | _ -> print_endline ("Multiple files provided, only one file is allowed: " ^ (String.concat " " (!input_files)))
  