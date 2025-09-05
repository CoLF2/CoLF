

module A = Ast
module Ctx = TypeCheckingContext  
module HS = HereditarySubstitution
module Unif = Unification

let read_and_parse_input (input : string) ( g : A.ssig) : A.ssig  = 
      let processed = Lexer.lex_string input in
      let rawparsed = Parse.rawparse processed in
      let elaborated = Elborate.elaborateDec A.empty_ssig rawparsed in
      let type_checked = TypeReconstruct.typecheckAdditionalSig g.decls elaborated.decls in
      let _ = (
        let all_names = (List.map (fun ((name, _)) -> name) (type_checked@g.decls)) in
        if ListUtil.contains_duplicate all_names 
          then failwith ("Duplicate names in the input : " ^ (String.concat ", " (ListUtil.find_duplicates all_names)))
        else (())
      ) in
      let _ = print_endline ("Read as " ^ A.ds_decls type_checked) in
      {elaborated with decls = type_checked}


let default_inductive_limit = 100
let default_coinductive_limit = 3



let ds_depth_ctx = fun (n, p ) -> "(" ^ string_of_int n ^ ", " ^ string_of_int p ^ ")"

let log_lg (lg : A.decls) (query: string) = 
  LazyLpLogging.push_new_json_message "meta" (
    `Assoc [
      ("signature", (
          `Assoc (List.map (fun ((name, ty)) -> (name, `String (PrettyPrint.pp_abt lg ty))) lg)
        ));
      ("query", `String query)
    ]
  )

      

let rec depth_loop_wrap ( g : A.ssig)  (ind_depth : int) (coind_depth : int)
        (lp_top_level: int -> int -> A.ssig -> A.ssig -> unit): unit = 
  try(
  let _ = Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> (failwith "Interrupted."))) in
  (* let _ = print_endline "?-" in *)
  let _  = Stdlib.output_string Stdlib.stdout (ds_depth_ctx ( coind_depth, ind_depth) ^ " ?- ")  in
  let _ = Stdlib.flush Stdlib.stdout  in

  let input = Stdlib.input_line Stdlib.stdin in
  if String.starts_with ~prefix:"%depth=" input
    then 
      let new_depth = int_of_string (String.sub input 7 ((String.length input) - 7)) in
      depth_loop_wrap g ind_depth new_depth  lp_top_level
    else
      let _ = print_endline ("Query: " ^ input) in
      let type_checked = read_and_parse_input input g in
      let _ = if Flags.d_lp_trace() then LazyLpLogging.begin_new_session () else 0 in
      let _ = if Flags.d_lp_trace() then log_lg (g.decls@type_checked.decls) input else () in
      let _ = lp_top_level ind_depth coind_depth g type_checked in
      let _ = if Flags.d_lp_trace() then LazyLpLogging.end_current_session () else () in
      depth_loop_wrap g ind_depth coind_depth  lp_top_level
  ) with 
    Failure s -> 
    (print_endline s;
    Printexc.print_backtrace Stdlib.stdout;
    if Flags.d_lp_trace() then LazyLpLogging.push_new_json_message "exception" (`String s) else ();
     print_endline "Exception occurred during program execution. Try again."; 
     if Flags.d_lp_trace() then LazyLpLogging.end_current_session () else ();
      depth_loop_wrap g ind_depth coind_depth  lp_top_level)
    (* | Sys.Break -> 
      (
        print_endline "Interrupted by user. Exiting.";
        LazyLpLogging.push_new_json_message "exception" (`String "Interrupted by user. Exiting.");
        LazyLpLogging.end_current_session ();
        depth_loop_wrap g ind_depth coind_depth  lp_top_level
      ) *)
  

let depth_loop_wrap_top ( g : A.ssig) (lp_top_level: int -> int -> A.ssig -> A.ssig -> unit) : unit = 
    depth_loop_wrap g default_inductive_limit default_coinductive_limit lp_top_level