module LF = CoLFSignature.CoLFSignature
module TP = CoLPTranslationSignature
module LP = CoLPSignature.CoLPSignature


let rec mkdir_p dir =
  if Sys.file_exists dir then
    if Sys.is_directory dir then ()
    else failwith (dir ^ " exists but is not a directory")
  else
    let parent = Filename.dirname dir in
    if parent <> dir then mkdir_p parent;
    Unix.mkdir dir 0o755 (* Permission: rwxr-xr-x *)

let write_file (original_fname : string) (desig : string) (content : string) = 
  let new_fname = original_fname ^ "." ^ desig in
  let oc = open_out new_fname in
  let _ = output_string oc content in
  close_out oc;
  print_endline ("                       + written " ^ new_fname ^ "")

(* let compile_to_nd (signature: Sig.t) : unit = 
  let rec aux (remaining : Sig.t) = 
    match remaining with
    | [] -> ()
    | Sig.TypeDecl(name, tp):: tl -> 
      let _ = (TypeChecking.synth_top Ctx.empty tp)  in 
      if Ctx.name_exists Ctx.empty (Ext.get_str_content name) then
        failwith ("Name already exists: " ^ (Ext.get_str_content name))
      else
        aux tl
let compile_to_nd_lab2_top_level (fname : string) (signature: Sig.t) : unit = 
  (* write to fname.nd *)
  let _ = mkdir_p ("_compilation/" ^ Filename.dirname fname) in
  let oc = open_out ("_compilation/" ^ fname ^ ".nd") in
  let _ = output_string oc (CoLFSignature.CoLFSignature.show_signature signature) in
  close_out oc *)

let compiled_exec_top_level (original_fname : string) (lf: LF.t) : unit = 
  let directory = Filename.dirname original_fname in
  let file_name = Filename.basename original_fname in
  let new_file_dir = 
    if Flags.c_debug "save"
      then directory ^ "/compiled/" 
      else directory ^ "/_compilation/" in
  let _ = mkdir_p new_file_dir in
  let new_file_name = new_file_dir ^ file_name in
  write_file new_file_name "a.0.colf" (CoLFSignature.CoLFSignature.show_signature lf);
  (* let lf2 = DupDeallocInsertion.dup_dealloc_insertion lf in *)
  let lf2 = ImplicitArgumentFilling.implicit_argument_filling lf in
  write_file new_file_name "a.1.colf" (CoLFSignature.CoLFSignature.show_signature lf2);
  TypeChecking.static_check_signature_top_level lf2;
  print_endline "[DONE] LF Type Checking";
  if Flags.tc_only() then (print_endline "[DONE] LF Type Checking only, exiting"; exit 0);
  let lf3 = DefinitionElaboration.definition_elaboration lf2 in
  write_file new_file_name "a.2.colf" (CoLFSignature.CoLFSignature.show_signature lf3);
  TypeChecking.static_check_signature_top_level lf3;
  print_endline "[DONE] LF Definition Elaboration";
  let tp_sig = LF_to_TP.extract_tp_sig_from_lf lf3 in
  print_endline "[DONE] LF to TP";
  write_file new_file_name "b.0.tp" (TP.show_signature tp_sig);
  let tp_final, _tp_intermediate = TP_to_TP_top.tp_to_tp_top tp_sig in
  print_endline "[DONE] TP to TP";
  write_file new_file_name "b.1.tp" (TP.show_signature tp_final);
  (* List.iteri (fun i it -> 
    write_file original_fname ("1." ^ string_of_int i ^ ".tp") (TP.show_signature it)
    ) tp_intermediate; *)
  let lp_sig_dup = TP_to_LP.tp_to_lp_top tp_final in
  print_endline "[DONE] TP to LP";
  write_file new_file_name "c.0.lp" (LP.show_sig_duplicated lp_sig_dup);
  let lp_sig = LP_Deduplication.deduplicate_lp lp_sig_dup in
  print_endline "[DONE] LP Deduplication";
  write_file new_file_name "c.1.lp" (LP.show_sig lp_sig);
  write_file new_file_name "d.0.sax" (LP.SAXPrint.print_sig lp_sig);
  write_file new_file_name "d.1.sax" (LP.SAXPrint.print_compact lp_sig);
  CoLPSignature.CoLPSignature.type_check_data_sig lp_sig.data_sig;
  CoLPSignature.CoLPSignature.type_check_relational_sig lp_sig.data_sig lp_sig.relational_sig;
  CoLPEioExec.exec_top lp_sig

  
