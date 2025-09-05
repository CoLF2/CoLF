
let current_session_count = ref 0

let begin_new_session () = 
  let _ = current_session_count := !current_session_count + 1 in
  !current_session_count

let messages = ref []

let push_new_json_message (sign : string) (msg : Yojson.Safe.t) = 
  let _ = messages := (!messages)@[
    `Assoc [
      ("type", `String sign);
      ("message", msg)
    ]
    ] in
  ()

let flush_current_json_msgs () = 

  let () = 
    if not (Sys.file_exists "_lazylplogs") then
      Sys.mkdir "_lazylplogs" 0o755
  in

  let session_number = !current_session_count in

  (* Construct the filename *)
  let filename = Printf.sprintf "_lazylplogs/%d.json" session_number in

  (* Dump the messages to the JSON file *)
  let json = `List !messages in
  let json_str = Yojson.Safe.pretty_to_string json in
  let oc = open_out filename in
  output_string oc json_str;
  close_out oc


let end_current_session () = 
  (* dump json to _lazylplogs/<session_number>.json *)

  let _ = flush_current_json_msgs () in


  let _ = messages := [] in
  ()
