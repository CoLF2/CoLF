
let c_debug_flags : string list ref = ref []

let add_c_debug_flag (s : string) : unit = 
  c_debug_flags := s :: !c_debug_flags

let c_debug (s : string) : bool = 
  List.mem s !c_debug_flags

(* let d_lp_debug () = c_debug "dlp" *)

let show_parse_steps () = c_debug "show-parse-steps"
let show_type_checking_steps () = c_debug "show-type-checking-steps"
let substitution_debug () = c_debug "substitution-debug"
let use_lazy_substitution () = c_debug "use-lazy-substitution"