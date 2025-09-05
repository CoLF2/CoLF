let override_debug_on = false
(* let override_debug_on = true *)


(* let tr_debug = true  *)
let tr_debug = false || override_debug_on
(* let hs_debug = true  *)
let hs_debug = false 

(* let tcc_debug = true *)
let tcc_debug = false || override_debug_on
(* let unif_debug = true *)
let unif_debug = false || override_debug_on

(* let lp_debug = true *)
let lp_debug = false || override_debug_on 


(* let circ_debug = true *)
let circ_debug = false || override_debug_on

(* let ctx_always_show_full = true *)
let ctx_always_show_full = false


let show_ctx = false

let show_raw_lp_result = false


let c_debug_flags : string list ref = ref []

let add_c_debug_flag (s : string) : unit = 
  c_debug_flags := s :: !c_debug_flags

let c_debug (s : string) : bool = 
  List.mem s !c_debug_flags

(* let d_lp_debug = true *)
let d_lp_debug () = false || override_debug_on || c_debug "dlp"

let d_lp_trace () = false || c_debug "trace"