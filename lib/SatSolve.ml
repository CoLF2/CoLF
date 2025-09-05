
module LPUtils = LogicProgrammingUtils
module A = Ast

let max_width = 10
let mAX_DEPTH = 100
type sat = Sat
(* 
let abt_to_sat (lg: A.decls) (abt: A.abt) : int list list = 
  let rec abt_to_sat_rec (sofar : int list) (abt: A.abt) : int list list = 
    match abt with
    | A.FreeVar(c) -> [[0]]
    | A.Bnd(_, sub) -> abt_to_sat_rec sub
    | A.BoundVar(i) -> []
    | A.N(_, tl) -> List.concat (List.map abt_to_sat_rec tl)
  in 
  List.map (fun l -> List.sort_uniq compare l) (abt_to_sat_rec abt)

 *)
let new_sat() : sat = Sat

let rec sat_loop (sat: sat) (lg: A.decls) (goal: A.abt) : unit = 
  sat_loop sat lg goal

  


let lp_top_level (_ind_depth : int) (_coind_depth : int) (global : A.ssig) (local : A.ssig) : unit =
  if List.length (local.decls) != 1
    then failwith "Expected exactly one declaration."
  else
  (
    sat_loop (new_sat()) global.decls (List.hd local.decls |> snd) 
  )
  
  
  
let loop_top g = LPUtils.depth_loop_wrap_top g lp_top_level
