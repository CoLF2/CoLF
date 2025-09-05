module A = Ast
let getModeForTp (lg : A.ssig) (tp : A.abt) : A.abt = 
  let tp_head = AstOps.get_tp_head tp in
  let modes =  List.filter (fun (name, mode) -> name = "mode" && AstOps.get_tp_head mode = tp_head) lg.cmds in 
  match modes with
  | [] -> failwith ("No mode found for " ^ PrettyPrint.pp_abt lg.decls tp ^ " tp_head " ^ tp_head )
  | [(_, mode)] -> mode
  | _ -> failwith ("Multiple modes found for " ^ PrettyPrint.pp_abt lg.decls tp)

 