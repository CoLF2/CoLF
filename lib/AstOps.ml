
module A = Ast



let rec replace_unif_vars_with_lppending (tm : A.abt) : A.abt = 
  match tm with
  | A.N(A.UnifVar _, _) -> 
    (
      A.N(A.LPPending, [])
    )
  | _ -> A.map_abt (replace_unif_vars_with_lppending ) tm

let rec get_tp_head (tp : A.abt) : string =
  match tp with
  | A.N(A.Pi, [_; t1]) -> get_tp_head (snd (A.unbind_expr t1))
  | A.N(A.At, t1::_) -> get_tp_head t1
  | A.N(A.Type, []) -> "Type"
  | A.N(A.CoType, []) -> "CoType"
  | A.FreeVar s -> s
  | _ -> failwith ("Unrecognized expression in get_tp_head " ^ A.ds_abt tp)
