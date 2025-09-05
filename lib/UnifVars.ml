
module A = Ast

module UnifVarMap = Map.Make(Int)
module NameMap = Map.Make(String)

let all_unif_vars = ref UnifVarMap.empty

let all_unif_var_pretty_name = ref UnifVarMap.empty
let unif_var_name_count = ref NameMap.empty

let increment_name_count (name : string) : int = 
  let count = 
    if NameMap.mem name !unif_var_name_count 
    then NameMap.find name !unif_var_name_count
    else 0 in 
  let _ = unif_var_name_count := NameMap.add name (count + 1) !unif_var_name_count in 
  count + 1

(* arguments to Unif should be provided by Pi abstractions*)
let new_unif_var (tp : A.abt) (name_ref: string) : A.abt = 
  let id = Uid.next() in 
  let _ = all_unif_vars := UnifVarMap.add id tp !all_unif_vars in
  let name_idx = (increment_name_count name_ref) in
  let true_name = if name_idx <= 1 then name_ref else name_ref ^ (string_of_int name_idx) in
  let _ = all_unif_var_pretty_name := UnifVarMap.add id true_name !all_unif_var_pretty_name in
  A.N(A.UnifVar id, []) 

let lookup_unif_var_name (id : int) : string = 
  UnifVarMap.find id !all_unif_var_pretty_name

let get_unif_var_id_from_tm (tm : A.abt) : int = 
  match tm with 
  | A.N(A.UnifVar id, []) -> id
  | _ -> failwith ("get_unif_var_id: not a unif var, got " ^ A.ds_abt tm)

let get_tm_is_unif_var (tm : A.abt) : bool = 
  match tm with 
  | A.N(A.UnifVar _, []) -> true
  | _ -> false

let unif_var_id_to_term (id : int) : A.abt =
  A.N(A.UnifVar id, [])

let lookup_unif_var_tp (id : int) : A.abt = 
  UnifVarMap.find id !all_unif_vars