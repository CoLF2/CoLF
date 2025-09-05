
module A = Ast
module Ctx = TypeCheckingContext  
module HS = HereditarySubstitution
module Unif = Unification
module LPUtils = LogicProgrammingUtils
module UnifVarMap = Map.Make(Int)
module Log = LazyLpLogging


type configuration = {
  meta_vars : A.abt UnifVarMap.t; (* int -> pi typing map *)
  resolutions: A.abt UnifVarMap.t; (* int -> resolution map *) 
  constraints : (int * A.abt * A.abt) list; (* equations *)
  dependencies : (int list * int list) UnifVarMap.t; (* key id *)
  freemvars : (int * int list) UnifVarMap.t; (* free meta vars *)
  requested : (int * int) list;
}

let add_dependency (id : int) ((input, output) : int list * int list)  (dependencies : (int list * int list) UnifVarMap.t) : (int list * int list) UnifVarMap.t =
  (* if List.is_empty input && List.is_empty output *)
  (* then  *)
    (* dependencies *)
  (* else  *)
    UnifVarMap.add id (input, output) dependencies

let ds_unif_id (id : int) : string = 
  A.ds_abt (UnifVars.unif_var_id_to_term id)

let pp_unif_id (id : int) : string = 
  PrettyPrint.pp_abt [] (UnifVars.unif_var_id_to_term id)

let pp_abt (lg : A.ssig) (tm : A.abt)  : string = 
  PrettyPrint.pp_abt lg.decls tm

let pp_constraint (c: int * A.abt * A.abt) (lg : A.ssig) = (
  let (id, tm1, tm2) = c in
    pp_unif_id id ^ " |- " ^ pp_abt lg tm1 ^ " = " ^ pp_abt lg tm2 
) 

let ds_configuration (ctx: configuration) : string = 
  "{" ^ 
  "\n    ||MetaVars|| " ^ (UnifVarMap.fold (fun id tm acc -> acc ^ "⟨" ^ (ds_unif_id id) ^ "⟩ : " ^ A.ds_abt tm ^ ", ") ctx.meta_vars "") ^ 
  "\n    ||Resolutions|| " ^ (UnifVarMap.fold (fun id tm acc -> acc ^ "⟨" ^ (ds_unif_id id) ^ "⟩ : " ^ A.ds_abt tm ^ ", ") ctx.resolutions "") ^ 
  "\n    ||Constraints|| " ^ (String.concat ", " (List.map (fun (id, tm1, tm2) -> (ds_unif_id id) ^ " |- " ^ A.ds_abt tm1 ^ " = " ^ A.ds_abt tm2) ctx.constraints)) ^ 
  "\n    ||Dependencies|| " ^ (UnifVarMap.fold (fun id (input, output) acc -> acc ^ (String.concat ", " (List.map string_of_int input)) ^ " -> " ^ (ds_unif_id id) ^ " -> "  ^ (String.concat ", " (List.map string_of_int output)) ^ ", ") ctx.dependencies "") ^ 
  "\n    ||Requested|| " ^ (String.concat ", " (List.map (fun (id, depth) -> (ds_unif_id id) ^ " : " ^ (string_of_int depth)) ctx.requested))
  ^ "}"

let pp_configuration (lgsig : A.ssig) (ctx: configuration) : string = 
  let lg = lgsig.decls in
  "{" ^ 
(* String.concat "\n" (List.map (fun (id, tp) -> 
  "⟨" ^ (pp_unif_id id) ^ "⟩ : " ^ PrettyPrint.pp_abt lg tp
  ^ "\t "  ^ (if UnifVarMap.mem id ctx.dependencies 
              then (
                let (inputs, outputs) = UnifVarMap.find id ctx.dependencies in
                (String.concat ", " (List.map (pp_unif_id) inputs)) ^ " -> " ^ (pp_unif_id id) ^ " -> " ^ (String.concat ", " (List.map (pp_unif_id) outputs)))
              else "")
  ^ "\t " ^ (if UnifVarMap.mem id ctx.resolutions 
              then  pp_abt lg (UnifVarMap.find id ctx.resolutions) else "")
  ) (UnifVarMap.bindings ctx.meta_vars)
   ) ^ *)
  "\n    ||MetaVars|| " ^ (UnifVarMap.fold (fun id tm acc -> acc ^ "⟨" ^ (pp_unif_id id) ^ "⟩ : " ^ PrettyPrint.pp_abt lg tm ^ ", ") ctx.meta_vars "") ^ 
  "\n    ||Resolutions|| " ^ (UnifVarMap.fold (fun id tm acc -> acc ^ "⟨" ^ (pp_unif_id id) ^ "⟩ : " ^ PrettyPrint.pp_abt lg tm ^ ", ") ctx.resolutions "") ^ 
  "\n    ||Dependencies|| " ^ (UnifVarMap.fold (fun id (input, output) acc -> acc ^ (String.concat ", " (List.map (pp_unif_id) input)) ^ " -> " ^ (pp_unif_id id) ^ " -> "  ^ (String.concat ", " (List.map (pp_unif_id) output)) ^ ", ") ctx.dependencies "") ^ 
  "\n    ||Constraints|| " ^ (String.concat ", " (List.map (fun (id, tm1, tm2) -> (pp_unif_id id) ^ " |- " ^ PrettyPrint.pp_abt lg tm1 ^ " = " ^ PrettyPrint.pp_abt lg tm2) ctx.constraints)) ^ 
  "\n    ||Requested|| " ^ (String.concat ", " (List.map (fun (id, depth) -> (pp_unif_id id) ^ " : " ^ (string_of_int depth)) ctx.requested))
  ^ "}"


let debug () = Flags.d_lp_debug ()
let trace () = Flags.d_lp_trace ()


let log_action_message (msg: string) : unit = 
  let _ = if debug() then print_endline msg else () in
  Log.push_new_json_message "action" (`String msg)

let log_info_message (msg: string) : unit = 
  let _ = if debug() then print_endline msg else () in
  Log.push_new_json_message "info" (`String msg)

let is_output_unif_var_in_configuration (c : configuration) (id : int) : bool = 
  UnifVarMap.exists (fun _ (_input, output) -> List.mem id output) c.dependencies

let is_program_unif_var_in_configuration (c : configuration) (id : int) : bool = 
  UnifVarMap.mem id c.dependencies

let is_free_unif_var_in_configuration (c : configuration) (id : int) : bool = 
  UnifVarMap.mem id c.freemvars

let is_one_of_goals_in_configuration (c : configuration) (id : int) : bool = 
  List.mem id (List.map fst c.requested)

let get_free_unif_var_output_var_in_configuration (c : configuration) (id : int) : int list = 
  if not (is_free_unif_var_in_configuration c id)
    then failwith "Not a free unification variable"
  else snd (UnifVarMap.find id c.freemvars)

let get_free_unif_var_parent_var_in_configuration (c : configuration) (id : int) : int  = 
  if not (is_free_unif_var_in_configuration c id)
    then failwith "Not a free unification variable"
  else fst (UnifVarMap.find id c.freemvars)

let set_free_unif_var_output_var_in_configuration (c : configuration) (id : int) (parent : int) (output: int list) : configuration = 
  {c with freemvars = UnifVarMap.add id (parent, output) c.freemvars}

let get_all_output_unif_vars_in_configuration (c : configuration) : int list = 
  List.sort_uniq compare (UnifVarMap.fold (fun _ (_input, output) acc -> acc@output) c.dependencies [])

let get_program_unif_var_for_output_unif_var (c : configuration) (id : int) : int = 
  (* let _ = print_endline ("[⚠] finding " ^ ds_unif_id id) in *)
  (* let _ = print_endline (ds_configuration c) in *)
  if not (is_output_unif_var_in_configuration c id)
  then failwith "Not an output unification variable"
  else List.hd (List.filter_map (fun (key, (_, output)) -> if List.mem id output then Some key else None) (UnifVarMap.bindings c.dependencies))
  (* else fst (UnifVarMap.find_first (fun key -> 
    let _ = print_endline ("Map has dependencies" ^ (List.length (UnifVarMap.bindings c.dependencies) |> string_of_int)) in
    let deps = (snd (UnifVarMap.find key c.dependencies)) in
    let _ = print_endline ("[⚠] checking " ^ ds_unif_id key ^ " -> " ^ String.concat ", " (List.map string_of_int deps)) in
      List.mem id deps
    ) c.dependencies) *)

let append_output_unif_vars_to_program_unif_var (c : configuration) (id : int) (to_add: int list) : configuration =
  if UnifVarMap.mem id c.dependencies
  then 
    let (input, output) = UnifVarMap.find id c.dependencies in
    let new_output = List.sort_uniq compare (output@to_add) in
    {c with dependencies = UnifVarMap.add id (input, new_output) c.dependencies}
  else 
    {c with dependencies = UnifVarMap.add id ([], to_add) c.dependencies}

let append_free_unif_vars (c : configuration)(to_add: (int * (int * int list)) list) : configuration =
  {c with freemvars = List.fold_left (fun acc (id, deps) -> UnifVarMap.add id deps acc) c.freemvars to_add}

  (* TODO optimize this *)
let unif_ctx_from_configuration (c : configuration) : Ctx.unif_ctx = 
  UnifVarMap.fold (fun id tm acc -> Unif.add_unification_equation acc (UnifVars.unif_var_id_to_term id) tm) c.resolutions Ctx.empty_unif_ctx

let get_unif_var_tp (c : configuration) (id : int) : A.abt = 
  let tp = UnifVarMap.find_opt id c.meta_vars in
  match tp with
  | None -> failwith "Unification variable not found"
  | Some tp -> tp

let get_unif_var_is_resolved (c : configuration) (id : int) : bool = 
  UnifVarMap.mem id c.resolutions

let get_unif_var_resolution (c : configuration) (id : int) : A.abt = 
  let resolved_tm = UnifVarMap.find_opt id c.resolutions in
  match resolved_tm with
  | None -> failwith ("Unresolved unification variable, " ^ ds_unif_id id)
  | Some tm -> tm

let get_unif_var_subgoals_with_depth (c : configuration) (id : int) (id_depth: int) : (int * int) list = 
  let rec aux_resolve (tm : A.abt) (cur_depth : int) : (int * int) list = 
      if UnifVars.get_tm_is_unif_var tm
      then [(UnifVars.get_unif_var_id_from_tm tm, cur_depth)] 
      else
        match tm with
        | A.N(A.At, hd::spine) -> 
          if UnifVars.get_tm_is_unif_var hd
            then [(UnifVars.get_unif_var_id_from_tm hd, cur_depth)] 
            else List.concat_map (fun tm -> aux_resolve tm (cur_depth - 1)) spine
        | A.FreeVar(_) -> []
        | _ -> failwith ("Unhandled Subgoals "  ^ A.ds_abt tm)
    in
  let resolved_tm = get_unif_var_resolution c id in
  let result = aux_resolve resolved_tm id_depth in
  result
  (* List.filter (fun (id, _) -> is_output_unif_var_in_configuration c id) result *)

let rec get_unif_var_hereditary_resolution_fmv (c : configuration) (id : int) : int list = 
  if get_unif_var_is_resolved c id
  then
    let recur_fmv_or_self (id: int) = 
      if get_unif_var_is_resolved c id
      then get_unif_var_hereditary_resolution_fmv c id
      else [id] in
    let result = 
      (let resolved_tm = get_unif_var_resolution c id in
        match resolved_tm with
        | A.N(A.At, hd::spine) -> 
          if UnifVars.get_tm_is_unif_var hd
          then [UnifVars.get_unif_var_id_from_tm hd]
          else ListUtil.remove_duplicates (List.concat_map 
                  (fun tm -> List.concat_map (recur_fmv_or_self)
                  (A.collect_free_unif_vars tm)) spine)
        | _ -> failwith "Unexpected resolved term") in
    (* let _ = if debug() then log_info_message ("[FMV] " ^ pp_unif_id [] id ^ " -> " ^ String.concat ", " (List.map (pp_unif_id []) result)) in *)
    result
  else 
    []

let get_unif_var_hereditary_resolution (c : configuration) (id : int) : A.abt = 
  if get_unif_var_is_resolved c id
  then
    let rec recur_resolution_or_self (tm: A.abt) = 
      (match tm with
      | A.N(A.At, hd::spine) -> 
        if UnifVars.get_tm_is_unif_var hd
        then failwith "unimplemnted 190"
        else A.N(A.At, hd::(List.map recur_resolution_or_self spine))
      | A.FreeVar(_) -> tm
      | A.N(A.UnifVar i, []) -> 
        if get_unif_var_is_resolved c i
        then recur_resolution_or_self (get_unif_var_resolution c i)
        else tm
      | _ -> failwith ("188 Unexpected resolved term" ^ A.ds_abt tm)
      ) in
    let   resolved_tm = get_unif_var_resolution c id in
    (recur_resolution_or_self resolved_tm)
  else 
    UnifVars.unif_var_id_to_term id


 

let rec get_unif_var_max_resolution_depth (c : configuration) (id : int) : int = 
  if get_unif_var_is_resolved c id
    then
      let rec recur_tm (tm: A.abt) : int = 
        (if UnifVars.get_tm_is_unif_var tm
        then get_unif_var_max_resolution_depth c (UnifVars.get_unif_var_id_from_tm tm)
        else
          match tm with
          | A.N(A.At, _hd::spine) -> 1 + (
            match spine with
            | [] -> 0
            | _ -> 
                List.fold_left max 0 (List.map recur_tm spine)
          )
          | A.FreeVar(_) -> 0
          | _ -> failwith ("Unexpected resolved term, " ^ A.ds_abt tm)
        )
      in
      let resolved_tm = get_unif_var_resolution c id in
      recur_tm resolved_tm
    else 0

(* depth  and unif var id pair*)
let rec get_unif_var_min_resolution_depth_and_var (c : configuration) (id : int) : (int * int) option =
  if get_unif_var_is_resolved c id
    then
      let rec recur_tm (tm: A.abt) : (int * int) option = 
        (if UnifVars.get_tm_is_unif_var tm
        then 
          get_unif_var_min_resolution_depth_and_var c (UnifVars.get_unif_var_id_from_tm tm)
        else
          match tm with
          | A.N(A.At, _hd::spine) ->  (
            match spine with
            | [] -> None
            | _ -> 
                List.fold_left (fun prev this -> 
                  match prev , this with
                  | None, None -> None
                  | None, Some (x, x_id) -> Some (x + 1, x_id)
                  | Some x, None -> Some x
                  | Some (x, x_id) , Some (y, y_id) -> Some (if  x <= (y + 1) then (x, x_id) else (y + 1, y_id))
                    ) None (List.map recur_tm spine)
          )
          | A.FreeVar(_) -> None
          | _ -> failwith ("Unexpected resolved term, " ^ A.ds_abt tm)
        )
      in
      let resolved_tm = get_unif_var_resolution c id in
      recur_tm resolved_tm
    else Some (0, id)

let get_unif_var_min_resolution_depth (c : configuration) (id : int) : int option =
  match (get_unif_var_min_resolution_depth_and_var c id) with
  | Some (depth, _) -> Some depth
  | None -> None

let get_unif_var_min_resolution_depth_or_zero (c : configuration) (id : int) : int = 
  match get_unif_var_min_resolution_depth c id with
  | None -> 0
  | Some x -> x

(* let unif_var_is_fully_resolved_in_ctx (c : configuration) (id : int) : bool = 
  match get_unif_var_min_resolution_depth c id with
  | None -> false
  | Some _ -> true *)


(* exception SolutionNotFound
exception FoundSolution  of (Ctx.ctxtype * A.tm)  (* solution*)
                          * ( unit -> unit ) continue *)

(* let debug = true *)


let json_configuration (lg : A.ssig) (ctx : configuration) : Yojson.Safe.t = 
  `Assoc [
    ("meta_vars", `List (UnifVarMap.bindings ctx.meta_vars |> List.map (fun (id, tm) -> `Assoc [("id", `String (pp_unif_id id)); ("tp", `String (pp_abt lg tm))])));
    ("resolutions", `List (UnifVarMap.bindings ctx.resolutions |> List.map (fun (id, tm) -> `Assoc [("id", `String (pp_unif_id id)); ("tm", `String (pp_abt lg tm))])));
    ("dependencies", `List (UnifVarMap.bindings ctx.dependencies |> List.map (fun (id, (input, output)) -> `Assoc [("id", `String (pp_unif_id id)); ("input", `List (List.map (fun x -> `String (pp_unif_id x)) input)); ("output", `List (List.map (fun x -> `String (pp_unif_id x)) output))])));
    ("freemvars", `Assoc (UnifVarMap.bindings ctx.freemvars |> List.map (fun (id, (parent, possible_follow)) -> 
                    (pp_unif_id id,
                    `Assoc [("parent", `String (pp_unif_id parent)); ("following", `List (List.map (fun x -> `String (pp_unif_id x)) possible_follow))]
                    ))));
    ("constraints", `List (List.map (fun (id, tm1, tm2) -> `Assoc [("id", `String (pp_unif_id id)); ("tm1", `String (pp_abt lg tm1)); ("tm2", `String (pp_abt lg tm2))]) ctx.constraints));
    ("requested", `List (List.map (fun (id, depth) -> `Assoc [("id", `String (pp_unif_id id)); ("depth", `Int depth); 
      ("maxresolution", `Int (get_unif_var_max_resolution_depth ctx id));
      ("minresolution",  (match get_unif_var_min_resolution_depth ctx id with None -> `Null | Some x -> `Int x));
      ("resolution", `String (pp_abt lg (get_unif_var_hereditary_resolution ctx id)));
      ]) ctx.requested));

  ]

type failure_kont = unit -> unit
type lp_solution = (configuration)
type succss_kont = lp_solution -> failure_kont -> unit
type depth_ctx =  int * int (* trial depth, inductive depth, coinductive depth *)

let generate_spine_from_premise_tp_and_config (ctx: configuration) (pi_tp : A.abt) : configuration * A.abt list (* spine *) * A.abt (* remaining pi type *)= 
  let rec aux (cur_ctx : configuration) (cur_tp : A.abt) (spine : A.abt list)  : configuration * A.abt list * A.abt = 
    match cur_tp with
    | A.N(A.Pi, [t1; t2]) -> 
      let (t2_bnd, t2_body) = A.unbind_expr t2 in
        let v = UnifVars.new_unif_var t1 t2_bnd in (* TODO: eta expand v*)
        let new_ctx = {cur_ctx with meta_vars = UnifVarMap.add (UnifVars.get_unif_var_id_from_tm v) t1 cur_ctx.meta_vars} in
        aux new_ctx (A.hereditary_subst v (t2_bnd) t2_body) (spine@[v])
    | _ -> cur_ctx, spine, cur_tp
  in
    aux ctx pi_tp []

let populate_ctx_dependencies_new_spine (ctx: configuration) 
             (lg: A.ssig) (meta_var_base_tp : A.abt) (meta_var_final_tp: A.abt)
             (requested_unif_var_id : int)
             (spine: A.abt list) (pi_tp : A.abt) : configuration = 
  let processed_spine = List.map (fun tm -> UnifVars.get_unif_var_id_from_tm tm) spine in
  let mode_for_unif_var = ModeUtils.getModeForTp lg meta_var_final_tp in
  let input_meta_vars_and_deps = (match mode_for_unif_var, meta_var_final_tp, meta_var_base_tp with
    | A.N(A.At, _::mode_spine), A.N(A.At, _::final_spine), A.N(A.At, _ ::base_spine) -> (
        let _ = if List.length mode_spine != List.length final_spine || List.length final_spine != List.length base_spine then failwith ("197 Arity mismatch " ^ A.ds_abt mode_for_unif_var ^ " not= " ^ String.concat ", " (List.map A.ds_abt spine)) else () in
        ListUtil.remove_duplicates (List.concat (List.mapi (fun index final_elem -> 
          let mode_elem = List.nth mode_spine index in
          let base_elem = List.nth base_spine index in
          match mode_elem with
          | A.FreeVar(mode_designation) ->  (
            match mode_designation.[0] with
            | '+' -> (
              let rec match_final_with_base_elem (this_final_elem : A.abt) (this_base_elem: A.abt) = (
                let default_return = (fun () -> 
                  let this_meta_vars = ListUtil.intersect processed_spine (A.collect_free_unif_vars final_elem) in 
                  let this_deps = List.filter (fun id -> is_output_unif_var_in_configuration ctx id || is_free_unif_var_in_configuration ctx id) (A.collect_free_unif_vars base_elem) in
                  List.map (fun id -> (id, (requested_unif_var_id, this_deps))) this_meta_vars 
                ) in
                if UnifVars.get_tm_is_unif_var this_final_elem
                then 
                  let this_final_id = UnifVars.get_unif_var_id_from_tm this_final_elem in
                  let _ = if not (List.mem this_final_id processed_spine) then failwith ("Unresolved unification variable " ^ A.ds_abt this_final_elem) else () in
                  let this_deps = List.filter (fun id -> is_output_unif_var_in_configuration ctx id || is_free_unif_var_in_configuration ctx id) (A.collect_free_unif_vars this_base_elem) in
                  (this_final_id, (requested_unif_var_id, this_deps))::[]
                else
                match this_final_elem, this_base_elem with
                | A.N(A.At, hd_final::final_elem_spine), A.N(A.At, hd_base::base_elem_spine) -> 
                  if hd_final = hd_base 
                    then 
                      let _ = if List.length final_spine != List.length base_spine then failwith ("349 Arity mismatch " ^ A.ds_abt this_final_elem ^ " not= " ^ A.ds_abt this_base_elem) else () in
                      List.concat (List.map2 match_final_with_base_elem final_elem_spine base_elem_spine)
                    else
                      default_return()
                | _ -> default_return()
              ) in 
              match_final_with_base_elem final_elem base_elem
            )
            | _ -> []
          )
          | _ -> failwith ("Unexpected mode " ^ A.ds_abt mode_elem)
        ) final_spine))
      )
    | A.FreeVar _, A.FreeVar _, A.FreeVar _ -> []
    | _ -> failwith ("Unexpected mode type " ^ A.ds_abt mode_for_unif_var ^ " and " ^ A.ds_abt meta_var_final_tp ^ " and " ^ A.ds_abt meta_var_base_tp)
  ) in
  let input_meta_vars = List.map fst input_meta_vars_and_deps in
  (* let updated_ctx = append_output_unif_vars_to_program_unif_var ctx requested_unif_var_id input_meta_vars in *)
  let updated_ctx = append_free_unif_vars ctx input_meta_vars_and_deps in
  (* let updated_ctx = ctx in *)
  let rec aux (cur_ctx : configuration) (cur_tp : A.abt) (remaining_spine : int list)  (free_meta_vars: int list) : configuration = 
    match (cur_tp, remaining_spine) with
    | (A.N(A.Pi, [t1; t2]), this_meta::spine_tl) -> 
      let (t2_bnd, t2_body) = A.unbind_expr t2 in
      if A.appears_in_expr t2_bnd t2_body
      then 
        let next_free_meta_vars = if List.mem this_meta input_meta_vars then free_meta_vars else free_meta_vars@[this_meta] in
        aux cur_ctx (A.hereditary_subst (UnifVars.unif_var_id_to_term this_meta) (t2_bnd) t2_body) spine_tl next_free_meta_vars
      else 
        let t1_fmv = A.collect_free_unif_vars t1 in 
        let new_ctx = {cur_ctx with
          dependencies = add_dependency this_meta 
            (ListUtil.minus t1_fmv free_meta_vars, ListUtil.intersect t1_fmv free_meta_vars) cur_ctx.dependencies  
         } in
        aux new_ctx t2_body spine_tl (ListUtil.minus free_meta_vars t1_fmv)
    | (_, []) -> cur_ctx
    | _ -> failwith "Unexpected spine"
  in
    aux updated_ctx pi_tp processed_spine []


let step_configuration_search_candidates (ctx: configuration) (lg : A.ssig) (requested_unif_var_id: int) : configuration list = 
  let metavar_tp = get_unif_var_tp ctx requested_unif_var_id in
  let (metavar_ctx, metavar_base_tp) = Ctx.ctx_from_pi_types metavar_tp in
  let available_premises = metavar_ctx @ (List.map (fun ((name, tp)) -> (name, tp)) lg.decls) in
  let applicable_premises = List.filter (fun (_, tp) -> AstOps.get_tp_head tp = AstOps.get_tp_head metavar_tp) available_premises  in
  List.map (fun (name, tp) -> 
    let (intermediate_ctx, spine, remaining_tp) = generate_spine_from_premise_tp_and_config ctx tp in
    let (new_ctx) = populate_ctx_dependencies_new_spine intermediate_ctx lg metavar_base_tp remaining_tp requested_unif_var_id spine tp in
      {new_ctx with 
        constraints = (requested_unif_var_id, metavar_base_tp, remaining_tp)::ctx.constraints;
        resolutions = UnifVarMap.add requested_unif_var_id (Ctx.lam_tm_from_ctx metavar_ctx (A.N(A.At, A.FreeVar(name) :: spine))) ctx.resolutions;
        }
  ) applicable_premises

let step_count = ref 0

let rec step_configuration (ctx: configuration) (lg : A.ssig) (succss_k: succss_kont) (failure_k : failure_kont) : 'a = 
  let _ = if trace() then Log.push_new_json_message "current_config" ( json_configuration lg ctx) else () in
  let _ = step_count := !step_count + 1 in
  let _ = print_string (
    if List.is_empty ctx.requested
    then 
      "\r[⚙] Step " ^ string_of_int !step_count ^ ". Goal Stack is empty.     \n"
    else
      "\r[⚙] Step " ^ string_of_int !step_count ^
      (
        (* if debug() 
          then 
      let initial_goal = fst (List.nth ctx.requested (List.length ctx.requested - 1)) in
      let initial_goal_resolution = get_unif_var_hereditary_resolution ctx (initial_goal) in
        ". Current resolution for " ^ pp_unif_id initial_goal ^ " is " ^ (pp_abt lg initial_goal_resolution) 
        ^ ". Goal Stack is" ^ (String.concat ", " (List.map (fun (id, depth) -> pp_unif_id id ^ " : " ^ string_of_int depth) (List.rev ctx.requested)))
        ^ ".     "
        else  *)
          ""
      )
    ) in
  let _ = flush stdout in
  (* let _ = if debug() then print_endline ("current_config: " ^ pp_configuration lg ctx) else () in *)
  process_constraints ctx lg succss_k failure_k
and process_constraints (ctx: configuration) (lg : A.ssig)  (succss_k: succss_kont) (failure_k : failure_kont) : 'a = 
  let rec process_constraints_aux (cur_ctx: configuration) (sofar : (int * A.abt * A.abt) list) (remaining: (int * A.abt * A.abt) list) (next: configuration -> 'a) : 'a = 
    let simplify_constraint (id, tm1, tm2) = 
      let tm1' = Unification.deref_all_unifvar (unif_ctx_from_configuration cur_ctx) tm1 in
      let tm2' = Unification.deref_all_unifvar (unif_ctx_from_configuration cur_ctx) tm2 in
      (id, tm1', tm2') in
    match remaining with
    | [] -> next {cur_ctx with constraints = sofar}
    | cur_constraint::constraint_tail -> (
      let simplified_constraint = simplify_constraint cur_constraint in
      let pp_current_constraint () = pp_constraint cur_constraint lg in
      let pp_simplified_constraint () = pp_constraint simplified_constraint lg in
      let _ = if trace() then log_action_message ("[⚙] eqn " ^ pp_current_constraint() ^ " is " ^ pp_simplified_constraint ()) in
      (* let _ = if debug() then print_endline ("[⚙] eqn " ^ pp_current_constraint() ^ " is " ^ pp_simplified_constraint ()) in *)
      let resolution_condition_for_unif_id (parent_id: int)(candidate_id: int) = 
          (is_output_unif_var_in_configuration cur_ctx candidate_id && parent_id = get_program_unif_var_for_output_unif_var cur_ctx candidate_id)
          || (UnifVarMap.mem candidate_id cur_ctx.freemvars && parent_id = get_free_unif_var_parent_var_in_configuration cur_ctx candidate_id) 
          (* || (UnifVarMap.mem candidate_id cur_ctx.freemvars && List.is_empty (get_free_unif_var_output_var_in_configuration cur_ctx candidate_id))  *)
      in
      match simplified_constraint with
      | (id, (A.N (A.At, hd_l::args_l)), A.N (A.At, hd_r::args_r)) -> 
            if hd_l <> hd_r 
              then (
                let _ = if trace() then log_action_message ("[✗ FAIL] head mismatch " ^ pp_abt lg hd_l ^ " != " ^ pp_abt lg hd_r) in
                failure_k ()
              ) 
            else 
              if List.length args_l != List.length args_r then
                failwith "Arity mismatch"
              else 
                let new_constraints = List.map2 (fun l r -> (id, l, r)) args_l args_r in
                process_constraints_aux cur_ctx sofar (new_constraints@constraint_tail) next
      | (_, A.N(A.UnifVar _, []), A.N(A.UnifVar _, [])) -> (
        process_constraints_aux cur_ctx (sofar@[cur_constraint]) constraint_tail next
      )
      | (id, A.N(A.UnifVar id_l, []), tm_r) -> (
        if resolution_condition_for_unif_id id id_l
          then 
            let _ = if trace() then log_action_message ("[✓ RESOLVED] " ^ pp_unif_id id_l ^ " = " ^ pp_abt lg tm_r ^ " for eqn " ^ pp_current_constraint()) in
            process_constraints_aux {cur_ctx with resolutions = UnifVarMap.add id_l tm_r cur_ctx.resolutions} sofar constraint_tail next
          else 
            if not (is_one_of_goals_in_configuration cur_ctx id_l)
              then (
                let _ = if trace() then log_action_message ("[↗ CONSTRAINT INDUCED GOAL] " ^ pp_unif_id id_l) in
                (* Depth 1 is sufficient because otherwise this will be resolved *)
                process_constraints_aux {cur_ctx with requested = (id_l, 1)::ctx.requested}  (sofar@[cur_constraint]) constraint_tail next
              )
              else process_constraints_aux cur_ctx (sofar@[cur_constraint]) constraint_tail next
      )
      | (id, tm_l, A.N(A.UnifVar id_r, [])) -> (
        if resolution_condition_for_unif_id id id_r
          then 
            let _ = if trace() then log_action_message ("[✓ RESOLVED] " ^ pp_unif_id id_r ^ " = " ^ pp_abt lg tm_l ^ " for eqn " ^ pp_current_constraint()) in
            process_constraints_aux {cur_ctx with resolutions = UnifVarMap.add id_r tm_l cur_ctx.resolutions} sofar constraint_tail next
          else 
            if not (is_one_of_goals_in_configuration cur_ctx id_r)
              then (
                let _ = if trace() then log_action_message ("[↗ CONSTRAINT INDUCED GOAL] " ^ pp_unif_id id_r) in
                (* Depth 1 is sufficient because otherwise this will be resolved *)
                process_constraints_aux {cur_ctx with requested = (id_r, 1)::ctx.requested}  (sofar@[cur_constraint]) constraint_tail next
              )
              else process_constraints_aux cur_ctx (sofar@[cur_constraint]) constraint_tail next
      )
      | (id, A.FreeVar l, tm_r) -> 
        process_constraints_aux cur_ctx sofar ((id, A.N(A.At, [A.FreeVar l]), tm_r)::constraint_tail) next
      | (id, tm_l, A.FreeVar r) ->
        process_constraints_aux cur_ctx sofar ((id, tm_l, A.N(A.At, [A.FreeVar r]))::constraint_tail) next
      | (id, tm_l, tm_r) -> failwith ("Unexpected constraint " ^ pp_unif_id id ^ " |- " ^ pp_abt lg tm_l ^ " = " ^ pp_abt lg tm_r)
    ) in
  let rec repeat_constraints_until_stable (cur_ctx: configuration) : 'a = 
    process_constraints_aux cur_ctx [] cur_ctx.constraints (fun next_ctx -> 
        if List.length next_ctx.constraints = List.length cur_ctx.constraints
        then process_goals next_ctx lg succss_k failure_k
        else repeat_constraints_until_stable next_ctx
      ) in
  repeat_constraints_until_stable ctx 
and process_goals (ctx: configuration) (lg : A.ssig) (succss_k: succss_kont) (failure_k : failure_kont) : 'a = 
    match ctx.requested with
    | [] -> succss_k ctx failure_k
    | (requested_unif_var_id, depth)::requested_tail -> 
      if List.length (List.filter (fun x -> x = (requested_unif_var_id, depth)) requested_tail) > 10
        then failwith "Possible Cycle Detected During Search"
        else
          let _ = if trace() then log_info_message ("Current Goal " ^ pp_unif_id requested_unif_var_id ^ " (" ^ string_of_int depth ^ ")" ) else () in
          if  (* check alrady resolved to depth *)
            (match get_unif_var_min_resolution_depth ctx requested_unif_var_id with None -> true | Some x -> depth <= x)
          then 
            let _ = if trace() then log_action_message ("[✓ OK] " ^ pp_unif_id requested_unif_var_id ^ " Done") else () in
            step_configuration {ctx with requested = requested_tail} lg succss_k failure_k
          else 
            if get_unif_var_is_resolved ctx requested_unif_var_id
              then (
                let new_requested = get_unif_var_subgoals_with_depth ctx requested_unif_var_id depth in
                let new_ctx = {ctx with requested = new_requested@ctx.requested} in
                let _ = if trace() then log_action_message ("[↘ DEEPER] " ^ pp_unif_id requested_unif_var_id ^ " -(currently resolved as)-> " ^ pp_abt lg (get_unif_var_resolution ctx requested_unif_var_id)) in
                step_configuration new_ctx lg succss_k failure_k
              )
              else
              if is_free_unif_var_in_configuration ctx requested_unif_var_id then (
              (* we need to check if there is an equation involving this and another unresolved unification var *)
                match get_free_unif_var_output_var_in_configuration ctx requested_unif_var_id with
                | [output_var] -> (
                  let _ = if trace() then log_action_message ("[↔ FORWARDING] " ^ pp_unif_id requested_unif_var_id ^ " ~> " ^ pp_unif_id output_var) in
                  step_configuration {ctx with requested = (output_var, get_unif_var_min_resolution_depth_or_zero ctx output_var + 1)::ctx.requested} lg succss_k failure_k
                )
                | [] -> (
                  failwith ("Does not know how to progres free var " ^ pp_unif_id requested_unif_var_id)
                )
                | multiple -> (
                  failwith ("Multiple output vars for " ^ pp_unif_id requested_unif_var_id ^ " : " ^ String.concat ", " (List.map pp_unif_id multiple))
                )
                )
              else 
                (* this function steps (putting into goal) program var for some output var *)
                let step_program_var (prgm_unif_var : int) = 
                  let prgm_depth = get_unif_var_min_resolution_depth_or_zero ctx prgm_unif_var in
                  let new_ctx = {ctx with requested = (prgm_unif_var, prgm_depth + 1)::ctx.requested} in
                  let _ = if trace() then log_action_message ("[↺ RUN] " ^ pp_unif_id prgm_unif_var ^ "(" ^ string_of_int prgm_depth ^ ")"  ^ " =(outputting)=> " ^ pp_unif_id requested_unif_var_id ) in
                  step_configuration new_ctx lg succss_k failure_k
                in
                if is_output_unif_var_in_configuration ctx requested_unif_var_id
                then (
                  step_program_var  (get_program_unif_var_for_output_unif_var ctx requested_unif_var_id )
                )
                (* check if requsted_unif_var is a program var*)
                else if UnifVarMap.mem requested_unif_var_id ctx.dependencies
                  then
                    (
                      let rec try_premises 
                                (remaining : configuration list) 
                                (cur_success_k : succss_kont)
                                (cur_failure_k : failure_kont) : 'a =
                        match remaining with
                        | [] -> cur_failure_k ()
                        | cur_ctx::tl -> 
                          (
                            let cur_failure_k' = fun () -> try_premises tl cur_success_k cur_failure_k in
                            let _ = if trace() then log_action_message ("[◊ TRY] " ^ pp_unif_id requested_unif_var_id ^ " -> " ^ pp_abt lg (get_unif_var_resolution cur_ctx requested_unif_var_id)) else () in
                            step_configuration cur_ctx lg cur_success_k cur_failure_k'
                          )
                        in
                        try_premises (step_configuration_search_candidates ctx lg requested_unif_var_id) succss_k failure_k
                    )
                else
                  failwith ("No classification for variable " ^ pp_unif_id requested_unif_var_id)


let request_unifvar_to_depth (ctx: configuration) (resolution: (string * A.abt) list)  (depth: int) : configuration = 
  ( let all_outputs = List.filter (is_output_unif_var_in_configuration ctx) (List.map (fun (_, v)  -> UnifVars.get_unif_var_id_from_tm v) resolution) in
    let last_unif_var = (
      if List.length all_outputs = 0
      then 
        (
          if List.length resolution = 0
          then failwith "Empty Signature. Cannot find any output."
          else UnifVars.get_unif_var_id_from_tm (snd (List.hd (List.rev resolution)))
      ) else List.hd (List.rev all_outputs)
    ) in
    let starting_ctx = {
        ctx with requested = [(last_unif_var, depth)]
      } in 
    let _ = if debug() then print_endline ("Start Proof Search for : " ^ (ds_unif_id last_unif_var) ^ " in " ^ ds_configuration starting_ctx) else () in
    starting_ctx 
  )


let lp_top_level (ind_depth : int) (coind_depth : int) (global : A.ssig) (local : A.ssig) : unit =
  if not (List.is_empty local.cmds)
    then failwith "Local context should not have commands"
  else
  let rec process_local 
            (ctx : configuration) 
            (resolution : (string * A.abt) list)
            (processed : A.decls) 
            (remaning : A.decls) : configuration * (string * A.abt) list =
    match remaning with
    | ((name, tp)::tl) -> 
      (
          let v = UnifVars.new_unif_var tp name in
          let deps = List.partition (fun unif_var_id -> is_output_unif_var_in_configuration ctx unif_var_id) (A.collect_free_unif_vars tp) in
          let is_dependent = List.exists (fun ((_, tp)) -> A.appears_in_expr name tp) tl in
          let new_remaining = List.map (fun ((n, tp)) -> (n, A.subst v name tp)) tl in
          process_local { ctx with 
            meta_vars = UnifVarMap.add (UnifVars.get_unif_var_id_from_tm v) tp ctx.meta_vars;
            dependencies = 
             ( (* only add dependencies if not dependent *)
              if is_dependent 
              then ctx.dependencies 
              else add_dependency (UnifVars.get_unif_var_id_from_tm v) deps ctx.dependencies);
           } (resolution@[(name, v)]) (processed@[((name, tp))]) new_remaining 
      )
    | [] -> (
      request_unifvar_to_depth ctx resolution coind_depth, resolution
        (* step_configuration starting_ctx global (fun ctx' failure_k' -> success_k (ctx', resolution) failure_k') failure_k *)
    )
  in 
  let (starting_ctx, resolution) = process_local {
        meta_vars = UnifVarMap.empty;
        resolutions = UnifVarMap.empty;
        constraints = [];
        dependencies = UnifVarMap.empty;
        freemvars = UnifVarMap.empty;
        requested = [];
      } [] [] local.decls in
  let rec repl_loop 
    (guide_ctx : configuration)
    (depth_ctx: depth_ctx) =
      let success_kont = (fun ((config : configuration) ) failure_kont' -> 
        (
          let unif_ctx = unif_ctx_from_configuration config in
          let resolved_resolution = (List.map (fun (name, tm) ->
                    let resolved_tm = (Unification.deref_all_unifvar unif_ctx tm) in 
                    (name, UnifVars.get_unif_var_id_from_tm tm, resolved_tm)
                    ) resolution) in
          let _ = print_endline 
            (
              (if Flags.show_raw_lp_result
                then ((String.concat ", " (List.map (fun (name, tm) -> name ^ " = " ^ A.ds_abt tm) resolution)) ^ "\n" ^
                      Ctx.ds_unif_ctx unif_ctx ^ "\n") else "")
            ^ (
              let _ = if debug() then print_endline (pp_configuration global config) else () in
                  "Success: " ^ (String.concat ",\n" (List.map (fun (name, unif_var_id, resolved_tm) ->
                     name ^ " (?" ^  string_of_int unif_var_id ^ ")" ^ " = " ^ pp_abt global resolved_tm  ^ 
                     ( 
                      match (Ctx.find_id_sig_local name local.decls) with
                      | None -> failwith ("Cannot find " ^ name ^ " in the local context")
                      | Some tp_def ->
                      let tp_name = (AstOps.get_tp_head tp_def) in
                      if PrettyPrint.tp_name_has_special_pp tp_name
                      then " ~~> " ^ PrettyPrint.special_pp_top_level global.decls resolved_tm ^ ""
                      else ""
                     )) 
                     resolved_resolution)) ^ "\n" ^
                     (String.concat ",\n" (List.filter_map (fun (name, _, resolved_tm) ->
                      
                       match (Ctx.find_id_sig_local name local.decls) with
                       | None -> failwith ("Cannot find " ^ name ^ " in the local context")
                       | Some tp_def ->
                       let tp_name = (AstOps.get_tp_head tp_def) in
                       if PrettyPrint.tp_name_has_special_pp tp_name
                       then  Some (name ^   " = "  ^ PrettyPrint.special_pp_top_level global.decls resolved_tm ^ "")
                       else None
                      ) 
                      resolved_resolution))
                ^ "\n"
            )
            ) in
          let _ = if trace() then Log.flush_current_json_msgs() else () in
          let _  = Stdlib.output_string Stdlib.stdout (LPUtils.ds_depth_ctx depth_ctx ^ " (type `;` for next, type `:` (or `u`) to increase depth (while commiting to the current choice), type `.` to end) ")  in
          let _ = Stdlib.flush Stdlib.stdout  in
          let prompt_char = IOUtils.get1char () in
          let (cur_coind, cur_ind) = depth_ctx in
          let _ = print_newline() in
          match prompt_char with
          | ';' -> (failure_kont'())
          | ':' -> 
            (let _ = if trace() then log_info_message ("Requesting up to depth " ^ string_of_int (cur_coind * 2)) else () in
              (repl_loop (request_unifvar_to_depth config resolution (cur_coind * 2)) (cur_coind * 2, cur_ind))
            )

          | 'u' -> 
            (let _ = if trace() then log_info_message ("Requesting up to depth " ^ string_of_int (cur_coind + 1)) else () in
              (repl_loop (request_unifvar_to_depth config resolution (cur_coind + 1)) (cur_coind + 1, cur_ind))
            )
          | _ -> ()
        )) in 
      let failure_kont = fun () -> print_endline ("Failed") in 
      (* process_local guide_ctx [] [] local success_kont failure_kont *)
      step_configuration guide_ctx global success_kont failure_kont
  in
  repl_loop starting_ctx (coind_depth, ind_depth)
  
  
  


  
  
let loop_top g = LPUtils.depth_loop_wrap_top g lp_top_level


(* 
   
TODO: 

0. Real arithmetic as an example
1. Padded Streams, stream processors (e.g. adding two streams together, compute diagonal of a stream of streams)
2. Ternary arithmetic


1. Pretty print omit parametric arguments
2. Print the terms in the format M1, M2, M3, ..., not ap[M1; M2; .. M3]
3. Mode checker 
4. Productivity and termination checking
5. Coverage checking
6. (Later) Metatheorem

*)