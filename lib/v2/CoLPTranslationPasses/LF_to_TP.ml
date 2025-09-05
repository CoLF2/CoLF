
module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode
module LF = CoLFSignature.CoLFSignature
module TP = CoLPTranslationSignature
module LP = CoLPSignature.CoLPSignature
module Ext = AbtLib.Extent


let dereference_pis (tp : A.t) : string list (* free vars *) * A.t list * A.t_view = 
  let rec aux freevars sofar tp =
    match A.view tp with
    | A.N(N.Pi, [([], tp1); ([x], tp2)]) -> 
      (* check if hypothetical*)
        if A.appears_in_expr x tp2 then
          (* general, do the rest, skip tp1 *)
          aux (freevars@[x]) sofar tp2
        else
          aux freevars (sofar@[tp1]) tp2
    | tp_view -> (freevars, sofar, tp_view)
  in
  aux [] [] tp

type clause = {
  free_vars : string list;
  premises : A.t list;
  conclusion : A.t_view;
}

type classification = DataType | DataClause | RelationalType | RelationalClause

type ('a, 'b) map = ('a * 'b) list

type lf_t = (string, classification * clause) map
type lf_mode_t = (string, PairSplit.t) map


let lf_t_from_LF_t (lf : LF.t) : lf_t = 
  List.filter_map (fun x ->
    match x with
    | LF.TypeDecl(name, tp) -> (
      let name = Ext.get_str_content name in
      match dereference_pis tp with
      | [], [], A.N(N.CoType, []) -> Some (name, (DataType, { free_vars = []; premises = []; conclusion = A.N(N.CoType, []) }))
      | [], premises, A.N(N.CoType, []) -> Some (name, (RelationalType, { free_vars = []; premises = premises; conclusion = A.N(N.CoType, []) }))
      | [], premises, A.FreeVar(s) -> Some(name, (DataClause, { free_vars = []; premises = premises; conclusion = A.FreeVar(s) }))
      | fv, premises, A.N(N.Ap, args) -> Some(name, (RelationalClause, { free_vars = fv; premises = premises; conclusion = A.N(N.Ap, args) }))
      | free_vars, premises, concl -> failwith ("E48: Unsupported LF Declaration: " ^ name ^ " : " ^ A.show_view tp
        ^ "\nFree Vars: " ^ String.concat ", " free_vars
        ^ "\nPremises: " ^ String.concat ", " (List.map A.show_view premises)
        ^ "\nConclusion: " ^ A.show_view (A.fold concl)
      )
    )
    | _ -> None
  ) lf

let get_all_clauses_with_cls_from_lf_t (lf_t : lf_t) (cls : classification) : (string * clause) list =
  List.filter_map (fun (name, (cls', clause)) ->
    if cls' = cls then
      Some (name, clause)
    else
      None
  ) lf_t

let get_lf_mode_t_from_LF_t (lf : LF.t) (lf_t : lf_t) : lf_mode_t = 
  (* let lf_t = lf_t_from_LF_t lf in *)
  let relational_types = List.map fst (get_all_clauses_with_cls_from_lf_t lf_t RelationalType) in
  List.map (fun name ->
    let split = CoLFSignature.CoLFSignatureOps.lookup_unique_mode_declaration name lf in
    (name, PairSplit.from_list_f split (function | LF.Input -> PairSplit.Left | LF.Output -> PairSplit.Right))
  ) relational_types

let lookup_lf_mode_t (lf_mode_t : lf_mode_t) (name : string) : PairSplit.t = 
  ListUtil.lookup_elem_by_key lf_mode_t name

let find_all_data_types (lf : lf_t) : string list = 
    List.map ( function (name, _) -> name ) (get_all_clauses_with_cls_from_lf_t lf DataType)

let rec data_args_to_tp (premises : A.t_view list) : LP.tp = 
  match premises with
  | [] -> LP.TpUnit
  | [A.FreeVar(name)] -> LP.TpVar(name)
  | A.FreeVar(name_l)::rest ->
    LP.TpTensor(LP.TpVar(name_l), data_args_to_tp rest)
  | _ -> failwith "E44: Invalid premises in data type constructor"

let get_data_type_constructor_information (lf : lf_t) (tp_name : string) : (string * LP.tp) list = 
  List.filter_map
        ( function
        | (name, {free_vars=[]; premises=premises; conclusion=A.FreeVar(name')}) -> 
            (
              if name' = tp_name
                then (
                  Some (name, data_args_to_tp (List.map A.view premises))
                )
                else None
            )
        | _ -> failwith ("E78: Unsupported LF Declaration: ")
        ) (get_all_clauses_with_cls_from_lf_t lf DataClause)

let extract_data_types_from_lf (lf : lf_t) : LP.data_sig = 
  let all_data_type_names = find_all_data_types lf in
  List.map (fun tp_name -> 
    (tp_name, get_data_type_constructor_information lf tp_name)
  ) all_data_type_names

let rec lf_term_to_tp_type (v : A.t) : TP.LP.tp = 
  match A.view v with
  | A.FreeVar(name) -> LP.TpVar(name)
  | A.N(N.Pi, [[], dom; [_], cod]) -> 
      LP.TpArrow(lf_term_to_tp_type dom, lf_term_to_tp_type cod)
  | _ -> failwith ("E108: Invalid LF view: " ^ A.show_view v)

let rec lf_terms_to_tp_concl_type (vs : A.t list) : TP.LP.tp = 
  match vs with
  | [] -> LP.TpUnit
  | [v] -> lf_term_to_tp_type v
  | x :: ys -> LP.TpTensor(lf_term_to_tp_type x, lf_terms_to_tp_concl_type ys)


let rec fold_tps_using_tensor (tps : TP.LP.tp list) : TP.LP.tp = 
  match tps with
  | [] -> failwith ("E1123: Empty list of LF terms")
  | [tp] -> tp
  | x :: ys -> LP.TpTensor(x, fold_tps_using_tensor ys)

let rec fold_tms_using_pair (tps : TP.term list) : TP.term =
  match tps with
  | [] -> TP.TmUnit
  | [tp] -> tp
  | x :: ys -> TP.TmPair(x, fold_tms_using_pair ys)

let rec lf_term_to_tp_term (uni_exps : string list) (v : A.t) : TP.term = 
  match A.view v with
  | A.FreeVar(name) -> 
    if List.mem name uni_exps then
      TP.Ap(name, TP.TmUnit)
    else
      TP.Var(name)
  | A.N(N.Ap, ([], head)::args) -> 
    (
    match A.view head with
    | A.FreeVar(name) ->
      (* let head_arg' = lf_term_to_tp_term uni_exps head_arg in
      let args' = List.map (fun (_, x) -> lf_term_to_tp_term uni_exps x) args in *)
      let args' = List.map (fun (_, x) -> lf_term_to_tp_term uni_exps x) args in 
      if List.length args' = 0 then failwith ("E145: Ap empty spine: " ^ A.show_view v);
      TP.Ap(name, fold_tms_using_pair args')
    | _ -> failwith ("EL23: Invalid LF view: " ^ A.show_view v)
    )
  | A.N(N.Lam, [[var_name], body]) ->
      (* For lambda terms, we need to create a special representation
         This is a simplified approach - treating lambda as a special constructor *)
      let body_term = lf_term_to_tp_term (uni_exps @ [var_name]) body in
      TP.Ap("__lambda_" ^ var_name, body_term)
  | _ -> failwith ("EL92: Invalid LF view: " ^ A.show_view v)
(* and lf_terms_to_tp_term (uni_exps : string list) (vs : A.t list) : TP.term = 
  match vs with
  | [] -> failwith ("E112: Empty list of LF terms")
  | [v] -> lf_term_to_tp_term uni_exps v
  | x :: ys -> TP.TmPair(lf_term_to_tp_term uni_exps x, lf_terms_to_tp_term uni_exps ys) *)

(* let pair_split_by_mode (lf : lf_t) (rel_name : string) : PairSplit.t = 
  let modes = CoLFSignature.CoLFSignatureOps.find_unique_mode_declaration rel_name lf in
  let split = PairSplit.from_list_f modes (function | LF.Input -> PairSplit.Left | LF.Output -> PairSplit.Right) in
  split *)

(* let pair_split_by_mode (lf : lf_t) (rel_name : string) : PairSplit.t = 
  let modes = CoLFSignature.CoLFSignatureOps.find_unique_mode_declaration rel_name lf in
  let split = PairSplit.from_list_f modes (function | LF.Input -> PairSplit.Left | LF.Output -> PairSplit.Right) in
  split *)
  
let extract_relational_types_from_lf (lf : lf_t) (lf_mode : lf_mode_t) : TP.rel_type_signature = 
  List.map (function
      | (name, {free_vars=[];premises=depends;conclusion=A.N(N.CoType, [])}) ->
        (* This is a relational type, then figure out inputs and outputs *)
        (
          let split = lookup_lf_mode_t lf_mode name in
          assert (List.length split = List.length depends);
          let inputs = PairSplit.select_left split depends in
          let outputs = PairSplit.select_right split depends in
          let input_tps = List.map lf_term_to_tp_type inputs in
          let output_tp =  lf_terms_to_tp_concl_type outputs in
          (name, ({inputs=input_tps; output=output_tp}:TP.rel_type)) (*, (inputs, outputs)*)
        )
      | (name, _) -> failwith ("E140: Unsupported LF Declaration: " ^ name)
    ) (get_all_clauses_with_cls_from_lf_t lf RelationalType)

let get_premise_from_lf_term (unit_exps : string list) (lf_mode: lf_mode_t) (tm : A.t) : TP.premise = 
  match A.view tm with
  | A.N(N.Ap, ([], head)::args) -> 
    (
      match A.view head with
      | A.FreeVar(name) ->
        let args' = List.map (fun (_, x) -> lf_term_to_tp_term unit_exps x) args in
        let split = lookup_lf_mode_t lf_mode name in
        let input_args = PairSplit.select_left split args' in
        let output_args = PairSplit.select_right split args' in
        (* if List.length output_args = 0 then failwith ("E192LT: Ap empty spine: " ^ A.show_view tm); *)
        (input_args, name, fold_tms_using_pair output_args)
      | _ -> failwith ("EL132: Invalid LF view: " ^ A.show_view tm)
    )
  | _ -> failwith ("EL142: Invalid LF view: " ^ A.show_view tm)

let extract_relational_clauses_from_lf (unit_exps : string list)(lf : lf_t) (lf_mode : lf_mode_t) : TP.rel_clause_signature = 
  List.map (function
      | (name, {free_vars=_;premises=premises;conclusion=(A.N(N.Ap, _) as concl)}) -> (
        let concl' = get_premise_from_lf_term unit_exps lf_mode (A.fold concl) in
        let premises' = List.map (get_premise_from_lf_term unit_exps lf_mode) premises in
        (name, (premises', concl'))
      )
    | _ -> failwith ("E1544: Unsupported LF Declaration ")
  ) (get_all_clauses_with_cls_from_lf_t lf RelationalClause)

let extract_tp_sig_from_lf (lf_t_raw : LF.t) : TP.t = 
  let lf = lf_t_from_LF_t lf_t_raw in
  let lf_mode = get_lf_mode_t_from_LF_t lf_t_raw lf in
  let data_types = extract_data_types_from_lf lf in
  let rel_types = extract_relational_types_from_lf lf lf_mode in
  (* extracts newly inserted constants *)
  let unit_exps = List.concat_map (fun (_, clauses) -> 
      List.filter_map (fun (c_name, clause) -> 
        match clause with
        | LP.TpUnit -> Some c_name
        | _ -> None
      ) clauses
    ) data_types in
  (* let _ = print_endline ("unit_exps = " ^ String.concat ", " unit_exps) in *)
  let rel_clauses = extract_relational_clauses_from_lf unit_exps lf lf_mode in
  {
    data_sig = data_types;
    rel_sig = rel_types;
    rel_clause_sig = rel_clauses;
  }
