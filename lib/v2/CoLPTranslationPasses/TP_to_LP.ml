
module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode
module LF = CoLFSignature.CoLFSignature
module TP = CoLPTranslationSignature
module LP = CoLPSignature.CoLPSignature
module Ext = AbtLib.Extent

let find_unique_guarded_idx_in_list (list : TP.term list) : int option  = 
  match ListUtil.filter_map_i (fun i term ->
    match term with
    | TP.Ap _ -> Some i
    | TP.TmUnit -> Some i
    | _ -> None
    ) list with
  | [] -> None
  | [guarded_idx] -> Some guarded_idx
  | _ -> failwith "Multiple guarded indices found in list"

let force_unwrap_tp_var (tp : TP.term) : string =
  match tp with
  | TP.Var x -> x
  | _ -> failwith ("E30: Expected a variable, got " ^ TP.show_term tp)

(* check if the clause is of the form (premise_in, premise_name, premise_out) -> (concl_in, concl_name, concl_out)
   and that the premise_out matches the conclusion_out *)

(* returns constructor_name -> premise name pair *)
let check_clause_is_plus_left_with_idx (idx : int) (clause : TP.rel_clause) : string * string =
  match clause with
  | ([premise_in, premise_name, premise_out], (concl_in, concl_name, concl_out)) -> (
    if premise_out <> concl_out then failwith ("E31: Premise and conclusion outputs do not match in clause " ^ concl_name);
    let supposed_premise_in = List.mapi (fun i term ->
      match term with
      | TP.Ap(_cons_name, TP.Var arg) -> (
        if i <> idx then failwith ("E32: expecting unique terms in premise " ^ premise_name);
        arg
      )
      | TP.Var x -> (
        if i = idx then failwith ("E32: Uniqueness violated, expecting unique constructor terms in premise " ^ premise_name);
        x
      )
      | _ -> failwith ("E342: Unsupported term in premise " ^ premise_name ^ " " ^ TP.show_rel_clause clause)
    ) concl_in in
    if supposed_premise_in <> (List.map force_unwrap_tp_var premise_in) then
      failwith ("E3323: Premise input does not match expected input in clause " ^ concl_name);
    let cons_name = (match (List.nth (concl_in) idx) with 
      | TP.Ap(name, _) -> name
      | _ -> failwith ("E35: Expected a constructor term in conclusion " ^ concl_name)
    ) in
    (cons_name, premise_name)
  )
  | _ -> failwith ("E36: Expecting single premise for plusL clause, got " ^ TP.show_rel_clause clause)

let get_non_var_terms_with_idxs (terms : TP.term list) : (TP.term * int) list =
  ListUtil.filter_map_i (fun i term ->
    match term with
    | TP.Var _ -> None
    | _ -> Some (term, i)
  ) terms
(* returns the flattened term things expanded and contracted as appropriate, together with list of 
terms that are not Vars and their indexes
*)
let transpile_term_list_vars (tml : TP.term list) : string list * (TP.term * int) list = 
  List.concat_map (fun term ->
    match term with
    | TP.Ap (_name, TP.Var x) -> [x]
    | TP.TmUnit -> []
    | TP.Var x -> [x]
    | TP.TmPair(TP.Var x, TP.Var y) -> [x; y]
    | _ -> failwith ("E38: Unsupported term in transpile_term_list_vars " ^ TP.show_term term)

  ) tml, get_non_var_terms_with_idxs tml

let get_index_mapping (premise : string list) (params : string list) : int list = 
  List.map (fun x -> match List.find_index (fun y -> x = y) params with
  | Some i -> i
  | None -> failwith ("E39: Expected " ^ x ^ " in params, got " ^ String.concat ", " params)
  ) premise

let list_identical (l1 : string list) (l2 : string list) : bool = 
  List.for_all2 (fun x y -> x = y) l1 l2

(* transpile a premise to a form that can be used in the relational clause *)
(* returns a tuple of the form (input, name, output) where input and output are lists of strings *)

type transpiled_premise_tp = string list * string * string list

let transpile_premise (pre : TP.premise) : transpiled_premise_tp = 
  let (i, name, out) = pre in
  match transpile_term_list_vars i with
  | i', [] -> (
    match transpile_term_list_vars [out] with
    | [o'], [] -> (
      (* no non-var terms, just return the premise *)
      i', name, [o']
    )
    | _ -> failwith ("E401: Unsupported term in transpile_premise " ^ TP.show_premise pre)
  )
  | _ -> failwith ("E40: Unsupported term in transpile_premise " ^ TP.show_premise pre)

(* attempt to find a matching relational clause, return None if not found *)
let compile_single_rel_clause (rel_types : TP.rel_type_signature)(rel_clause : string * TP.rel_clause) : LP.relational_clause =
  if Flags.verbose () then print_endline ("Compiling " ^ TP.show_rel_clause_entry rel_clause);
        let rel_clause_print = TP.show_rel_clause_entry rel_clause in
        let ((_name, (premises, (concl_in, _, concl_out)))) = rel_clause in
        let transpiled_premises = List.map transpile_premise premises in
        let transpiled_concl_in, concl_in_nv_terms = transpile_term_list_vars concl_in in
        let transpiled_concl_out, concl_out_nv_terms = transpile_term_list_vars [concl_out] in
        let assert_premise_concl_agreement () = 
          (
            match transpiled_premises with
            | [premise_in, _, premises_out] -> (
              if not (list_identical premise_in transpiled_concl_in) then
                failwith ("E4033: Premise input does not match conclusion input in clause " ^ rel_clause_print);
              if not (list_identical premises_out transpiled_concl_out) then
                failwith ("E40: Premise output does not match conclusion output in clause " ^ rel_clause_print);
                ()
            )
            | _ -> failwith ("E41: Unsupported number of premises in clause " ^ rel_clause_print)
          ) in 
        match transpiled_premises, transpiled_concl_in, transpiled_concl_out, concl_in_nv_terms, concl_out_nv_terms with
        (* 1R *)
        | [], [], [], [], [TP.TmUnit, 0] -> (
          (LP.UnitR)
        )
        (* id *)
        | [], [ivar], [ovar], [], [] -> (
          if ivar = ovar then (LP.Id)
          else failwith ("E41: Id clause with different input and output variables " ^ rel_clause_print)
        )
        (* dup *)
        | [], [ivar], [ovar1; ovar2], [], [TP.TmPair(_, _), 0] -> (
          if ivar = ovar1 && ivar = ovar2 then (LP.Duplicate)
          else failwith ("E41: Duplicate clause with different input and output variables " ^ rel_clause_print)
        )
        (* dealloc *)
        | [], [_ivar], [], [], [TP.TmUnit, 0] -> (
          LP.Dealloc
        )
        (* 1L *)
        | [_, premise_name, _], _, _, [TP.TmUnit, idx], []  -> (
          assert_premise_concl_agreement ();
          LP.UnitL ({
              premise_name = premise_name;
              idx = idx;
          })
        )
        (* plusR *)
        | [_, premise_name, _], _, _, [], [TP.Ap(cons_name, _), _] -> (
          assert_premise_concl_agreement ();
          (LP.PlusR ({
            premise_name = premise_name;
            data_constructor_name = cons_name;
          }))
        )
        (* single plusL *)
        | [_, premise_name, _], _, _, [TP.Ap(cons_name, _), idx], [] -> (
          assert_premise_concl_agreement ();
          (* assert unique *)
          (LP.PlusL ({
            premise_names = [(cons_name, premise_name)];
            idx = idx;
          }))
        )
        (* tensorL *)
        | [_, premise_name, _], _, _, [TP.TmPair(_, _), idx], [] -> (
          assert_premise_concl_agreement ();
          (LP.TensorL ({
            premise_name = premise_name;
            idx = idx;
          }))
        )
        (* permutation *)
        | [premise_in, premise_name, premise_out], _, _, [], [] -> (
          if not (list_identical premise_out transpiled_concl_out) then
            failwith ("E42: Premise output does not match conclusion output in clause " ^ rel_clause_print);
          if not (ListUtil.equal_as_sets premise_in transpiled_concl_in) then
            failwith ("E42: Premise input does not match conclusion input in clause " ^ rel_clause_print);
          (* assert_premise_concl_agreement (); *)
          (LP.PermL ({
            premise_name = premise_name;
            indexes = get_index_mapping premise_in transpiled_concl_in
          }))
        )
        (* tensorR *)
        | [premise_L_in, premise_L_name, premise_L_out;
            premise_R_in, premise_R_name, premise_R_out
          ], _, _, [], [TP.TmPair(TP.Var(concl_l), TP.Var(concl_r)), _] -> (
            if not (list_identical premise_L_out [concl_l]) then
              failwith ("E43: Premise output does not match conclusion output in clause " ^ rel_clause_print);
            if not (list_identical premise_R_out [concl_r]) then
              failwith ("E44: Premise output does not match conclusion output in clause " ^ rel_clause_print);
            let left_index_mapping = get_index_mapping premise_L_in transpiled_concl_in in
            let right_index_mapping = get_index_mapping premise_R_in transpiled_concl_in in
            (* TODO check partition *)
            LP.TensorR ({
              left_premise = premise_L_name;
              right_premise = premise_R_name;
              split = PairSplit.from_two_lists left_index_mapping right_index_mapping;
            }) 
          )
        (* cut *)
        | [premise_L_in, premise_L_name, [premise_L_out];
            premise_R_in, premise_R_name, premise_R_out
          ], _, _, [], [] -> (
            if not (list_identical premise_R_out transpiled_concl_out) then
              failwith ("E45: Premise output does not match conclusion output in clause " ^ rel_clause_print);
            let new_chan_tp = (ListUtil.lookup_elem_by_key rel_types premise_L_name).output in
            (* the last element of premise_R_in is premise_L_out *)
            let idx = (match  ListUtil.find_index_i (fun i _ -> 
                premise_L_out = (List.nth premise_R_in i)
               ) premise_R_in with
            | None -> failwith ("E46: Premise output does not match right premise input in clause " ^ rel_clause_print)
            | Some i -> i) in
            (* check that the last element of premise_R_in is the same as premise_L_out *)
            if  premise_L_out <> (List.nth premise_R_in idx) then
              failwith ("E47: Premise output does not match conclusion output in clause " ^ rel_clause_print);
            let premise_R_in' = ListUtil.replace_idx premise_R_in idx [] in
            let left_indexes = get_index_mapping premise_L_in transpiled_concl_in in
            let right_indexes = get_index_mapping premise_R_in' transpiled_concl_in in
            let split = PairSplit.from_two_lists left_indexes right_indexes in 
            if  ((left_indexes, right_indexes) <> (PairSplit.get_left split, PairSplit.get_right split))
              then failwith ("TL223: Left and right indexes do not match split in clause " ^ rel_clause_print
            ^ " LEFT= " ^ String.concat ", " (List.map string_of_int left_indexes) ^ 
            " RIGHT= " ^ String.concat ", " (List.map string_of_int right_indexes) ^
            " SPLITLEFT = " ^ String.concat ", " (List.map string_of_int (PairSplit.get_left split)) ^
            " SPLITRIGHT = " ^ String.concat ", " (List.map string_of_int (PairSplit.get_right split))
          )
              ;
            (* TODO check partition *)
            LP.Cut ({
              new_chan_tp=new_chan_tp;
              left_premise = premise_L_name;
              right_premise = premise_R_name;
              split = split;
              idx=idx;
            })
          )
        | _ -> failwith ("E4823: Unsupported clause in " ^ rel_clause_print ^ " " ^ TP.show_rel_clause_entry (rel_clause))

(* let can_compile_single_rel_clause (rel_types : TP.rel_type_signature) (rel_clause : TP.rel_clause) : bool =
  (* print_endline ("Checking " ^ TP.show_rel_clause rel_clause); *)
  try
    compile_single_rel_clause rel_types ("PH", rel_clause) |> ignore;
    (* if we can compile it, then it is valid *)
    true
  with
  | _ -> false *)

let compile_rel_type (rel_types : TP.rel_type_signature) (rel_clauses : TP.rel_clause_signature) (rel_name : string) : LP.relational_clause list = 
  let all_candidates = List.filter (fun (_name, (_premises, (_, rel_name', _))) -> rel_name = rel_name') rel_clauses in
  match all_candidates with
  | [] -> failwith ("No relational clause found for " ^ rel_name)
  | _ -> (
    List.map (compile_single_rel_clause rel_types) all_candidates
  )
  (* | [single]  -> (
    compile_single_rel_clause rel_types single
  )
  (* multiple clauses, only plusL rule can apply*)
  | (_name, ((_premises, (concl_in, _, _concl_out)) as cls))  :: _-> (
    match find_unique_guarded_idx_in_list concl_in with
    | None -> failwith ("E323: No unique guarded index found in relational clause " ^ _name ^ " : " ^ TP.show_rel_clause cls)
    | Some idx -> (
        let supposed_premises = List.map (fun (_, rel_clause) -> 
          check_clause_is_plus_left_with_idx idx rel_clause
        ) all_candidates in
        LP.PlusL ({
          premise_names = supposed_premises;
          idx = idx;
        })
    )
  ) *)

(* the first pass may contain duplicates as deduplication is moved to a later stage*)
let tp_to_lp_top (tp_t : TP.t) : LP.colp_sig_duplicated = 
  let data_sig = tp_t.data_sig in
  let rel_types = tp_t.rel_sig in
  let rel_clauses = tp_t.rel_clause_sig in
  let final_rel_sig  = List.map (fun (name, rel_type) -> 
      (name, (rel_type, compile_rel_type rel_types rel_clauses name))
  ) rel_types in
  {
    data_sig = data_sig;
    relational_sig = final_rel_sig;
  }
