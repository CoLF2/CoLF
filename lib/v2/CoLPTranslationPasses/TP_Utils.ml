(* 
module TP = CoLPTranslationSignature
module LP = CoLPSignature.CoLPSignature



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
    | TP.Ap (_name, TP.Var x, []) -> [x]
    | TP.TmUnit -> []
    | TP.Var x -> [x]
    | TP.Tensor(TP.Var x, TP.Var y) -> [x; y]
    | _ -> failwith ("E38: Unsupported term in transpile_term_list_vars " ^ TP.show_term term)

  ) tml, get_non_var_terms_with_idxs tml

let get_index_mapping (premise : string list) (params : string list) : int list = 
  List.map (fun x -> match List.find_index (fun y -> x = y) params with
  | Some i -> i
  | None -> failwith ("E39: Expected " ^ x ^ " in params, got " ^ String.concat ", " params)
  ) premise

(* transpile a premise to a form that can be used in the relational clause *)
(* returns a tuple of the form (input, name, output) where input and output are lists of strings *)

type transpiled_premise_tp = string list * string * string list

let transpile_premise (pre : TP.premise) : transpiled_premise_tp = 
  let (i, name, out) = pre in
  match transpile_term_list_vars i with
  | i', [] -> (
    match transpile_term_list_vars out with
    | [o'], [] -> (
      (* no non-var terms, just return the premise *)
      i', name, [o']
    )
    | _ -> failwith ("E401: Unsupported term in transpile_premise " ^ TP.show_premise pre)
  )
  | _ -> failwith ("E40: Unsupported term in transpile_premise " ^ TP.show_premise pre)


(* attempt to find a matching relational clause, return None if not found *)
let is_tp_rel_clause_compilable_to_lp (rel_clause : TP.rel_clause) (lp_clause : LP.relational_clause_template) = 
      let (premises, (concl_in, _, concl_out)) = rel_clause in
      (* let transpiled_premises = List.map transpile_premise premises in
      let transpiled_concl_in, concl_in_nv_terms = transpile_term_list_vars concl_in in
      let transpiled_concl_out, concl_out_nv_terms = transpile_term_list_vars concl_out in *)
      let check_single_premise_concl_agreement (supposed_premise_name : string) = 
        (
          match premises with
          | [premise_in, premise_name, premises_out] -> (

            if not (ListUtil.list_identical premise_in transpiled_concl_in) then
              failwith ("E4033: Premise input does not match conclusion input in clause " ^ TP.show_rel_clause rel_clause);
            if not (ListUtil.list_identical premises_out transpiled_concl_out) then
              failwith ("E40: Premise output does not match conclusion output in clause " ^ TP.show_rel_clause rel_clause);
              ()
          )
          | _ -> failwith ("E41: Unsupported number of premises in clause " ^ TP.show_rel_clause rel_clause)
        ) in 
      (* 1R *)
    match lp_clause with
    | LP.UnitR -> (
      match premises, concl_in, concl_out with
      | [], [], [TP.TmUnit] -> true
      | _ -> false
    )
    | LP.Id -> (
      match premises, concl_in, concl_out with
      | [], [TP.Var ivar], [TP.Var ovar] -> ivar = ovar
      | _ -> false
    )
    | LP.UnitL {
        premise_name;
        idx;
      } -> (
        List.nth_opt concl_in idx = Some TP.TmUnit &&
      match transpiled_premises, concl_in, concl_out with
      | [_, premise_name, _], [], [TP.TmUnit] -> (
        assert_premise_concl_agreement ();
        premise_name = premise_name
      )
      | _ -> false
    )
    }

      (* id *)
      | [], [ivar], [ovar], [], [] -> (
        if ivar = ovar then (LP.Id)
        else failwith ("E41: Id clause with different input and output variables " ^ rel_name)
      )
      (* match transpiled_premises, transpiled_concl_in, transpiled_concl_out, concl_in_nv_terms, concl_out_nv_terms with *)
      (* 1L *)
      | [_, premise_name, _], _, _, [TP.TmUnit, idx], []  -> (
        assert_premise_concl_agreement ();
        LP.UnitL ({
            premise_name = premise_name;
            idx = idx;
        })
      )
      (* plusR *)
      | [_, premise_name, _], _, _, [], [TP.Ap(cons_name, _, []), _] -> (
        assert_premise_concl_agreement ();
        (LP.PlusR ({
          premise_name = premise_name;
          data_constructor_name = cons_name;
        }))
      )
      (* tensorL *)
      | [_, premise_name, _], _, _, [TP.Tensor(_, _), idx], [] -> (
        assert_premise_concl_agreement ();
        (LP.TensorL ({
          premise_name = premise_name;
          idx = idx;
        }))
      )
      (* permutation *)
      | [premise_in, premise_name, premise_out], _, _, [], [] -> (
        if not (list_identical premise_out transpiled_concl_out) then
          failwith ("E42: Premise output does not match conclusion output in clause " ^ rel_name);
        assert_premise_concl_agreement ();
        (LP.PermL ({
          premise_name = premise_name;
          indexes = get_index_mapping premise_in transpiled_concl_in
        }))
      )
      (* tensorR *)
      | [premise_L_in, premise_L_name, premise_L_out;
          premise_R_in, premise_R_name, premise_R_out
        ], _, _, [], [TP.Tensor(TP.Var(concl_l), TP.Var(concl_r)), _] -> (
          if not (list_identical premise_L_out [concl_l]) then
            failwith ("E43: Premise output does not match conclusion output in clause " ^ rel_name);
          if not (list_identical premise_R_out [concl_r]) then
            failwith ("E44: Premise output does not match conclusion output in clause " ^ rel_name);
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
            failwith ("E45: Premise output does not match conclusion output in clause " ^ rel_name);
          let new_chan_tp = (match snd (ListUtil.lookup_elem_by_key rel_types premise_L_name) with
          | [tp] -> tp
          | _ -> failwith ("E46: Expected a single channel type for " ^ premise_L_name)
          ) in
          (* the last element of premise_R_in is premise_L_out *)
          if  premise_L_out <> (List.nth premise_R_in (List.length premise_R_in - 1)) then
            failwith ("E47: Premise output does not match conclusion output in clause " ^ rel_name);
          let premise_R_in' = ListUtil.take (List.length premise_R_in - 1) premise_R_in in
          let left_indexes = get_index_mapping premise_L_in transpiled_concl_in in
          let right_indexes = get_index_mapping premise_R_in' transpiled_concl_in in
          LP.Cut ({
            new_chan_tp=new_chan_tp;
            left_premise = premise_L_name;
            right_premise = premise_R_name;
            split = PairSplit.from_two_lists left_indexes right_indexes;
          })
        )
      | _ -> failwith ("E4823: Unsupported clause in " ^ rel_name ^ " " ^ TP.show_rel_clause_entry (List.hd all_candidates)) *)