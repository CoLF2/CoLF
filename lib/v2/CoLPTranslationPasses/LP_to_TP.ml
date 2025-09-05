module LP = CoLPSignature.CoLPSignature
module TP = CoLPTranslationSignature


let lp_relational_clause_to_tp_rel_clause 
  (concl_rel_name : string) 
  (concl_rel_type_input_length : int)
  (lp_clause : LP.relational_clause) : TP.rel_clause = 
  let ci_length = concl_rel_type_input_length in
  let c_name = "Y" in
  let p_name i = "X" ^ string_of_int i in 
  let p_list n = 
    List.map (fun x -> TP.Var (p_name x)) (ListUtil.range 0 n) in
  let p_list_except n idx repl = 
    List.concat (List.mapi (fun i x -> if i = idx then repl else [TP.Var (p_name x)]) (ListUtil.range 0 n))  in
  match lp_clause with
  | LP.Id -> ([], ([TP.Var c_name], concl_rel_name, TP.Var c_name))
  | LP.UnitR -> ([], ([], concl_rel_name, TP.TmUnit))
  | LP.Duplicate -> ([], ([TP.Var c_name], concl_rel_name, TP.TmPair(TP.Var c_name, TP.Var c_name)))
  | LP.Dealloc -> ([], ([TP.Var c_name], concl_rel_name, TP.TmUnit))
  | LP.UnitL { premise_name; idx } -> (
    (
      [(p_list_except ci_length idx [], premise_name, TP.Var c_name)],
      (p_list_except ci_length idx [TP.TmUnit], concl_rel_name, TP.Var c_name)
    )
  )
  | LP.PlusL { premise_names;idx } -> (
    (
      match premise_names with
      | [(cons_name, premise_name)] -> (
        let p_in = p_list (ci_length) in
        let c_in = p_list_except ci_length idx [TP.Ap(cons_name, TP.Var (p_name idx))] in
        (
          [ (p_in, premise_name, TP.Var c_name) ],
          (c_in, concl_rel_name, TP.Var c_name)
        )
      )
      | _ -> failwith ("E42: Unsupported number of premises in clause " ^ concl_rel_name)
    )
  )
  | LP.PlusR {
    premise_name;
    data_constructor_name;
  } -> (
    (
      [(p_list (ci_length), premise_name, TP.Var c_name)],
      (p_list (ci_length), concl_rel_name, TP.Ap(data_constructor_name, TP.Var c_name))
    )
  )
  | LP.PermL {
    premise_name;
    indexes;
  } -> (
    (
      [(List.map (fun x -> TP.Var (p_name x)) indexes, premise_name, TP.Var c_name)],
      (p_list (ci_length), concl_rel_name, TP.Var c_name)
    )
  )
  | LP.TensorL {
    premise_name;
    idx;
  } -> (
    (
      let name1 = TP.Var ("Z1") in
      let name2 = TP.Var ("Z2") in
      ([p_list_except (ci_length) idx [name1; name2], premise_name, TP.Var c_name],
      (p_list_except ci_length idx [TP.TmPair(name1, name2)], concl_rel_name, TP.Var c_name))
    )
  )
  | LP.TensorR {
    left_premise;
    right_premise;
    split;
  } -> (
    (
      let name1 = TP.Var ("Z1") in
      let name2 = TP.Var ("Z2") in
      let c_in = p_list (ci_length) in
      ([PairSplit.select_left split c_in, left_premise, name1;
        PairSplit.select_right split c_in, right_premise, name2],
      (c_in, concl_rel_name, TP.TmPair(name1, name2)))
    )
  )
  | LP.Cut {
    new_chan_tp=_;
    left_premise;
    right_premise;
    split;
    idx;
  } -> (
    (
      let new_name = TP.Var ("Z") in
      let c_in = p_list (ci_length) in
      ([PairSplit.select_left split c_in, left_premise, new_name;
        ListUtil.insert_at_index (PairSplit.select_right split c_in) idx [new_name], right_premise, TP.Var c_name],
      (c_in, concl_rel_name, TP.Var c_name))
    )
  )


