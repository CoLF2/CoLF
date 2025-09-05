
module TP = CoLPTranslationSignature
module LP = CoLPSignature.CoLPSignature

let transform_rel_tp (tp : TP.rel_type) (input_transform : LP.tp list -> LP.tp list) (output_transform : LP.tp -> LP.tp) : TP.rel_type = 
  {inputs = input_transform tp.inputs; output = output_transform tp.output}

let rel_type_by_decomposing_concl_ith_input_or_output (tp: TP.t) (concl_rel_name : string) 
  (ith : int option) (* None if concl*)
   (cons_name : string option (* only needed for PlusL or PlusR *)) : TP.rel_type = 
  let data_sig = tp.data_sig in
  let rel_sig = tp.rel_sig in
  let tp_clause_type = ListUtil.lookup_elem_by_key rel_sig concl_rel_name in
  (* if List.length (snd tp_clause_type) <> 1 then failwith ("E4021: Expected a single channel type for " ^ concl_rel_name); *)
  (* check if ith is in the signature *)
  match ith with 
  | None ->  (
    (* conclusion *)
    transform_rel_tp tp_clause_type (fun i -> i)
    (function
      | LP.TpVar data_tp_name -> 
          ListUtil.lookup_elem_by_key (ListUtil.lookup_elem_by_key data_sig data_tp_name) (Option.get cons_name) 
      | LP.TpArrow (_, _) ->
          failwith "E4022: Higher-order function types not supported in conclusion decomposition"
      | y -> failwith ("E4022: Not implemented yet" ^ (LP.show_tp y))
    )
   )
  | Some idx ->(
    (* ith premise *)
    transform_rel_tp tp_clause_type
    (fun inputs -> 
        match (List.nth inputs idx) with 
        LP.TpVar ith_data_tp -> 
          let new_data_tp = ListUtil.lookup_elem_by_key (ListUtil.lookup_elem_by_key data_sig ith_data_tp) (Option.get cons_name) in
          ListUtil.replace_idx (tp_clause_type.inputs) idx [new_data_tp]
        | LP.TpUnit -> 
          ListUtil.replace_idx (tp_clause_type.inputs) idx []
        | LP.TpTensor (lt, rt) -> 
          ListUtil.replace_idx (tp_clause_type.inputs) idx [lt; rt]
        | LP.TpArrow (_, _) ->
          failwith "TpArrow cannot be decomposed in PlusL clause"
    ) (fun o -> o)
  )

let new_var_name (tp : TP.t) (clause_idx : int) (prefix : string) =
  let first_clause = List.nth tp.rel_clause_sig clause_idx in
  let (_clause_name, (premises, (concl_in, _concl_rel_name, concl_out))) = first_clause in
  Naming.new_var_name prefix (List.concat_map TP.free_vars_in_term concl_in @ List.concat_map TP.free_vars_in_premise premises @ TP.free_vars_in_term concl_out)

let new_rel_name_with_prefix (tp : TP.t) (concl_rel_name : string) (new_name_prefix : string) = 
  let new_rel_name = (concl_rel_name ^ "_" ^ new_name_prefix) in
  let exclude = List.map fst tp.rel_sig in
  Naming.new_var_name new_rel_name exclude

let do_plus_l_transform (tp: TP.t) (cons_name : string) (concl_rel_name: string) 
(concl_rel_input_length : int)
(idx : int) : TP.t = 
  let data_sig = tp.data_sig in
  let rel_sig = tp.rel_sig in
  let rel_clause_sig = tp.rel_clause_sig in
  let new_rel_name = new_rel_name_with_prefix tp concl_rel_name ("L" ^ string_of_int idx ^ cons_name) in
  let lp_clase = LP.PlusL {
    premise_names = [(cons_name, new_rel_name)];
    idx = idx;
  } in
  let last_clause_idx = ref 0 in
  let new_clauses = List.mapi (fun i (orig : string * TP.rel_clause) -> 
    let (rel_clause_name, (premises, (concl_in, concl_name, concl_out))) = orig in
    (* check if the ith in agrees with concl_rel_name *)
    match (List.nth_opt concl_in idx) with
    | Some (TP.Ap(cons_name', arg)) -> (
      (* now we can transform the clause *)
      if (cons_name' <> cons_name || concl_rel_name <> concl_name) then orig
        else (
          last_clause_idx := i;
          (* we will insert lp_clause (actually the tp_clause corresponding to the lp_clause for that case, we 
          just need to change the concl_name to the clause with analysis *)
          (rel_clause_name, 
            (
              premises,
              (ListUtil.replace_idx concl_in idx [arg],
              new_rel_name,
              concl_out)
            )
          )
        )
    )
    | _ -> orig
  ) rel_clause_sig in
  let tp_clause = LP_to_TP.lp_relational_clause_to_tp_rel_clause concl_rel_name (concl_rel_input_length) lp_clase in
  (* now figure out the typing of this new thing *)
  let new_tp_clause_type = rel_type_by_decomposing_concl_ith_input_or_output tp concl_rel_name (Some idx) (Some cons_name) in
  (* now we need to add the new clause to the signature *)
  { data_sig; 
  rel_sig=
    ListUtil.insert_after_index rel_sig 
      (ListUtil.lookup_index_of_elem_by_key rel_sig concl_rel_name)
      (new_rel_name, new_tp_clause_type); 
  rel_clause_sig = 
    ListUtil.insert_after_index new_clauses (!last_clause_idx) (new_rel_name ^ "_intro", tp_clause) }



let transform_tp_clause_and_add_lp_clause 
  (tp : TP.t) 
  (rel_clause_index: int) 
  (new_name_prefix: string)
  (idx_for_rel_type_gen : int option) (* None if concl*)
  (c_name_for_rel_type_gen : string option) (* only needed for PlusL or PlusR *)
  (lp_clause_cons : string (* new premise name *) -> LP.relational_clause)
  (concl_in_transform : TP.term list -> TP.term list)
  (concl_out_transform : TP.term -> TP.term )
   : TP.t = 
  let data_sig = tp.data_sig in
  let rel_sig = tp.rel_sig in
  let rel_clause_sig = tp.rel_clause_sig in
  let (clause_name, (premises, ( concl_in, concl_rel_name, concl_out))) = List.nth rel_clause_sig rel_clause_index in
  let new_rel_name = new_rel_name_with_prefix tp concl_rel_name new_name_prefix in
  let new_tp_clause_type = rel_type_by_decomposing_concl_ith_input_or_output tp concl_rel_name idx_for_rel_type_gen c_name_for_rel_type_gen in
  { data_sig; rel_sig=ListUtil.insert_after_index rel_sig
  (ListUtil.lookup_index_of_elem_by_key rel_sig concl_rel_name)
    (new_rel_name, new_tp_clause_type);
  rel_clause_sig = (
    ListUtil.replace_idx rel_clause_sig rel_clause_index 
      [(clause_name, (premises, (concl_in_transform concl_in, new_rel_name, concl_out_transform concl_out))) ;
    new_rel_name ^ "_intro", LP_to_TP.lp_relational_clause_to_tp_rel_clause concl_rel_name (List.length (concl_in)) (lp_clause_cons new_rel_name)] )}

let tp_to_tp_proc (tp : TP.t) (cond : TP.rel_clause -> bool) (trans : int * string * TP.rel_clause -> TP.t) : TP.t option = 
  let rel_clause_sig = tp.rel_clause_sig in
  let (clause_to_transform) = ListUtil.find_opt_i (
    fun (_, rel_clause) -> 
      cond rel_clause
  ) rel_clause_sig in
  match clause_to_transform with
  | None -> None
  | Some (clause_idx, (clause_name, first_clause)) -> (
    (* print_endline ("Transforming " ^ TP.show_rel_clause_entry (clause_name, first_clause)); *)
    (* check if the transformation is the same *)
    let result = (trans (clause_idx, clause_name, first_clause)) in
    (* if result = tp then failwith ("E120: tp_to_tp_proc returns an identical clause on ") else  *)
      Some result
  )

let do_decompose_concl_in_patterns (tp : TP.t) 
  (clause_idx : int) : TP.t = 
  let first_clause = List.nth tp.rel_clause_sig clause_idx in
  let (_clause_name, (_premises, (concl_in, _concl_rel_name, _concl_out))) = first_clause in
  let concl_in_patterns = TP_to_LP.get_non_var_terms_with_idxs concl_in in
  match concl_in_patterns with
  | (TP.TmUnit, idx) :: _ -> (
    transform_tp_clause_and_add_lp_clause tp clause_idx ("L" ^ string_of_int idx ^ "Unit") (Some idx) None 
      (fun new_rel_name ->
          LP.UnitL {
            premise_name = new_rel_name;
            idx = idx;
          }
        )
      (fun concl_in -> ListUtil.replace_idx concl_in idx [])
      (fun concl_out -> concl_out)
  )
  | ((TP.TmPair(l, r), idx) :: _ ) -> (
    transform_tp_clause_and_add_lp_clause tp clause_idx ("L" ^ string_of_int idx ^ "Pair") (Some idx) None 
      (fun new_rel_name ->
          LP.TensorL {
            premise_name = new_rel_name;
            idx = idx;
          }
        )
      (fun concl_in -> ListUtil.replace_idx concl_in idx [l; r])
      (fun concl_out -> concl_out)
  )
  | ((TP.Ap(cons_name, arg), idx) :: _ ) -> (
    transform_tp_clause_and_add_lp_clause tp clause_idx ("L"^ string_of_int idx ^ cons_name) (Some idx) (Some cons_name)
      (fun new_rel_name ->
          LP.PlusL {
            premise_names = [(cons_name, new_rel_name)];
            idx = idx;
          }
        )
      (fun concl_in -> ListUtil.replace_idx concl_in idx [arg])
      (fun concl_out -> concl_out)
  )
  | _::_ -> failwith ("E45823: Not implemented yet " ^ TP.show_rel_clause_entry first_clause)
  | [] -> failwith ("E171: Cannot decompose concl_in " ^ TP.show_rel_clause_entry first_clause)


let do_decompose_premise_in_patterns (tp : TP.t) 
  (clause_idx : int) : TP.t = 
  (*
  ... (c Y) ... >= p >= M, ... -> IN >= q >= OUT
  vvv
  Y >= r >= (c Y)
  ... >= r >= X, ... X ... >= p >= M, IN >= q >= OUT
  *)
  let first_clause = List.nth tp.rel_clause_sig clause_idx in
  let (clause_name, (premises, (concl_in, concl_rel_name, concl_out))) = first_clause in
  match premises with
  | [] -> failwith ("E171: Cannot decompose premise_in " ^ TP.show_rel_clause_entry first_clause)
  | (premise_in, premise_rel_name, premise_out)::rest_premise -> (
    (* concl needs to be all tpvars *)
    if not (List.for_all TP.is_tm_var concl_in) then failwith ("E170: Cannot decompose cut_rules , some concl_in have guarded inputs: " ^ TP.show_rel_clause_entry first_clause);
    let premise_in_patterns = TP_to_LP.get_non_var_terms_with_idxs premise_in in
    match premise_in_patterns with
    | (tm, idx) :: _ -> (
      (**)
      let concl_in_tps = List.map2 (fun concl_in_tm concl_in_tp -> 
        TP.get_tm_var concl_in_tm, concl_in_tp
        ) concl_in (ListUtil.lookup_elem_by_key tp.rel_sig concl_rel_name).inputs in
      let tm_free_vars = TP.free_vars_in_term tm in
      let tm_free_var_tps = List.map (fun v -> ListUtil.lookup_elem_by_key concl_in_tps v) tm_free_vars in
      let new_premise_concl_tp = List.nth (ListUtil.lookup_elem_by_key tp.rel_sig premise_rel_name).inputs idx in
      let new_premise_name = new_rel_name_with_prefix tp concl_rel_name ("P"^string_of_int idx) in
      let var_name = new_var_name tp clause_idx "X"  in
      {
        data_sig = tp.data_sig;
        rel_sig = ListUtil.insert_after_index tp.rel_sig (ListUtil.lookup_index_of_elem_by_key tp.rel_sig concl_rel_name)
          (new_premise_name, {inputs=tm_free_var_tps; output=new_premise_concl_tp});
        rel_clause_sig =
        ListUtil.replace_idx tp.rel_clause_sig clause_idx (
          [
            (clause_name, 
              (
                (List.map (fun x -> TP.Var x) tm_free_vars, new_premise_name, TP.Var var_name) ::
                (ListUtil.replace_idx premise_in idx [TP.Var var_name], premise_rel_name, premise_out) :: rest_premise,
                (concl_in, concl_rel_name, concl_out)
              )
            );
            (new_premise_name ^ "_intro", 
              ([], 
                (List.map (fun x -> TP.Var x) tm_free_vars, new_premise_name, tm)
              )
            )
          ]
        )
      }
    )
    | [] -> failwith ("E171: Cannot decompose concl_in " ^ TP.show_rel_clause_entry first_clause)
  )

let do_cut_rules (tp : TP.t) (clause_idx : int) : TP.t = 
  (*
        X >= p >= PAT;  rest -> IN >= q >= OUT
        vvv
        rest -> IN - X, PAT >= r >= OUT
        X >= p >= Y; IN - X, Y >= r >= Z -> IN >= q >= Z
  *)
  let first_clause = List.nth tp.rel_clause_sig clause_idx in
  let (clause_name, (premises, (concl_in, concl_rel_name, concl_out))) = first_clause in
  match premises with
    | (premise_in, premise_name, premise_out) :: rest_premises -> (
      if not (List.for_all TP.is_tm_var premise_in) then failwith ("E170: Cannot decompose cut_rules , some premises have guarded inputs: " ^ TP.show_rel_clause_entry first_clause);
      (* reoder premise_in to *)
      if ListUtil.contains_duplicate premise_in then failwith ("E171: Cannot decompose cut_rules , some premises have duplicate inputs: " ^ TP.show_rel_clause_entry first_clause);
      let {inputs=premise_in_types; output=premise_out_type} : TP.rel_type = ListUtil.lookup_elem_by_key tp.rel_sig premise_name in
      let {inputs=concl_in_types; output=concl_out_type}: TP.rel_type = ListUtil.lookup_elem_by_key tp.rel_sig concl_rel_name in
      (* assign a priority to each element in premise in*)
      let premise_in_sorting_idx = List.mapi (fun i x -> (x, i)) concl_in in
      let (sorted_premise_in, sorted_premise_in_types) = List.split (
        List.sort (fun (x, _) (y, _) ->
          let x_idx = ListUtil.lookup_elem_by_key_generic premise_in_sorting_idx x in
          let y_idx = ListUtil.lookup_elem_by_key_generic premise_in_sorting_idx y in
          compare x_idx y_idx
        )
        (ListUtil.zip premise_in premise_in_types)
      ) in
      let new_rel_name_right = new_rel_name_with_prefix tp concl_rel_name "cutR" in
      let new_rel_name_left = new_rel_name_with_prefix tp concl_rel_name "cutL" in
      let premise_out_var = new_var_name tp clause_idx "Y" in
      let concl_out_var = new_var_name tp clause_idx "U" in
      let new_rel_inputs = 
        (* remove premise_in from rel_inputs and (to add premise_outputs) *)
        ListUtil.minus (ListUtil.zip concl_in concl_in_types) (ListUtil.zip sorted_premise_in sorted_premise_in_types)
        (* @ [premise_out, premise_out_type] *)
      in 
      let updated_clause = 
        ((sorted_premise_in, new_rel_name_left, TP.Var premise_out_var) ::
        (List.map fst new_rel_inputs @ [TP.Var premise_out_var], new_rel_name_right, TP.Var concl_out_var) ::[],
        (concl_in, concl_rel_name, TP.Var concl_out_var)) in
      let new_rel_clause_left = 
        [premise_in, premise_name, TP.Var premise_out_var],
        (sorted_premise_in, new_rel_name_left, TP.Var premise_out_var) in
      let new_rel_clause_right = 
        (rest_premises, (List.map fst new_rel_inputs @ [premise_out], new_rel_name_right, concl_out)) in
      {
        data_sig = tp.data_sig;
        rel_sig = ListUtil.insert_at_index tp.rel_sig 
          (ListUtil.lookup_index_of_elem_by_key tp.rel_sig concl_rel_name + 1)
          [
            new_rel_name_left, {inputs=sorted_premise_in_types; output=premise_out_type};
            new_rel_name_right, {inputs=List.map snd new_rel_inputs @ [premise_out_type]; output=concl_out_type};
          ];
        rel_clause_sig = 
          ListUtil.replace_idx tp.rel_clause_sig clause_idx [
            clause_name, updated_clause;
            new_rel_name_left ^ "_intro", new_rel_clause_left;
            new_rel_name_right ^ "_intro", new_rel_clause_right
            ]
      }
      )
    | []  -> failwith ("E172: Cannot decompose cut_rules concl_in " ^ TP.show_rel_clause_entry first_clause)

(* we want lazy, only find duplicates in the first premise *)
(* also the intersect is left-biased, if a variable occurs in the second arg twice, it won't appear,
  it is filtering fir*)
(* finds 
(1) duplicate inputs in the first premise
(2) first premise shares inputs with some rest premise
(3) first premise shares inputs with concl_out

so we need to find all inputs then filter out those that are not used in the first premise
*)
let possibly_duplicate_inputs_used_by_the_first_premise (premises : TP.premise list) 
  (concl_in : TP.term list) (concl_out : TP.term) : string list = 
  ListUtil.intersect 
  (
    ListUtil.intersect 
      ((List.concat_map (fun (x, _, _) -> List.concat_map TP.free_vars_in_term x) premises) @ (TP.free_vars_in_term concl_out))
      (List.concat_map TP.free_vars_in_term concl_in)
  )
  (
    match premises with
    | [] -> []
    | (premise_in, _, _) :: _ -> (
      ListUtil.intersect
      (
        List.concat_map TP.free_vars_in_term premise_in
      )
      (
        List.concat_map TP.free_vars_in_term concl_in
      )
    )
  )
(* TODO: also need dup insertion for (X, X) >= ((X, X), (X, X)) ??? *)
let can_do_dup_insertion_for_premise (tp : TP.t) (clause_idx : int) : bool = 
  let first_clause = List.nth tp.rel_clause_sig clause_idx in
  let (_clause_name, (premises, (concl_in, _concl_rel_name, concl_out))) = first_clause in
  ListUtil.contains_duplicate (
    possibly_duplicate_inputs_used_by_the_first_premise premises concl_in concl_out
  )


let do_dup_insertion_for_premise (tp : TP.t) (clause_idx : int) : TP.t = 
  (*
  Y >= p >= M, ..., Y >= r >= T -> IN >= q >= OUT
  vvv
  Y >= dup >= (W, H), W >= p >= M, ..., H >= r >= T -> IN >= q >= OUT
  *)
  let first_clause = List.nth tp.rel_clause_sig clause_idx in
  let (clause_name, (premises, (concl_in, concl_rel_name, concl_out))) = first_clause in
  let duplicates = ListUtil.find_duplicates (
    possibly_duplicate_inputs_used_by_the_first_premise premises concl_in concl_out
  ) in
  match duplicates with
  | [] -> failwith ("E172: Cannot do dup insertion on concl_in " ^ TP.show_rel_clause_entry first_clause)
  | hd_var :: _ -> (
        let hd_var1 = new_var_name tp clause_idx (hd_var ^ "L") in
        let hd_var2 = new_var_name tp clause_idx (hd_var ^ "R") in
        let new_rel_name = new_rel_name_with_prefix tp concl_rel_name (hd_var ^ "dup") in
        let hd_var_tp = List.nth (
          (ListUtil.lookup_elem_by_key tp.rel_sig concl_rel_name).inputs
        ) (ListUtil.lookup_index_of (TP.Var hd_var) concl_in ) in
        let (subst_premises, subst_concl_out) = (
          let (subst_premises, idx) = TP.subst_occurrence_in_premises (TP.Var hd_var1) hd_var 0 premises in
          if idx < 0 (* this indicates successful substitution *)
            then (List.map (TP.subst_tm_in_premise (TP.Var hd_var2) hd_var) subst_premises, TP.subst_tm (TP.Var hd_var2) hd_var concl_out)
            else (* duplicates are in the concl_out*)
            (subst_premises, 
            TP.subst_tm (TP.Var hd_var2) hd_var (fst (TP.subst_occurrence (TP.Var hd_var1) hd_var 0 concl_out))
            )
        ) in
        {
          data_sig = tp.data_sig;
          rel_sig = (
            ListUtil.insert_after_index tp.rel_sig 
              (ListUtil.lookup_index_of_elem_by_key tp.rel_sig concl_rel_name)
              (new_rel_name, { inputs=[hd_var_tp]; output=LP.TpTensor(hd_var_tp, hd_var_tp); }); 
          );
          rel_clause_sig = 
            ListUtil.replace_idx tp.rel_clause_sig clause_idx [
              clause_name, (
                ([TP.Var hd_var], new_rel_name, TP.TmPair (TP.Var hd_var1, TP.Var hd_var2)) ::
                (
                  subst_premises
                ),
                (concl_in, concl_rel_name, subst_concl_out) 
              );
              new_rel_name ^ "_intro", ([], 
                ([TP.Var hd_var] , new_rel_name, TP.TmPair (TP.Var hd_var, TP.Var hd_var))
              );
            ]
        }
    )

let do_dealloc_insertion (tp : TP.t) (clause_idx : int) : TP.t = 
  (*
  [] -> IN >= q >= OUT
  vvv
  Y >= dealloc >= () -> IN - Y >= q >= OUT
  *)
  let first_clause = List.nth tp.rel_clause_sig clause_idx in
  let (clause_name, (premises, (concl_in, concl_rel_name, concl_out))) = first_clause in
  match premises with
  | _ :: _ -> failwith "TP349: Dealloc requires empty premises"
    | [] -> (
      match ListUtil.minus (List.concat_map TP.free_vars_in_term concl_in) (TP.free_vars_in_term concl_out) with
      | [] -> failwith ("E172: Cannot do dealloc insertion on concl_in " ^ TP.show_rel_clause_entry first_clause)
      | hd_var :: _ -> (
        (* check if the concl_in is a single term *)
        let new_rel_name = new_rel_name_with_prefix tp concl_rel_name (hd_var ^ "dealloc") in
        let hd_var_tp = List.nth (
          (ListUtil.lookup_elem_by_key tp.rel_sig concl_rel_name).inputs
        ) (ListUtil.lookup_index_of (TP.Var hd_var) concl_in ) in
        {
          data_sig = tp.data_sig;
          rel_sig = (
            ListUtil.insert_after_index tp.rel_sig 
              (ListUtil.lookup_index_of_elem_by_key tp.rel_sig concl_rel_name)
              (new_rel_name, { inputs=[hd_var_tp]; output=LP.TpUnit; }); 
          );
          rel_clause_sig = 
            ListUtil.replace_idx tp.rel_clause_sig clause_idx [
              clause_name, (
                ([TP.Var hd_var], new_rel_name, TP.TmUnit) :: [],
                (concl_in, concl_rel_name, concl_out) 
              );
              new_rel_name ^ "_intro", ([], 
                ([TP.Var hd_var] , new_rel_name, TP.TmUnit)
              );
            ]
        }
    )
  )
let do_concl_out_rules (tp : TP.t) (clause_idx : int) : TP.t = 
  let first_clause = List.nth tp.rel_clause_sig clause_idx in
  let (clause_name, (premises, (concl_in, concl_rel_name, concl_out))) = first_clause in
  if premises <> [] then failwith ("E173: Cannot decompose concl_out rules concl_in " ^ TP.show_rel_clause_entry first_clause);
  match concl_out with
  | TP.Ap(cons_name, arg) -> (
    transform_tp_clause_and_add_lp_clause tp clause_idx ("R"^cons_name) None (Some cons_name)
      (fun new_rel_name ->
          LP.PlusR {
            premise_name = new_rel_name;
            data_constructor_name = cons_name;
          }
        )
      (fun concl_in -> concl_in)
      (fun _concl_out -> arg)
  )
  | TP.TmPair (l, r) -> ( 
     let {inputs=concl_in_tps; output=concl_out_tp} : TP.rel_type = ListUtil.lookup_elem_by_key tp.rel_sig concl_rel_name in
    match concl_out_tp with
    | LP.TpTensor(lt, rt) -> (
      let ins = ListUtil.zip concl_in concl_in_tps in
      let split = PairSplit.from_list_f ins (fun (tpvar, _) -> 
        match tpvar with
        | TP.Var(x) -> (
            match List.mem x (TP.free_vars_in_term l), List.mem x (TP.free_vars_in_term r) with
            | true, false -> PairSplit.Left
            | false, true -> PairSplit.Right
            | true, true -> failwith ("E212: duplicating Vars " ^ x ^ " in " ^ TP.show_rel_clause_entry first_clause)
            | false, false -> failwith ("E213: ommitted Vars " ^ x ^ " in " ^ TP.show_rel_clause_entry first_clause)
        )
        | _ -> failwith ("E209: Expecting Vars")
      ) in
      let left_new_premise_name = new_rel_name_with_prefix tp concl_rel_name "Rleft" in
      let right_new_premise_name = new_rel_name_with_prefix tp concl_rel_name "Rright" in
      let left_tp : TP.rel_type = {
        inputs=List.map snd (PairSplit.select_left split ins);
        output=lt;
      } in 
      let right_tp : TP.rel_type = {
        inputs=List.map snd (PairSplit.select_right split ins);
        output=rt;
      } in
      let l_var_name = new_var_name tp clause_idx "L" in
      let r_var_name = new_var_name tp clause_idx "R" in
      let concl_rel_idx = (ListUtil.lookup_index_of_elem_by_key tp.rel_sig concl_rel_name) in
      {data_sig = tp.data_sig;
      rel_sig = ListUtil.replace_idx tp.rel_sig concl_rel_idx [
        List.nth tp.rel_sig concl_rel_idx;
        left_new_premise_name, left_tp;
        right_new_premise_name, right_tp;
      ];
      rel_clause_sig = 
        ListUtil.replace_idx tp.rel_clause_sig clause_idx [
          clause_name, ([
            (PairSplit.select_left split concl_in, left_new_premise_name, TP.Var l_var_name);
            (PairSplit.select_right split concl_in, right_new_premise_name, TP.Var r_var_name)
          ]
            , (concl_in, concl_rel_name, TP.TmPair (TP.Var l_var_name, TP.Var r_var_name))
          );
          left_new_premise_name ^ "_intro", ([], 
            (PairSplit.select_left split concl_in, left_new_premise_name, l)
          );
          right_new_premise_name ^ "_intro", ([],
            (PairSplit.select_right split concl_in, right_new_premise_name, r)
          )
        ]
      }
    )
    | _ -> failwith ("E205: Expectign Tensor types got " ^ TP.show_rel_clause_entry first_clause ^ " " ^ LP.show_tp concl_out_tp)
  )
  | TP.TmUnit -> failwith ("E424: Not implemented yet " ^ TP.show_rel_clause_entry first_clause)
  | TP.Var _  -> (
      failwith ("E204: Not implemented yet " ^ TP.show_rel_clause_entry first_clause)
  )

(* check if the clause have the following nine forms*)
let can_compile_single_rel_clause(rel_clause : TP.rel_clause) : bool = 
  let (premises, (concl_in, _, concl_out)) = rel_clause in
  let concl_in_patterns = TP_to_LP.get_non_var_terms_with_idxs concl_in in
  let concl_out_patterns = TP_to_LP.get_non_var_terms_with_idxs [concl_out] in
  (* check if the concl_in is a single term *)
  match premises with
  | [] -> (
    (* zero premises are id for vars or 1R or dup or dealloc *)
    (concl_in = [concl_out] && TP.is_tm_var concl_out) (* id *)
    || (concl_in = [] && concl_out = TmUnit) (* 1R *)
    || (
      match concl_in with
      | [single] -> TP.is_tm_var single
        && (
          concl_out = TP.TmPair(single, single) (* dup *) 
          || concl_out = TP.TmUnit (* dealloc*)
        )
      | _ -> false
    ) 
  )
  | [single_premise_in, _, single_premise_out] -> (
    (* single premise are always case analysis rules *)
    match concl_in_patterns, concl_out_patterns with
    (* no conclusion patterns means PermutationL rule, check input permutations and output agreement*)
    | [] , [] -> (
      single_premise_out = concl_out
      && ( ListUtil.equal_as_sets concl_in single_premise_in)
      (* premise1_in should not contain duplicating vars*)
      && List.for_all TP.is_tm_var single_premise_in
      && not (ListUtil.contains_duplicate (List.filter TP.is_tm_var single_premise_in))
    )
    (* single patterns, variables must be identical *)
    | [], [pat, _] | [pat, _], [] -> (
      List.concat_map TP.free_vars_in_term concl_in = List.concat_map TP.free_vars_in_term single_premise_in
      && TP.free_vars_in_term concl_out = TP.free_vars_in_term single_premise_out
      &&
      (* pattern must be shallow*)
      (TP.is_tm_shallow pat)
      (* premises must be vars only *)
      && List.for_all TP.is_tm_var single_premise_in
      && TP.is_tm_var single_premise_out

    )
    | _ -> false
  )
  | [premise1_in, _, premise1_out;
      premise2_in, _, premise2_out] -> (
        (* either tensor r or cut*)
        match concl_in_patterns, concl_out_patterns with
        | [], [] -> (
          (* check is cut *)
          match TP_to_LP.get_non_var_terms_with_idxs premise1_in 
          @ TP_to_LP.get_non_var_terms_with_idxs premise2_in 
          @TP_to_LP.get_non_var_terms_with_idxs [premise1_out]
          @ TP_to_LP.get_non_var_terms_with_idxs [premise2_out] with
          | [] -> (
            List.mem premise1_out premise2_in &&
            ListUtil.equal_as_sets concl_in (ListUtil.minus (premise1_in @ premise2_in) [premise1_out])
            && premise2_out = concl_out
            (* premise1_in should not contain duplicating vars*)
            && not (ListUtil.contains_duplicate (List.filter TP.is_tm_var premise1_in))
            (* premise2_in should not contain duplicating vars*)
            && not (ListUtil.contains_duplicate (List.filter TP.is_tm_var premise2_in))
            (* check if the concl_in is a single term *)
            && (* ordering of premise terms agree with those in the conclusion *)
            (
              (* this willl not terminate if concl_in contains duplicate patterns (equality required) *)
              if ListUtil.contains_duplicate concl_in
                then failwith ("Cannot handle duplicate terms in concl_in " ^ TP.show_rel_clause rel_clause)
              else
              let split = PairSplit.from_list_f concl_in (fun t -> 
                if List.mem t premise1_in 
                  then PairSplit.Left 
                else if List.mem t premise2_in 
                  then PairSplit.Right 
                else failwith "E201: Cannot split concl_in") in
              premise1_in = PairSplit.select_left split concl_in
              && (ListUtil.minus premise2_in [premise1_out]) = (PairSplit.select_right split concl_in)
            )
          )
          | _ -> false (* not cut if free vars*)
        )
        | [], [TP.TmPair(l, r), _] -> (
          (* check is tensor *)
          premise1_out = l
          && premise2_out = r
          && ListUtil.equal_as_sets concl_in (premise1_in @ premise2_in)
        )
        | _ -> false (* two premises not cut or tensorR*)
    )
  | _ -> false (* more than two premises*)

let tp_to_tp_concl_patterns (tp : TP.t) : TP.t option = 
  (* print_endline "Calling on "; *)
  tp_to_tp_proc tp (
    fun (rel_clause) -> 
      (* try to compile only those that cannot be compiled*)
      if can_compile_single_rel_clause rel_clause 
      then (
        (* print_endline ("OK to compile" ^ TP.show_rel_clause rel_clause); *)
        false 
      )
      else (
        true 
      )
  ) (fun (clause_idx, clause_name, first_clause) -> 
    let (premises, (concl_in, _concl_rel_name, concl_out)) = first_clause in
    if Flags.verbose () then print_endline ("TP544: Transforming " ^ TP.show_rel_clause_entry (clause_name, first_clause));
    if ListUtil.contains_duplicate (List.filter (fun x -> TP.is_tm_var x) concl_in) 
      then failwith ("Cannot handle duplicate terms in concl_in " ^ TP.show_rel_clause_entry (clause_name, first_clause));
    (* check if the concl_in is a single term *)
    let concl_in_patterns = TP_to_LP.get_non_var_terms_with_idxs concl_in in
    (* check if there are PlusL candidates, if so, a global signature transform is required.
      For example, X (P, Q) (c Z) > d > W, we cannot decompose (P,Q) here because (P, Q) can only be 
    decomposed when (c Z) is the case, thus all plusL rules have priority and plusL rules need to simultaneously 
    do other clause transformations
      *)
(* PlusL needs to be a global transformation, semantics changes if plusL is not global *)
    (* BIG STEP 1  PLUS L GOES FIRST (OUTDATED)*)
    (* match (List.find_opt (fun (term, _) -> 
                              match term with
                              | TP.Ap (_, _) -> true (* TODO: multiarg*)
                              | _ -> false
                          ) concl_in_patterns) with
    | Some(TP.Ap(cons_name, _arg), idx) -> (
        (* need to transform all clauses in signature whose idx-th argument agrees with this *)
        (do_plus_l_transform tp cons_name concl_rel_name (List.length concl_in) idx)
    )
    | Some _ -> failwith ("E40: Unsupported term in tp_to_tp " ^ TP.show_rel_clause first_clause)
    | None ->  *)
    (
      (* now we can do the remaining rules directly without global transformation *)
      (* BIG STEP 1 : CONCL IN RULES *)
      match concl_in_patterns with
      | _::_ -> do_decompose_concl_in_patterns tp clause_idx
      | [] -> (
        match premises with
        | (premise_in, _, _)::_ -> (
          let premise_in_patterns = TP_to_LP.get_non_var_terms_with_idxs premise_in in
          match premise_in_patterns with
          | _ :: _ -> (
            (* BIG STEP 2: PREMISE IN RULES *)
            do_decompose_premise_in_patterns tp clause_idx
          )
          | [] -> (
            if can_do_dup_insertion_for_premise tp clause_idx 
              then 
                (* BIG STEP 3: DUP for premises*)
                do_dup_insertion_for_premise tp clause_idx
              else
                (* BIG STEP 4: CUT RULES *)
                do_cut_rules tp clause_idx
          )
        )
        | [] -> (
          if not (List.is_empty (ListUtil.minus (List.concat_map TP.free_vars_in_term concl_in) (TP.free_vars_in_term concl_out))) 
            then
              (* BIG STEP 5 : INSERT DEALLOC *)
              do_dealloc_insertion tp clause_idx
            else
              (* BIG STEP 6 : CONCL OUT RULES *)
              do_concl_out_rules tp clause_idx
        )
      )
    )
  )

let tp_to_tp_top (tp : TP.t) : TP.t * TP.t list (* intermediate steps for debugging *) = 
  let rec aux tp acc = 
    (* print_endline ("TP_to_TP_top on " ^ TP.show_signature tp); *)
    match tp_to_tp_concl_patterns tp with
    | None -> tp, acc
    | Some new_tp -> aux new_tp (acc @ [new_tp])
  in
  aux tp []
