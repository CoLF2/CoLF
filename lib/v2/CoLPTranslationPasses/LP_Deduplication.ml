
module LP = CoLPSignature.CoLPSignature
  
type ('a, 'b) map = ('a * 'b) list
module UnionFind : sig
  type t
  val new_uf : string list -> t
  val is_same : t -> string -> string -> bool
  val union : t -> string -> string -> t
end = struct
  type t = (string * string) list
  let new_uf (names : string list) : t = 
    assert (ListUtil.contains_duplicate names = false);
    List.map (fun name -> (name, name)) names

  let find (parent : (string, string) map) (name : string) : string =
    let result = ref name in
    while !result <> ListUtil.lookup_elem_by_key parent name do
      result := ListUtil.lookup_elem_by_key parent !result
    done;
    !result

  let is_same (uf : t) (name1 : string) (name2 : string) : bool =
    let parent1 = find uf name1 in
    let parent2 = find uf name2 in
    parent1 = parent2
  
  let union (uf : t) (name1 : string) (name2 : string) : t =
    let parent1 = find uf name1 in
    let parent2 = find uf name2 in
    if parent1 <> parent2 then
      ListUtil.update_elem_by_key uf parent1 parent2
    else
      failwith "UnionFind.union: names are already in the same set"
  end

  
  
let new_rel_name_with_prefix (tp : LP.colp_sig_duplicated) (concl_rel_name : string) (new_name_prefix : string) = 
  let new_rel_name = ref (concl_rel_name ^ "_" ^ new_name_prefix) in
  let exclude = List.map fst tp.relational_sig in
  Naming.new_var_name !new_rel_name exclude
  

let union_rel_clause 
  (_s : LP.colp_sig_duplicated ref)
  (name_unify : string -> string -> unit) (* if the union is successful provided that the two names are the same *)
  (_add_relational_clause : string -> string -> LP.relational_type -> LP.relational_clause -> unit)
  (_l_rel_name : string) 
  (_r_rel_name : string)
  (l : LP.relational_clause) (* primary*) (r : LP.relational_clause) : LP.relational_clause = 
  match l, r with
  | LP.Id, LP.Id -> LP.Id
  | LP.UnitR, LP.UnitR -> LP.UnitR
  | LP.Duplicate, LP.Duplicate -> LP.Duplicate
  | LP.Dealloc, LP.Dealloc -> LP.Dealloc
  | LP.PlusL { premise_names = l_premise_names; idx = l_idx }, LP.PlusL { premise_names = r_premise_names; idx = r_idx } -> ( 
    if l_idx <> r_idx then failwith (
      "LPD58: PlusL clauses with different indexes\n" ^ 
      LP.show_rel_clause l ^ "\n" ^
      LP.show_rel_clause r
    )
    else (
      let domain = ListUtil.union (List.map fst l_premise_names) (List.map fst r_premise_names) in
      let new_premise_names = List.map (
        fun (name) ->
          (* check if name in r_premise_names*)
          match ListUtil.find_elem_by_key l_premise_names name, 
                ListUtil.find_elem_by_key r_premise_names name with
          | Some l_premise_name, Some r_premise_name -> 
            name_unify l_premise_name r_premise_name;
            (name, l_premise_name)
          | Some l_premise_name, None -> 
            (name, l_premise_name)
          | None, Some r_premise_name ->
            (name, r_premise_name)
          | None, None ->
            failwith ("E44: Premise name not found in either clause " ^ name)
      ) domain in
      LP.PlusL { premise_names = new_premise_names; idx = l_idx }
    )
  )
  | LP.PlusR { premise_name = l_premise_name; data_constructor_name = l_data_constructor_name }, 
    LP.PlusR { premise_name = r_premise_name; data_constructor_name = r_data_constructor_name } -> (
      if l_data_constructor_name <> r_data_constructor_name then failwith "E45: PlusR clauses with different data constructor names"
      else (
        name_unify l_premise_name r_premise_name;
        LP.PlusR { premise_name = l_premise_name; data_constructor_name = l_data_constructor_name }
      )
    )
  | LP.Cut { new_chan_tp = l_new_chan_tp; left_premise = l_left_premise; right_premise = l_right_premise; split = l_split; idx = l_idx }, 
    LP.Cut { new_chan_tp = r_new_chan_tp; left_premise = r_left_premise; right_premise = r_right_premise; split = r_split; idx = r_idx } -> (
      if l_new_chan_tp <> r_new_chan_tp 
        || l_idx <> r_idx
        || l_split <> r_split
        then failwith (
          "E46: Cut clauses with different new channel types or splits" ^
          "\n" ^ LP.show_rel_clause l ^
          "\n" ^ LP.show_rel_clause r
        )
      else (
          name_unify l_left_premise r_left_premise;
          name_unify l_right_premise r_right_premise;
          l
      )
    )
  | LP.UnitL { premise_name = l_premise_name; idx = l_idx }, LP.UnitL { premise_name = r_premise_name; idx = r_idx } -> (
    if l_idx <> r_idx then failwith "E47: UnitL clauses with different indexes"
    else (
      name_unify l_premise_name r_premise_name;
      l
    )
  )
  | LP.TensorL { premise_name = l_premise_name; idx = l_idx }, LP.TensorL { premise_name = r_premise_name; idx = r_idx } -> (
    if l_idx <> r_idx then failwith "E48: TensorL clauses with different indexes"
    else (
      name_unify l_premise_name r_premise_name;
      l
    )
  )
  | LP.TensorR { left_premise = l_left_premise; right_premise = l_right_premise; split = l_split }, 
    LP.TensorR { left_premise = r_left_premise; right_premise = r_right_premise; split = r_split } -> (
      if l_split <> r_split then failwith "E49: TensorR clauses with different splits"
      else (
        name_unify l_left_premise r_left_premise;
        name_unify l_right_premise r_right_premise;
        l
      )
    )
  | LP.PermL { premise_name = l_premise_name; indexes = l_indexes },
    LP.PermL { premise_name = r_premise_name; indexes = r_indexes } -> (
      if l_indexes <> r_indexes then failwith "E50: PermL clauses with different indexes"
      else (
        name_unify l_premise_name r_premise_name;
        l
      )
    )
  (* | _, LP.Cut _ -> (
      (* if one side is cut and the other side is not, carry out cut_id expansion for the other side so we can proceed*)
      let new_l_rel_name = new_rel_name_with_prefix !s l_rel_name "cutexp_cut" in
      let new_r_rel_name = new_rel_name_with_prefix !s l_rel_name "cutexp_id" in
      let l_rel_tp = (fst (ListUtil.lookup_elem_by_key !s.relational_sig l_rel_name)) in
      let output_tp = l_rel_tp.output in
      let new_l_rel_tp = l_rel_tp in
      let new_r_rel_tp : LP.relational_type = {
        inputs = [output_tp];
        output = output_tp;
      } in
      let new_l_rel_clause = l in
      let new_r_rel_clause = LP.Id in
      let new_this_rel_clause = LP.Cut {
        new_chan_tp = output_tp;
        left_premise = new_l_rel_name;
        right_premise = new_r_rel_name;
        split = PairSplit.from_list_f (ListUtil.range 0 (List.length l_rel_tp.inputs)) (fun _ -> PairSplit.Left);
        idx = 0;
      } in
      add_relational_clause l_rel_name new_l_rel_name new_l_rel_tp new_l_rel_clause;
      add_relational_clause l_rel_name new_r_rel_name new_r_rel_tp new_r_rel_clause;
      union_rel_clause s name_unify add_relational_clause l_rel_name r_rel_name new_this_rel_clause r
    ) *)
  | _ -> failwith (
      "E51: Different clauses found in deduplication" ^
      "\n" ^ LP.show_rel_clause l ^
      "\n" ^ LP.show_rel_clause r
    )

let deduplicate_lp (s : LP.colp_sig_duplicated) : LP.colp_sig = 
  let uf = ref (UnionFind.new_uf (List.map fst s.relational_sig)) in
  let propagation_queue = ref [] in
  let sref = ref s in
  let lookup_relational_clauses name = snd (ListUtil.lookup_elem_by_key !sref.relational_sig name) in
  let update_relational_clauses name rel_clauses = 
    sref := { !sref with relational_sig = ListUtil.update_elem_by_key !sref.relational_sig name (
        (fst (ListUtil.lookup_elem_by_key !sref.relational_sig name), rel_clauses)
    ) } in
  let add_relational_clause (name_idx : string) name rel_type rel_clause = 
    sref := { !sref with relational_sig = 
    ListUtil.insert_after_index !sref.relational_sig (ListUtil.lookup_index_of_elem_by_key !sref.relational_sig name_idx) (
      (name, (rel_type, [rel_clause]))
    ) } in
  let name_unify name1 name2 = 
    if UnionFind.is_same !uf name1 name2
      then ()
      else (
        uf := UnionFind.union !uf name1 name2;
        propagation_queue := (name1, name2) :: !propagation_queue
      ) in
  let union_rel_clause = union_rel_clause sref name_unify add_relational_clause in
  let do_propagate() = 
    while !propagation_queue <> [] do
      let (name1, name2) = List.hd !propagation_queue in
      if Flags.verbose() then print_endline ("LP_Dedup Propagating " ^ name1 ^ " and " ^ name2);
      propagation_queue := List.tl !propagation_queue;
      let rel_clauses1 = lookup_relational_clauses name1 in
      let rel_clauses2 = lookup_relational_clauses name2 in
      let rel_clause1 = ListUtil.fold_left_non_empty (union_rel_clause name1 name1) rel_clauses1 in
      let rel_clause2 = ListUtil.fold_left_non_empty (union_rel_clause name2 name2) rel_clauses2 in
      let new_rel_clause1 = union_rel_clause name1 name2 rel_clause1 rel_clause2 in
      let new_rel_clause2 = union_rel_clause name2 name1 rel_clause2 rel_clause1 in
      update_relational_clauses name1 [new_rel_clause1];
      update_relational_clauses name2 [new_rel_clause2];
    done
  in
  while List.exists (fun (_name, (_tp, entry)) -> List.length entry > 1) !sref.relational_sig do
    let (name, (_tp, entry)) =  List.find  (fun (_name, (_tp, entry)) -> List.length entry > 1) !sref.relational_sig in
      if Flags.verbose() then print_endline ("LP_Dedup Unifying the clauses of " ^ name);
    let new_rel_clause = ListUtil.fold_left_non_empty (union_rel_clause name name) entry in
    update_relational_clauses name [new_rel_clause];
    do_propagate()
  done;
  {data_sig = !sref.data_sig;
  relational_sig = List.map (fun (name, (tp, y)) -> 
    (name, (tp, List.hd y) 
  )) !sref.relational_sig
  }










