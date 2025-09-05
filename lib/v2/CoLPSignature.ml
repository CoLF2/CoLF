module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode
module PrettyPrint = PrettyPrint.PrettyPrint
module Ctx = TypeCheckingCtx.TypeCheckingCtx
module Ext = AbtLib.Extent


module CoLPSignature = struct
  type ('a, 'b) map = ('a * 'b) list

  type tp = TpVar of string | TpTensor of tp * tp| TpUnit | TpArrow of tp * tp

  let is_tp_var (tp : tp) : bool =
    match tp with
    | TpVar _ -> true
    | _ -> false

  let rec tp_iter (tp : tp) (f : string -> unit) : unit =
    match tp with
    | TpVar s -> f s
    | TpUnit -> ()
    | TpTensor (tp1, tp2) ->
      tp_iter tp1 f;
      tp_iter tp2 f
    | TpArrow (tp1, tp2) ->
      tp_iter tp1 f;
      tp_iter tp2 f

  type data_sig = (string (* type name *), (string (* constructor name*) * tp) list ) map


  type relational_clause = 
    (* x : A |- x : A *)
    Id  
    (* G |- A;     D, x : A, D' |- B ==> G, D, D' |- B *)
    | Cut of {
      new_chan_tp : tp;
      left_premise : string;
      right_premise : string;
      split : PairSplit.t;
      idx : int; (* cutted new channel is inserted at this index when calling the right premise*)
    }
    | PlusR of {
      premise_name : string;
      data_constructor_name : string;
    }
    | PlusL of {
      premise_names: (string, string) map; (* constructor_name -> premise name*)
      idx: int; (* analyze the ith argument *)
    }
    | TensorR of {
      left_premise : string;
      right_premise : string ;
      split : PairSplit.t;
    }
    | TensorL of {
      premise_name : string;
      idx : int;
    }
    | UnitR 
    | UnitL of {
      premise_name : string;
      idx : int;
    }
    | PermL of {
      premise_name : string;
      indexes : int list; (* index remapping, indexes[i]=j indicates that the ith inputs in the premise is the j-th input in the conclusion*)
    }
    | Duplicate
    | Dealloc

  type relational_type = {
    inputs : tp list;
    output : tp;
  }

  type relational_sig = (string, relational_type  * relational_clause ) map

  type colp_sig = {
    data_sig : data_sig;
    relational_sig : relational_sig;
  }
  type colp_sig_duplicated = {
    data_sig : data_sig;
    relational_sig :  (string, relational_type  * relational_clause list ) map
  }
  type t = colp_sig
  let rec show_tp (t : tp) : string =
    match t with
    | TpVar s -> s
    | TpUnit -> "1"
    | TpTensor (tp1, tp2) -> "(" ^ (show_tp tp1) ^ " * " ^ (show_tp tp2) ^ ")"
    | TpArrow (tp1, tp2) -> "(" ^ (show_tp tp1) ^ " -> " ^ (show_tp tp2) ^ ")"

  let show_rel_clause (r : relational_clause) : string = 
    match r with
    | Id -> "Id"
    | Cut {new_chan_tp = new_chan_tp; left_premise = left_premise_name; right_premise = right_premise_name; split = split; idx=idx} ->
      "Cut {new_chan_tp = " ^ show_tp new_chan_tp ^ "; left_premise = " ^ left_premise_name ^ "; right_premise = " ^ right_premise_name ^ "; split = " ^ PairSplit.show split ^ "; idx = " ^ string_of_int idx ^ "}"
    | PlusR {premise_name = premise_name; data_constructor_name = data_constructor_name} ->
      "PlusR {premise_name = " ^ premise_name ^ "; data_constructor_name = " ^ data_constructor_name ^ "}"
    | PlusL {premise_names = premise_names; idx = idx} ->
      "PlusL {premise_names = " ^ String.concat "\n                         , " (List.map (fun (cons_name, subcall_name) -> Printf.sprintf "'%s => %s" cons_name subcall_name) premise_names) ^ "; idx = " ^ string_of_int idx ^ "}"
    | TensorR {left_premise = left_premise_name; right_premise = right_premise_name; split = split} ->
      "TensorR {left_premise = " ^ left_premise_name ^ "; right_premise = " ^ right_premise_name ^ "; split = " ^ PairSplit.show split ^ "}"
    | TensorL {premise_name = premise_name; idx = idx} ->
      "TensorL {premise_name = " ^ premise_name ^ "; idx = " ^ string_of_int idx ^ "}"
    | UnitR -> "UnitR"
    | UnitL {premise_name = premise_name; idx = idx} ->
      "UnitL {premise_name = " ^ premise_name ^ "; idx = " ^ string_of_int idx ^ "}"
    | PermL {premise_name = premise_name; indexes = indexes} ->
      "PermL {premise_name = " ^ premise_name ^ "; indexes = " ^ String.concat ", " (List.map string_of_int indexes) ^ "}"
    | Duplicate -> "Duplicate"
    | Dealloc -> "Dealloc"

  let show_rel_type ({inputs = inputs; output = output} : relational_type) : string =
    let inputs_str = String.concat " , " (List.map show_tp inputs) in
    let output_str = show_tp output in
    inputs_str ^ " >=> " ^ output_str

  let show_rel_clause_entry ((rel_name, ({inputs;output}, rel_clause)) : (string * (relational_type * relational_clause))) : string =
    Printf.sprintf "%s : %s = %s" rel_name (show_rel_type {inputs = inputs; output = output}) (show_rel_clause rel_clause)

  let collect_premise_names (clause : relational_clause) : string list = 
    match clause with
    | Id -> []
    | Cut {left_premise = left_premise_name; right_premise = right_premise_name; _} -> 
      [left_premise_name; right_premise_name]
    | PlusR {premise_name = premise_name; _} ->

      [premise_name]
    | PlusL {premise_names = premise_names; _} ->
      List.map snd premise_names
    | TensorR {left_premise = left_premise_name; right_premise = right_premise_name; _} ->
      [left_premise_name; right_premise_name]
    | TensorL {premise_name = premise_name; _} ->
      [premise_name]
    | UnitR -> []
    | UnitL {premise_name = premise_name; _} ->
      [premise_name]
    | PermL {premise_name = premise_name; _} ->
      [premise_name]
    | Duplicate -> []
    | Dealloc -> []


  let assert_b (b : bool) (s : string) : unit =
    if not b then
      failwith s
    else ()

  let type_check_data_sig (ds : data_sig) : unit =
    List.iter (fun (_tp_name, clauses) ->
      List.iter (fun (_cons_name, cons_tp) ->
        tp_iter cons_tp (fun c ->
          assert_b (ListUtil.elem_exists_by_key ds c) ("Data constructor " ^ c ^ " not found in data signature")
        ) 
      ) clauses
    ) ds

  let lookup_rel_type (rs : relational_sig) (name : string) : relational_type =
      let (tp, _) = ListUtil.lookup_elem_by_key rs name in
      tp

  let lookup_data_cons_arg (rs : data_sig) (c_name : string) : tp = 
    let candidates = List.filter_map (fun (_, clauses) -> (
      ListUtil.find_elem_by_key clauses c_name
    )) rs in
    match candidates with
    | [] -> failwith ("Data constructor " ^ c_name ^ " not found in data signature")
    | [cons_tp] -> cons_tp
    | _ -> failwith ("Data constructor " ^ c_name ^ " found in multiple data signatures")

  let input_replace (inputs : 'a list) (idx : int) (new_input : 'a list) : 'a list =
    List.concat (List.mapi (fun i x ->
      if i = idx then new_input else [x]
    ) inputs)

  let type_check_relational_sig (ds : data_sig) (rs : relational_sig) : unit =
    List.iter (fun ((_, ({inputs =inputs; output =output}, clause)) as entry) ->
      match clause with
      | Id -> (
        match inputs with 
        | [input] -> assert_b (input = output) ("Id clause must have the same input and output type")
        | _ -> failwith "Relational clause Id must have exactly one input"
      )
      | Duplicate -> (
        match inputs, output with
        | [i], TpTensor(j, k) -> assert_b (i = j && i = k) ("Duplicate E185")
        | _ -> failwith "E186"
      )
      | Dealloc -> (
        match inputs, output with
        | [_], TpUnit -> ()
        | _ -> failwith "E191"
      )
      | PermL {
        premise_name = premise_name;
        indexes = indexes;
      } -> (
        assert_b (lookup_rel_type rs premise_name = 
        {inputs = (List.map (fun idx -> List.nth inputs idx) indexes); output = output}) ("PermL clause " ^ premise_name ^ " does not match the relational signature");
      )
      | Cut {new_chan_tp = new_chan_tp; 
      left_premise = (left_premise_name);
      right_premise = (right_premise_name);
      split = split;
      idx=idx;
      } -> (
        (* check left_premise_indices and right_premise_indices are okay *)
        (* check left_premise_name and right_premise_name are okay *)
        assert_b (ListUtil.elem_exists_by_key rs left_premise_name) ("CS156: Left premise " ^ left_premise_name ^ " not found in data signature");
        assert_b (ListUtil.elem_exists_by_key rs right_premise_name) ("CS157: Right premise " ^ right_premise_name ^ " not found in data signature");
        assert_b ({
          inputs = PairSplit.select_left split inputs;
          output = new_chan_tp;
        } = lookup_rel_type rs left_premise_name ) ("Left premise " ^ left_premise_name ^ " does not match the relational signature");
        assert_b ({
          inputs = 
          ListUtil.insert_at_index (PairSplit.select_right split inputs ) idx [new_chan_tp];
          output = output;
        } = lookup_rel_type rs right_premise_name) ("Right premise " ^ right_premise_name ^ " does not match the relational signature")
      )
      | TensorR {left_premise = (left_premise_name);
        right_premise = (right_premise_name);
        split = split;
        } -> (
        (* check left_premise_name and right_premise_name are okay *)
        assert_b (ListUtil.elem_exists_by_key rs left_premise_name) ("Left premise " ^ left_premise_name ^ " not found in data signature");
        assert_b (ListUtil.elem_exists_by_key rs right_premise_name) ("Right premise " ^ right_premise_name ^ " not found in data signature");
        match output with
        | TpVar _ | TpUnit | TpArrow _ -> failwith "TensorR clause must have a tensor output type"
        | TpTensor (l, r) -> (
          assert_b (lookup_rel_type rs left_premise_name = {inputs = PairSplit.select_left split inputs; output = l}) ("Left premise " ^ left_premise_name ^ " does not match the relational signature");
          assert_b (lookup_rel_type rs right_premise_name = {inputs = PairSplit.select_right split inputs; output = r}) ("Right premise " ^ right_premise_name ^ " does not match the relational signature")
        )
        )
      | PlusR {premise_name = premise_name; data_constructor_name = data_constructor_name} -> (
        (* check premise_name and data_constructor_name are okay *)
        match output with
        | TpTensor _ | TpUnit | TpArrow _ -> failwith "PlusR clause must not have a tensor output type"
        | TpVar tp_name ->
          let new_output = ListUtil.lookup_elem_by_key (ListUtil.lookup_elem_by_key ds tp_name) data_constructor_name in
          assert_b (lookup_rel_type rs premise_name = {inputs = inputs; output = new_output}) ("PlusR clause " ^ premise_name ^ " does not match the relational signature")
      )
      | TensorL {premise_name = premise_name; idx = idx} -> (
        (* check premise_name and idx are okay *)
        match List.nth inputs idx with
        | TpVar _ | TpUnit | TpArrow _ -> failwith "TensorL clause must not have a tensor output type"
        | TpTensor (l, r) ->
          let new_inputs = input_replace inputs idx [l; r] in
          assert_b (lookup_rel_type rs premise_name = {inputs = new_inputs; output = output}) ("TensorL clause " ^ premise_name ^ " does not match the relational signature")
      )
      | UnitL {premise_name = premise_name; idx = idx} -> (
        (* check premise_name and idx are okay *)
        match List.nth inputs idx with
        | TpVar _ | TpTensor _ | TpArrow _ -> failwith "UnitL clause must not have a tensor output type"
        | TpUnit ->
          let new_inputs = input_replace inputs idx [] in
          assert_b (lookup_rel_type rs premise_name = {inputs = new_inputs; output = output}) ("UnitL clause " ^ premise_name ^ " does not match the relational signature")
      )
      | UnitR -> (
        match inputs, output with
        | [], TpUnit -> ()
        | _ -> failwith "UnitR clause must have a unit output type"
      )
      | PlusL {
        premise_names = premise_names;
        idx = idx;
      } -> (
        match List.nth inputs idx with
        | TpTensor _ | TpUnit | TpArrow _ -> failwith "PlusL clause must not have a tensor output type"
        | TpVar tp_name ->
          (* check coverage *)
          let cons_and_tps =  (ListUtil.lookup_elem_by_key ds tp_name) in
          if not (List.for_all (fun (data_constructor_name, _) -> 
            List.mem data_constructor_name (List.map fst premise_names)) cons_and_tps)
            then failwith 
              ("CLP275: PlusL clause " ^ show_rel_clause_entry entry ^ " does not cover all data constructors in the data signature: \n" ^
              "All premise names of PlusL: " ^ String.concat ", " (List.map fst premise_names) ^
              "\nAll data constructors: " ^ String.concat ", " (List.map fst cons_and_tps)
              );

        (* check premise_names and idx are okay *)
        List.iter (fun (data_constructor_name, data_cons_tp) ->
          let new_inputs = input_replace inputs idx [data_cons_tp] in
          try
            assert_b (lookup_rel_type rs (ListUtil.lookup_elem_by_key premise_names data_constructor_name) = {inputs = new_inputs; output = output}) ("PlusL clause " ^ data_constructor_name ^ " does not match the relational signature");
          with Failure s ->
            failwith (s ^ "when checking PlusL clause " ^ show_rel_clause clause ^ " with inputs " ^ String.concat ", " (List.map show_tp inputs) ^ " and output " ^ show_tp output)
        ) (ListUtil.lookup_elem_by_key ds tp_name);
      )
    ) rs
(* 
  let rec flatten_tp (tp : tp) : string list =
    match tp with
    | TpVar s -> [s]
    | Tensor (tp1, tp2) -> flatten_tp tp1 @ flatten_tp tp2

  let rec flatten_tp_list (tps : tp list) : string list =
    List.concat (List.map flatten_tp tps) *)
  
  let print_ds (ds : data_sig) : string = 
    String.concat "" (List.map (fun (tp_name, clauses) ->
            "type "^ tp_name ^ " = +{" ^ 
            String.concat ", " (List.map (fun (cons_name, cons_tp) ->
              "'" ^ cons_name ^ " : " ^ (show_tp cons_tp) 
            ) clauses) ^
            "}\n"
          ) ds
    )

  let show_sig (s : t) : string = 
    print_ds s.data_sig ^ "\n\n" ^
    String.concat "\n" (List.map (fun (rel_name, (rel_type, clause)) ->
      rel_name ^ " : " ^ show_rel_type rel_type ^ "\n    " ^ show_rel_clause clause
    ) s.relational_sig)

  let show_sig_duplicated (s : colp_sig_duplicated) : string = 
    print_ds s.data_sig ^ "\n\n" ^
    String.concat "\n" (List.map (fun (rel_name, (rel_type, clauses)) ->
      rel_name ^ " : " ^ show_rel_type rel_type ^ 
      String.concat "" (List.map (fun clause -> "\n    " ^ show_rel_clause clause) clauses)
    ) s.relational_sig)

  module SAXPrint = struct


    (* print rel_clause assuming indent is already printed, does not print terminal newline*)
    let print_rel_clause (lp_sig: t) (indent: int)(clause : relational_clause) (inputs : (string * tp) list) ((output_name, output_tp) as output : string * tp)
        (premise_print : int -> string (*fname*)-> (string * tp) list -> string * tp -> string) 
    =
    let newline = "\n" ^ String.make indent ' ' in
    let next_indent = indent + 2 in
    let new_var_name x = Naming.new_var_name x (output_name::(List.map fst inputs)) in
    let indented_newline = "\n" ^ String.make next_indent ' ' in
    let double_indented_newline = "\n" ^ String.make (next_indent+2) ' ' in
        match clause, inputs with
        | Id, [(single_input, _)] ->  Printf.sprintf "id %s %s" output_name single_input
        | Id, _ -> failwith "Id clause must have exactly one input"
        | UnitR, [] -> Printf.sprintf "write %s ()" output_name
        | UnitR, _ -> failwith "UnitR clause must have exactly zero input"
        | Duplicate, [(single_input, _)] -> Printf.sprintf "write %s (%s, %s)" output_name single_input single_input
        | Duplicate, _ -> failwith "Duplicate clause must have exactly one input"
        | Dealloc, [(_single_input, _)] -> Printf.sprintf "write %s ()" output_name
        | Dealloc, _ -> failwith "Dealloc clause must have exactly one input"
        | Cut {
          new_chan_tp = new_chan_tp;
          left_premise = left_premise_name;
          right_premise = right_premise_name;
          split = split;
          idx = idx;
        }, _ -> (
          (* let left_premise_indices = PairSplit.get_left split in
          let right_premise_indices = PairSplit.get_right split in *)
          let cut_var = (new_var_name "y", new_chan_tp) in
          "cut " ^ fst cut_var ^ " : " ^ show_tp new_chan_tp ^ indented_newline ^
          premise_print next_indent left_premise_name (PairSplit.select_left split inputs) cut_var
          ^ newline
          ^ premise_print indent right_premise_name (ListUtil.insert_at_index (PairSplit.select_right split inputs) idx [cut_var]) output 
          (* left_premise_name ^ " y " ^ 
          String.concat "" (List.map (fun i -> Printf.sprintf "x%d " i) left_premise_indices) ^ "\n  " ^
          right_premise_name ^ " d " ^
          String.concat "" (List.map (fun i -> Printf.sprintf "x%d " i) right_premise_indices) ^
          "y\n" *)
        )
        | PlusL {premise_names = premise_names; idx = idx}, _ -> (
          let read_var = Naming.new_var_name ("x"^string_of_int idx) (
            output_name :: (List.map fst (ListUtil.replace_idx inputs idx []))
          ) in
          Printf.sprintf "read " ^ (List.nth inputs idx |> fst) ^ " {\n" ^ 
          String.concat "" (List.map (fun (cons_name, subcall_name) -> 
            let read_var_tp = (
              List.nth (lookup_rel_type lp_sig.relational_sig subcall_name).inputs idx
            ) in
            Printf.sprintf "%s| '%s(%s) => " (String.make next_indent ' ') cons_name read_var ^ indented_newline ^ "  "
            ^ premise_print (next_indent + 2) subcall_name (ListUtil.replace_idx inputs idx [(read_var, read_var_tp)]) output ^ "\n"
          )
            premise_names) ^
            String.make indent ' ' ^ "}"
        )
        | PlusR {premise_name = premise_name; data_constructor_name = data_constructor_name}, _ -> (
          match output_tp with
          | TpTensor _ | TpUnit | TpArrow _ -> failwith "PlusR clause must not have a tensor output type"
          | TpVar output_tp_name ->
             let cut_type = ListUtil.lookup_elem_by_key (ListUtil.lookup_elem_by_key lp_sig.data_sig output_tp_name) data_constructor_name in
             let cut_name = Naming.new_var_name "y" (output_name::(List.map fst inputs)) in
             "cut "^ cut_name ^" : " ^ show_tp cut_type ^ indented_newline ^
             premise_print next_indent premise_name inputs (cut_name, cut_type) ^ newline ^
             "write " ^ output_name ^ " '" ^ data_constructor_name ^ " "  ^ cut_name
        )
        | TensorR {
          left_premise = left_premise_name;
          right_premise = right_premise_name;
          split = split;
        },_ -> (
          match output_tp with
          | TpVar _ | TpUnit | TpArrow _ -> failwith "TensorR clause must have a tensor output type"
          | TpTensor (l, r) ->
          let l_name = new_var_name "y" in
          let r_name = new_var_name "z" in
          "cut " ^ l_name ^ " : " ^ show_tp l ^ indented_newline ^
          premise_print next_indent left_premise_name (PairSplit.select_left split inputs) (l_name, l) ^ newline ^
          "cut " ^ r_name ^ " : " ^ show_tp r ^ indented_newline ^
          premise_print next_indent right_premise_name (PairSplit.select_right split inputs) (r_name, r) ^ newline ^
          Printf.sprintf "write %s (%s, %s)" output_name l_name r_name
        )
        | TensorL {premise_name = premise_name; idx = idx} , _ -> (
          match List.nth inputs idx |> snd with
          | TpVar _ | TpUnit | TpArrow _ -> failwith "TensorL clause must not have a tensor output type"
          | TpTensor (l_tp, r_tp) ->
            let l_name = new_var_name "y" in
            let r_name = new_var_name "z" in
            Printf.sprintf "read %s {%s" (List.nth inputs idx |> fst) indented_newline ^
            Printf.sprintf "| (%s, %s) => " l_name r_name ^ double_indented_newline ^
            (premise_print (next_indent + 2) premise_name (ListUtil.replace_idx inputs idx [(l_name, l_tp); (r_name, r_tp)]) output)
             ^ newline ^ "}"
        )
        | UnitL {premise_name = premise_name; idx = idx},_ -> (
          match List.nth inputs idx |> snd with
          | TpVar _ | TpTensor _ | TpArrow _ -> failwith "UnitL clause must not have a tensor output type"
          | TpUnit ->
            Printf.sprintf "read %s {%s" (List.nth inputs idx |> fst) indented_newline ^
            Printf.sprintf "| () => "  ^ double_indented_newline ^
            (premise_print (next_indent + 2) premise_name (ListUtil.replace_idx inputs idx []) output)
             ^ newline ^ "}"
            (* Printf.sprintf "read x%d {\n    " idx ^
            Printf.sprintf "| () => %s d " premise_name ^ 
            String.concat "" (List.mapi (fun i _ -> if i <> idx then Printf.sprintf "x%d " i else "") inputs) ^ "\n  }" *)
        )
        | PermL {
          premise_name = premise_name;
          indexes = indexes;
        }, _ -> (
          premise_print indent premise_name (List.map (fun i -> List.nth inputs i) indexes) output
        )
    let print_proc_decl (lp_sig : t) (rel_name : string) (clause : relational_clause) (inputs : (tp) list) (output : tp)
    (premise_print : int -> string (*fname*)-> (string * tp) list -> string * tp -> string) 
     : string = 
        let input_names = List.map (fun i -> 
          Printf.sprintf "x%d" i
        ) (ListUtil.range 0 (List.length inputs)) in
        let output_name = "d" in
        "proc " ^ rel_name ^ " (" ^ output_name ^ " : " ^ show_tp (output) ^ ") " ^ String.concat "" (
          List.map (fun (name, tp) -> 
            Printf.sprintf "(%s : %s) " name (show_tp tp)
          ) (List.combine input_names inputs)
        ) ^ " = \n  " ^
        (
          print_rel_clause lp_sig 2 clause (List.combine input_names inputs) (output_name, output) premise_print 
        ) ^ "\n\n"

    let print_rel_sig (lp_sig : colp_sig) : string = 
     String.concat "" (List.map (fun (rel_name, ({inputs = inputs; output = output}, clause)) ->
        print_proc_decl lp_sig rel_name clause (inputs) (output)
        (fun _indent premise_name inputs output ->
                    String.concat " " ([
                      premise_name;
                    ]@(List.map fst (output::inputs))
                  ))
              ) lp_sig.relational_sig 
     )

    let print_sig (lp_sig : colp_sig) : string = 
      let ds_str = print_ds lp_sig.data_sig  in
      let rs_str = print_rel_sig lp_sig in
      ds_str ^ "\n\n" ^ rs_str

    let get_non_inlinable_rel_clause_names (lp_sig : colp_sig) : string list = 
      (* a relclause is non-inlinable if it is self-recursive or it is referenced 
        more than once by other clauses
      TODO: circular loop self-recursion check
        *)
      let referenced = List.map (fun (clause_name, (_, clause)) ->
        (clause_name, collect_premise_names clause)
      ) lp_sig.relational_sig in
      List.filter (fun (clause_name, (_, clause)) ->
        (* check_self_recursive *)
        let premise_names = collect_premise_names clause in
        let self_recur = List.mem clause_name premise_names in
        if self_recur 
          then true
      else
        (* it is not self-recursive *)
        (* check if it is referenced more than once in other clauses *)
        let referenced_count = List.length (
          List.filter (fun (_, premise_names) ->
            List.mem clause_name premise_names
          ) referenced
        ) in
        if referenced_count > 1
          then true
        else false
        (* check if it is referenced more than once in other clauses *)
      ) lp_sig.relational_sig |> List.map fst

    let print_rel_sig_compact (lp_sig : colp_sig) : string = 
      let non_inlinable_names = get_non_inlinable_rel_clause_names lp_sig @["main"] in
      (* print_endline ("Non-inlinable names: " ^ String.concat ", " non_inlinable_names); *)
      (* print constructors *)
      let rec premise_print_f = (fun indent premise_name inputs output ->
            if List.mem premise_name non_inlinable_names
              then
                (* only call for non_inlinable names*)
                      String.concat " " ([
                        premise_name;
                      ]@(List.map fst (output::inputs))
                    )
              else  (
                (* call print rule recursively *)
                let clause = ListUtil.lookup_elem_by_key lp_sig.relational_sig premise_name |> snd in
                print_rel_clause lp_sig indent clause inputs output premise_print_f
              )
                ) in
      String.concat "" (List.map (fun (rel_name, ({inputs = inputs; output = output}, clause)) ->
        if List.mem rel_name non_inlinable_names
          then
            (* only call for non_inlinable names*)
            print_proc_decl lp_sig rel_name clause (inputs) (output) premise_print_f
          else
            (* call print rule recursively *)
            ""
          ) lp_sig.relational_sig 
      )

    let print_compact (lp_sig : colp_sig) : string = 
      let ds_str = print_ds lp_sig.data_sig  in
      let rs_str = print_rel_sig_compact lp_sig in
      ds_str ^ "\n\n" ^ rs_str
  end

  module CoLFPrint = struct
    
    let show_ds (ds : data_sig) : string = 
      (* print type names *)
      String.concat "" (List.map (fun (tp_name, _) -> tp_name ^ " : cotype.\n") ds) ^
      (* print constructors *)
      String.concat "" (List.concat_map (fun (tp_name, clauses) ->
        List.map (fun (cons_name, cons_tp) ->
          cons_name ^ " : " ^ (show_tp cons_tp) ^ " -> " ^ tp_name ^ ".\n"
        ) clauses
      ) ds)

    (* let show_rel_type ({inputs = inputs; output = output} : relational_type) : string =
      let inputs_str = String.concat " , " (List.map show_tp inputs) in
      let output_str = show_tp output in
      inputs_str ^ " >=> " ^ output_str *)

  
  end

  (* 

  let print_rs (rs : relational_sig) : string list = 
    (* print constructors *)
    (List.concat_map (fun (tp_name, ({inputs = inputs; output = output}, clause)) ->
      let flattened_inputs = flatten_tp_list inputs in
      let flattened_outputs = flatten_tp output in
      let tp_decl = tp_name ^ " : " ^ (String.concat " -> " (flattened_inputs @ flattened_outputs)) ^ " -> cotype.\n" in
      let mode_decl = "%mode " ^ tp_name ^ " : " ^ (String.concat "" (List.map (fun s -> "+"^s^" " ) flattened_inputs))
      ^ " " ^ String.concat "" (List.map (fun s -> "-"^s^" " ) flattened_outputs) ^ ".\n" in
      let def_decl = tp_name ^ "/def : " ^ String.concat "" (
      match clause with
      | Id -> (
          List.mapi (fun i x -> 
            Printf.sprintf "{ x%d : %s }" i x
          ) flattened_outputs
          @ [" "; tp_name; " "]
          @ List.mapi (fun i _ -> 
            Printf.sprintf " x%d" i
          ) flattened_inputs
          @ List.mapi (fun i _ -> 
            Printf.sprintf " x%d" i
          ) flattened_outputs  
        )
      | Cut {new_chan_tp = new_chan_tp; left_premise = left_premise_name; right_premise = right_premise_name; split = split} ->
        (
          let new_channel_name = "x_new" in
          let left_premise_indices = PairSplit.get_left split in
          let right_premise_indices = PairSplit.get_right split in
          List.mapi (fun i x -> 
            Printf.sprintf "{ x%d : %s }" i x
          ) (flattened_inputs @ flattened_outputs @ flatten_tp new_chan_tp)
          @ [" "; tp_name; " "]
          @ List.mapi (fun i _ -> 
            Printf.sprintf " x%d" i
          ) flattened_inputs
          @ List.mapi (fun i _ -> 
            Printf.sprintf " x%d" i
          ) flattened_outputs
        )

      | PlusR {premise_name = premise_name; data_constructor_name = data_constructor_name} ->
        [tp_name ^ " : " ^ inputs_str ^ " -> " ^ output_str ^ ".\n"]
      | PlusL {premise_names = premise_names; idx = idx} ->
        [tp_name ^ " : " ^ inputs_str ^ " -> " ^ output_str ^ ".\n"]
      | TensorR {left_premise = left_premise_name; right_premise = right_premise_name; split = split} ->
        [tp_name ^ " : " ^ inputs_str ^ " -> " ^ output_str ^ ".\n"]
      | TensorL {premise_name = premise_name; idx = idx} ->
        [tp_name ^ " : " ^ inputs_str ^ " -> " ^ output_str ^ ".\n"]
      ) ^ ".\n" in 
      [tp_decl ^ mode_decl ^ def_decl]
    ) rs)
    

  

  let print_colp_sig ((ds, rs) : colp_sig) : string = 
      
  end *)


    


end