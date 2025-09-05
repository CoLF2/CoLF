module Errors = Errors.Errors



module type OPERATOR = Operators.OPERATOR
module type OPERATORS_SET = OperatorsSet.OPERATORS_SET

module type MIXFIX_PARSER = sig

  type t_expr
  type t_charstream

  val parse : t_charstream -> t_expr list

end

module MixfixParser 
  (Operator : OPERATOR)
  (OperatorsSet: OPERATORS_SET with type operator = Operator.operator and type t_expr = Operator.t_expr) 
  : MIXFIX_PARSER with type t_expr = OperatorsSet.t_expr and type t_charstream = CharStream.CharStream.t = struct

    type t_expr = OperatorsSet.t_expr
    type t_charstream = CharStream.CharStream.t


    type t_stack_op_component = OperatorsSet.operator * int (* component index *)
    type t_extent = string * (int * int) * (int * int)
    type stack_elem = 
      | OperatorComponent of t_stack_op_component  (* this should only be CKeyword Component*)
      | UnknownSymbol of string (* Unknown symbol cannot be pushed on to the stack, convert to expr first*)
      | Space  (* Space cannnot be pushed, drop it first *)
      | Expr of t_expr (* this expression should contain the same t_extent as the stack element *)
      | ArbitraryString of string (* Binding or specialized comments *)

    type stack = (stack_elem * t_extent) list

    module Extent = AbtLib.Extent


    let mark_extent (expr: t_expr) (ext : t_extent) : t_expr = 
      OperatorsSet.annotate_with_extent expr ext

    let show_stack_elem elem =
        match elem with
        | OperatorComponent((op, idx)) ->  "!(" ^ (string_of_int op.id) ^ "," ^ (string_of_int idx) ^ ")<" ^ (Operator.debug_print_operator op) ^ ">"
        | UnknownSymbol s ->  "?(" ^ s ^ ")"
        | Space ->  "<space>"
        | Expr expr ->  ">(" ^ OperatorsSet.debug_show_expr expr ^ ")"
        | ArbitraryString _s ->  "<str>"

    let show_stack (s : stack) : string = 
      List.fold_right (fun (elem, _) acc -> 
        acc ^ "|" ^ (show_stack_elem elem)
      ) s "|start>"

    let show_input (s : t_charstream) : string = 
      let (row, col) = CharStream.CharStream.get_row_col s in
      CharStream.CharStream.get_file_path s ^ ":" ^
      string_of_int row ^ ":" ^ string_of_int col

    let get_op_component (stack_op : t_stack_op_component) : Operator.component = 
      let (op, id) = stack_op in
      List.nth op.components id

    let get_prev_op_component (stack_op : t_stack_op_component) : Operator.component option = 
      let (op, id) = stack_op in
      if id = 0 then None
      else Some (List.nth op.components (id - 1))
    
    let get_next_op_component (stack_op : t_stack_op_component) : Operator.component option = 
      let (op, id) = stack_op in
      if id + 1 = List.length op.components then None
      else Some (List.nth op.components (id + 1))

    let get_all_start_component () : t_stack_op_component list = 
      List.filter_map (fun (op : Operator.operator) -> 
        match op.components with
        | Operator.CKeyword _ ::_ -> Some(op, 0)
        | _ -> None
        ) (OperatorsSet.all_operators ())

    let get_all_start_following_component () : t_stack_op_component list = 
      List.filter_map (fun (op : Operator.operator) -> 
        match op.components with
        | Operator.CComponent _ :: Operator.CKeyword _ ::_ -> Some(op, 1)
        | _ -> None
        ) (OperatorsSet.all_operators ())

    let get_all_following_component (s : stack) :t_stack_op_component list = 
      ListUtil.remove_duplicates (
        get_all_start_component() @
        get_all_start_following_component() @ (
          List.filter_map (fun (stack_elem) -> 
            match stack_elem with
            | OperatorComponent((op, id)),_ -> (
              if id + 2 < List.length op.components then (
                match (List.nth op.components (id + 2)) with
                | Operator.CKeyword _ -> Some(op, id + 2)
                | _ -> None
              ) else None
            )
            | _ -> None
          ) s)
        )

    let get_next_possible_token (s : stack) :t_stack_op_component list = 
        match s with
        | [] -> get_all_start_component ()
        | (OperatorComponent(_), _) :: _ -> get_all_start_component ()
        | _ :: _ -> get_all_following_component s

    let match_token_on_input (input : t_charstream) (tok : t_stack_op_component)  : ((stack_elem * t_extent) * t_charstream) option = 
      match get_op_component tok with
      | Operator.CKeyword s -> (
        let start_rc = CharStream.CharStream.get_row_col input in
        match CharStream.CharStream.match_string input s with
        Some (input') -> (
          let end_rc = CharStream.CharStream.get_row_col input' in
          let ext = (CharStream.CharStream.get_file_path input, start_rc, end_rc) in
          Some ((OperatorComponent(tok), ext), input')
        )
        | None -> None)
      | _ -> failwith "Not implemented"

    let reduce_stack_top_with_op (stack : stack) (op : Operator.operator) : stack option = 
      let stack_tops = ListUtil.take (List.length op.components) stack in
      let args_and_extents = List.map2 (fun (stack_elem, ext) component -> 
        match stack_elem, component with
        | Expr e, Operator.CComponent _ -> Operator.PComponent e, ext
        | ArbitraryString s, Operator.CArbitraryContent _ -> Operator.PArbitraryContent s, ext
        | ArbitraryString s, Operator.CBinding _ -> Operator.PBinding s, ext
        | OperatorComponent _, Operator.CKeyword k -> Operator.PKeyword (Extent.str_with_extent k ext), ext
        | _ -> failwith ("110 Not matching! stack_elem " ^ show_stack_elem stack_elem ^ " component " ^ Operator.debug_print_component component
        ^ " stack " ^ show_stack stack ^ " op " ^ Operator.debug_print_operator op ^ " stack_top " ^ show_stack stack_tops)
      ) (List.rev stack_tops) op.components in
      let args = List.map fst args_and_extents in
      let arg_extent = (
        match (List.map snd args_and_extents) with 
        | [] -> failwith "Empty extent" 
        | h:: t  -> Extent.combine_extent h (List.nth t ((List.length t) - 1))
      ) in 
      try (
        match op.reductions args  with
        | None -> None
        | Some reduced_exprs -> 
          Some (List.rev (List.map (fun x -> Expr (mark_extent x arg_extent), arg_extent) reduced_exprs) @ ListUtil.drop (List.length op.components) stack )
      ) with Failure s -> (
        failwith (s ^ "\nFailed to reduce " ^  " with " ^ show_stack stack)
      )


    (* reduce current stack considering all operators, None indicates in consistencies due to individual operator's reductions *)
    let rec try_reduce_all_stack_with_applicable_ops (stack: stack) (all_reducible_operators : Operator.operator list) : stack option = 
      match stack with 
      | [] -> Some []
      (* | UnknownSymbol s :: stack' -> (
        let unknown_symbol_expr = OperatorsSet.unknown_symbol_reduction s in
        try_reduce_all_stack_with_applicable_ops (Expr unknown_symbol_expr :: stack') all_reducible_operators
      ) *)
      (* | Space :: stack' -> try_reduce_all_stack_with_applicable_ops stack' all_reducible_operators *)
      | (OperatorComponent ((op, idx) as sop), _) :: _ -> (
        match get_next_op_component sop with 
        | Some _  -> Some stack (* cannot reduce this, expecting more components *)
        | None -> (
              if idx + 1 = List.length op.components  && List.mem op all_reducible_operators then (
                Option.bind (reduce_stack_top_with_op stack op) (fun next_stack ->
                  try_reduce_all_stack_with_applicable_ops next_stack all_reducible_operators
                )
              ) else (
                (* cannot reduce this, expecting more components *)
                Some stack
              )

        )
      )
      | (Expr _, _) :: (OperatorComponent ((op, idx)), _) :: _ -> (
        if idx + 2 = List.length op.components && List.mem op all_reducible_operators then (
          Option.bind (reduce_stack_top_with_op stack op) (fun next_stack ->
            try_reduce_all_stack_with_applicable_ops next_stack all_reducible_operators
          )
        ) else (
          Some stack
        )
      )
      | (Expr e2, ext2) :: (Expr e1, ext1) :: stack' -> (
        let possibly_reduced_expr = OperatorsSet.consecutive_expr_reduction e1 e2 in
        let final_extent = Extent.combine_extent ext1 ext2 in
        if List.length possibly_reduced_expr = 1 then (
          try_reduce_all_stack_with_applicable_ops ((Expr (mark_extent (List.hd possibly_reduced_expr) final_extent), final_extent) :: stack') all_reducible_operators
        ) else (
          Some (List.rev (List.map (fun x -> Expr (mark_extent x final_extent), final_extent) possibly_reduced_expr) @ stack')
        )
      )
      | (Expr _, _) :: [] -> Some stack
      | _ -> failwith ("152 Not implemented : " ^ show_stack stack)

    (* let try_reduce_all_stack_with_tail_applications_only (stack: stack)  : stack = 
      match stack with 
        | Expr e2 :: Expr e1 :: stack' -> (
          let possibly_reduced_expr = OperatorsSet.consecutive_expr_reduction e1 e2 in
          if List.length possibly_reduced_expr = 1 then (
            (Expr (List.hd possibly_reduced_expr) :: stack')
          ) else (
            (List.rev (List.map (fun x -> Expr x) possibly_reduced_expr) @ stack')
          )
        )
        | _ -> stack *)

    let try_reduce_all_stack (stack : stack) : stack option = 
      let all_reducible_operators = OperatorsSet.all_operators () in
      try_reduce_all_stack_with_applicable_ops stack all_reducible_operators 

    let try_reduce_stackelem (stack : stack) ((elem, ext): stack_elem * t_extent)  : stack option = 
      (* let _ = print_endline ("Reducing " ^ show_stack_elem elem ^ " on " ^ show_stack stack) in *)
      (* reduce stack elem first then shift*)
      match elem with 
      | OperatorComponent ((op, idx) as sop) -> 
          (match get_prev_op_component sop with
          | Some (Operator.CBinding _) -> (
            failwith "Binding content must be followed by a keyword"
            )
          | Some (Operator.CArbitraryContent _) -> (
            failwith "Arbitrary content must be followed by a keyword"
          )
          | Some (Operator.CKeyword _) -> (
            failwith "You cannot have two consecutive keywords"
          )
          | Some (Operator.CComponent p) -> (
            let prev_reduced_stack = (
                match p with
                | Operator.Same -> try_reduce_all_stack_with_applicable_ops stack (OperatorsSet.all_operators_of_equal_or_higher_precedence op)
                | Operator.Higher -> try_reduce_all_stack_with_applicable_ops stack (OperatorsSet.all_operators_of_strictly_higher_precedence op)
                | Operator.Reset -> try_reduce_all_stack_with_applicable_ops stack (OperatorsSet.all_operators ())
            ) in 
            (* check prev 2 component *)
            (match get_prev_op_component (op, idx-1) with
            | None  -> (* no prev prev component, check stack *)
              (match prev_reduced_stack with 
                | Some (((Expr _, _)::_) as pvs ) -> Some ((OperatorComponent (op, idx), ext) :: pvs)
                | _ -> None

              )
            | Some (Operator.CKeyword _) -> (
              match prev_reduced_stack with
              | Some (((Expr _, _)::((OperatorComponent((pop, pidx))), _)::_) as pvs ) -> (
                if pop.id = op.id && pidx = idx - 2 then Some ((OperatorComponent ((op, idx)), ext) :: pvs)
                else None
              )
              | _ -> None
            )
            | _ -> failwith "Operators must be Ckeyword CComponent CKeyword"
            )
          )

          | None -> (* no prev component, this marks a new start, reduce all possible stack elems with higher precedence*)
            Option.bind (try_reduce_all_stack_with_applicable_ops stack (OperatorsSet.all_operators_of_strictly_higher_precedence op))
              (fun next_stack -> 
                Some ((elem, ext) :: next_stack)
              )
          )
      | UnknownSymbol s_current -> (
        let unknown_symbol_expr = OperatorsSet.unknown_symbol_reduction s_current in
        try_reduce_all_stack_with_applicable_ops ((Expr (mark_extent unknown_symbol_expr ext), ext) :: stack) []
      )
      
      | Space -> ( Some stack)
      | _ -> failwith "138 Not implemented"
      
           
    module CS = CharStream.CharStream
    let try_match_inputs (input : t_charstream) (stack : stack) : ((stack_elem * t_extent) * t_charstream) list = 
      let possible_next_tokens = get_next_possible_token stack in
      let possible_matches = List.filter_map (match_token_on_input input) possible_next_tokens in
      if List.length possible_matches > 0 
        then possible_matches
        else 
          let cur_rc = CS.get_row_col input in
          let next_token, input' = CS.get_next_token input in
          let next_rc = CS.get_row_col input' in
          let ext = (CS.get_file_path input', cur_rc, next_rc) in
          match next_token with
          | CS.EOF -> []
          | CS.Space _ -> [((Space, ext), input')]
          | CS.Identifier s -> [((UnknownSymbol s, ext), input')] 
          | CS.SpecialChar _ -> ([]
          (* This is due to the ending special char not picked up by previous application of the stack, there must be something wrong in the interpretation of stack elements*)
            (* failwith (
            CS.get_file_path input ^ ":" ^ (let (row, col) = CS.get_row_col input in string_of_int row ^ ":" ^ string_of_int col ^" : " ^
            "cannot have unknown special char symbol: " ^ s  
            )) *)
          )

    

    let rec shift_reduce (failure_signal: stack -> t_charstream -> unit) (stack : stack) (char_stream: t_charstream) : (t_expr list) list = 
      let _ = if Flags.show_parse_steps() then print_endline ( show_input char_stream ^ ":" ^ show_stack stack) else () in
      if CS.is_eof char_stream then (
        match try_reduce_all_stack stack with
        | None -> (
          failure_signal stack char_stream;
          []
        )
        | Some final_stack -> 
        (* let _ = print_endline( "Finished Parsing") in *)
        (* let _ = print_endline ( show_input char_stream ^ ":" ^ show_stack final_stack) in *)
        let expr_list = List.filter_map (fun elem -> match elem with | (Expr expr, _) -> Some expr | _ -> None) final_stack in
        if List.length expr_list <> List.length final_stack then (
          failure_signal stack char_stream;
          []
        )
        else [List.rev expr_list]
      ) else (
        let default_handle() = (
          let possible_matches = try_match_inputs char_stream stack in
          let next_stacks = (List.filter_map ( fun (elem, input') -> match try_reduce_stackelem stack elem with | Some stack' -> Some (stack', input') | None -> None)  possible_matches) in 
          if List.length next_stacks = 0 then (
            failure_signal stack char_stream;
            []
          )
          else if List.length next_stacks = 1 then (
            let (stack', input') = List.hd next_stacks in
            shift_reduce failure_signal stack' input'
          )
          else(
          List.concat_map (fun (stack', input') -> shift_reduce failure_signal stack' input') next_stacks
          (* failwith ("Ambiguous parse found ^ " ^ (String.concat "\n" (List.map (fun (stack', _input') -> show_stack stack') next_stacks))) *)
          )
        ) in
        (* check *)
        match stack with
        | (OperatorComponent (op, idx), _) :: _ -> (
            match get_next_op_component (op, idx) with 
            | None -> ( (* we are at the end, reduce the current stack*)
              match try_reduce_all_stack_with_applicable_ops stack [op] with
              | Some stack'' -> shift_reduce failure_signal stack'' char_stream
              | None -> (
                failure_signal stack char_stream;
                []
              )
              (* | None -> failwith ("254, elements on stack cannot receive reduction " ^ show_stack stack) *)
            )
            | Some (Operator.CArbitraryContent content_spec) -> (
              match get_next_op_component (op, idx+1) with
              | Some (Operator.CKeyword keyword)  -> (
                let start_rc = CS.get_row_col char_stream in
                match CS.scan_with_end_and_groups keyword content_spec.except_end_following content_spec.matching_pairs char_stream  with
                | Some (content, input') -> (
                  let end_rc = CS.get_row_col input' in
                  let ext = (CS.get_file_path char_stream, start_rc, end_rc) in
                  shift_reduce failure_signal ((OperatorComponent (op, idx+2), ext) :: (ArbitraryString content, ext) :: stack) input'
                )
                (* | None -> [] this cannot have a parse, need end pattern *)
                | None -> failwith "Arbitrary content must be followed by a keyword"
              )
              | _ -> failwith "Arbitrary content must be followed by a keyword"
            )
            | Some (Operator.CBinding _) -> (
              match get_next_op_component (op, idx+1) with
              | Some (Operator.CKeyword keyword)  -> (
                let start_rc = CS.get_row_col char_stream in
                match CS.scan_with_end_and_groups keyword [] [] char_stream  with
                | Some (content, input') -> (
                  let end_rc = CS.get_row_col input' in
                  let ext = (CS.get_file_path char_stream, start_rc, end_rc) in
                  shift_reduce failure_signal ((OperatorComponent (op, idx+2), ext) :: (ArbitraryString (String.trim content), ext) :: stack) input'
                )
                (* | None -> [] *)
                | None -> failwith "Binding content must be followed by a keyword"
              )
              | _ -> failwith "Binding content must be followed by a keyword"
            )
            | Some _ -> default_handle()
        )
        | _ -> default_handle()
      )

      

      



    let parse (s : t_charstream) : t_expr list =
      let last_failure = ref None in
      let failure_signal stack input = (
        match !last_failure with
        | None -> last_failure := Some (stack, input)
        | Some (_, cur_input) -> if 
            CharStream.CharStream.get_num_chars_read cur_input > CharStream.CharStream.get_num_chars_read input then
              () (* do nothing *)
            else last_failure := Some (stack, input)
      ) in
      match shift_reduce failure_signal [] s with
      | [] -> (match !last_failure with
        | Some (_stack, input) -> (
          let rc = CharStream.CharStream.get_row_col input in
          let ext = (CharStream.CharStream.get_file_path input, rc, rc) in
          let message = "No parse found\n" ^"Last failed stack: " ^ show_stack _stack  in
          Errors.raise_with_explicit_extent (Some ext) message
        )
        | None -> (
          Errors.raise_with_explicit_extent None "No parse found"
        )
      )
      | [expr] -> expr
      | options -> Errors.raise_with_explicit_extent None ("Ambiguous parse found\n" ^ String.concat "\n" (List.mapi (fun idx expr_l -> string_of_int idx ^ ": " ^ (String.concat ">>"  (List.map OperatorsSet.debug_show_expr expr_l))) options))



end

module CoLFParser = MixfixParser(OperatorsSet.CoLFOperator)(OperatorsSet.CoLFOperatorsSet)