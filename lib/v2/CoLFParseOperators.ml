module CoLFOperator = Operators.CoLFOperator
module Abt = CoLFAbt.CoLFAbt
module Node = CoLFAbt.CoLFNode
module Errors = Errors.Errors
module Ext = AbtLib.Extent

module CoLFParseOperators = struct
  let id_ref = ref 0
  let next_id = fun () -> let id = !id_ref in id_ref := id + 1; id

  let view_expr_as_ext_str (expr: Abt.t) : Ext.t_str = 
    match Abt.view expr with
    | Abt.FreeVar s -> (
      match Abt.get_extent expr with
      | Some ext -> Ext.str_with_extent s ext
      | None -> failwith "po41: Extent not found"
    )
    | _ -> Errors.raise_error expr ("expecting a free variable, got " ^ (Abt.show_view expr))

  let get_command_op_for (command_name: string) : CoLFOperator.operator = 
    {
      id = next_id();
      components = [CoLFOperator.CKeyword ("%"^command_name); CoLFOperator.CComponent Higher; CKeyword "."];
      reductions = (fun arg -> 
        match arg with
        | [PKeyword ext_cmd_name; PComponent body; PKeyword _] -> 
            Some [Abt.fold (Abt.N(Node.CommandDecl(
              Ext.str_with_extent command_name (Ext.get_str_extent ext_cmd_name)
            ), [([], body)]))]
        | _ -> failwith "Invalid argument for command"
        )
    }

  (* higher precedence appears later*)
  let all_colf_operators : CoLFOperator.operator list list = 
    [
      [
      (* Declarations c : A.  and a : K. *)
      {
        id = next_id();
        components = [CComponent Higher; CKeyword ":"; CComponent Higher; CKeyword "."];
        reductions = (fun arg -> 
          match arg with
          | [PComponent name_expr; PKeyword _; PComponent type_expr; PKeyword _] -> 
            (
              Some [Abt.fold (Abt.N(Node.TypeDecl(view_expr_as_ext_str name_expr), [([], type_expr)]))]
            )
          | _ -> failwith "35 Invalid argument for declaration"
          )
      };
      (* Definitions c : A = M.  *)
      {
        id = next_id();
        components = [CComponent Higher; CKeyword ":"; CComponent Higher; CKeyword "="; CComponent Higher; CKeyword "."];
        reductions = (fun arg -> 
          match arg with
          | [PComponent name_expr; PKeyword _; PComponent type_expr; PKeyword _; PComponent definition; PKeyword _] -> 
            (
              Some [Abt.fold (Abt.N(Node.ConstantDef(view_expr_as_ext_str name_expr), [([], type_expr); ([], definition)]))]
            )
          | _ -> failwith "35 Invalid argument for declaration"
          )
      };
      (* Commands *)
      get_command_op_for "mode";
      get_command_op_for "separator";
      ];
      (* Arrow Types, Right Associative *)
      [{
        id = next_id();
        components = [CComponent Higher; CKeyword "->"; CComponent Same];
        reductions = (fun arg -> 
          match arg with
          | [PComponent left; PKeyword _; PComponent right] -> 
            Some [Abt.fold (Abt.N(Node.Pi, [([], left); Abt.unbind_abt_list (Abt.abstract_over_no_name right) 1]))]
          | _ -> failwith "Invalid argument for arrow type"
          )
      };
      (* Pi Types {x : A} B *)
      {
        id = next_id();
        components = [CKeyword "{"; CBinding 5; CKeyword ":"; CComponent Reset; CKeyword "}"; CComponent Same];
        reductions = (fun arg -> 
          match arg with
          | [PKeyword _; PBinding name; PKeyword _; PComponent type_expr; PKeyword _; PComponent body] -> 
            let result = [Abt.fold (Abt.N(Node.Pi, [([], type_expr); ([name], body)]))] in 
            (* let _ = print_endline (
              " type_expr " ^ (Abt.show_view type_expr) ^
              " type_expr_raw " ^ (Abt.show_raw type_expr) ^
              " body " ^ (Abt.show_view body) ^
              " body_raw " ^ (Abt.show_raw body) ^
              " result " ^ (Abt.show_view (List.hd result)) ^
              " result_raw " ^ (Abt.show_raw (List.hd result))
            ) in *)
            Some result
          | _ -> failwith "Invalid argument for pi type"
          )
      };
      ];
      (* Lambda abstractions [x] M *)
      [{
        id = next_id();
        components = [CKeyword "["; CBinding 3; CKeyword "]"; CComponent Same];
        reductions = (fun arg -> 
          match arg with
          | [PKeyword _; PBinding name; PKeyword _; PComponent body] -> 
            Some [Abt.fold (Abt.N(Node.Lam, [([name], body)]))]
          | _ -> failwith "Invalid argument for lambda abstraction"
          )
      }

      ];
      (* Comments %%  *)
      [{id = next_id();
      components = [CoLFOperator.CKeyword "%%"; CoLFOperator.CArbitraryContent {except_end_following = ["\n"]; matching_pairs = []}; CoLFOperator.CKeyword "\n"];
      reductions = (fun _ -> Some [])
      }];
      (* Parenthesized Expressions (e) *)
      [{id = next_id();
      components = [CoLFOperator.CKeyword "("; CoLFOperator.CComponent Reset; CoLFOperator.CKeyword ")"];
      reductions = (fun arg -> 
        match arg with
        | [CoLFOperator.PKeyword _; CoLFOperator.PComponent body; CoLFOperator.PKeyword _] -> Some [body]
        | _ -> failwith "Invalid argument for parenthesized expression"
        )
      }];
    ]
end

(* This is to get the syntax highlighting right*)
module B =  struct
end
