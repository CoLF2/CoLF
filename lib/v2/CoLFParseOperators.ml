module CoLFOperator = Operators.CoLFOperator
module Abt = CoLFAbt.CoLFAbt
module Node = CoLFAbt.CoLFNode
module Errors = Errors.Errors

module CoLFParseOperators = struct
  let id_ref = ref 0
  let next_id = fun () -> let id = !id_ref in id_ref := id + 1; id

  let get_command_op_for (command_name: string) : CoLFOperator.operator = 
    {
      id = next_id();
      components = [CoLFOperator.CKeyword ("%"^command_name); CoLFOperator.CComponent Higher; CKeyword "."];
      reductions = (fun arg -> 
        match arg with
        | [PKeyword _; PComponent body; PKeyword _] -> [Abt.fold (Abt.N(Node.CommandDecl(command_name), [([], body)]))]
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
          | [PComponent name_expr; PKeyword _; PComponent type_expr; PKeyword "."] -> 
            (
              match Abt.view name_expr with
              | Abt.FreeVar s -> [Abt.fold (Abt.N(Node.TypeDecl(s), [([], type_expr)]))]
              | _ -> (Errors.raise_error name_expr ("36 Invalid argument for declaration, got " ^ (Abt.show_view name_expr)))
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
              match Abt.view name_expr with
              | Abt.FreeVar s -> [Abt.fold (Abt.N(Node.ConstantDef(s), [([], type_expr); ([], definition)]))]
              | _ ->  (Errors.raise_error name_expr ("33 Invalid argument for declaration, got " ^ (Abt.show_view name_expr)))
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
          | [PComponent left; PKeyword _; PComponent right] -> [Abt.fold (Abt.N(Node.Pi, [([], left); Abt.unbind_abt_list (Abt.abstract_over_no_name right) 1]))]
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
            result
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
          | [PKeyword _; PBinding name; PKeyword _; PComponent body] -> [Abt.fold (Abt.N(Node.Lam, [([name], body)]))]
          | _ -> failwith "Invalid argument for lambda abstraction"
          )
      }

      ];
      (* Comments %%  *)
      [{id = next_id();
      components = [CoLFOperator.CKeyword "%%"; CoLFOperator.CArbitraryContent {except_end_following = ["\n"]; matching_pairs = []}; CoLFOperator.CKeyword "\n"];
      reductions = (fun _ -> [])
      }];
      (* Parenthesized Expressions (e) *)
      [{id = next_id();
      components = [CoLFOperator.CKeyword "("; CoLFOperator.CComponent Reset; CoLFOperator.CKeyword ")"];
      reductions = (fun arg -> 
        match arg with
        | [CoLFOperator.PKeyword _; CoLFOperator.PComponent body; CoLFOperator.PKeyword _] -> [body]
        | _ -> failwith "Invalid argument for parenthesized expression"
        )
      }];
    ]
end

(* This is to get the syntax highlighting right*)
module B =  struct
end
