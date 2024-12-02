
module type OPERATORS_SET = sig
  type operator
  type t_expr

  val all_operators : unit -> operator list 
  val all_operators_of_equal_or_higher_precedence : operator -> operator list
  val all_operators_of_strictly_higher_precedence : operator -> operator list

  val check_precedence_strictly_less_than : operator -> operator -> bool


  val unknown_symbol_reduction : string -> t_expr
  val consecutive_expr_reduction : t_expr -> t_expr -> t_expr list (* given a, b, return [a,b] if no reduction is possible *)

  val annotate_with_extent : t_expr -> string * (int * int) * (int * int) -> t_expr
  val debug_show_expr : t_expr -> string
  


end

module Abt = CoLFAbt.CoLFAbt
module Node = CoLFAbt.CoLFNode
module CoLFOperator = Operators.CoLFOperator

module CoLFOperatorsSet : OPERATORS_SET 
  with type operator = CoLFOperator.operator 
  and type t_expr = Abt.t
  = struct
  type operator = CoLFOperator.operator
  type t_expr = Abt.t

  
  let all_colf_operators = CoLFParseOperators.CoLFParseOperators.all_colf_operators

  let loopup_precedence (target:  operator) : int = 
    match List.find_index (fun (opl : operator list) -> List.mem target opl) all_colf_operators with
    | Some i -> i
    | None -> failwith "Operator not found in all_operators"

  let all_operators () : operator list = 
    List.concat all_colf_operators
  
  let all_operators_of_equal_or_higher_precedence (target: operator) : operator list =
    let precedence = loopup_precedence target in
    (List.filter (fun candidate -> loopup_precedence candidate >= precedence) (all_operators()))
  
  let all_operators_of_strictly_higher_precedence (target: operator) : operator list =
    let precedence = loopup_precedence target in
    (List.filter (fun candidate -> loopup_precedence candidate > precedence) (all_operators()))
  
  let check_precedence_strictly_less_than (op1: operator) (op2: operator) : bool =
    loopup_precedence op1 < loopup_precedence op2
  
  let unknown_symbol_reduction (symbol: string) : t_expr =
    match symbol with
    | "type" -> Abt.fold (Abt.N(Node.Type, []))
    | "cotype" -> Abt.fold (Abt.N(Node.CoType, []))
    | _ -> Abt.fold (Abt.FreeVar symbol)

  let consecutive_expr_reduction (expr1: t_expr) (expr2: t_expr) : t_expr list =
    (* let _ = Printf.printf "consecutive_expr_reduction: %s, %s. i.e. %s, %s\n" (Abt.show_raw expr1) (Abt.show_raw expr2) (Abt.show_view expr1) (Abt.show_view expr2) in *)
    match Abt.view expr1 with
    | Abt.N(Node.Ap, args) -> [Abt.fold (Abt.N(Node.Ap, args@[([], expr2)]))]
    | Abt.N(Node.TypeDecl _, _) -> [expr1; expr2]
    | Abt.N(Node.CommandDecl _, _) -> [expr1; expr2]
    | Abt.N(Node.ConstantDef _, _) -> [expr1; expr2]
    | _ -> [Abt.fold (Abt.N(Node.Ap, [([], expr1); ([], expr2)]))]

  let annotate_with_extent (expr: t_expr) ext : t_expr =
    Abt.annotate_with_extent expr ext
    (* Abt.fold (Abt.N(Node.ExtentAnnotation(filename, start_pos, end_pos), [([], expr)])) *)


  let debug_show_expr (expr: t_expr) : string =
    Abt.show_view expr
end
