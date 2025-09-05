
module Ext = AbtLib.Extent

module type OPERATOR = sig

  type t_expr
  type precedence = Same | Higher | Reset
  type component = CKeyword of string 
                 | CBinding of int (* the absolute index which this binding occurs*)
                 | CComponent of precedence 
                 (* used for string or comments *)
                 | CArbitraryContent of {
                      (* endBy: string; (* end by should be the same as next keyword *)  *)
                      except_end_following:  string list; (* except that the end by is followed by any char in this list*) 
                      matching_pairs :  (string * string) list; (* matching pairs to skip*)
                 }

  type parsed_elem = 
    | PKeyword of Ext.t_str
    | PBinding of string
    | PComponent of t_expr
    | PArbitraryContent of string 

  type operator = {
    id : int;
    components : component list;
    reductions : parsed_elem list -> t_expr list option; (* can drop comments, none indicates no reduction*)
  }

  val debug_print_component: component -> string
  val debug_print_operator: operator -> string


end

module CoLFOperator : OPERATOR with type t_expr = CoLFAbt.CoLFAbt.t = struct
  type t_expr = CoLFAbt.CoLFAbt.t
  type precedence = Same | Higher | Reset
  type component = CKeyword of string 
                 | CBinding of int (* the absolute index which this binding occurs*)
                 | CComponent of precedence 
                 (* used for string or comments *)
                 | CArbitraryContent of {
                      (* endBy: string; (* end by should be the same as next keyword *)  *)
                      except_end_following:  string list; (* except that the end by is followed by any char in this list*) 
                      matching_pairs :  (string * string) list; (* matching pairs to skip*)
                 }

  type parsed_elem = 
    | PKeyword of Ext.t_str
    | PBinding of string
    | PComponent of t_expr
    | PArbitraryContent of string 

  type operator = {
    id : int;
    components : component list;
    reductions : parsed_elem list -> t_expr list option; (* can drop comments *)
  } 

  let debug_print_component (c: component) : string = 
    match c with
    | CKeyword s -> if s = "\n" then "\\n" else s
    | CBinding _ -> "?"
    | CComponent _ -> "_"
    | CArbitraryContent _ -> "<content>"

  let debug_print_operator (op: operator) : string =
    let components_str = List.map debug_print_component op.components in
    (String.concat "" components_str)


end
