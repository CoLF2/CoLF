module type NODE_CLASS = AbtLib.NODE_CLASS
module Ext = AbtLib.Extent


module CoLPNode = struct
  type t = Pi of int * Ext.t_str list (* abstraction names *)
        | CoType
        | Arr 
        | DataTypeDef of Ext.t_str
        | DataClauseDef of Ext.t_str
        | ClauseSet of Ext.t_str list  (* plain applications, e.g. x, y, z *)
        | IOType of Ext.t_str list * Ext.t_str list (* nat , nat > nat*)
        | IOClause of Ext.t_str list * Ext.t_str * Ext.t_str list (* nat , nat > add > nat *)
        | RelationTypeDef of Ext.t_str
        | RelationClauseDef of Ext.t_str
end

module CoLFNodeImpl : NODE_CLASS with  type t = CoLPNode.t
  = struct
  type t = CoLPNode.t

  open CoLPNode
  let arity (n : t) : int list option = 
    match n with
    | Pi (i, _) ->  Some(ListUtil.repeat i 0)
    | CoType -> Some([])
    | Arr -> Some([0; 0])
    | DataTypeDef _ -> Some([])
    | DataClauseDef _ -> Some([])
    | ClauseSet _ -> Some([])
    | IOType (_, _) -> Some([])
    | IOClause (_, _, _) -> Some([])
    | RelationTypeDef _ -> Some([])
    | RelationClauseDef _ -> Some([])
  
  let show (n : t) : string =
    match n with
    | Pi (i, l) -> "Π(" ^ string_of_int i ^ ")(" ^ String.concat "," (List.map Ext.get_str_content l) ^ ")"
    | CoType -> "CoType"
    | Arr -> "Arr"
    | DataTypeDef s -> "DataTypeDef(" ^ Ext.get_str_content s ^ ")"
    | DataClauseDef s -> "DataClauseDef(" ^ Ext.get_str_content s ^ ")"
    | ClauseSet l -> "ClauseSet(" ^ String.concat "," (List.map Ext.get_str_content l) ^ ")"
    | IOType (l1, l2) -> "IOType(" ^ String.concat "," (List.map Ext.get_str_content l1) ^ " > " ^ String.concat "," (List.map Ext.get_str_content l2) ^ ")"
    | IOClause (l1, l2, l3) -> "IOClause(" ^ String.concat "," (List.map Ext.get_str_content l1) ^ " > " ^ Ext.get_str_content l2 ^ " > " ^ String.concat "," (List.map Ext.get_str_content l3) ^ ")"
    | RelationTypeDef s -> "RelationTypeDef(" ^ Ext.get_str_content s ^ ")"
    | RelationClauseDef s -> "RelationClauseDef(" ^ Ext.get_str_content s ^ ")"
end

module CoLFAbt = AbtLib.Abt(CoLFNodeImpl)
