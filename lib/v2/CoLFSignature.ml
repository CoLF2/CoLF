module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode
module PrettyPrint = PrettyPrint.PrettyPrint
module Ctx = TypeCheckingCtx.TypeCheckingCtx
module Ext = AbtLib.Extent

module type COLF_SIGNATURE = sig

  type dec = TypeDecl of Ext.t_str * A.t | ModeDecl of A.t | ConstantDef of Ext.t_str * A.t * A.t | SeparatorDecl
  type t = dec list
  type mode = Input | Output

  val new_signature : A.t list -> t
  val show_signature : t -> string
  val debug_show_signature : t -> string
  val debug_show_signature_raw : t -> string
end

module CoLFSignature : COLF_SIGNATURE = struct
  type dec = TypeDecl of Ext.t_str * A.t | ModeDecl of A.t | ConstantDef of Ext.t_str * A.t * A.t | SeparatorDecl

  type t = dec list

  type mode = Input | Output

  let new_signature (decls : A.t list) : dec list = 
    List.map (fun decl -> 
      match A.view decl with
      | A.N(N.TypeDecl(name), [([], tp)]) -> TypeDecl(name, tp)
      | A.N(N.CommandDecl(cmd_name), args) -> (
        match Ext.get_str_content cmd_name, args with
        | "mode", [([], tp)] -> ModeDecl(tp)
        | "separator", [([], _)] -> SeparatorDecl
        | _ -> failwith ("E34: Invalid declaration: " ^ (A.show_view decl))
      )
      | A.N(N.ConstantDef(name), [([], tp); ([], tm)]) -> ConstantDef(name, tp, tm)
      | _ -> failwith ("E37: Invalid declaration: " ^ (A.show_view decl))
    ) decls

  let generic_show(sig_ : dec list) (show_tm : A.t -> string) : string = 
    String.concat "\n" (List.map (fun dec -> 
      match dec with
      | TypeDecl(name, tp) -> Ext.get_str_content name ^ " : " ^ show_tm tp ^ "."
      | ModeDecl(tp) -> "%mode " ^ show_tm tp ^ "."
      | SeparatorDecl -> "%separator."
      | ConstantDef(name, tp, tm) -> Ext.get_str_content name ^ " : " ^ show_tm tp ^ " = " ^ (show_tm tm) ^ "."
    ) sig_)


  let show_signature (sig_ : dec list) : string =
    generic_show sig_ PrettyPrint.show_term

  let debug_show_signature (sig_ : dec list) : string =
    generic_show sig_ A.show_view

  let debug_show_signature_raw (sig_ : dec list) : string =
    generic_show sig_ A.show_raw


end

module CoLFSignatureOps = struct

  type mode = CoLFSignature.mode

  let show_mode (m : mode) : string = 
    match m with
    | CoLFSignature.Input -> "+"
    | CoLFSignature.Output -> "-"

  let find_unique_mode_declaration (name : string) (t : CoLFSignature.t) : mode list option = 
    let candidates = List.filter_map (fun dec -> 
      match dec with
      | CoLFSignature.ModeDecl(x) -> (
        match A.view x with
        | A.N(N.Ap, ([], hd)::tl) -> (
          match A.view hd with
          | A.FreeVar(y) -> 
              if y = name
              then Some (
                List.map (fun (_, mt) -> 
                  match A.view mt with
                  | A.FreeVar(s) -> (
                    if String.starts_with ~prefix:"+" s
                      then CoLFSignature.Input
                  else if String.starts_with ~prefix:"-" s
                    then CoLFSignature.Output
                  else Errors.Errors.raise_error mt ("E93: Invalid mode declaration " ^ A.show_view x)
                  )
                  | _ -> failwith ("E94: Invalid mode declaration " ^ A.show_view x)
                ) tl
              )
              else None
          | _ -> failwith ("E874: Invalid mode declaration" ^ A.show_view x)
          )
        | _ -> failwith ("E94: Invalid mode declaration" ^ A.show_view x)
      )
      | _ -> None
    ) t in
    match candidates with
    | [] -> None
    | [decl] -> 
      Some ( decl)
    | _ -> failwith ("E234: Multiple mode declarations found for " ^ name ^ ": " ^ (String.concat ", " (List.map (fun x -> String.concat "" (List.map show_mode x)) candidates))) 

  let lookup_unique_mode_declaration (name : string) (t : CoLFSignature.t) : mode list = 
    match find_unique_mode_declaration name t with
    | Some decl -> decl
    | None -> failwith ("E91: No mode declaration found for " ^ name)

  let find_unique_type_of_name (name : string) (t : CoLFSignature.t) : A.t option = 
    let candidates = List.filter_map (fun dec -> 
      match dec with
      | CoLFSignature.TypeDecl(name', x) -> 
        if Ext.get_str_content name' = name
        then Some x
        else None
      | _ -> None
    ) t in
    match candidates with
    | [] -> None
    | [tp] -> (Some tp)
    | _ -> failwith ("E234: Multiple type declarations found for " ^ name ^ ": " ^ (String.concat ", " (List.map (fun x -> A.show_view x) candidates))) 

  let lookup_unique_type_of_name (name : string) (t : CoLFSignature.t) : A.t =  
    match find_unique_type_of_name name t with
    | Some tp -> tp
    | None -> failwith ("E91: No type declaration found for " ^ name)

  let find_uniq_constant_def (name : string) (t : CoLFSignature.t) : A.t * A.t = 
    let candidates = List.filter_map (fun dec -> 
      match dec with
      | CoLFSignature.ConstantDef(name', tp, x) -> 
        if Ext.get_str_content name' = name
        then Some (tp, x)
        else None
      | _ -> None
    ) t in
    match candidates with
    | [] -> failwith ("E91: No constant definition found for " ^ name)
    | [tp] -> (tp)
    | _ -> failwith ("E234: Multiple constant definitions found for " ^ name ^ ": " ^ (String.concat ", " (List.map (fun (x, y) -> A.show_view x ^ A.show_view y) candidates)))

end