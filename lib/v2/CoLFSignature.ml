module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode
module PrettyPrint = PrettyPrint.PrettyPrint
module Ctx = TypeCheckingCtx.TypeCheckingCtx

module type COLF_SIGNATURE = sig

  type dec = TypeDecl of string * A.t | ModeDecl of A.t | ConstantDef of string * A.t * A.t | SeparatorDecl
  type t = dec list

  val new_signature : A.t list -> t
  val show_signature : t -> string
  val debug_show_signature : t -> string
  val debug_show_signature_raw : t -> string
end

module CoLFSignature : COLF_SIGNATURE = struct
  type dec = TypeDecl of string * A.t | ModeDecl of A.t | ConstantDef of string * A.t * A.t | SeparatorDecl

  type t = dec list

  let new_signature (decls : A.t list) : dec list = 
    List.map (fun decl -> 
      match A.view decl with
      | A.N(N.TypeDecl(name), [([], tp)]) -> TypeDecl(name, tp)
      | A.N(N.CommandDecl("mode"), [([], tp)]) -> ModeDecl(tp)
      | A.N(N.CommandDecl("separator"), [([], _)]) -> SeparatorDecl
      | A.N(N.ConstantDef(name), [([], tp); ([], tm)]) -> ConstantDef(name, tp, tm)
      | _ -> failwith ("s16: Invalid declaration: " ^ (A.show_view decl))
    ) decls

  let generic_show(sig_ : dec list) (show_tm : A.t -> string) : string = 
    String.concat "\n" (List.map (fun dec -> 
      match dec with
      | TypeDecl(name, tp) -> name ^ " : " ^ show_tm tp ^ "."
      | ModeDecl(tp) -> "%mode " ^ show_tm tp ^ "."
      | SeparatorDecl -> "%separator."
      | ConstantDef(name, tp, tm) -> name ^ " : " ^ show_tm tp ^ " = " ^ (show_tm tm) ^ "."
    ) sig_)


  let show_signature (sig_ : dec list) : string =
    generic_show sig_ PrettyPrint.show_term

  let debug_show_signature (sig_ : dec list) : string =
    generic_show sig_ A.show_view

  let debug_show_signature_raw (sig_ : dec list) : string =
    generic_show sig_ A.show_raw


end