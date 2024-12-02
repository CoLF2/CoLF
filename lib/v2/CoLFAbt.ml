module type NODE_CLASS = AbtLib.NODE_CLASS


module CoLFNode = struct
  type t = Pi 
        | Lam 
        | Ap 
        | Type
        | CoType
        (* | ExtentAnnotation of string * (int * int) * (int * int)  *)
        | TypeDecl of string 
        | ConstantDef of string 
        | CommandDecl of string
end

module CoLFNodeImpl : NODE_CLASS with  type t = CoLFNode.t
  = struct
  type t = CoLFNode.t

  open CoLFNode
  let arity (n : t) : int list option = 
    match n with
    | Pi -> Some([0; 1])
    | Lam -> Some([1])
    | Ap -> None
    | Type -> Some([])
    | CoType -> Some([])
    (* | ExtentAnnotation _ -> Some([0]) *)
    | TypeDecl _ -> Some([0])
    | CommandDecl _ -> Some([0])
    | ConstantDef _ -> Some([0; 0])
  
  let show (n : t) : string =
    match n with
    | Pi -> "Π"
    | Lam -> "λ"
    | Ap -> "ap"
    | Type -> "Type"
    | CoType -> "CoType"
    (* | ExtentAnnotation _ -> "™" *)
    | TypeDecl s -> "TypeDecl(" ^ s ^ ")"
    | CommandDecl s -> "CommandDecl(" ^ s ^ ")"
    | ConstantDef s -> "ConstantDef(" ^ s ^ ")"
end

module CoLFAbt = AbtLib.Abt(CoLFNodeImpl)
