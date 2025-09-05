let show_ctx_flag = Flags.show_ctx

let debug = Flags.tcc_debug


module A = Ast
module HS = HereditarySubstitution

type ctx = (string * A.abt) list

let ds_ctx (ctx: ctx) : string = 
  "{" ^ String.concat ",\n" (List.map (fun (n, abt) -> n ^ " : " ^ A.ds_abt abt) ctx) ^ "}"

let ds_conditional_show_ctx (ctx : ctx) : string = 
  if show_ctx_flag 
    then " \tin context " ^ ds_ctx ctx
    else ""


let rec find_id_sig_local  (lookupid : string) ((local): (string * A.abt) list) : (A.abt) option = 
  match local with
  | ((ca, tp):: lt) -> 
        if ca = lookupid then Some(tp) else find_id_sig_local lookupid (lt)
  | [] -> None

let rec find_id_in_ctx (ctx : ctx) (lookupid : string) : (A.abt ) option = 
      match ctx with
      | [] -> None
      | ((id, tp):: t) -> if id = lookupid then Some (tp) else find_id_in_ctx t lookupid

(* Looks up free variables and bound variables, does not lookup unification variables nor weak variables *)
let find_id_in_ctx_and_sig (ctx : ctx) (name : string)(lg : A.decls) : (A.abt ) option = 
      (match find_id_in_ctx ctx name with
        | Some v -> Some v
        | None -> find_id_sig_local name lg 
      )


let  lookup_id_in_ctx_and_sig (ctx : ctx) (name : string)(lg : A.decls) : (A.abt ) = 
  match find_id_in_ctx_and_sig ctx name lg  with
  | Some t -> t
  | None -> failwith ("tcc85: lookup not found" ^ "\n when looking up " ^  name ^ " in context " ^ ds_conditional_show_ctx ctx)

(* checks whether the string begins with an upper case letter *)
let str_is_upper (s : string) = 
  let firstLetter = String.sub s 0 1 in
  String.uppercase_ascii firstLetter = firstLetter


let ctx_extend_with_binding(ctx : ctx) (tp : A.abt) (bnd : A.abt) : ctx * string * A.abt = 
  match bnd with
  | A.Bnd(_) -> 
      let (bnd_name, body) = A.unbind_expr ~avoid_list:(List.map (fun (n, _) -> n) ctx) bnd in
      let new_ctx = (bnd_name, tp) :: ctx in
      (new_ctx, bnd_name, body)
  | _ -> failwith "tcc56: ctx_extend_with_binding: expected a binding"


let ctx_from_pi_types (pi_tp : A.abt) : ctx * A.abt = 
  let rec aux (pi_tp : A.abt) (ctx : ctx) : ctx * A.abt = 
    match pi_tp with
    | A.N(A.Pi, [tp; bnd]) -> 
        let (ctx, _bnd_name, body) = ctx_extend_with_binding ctx tp bnd in
        aux body ctx
    | _ -> (ctx, pi_tp)
  in
  aux pi_tp []


let pi_type_from_ctx (ctx : ctx) (tp : A.abt) : A.abt = 
  List.fold_right (fun (n, tp) bnd -> A.N(A.Pi, [tp; A.abstract_over n bnd])) ctx tp

let lam_tm_from_ctx (ctx : ctx) (tm : A.abt) : A.abt = 
  List.fold_right (fun (n, tp) bnd -> A.N(A.Lam, [tp; A.abstract_over n bnd])) ctx tm

type unif_ctx = OkCtx of (A.abt * A.abt) list | UnifFailed


let empty_unif_ctx : unif_ctx = OkCtx []

let unif_ctx_is_ok (uc : unif_ctx) : bool = 
  match uc with
  | OkCtx _ -> true
  | UnifFailed -> false



let ds_unif_ctx (uc : unif_ctx) : string = 
  match uc with
  | OkCtx l -> "{" ^ String.concat ",\n" (List.map (fun (a, b) -> A.ds_abt a ^ " = " ^ A.ds_abt b) l) ^ "}"
  | UnifFailed -> "{UnifFailed}"