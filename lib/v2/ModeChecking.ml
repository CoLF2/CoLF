module A = CoLFAbt.CoLFAbt
module AOps = CoLFAbtOps.CoLFAbtOps
module PP = PrettyPrint.PrettyPrint
module N = CoLFAbt.CoLFNode
module Ctx = TypeCheckingCtx.TypeCheckingCtx
module Sig = CoLFSignature.CoLFSignature
module CoLFSignatureOps = CoLFSignature.CoLFSignatureOps
module Errors = Errors.Errors
module Ext = AbtLib.Extent

let collect_pis (tp : A.t) : string list * A.t = 
  let rec aux (acc : string list) (tp : A.t) : string list * A.t = 
    match A.view tp with
    | A.N(N.Pi, [[], _t2; [name], t1]) -> (
      if A.appears_in_expr name t1 
        then aux (name::acc) t1
        else (acc, tp)
    )
    | _ -> (acc, tp)
  in
  aux [] tp

let collect_premises (tp : A.t) : A.t list * A.t = 
  let rec aux (acc : A.t list) (tp : A.t) : A.t list * A.t = 
    match A.view tp with
    | A.N(N.Pi, [[], t2; [name], t1]) -> (
      if A.appears_in_expr name t1
        then Errors.raise_error t1 ("Name " ^ (name) ^ " appears in premise " ^ (A.show_view t1) ^ ".");
      aux (acc@[t2]) t1
    )
    | _ -> (acc, tp)
  in
  aux [] tp

type var_status = Unknown | Known 
let split_premise_according_to_mode (signature : Sig.t) (tp : A.t) : A.t list * A.t list = 
  match A.view tp with
  | A.N(N.Ap, (_, hd)::tl) -> (
    match A.view hd with
    | A.FreeVar(rel_name) -> (
      let mode_decl = CoLFSignatureOps.lookup_unique_mode_declaration rel_name signature in
      if List.length tl <> List.length mode_decl then failwith ("MC45: Unexpected number of premises, got " ^ (string_of_int (List.length tl)) ^ " and " ^ (string_of_int (List.length mode_decl)));
      List.partition_map (fun ((_, premise), mode) -> 
        match mode with
        | Sig.Input -> Either.Left premise
        | Sig.Output -> Either.Right premise
        ) (ListUtil.zip tl mode_decl)
    )
    | _ -> failwith ("MC43: Unexpected term, got " ^ (A.show_view tp))
  )
  | _ -> failwith ("MC44: Unexpected term, got " ^ (A.show_view tp))

let check_single_tp_top_level (signature : Sig.t) (tp : A.t) : unit =
  let pis, tp = collect_pis tp in
  let premises, tp = collect_premises tp in
  (* make sure the terminal term is an application*)
  match A.view tp with
  | A.N(N.CoType, []) -> ()
  | A.FreeVar(_) -> ()
  | A.N(N.Ap, (_, _hd)::_tl) -> (
    let input_premises, output_premises = split_premise_according_to_mode signature tp in
    let premises_partitioned = List.map (split_premise_according_to_mode signature) premises in
    let all_together = [[], input_premises] @ premises_partitioned @ [output_premises, []] in
    let status = ref (List.map (fun x -> (x, Unknown)) pis) in
    List.iter (fun (inputs, outputs) -> 
      (* check all variables (that are in the pis) in the input are known *)
      (* set all variables (that are in the pis) in the output to unknown *)
      List.iter (fun x -> 
        List.iter (fun fv -> 
            match ListUtil.find_elem_by_key !status fv with
            | Some Known -> ()
            | Some Unknown -> (Errors.raise_error x ("MC72: Variable " ^ fv ^ " is not yet known at this point in " ^ (A.show_view x)))
            | None -> ()
          ) (A.get_free_vars x)
        ) inputs;
        List.iter (fun x -> 
          List.iter (fun fv -> 
            match ListUtil.find_elem_by_key !status fv with
            | Some Unknown -> status := ListUtil.update_elem_by_key !status fv (Known)
            | _ -> ()
          ) (A.get_free_vars x)
        ) outputs
    ) all_together
  )
  | _ -> failwith ("E93: Unexpected terminal term, got " ^ (A.show_view tp))
let mode_check_signature (signature : Sig.t) : unit = 
  let rec aux  (remaining: Sig.t) : unit = 
    match remaining with
    | [] -> ()
    | Sig.TypeDecl(_name, tp):: tl -> 
      (
        check_single_tp_top_level signature tp;
        aux tl
      )
    | Sig.ModeDecl(_)::tl -> 
      aux tl
    | Sig.SeparatorDecl::tl -> 
      aux tl
    | Sig.ConstantDef(_, _, _)::tl -> 
      (
        aux tl
      )
    in 
  aux signature

