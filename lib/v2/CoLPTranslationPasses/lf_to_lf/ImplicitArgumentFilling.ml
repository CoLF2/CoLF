
module CoLFSignatureOps = CoLFSignature.CoLFSignatureOps
module CoLFSignature = CoLFSignature.CoLFSignature
module Sig = CoLFSignature
module Ext = AbtLib.Extent
module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode

open StringUtil

let assert_lower_case (s : Ext.t_str) : unit =
  let s_content = Ext.get_str_content s in
  if not (is_str_starting_with_lowercase s_content) then
    failwith ("Name " ^ s_content ^ " is not lower case.")

let is_all_FV_lower_case (s : A.t ) : bool =
  let fvs = A.get_free_vars s in
  List.for_all is_str_starting_with_lowercase fvs


let rec get_type_of_free_var (lf_sig : CoLFSignature.t) (mname : string) (tp : A.t) : A.t = 
  match A.view tp with
  | A.FreeVar(_) -> failwith ("LL21: Cannot determine the type of " ^ mname) 
  | A.N(N.Ap , ([], hd)::spine) -> 
    (

    match (List.find_index (fun arg -> 
      match A.view (snd arg) with
      | A.FreeVar(name) -> name = mname
      | _ -> false
      ) spine) with
    | None -> (
      (* recurse into spine *)
      match List.find_opt (fun arg -> 
        List.mem (mname) (A.get_free_vars (snd arg))
      ) spine with
      | None -> failwith ("LL21: Cannot determine the type of " ^ mname)
      | Some arg ->  get_type_of_free_var lf_sig mname (snd arg)
    )
    | Some idx ->
      (
        match A.view hd with
        | A.FreeVar name -> 
            (let tp = (match CoLFSignatureOps.find_unique_type_of_name name lf_sig with
                       | Some tp -> tp
                       | None -> 
                         Errors.Errors.raise_error (hd) ("LL21: Cannot determine the type of " ^ mname )
            ) in
            let rec aux idx tp = 
              match idx, A.view tp with
              | 0, A.N(N.Pi, [[], t2; [_], _]) -> t2
              | _, A.N(N.Pi, [[], _; [name], t1]) -> 
                if A.appears_in_expr name t1 then 
                  failwith ("LL48: assuming non-dependent typing, but " ^ name ^ " appears in the type of " ^ A.show_view t1)
                else
                  aux (idx - 1) t1
              | _ -> Errors.Errors.raise_error hd ("IA549: expecting a pi type, got " ^ A.show_view tp)
            in
            aux idx tp
            )
        | _ -> failwith ("LL50: expecting a free variable as head of application, got " ^ A.show_view hd)
      )
    )
  | A.N(N.Pi, [[], t2; [pi_name], t1]) -> 
    (
    (assert (pi_name <> mname));
    if A.appears_in_expr mname t2 then 
      get_type_of_free_var lf_sig mname t2
    else
      get_type_of_free_var lf_sig mname t1
    )
  | _ ->  failwith ("LL24: Tp ill-formed " ^ A.show_view tp)
  


    



let implicit_argument_filling (lf_sig : CoLFSignature.t) : CoLFSignature.t =
  let aux (dec: CoLFSignature.dec) : CoLFSignature.dec = 
    (
    match dec with
    | Sig.TypeDecl(name, tp) -> 
      assert_lower_case name;
      let upper_fvs = List.filter (fun x -> not (is_str_starting_with_lowercase x)) (A.get_free_vars tp) in
      let upper_fvs_tps = List.map (fun x -> get_type_of_free_var lf_sig x tp) upper_fvs in
      let new_tp = List.fold_right2 (fun x tp acc -> 
        A.fold(A.N(N.Pi, [[], tp; [x], acc]))
        ) upper_fvs upper_fvs_tps tp in
      Sig.TypeDecl(name, new_tp)
    | Sig.ModeDecl(_) -> 
      dec
    | Sig.SeparatorDecl -> 
      dec
    | Sig.ConstantDef(name, tp, tm) -> 
      assert_lower_case name;
      if not (is_all_FV_lower_case tp) then
        failwith ("Type of the constant " ^ (Ext.get_str_content name) ^ " has free variables that are Upper Case (which is not allowed as upper case is reserved for implicit metavars).");
      if not (is_all_FV_lower_case tm) then
        Errors.Errors.raise_error (tm) ("Body of the constant " ^ (Ext.get_str_content name) ^ " has free variables that are Upper Case (which is not allowed as upper case is reserved for implicit metavars).");
      dec
    )
    in 
  List.map aux lf_sig
(* 
let lf_to_lf_top (lf_sig : CoLFSignature.t) : CoLFSignature.t = 
  implicit_argument_filling lf_sig *)