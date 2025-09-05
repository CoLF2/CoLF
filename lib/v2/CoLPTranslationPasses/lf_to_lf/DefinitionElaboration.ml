
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
            (let tp = CoLFSignatureOps.lookup_unique_type_of_name name lf_sig in
            let rec aux idx tp = 
              match idx, A.view tp with
              | 0, A.N(N.Pi, [[], t2; [_], _]) -> t2
              | _, A.N(N.Pi, [[], _; [name], t1]) -> 
                if A.appears_in_expr name t1 then 
                  failwith ("LL48: assuming non-dependent typing, but " ^ name ^ " appears in the type of " ^ A.show_view t1)
                else
                  aux (idx - 1) t1
              | _ -> Errors.Errors.raise_error hd ("IA49: expecting a pi type, got " ^ A.show_view tp)
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
  


let rec operate_under_consecutive_bound_pis (tp: A.t) (f : A.t -> A.t) : A.t = 
  match A.view tp with
  | A.N(N.Pi, [[], t2; [pi_name], t1]) -> 
    if A.appears_in_expr pi_name t1 then 
      A.fold (A.N(N.Pi, [[], t2; [pi_name], operate_under_consecutive_bound_pis t1 f]))
    else
      f tp
  | _ -> f tp


let get_all_constant_names (lf_sig : CoLFSignature.t) : string list = 
  List.filter_map (fun dec -> 
    match dec with
    | Sig.ConstantDef(name, _, _) -> Some (Ext.get_str_content name)
    | _ -> None
  ) lf_sig

type finalization = {
  premises : A.t list;
  final_pi : A.t -> A.t;
}


let id_finalization : finalization = {
  premises = [];
  final_pi = (fun x -> x);
}

let chain_finalization (this : finalization) 
    (new_premise : A.t) 
    (final_pi : A.t -> A.t) : finalization = 
    {
      premises = this.premises@[new_premise];
      final_pi = (fun x -> final_pi (this.final_pi x));
    }

let run_finalization (finalization : finalization) (tp : A.t) : A.t = 
  finalization.final_pi (
    List.fold_right 
    (fun premise acc -> A.n(N.Pi, [[], premise; [Uid.next_name "__unnamed_abs_not_binding"], acc]))
    finalization.premises tp
  )


let rec replace_constant_with_capital (x : string) (x_tp : A.t) (tp : A.t) (finalization : finalization) : A.t * finalization = 
  match A.view tp with
  | A.FreeVar(y) -> (
    if y = x then
      let x_capital = Uid.next_name (StringUtil.capitalize_first_letter x) in
      A.free_var x_capital, chain_finalization finalization (
          A.n(N.Ap, [[], A.free_var x;
                          [], A.free_var x_capital
                         ])
      ) (
        fun tm -> 
          A.n(N.Pi, 
          [[], x_tp; [x_capital], tm]
          )
      )
    else
      A.free_var y, finalization
  )
  | A.N(N.Ap, ([], hd)::spine) -> 
    (
      match A.view hd with
      | A.FreeVar(y) -> 
        let (spine_new, finalization) = List.fold_left (fun (acc, finalization) (_, arg) -> 
            let (new_arg, finalization) = replace_constant_with_capital x x_tp arg finalization in
            acc@[([], new_arg)], finalization
          ) ([], finalization) spine in
        if y = x then
          (
            let x_capital = Uid.next_name (StringUtil.capitalize_first_letter x) in
            A.free_var x_capital, chain_finalization finalization (
                A.n(N.Ap, [[], A.free_var x]@spine_new@[[], A.free_var x_capital])
            ) (
              fun tm -> 
                A.n(N.Pi, 
                [[], x_tp; [x_capital], tm]
                )
            )
          )
        else
          (
            A.n(N.Ap, ([], hd)::(spine_new)), finalization
          )
      | _ -> failwith ("Expect ap to have a free variable as head, got " ^ A.show_view hd)
    )
  | A.N(N.Pi, [[], t1; [pi_name], t2]) -> 
    (
      if A.appears_in_expr pi_name t2 then
        failwith ("DE116: " ^ pi_name ^ " appears in the type of " ^ A.show_view t2 ^ " internal error likely");
      let t1_new, finalization = replace_constant_with_capital x x_tp t1 finalization in
      let t2_new, finalization = replace_constant_with_capital x x_tp t2 finalization in
      A.n(N.Pi, [[], t1_new; [pi_name], t2_new]), finalization
    )
  | _ -> failwith ("DE115: Not a free variable or an application, got " ^ A.show_view tp)
    
let elaborate_tm_tp (lf_sig : CoLFSignature.t) (tp : A.t) (finializing_transform : finalization)
  (before_finalization : A.t -> A.t) : A.t = 
  let all_constant_names = get_all_constant_names lf_sig in
  let lower_fvs = List.filter (fun x -> (is_str_starting_with_lowercase x)) (A.get_free_vars tp) in
  let relevant_const_names = ListUtil.remove_duplicates (List.filter (fun x -> List.mem x all_constant_names) lower_fvs) in
  let relevant_const_tps = List.map (fun x -> 
    let (tp, _) = CoLFSignatureOps.find_uniq_constant_def x lf_sig in
    let rec get_tp_output tp = 
      match A.view tp with
      | A.N(N.Pi, [[], _t1; [pi_name], t2]) -> 
        if A.appears_in_expr pi_name t2 then
          failwith ("DE117: " ^ pi_name ^ " appears in the type of " ^ A.show_view t2 ^ " internal error likely");
        get_tp_output t2
      | _ -> tp in
    get_tp_output tp
  ) relevant_const_names in
  let new_tp = operate_under_consecutive_bound_pis tp (fun tp -> 
    let defn_folded, finializing_transform = List.fold_right (fun (x, x_tp) (acc, finalization) -> 
      (* let x_capital = StringUtil.capitalize_first_letter x in
      let acc_subst = A.subst (A.free_var x_capital) x acc in
      A.fold(A.N(N.Pi, 
      [[], A.fold(A.N(N.Ap, [[], A.free_var x
                            ;[], A.free_var x_capital]))
      ; [Uid.next_name "__unnamed_abs_not_binding"], acc_subst])) *)
      replace_constant_with_capital x x_tp acc finalization
      ) (ListUtil.zip relevant_const_names relevant_const_tps) (tp, finializing_transform) in
    let transformed = run_finalization finializing_transform (before_finalization defn_folded) in
    (* let pi_folded = List.fold_right (fun x acc -> 
      let x_capital = StringUtil.capitalize_first_letter x in
      let (x_tp, _) = CoLFSignatureOps.find_uniq_constant_def x lf_sig in
      A.fold(A.N(N.Pi, [[], x_tp ; [x_capital], acc]))
      ) relevant_const_names transformed in *)
    transformed
    ) in
    new_tp


(* gets rid of all definitions and turn them into predicates*)
(*
        
  two : nat = M  
  -> 
  two : nat -> cotype.
  two/def : two M.

  y : {x : A} b two.
  -> 
  y : {x : A} {Two : nat} two Two -> b Two.

*)
let definition_elaboration (lf_sig : CoLFSignature.t) : CoLFSignature.t =
  let aux (dec: CoLFSignature.dec) : CoLFSignature.dec list = 
    (
      match dec with
      | Sig.TypeDecl(name, tp) -> 
        (
          assert_lower_case name;
          [Sig.TypeDecl(name, elaborate_tm_tp lf_sig tp id_finalization (fun tp -> tp))]
        )
      | Sig.ModeDecl(_) -> 
        [dec]
      | Sig.SeparatorDecl -> 
        [dec]
      | Sig.ConstantDef(name, tp, tm) -> 
        (
          let rec get_pi_abs (acc : (string * A.t) list) (tp : A.t) (tm : A.t) : 
            (string * A.t) list  * (A.t * A.t) = 
            match A.view tp, A.view tm with
            | A.N(N.Pi, [[], t1; [pi_name], t2]), A.N(N.Lam, [[lam_name], lam_body]) -> 
              (
                if A.appears_in_expr pi_name t2 then 
                  failwith ("LL145: " ^ pi_name ^ " appears in the type of " ^ A.show_view t2 
                ^ " Dependent typing is not supported yet");
                if not (A.appears_in_expr lam_name lam_body) then 
                  failwith ("LL146: " ^ lam_name ^ " does not appear in the body of the lambda " ^ A.show_view lam_body
                ^ " We require everything to be bound when having a definition.");
                get_pi_abs (acc @ [(lam_name, t1)]) t2 lam_body
              )
            | _, _ -> (acc, (tp, tm))
            in
          let (pi_names, (tp', tm')) = get_pi_abs [] tp tm in
          let all_constant_names = get_all_constant_names lf_sig in
          (* check that no constant name is used as a variable name *)
          (
            match List.find_opt (fun (x, _) -> List.mem x all_constant_names) pi_names with
              | Some (x, _) -> failwith ("LL147: " ^ x ^ " is a constant name, and cannot be used as a variable name.");
              | None -> ()
          );

          (* typing *)
          Sig.TypeDecl(name, 
          List.fold_right (fun (t) acc -> 
              A.n(N.Pi, [[], t; [Uid.next_name "__noname__"], acc])
             ) ((List.map snd pi_names)@[tp']) (A.n(N.CoType, []))
          )::
          (* mode *)
          Sig.ModeDecl(
            A.n(N.Ap, [[], A.free_var (Ext.get_str_content name)]@(ListUtil.repeat (List.length pi_names) ([], A.free_var "+"))@[[], A.free_var "-"])
          )::
          (* definition *)
          Sig.TypeDecl(
            Ext.str_with_extent (Ext.get_str_content name ^ "_def")  (Ext.get_str_extent name),
            elaborate_tm_tp lf_sig tm' {
              premises = [] ;
              final_pi = (fun tm -> 
                List.fold_right (fun (x, x_tp) acc -> 
                  A.n(N.Pi, [[], x_tp; [x], acc])
                ) pi_names tm
              );
            } (fun tp ->
                A.operate_on_view tp (function
                | A.N(N.Ap, _) | A.FreeVar _ -> A.N(N.Ap, [[], A.free_var (Ext.get_str_content name)]@(
                  List.map (fun (x, _) -> [], A.free_var x) pi_names
                )@[ [], tp]) (* TODO: Extent handling *)
                | _ -> failwith ("LL51: expecting a pi type, got " ^ A.show_view tp ^ " with " ^ A.show_view tm')
                ))
          )::
          []
        )
    )
    in 
  List.concat_map aux lf_sig
(* 
let lf_to_lf_top (lf_sig : CoLFSignature.t) : CoLFSignature.t = 
  implicit_argument_filling lf_sig *)