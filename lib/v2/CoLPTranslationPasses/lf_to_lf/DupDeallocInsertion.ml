
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
              | _ -> failwith ("LL49: expecting a pi type, got " ^ A.show_view tp)
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
  


    



let dup_dealloc_insertion (lf_sig : CoLFSignature.t) : CoLFSignature.t =
  let aux (dec: CoLFSignature.dec) : CoLFSignature.dec list = 
    (
    match dec with
    | Sig.TypeDecl(name, tp) -> 
      (

      let tp_name = Ext.get_str_content name in
      match A.view tp with
      | A.N(N.CoType, []) -> (
        dec ::
        (Sig.TypeDecl(Ext.str_with_extent (tp_name ^ "_dup") (Ext.get_str_extent name), 
          A.n(N.Pi, [[], A.free_var(tp_name); 
            [Uid.next_name "__res"],
              A.n(N.Pi, [
                ([], A.free_var tp_name);
                ([Uid.next_name "__res1"], 
                  A.n(N.Pi, [
                    ([], A.free_var tp_name);
                    ([Uid.next_name "__res2"], 
                      A.n(N.CoType, [])
                    )
                    ]
                  ))
                ]
              )
          ])
        ))
        ::
        (Sig.TypeDecl(Ext.str_with_extent (tp_name ^ "_dealloc") (Ext.get_str_extent name), 
          A.n(N.Pi, [[], A.free_var(tp_name); 
            [Uid.next_name "__res"], A.n(N.CoType, [])]
          )
        ))
        :: 
        (Sig.TypeDecl(Ext.str_with_extent (tp_name ^ "_dup_def") (Ext.get_str_extent name), 
          A.n(N.Ap, [[], A.free_var(tp_name ^ "_dup");
          [], A.free_var (capitalize_first_letter tp_name);
          [], A.free_var (capitalize_first_letter tp_name);
          [], A.free_var (capitalize_first_letter tp_name);
          ])
        ))
        :: 
        (Sig.TypeDecl(Ext.str_with_extent (tp_name ^ "_dealloc_def") (Ext.get_str_extent name), 
          A.n(N.Ap, [[], A.free_var(tp_name ^ "_dealloc");
          [], A.free_var (capitalize_first_letter tp_name);
          ])
        ))
        :: 
        (Sig.ModeDecl(
          A.n(N.Ap, [[], A.free_var(tp_name ^ "_dup");
          [], A.free_var ("+");
          [], A.free_var ("-");
          [], A.free_var ("-");
          ])
        ))
        :: 
        (Sig.ModeDecl(
          A.n(N.Ap, [[], A.free_var(tp_name ^ "_dealloc");
          [], A.free_var ("+");
          ])
        ))
        ::
        []
      )
      | _ -> [dec]
      )
    | Sig.ModeDecl(_) -> 
      [dec]
    | Sig.SeparatorDecl -> 
      [dec]
    | Sig.ConstantDef(_) -> 
      [dec]
    )
    in 
  List.concat_map aux lf_sig
(* 
let lf_to_lf_top (lf_sig : CoLFSignature.t) : CoLFSignature.t = 
  implicit_argument_filling lf_sig *)