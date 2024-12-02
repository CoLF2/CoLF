module A = CoLFAbt.CoLFAbt
module AOps = CoLFAbtOps.CoLFAbtOps
module PP = PrettyPrint.PrettyPrint
module N = CoLFAbt.CoLFNode
module Ctx = TypeCheckingCtx.TypeCheckingCtx
module Sig = CoLFSignature.CoLFSignature
module Errors = Errors.Errors

module type TYPE_CHECKING = sig
  val type_check_signature : Sig.t -> unit
end

module TypeChecking : TYPE_CHECKING = struct
            
let rec synth  (ctx : Ctx.t) (tm : A.t)  : A.t  = 
  let _ = if Flags.show_type_checking_steps() then print_endline ("[TCK] synth on " ^ PP.show_term tm ^ " in ctx " ^ Ctx.show_ctx_view_top ctx ) else () in 
  Errors.try_with_error ( fun _ -> 
    match A.view tm with
      | A.FreeVar(name) -> (
          match Ctx.find_type_decl ctx name with
          | Some(tp) -> tp
          | None -> Errors.raise_error tm ("Variable " ^ name ^ " not found in context " ^ Ctx.show_ctx_view ctx (Some PP.show_term))
        )
      | A.N(N.Type, []) -> 
          tm
      | A.N(N.CoType, []) -> 
          tm
      | A.N(N.Pi, [[], t2; [name], t1]) -> 
          let _ = check_type_or_cotype ctx t2 in
          let new_ctx = if A.appears_in_expr name t1 then Ctx.add_local_type_decl ctx name t2  else ctx in
          let tp = synth new_ctx t1 in
          tp
      | A.N(N.Ap, ([], hd)::spine) ->  
          (
            match A.view hd with
            | A.FreeVar(name) -> 
                (
                  match Ctx.find_type_decl ctx name with
                  | Some hd_tp ->  tr_feed_spine ctx (List.map snd spine) hd_tp 
                  | None -> Errors.raise_error hd ("Variable " ^ name ^ " not found in context " ^ Ctx.show_ctx_view ctx (Some PP.show_term))
                )
            | _ -> failwith ("synth: expecting a free variable as head of application, got " ^ PP.show_term hd)
          )
      | _ -> failwith ("synth: not implemented for " ^ PP.show_term tm) 
      ) (Some tm)  ("when synthesizing the type of " ^ PP.show_term tm ^ " in "  ^ Ctx.show_ctx_view_top ctx )


and check  (ctx : Ctx.t) (tm : A.t) (tp: A.t)  : unit = 
  (* let _ = if Flags.show_type_checking_steps() then print_endline ("[TCK] check on " ^ A.show_raw tm ^ " : " ^ A.show_raw tp ^ " in ctx " ^ Ctx.show_ctx_view_top ctx ) else () in *)
  (* let _ = if Flags.show_type_checking_steps() then print_endline ("[TCK] check on " ^ A.show_view tm ^ " : " ^ A.show_view tp ^ " in ctx " ^ Ctx.show_ctx_view_top ctx ) else () in *)
  let _ = if Flags.show_type_checking_steps() then print_endline ("[TCK] check on " ^ PP.show_term tm ^ " : " ^ PP.show_term tp ^ " in ctx " ^ Ctx.show_ctx_view_top ctx ) else () in
  Errors.try_with_error (fun _ -> 
    match A.view tm with
    | A.N(N.Lam, [[lam_name], arg]) -> 
      (
        match A.view tp with
        | A.N(N.Pi, [[], t2; [pi_name], t1]) -> 
            let t1' = if lam_name = pi_name then t1 else A.subst (A.free_var lam_name) pi_name t1 in
            let ctx' = Ctx.add_local_type_decl ctx lam_name t2 in
            check ctx' arg t1'
        | _ -> failwith "expecting pi type 63"
      )
    | _ ->
        let tp' = synth ctx tm in
        ( try Ctx.assert_eq_true ctx (tp, tp') 
        with  Failure s -> Errors.raise_error tm s)
  ) (Some tm) ("when checking " ^ PP.show_term tm ^ " : " ^ PP.show_term tp ^ " in "  ^ Ctx.show_ctx_view_top ctx)
      

and check_type_or_cotype (ctx : Ctx.t) (tm : A.t) : unit = 
  let tp = synth ctx tm in
  match A.view tp with
  | A.N(N.Type, []) -> ()
  | A.N(N.CoType, []) -> ()
  | _ -> Errors.raise_error tm ("expecting type or cotype, got " ^ PP.show_term tp)



          
(* corresponds to the judgment S \rhd A/K => A/K *)
(* assumes fed is well-typed *)
and tr_feed_spine (ctx : Ctx.t) (spine : A.t list) (fed : A.t )  :  A.t = 
  let _ = if Flags.show_type_checking_steps() then print_endline ("tr_feed_spine on " ^  PP.show_terms spine ^ " into " ^ PP.show_term fed ^ " in ctx " ^ Ctx.show_ctx_view_top ctx ) else () in 
  Errors.try_with_error
  ( fun _ -> 
      match spine with
      | []  -> fed
      | (m :: ms) -> (
              match A.view fed with
              | A.N(N.Pi, [[], t2; [bnd_name], t1]) -> (
                  let _ = check ctx m t2 in
                  let t1' = AOps.hereditary_subst m bnd_name t1 in
                  tr_feed_spine ctx ms t1'
              )
              | _ -> Errors.raise_error m "expecting pi type 63: The number of arguments (=spine) may be more than the number of Pi's in the type of head (=into) of the term "
      )
    ) None ("when feeding spine " ^ PP.show_terms spine ^ 
    " into  " ^ PP.show_term fed ^ " in "  ^ Ctx.show_ctx_view_top ctx)

let synth_top ctx tm = 
  Errors.try_with_error (fun _ -> synth ctx tm) (Some tm) ("when synthesizing the type of " ^ PP.show_term tm ^ " in "  ^ Ctx.show_ctx_view ctx (Some PP.show_term))

let check_top ctx tm tp =
  Errors.try_with_error (fun _ -> check ctx tm tp) (Some tm) ("when checking " ^ PP.show_term tm ^ " : " ^ PP.show_term tp ^ " in "  ^ Ctx.show_ctx_view ctx (Some PP.show_term))

let type_check_signature (signature : Sig.t) : unit = 
  let rec aux (ctx: Ctx.t) (remaining: Sig.t) : unit = 
    match remaining with
    | [] -> ()
    | Sig.TypeDecl(name, tp):: tl -> 
      let _ = (synth_top ctx tp)  in 
      let new_ctx = Ctx.add_global_type_decl ctx name tp in
      aux new_ctx tl
    | Sig.ModeDecl(_)::tl -> 
      aux ctx tl
    | Sig.SeparatorDecl::tl -> 
      aux ctx tl
    | Sig.ConstantDef(_, _, _)::_ -> 
      (* We want to check the tps of all consecutive contantDef (while keeping ctx the same), and 
      then their body under all tp assumptions, essentially making them mutually recursive *)
      (
        let rec aux_rec_def (sofar : Sig.t) (remaining : Sig.t) : unit = 
          match remaining with
          | (Sig.ConstantDef(_, tp, _) as h)::tl -> 
            let _ = if AOps.check_is_kind tp then Errors.raise_error tp "Rec defs cannot have ... -> (co)type type." else () in
            aux_rec_def (sofar @ [h]) tl
          | _ -> (
            let ctx' = List.fold_left (fun acc dec -> 
              match dec with 
              | (Sig.ConstantDef(name, tp, _)) -> (
                let _ = synth_top acc tp in ();
                try Ctx.add_global_type_decl acc name tp  with Failure s -> Errors.raise_error tp s
                )
              | _ -> failwith "expecting constant dec") ctx sofar in
            let to_add = List.map (fun dec -> match dec with 
              | (Sig.ConstantDef(name, tp, body)) -> 
                let _ = check_top ctx' body tp in
                (name, body)
              | _ -> failwith "expecting constant dec")  sofar in
            let final_ctx = Ctx.add_global_rec_defs ctx' to_add in
            aux final_ctx remaining
          )
        in 
        aux_rec_def [] remaining
      )
    in 
  aux (Ctx.empty_ctx()) signature

end
