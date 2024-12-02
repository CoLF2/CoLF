
module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode
module PP = PrettyPrint.PrettyPrint

module CoLFAbtOps = struct


  let rec check_is_kind (tp : A.t) : bool = 
    match A.view tp with
    | A.N(N.Type, []) -> true
    | A.N(N.Pi, [([], _); ([_], t1)]) -> check_is_kind t1
    | _ -> false
  
  let rec hereditary_normalize (tm : A.t) : A.t = 
    (* let _ = print_endline ("hereditary_normalize: " ^ A.show_raw tm) in 
    let _ = print_endline ("hereditary_normalize[view]: " ^ A.show_view tm) in  *)
    match A.view tm with
    | A.FreeVar _ -> tm
    | A.N(N.Ap, ([], hd)::spine) -> (
      let hd' = hereditary_normalize hd in
      match A.view hd' with
      | A.N(N.Lam, [[name], body]) -> 
          (
            match spine with
            | [] -> hd'
            | ([], arg)::spine' ->
                (
                  let real_arg = hereditary_subst (hereditary_normalize arg) name body in
                  hereditary_normalize (A.fold (A.N(N.Ap, [([], real_arg)]@spine')))
                )
            | _ -> failwith ("hereditary_normalize: spine is not simple " ^ A.show_view tm)
          )
      | A.N(N.Ap, spine') ->  
        (
          hereditary_normalize (A.fold (A.N(N.Ap, (spine'@spine))))
        )
      | A.FreeVar _ -> (
        let spine' = List.map (fun arg -> (fst arg, hereditary_normalize (snd arg))) spine in
        A.fold (A.N(N.Ap, ([], hd')::spine'))
      )
      | _ -> failwith ("hereditary_normalize: head of application is not a lambda abstraction or application " ^ A.show_view tm)
    )
    | A.N(nt, args) -> (
      A.fold (A.N(nt, List.map (fun (ctx, tm) -> (ctx, hereditary_normalize tm)) args))
    )
    (* | _ -> failwith ("hereditary_normalize: not implemented for this term" ^ A.show_view tm) *)
  and hereditary_subst (tm_l : A.t) (x : string) (tm_r : A.t) : A.t = 
    (* let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst: [" ^ A.show_raw tm_l ^ "/" ^ x ^ "]" ^ A.show_raw tm_r) in *)
    (* let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst: [" ^ A.show_view tm_l ^ "/" ^ x ^ "]" ^ A.show_view tm_r) in *)
    let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst: [" ^ PP.show_term tm_l ^ "/" ^ x ^ "]" ^ PP.show_term tm_r) in
    let raw_subst_result = A.subst tm_l x tm_r in
    (* let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst(intermediate): [" ^ A.show_raw tm_l ^ "/" ^ x ^ "]" ^ A.show_raw tm_r ^ " = " ^ A.show_raw raw_subst_result) in *)
    (* let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst(intermediate): [" ^ A.show_view tm_l ^ "/" ^ x ^ "]" ^ A.show_view tm_r ^ " = " ^ A.show_view raw_subst_result) in *)
    let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst(intermediate): [" ^ PP.show_term tm_l ^ "/" ^ x ^ "]" ^ PP.show_term tm_r ^ " = " ^ PP.show_term raw_subst_result) in
    let result = hereditary_normalize raw_subst_result in 
    (* let result = (A.subst tm_l x tm_r) in  *)
    (* let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst: [" ^ A.show_raw tm_l ^ "/" ^ x ^ "]" ^ A.show_raw tm_r ^ " = " ^ A.show_raw result) in *)
    (* let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst: [" ^ A.show_view tm_l ^ "/" ^ x ^ "]" ^ A.show_view tm_r ^ " = " ^ A.show_view result) in *)
    let _ = if Flags.substitution_debug() then print_endline ("hereditary_subst: [" ^ PP.show_term tm_l ^ "/" ^ x ^ "]" ^ PP.show_term tm_r ^ " = " ^ PP.show_term result) in
    result

  let apply_spine_to_lambda (tm: A.t) (spine: A.t list) : A.t = 
    List.fold_left (fun tm arg -> 
      match A.view tm with
      | A.N(N.Lam, [[name], body]) -> hereditary_subst arg name body
      | A.N(N.Ap, hd::spine') -> A.fold (A.N(N.Ap, hd::(spine'@[[], arg])))
      | _ -> failwith ("apply_spine: head of spine is not a lambda abstraction or application " ^ A.show_view tm)
    ) tm spine

  let construct_iterative_lambda (abstracted: string list) (tm : A.t)  : A.t = 
    List.fold_right (fun name tm' -> A.fold (A.N(N.Lam, [[name], tm'])) ) abstracted tm

  let check_spine_is_simple (spine: A.t list) : bool = 
    List.for_all (fun tm -> 
      match A.view tm with
      | A.FreeVar _ -> true
      | A.N(N.Ap, [[], m]) -> (
        match A.view m with
        | A.FreeVar _ -> true
        | _ -> false
      )
      | _ -> false
    ) spine
end