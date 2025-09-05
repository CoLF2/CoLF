(* (* MEMO: 
How did we implement flattened definitions?

Essentially, flattened signatures are stored in the context, but 
unflattened ones are stored in a local signature
With every type check and unification, context is compared to local signatures 
to detect changes, 
   
*)

module A = Ast
module Ctx = TypeCheckingContext
module HS = HereditarySubstitution
let debug = Flags.circ_debug
(* checks whether [theta]a = b, or set [theta]a = b *)
let check_id_unifiability (theta: ((A.id * A.id) list) option) (a : A.id) (b : A.id)   : (A.id * A.id ) list option = 
match theta with
  | None -> None
  | Some theta ->
    (match List.find_opt (fun (c,_) -> c = a) theta with
      | None -> Some( (a,b) :: theta)
      | Some(_, d) -> if b = d then Some(theta) else None
    )

let rec list_mem_modulo (((h1, s1), (h2, s2)) as arg : (A.id * A.id list) * (A.id * A.id list)) (assump : Ctx.assump): bool = 
  match assump with
  | [] -> false
  | (((h1', s1'), (h2', s2')) :: t) -> 
      if h1' = h1 && h2 = h2' 
        && List.length s1' = List.length s1 && List.length s2' = List.length s2 
      (* length checking is necessary as we may query directly whether r1 = r2 without supplying arguments*)
      then (let theta = List.fold_left2 (fun theta a b -> 
        check_id_unifiability theta a b 
      ) (Some([])) s1' s1 in
      let theta = List.fold_left2 check_id_unifiability theta s2' s2 in
      match theta with
      | Some _ -> true
      | None -> list_mem_modulo arg t
      )
      else list_mem_modulo arg t
      

let rec is_equal_in_ctx  (ctx : Ctx.ctxtype) (assump : Ctx.assump) (m1 : A.tm) (m2 : A.tm)  : bool = 
    let _ = if debug then print_endline ("checking " ^ A.ds_tm m1 ^ " = " ^ A.ds_tm m2 ^ " with " ^ Ctx.ds_assump assump ^ Ctx.ds_conditional_show_ctx ctx)  else () in
    let res = 
      (
        match (m1, m2) with
          | (A.Lam(x1, b1), A.Lam(x2, b2)) -> 
            (let ((x1, b1, b2)) = UnifyUtil.unify_bnd_tm_tm (x1, b1) (x2, b2) in 
            let (_, b) = Ctx.with_new_name ctx x1 A.placeholder_tp (fun ctx -> 
                (ctx, is_equal_in_ctx ctx assump b1 b2)
              ) in
              b
            )
          | (A.Atm(h1, s1), A.Atm(h2, s2)) -> 
            (* WARNING: this code is copied from the unif for types, maybe we can combine them some day? *)
            (* NO! this has more patterns*)
              (match (h1, h2) with
                | (A.Prvd n1, A.Prvd n2)  -> 
                  (* Rigid - Circular/ Rigid - Rigid / Circular - Circular patterns *)
                  let (tpcls1, tpcls2) =(Ctx.find_id_in_ctx ctx h1 , Ctx.find_id_in_ctx ctx h2 ) in
                  (match  (tpcls1, tpcls2) with
                  (* circular - circular case *)
                  | (Some (_, Ctx.IdRecConstantInCtx tm1), Some(_, Ctx.IdRecConstantInCtx tm2)) -> 
                    let s1' = Validity.check_spine_is_weak s1 in
                    let s2' = Validity.check_spine_is_weak s2 in
                    let tm1 = HS.rename_feed_spine_tm s1'  tm1  in
                    let tm2 = HS.rename_feed_spine_tm s1' tm2  in
                    if list_mem_modulo ((h1, s1'), (h2, s2')) assump
                      then true
                      else is_equal_in_ctx ctx (((h1, s1'), (h2, s2')) :: assump) tm1 tm2
                  | (Some(_, Ctx.IdRecConstantInCtx tm), ( _)) ->  
                      (* expand circular side *)
                    let s1' = Validity.check_spine_is_weak s1 in
                      let expanded = HS.rename_feed_spine_tm s1' tm  in
                        is_equal_in_ctx ctx assump expanded m2 
                  (* circular - rigid case *)
                  | ((_), Some(_, Ctx.IdRecConstantInCtx _)) -> is_equal_in_ctx ctx assump m2 m1 
                  (* rigid - rigid case *)
                  | _ ->
                  if n1 = n2 
                    then ( List.for_all2 (fun m1 m2 -> is_equal_in_ctx ctx assump m1 m2 ) s1 s2)
                    else failwith "circular equality failure: distinct head tm"
                  )
              | _ -> failwith "circ59: cannot contain gen or placeholder when checking equality\n Please check if you have placeholder variables inside recursive defintions\n TODO: we should check if there are unsolved unification variables after type check the body of a recursive definition"
              )
          | _ -> false
      ) in 
    let _ = if debug then print_endline ("checking " ^ A.ds_tm m1 ^ " = " ^ A.ds_tm m2 ^ " with " ^ Ctx.ds_assump assump ^ " result is " ^ string_of_bool res)  else () in
    res


    (* asserts that context does not contain duplicate recursion definitions*)
let assert_ctx_no_duplicates (ctx : Ctx.ctxtype) (errmsg : string) : unit = 
  let _ = if ListUtil.contains_duplicate (Ctx.collect_all_rec_constants ctx) then 
    failwith errmsg else () in
  ()

  

(* 
find the subset of rs that denotes differently in g2 than g1
the commmon set of recursion constants of g1 and g2 must be rs, i.e.
rs must be all and the only recursion constants that are common to both g1 and g2
   *)
   (* because definitions are flattened, provided list is not used, returned list 
      is not a proper subset of provided list*)
let definition_changed_for_rec_consts (rs : A.id list) (g1 : Ctx.ctxtype) (g2 : Ctx.ctxtype) : A.id list = 
  try(
    let _ = assert_ctx_no_duplicates g1 "g1 contains duplicates" in
    let _ = assert_ctx_no_duplicates g2 "g2 contains duplicates" in
    let g1rs = Ctx.collect_all_rec_constants g1 in
    let g2rs = Ctx.collect_all_rec_constants g1 in
    let common_rs = ListUtil.intersect g1rs g2rs in
    (* let _ = if ListUtil.equal_as_sets common_rs rs then () 
            else failwith "definition_same must check sets that are common to both signatures" in *)
            (* because definitions are now flattened, provided name may be insufficient as they may refer to other definitions*)
    let _ = if ListUtil.is_sublist rs common_rs then () 
            else failwith "provided list not common to both" in
    let (g1', common_new_name_g1') = Ctx.rename_rec_consts_to_fresh_names g1 common_rs in
    let combined_g = g1' @ g2 in
    let _ = assert_ctx_no_duplicates combined_g 
    (
    let _ = Ctx.ds_reset_ctx_printing() in
    let g1ctx = Ctx.ds_ctxtype g1    in
    let _ = Ctx.ds_reset_ctx_printing() in
    let g1'ctx = Ctx.ds_ctxtype g1'    in
    let _ = Ctx.ds_reset_ctx_printing() in
    let g2ctx = Ctx.ds_ctxtype g2    in
    let _ = Ctx.ds_reset_ctx_printing() in
    let combinectx = Ctx.ds_ctxtype combined_g in
      "renaming failed, g1 and g2 still contains duplicates, check your implementation"
    ^ "\n g1 is " ^ g1ctx
    ^ "\n g1' is " ^ g1'ctx
    ^ "\n g2 is " ^ g2ctx
    ^ "\n f(g1);g2 is " ^ combinectx
    ) in
    let res = 
      (* filter from common names those differnt in g1 and g2 *)
      List.filteri (fun i g2name -> 
        let g1name = List.nth common_new_name_g1' i in
        not (is_equal_in_ctx combined_g [] (A.Atm(g1name, [])) (A.Atm(g2name, [])))
        )  common_rs in 
    res
  ) with Failure s -> 
    (
    let _ = Ctx.ds_reset_ctx_printing() in
    let g1ctx = Ctx.ds_ctxtype g1    in
    let _ = Ctx.ds_reset_ctx_printing() in
    let g2ctx = Ctx.ds_ctxtype g2    in
    let _ = Ctx.ds_reset_ctx_printing() in
      raise (Failure (s ^ "\n when checking whether definitions for "
      ^ String.concat ", " (List.map A.ds_id rs) ^ " changed for "
      
      ^
      (if Flags.show_ctx then 
       "\n g1 = " ^ g1ctx ^ "\n g2 = " ^ g2ctx else "")
      ))
    )
  


  (* transforms the input term into a recursion constant,  hereditarily flattening,
    with new definitions stored in the context 

    ** Does not modify existing stuff in the context **

    *)
(* recursion constants are determined if they can be found in the current context, 
   i.e. requires all recursion constants to be in the context not the signature *)
let rec transform_into_recursive (ctx : Ctx.ctxtype) (tm : A.tm) (tp : A.tp) (lg : A.lgsig) : (Ctx.ctxtype * A.tm) = 
  let _ = if debug then print_endline ("transform_into_recursive transforming into recursive on " ^ A.ds_tm tm ^ " : " ^ A.ds_tp tp ^ Ctx.ds_conditional_show_ctx ctx) else () in
  try(
    match (tm, tp) with
    | (A.Lam(mx, mb), A.Pi(tx, t2, t1)) -> (
        let (x, mb, t1) = UnifyUtil.unify_bnd_tm_tp (mx, mb) (tx, t1) in
        let (ctx, mb) = Ctx.with_new_name ctx x t2 (fun ctx -> 
            transform_into_recursive ctx mb t1 lg
          )
        in (ctx, A.Lam(x, mb))
      )
    | (A.Atm(h, _), A.Atp(_)) -> (
        match Ctx.lookup_id_in_ctx_and_sig ctx true h lg with
        | (_, (Ctx.IdRecConstantInCtx _ | Ctx.IdRecConstantInSig _ 
          | Ctx.IdUniVar(Ctx.UTmVarRec _))) -> (ctx,tm)
        | _ -> (* not recursion constants *)
          (
            let newR = A.Prvd (Uid.nextr()) in
            let bound_free_vars =  Ctx.get_bound_free_vars_in_tm ctx tm lg in
            let _ = if debug then print_endline ("bound_free_vars is " ^ A.ds_ids bound_free_vars) else () in
            let (ctx, body) = transform_into_contractive ctx tm tp lg in
            let (rtm, rtp) = Ctx.abstract_over_tm_tp ctx bound_free_vars (body, tp) lg in
            let ctx = (Ctx.RecDef(newR, rtp, rtm) :: ctx) in
            (* TODO do we need to eta-expand the arguments? *)
            let final_tm = (A.Atm(newR, List.map(fun v -> A.Atm(v, [])) bound_free_vars))  in
            (ctx, final_tm)
          )
    )
    | _ -> failwith "circ167: type term mismatch"
  ) with Failure s  -> 
      raise (Failure (s ^ "\n when transforming into recursive on " ^ A.ds_tm tm ^ " : " ^ A.ds_tp tp ^ Ctx.ds_conditional_show_ctx ctx))

  (* transforms the input term into a recursion constant,  hereditarily flattening,
    with new definitions stored in the context 

    ** Does not modify existing stuff in the context **

    *)
and transform_into_contractive (ctx : Ctx.ctxtype) (tm : A.tm)  (tp : A.tp) (lg : A.lgsig) : (Ctx.ctxtype * A.tm) = 
  let _ = if debug then print_endline ("transform_into_contractive transforming into contractive on " ^ A.ds_tm tm ^ " : " ^ A.ds_tp tp ^ Ctx.ds_conditional_show_ctx ctx) else () in
  try(
    match (tm, tp) with
      | (A.Lam(mx, mb), A.Pi(tx, t2, t1)) -> (
          let (x, mb, t1) = UnifyUtil.unify_bnd_tm_tp (mx, mb) (tx, t1) in
          let (ctx, mb) = Ctx.with_new_name ctx x t2 (fun ctx -> 
              transform_into_recursive ctx mb t1 lg
            )
          in (ctx, A.Lam(x, mb))
        )
      | (A.Atm(h, s), A.Atp(_)) -> (
          match Ctx.lookup_id_in_ctx_and_sig ctx true h lg with
          | (_, (Ctx.IdRecConstantInCtx _ | Ctx.IdRecConstantInSig _ 
            | Ctx.IdUniVar(Ctx.UTmVarRec _))) -> failwith "cannot transform a recursion constant into contractive"
          | (tp, _) -> (* not recursion constants *)
            (
              let (ctx, s, _) = List.fold_left (fun (ctx, sofar, nextTp) next -> 
                match nextTp with
                | A.Pi(x, t2, t1) -> 
                  let (ctx, tm) = transform_into_recursive ctx next t2 lg in
                  let nextTp = HS.h_sub_in_tp tm (A.to_weak t2) x t1 in
                  (ctx, sofar@[tm], nextTp)
                | _ -> failwith "circ189: type mismatch"
                ) (ctx, [], tp) s in
              (ctx, A.Atm(h, s))
            )
      )          
    | _ -> failwith "circ194: type term mismatch"
  ) with Failure s  -> 
      raise (Failure (s ^ "\n when transforming into contractive on " ^ A.ds_tm tm ^ " : " ^ A.ds_tp tp ^ Ctx.ds_conditional_show_ctx ctx))



(* invoke with to_collect = empty*)
let rec collect_all_reachable_rec_constants_in_ctx (ctx : Ctx.ctxtype)
  (to_collect : A.id list) (collected : (A.id * A.tp * A.tm) list) : (A.id * A.tp * A.tm) list = 
  (* collected is a sublist of to_collect *)
  match to_collect with
    | [] -> collected
    | (A.Prvd x :: xs) -> (
      match Ctx.find_id_in_ctx ctx (A.Prvd x) with
        | Some (xtp, Ctx.IdRecConstantInCtx(xtm)) -> 
            (* finds the rechable ids that have not yet been collected*)
            let newids = Ctx.get_rec_constants_in_tm_ctx ctx xtm  in
            (* let newids = List.map (fun v -> A.Prvd(v)) newids in *)
            let collected_ids = List.map (fun (id, _, _) -> id) collected in
            let not_collected = ListUtil.minus newids collected_ids in
            let to_collect_diff = ListUtil.minus not_collected to_collect in
            let new_to_collect = to_collect_diff @ xs in
            collect_all_reachable_rec_constants_in_ctx ctx new_to_collect ((A.Prvd x, xtp, xtm) :: collected) 
        | _ -> failwith "trying to collect non-rec constants"
      )
    | _ -> failwith "Collecting Non Prvd names" *)
