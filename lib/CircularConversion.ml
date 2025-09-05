(* (* for converting a super-flattend recursive definition 
into a very unflattened version that are easier to understand for 
humans *)
module A = Ast
module Ctx = TypeCheckingContext 
module HS = HereditarySubstitution 


(* returns the id that can be eliminated *)
let rec can_eliminate_any_rec_def_in_ctx_except 
          (ctx : Ctx.ctxtype)
          (except : A.id list) : A.id option = 
    match ctx with
    | [] -> None
    | (Ctx.RecDef(name, _, tm) :: ct ) -> 
      if HS.occurs_in_tm name tm || List.mem name except
        then can_eliminate_any_rec_def_in_ctx_except ct except
      else Some(name)
    | _ :: ct -> can_eliminate_any_rec_def_in_ctx_except ct except
    
    

let eliminate_one_rec_def_in_ctx_except 
          (ctx : Ctx.ctxtype)
          (name : A.id) : Ctx.ctxtype = 
  match Ctx.lookup_id_in_ctx ctx name  with
  | (rtp, Ctx.IdRecConstantInCtx rtm) ->
    (
      let trans_tm m = HS.h_sub_in_tm rtm (A.to_weak rtp) name m in
      let trans_tp m = HS.h_sub_in_tp rtm (A.to_weak rtp) name m in
      let trans_ures ures = (match ures with
        | Ctx.Unresolved -> Ctx.Unresolved
        | Ctx.ResolvedTp tp -> Ctx.ResolvedTp (trans_tp tp)
        | Ctx.ResolvedTm (tm, tp) -> Ctx.ResolvedTm (trans_tm tm, trans_tp tp)
      ) in
      List.filter_map (fun ctxitem -> 
        match ctxitem with
        | Ctx.Aid(name, tp) -> Some(Ctx.Aid(name, trans_tp tp))
        | Ctx.FreeVar(name, tp) -> Some(Ctx.FreeVar(name, trans_tp tp))
        | Ctx.UniVar(name, utp, ures) -> Some(Ctx.UniVar(name, utp, trans_ures ures))
        | Ctx.UnifContraintTp _ -> failwith "cannot be called during unification"
        | Ctx.UnifContraintTm _ -> failwith "cannot be called during unification"
        | Ctx.RecDef(n, tp, tm) -> if n = name then
            None else Some(Ctx.RecDef(n, trans_tp tp, trans_tm tm))
        ) ctx
    )
  | _ -> failwith "cc47: not found"

(* unflatten all recursion definitions in context 
   except those in the argument list *)
let rec eliminate_all_rec_def_in_ctx_except 
          (ctx : Ctx.ctxtype)
          (except : A.id list) : Ctx.ctxtype = 
    let _ = Circular.assert_ctx_no_duplicates ctx "cc29" in
    match can_eliminate_any_rec_def_in_ctx_except ctx except with
      | Some(id) -> 
        (let ctx = eliminate_one_rec_def_in_ctx_except ctx id in
          eliminate_all_rec_def_in_ctx_except ctx except)
      | None -> ctx


(* TODO flatten tp more by changing e.g. r = c, h r into h c*)
let efficiently_represent_tms (ctx : Ctx.ctxtype) (tms : A.tm list) :  A.rec_sig  = 
try(
  let all_rec_vars = List.concat_map (Ctx.get_rec_constants_in_tm_ctx ctx) tms in
  let all_rec_vars = ListUtil.remove_duplicates all_rec_vars in
  let ctx = eliminate_all_rec_def_in_ctx_except ctx all_rec_vars in
  let _ = Circular.assert_ctx_no_duplicates ctx "cc6t: contains duplicate" in
  let all_reachable = Circular.collect_all_reachable_rec_constants_in_ctx ctx all_rec_vars [] in
  let _ = if ListUtil.contains_duplicate all_reachable then failwith "cc67: contains duplicate" else () in
  (all_reachable)
) with Failure s -> raise (Failure (s ^ "\n when efficiently representing terms")) *)