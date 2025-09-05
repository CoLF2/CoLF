
module A = Ast
module Ctx = TypeCheckingContext
module HS = HereditarySubstitution
let debug = Flags.unif_debug

(* 

type unif_final_ctx = UnifDone of Ctx.ctxtype


(* supposedly return the list of ordered bindings by eta-contracting*)
let check_spine_is_pattern (ctx : Ctx.ctxtype) (spine : A.tm list) (lg : A.lgsig) :  A.id list = 
  try (
  let arglist = 
  ( List.map (fun m ->  match HS.hered_eta_contract m with
  | A.Atm(A.Prvd h, []) -> (
      (* make sure it is not a constant *)
      match Ctx.lookup_id_weaktp ctx (A.Prvd h) lg with
        | (_, (Ctx.IdBound | Ctx.IdFreeVar)) -> A.Prvd h 
        | _ -> failwith "spine is not in the pattern fragment (unif51), because at least one term is a constant or free variables, all free variables must be explicitly bound by a Pi"
    )
  | _ -> failwith "spine is not in the pattern fragment (unif51), because some terms are unification variables or complex"
  ) spine) in
  if ListUtil.contains_duplicate arglist 
    then failwith "unif63: pattern has duplicate" 
    else 
      arglist
  ) with Failure s -> raise (Failure (s ^ "\n when checking that spine " ^ A.ds_spine spine ^ " is a pattern "))
  





let rec find_common_pattern (position_wise: bool) (s1 : A.id list) (s2 : A.id list) (ctx : Ctx.ctxtype) (lg : A.lgsig) : A.id list = 
  if position_wise
  then
    (match (s1, s2) with
    | ([], []) -> ([])
    | ((h1:: t1), (h2 :: t2)) -> 
          let tail = find_common_pattern true t1 t2 ctx lg in
          (* TODO: check free variables, they may also unify, e.g. u F = u x can be unified with u = \x. u F *)
              if h1 = h2 then h1 :: tail else tail
    | _ -> failwith "same argument with different argument list length"
    )
  else 
    ( List.filter (fun x -> List.mem x s2) s1
      (* let (common, s1extra) = List.partition (fun x -> List.mem x s2) s1 in
      let (common2, s2extra) = List.partition (fun x -> List.mem x s1) s2 in
      let  _ = if common <> common2 then failwith "error unif83" else () in
      (* find in s1extra and s2extra all free variables*)
      let freevars = List.filter (fun x -> 
          let (_, cls) = Ctx.lookup_id_in_ctx_and_sig ctx x lg in
          match cls with
          | IdFreeVar -> true
          | _ -> false
        ) (s1extra@List.filter (fun x -> not (List.mem x s1extra))s2extra (* remove duplicates *))
      in common @freevars *)
    )







(* the actual content of A.tp is always ignored, only the pi structure is tracked *)
let rec unify_tm (ctx : Ctx.ctxtype) (m1 : A.tm) (m2 : A.tm) (index : A.tp) (assump : Ctx.assump) (lg : A.lgsig) : unif_final_ctx  = 
let _ = if debug then print_endline("unify_tm unifying terms " ^ A.ds_tm m1 ^ " and " ^ A.ds_tm m2 ^ " at index " ^ A.ds_tp index  ^ Ctx.ds_conditional_show_ctx ctx) else () in
try(
      match (m1, m2, index) with
      | (A.Lam(x1, b1), A.Lam(x2, b2), A.Pi(tx, t2, t1)) -> 
        (let ((x1, b1, b2)) = UnifyUtil.unify_bnd_tm_tm (x1, b1) (x2, b2) in 
        let t1 = HS.rename_in_tp x1 tx t1 in
        let (ctx, ()) = Ctx.with_new_name ctx x1 t2 (fun ctx -> 
            (* this is a hack how we handle new names *)
            let UnifDone ctx = unify_tm ctx b1 b2 t1 assump lg in
            (ctx, ())
          )
        in process_unifications ctx lg
        )
      | (A.Atm(h1, s1), A.Atm(h2, s2), (A.Atp _ )) -> 
        (* WARNING: this code is copied from the unif for types, maybe we can combine them some day? *)
        (* NO! this has more patterns*)
          (match (h1, h2) with
              (* Rigid - Circular/ Rigid - Rigid / Circular - Circular patterns *)
            | (A.Prvd n1, A.Prvd n2)  -> 
              let ((tp1, cls1), (tp2, cls2)) =(Ctx.lookup_id_in_ctx_and_sig ctx true h1 lg, Ctx.lookup_id_in_ctx_and_sig ctx true h2 lg) in
              (match  (cls1, cls2) with
              | ((Ctx.IdRecConstantInSig _), _) -> failwith ("expecting rec const to be in ctx during unification, rec const is " ^ n1)
              | (_, (Ctx.IdRecConstantInSig _)) -> failwith ("expecting rec const to be in ctx during unification, rec const is " ^ n2)
              (* circular - circular case *)
              | ((Ctx.IdRecConstantInCtx tm1), (Ctx.IdRecConstantInCtx tm2)) -> 
                let s1' = Validity.check_spine_is_weak s1 in
                let s2' = Validity.check_spine_is_weak s2 in
                let tm1 = HS.h_sub_feed_spine s1  tm1 (A.to_weak tp1) in
                let tm2 = HS.h_sub_feed_spine s1  tm2 (A.to_weak tp2) in
                if Circular.list_mem_modulo ((h1, s1'), (h2, s2')) assump
                  then process_unifications ctx lg (* successful *)
                  else (let ctx = (Ctx.add_unification_equations_tm ctx [(tm1, tm2, index, ((h1, s1'), (h2, s2')) :: assump)]) in
                    process_unifications  ctx lg
                    )
                (* failwith "ni r-r pair" *)
              (* rigid - circular case *)
              | ((Ctx.IdRecConstantInCtx tm), ( _)) ->  
                  (* expand circular side *)
                  let expanded = HS.h_sub_feed_spine s1 tm (A.to_weak tp1) in
                    unify_tm ctx expanded m2 index assump lg
              (* circular - rigid case *)
              | ((_), (Ctx.IdRecConstantInCtx _)) -> unify_tm ctx m2 m1 index assump lg
              (* rigid - rigid case *)
              | _ ->
              if n1 = n2 
                then (
                  let (wtp, _) = (Ctx.lookup_id_in_ctx_and_sig ctx true h1 lg) in
                   unify_spine ctx s1 s2 wtp assump lg
                        )
                else failwith "unif failure: distinct head tm"
              )
            (* Flexible - Rigid / Flexible - Circular Patterns*)
            | (A.Gen n1, A.Prvd _) -> 
              let ( s1') = check_spine_is_pattern ctx s1 lg  in
              (* let (_, _) = Ctx.lookup_id_in_ctx_and_sig ctx true h2 lg in  *)
              let (tp2, t2cls) = Ctx.lookup_id_in_ctx_and_sig ctx true h2 lg in 
              (match t2cls with
                | IdRecConstantInSig _ -> failwith "expect rec constant to be in context not signature during unification, check the implementation of when body of recursion definitions are checked"
                (* flexible - circular case*)
                | IdRecConstantInCtx _ -> 
                      (let s2' = check_spine_is_pattern ctx s2 lg in
                        if ListUtil.is_sublist s2' s1'
                          then 
                            let resolution_body = ( A.Atm(h2,s2)) in  (* s2 is eta-expanded, so we're fine *)
                            let resolution = Ctx.abstract_over_tm_tp ctx s1' (resolution_body, index (* or tp2 *)) lg in
                            let ctx = Ctx.resolve_metavar ctx n1 (Ctx.ResolvedTm resolution) in
                            process_unifications ctx lg (* the resolution is compelete *)
                            (* unify_tm ctx resolution_body m2 index assump lg *)
                      else 
                        ( print_endline "WARINING: unification has encoutered a case that has not been implemented. Case: Flexible - Circular Case with Pruning"
                          ;failwith "unif126: the case of truncating recursion constants (flexible-circular case)")
                      )
                | _ -> (
                (* flexible - rigid case*)
                  let h1avoidList = Ctx.get_avoid_list ctx h1 in
                  if HS.occurs_in_tm h1 m2
                    then 
                      (
                        (* TODO: replace this code segment with turn_rec_univar_into_contra_univar, 
                           there are some implementation difference as primarily types of univar can be read 
                           from context instead of from argument index
                           *)
                        let newR = A.Prvd( Uid.nextr()) in
                        let (ctx, newUnivar) = Ctx.new_metavar_tm_contrac ctx (Ctx.abstract_over_tp ctx s1' index lg) (newR :: h1avoidList)  in
                        let newRBody = A.Atm(A.Gen newUnivar, s1) in
                        let (rdef, rtp) = Ctx.abstract_over_tm_tp ctx s1' (newRBody, index) lg in
                        let ctx = Ctx.RecDef(newR, rtp, rdef) :: ctx in
                        let resolution = Ctx.abstract_over_tm_tp ctx s1' (A.Atm(newR, s1), index) lg in
                        let ctx = Ctx.resolve_metavar ctx n1 (Ctx.ResolvedTm resolution) in
                        let m2 = Ctx.instantiate_metavar_tm ctx m2 in
                          unify_tm ctx newRBody m2 index assump lg
                      )
                  else 
                    (* TODO: determine imitation OR projection *)
                    let _check = (match t2cls with
                    | IdConstant 0 -> ()
                    | IdFreeVar  -> ()
                    | IdConstant _ -> ()
                    (* | IdConstant i -> failwith ("unif124 : ni constants with " ^ string_of_int i ^ " implicit arguemnts") *)
                    | (IdBound ) -> if List.mem h2 s1' then () else failwith "unif125: The bound variable does not occur in pattern"
                    | IdUniVar _ -> failwith "unif126: should not be the case, check lookup_id_in_ctx_and_sig implementation, specifically only Gen should match univar, but t2 now is Prvd"
                    | Ctx.IdRecConstantInSig _ | Ctx.IdRecConstantInCtx _ -> failwith "not possible (see previous match)"
                    ) in
                    let h2isConstant = (match t2cls with
                    | IdConstant _ ->true
                    |_ -> false
                    ) in
                    let newavoidList = if h2isConstant then  
                            (match Validity.classify_tp tp2 (match lg with | (l,g) -> l@g) with
                            | Validity.Inductive _ -> h1avoidList
                            | Validity.Coinductive _ -> []
                          ) else h1avoidList in
                    let (ctx, unifVars ) = Ctx.new_metavars_tm ctx tp2 s2 s1' newavoidList lg in
                    let resolution_body =
                      ( A.Atm(h2, List.map
                              (fun v -> A.Atm(A.Gen v, List.map (fun m -> A.Atm(m, [])) s1')) unifVars))  in
                    let resolution = Ctx.abstract_over_tm_tp ctx s1' (resolution_body, index) lg in
                    let ctx = Ctx.resolve_metavar ctx n1 (Ctx.ResolvedTm resolution) in
                    unify_tm ctx resolution_body m2 index assump lg
              ))
            (*  Rigid - Flexible /  Circular - Flexible Patterns*)
            | (A.Prvd _, A.Gen _) -> unify_tm ctx m2 m1 index assump lg
            (*  Flexible - Flexible  Patterns*)
            | (A.Gen n1, A.Gen n2) -> 
                let (h1_tp, _) = Ctx.lookup_id_in_ctx_and_sig ctx true  h1 lg in
                let target_tp = HS.h_sub_feed_spine_tp s1 h1_tp in
                let ( s1) = check_spine_is_pattern ctx s1 lg in 
                let ( s2) = check_spine_is_pattern ctx s2 lg in
                let common = find_common_pattern (n1 = n2)  s1 s2 ctx lg in
                let metavar_tp = Ctx.abstract_over_tp ctx common target_tp lg in
                let newavoidlist = ListUtil.union (Ctx.get_avoid_list ctx h1) (Ctx.get_avoid_list ctx h2) in
                let (ctx, newuvar) = Ctx.new_metavar_tm ctx metavar_tp newavoidlist in (* TODO: use metavar_tm_with_abstractions*)
                let resolution_body = A.Atm(A.Gen newuvar, List.map(fun id -> A.Atm(id, [])) common) in
                let r1 = Ctx.abstract_over_tm_tp ctx s1 (resolution_body, index) lg in
                let r2 = Ctx.abstract_over_tm_tp ctx s2 (resolution_body, index) lg in
                let ctx = if n1 = n2 then Ctx.resolve_metavar ctx n1 (Ctx.ResolvedTm r1)
            else Ctx.resolve_metavar (Ctx.resolve_metavar ctx n1 (Ctx.ResolvedTm r1)) 
            n2 (Ctx.ResolvedTm r2) in 
                (process_unifications ctx lg)
            | _ -> failwith "should not contain placeholder"
          )
      | (A.Atm(_), A.Lam(_), A.Pi(_)) -> 
          unify_tm ctx (HS.eta_expand m1 (A.to_weak index)) m2 index assump lg
      | (A.Lam _, A.Atm(A.Gen _, _), A.Atp _) -> unify_tm ctx m2 m1 index assump lg
      | _ -> failwith "Cannot unify a lambda with a non-lambda term"
) with Failure s -> raise (Failure  (s ^ "\n when attempting to unify (terms) " ^ A.ds_tm m1 ^ " and " ^ A.ds_tm m2  ^ " at index " ^ A.ds_tp index ^ Ctx.ds_conditional_show_ctx ctx))
        
and unify_spine (ctx : Ctx.ctxtype) (s1 : A.tm list) (s2 : A.tm list) (index : A.tp) (assump : Ctx.assump)  (lg : A.lgsig)  : unif_final_ctx  = 
let _ = if debug then print_endline("unify_spine unifying spines " ^ A.ds_spine s1 ^ " and " ^ A.ds_spine s2 ^ " at index " ^ A.ds_tp index  ^ Ctx.ds_conditional_show_ctx ctx) else () in
try(
  match (s1, s2, index) with
  | ([], [], A.Atp _) -> (process_unifications ctx lg)
  | ([], [], A.Type _) -> (process_unifications ctx lg)
  | ([], [], A.CoType _) -> (process_unifications ctx lg)
  | ([], [], _) -> failwith ("unify: spine index does not match at index " ^ A.ds_tp index)
  | ([], _, _) -> failwith "unify: spine unequal length"
  | (_, [], _) -> failwith "unify: spine unequal length"
  | ((m1 :: s1t), (m2 :: s2t), A.Pi(tx, t2, t1)) -> 
      (* let (ctx) = unify_tm ctx m1 m2 t2 lg in *)
      let (ctx) = Ctx.add_unification_equations_tm ctx [(m1, m2, t2, assump)] in
      let t1 = HS.h_sub_in_tp m1 (A.to_weak t2) tx t1 in (* *)
       unify_spine ctx s1t s2t t1 assump lg 
  | _ -> failwith "unif151: type mismatch"
) with Failure s -> raise (Failure  (s ^ "\n when attempting to unify (spines) " ^ A.ds_spine s1 ^ " and " ^ A.ds_spine s2  ^ " at index " ^ A.ds_tp index ^ Ctx.ds_conditional_show_ctx ctx))



and unify_tp (ctx : Ctx.ctxtype) (t1 : A.tp) (t2 : A.tp) (lg : A.lgsig) : unif_final_ctx   = 
let _ = if debug then print_endline("unify_tp unifying types " ^ A.ds_tp t1 ^ " and " ^ A.ds_tp t2  ^ Ctx.ds_conditional_show_ctx ctx) else () in
try(
  match (t1, t2) with
  | (A.Pi(x1, t1_2, t1_1), A.Pi(x2, t2_2, t2_1)) -> 
      let UnifDone ctx = unify_tp ctx t1_2 t2_2 lg in
      let ((x1, t1_1, t2_1)) = UnifyUtil.unify_bnd_tp_tp (x1, t1_1) (x2, t2_1) in
      let (ctx, ())  =
      Ctx.with_new_name ctx x1 t2 (fun ctx -> 
            (* this is a hack how we handle new names *)
          let (UnifDone ctx) = unify_tp ctx t1_1 t2_1 lg in
          (ctx, ())
        )
      in process_unifications ctx lg
  | (A.Atp(h1, s1), A.Atp(h2, s2)) ->
      (match (h1, h2) with
        | (A.Prvd n1, A.Prvd n2)  -> 
          if n1 = n2 
            then (
          match Ctx.find_id_in_ctx_and_sig ctx true h1 lg with
          | Some (tp, (Ctx.IdBound | Ctx.IdConstant _ | Ctx.IdFreeVar | Ctx.IdUniVar _))  -> 
                 unify_spine ctx s1 s2 (tp) [] lg 
          | Some (_, _) -> failwith ("unif169: not implemented when unifying " ^ A.ds_tp t1 ^ " and " ^ A.ds_tp t2)
          | _ -> failwith ("unif170: lookup not found " ^ A.ds_id h1))
        else failwith "unif failure: distinct head tp"
        | (A.Gen n1, A.Prvd _) -> 
          if HS.occurs_in_tp h1 t2 
            then failwith "unif100: occurs check failure"
          else 
            (* TODO: determine imitation OR projection 
               - for types this can only be imitation *)
            let ( s1') = check_spine_is_pattern ctx s1 lg  in
            (* let _ = if s1' = [] then () else failwith "unif215: type variables applied to arguments?" in *)
            (* prepare the types for unification variables *)
            let (h2tp, _) = Ctx.lookup_id_in_ctx_and_sig ctx true h2 lg in 
            let (ctx, unifVars ) = Ctx.new_metavars_tm ctx h2tp s2 s1' [] lg in
            let resolution = 
              Ctx.abstract_over_tp ctx s1' 
              ( A.Atp(h2, List.map
                      (fun v -> A.Atm(A.Gen v, List.map(fun m -> A.Atm(m, []))s1')) unifVars)) lg in
            let ctx = Ctx.resolve_metavar ctx n1 (Ctx.ResolvedTp resolution) in
            let resolution' = HS.h_sub_feed_spine_tp s1 resolution in
            unify_tp ctx resolution' t2 lg
        | (A.Prvd _, A.Gen _) -> unify_tp ctx t2 t1 lg
        | (A.Gen n1, A.Gen n2) -> 
            let ( s1) = check_spine_is_pattern ctx s1 lg in 
            let ( s2) = check_spine_is_pattern ctx s2 lg in
            let common = find_common_pattern (n1 = n2)  s1 s2 ctx lg in
            let (ctx, newuvar) = Ctx.new_metavar_tp ctx in
            let resolution_body = A.Atp(A.Gen newuvar, List.map(fun id -> A.Atm(id, [])) common) in
            let r1 = Ctx.abstract_over_tp ctx s1 resolution_body lg in
            let r2 = Ctx.abstract_over_tp ctx s2 resolution_body lg in
            let ctx = if n1 = n2 then Ctx.resolve_metavar ctx n1 (Ctx.ResolvedTp r1)
        else Ctx.resolve_metavar (Ctx.resolve_metavar ctx n1 (Ctx.ResolvedTp r1)) 
        n2 (Ctx.ResolvedTp r2) in 
            (process_unifications ctx lg)
        | _ -> failwith "should not contain placeholder"
      )
  | (A.Atp(A.Gen n1, s1), A.Pi(_)) -> 
      let s1' = check_spine_is_pattern ctx s1 lg in
      let boundName = A.Prvd (Uid.nextz())  in
      let (ctx, t1_2_var) = Ctx.new_metavar_tp ctx in
      let (ctx, t1_1_var) = Ctx.new_metavar_tp ctx in
      let resolution_body = A.Pi(boundName, A.Atp(A.Gen t1_2_var, s1), A.Atp(A.Gen t1_1_var, s1@[A.Atm(boundName, [])])) in
      let resolution = Ctx.abstract_over_tp ctx s1' resolution_body lg in
      let ctx = Ctx.resolve_metavar ctx n1 (ResolvedTp resolution) in
      unify_tp ctx resolution_body t2 lg
  | (A.Pi _, A.Atp(A.Gen _, _)) -> unify_tp ctx t2 t1 lg
  (* | _ -> failwith "ni69: unif" *)
  | _ -> failwith "no unification between a pi and an atomic type"
) with Failure s -> raise (Failure  (s ^ "\n when attempting to unify types " ^ A.ds_tp t1 ^ " and " ^ A.ds_tp t2  ^ Ctx.ds_conditional_show_ctx ctx))



    

and find_and_process_first_unif_eq (sofar : Ctx.ctxtype) (l : Ctx.ctxtype)(lg : A.lgsig)  : (unif_final_ctx) = 
    match l with
    | [] -> (UnifDone sofar) (*DONE *)
    | (Ctx.UnifContraintTm(m1, m2, t, assump) :: lt) -> (unify_tm (sofar@lt) m1 m2 t assump lg )
    | (Ctx.UnifContraintTp(t1, t2) :: lt) -> (unify_tp (sofar@lt) t1 t2 lg )
    | (h :: lt) -> find_and_process_first_unif_eq (sofar@[h]) lt lg 

and process_unifications (ctx : Ctx.ctxtype) (lg : A.lgsig) : unif_final_ctx = 
  find_and_process_first_unif_eq [] ctx lg 
(* in
  let (ctx, keepgoing) = 
  if keepgoing then process_unifications ctx lg else ctx *)

let rec assert_unification_done  (l : Ctx.ctxtype) : unit = 
    match l with
    | [] -> (() ) (*DONE *)
    | (Ctx.UnifContraintTm(_) :: _) -> failwith "unification equations still exists, check if unify_* calls process unifications at the end"
    | (Ctx.UnifContraintTp(_) :: _) -> failwith "unification equations still exists, check if unify_* calls process unifications at the end"
    | (_ :: lt) -> assert_unification_done lt
    
let request_unify_tp (ctx : Ctx.ctxtype) (t1 : A.tp) (t2 : A.tp) (lg : A.lgsig) : Ctx.ctxtype * A.tp  = 
try(
  (* Added because of logic programming, remove once logic programming switches to use whole context *)
  let (t1, t2) =  (Ctx.instantiate_metavar_tp ctx t1, Ctx.instantiate_metavar_tp ctx t2) in
  let ctx = Ctx.add_unification_equations_tp ctx [(t1, t2)] in
  let UnifDone ctx = process_unifications ctx lg in
  let _ = assert_unification_done ctx in
  let t1' = Ctx.instantiate_metavar_tp ctx t1 in
  (ctx, t1')
) with Failure s -> raise (Failure  (s ^ "\n when attempting to unify (toplevel) types " ^ A.ds_tp t1 ^ " and " ^ A.ds_tp t2  ^ Ctx.ds_conditional_show_ctx ctx))



let request_unify_tm (ctx : Ctx.ctxtype) (m1 : A.tm) (m2 : A.tm) (tp : A.tp) (lg : A.lgsig) : Ctx.ctxtype * A.tm  = 
try(
  (* Added because of logic programming, remove once logic programming switches to use whole context *)
  let (m1, m2, tp) =  (Ctx.instantiate_metavar_tm ctx m1, Ctx.instantiate_metavar_tm ctx m2, Ctx.instantiate_metavar_tp ctx tp) in
  let ctx = Ctx.add_unification_equations_tm ctx [(m1, m2, tp, [])] in
  let UnifDone ctx = process_unifications ctx lg in
  let _ = assert_unification_done ctx in
  let m1' = Ctx.instantiate_metavar_tm ctx m1 in
  (ctx, m1')
) with Failure s -> raise (Failure  (s ^ "\n when attempting to unify (toplevel) (terms) " ^ A.ds_tm m1 ^ " and " ^ A.ds_tm m2  ^ " at index " ^ A.ds_tp tp ^ Ctx.ds_conditional_show_ctx ctx)) *)


let get_pattern_spine (args : A.abt list) : string list = 
  let free_vars = List.map (fun a -> match a with
  | A.FreeVar s -> s
  | _ -> failwith "unif: get_pattern_spine: expected free variable"
  ) args in 
  free_vars

let is_pattern_spine (args : A.abt list) : bool = 
  if List.for_all (fun a -> match a with
  | A.FreeVar _ -> true
  | _ -> false
  ) args 
  then (let free_vars = get_pattern_spine args in
        if ListUtil.contains_duplicate free_vars 
        then false
        else true)
  else false

let find_unif_var (uc : Ctx.unif_ctx) (i : int) : A.abt option = 
  match uc with
  | Ctx.OkCtx l -> 
    (
      match List.find_opt (fun (l, _) -> match l with
      | A.N(A.UnifVar ci, _) -> ci = i
      | _ -> false
      ) l with
      | Some (A.N(A.UnifVar _, args), tm) -> Some (A.abstract_over_list (get_pattern_spine args) tm)
      | _ -> None
    )
  | Ctx.UnifFailed -> failwith "unif: find_unif_var: unification failed"

let rec deref_all_unifvar (uc : Ctx.unif_ctx) (tm : A.abt) : A.abt = 
  match tm with
  | A.N(A.UnifVar i, args) -> 
    (
      match find_unif_var uc i with
      | Some tm' -> deref_all_unifvar uc (A.instantiate_expr_list args tm')
      | None -> tm
    )
  | _ -> A.map_abt (deref_all_unifvar uc) tm


let add_unification_equation (uc : Ctx.unif_ctx) (a : A.abt) (b : A.abt) : Ctx.unif_ctx = 
  match uc with
  | Ctx.OkCtx l -> 
    (
      match a with
      | A.N(A.UnifVar _, args) -> 
          (if is_pattern_spine args
            then OkCtx ((a, b) :: l)
            else failwith "tcc72: add_unification_equation: expected a pattern spine"
          )
      | _ -> failwith "tcc72: add_unification_equation: expected a unification variable as LHS"
    )
  | Ctx.UnifFailed -> UnifFailed

let rec consistify_ctx (unif_ctx : Ctx.unif_ctx) (i : int) : Ctx.unif_ctx = 
  match unif_ctx with
  | Ctx.UnifFailed -> Ctx.UnifFailed
  | Ctx.OkCtx l -> 
    (
      let (candidate_equations, rest_equations) = List.partition (fun (l, _) -> match l with
                                              | (A.N(A.UnifVar ci, _)) -> ci = i
                                              | _ -> false
                                              ) l in
      match candidate_equations with
      | [] -> failwith "unif366: consistify_ctx: no candidate equations"
      | [_] -> unif_ctx
      (* The idea is we remove the current unification variable from the current context*)
      | (A.N(A.UnifVar i, args_l), tm_l)::rest  -> 
          let unif_ctx' = 
              List.fold_right (fun cur_eq cur_ctx -> 
                match cur_eq with
                | (A.N(A.UnifVar _, args_r), tm_r) -> 
                    request_unify cur_ctx tm_l (A.subst_list args_l (get_pattern_spine args_r) tm_r)
                | _ -> failwith "unif375: consistify_ctx: expected unification variable as LHS"
                ) rest (Ctx.OkCtx rest_equations)
                in (* TODO circular unification *)
          add_unification_equation unif_ctx' (A.N(A.UnifVar i, args_l)) tm_l
      | _ -> failwith "unif378: consistify_ctx: multiple candidate equations"
    )

and request_unify (unif_ctx : Ctx.unif_ctx) (tm1 : A.abt) (tm2 : A.abt) : Ctx.unif_ctx = 
  if debug then print_endline("request_unify: " ^ A.ds_abt tm1 ^ " ≐ " ^ A.ds_abt tm2) else ();
  if A.equal_abt tm1 tm2 then unif_ctx else 
  match (tm1, tm2) with
  | (A.N(A.UnifVar i, _), _) -> 
      consistify_ctx (add_unification_equation unif_ctx tm1 tm2) i
  | (_, A.N(A.UnifVar i, _)) ->
      consistify_ctx (add_unification_equation unif_ctx tm2 tm1) i
  | (A.N(n1, arg1), A.N(n2, arg2)) -> 
      if n1 = n2 
      then (
        if List.length arg1 = List.length arg2
        then List.fold_left2 (fun ctx a1 a2 -> request_unify ctx a1 a2 ) unif_ctx arg1 arg2
        else Ctx.UnifFailed
      )
      else Ctx.UnifFailed
  | (A.FreeVar s1, A.FreeVar s2) -> if s1 = s2 then unif_ctx else Ctx.UnifFailed
  | (A.FreeVar _, _) -> request_unify unif_ctx (A.N(A.At, [tm1])) tm2
  | (_, A.FreeVar _) -> request_unify unif_ctx tm1 (A.N(A.At, [tm2]))
  | _ -> failwith ("unhandled case 371: " ^ A.ds_abt tm1 ^ " ≐ " ^ A.ds_abt tm2)

    (* Ctx.UnifFailed *)
      (* failwith ("failed to unify " ^ A.ds_abt tm1 ^ " and " ^ A.ds_abt tm2) *)


let continue_if_ok (unif_ctx : Ctx.unif_ctx) (ok : unit -> 'a) (fail : unit -> 'a) : 'a =
  match unif_ctx with
  | Ctx.OkCtx _ -> ok ()
  | _ -> fail ()


let request_unify_ok (unif_ctx : Ctx.unif_ctx) (tm1 : A.abt) (tm2 : A.abt) : Ctx.unif_ctx = 
  let result = request_unify unif_ctx tm1 tm2 in
  match result with
  | Ctx.OkCtx _ -> result
  | _ -> failwith ("failed to unify " ^ A.ds_abt tm1 ^ " and " ^ A.ds_abt tm2)