

module A = Ast
(* warning: this version of type checking considers all DefI to be coinductive, 
   and do not consider notational definitions *)

module Ctx = TypeCheckingContext
module HS = HereditarySubstitution
module Unif = Unification


let debug = Flags.tr_debug


            
let rec synth (unif_ctx: Ctx.unif_ctx) (ctx : Ctx.ctx)(tm : A.abt) (lg : A.decls) : Ctx.unif_ctx * A.abt * A.abt (* tm and tp *) = 
  let _ = if debug then print_endline ("synth on " ^ A.ds_abt tm ^ " in ctx " ^ Ctx.ds_conditional_show_ctx ctx ) else () in 
  try(
    match tm with
      | A.FreeVar(name) -> 
          let tp = Ctx.lookup_id_in_ctx_and_sig ctx name lg in
          (unif_ctx, tm, tp)
      | A.N(A.Type, []) -> 
          (unif_ctx, tm, A.kind_expr)
      | A.N(A.CoType, []) -> 
          (unif_ctx, tm, A.kind_expr)
      | A.N(A.Pi, [t2; t1]) -> 
          let (unif_ctx', t2') = check_type_or_cotype unif_ctx ctx t2 lg in
          let (ctx', t1_abs, t1_body) = Ctx.ctx_extend_with_binding ctx t2' t1 in 
          let (unif_ctx'', t1', tp) = synth unif_ctx' ctx' t1_body lg in
          (unif_ctx'', A.N(A.Pi, [t2'; A.abstract_over t1_abs t1']), tp)
      | A.N(A.At, hd::spine) ->  
          (
            match hd with
            | A.FreeVar(name) -> 
                let hd_tp = Ctx.lookup_id_in_ctx_and_sig ctx name lg in
                let (unif_ctx', cspine, k) = tr_feed_spine unif_ctx ctx spine hd_tp lg in 
                (unif_ctx', A.N(A.At, hd::cspine), k)
            | _ -> failwith ("synth: expecting a free variable as head of application, got " ^ A.ds_abt hd)
          )
      | _ -> failwith ("synth: not implemented for " ^ A.ds_abt tm) 
      ) with Failure s -> raise (Failure (s ^ "\n when synthesizing the type of " ^ A.ds_abt tm ^ ""  ^ Ctx.ds_conditional_show_ctx ctx ))


and check (unif_ctx : Ctx.unif_ctx) (ctx : Ctx.ctx) (tm : A.abt) (tp: A.abt) (lg : A.decls) : (Ctx.unif_ctx * A.abt) = 
  match tm with
  | A.N(A.Lam, [arg]) -> 
    (
      match tp with
      | A.N(A.Pi, [t2; t1]) -> 
          let (ctx', bound_name, body) = Ctx.ctx_extend_with_binding ctx t2 arg in
          let t1' = A.instantiate_bound_var_no_repeat bound_name t1 in
          let (ctx'', body') = check unif_ctx ctx' body t1' lg in
          (ctx'', A.N(A.Lam, [A.abstract_over bound_name body']))
      | _ -> failwith "expecting pi type 63"
    )
  | _ ->
      let (unif_ctx', tm', tp') = synth unif_ctx ctx tm lg in
      let unif_ctx'' = Unif.request_unify_ok unif_ctx' tp' tp in
      (unif_ctx'', tm')

and check_type_or_cotype (unif_ctx : Ctx.unif_ctx) (ctx : Ctx.ctx) (tm : A.abt) (lg : A.decls) : (Ctx.unif_ctx * A.abt) = 
  let (unif_ctx', tm', tp') = synth unif_ctx ctx tm lg in
  match tp' with
  | A.N(A.Type, []) -> (unif_ctx', tm')
  | A.N(A.CoType, []) -> (unif_ctx', tm')
  | _ -> failwith ("expecting type or cotype, got " ^ A.ds_abt tp')



          
(* corresponds to the judgment S \rhd A/K => A/K *)
(* assumes fed is well-typed *)
and tr_feed_spine (unif_ctx: Ctx.unif_ctx) (ctx : Ctx.ctx) (spine : A.abt list) (fed : A.abt ) (lg : A.decls) : Ctx.unif_ctx * A.abt list *  A.abt = 
  let _ = if debug then print_endline ("tr_feed_spine on " ^  A.ds_abts spine ^ " into " ^ A.ds_abt fed ^ " in ctx " ^ Ctx.ds_conditional_show_ctx ctx ) else () in 
  try (
      match spine with
      | []  -> (unif_ctx, spine, fed)
      | (m :: ms) -> (
              match fed with
              | A.N(A.Pi, [t2; t1]) -> (
                  let (unif_ctx', cm) = check unif_ctx ctx m t2 lg in
                  let t1' = A.hereditary_instantiate_expr cm t1 in
                  let (unif_ctx'', cms, final_t) = tr_feed_spine unif_ctx' ctx ms t1' lg in
                  (unif_ctx'', (cm :: cms), final_t)
              )
              | _ -> failwith "expecting pi type 63: The number of arguments (=spine) may be more than the number of Pi's in the type of head (=into) of the term "
      )
    ) with Failure s -> raise (Failure (s ^ "\n when feeding spine " ^ A.ds_abts spine ^ 
    " into  " ^ A.ds_abt fed ^ ""  ^ Ctx.ds_conditional_show_ctx ctx))


let  tr_decl (tr : A.decl) ((l) as lg : A.decls) : A.decls * A.decl = 
  let _ = if debug then print_endline ("=======\ntr_decl on " ^ A.ds_decl tr ^ "\n=======") else () in
  try(
    match tr with
    | (name, t) -> 
        let (ctx', t', _) = synth Ctx.empty_unif_ctx [] t lg in 
        if Ctx.unif_ctx_is_ok ctx' then 
          (l, (name, t'))
        else 
          raise (Failure ("type checking failed for " ^ A.ds_decl tr))
  
  ) with Failure s -> raise (Failure (s ^ "\n when checking the declaration " ^ A.ds_decl tr  
  ^  "\nchecked signatures: " ^ A.ds_decls  (let (local) = lg in local)
  ))

(* checks signature, skips recursion definitions *)
let rec tr_sig ((localchecked , remaining) : A.decls * A.decls) : A.decls
= 
match remaining with
| [] -> localchecked
| (h::t) -> 
  let (localchecked, tlocal) = tr_decl h (localchecked) in 
  let lg = ((localchecked@[tlocal]), t) in 
  (* let lg = lazy_check_rec_def (lg) in *)
  tr_sig  lg

  (* TODO: check duplicates *)
(* let  typecheckSig (l : A.decls) : A.decls
= tr_sig ([], l) *)

let  typecheckSigTopLevel (l : A.ssig) : A.ssig
= {l with decls = tr_sig ([], l.decls)}

let  typecheckAdditionalSig (l : A.decls) (additional: A.decls) : A.decls
= ListUtil.drop_n (List.length l) (tr_sig (l, additional))
(*
Comment: 

Type checking is stratified:
The body of recursion constants must be checked before 
they are used in types
*)