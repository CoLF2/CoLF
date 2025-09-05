
module A = Ast
module Ctx = TypeCheckingContext  
module HS = HereditarySubstitution
module Unif = Unification
module LPUtils = LogicProgrammingUtils

(* exception SolutionNotFound
exception FoundSolution  of (Ctx.ctxtype * A.tm)  (* solution*)
                          * ( unit -> unit ) continue *)

let debug = Flags.lp_debug
(* let debug = true *)


let rec is_coinductive (tp : A.abt) (lg : A.decls) : bool = 
  match tp with
  | A.N(A.Pi, [_; t1]) -> is_coinductive (snd (A.unbind_expr t1)) lg
  | A.N(A.At, t1::_) -> is_coinductive t1 lg
  | A.N(A.CoType, []) -> true
  | A.N(A.Type, []) -> false
  | A.FreeVar s -> (
      match Ctx.find_id_sig_local s lg with
      | Some stp -> is_coinductive stp lg
      | None -> false
    )
  | _ -> failwith ("Unrecognized expression in is_coinductive " ^ A.ds_abt tp)

let rec is_inductive (tp : A.abt) (lg : A.decls) : bool = 
  match tp with
  | A.N(A.Pi, [_; t1]) -> is_inductive (snd (A.unbind_expr t1)) lg
  | A.N(A.At, t1::_) -> is_inductive t1 lg
  | A.N(A.CoType, []) -> false
  | A.N(A.Type, []) -> true
  | A.FreeVar s -> (
      match Ctx.find_id_sig_local s lg with
      | Some stp -> is_inductive stp lg
      | None -> false
    )
  | _ -> failwith ("Unrecognized expression in is_inductive " ^ A.ds_abt tp)

type depth_ctx =  int * int (* trial depth, inductive depth, coinductive depth *)

let get_inductive_depth (d : depth_ctx) : int = match d with | (_, n) -> n
let get_coinductive_depth (d : depth_ctx) : int = match d with | (p, _) -> p



let decrement_depth_ctx (d : depth_ctx) (tp : A.abt) (lg : A.decls) : depth_ctx option = 
  if is_coinductive tp lg
    then (
      if Flags.c_debug "tp_ind_coind" then print_endline ("Coinductive: " ^ A.ds_abt tp) else ();
      match d with
            | ( 0, _) -> None
            | ( m, _) -> Some ( m-1, LPUtils.default_inductive_limit)
          )
    else (
      if Flags.c_debug "tp_ind_coind" then print_endline ("Inductive: " ^ A.ds_abt tp) else ();
          if is_inductive tp lg 
          then (match d with
            | ( _, 0) -> None
            | ( m, n) -> Some ( m, n-1)
          )
          else failwith ("Cannot determine if the type is inductive or coinductive " ^ A.ds_abt tp)
        )

type failure_kont = unit -> unit
type lp_solution = (Ctx.unif_ctx * A.abt)
type succss_kont = lp_solution -> failure_kont -> unit

(* returns new unification context with a proof term *)
(* returns the updated trial depth *)
let rec focus_r 
          (unif_ctx : Ctx.unif_ctx) 
          (depth_ctx : depth_ctx) 
          (ctx : Ctx.ctx) 
          (focus_expr : A.abt) 
          (lg : A.decls)
          (guide : A.abt) (* guide is a term that guides the *search* but not the unification behavior *)
          (success_k : succss_kont)
          (failure_k : failure_kont) : unit =
  let _ = if Flags.c_debug "r_focus" then print_endline ("Right Focus: " ^ LPUtils.ds_depth_ctx depth_ctx ^ Ctx.ds_ctx ctx ^ " ==> " ^ A.ds_abt focus_expr ^ ", guide: " ^ A.ds_abt guide) else () in
  try (
    match unif_ctx with
    | Ctx.UnifFailed -> success_k (unif_ctx, A.N(A.LPFail, [])) failure_k
    | _ -> 
      (
        if get_coinductive_depth depth_ctx = 0 || get_inductive_depth depth_ctx = 0
          then 
            success_k (unif_ctx, A.N(A.LPPending, [])) failure_k
          else
            (match focus_expr with
            | (A.N(A.At, _) | A.FreeVar _) -> stable_seq unif_ctx depth_ctx ctx focus_expr lg guide success_k failure_k
            | (A.N(A.Pi, [t2; t1])) -> (
                let (ctx', name, t1') = Ctx.ctx_extend_with_binding ctx t2 t1  in
                let success_k' = fun (unif_ctx', tm) failure_k' -> success_k (unif_ctx', A.N(A.Lam, [A.abstract_over name tm])) failure_k' in
                (
                  match guide with
                  | A.N(A.LPPending, []) -> focus_r unif_ctx depth_ctx ctx' t1' lg guide success_k' failure_k
                  | A.N(A.Lam, [sub_guide]) -> focus_r unif_ctx depth_ctx ctx' t1' lg (A.instantiate_bound_var_no_repeat name sub_guide) success_k' failure_k
                  | _ -> failwith ("Unrecognized guide in focus_r " ^ A.ds_abt guide)
                )
              )
            | _ -> failwith ("Unrecognized expression in focus_r " ^ A.ds_abt focus_expr)
            )
      )
  ) with Failure s -> raise (Failure (s ^ "\n when right focusing on the goal " ^ A.ds_abt focus_expr))
and stable_seq 
      (unif_ctx : Ctx.unif_ctx) 
      (depth_ctx : depth_ctx) 
      (ctx : Ctx.ctx) 
      (right : A.abt) 
      (lg : A.decls) 
      (guide : A.abt)
      (success_k : succss_kont)
      (failure_k : failure_kont) : unit =
  let _ = if Flags.c_debug "stable" then print_endline ("Search: " ^ Ctx.ds_ctx ctx ^ " ==> " ^ A.ds_abt right ^ ", guide: " ^ A.ds_abt guide) else () in
  let available_premises = ctx @ (List.map (fun ((name, tp)) -> (name, tp)) lg) in
  let rec try_premises 
            (cur_depth_ctx : depth_ctx) 
            (remaining : (string * A.abt) list) 
            (cur_success_k : succss_kont)
            (cur_failure_k : failure_kont) : 'a =
    match remaining with
    | [] -> cur_failure_k ()
    | (name, tp)::tl -> 
      (
        let cur_failure_k' = fun () -> try_premises cur_depth_ctx tl cur_success_k cur_failure_k in
        match decrement_depth_ctx cur_depth_ctx tp lg with
          | Some(new_depth_ctx) -> 
              left_focus unif_ctx new_depth_ctx ctx right tp name lg guide cur_success_k cur_failure_k'
          | None -> failwith "Depth limit reached in search, this should not occur"
      )
    in
    match guide with
    | A.N(A.LPPending, []) -> (
      let applicable_premises = List.filter (fun (_, tp) -> AstOps.get_tp_head tp = AstOps.get_tp_head right) available_premises in
        try_premises depth_ctx applicable_premises success_k failure_k
    )
    | A.N(A.At, (A.FreeVar name)::_) -> 
      (
        match Ctx.find_id_sig_local name lg with
        | Some tp -> 
            (match decrement_depth_ctx depth_ctx tp lg with
              | Some(new_depth_ctx) -> 
                  left_focus unif_ctx new_depth_ctx ctx right tp name lg guide success_k failure_k
              | None -> failwith "Depth limit reached in search, this should not occur"
            )
        | None -> failwith ("Cannot find " ^ name ^ " in the local context with guide " ^ A.ds_abt guide ^ " during search")
      )
    | _ -> failwith ("Unrecognized guide in stable_seq " ^ A.ds_abt guide)

and left_focus 
      (unif_ctx : Ctx.unif_ctx) 
      (depth_ctx : depth_ctx) 
      (ctx : Ctx.ctx) 
      (right : A.abt) 
      (focus_expr : A.abt) 
      (name : string) 
      (lg : A.decls)
      (guide : A.abt)
      (success_k : succss_kont)
      (failure_k : failure_kont) : unit = 
  let _ = if Flags.c_debug "l_focus" then print_endline ("Left Focus: [" ^ name ^ " : " ^ A.ds_abt focus_expr ^ "] ==> " ^ A.ds_abt right) else () in
  let rec process_left 
            (processed : (A.abt option * A.abt) list) 
            (current_focus: A.abt) : 'a =
    let _ = if debug then print_endline ("Sub Left Focus: [" ^ A.ds_abt current_focus ^ "] ,  pending " ^ 
      String.concat ", " (List.map (fun (tm, tp) -> 
        match tm with 
        | Some tm' -> A.ds_abt tm' ^ " : " ^ A.ds_abt tp
        | None -> "NONE : " ^ A.ds_abt tp
       ) processed)) else () in
    match current_focus with
    | A.N(A.Pi, [t2; t1]) -> (
      let (name, t1') = A.unbind_expr t1 in 
      if A.appears_in_expr name t1' 
        then 
          let v = UnifVars.new_unif_var t2 "D" in
          let new_processed = processed@[(Some v, t2)] in
          process_left new_processed (A.subst v name t1')
        else 
          let new_processed = processed@[(None, t2)] in
          process_left new_processed t1'
    )
    | A.N(A.At, _) -> (
      let unif_ctx' = Unif.request_unify unif_ctx current_focus right in
      match unif_ctx' with
      | Ctx.OkCtx (_) -> (
          let rec process_goals 
                    (sub_unif_ctx : Ctx.unif_ctx) 
                    (processed : A.abt list) 
                    (remaining : (A.abt option * A.abt) list) 
                    (sub_guide : A.abt list)
                    (sub_success_k : succss_kont)
                    (sub_failure_k : failure_kont) : unit = 
            match remaining with
            | [] -> sub_success_k (sub_unif_ctx, A.N(A.At, (A.FreeVar name)::processed)) sub_failure_k
            | (Some tm, _)::tl -> 
              (
              match sub_guide with
              | _sub_guide_h :: sub_guide_t -> process_goals sub_unif_ctx (processed@[tm]) tl sub_guide_t sub_success_k sub_failure_k
              | [] -> failwith ("Mismatched guide in left_focus_process_goals " ^ A.ds_abt guide)
              )
            | (None, tp) :: tl -> 
                (
                  match sub_guide with
                  | sub_guide_h :: sub_guide_t -> 
                      let sub_success_k' = (fun (unif_ctx'', tm) -> fun sub_failure_k' ->
                        process_goals unif_ctx'' (processed@[tm]) tl sub_guide_t sub_success_k sub_failure_k') 
                      in
                        focus_r sub_unif_ctx depth_ctx ctx tp lg sub_guide_h sub_success_k' sub_failure_k
                        (* | None -> sub_success_k' (sub_unif_ctx, A.N(A.LPPending, [])) sub_failure_k *)
                        (* | None -> sub_success_k (sub_unif_ctx, A.N(A.LPPending, [])) sub_failure_k *)
                  | [] -> failwith ("Mismatched guide in left_focus_process_goals " ^ A.ds_abt guide)
                )
          in 
          (
            match guide with
            | A.N(A.LPPending, []) -> process_goals unif_ctx' [] processed (List.init (List.length processed) (fun _ -> guide)) success_k failure_k
            | A.N(A.At, (A.FreeVar name')::tl) -> (
                if name = name' 
                  then process_goals unif_ctx' [] processed (tl) success_k failure_k
                  else failwith ("Mismatched guide in left_focus " ^ A.ds_abt guide)
                )
            | _ -> failwith ("Unrecognized guide in left_focus " ^ A.ds_abt guide)
          )
      )
      | Ctx.UnifFailed -> failure_k()
    )
    | A.FreeVar s -> process_left processed (A.N(A.At, [A.FreeVar s]))
    | A.N(A.Type, []) -> failure_k()
    | A.N(A.CoType, []) -> failure_k()
    | _ -> failwith ("Unrecognized expression in left_focus " ^ A.ds_abt current_focus)
    in 
  try (
    process_left [] focus_expr
  ) with Failure s -> raise (Failure (s ^ "\n when left focusing on the goal " ^ name ^ ": " ^ A.ds_abt focus_expr))



let lp_top_level (ind_depth : int) (coind_depth : int) (global : A.ssig) (local : A.ssig) : unit =
  let all_unifiable_names = ListUtil.remove_duplicates 
      (List.concat_map (fun ((_, tp)) -> A.collect_free_vars tp) local.decls) in
  let rec process_local 
            (ctx : Ctx.unif_ctx) 
            (depth_ctx : depth_ctx) 
            (resolution : (string * A.abt) list)
            (processed : A.decls) 
            (remaning : A.decls) 
            (guide : (string * A.abt) list)
            (success_k : Ctx.unif_ctx * (string * A.abt) list -> failure_kont -> unit)
            (failure_k : (unit -> unit)) : unit =
    match remaning with
    | ((name, tp)::tl) -> 
      (
        if List.mem name all_unifiable_names 
        then 
          let v = UnifVars.new_unif_var tp "D" in
          let new_remaining = List.map (fun ((n, tp)) -> (n, A.subst v name tp)) tl in
          let _ = if debug then print_endline ("Unifiable: " ^ name ^ " = " ^ A.ds_abt v ^ " Remaining: " ^ A.ds_decls new_remaining) in
          process_local ctx depth_ctx (resolution@[(name, v)]) (processed@[((name, tp))]) new_remaining guide success_k failure_k
        else
          let _ = if debug then print_endline ("Start Proof Search for : " ^ A.ds_decl ((name, tp))) else () in
          let success_k' = (fun (ctx', tm) failure_k' -> 
            let new_remaining = List.map (fun ((n, tp)) -> (n, A.hereditary_subst tm name tp)) tl in
            process_local ctx' depth_ctx (resolution@[(name, tm)]) (processed@[((name, tp))]) new_remaining guide success_k failure_k')
          in
          let this_guide_tm = (match ListUtil.find_elem_by_key guide name  with
                                | Some guide_tm -> guide_tm
                                | None -> A.N(A.LPPending, []))
          in
            focus_r ctx depth_ctx [] tp (global.decls@processed) this_guide_tm success_k' failure_k
      )
    | [] -> (
      success_k (ctx, resolution) failure_k
    )
  in 
  let rec repl_loop 
    (guide : (string * A.abt) list)
    (depth_ctx: depth_ctx) =
      let success_kont = (fun (unif_ctx, resolution) failure_kont' -> 
        (
          let resolved_resolution = (List.map (fun (name, tm) ->
                    let resolved_tm = (Unification.deref_all_unifvar unif_ctx tm) in 
                    (name, resolved_tm)
                    ) resolution) in
          let _ = print_endline 
            (
              (if Flags.show_raw_lp_result
                then ((String.concat ", " (List.map (fun (name, tm) -> name ^ " = " ^ A.ds_abt tm) resolution)) ^ "\n" ^
                      Ctx.ds_unif_ctx unif_ctx ^ "\n") else "")
            ^ (
                  "Success: " ^ (String.concat ",\n" (List.map (fun (name, resolved_tm) ->
                     name ^ " = " ^ PrettyPrint.pp_abt global.decls  resolved_tm  ^ 
                     ( 
                      match (Ctx.find_id_sig_local name local.decls) with
                      | None -> failwith ("Cannot find " ^ name ^ " in the local context")
                      | Some tp_def ->
                      let tp_name = (AstOps.get_tp_head tp_def) in
                      if PrettyPrint.tp_name_has_special_pp tp_name
                      then " ~~> " ^ PrettyPrint.special_pp_top_level global.decls resolved_tm ^ ""
                      else ""
                     )) 
                     resolved_resolution))
                ^ "\n"
            )
            ) in
          let _  = Stdlib.output_string Stdlib.stdout (LPUtils.ds_depth_ctx depth_ctx ^ " (type `;` for next, type `:` to increase depth (while commiting to the current choice), type `.` to end) ")  in
          let _ = Stdlib.flush Stdlib.stdout  in
          let prompt_char = IOUtils.get1char () in
          let (cur_coind, cur_ind) = depth_ctx in
          let removed_resolution = List.map (fun (name, tm) -> (name, AstOps.replace_unif_vars_with_lppending tm)) resolution in
          let _ = print_newline() in
          match prompt_char with
          | ';' -> (failure_kont'())
          | ':' -> ( repl_loop removed_resolution (cur_coind * 2, cur_ind))
          | 'u' -> ( repl_loop guide (cur_coind + 1, cur_ind))
          | _ -> ()
        )) in 
      let failure_kont = fun () -> print_endline ("Failed") in 
      process_local (Ctx.OkCtx []) (depth_ctx) [] [] local.decls guide success_kont failure_kont
  in
  repl_loop [] (coind_depth, ind_depth)
  
  
  


(* let rec loop ( g : A.dec list) (coind_depth : int) (ind_depth : int): unit = 
  try(
  (* let _ = print_endline "?-" in *)
  let _  = Stdlib.output_string Stdlib.stdout (ds_depth_ctx ( coind_depth, ind_depth) ^ " ?- ")  in
  let _ = Stdlib.flush Stdlib.stdout  in

  let input = Stdlib.input_line Stdlib.stdin in
  if String.starts_with ~prefix:"%depth=" input
    then 
      let new_depth = int_of_string (String.sub input 7 ((String.length input) - 7)) in
      loop g new_depth ind_depth
    else
      let _ = print_endline ("Query: " ^ input) in
      let processed = Lexer.lex_string input in
      let rawparsed = Parse.rawparse processed in
      let elaborated = Elborate.elaborateDec rawparsed in
      let type_checked = TypeReconstruct.typecheckAdditionalSig g elaborated in
      let _ = (
        let all_names = (List.map (fun (A.Decl(name, _)) -> name) (type_checked@g)) in
        if ListUtil.contains_duplicate all_names 
          then failwith ("Duplicate names in the input : " ^ (String.concat ", " (ListUtil.find_duplicates all_names)))
        else (())
      ) in
      let _ = print_endline ("Read as " ^ A.ds_decl type_checked) in
      let _ = lp_top_level ind_depth coind_depth g type_checked in
      loop g coind_depth ind_depth
  ) with 
   Failure s -> (print_endline s; print_endline "Exception occurred during program execution. Try again."; loop g coind_depth ind_depth)
   *)
  
  
let loop_top g = 
let _ =  print_endline "Please provide a period separated list of declarations in the form of `M1 : T1. .... Mn : Tn.`. Each Mi serves as an existential variable, Mi is resolved by unification if it appears in later queries. Use %depth=<num> to set depth. " in 
  LPUtils.depth_loop_wrap_top g lp_top_level


(* 
   
TODO: 

0. Real arithmetic as an example
1. Padded Streams, stream processors (e.g. adding two streams together, compute diagonal of a stream of streams)
2. Ternary arithmetic


1. Pretty print omit parametric arguments
2. Print the terms in the format M1, M2, M3, ..., not ap[M1; M2; .. M3]
3. Mode checker 
4. Productivity and termination checking
5. Coverage checking
6. (Later) Metatheorem

*)