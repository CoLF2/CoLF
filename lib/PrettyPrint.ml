
module A = Ast
module Ctx = TypeCheckingContext
  

let rec pp_ssig ( dl : A.ssig)  : string = 
  pp_decl dl.decls ^ ".\n" ^ pp_cmds dl.cmds
and pp_cmds (dl : A.decls) : string = 
  String.concat ".\n" (List.map (fun (c, a) -> "%" ^ c ^ " " ^ pp_abt dl a) dl)
and pp_decl ( dl : A.decls)  : string = 
  String.concat ".\n" (List.map (pp_dec dl) dl)
and pp_dec (lg : A.decls) (d : A.decl)  : string = 
match d with
  | (c, a) ->  c ^ " : " ^ pp_abt lg a
and pp_abt (lg : A.decls) (a: A.abt)  : string = 
  match a with
    | FreeVar(name) -> name
    | Bnd(_, _) -> let (name, sub) = A.unbind_expr a in 
              if A.appears_in_expr name sub 
                then name ^ "." ^ pp_abt lg sub
                else "_." ^ pp_abt lg sub
    | BoundVar(_) -> failwith "ast105: ds_abt: bound variable should not appear in the output"
    | N(At, tl) -> (
      match tl with
      | [single] -> pp_abt lg single
      | (FreeVar name)::tl' -> (
        match Ctx.find_id_sig_local name lg with
        | Some(tp) -> (
          let should_show = (
            let rec traverse_pi (tp : A.abt) = 
              match tp with
              | A.N(A.Pi, [_t2; t1]) -> (
                let (name, t1_body) = A.unbind_expr t1 in 
                if A.appears_in_expr name t1_body 
                  then false :: (traverse_pi t1_body)
                  else true :: (traverse_pi t1_body)
              )
              | _ -> []
              in 
            traverse_pi tp
          ) in
          if List.length should_show = List.length tl'
          then (
            let rec show_match (should_show_rest : bool list) (tl_rest : A.abt list) : string list = 
              match (should_show_rest, tl_rest) with
              | (true::should_show_rest', t::tl_rest') -> (pp_abt lg t) :: (show_match should_show_rest' tl_rest')
              | (false::should_show_rest', (A.N(A.UnifVar i, []))::tl_rest') -> (pp_abt lg (A.N(A.UnifVar i, []))) :: (show_match should_show_rest' tl_rest')
              | (false::should_show_rest', _::tl_rest') -> "_" :: (show_match should_show_rest' tl_rest')
              | _ -> []
            in 
            "(" ^  String.concat " " (name ::(show_match should_show tl')) ^ ")"
          )
          else (
            "(" ^ String.concat " " (List.map (pp_abt lg) tl) ^ ")"
          )

        )
        | None -> "(" ^ String.concat " " (List.map (pp_abt lg) tl) ^ ")"

      )
      | _ -> "(" ^ String.concat " " (List.map (pp_abt lg) tl) ^ ")"
    ) 
    | A.N(A.PPInt n, []) -> string_of_int n
    | A.N(A.PPReal (r, d), []) -> string_of_float r ^ " ± " ^ string_of_float d
    | A.N(A.PPList, elems) -> "[" ^ String.concat ", " (List.map (pp_abt lg) elems) ^ "]"
    | A.N(A.LPPending, []) -> "..."
    | A.N(A.UnifVar i, []) -> "?" ^ UnifVars.lookup_unif_var_name i ^ ""
    | A.N(A.Type, []) -> "type"
    | A.N(A.CoType, []) -> "cotype"
    | A.N(A.Pi, [t2; t1]) -> (
      let (name, t1_body) = A.unbind_expr t1 in 
      if A.appears_in_expr name t1_body 
        then "(" ^ name ^ " : " ^ pp_abt lg t2 ^ ") → " ^ pp_abt lg t1_body
        else pp_abt lg t2 ^ " → " ^ pp_abt lg t1_body
    )
    | N(node, tl) -> A.ds_node node ^ (pp_abts lg) tl
and pp_abts (lg : A.decls) (tl : A.abt list)  : string =
  "[" ^ String.concat "; " (List.map (pp_abt lg) tl) ^ "]"


let tp_name_has_special_pp (tp: string) : bool = 
  match tp with
  | "nat" -> true
  | "tn" -> true
  | "i" -> true
  | "stream" -> true
  | _ -> false

let rec special_pp  (tm: A.abt) : A.abt = 
  match tm with
  | A.FreeVar "tn_e" -> A.N(A.PPInt 0, [])
  | A.FreeVar "zero" -> A.N(A.PPInt 0, [])
  | A.N(A.At, [A.FreeVar x]) -> special_pp (A.FreeVar x)
  | A.N(A.At, [A.FreeVar "tn_m1"; sub]) -> (
    match special_pp sub  with
    | A.N(A.PPInt n, []) -> A.N(A.PPInt (3*n - 1), [])
    | other -> A.N(A.At, [A.FreeVar "tn_m1"; other])
  )
  | A.N(A.At, [A.FreeVar "tn_z0"; sub]) -> (
    match special_pp sub  with
    | A.N(A.PPInt n, []) -> A.N(A.PPInt (3*n ), [])
    | other -> A.N(A.At, [A.FreeVar "tn_z0"; other])
  )
  | A.N(A.At, [A.FreeVar "tn_p1"; sub]) -> (
    match special_pp sub  with
    | A.N(A.PPInt n, []) -> A.N(A.PPInt (3*n + 1), [])
    | other -> A.N(A.At, [A.FreeVar "tn_p1"; other])
  )
  | A.N(A.At, [A.FreeVar "i/c"; tn; sub]) -> (
    match (special_pp tn, special_pp sub)  with
    | (A.N(A.PPInt i, []), A.N(A.PPReal (r, d), [])) -> A.N(A.PPReal ( float_of_int i *. 0.5 +. r *. 0.5, d *. 0.5), [])
    | (A.N(A.UnifVar _, _), _) -> A.N(A.PPReal (0.0, 1.0), [])
    | (_, A.N(A.UnifVar _, _)) -> A.N(A.PPReal (0.0, 1.0), [])
    | (next_tn, next_sub) -> A.N(A.At, [A.FreeVar "i/c"; next_tn; next_sub])
  )
  | A.N(A.At, [A.FreeVar "succ"; n; ]) -> (
    match (special_pp n)  with
    | (A.N(A.PPInt i, [])) -> A.N(A.PPInt (i+1), [])
    | _ -> A.N(A.At, [A.FreeVar "succ"; n])
  )
  | A.N(A.At, [A.FreeVar "scons"; n; nt]) -> (
    match (special_pp nt)  with
    | (A.N(A.PPList, elems)) -> A.N(A.PPList, (special_pp n) :: elems)
    | other -> A.N(A.PPList, (special_pp n) :: [other])
  )
  | A.N(A.UnifVar _, []) -> tm
  | _ -> (
    print_endline ("WARNING: ast105: special_pp: not implemented for term "  ^ A.ds_abt tm);
    tm
  )

let special_pp_top_level (lg : A.decls) (tm: A.abt) : string = 
  special_pp tm |> pp_abt lg