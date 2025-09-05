
type node = 
   Pi  (* [T; x.T2]*)
  | Lam (* [x.M] *)
  | Type (* [] *)
  | CoType (* [] *)
  | Kind (* [] *)
  | At (* argument count *) (* [M; N_1; ... ; N_i] *)
  | UnifVar of int (* number, pretty print name *) (* [] *)
  | LPFail (* [] *)
  | LPPending (* [] *)
  | PPInt of int (* [] *)
  | PPReal of float (* absolute *) * float (* plus minus *) (* [] *) 
  | PPList 
  [@@deriving show, eq]


type abt =
   FreeVar of string
  | BoundVar of int (* starts with 1, so \x.x = \x.1 *)
  | N of node * abt list
  | Bnd of string option * abt
  [@@deriving show, eq]

(* type dec = Decl of string * abt
  [@@deriving show] *)


type decl = (string * abt) 
type decls = decl list

type ssig = {
  decls : (string * abt) list;
  cmds : (string * abt) list;
}



let rec ds_decls ( dl : (string * abt) list) : string = 
  String.concat ".\n" (List.map ds_decl dl)
and ds_decl (d : (string * abt)) : string = 
match d with
  | (c, a) ->  c ^ " : " ^ ds_abt a
and ds_abt (a: abt) : string = 
  match a with
    | FreeVar(name) -> name
    | Bnd(name, sub) -> 
      (match name with
        | Some n -> n
        | None -> "_") ^ "." ^ ds_abt sub
    | BoundVar(i) -> string_of_int i
    | N(node, tl) -> ds_node node ^ ds_abts tl
and ds_abts (tl : abt list) : string =
  "[" ^ String.concat "; " (List.map ds_abt tl) ^ "]"
and ds_node (n : node) : string = 
  match n with
  | Pi -> "Π"
  | Lam -> "λ"
  | Type -> "Type"
  | CoType -> "CoType"
  | Kind -> "Kind"
  | At -> "ap"
  | UnifVar i -> "?(" ^ string_of_int i ^ ")"
  | LPFail -> "LPFail"
  | LPPending -> "LPPending"
  | PPInt i -> "PPInt(" ^ string_of_int i ^ ")"
  | PPReal (r,d) -> "PPReal(" ^ string_of_float r ^ ", " ^ string_of_float d ^ ")"
  | PPList -> "PPList"
  
  

let empty_ssig : ssig = {
  decls = [];
  cmds = [];
}

let kind_expr = N(Kind, [])

let ap_l (abtl : abt list) = 
  match abtl with
  | (FreeVar _)::_ -> N(At, abtl)
  | (BoundVar _)::_ -> N(At, abtl)
  | (N(At, l1)::l2) -> N(At, l1 @ l2)
  | _ -> N(At, abtl)
  (* | _ -> failwith ("ast: ap: first element should be a variable, got " ^ show_abt (List.hd abtl)) *)

let abstract_over (x : string) (tree : abt) : abt = 
  let rec rec_with_binder_num(n : int) ( tree : abt) : abt = 
    match tree with
    | FreeVar(name) -> (if name = x then BoundVar(n) else FreeVar(name))
    | Bnd(name, sub) -> Bnd(name, rec_with_binder_num (n + 1) sub)
    | BoundVar(_) -> tree
    | N(node, tl) -> N(node, List.map (rec_with_binder_num n) tl)
    in 
  Bnd(Some x, rec_with_binder_num 1 tree)


let abstract_over_no_name  (tree : abt) : abt = 
  Bnd(None, tree)


let instantiate_bound_var_no_repeat (inst_var : string) (bound_expr : abt) = 
  let rec subst_expr_at_bnd_level(lvl: int) (expr: abt) = 
    match expr with
    | Bnd(Some name, sub) -> 
        if name = inst_var 
          then Bnd(Some (Uid.next_name name), subst_expr_at_bnd_level (lvl + 1) sub)
          else Bnd(Some name, subst_expr_at_bnd_level (lvl + 1) sub)
    | Bnd(None, sub) -> Bnd(None, subst_expr_at_bnd_level (lvl + 1) sub)
    | FreeVar(name) -> if name = inst_var then failwith "ast54: instantiate_bound_var_no_repeat: repeated variable" else FreeVar(name)
    | BoundVar(n) -> if n = lvl then FreeVar(inst_var) else BoundVar(n)
    | N(node, tl) -> N(node, List.map (subst_expr_at_bnd_level lvl) tl)
  in 

  match bound_expr with
  | Bnd(_, expr) -> subst_expr_at_bnd_level 1 expr
  | _ -> failwith ("ast65: instantiate_expr: not a bound expression, got " ^ show_abt bound_expr)


let collect_free_vars (expr : abt) : string list = 
  let rec rec_collect_free_vars (expr : abt) : string list = 
    match expr with
    | FreeVar(name) -> [name]
    | Bnd(_, sub) -> rec_collect_free_vars sub
    | BoundVar(_) -> []
    | N(_, tl) -> List.concat (List.map rec_collect_free_vars tl)
  in 
  List.sort_uniq String.compare (rec_collect_free_vars expr)

let appears_in_expr (name : string) (expr : abt) : bool = 
  List.mem name (collect_free_vars expr)

let collect_free_unif_vars (expr: abt) : int list = 
  let rec rec_collect_free_unif_vars (expr : abt) : int list = 
    match expr with
    | FreeVar(_) -> []
    | Bnd(_, sub) -> rec_collect_free_unif_vars sub
    | BoundVar(_) -> []
    | N(node, tl) -> 
        (
          match node with
          | UnifVar(i) -> [i] @ List.concat (List.map rec_collect_free_unif_vars tl)
          | _ -> List.concat (List.map rec_collect_free_unif_vars tl)
        )
  in 
  List.sort_uniq compare (rec_collect_free_unif_vars expr)

let unbind_expr ?(avoid_list: string list = []) (bound_expr : abt) : string * abt = 
  match bound_expr with
  | Bnd(possible_name, sub) -> 
      let should_renew_condition (name : string) : bool = appears_in_expr name sub || List.mem name avoid_list in
      let rec get_name () = 
          let candidate = (
            match possible_name with
              | Some name -> (
                if appears_in_expr name sub || List.mem name avoid_list
                  then Uid.next_name name
                  else name
              )
              | None -> Uid.next_name "x"
          ) in
          if should_renew_condition candidate 
            then get_name ()
            else candidate
      in 
      let name = get_name () in
      (name, instantiate_bound_var_no_repeat name bound_expr)
  | _ -> failwith "ast86: unbind_expr: not a bound expression"

let instantiate_expr (inst_expr : abt) (bound_expr: abt) = 
  let rec subst_expr_at_bnd_level(lvl: int) (expr: abt) = 
    match expr with
    | Bnd(name, sub) -> Bnd(name, subst_expr_at_bnd_level (lvl + 1) sub)
    | FreeVar(name) -> FreeVar(name)
    | BoundVar(n) -> if n = lvl then inst_expr else BoundVar(n)
    | N(node, tl) -> N(node, List.map (subst_expr_at_bnd_level lvl) tl)
  in 

  match bound_expr with
  | Bnd(_, expr) -> subst_expr_at_bnd_level 1 expr
  | _ -> failwith ("ast48: instantiate_expr: not a bound expression, got " ^ show_abt bound_expr)

let rec hereditary_instantiate_expr (inst_expr : abt) (bound_expr : abt) = 
  let rec hered_subst (e2 : abt) (x : string) (e1 : abt) = 
    match e1 with
    | FreeVar(name) -> if name = x then e2 else e1
    | Bnd(_) -> (
        let (new_name, new_sub) = unbind_expr e1 in
        let new_sub' = hered_subst e2 x new_sub in
        abstract_over new_name new_sub'
    )
    | BoundVar(_) -> failwith "ast61: hered_subst: bound variable should not appear in the output"
    | N(At, hd::spine) -> 
        (
          let rec feed_spine (hd : abt) (spine : abt list) = 
            match spine with
            | [] -> hd
            | (spine_hd :: spine_tl) -> 
              (
                match hd with
                | N(Lam, [arg]) -> feed_spine (hereditary_instantiate_expr spine_hd arg) spine_tl
                | _ -> ap_l ([hd] @ spine)
              )
            in 
          feed_spine (hered_subst e2 x hd) (List.map (hered_subst e2 x) spine)
        )
    | N(node, tl) -> N(node, List.map (hered_subst e2 x) tl)
  in
  match bound_expr with
  | Bnd(_) -> let (bnd_name, bnd_sub) = unbind_expr bound_expr in 
              let new_sub = hered_subst inst_expr bnd_name bnd_sub in
              (* let _ = print_endline ("subst " ^ (ds_abt inst_expr) ^ " in \t" ^ (ds_abt (bound_expr)) ^ " results in " ^ (ds_abt new_sub)) in *)
              new_sub
  | _ -> failwith ("ast63: instantiate_expr: not a bound expression, got " ^ show_abt bound_expr)


let subst (e2 : abt) (x : string) (e1 : abt) = 
  instantiate_expr e2 (abstract_over x e1)

let hereditary_subst (e2 : abt) (x : string) (e1 : abt) = 
  hereditary_instantiate_expr e2 (abstract_over x e1)


let abstract_over_list (l : string list) (tree : abt) : abt = 
  List.fold_right abstract_over l tree

let instantiate_expr_list (inst_expr : abt list) (bound_expr: abt) = 
  List.fold_left (fun acc x -> instantiate_expr x acc) bound_expr inst_expr

let subst_list (e2 : abt list) (x : string list) (e1 : abt) = 
  instantiate_expr_list e2 (abstract_over_list x e1)

let map_abt (f : abt -> abt) (tree : abt) : abt = 
  match tree with
  | FreeVar(name) -> FreeVar(name)
  | Bnd(_, _) -> let (name, sub) = unbind_expr tree in 
            abstract_over name (f sub)
  | BoundVar(_) -> failwith "ast105: map_abt: bound variable should not appear in the output"
  | N(node, tl) -> N(node, List.map (f) tl)
  

