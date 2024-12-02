module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode
module AOps = CoLFAbtOps.CoLFAbtOps
module Errors = Errors.Errors
module PP = PrettyPrint.PrettyPrint

module type TYPE_CHECKING_CTX = sig
  type t
  type ctx_state = Consistent | Inconsistent | Undetermined

  val empty_ctx : unit -> t
  val add_local_type_decl : t -> string -> A.t -> t
  val add_global_type_decl : t -> string -> A.t -> t
  val add_global_rec_defs : t -> (string * A.t) list -> t
  (* you must add type decl for rec defs first *)

  val find_type_decl : t -> string -> A.t option
  val find_global_rec_def : t -> string -> A.t option
  (* val lookup_type_decl : t -> string -> A.t *)

  val get_all_local_names : t -> string list

  val get_all_global_names : t -> string list
  val get_all_names : t -> string list

  val assert_eq_true : t -> A.t * A.t -> unit (* only returns true if the result context is definitely consistent *)

  val is_ctx_definitely_consistent : t -> bool
  val get_ctx_state : t -> ctx_state

  val show_ctx_view : t -> (A.t -> string) option -> string
  (* only show the most recent type decl, useful for printing error messages *)
  val show_ctx_view_top : t -> string
end

module type EQUALITY_CTX = sig
  type t
  val empty_ctx : unit -> t
  val add_equation : t -> A.t * A.t -> t
  val is_eqn_present : t -> A.t * A.t -> bool
  val is_hd_present : t -> string * string -> bool
  val show_eq_ctx : t -> string
end

module EqualityCtx : EQUALITY_CTX = struct
  type t= (A.t * A.t) list

  let empty_ctx () : t = []

  let show_eq_ctx (ctx : t) : string = 
    String.concat "," (List.map (fun (lhs, rhs) -> A.show_view lhs ^ " = " ^ A.show_view rhs) ctx)

  (* let show_eq_ctx_raw (ctx : t) : string = 
    String.concat "," (List.mapi (fun i (lhs, rhs) -> string_of_int i ^ ": " ^ A.show_raw lhs ^ " = " ^ A.show_raw rhs) ctx) *)

  let add_equation (ctx : t) (eqn : A.t * A.t) : t = 
    eqn :: ctx
  
  let is_eqn_present (ctx : t) (eqn : A.t * A.t) : bool =
    let result = List.exists (fun (lhs, rhs) -> A.eq_abt lhs (fst eqn) && A.eq_abt rhs (snd eqn)) ctx in
    (* let _ = print_endline ("is_eqn_present [" ^ string_of_bool result ^ "], eqn : " ^ A.show_view (fst eqn) ^ " = " ^ A.show_view (snd eqn) ^ " in " ^ show_eq_ctx ctx) in
    let _ = print_endline ("is_eqn_present [" ^ string_of_bool result ^ "], eqn : " ^ A.show_raw (fst eqn) ^ " = " ^ A.show_raw (snd eqn) ^ " in " ^ show_eq_ctx_raw ctx) in *)
    result

  let is_hd_present (ctx : t) (hd : string * string) : bool =
    List.exists (fun (lhs, rhs) -> 
      match (A.view lhs, A.view rhs) with
      | A.N(N.Ap, ([], hd1)::_), A.N(N.Ap, ([], hd2)::_) -> 
          (match A.view hd1, A.view hd2 with
          | A.FreeVar name1, A.FreeVar name2 -> name1 = fst hd && name2 = snd hd
          | _ -> false
          )
      | _ -> false
    ) ctx


end


module TypeCheckingCtx : TYPE_CHECKING_CTX = struct
  type ctx_state = Consistent | Inconsistent | Undetermined
  type t = {
    local_type_decls : (string * A.t) list;
    global_type_decls : (string * A.t) list;
    global_rec_defs : (string * A.t) list;
    internal_rec_defs : (string * A.t) list; (* used for flattening and unification *)
    ctx_state : ctx_state;
  }

  let local_rec_def_prefix = "__r_"

  let empty_ctx () : t = {
    local_type_decls = [];
    global_type_decls = [];
    global_rec_defs = [];
    internal_rec_defs = [];
    ctx_state = Consistent;
  }

  let find_type_decl (ctx : t) (name : string) : A.t option = 
    List.assoc_opt name (ctx.local_type_decls @ ctx.global_type_decls)

  let find_global_rec_def (ctx : t) (name : string) : A.t option =
    List.assoc_opt name ctx.global_rec_defs

  let find_internal_rec_def (ctx : t) (name : string) : A.t option =
    List.assoc_opt name ctx.internal_rec_defs

  let find_rec_def (ctx : t) (name : string) : A.t option = 
    match find_global_rec_def ctx name with
    | Some def -> Some def
    | None -> find_internal_rec_def ctx name

  let show_ctx_view (ctx : t) (tm_view : (A.t -> string) option) : string = 
    let show_tm = (match tm_view with
    | Some f -> f
    | None -> A.show_view) in
    let show_type_decl (name, tp) = 
      match find_global_rec_def ctx name with
      | Some def -> name ^ " : " ^ show_tm tp ^ " = " ^ show_tm def
      | None -> name ^ " : " ^ show_tm tp
    in
    let show_rec_def (name, def) = 
      name ^ " = " ^ show_tm def
    in
    let local_type_decls_str = String.concat "\n" (List.map show_type_decl ctx.local_type_decls) in
    let global_type_decls_str = String.concat "\n" (List.map show_type_decl ctx.global_type_decls) in
    let internal_rec_defs_str = String.concat "\n" (List.map show_rec_def ctx.internal_rec_defs) in
    local_type_decls_str ^ "\n" ^ global_type_decls_str ^ "\n" ^ internal_rec_defs_str

  let show_ctx_view_top (ctx : t) : string = 
    match ctx.local_type_decls with
    | [] -> (
      match ctx.global_type_decls with
      | [] -> ""
      | (name, tp) :: _ -> 
          "" ^ name ^ " : " ^ A.show_view tp
    )
    | (name, tp) :: _ -> 
        "" ^ name ^ " : " ^ A.show_view tp
  

  let get_all_local_names (ctx : t) : string list = 
    List.map fst ctx.local_type_decls

  let get_all_global_names (ctx : t) : string list = 
    let type_decl_names = List.map fst ctx.global_type_decls in
    type_decl_names
  
  let get_all_internal_names (ctx: t) : string list = 
    List.map fst ctx.internal_rec_defs

  let get_all_names (ctx : t) : string list = 
    let local_names = get_all_local_names ctx in
    let global_names = get_all_global_names ctx in
    let internal_names = get_all_internal_names ctx in
    local_names @ global_names @ internal_names

  let assert_bool (b : bool) (s : string) : unit = 
    if not b then Errors.raise_with_explicit_extent None s else ()

  let add_local_type_decl (ctx : t) (name : string) (tp : A.t) : t = 
    let _ = assert_bool (not (List.mem name (get_all_names ctx))) "Local type declaration already exists" in
    { ctx with local_type_decls = (name, tp) :: ctx.local_type_decls }

  let add_global_type_decl (ctx : t) (name : string) (tp : A.t) : t =
    let _ = assert_bool (List.is_empty ctx.local_type_decls) "Cannot add global type decl when local type decls exist" in
    let _ = assert_bool (not (List.mem name (get_all_names ctx))) ("Global type declaration already exists: " ^ name ^ " in context " ^ show_ctx_view ctx None) in
    { ctx with global_type_decls = (name, tp) :: ctx.global_type_decls }

  let add_internal_rec_def (ctx: t) (def: A.t) : string * t = 
    let name = local_rec_def_prefix ^ string_of_int (List.length ctx.internal_rec_defs) in
    let new_ctx = { ctx with internal_rec_defs = (name, def) :: ctx.internal_rec_defs } in
    (name, new_ctx)


  (* TODO: we might need to check contractiveness of all defs once a new rec def is added *)
  let add_global_rec_defs (ctx : t) (defs : (string *  A.t) list) : t = 
    let all_names = List.map fst defs in
    let _ = assert_bool (List.length (ListUtil.remove_duplicates (all_names)) = List.length all_names) "Global rec def names must be unique" in
    let _ = List.map (fun name -> 
      let _ = assert_bool (List.mem name (get_all_global_names ctx)) "Recursive definition must have a corresponding type declaration" in
      let _ = assert_bool (not (List.mem_assoc name ctx.global_rec_defs)) "Recursive definition already exists" in
      let _ = assert_bool (not (List.mem_assoc name ctx.internal_rec_defs)) "Rec def name clashes with internal ones, repick your name" in
      let _ = assert_bool (List.is_empty ctx.local_type_decls) "Cannot add global rec def when local type decls exist" in
      ()
    ) all_names in
    (* ctx ref for use in the below two functions *)
    let ctx_ref = ref ctx in
    (* TODO have a systematic way to handle free vars *)
    let rec transform_into_contractive  (def: A.t) : A.t =
      (* let _ = print_endline ("transform_into_contractive: " ^ A.show_view def) in *)
      match A.view def with
      | A.N(N.Ap, ([], hd)::spine) -> (
        match A.view hd with
        | A.FreeVar(hd_var) -> (
          match find_global_rec_def ctx hd_var with
          | None -> A.fold(A.N(N.Ap, ([], hd)::(List.map (fun x -> ([], transform_into_recursive (snd x))) spine)))
          | Some hd_def -> 
            let expanded_def = AOps.apply_spine_to_lambda hd_def (List.map snd spine) in 
            transform_into_contractive expanded_def
        )
        | _ -> failwith "transform_into_contractive: head of rec def is not a free var"
      )
      | A.N(N.Lam, [([name], body)]) -> A.fold(A.N(N.Lam, [([name], transform_into_contractive body)]))
      | _ -> failwith ("transform_into_contractive: not implemented for this kind of rec def "  ^ A.show_view def)
    and transform_into_recursive (def: A.t) : A.t = 
      (* let _ = print_endline ("transform_into_recursive: " ^ A.show_view def) in *)
      match A.view def with
      | A.N(N.Ap, ([], hd)::_) -> (
        match A.view hd with
        | A.FreeVar(hd_var) -> (
          if List.mem hd_var all_names then def else
          match find_rec_def ctx hd_var with
          | Some _ ->  def
          | None -> (
            let free_vars = ListUtil.minus (A.get_free_vars def) (get_all_names !ctx_ref) in
            let abstracted_def = AOps.construct_iterative_lambda free_vars def in
            let underlying_tm = transform_into_contractive abstracted_def in
            let (new_name, new_ctx) = add_internal_rec_def !ctx_ref underlying_tm in
            (* let _ = print_endline ("added internal rec def " ^ new_name ^ " = " ^ A.show_view underlying_tm) in *)
            ctx_ref := new_ctx;
            A.fold(A.N(N.Ap, ([], A.free_var new_name)::(List.map (fun x -> ([], A.free_var(x))) free_vars)))
          )
        )
        | _ -> failwith "transform_into_recursive: head of rec def is not a free var"
      )
      | A.FreeVar(x) -> transform_into_recursive (A.fold(A.N(N.Ap, ([], A.free_var x)::[])))
      | A.N(N.Lam, [([name], body)]) -> A.fold(A.N(N.Lam, [([name], transform_into_recursive body)]))
      | _ -> failwith ("transform_into_recursive: not implemented for this kind of rec def" ^ A.show_view def)
    in
    let transformed_defs = List.map (fun (name, def) -> (name, transform_into_recursive def)) defs in
    (* let _ = print_endline (
      "add_global_rec_defs: " ^ String.concat " " (List.map (fun (name, def) -> name ^ " = " ^ A.show_view def) defs) ^ 
      "transformed_defs: " ^ String.concat " " (List.map (fun (name, def) -> name ^ " = " ^ A.show_view def) transformed_defs)) in *)
    { !ctx_ref with global_rec_defs = transformed_defs@ctx.global_rec_defs }


  (* let lookup_type_decl (ctx : t) (name : string) : A.t = 
    match find_type_decl ctx name with
    | Some tp -> tp
    | None -> failwith ("lookup_type_decl: type declaration not found " ^ name) *)

  let rec assert_eq_true_rec (eq_ctx: EqualityCtx.t) (ctx : t) (lhs, rhs : A.t * A.t) : unit = 
    (* let _ = print_endline ("assert_eq_true_rec: " ^ A.show_view lhs ^ " = " ^ A.show_view rhs ^ " in " ^ EqualityCtx.show_eq_ctx eq_ctx) in *)
    Errors.try_with_error ( fun _ -> 
      if A.eq_abt lhs rhs then ()
      else
    match (A.view lhs, A.view rhs) with
    | A.FreeVar name1, _ -> 
      assert_eq_true_rec eq_ctx ctx (A.fold(A.N(N.Ap, ([], A.free_var name1)::[])), rhs)
    | _, A.FreeVar name2 ->
      assert_eq_true_rec eq_ctx ctx (lhs, A.fold(A.N(N.Ap, ([], A.free_var name2)::[])))
    | A.N(N.Ap, ([], hd1)::spine1), A.N(N.Ap, ([], hd2)::spine2) -> 
      (
        if EqualityCtx.is_eqn_present eq_ctx (lhs, rhs) then ()
        else
        match A.view hd1, A.view hd2 with
        | A.FreeVar name1, A.FreeVar name2 -> 
          (
          match find_rec_def ctx name1, find_rec_def ctx name2 with
          | None, None -> (
            if name1 <> name2 then Errors.raise_with_explicit_extent None ("Not equal: " ^ name1 ^ " <> " ^ name2) else
            let _ = assert_bool (List.length spine1 = List.length spine2) ("assert_eq_true: node arity mismatch: " 
            ^ string_of_int (List.length spine1) ^ " not eq " ^ string_of_int (List.length spine2) ^ " in " ^ PP.show_term lhs ^ " ?= " ^ PP.show_term rhs) in
            let _ = List.iter2 (fun (ctx1, tm1) (ctx2, tm2) -> 
              let _ = assert_bool (List.length ctx1 = List.length ctx2) "assert_eq_true: context arity mismatch" in
              let tm2' = List.fold_right2 (fun t1_name t2_name tm2' -> A.subst (A.free_var t1_name) t2_name tm2') ctx1 ctx2 tm2 in
              assert_eq_true_rec eq_ctx ctx (tm1, tm2')
              ) spine1 spine2 in
              ()
          )
          | Some def1, None -> (
            let def1expanded = AOps.apply_spine_to_lambda def1 (List.map snd spine1) in
            assert_eq_true_rec eq_ctx ctx (def1expanded, rhs)
          )
          | None, Some def2 -> (
            let def2expanded = AOps.apply_spine_to_lambda def2 (List.map snd spine2) in
            let _ = print_endline ("expanding rhs " ^ A.show_view rhs  ^ " def " ^ name2 ^ " from " ^ A.show_view def2 ^ " with spine " ^ String.concat " " (List.map (fun x -> A.show_view (snd x)) spine2)
            ^ " to " ^ A.show_view def2expanded) in
            assert_eq_true_rec eq_ctx ctx (lhs, def2expanded)
          )
          | Some def1, Some def2 -> (
            let expand_and_continue () = 
                let new_eqctx = EqualityCtx.add_equation eq_ctx (lhs, rhs) in
                let def1expanded = AOps.apply_spine_to_lambda def1 (List.map snd spine1) in
                let def2expanded = AOps.apply_spine_to_lambda def2 (List.map snd spine2) in
                assert_eq_true_rec new_eqctx ctx (def1expanded, def2expanded)
            in
            if AOps.check_spine_is_simple (List.map snd spine1) && AOps.check_spine_is_simple (List.map snd spine2)
              then
                expand_and_continue ()
              else
                if EqualityCtx.is_hd_present eq_ctx (name1, name2) then 
                  failwith ("assert_eq_true: cannot determine the equality of rec defs " ^ name1 ^ " " ^ name2 ^ " not in pattern fragment with limited expansion. Terms: " ^ A.show_view lhs ^ " " ^ A.show_view rhs)
                else
                  expand_and_continue ()


          )
          )
        | _ -> Errors.raise_with_explicit_extent None ("assert_eq_true: head of application is not a free var " ^ A.show_view lhs ^ " " ^ A.show_view rhs)
      )
    | A.N(N.Ap, _), A.N(N.Pi, _) -> Errors.raise_with_explicit_extent None ("Not equal: " ^ PP.show_term lhs ^ " <> " ^ PP.show_term rhs)
    | A.N(N.Pi, _), A.N(N.Ap, _) -> Errors.raise_with_explicit_extent None ("Not equal: " ^ PP.show_term lhs ^ " <> " ^ PP.show_term rhs)
    | A.N(N.Lam, [[x1], body1]), A.N(N.Lam, [[x2], body2]) -> 
      ( let body2' = A.subst (A.free_var x1) x2 body2 in
        assert_eq_true_rec eq_ctx ctx (body1, body2')
      )
    | _ -> failwith ("assert_eq_true: not implemented for " ^ PP.show_term lhs ^ " ?= " ^ PP.show_term rhs) 
    (* | A.N(nt1, args1), A.N(nt2, args2) -> 
        if nt1 <> nt2 then failwith ("assert_eq_true: node types are not equal" ^ A.show_view lhs ^ " " ^ A.show_view rhs) else
        ()

        *)
    ) None ("when eq checking " ^ PP.show_term lhs ^ " = " ^ PP.show_term rhs)



  let assert_eq_true (ctx : t) (lhs, rhs : A.t * A.t) : unit = 
    let _ = assert_eq_true_rec (EqualityCtx.empty_ctx()) ctx (lhs, rhs) in
    ()
    
    

  let is_ctx_definitely_consistent (ctx : t) : bool = 
    ctx.ctx_state = Consistent

  let get_ctx_state (ctx : t) : ctx_state = 
    ctx.ctx_state
  
end
