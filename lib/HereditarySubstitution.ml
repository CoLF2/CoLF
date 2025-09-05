(* 
module A = Ast

let debug = Flags.hs_debug

let rec eta_expand (tm : A.tm) (tp : A.weaktp) : A.tm = 
  (* let rec count_n_pi (tp : A.weaktp) = 
    match tp with
    | A.Arr(_, t1) -> count_n_pi t1 + 1
    | A.Atom -> 0
    (* | A.WeakTpUnivar _ -> failwith "unif75: cannot eta expand with unbound univar" *)
    | A.WeakTpUnivar _ -> 0
  in 
  let rec count_n_lam (tm : A.tm) = 
    match tm with
    | A.Atm _ -> 0
    | A.Lam(_, b) -> 1 + count_n_lam b
  in *)
  (let rec append_spine (tm : A.tm) (add : A.tm) = 
    match tm with
    | A.Lam(x, b) -> A.Lam(x, append_spine b add)
    | A.Atm(h, s) -> A.Atm(h, s@[add])
  in 
  match (tm, tp) with
  | (A.Lam(z, b), A.Arr(_, t1)) -> A.Lam(z, eta_expand b t1)
  | (A.Atm(_), A.Arr(t2, t1)) -> 
        let z = Uid.nextz() in
        A.Lam(A.Prvd z, eta_expand (append_spine tm (eta_expand (A.Atm(A.Prvd z, [])) t2)) t1)
  | (_, A.Atom) -> tm
  | (_, A.WeakTpUnivar _) -> tm
  )

  (* let n_expand = count_n_pi tp - count_n_lam tm in
  if n_expand <= 0
  then tm
  else 
    let rec collect (n : int) (tp : A.weaktp) = 
      if n <= 0 then []
      else
        match tp with
        | A.Arr(t2, t1) -> t2 :: collect (n-1) t1
        | _ -> failwith "unif96"
      in 
    let tps = collect n_expand tp in
    let res = 
    List.fold_right (fun tp tm -> 
      let z = Uid.nextz() in
        A.Lam(A.Prvd z, append_spine tm (eta_expand (A.Atm(A.Prvd z, [])) tp))
      ) tps tm in 
    (* let _ = print_endline ("unif104: the expansion of " ^ A.ds_tm tm ^ " at index " ^ A.ds_weaktp tp ^ " is " ^ A.ds_tm res) in  *)
    res *)

let rec removes_spine_tail (y : A.id) (m : A.tm) : A.tm  = match m with
    | A.Lam(_) -> failwith "cannot remove spine tail on non-atomic types"
      (* A.Lam (z, removes_spine_tail y b) *)
    | A.Atm(h, s) -> 
      let last = List.nth s (List.length s -1) in
      (match hered_eta_contract last with
      | A.Atm(h', []) -> if h' = y then A.Atm(h, Core.List.take s (List.length s -1))
      else raise (Failure "Cannot eta-contract lambda, last element does not match abstraction")
      | _ -> raise (Failure ("Cannot eta-contract lambda, last element does not match abstraction"))
        )
      (* contracts lambdas with tail spines until reaches atomic *)
and hered_eta_contract  (m : A.tm) : A.tm = match m with
| A.Atm _ -> m
| A.Lam(A.Placeholder, _) -> failwith "unexpected placeholder"
| A.Lam(x, ((A.Atm _ ) as b)) -> hered_eta_contract (removes_spine_tail x b)
| A.Lam(x, ((A.Lam _) as b)) -> hered_eta_contract (A.Lam (x, hered_eta_contract b))
    
let rec occurs_in_tm (y : A.id) (m : A.tm) : bool = 
  match y with
  | A.Placeholder -> false
  | _ -> (
    match m with
    | A.Lam(x, b) -> if x = y then false else occurs_in_tm y b 
    | A.Atm(h, s) -> if h = y then true else occurs_in_spine y s 
  )
and occurs_in_spine (y : A.id) (s : A.tm list) : bool = 
      List.exists (occurs_in_tm y) s

(* let any_occurs_in_spine (l : A.id list) (s : A.tm list) : bool = 
  List.exists (fun z -> occurs_in_spine z s) l *)

(* whether y occurs as a prvd *)
let rec occurs_in_tp (y : A.id) (m : A.tp) : bool = 
  match y with
  | A.Placeholder -> false
  | _ -> (
      match m with
      | A.Pi(x, t2, t1) -> if x = y then false else occurs_in_tp y t2 || occurs_in_tp y t1
      | A.Atp(h, s) -> if h = y then true else List.exists (occurs_in_tm y) s
      | Type _ -> false
      | CoType _ -> false
  )

let rec rename_in_tm (y : A.id) (x : A.id) (m : A.tm) : A.tm = 
  match y with
  | A.Placeholder -> failwith "cannot rename to a placeholder"
  | A.Gen _ -> failwith "cannot rename to a gen"
  | A.Prvd _ ->
      (match x with
        | A.Placeholder -> m
        | A.Gen _ -> failwith "warning: Gen subst hs7"
        | A.Prvd _ ->
          (match m with
          | A.Lam(z, b) -> if z = x then A.Lam(z, b) else 
                if z = y then (let z' = A.Prvd (Uid.nextz()) in 
                              let b = rename_in_tm z' z b in
                              let b = rename_in_tm y x b in
                              A.Lam(z', b)
                )
                        else  A.Lam(z, rename_in_tm y x b)
          | A.Atm(h, s) -> if x = h 
            then A.Atm(y, List.map (rename_in_tm y x) s) 
            else A.Atm(h, List.map (rename_in_tm y x) s) 
          )
      )

let rec rename_in_tp (y : A.id) (x : A.id) (m : A.tp) : A.tp = 
  match y with
  | A.Placeholder -> failwith "cannot rename to a placeholder"
  | A.Gen _ -> failwith "cannot rename to a gen"
  | A.Prvd _ ->
      (match x with
        | A.Placeholder -> m
        | A.Gen _ -> failwith "warning: Gen subst hs7"
        | A.Prvd _ ->
          (match m with
            | A.Pi(b, t2, t1) -> if b = x then A.Pi(b, t2, t1) else 
                if b = y then (let b' = A.Prvd (Uid.nextz()) in 
                              let t1 = rename_in_tp b' b t1 in
                              let t1 = rename_in_tp y x t1 in
                              let t2 = rename_in_tp y x t2 in
                              A.Pi(b', t2, t1)
                )
                        else  A.Pi(b, rename_in_tp y x t2, rename_in_tp y x t1)
            | A.Atp(h, s) -> if x = h 
                            then A.Atp(y, List.map (rename_in_tm y x) s) 
                            else A.Atp(h, List.map (rename_in_tm y x) s) 
            | A.Type p -> A.Type p
            | A.CoType p -> A.CoType p
          )
      )
let rec rename_feed_spine_tm (s : A.id list) (into : A.tm)   : A.tm = 
  let _ = if debug then print_endline ("rename_feed_spine feeding " ^ String.concat "," (List.map A.ds_id s) ^ " into " ^ A.ds_tm into ) else () in
  (match (s, into) with
  | ([], A.Atm _ ) -> into
  | ([], _) -> into 
  | ((sh:: st), A.Lam(z, b)) -> 
      let b = rename_in_tm sh z b in 
      rename_feed_spine_tm st b
  (* | ((_ :: _), A.Atm _, A.Arr(_)) ->  (* Hack of dealing eta-expansions as a result of unification e.g. Pi x : u. c x, and u gets unified with pi, but x does not expand during resolution*)
      h_sub_feed_spine s (eta_expand into (A.Arr(A.Atom, A.Atom))) index *)
  | _ -> failwith ("hs154: rename feed spine length mismatch") (* maybe uncomment previous *)
  )

let rec h_sub_feed_spine (s : A.tm list) (into : A.tm) (index : A.weaktp)  : A.tm = 
  let _ = if debug then print_endline ("h_sub feeding " ^ A.ds_spine s ^ " into " ^ A.ds_tm into ^ " at index " ^ A.ds_weaktp index) else () in
  (match (s, into, index) with
  | ([], A.Atm _, A.Atom) -> into
  | ([], _, _) -> into (*Hack to circumvent eta-expansion TODO: fix this??*)
  | ((sh:: st), A.Lam(z, b), A.Arr(t2, t1)) -> 
      let b = h_sub_in_tm sh t2 z b in 
      h_sub_feed_spine st b t1
  | ((_ :: _), A.Atm _, A.Arr(_)) ->  (* Hack of dealing eta-expansions as a result of unification e.g. Pi x : u. c x, and u gets unified with pi, but x does not expand during resolution*)
      h_sub_feed_spine s (eta_expand into (A.Arr(A.Atom, A.Atom))) index
  | _ -> failwith ("h_sub 80 : type mismatch, cannot sub (feed) " ^ A.ds_spine s ^ " into " ^ A.ds_tm into ^ " at index " ^ A.ds_weaktp index)
  )

(* substitutes both generated var and bound var*)
and h_sub_in_tm (n : A.tm) (index : A.weaktp) (x : A.id) (m : A.tm) : A.tm = 
  let _ =  if debug then print_endline ("h_sub substituting tm " ^ A.ds_tm n ^ " for " ^ A.ds_id x ^ " into tm " ^ A.ds_tm m ^ " at index " ^ A.ds_weaktp index) else () in
  try(
  (match x with
    | A.Placeholder -> m
    (* | A.Gen _ -> failwith "warning: Gen subst hs7" *)
    | (A.Prvd _ | A.Gen _) ->
        (match m with
        | A.Lam(z, b) -> 
            if z = x then m else
            if occurs_in_tm z n then 
              (* capture avoid *)
              (let z' = A.Prvd (Uid.nextz()) in 
               let b = rename_in_tm z' z b in
               let b = h_sub_in_tm n index x b in
               A.Lam(z', b)
              )
            else A.Lam(z, h_sub_in_tm n index x b)
        | A.Atm(h, s) -> 
            if x = h then (
              let s = List.map (h_sub_in_tm n index x ) s in
              h_sub_feed_spine s n index
            )
            else A.Atm(h, List.map (h_sub_in_tm n index x) s)
        )
  )

  ) with Failure r -> raise (Failure (r ^ "\n when substituting tm " ^ A.ds_tm n ^ " for " ^ A.ds_id x ^ " into tm " ^ A.ds_tm m ^ " at index " ^ A.ds_weaktp index))


let rec h_sub_in_tp (n : A.tm) (index : A.weaktp) (x : A.id) (m : A.tp) : A.tp = 
  let _ = if debug then  print_endline ("h_sub substituting tm " ^ A.ds_tm n ^ " for " ^ A.ds_id x ^ " into tp " ^ A.ds_tp m ^ " at index " ^ A.ds_weaktp index) else () in
  try(
  (match x with
    | A.Placeholder -> m
    (* | A.Gen _ -> failwith "warning: Gen subst hs7" *)
    | (A.Prvd _ | A.Gen _ )->
        (match m with
        | (A.CoType _ | A.Type _) -> m
        | A.Pi(z, t2, t1) -> 
            if z = x then m else
            if occurs_in_tm z n then 
              (* capture avoid *)
              (let z' = A.Prvd (Uid.nextz()) in 
               let t1 = rename_in_tp z' z t1 in
               let t1 = h_sub_in_tp n index x t1 in
               let t2 = h_sub_in_tp n index x t2 in
               A.Pi(z', t2, t1)
              )
            else A.Pi(z, h_sub_in_tp n index x t2, h_sub_in_tp n index x t1)
        | A.Atp(h, s) -> 
            if x = h then failwith "cannot substititute for type name"
            else A.Atp(h, List.map (h_sub_in_tm n index x) s)
        )
  )
  ) with Failure r -> raise (Failure (r ^ "\n when substituting tm " ^ A.ds_tm n ^ " for " ^ A.ds_id x ^ " into tp " ^ A.ds_tp m ^ " at index " ^ A.ds_weaktp index))



(* substitutes generated var only*)
(* n is a metavar resolution, whose outermost pi abstraction is instantiated with spine arguments *)
let rec h_sub_tp_in_tp ( n : A.tp)  (x : A.id) (m : A.tp) : A.tp = 
  try(
  (match x with
    | A.Placeholder -> m
    | A.Prvd _ -> failwith "cannot substitute regular var for types, only metavars can range over types"
    |  A.Gen _ ->
        (match m with
        | (A.CoType _ | A.Type _ ) -> m
        | A.Pi(z, t2, t1) -> 
            if z = x then m else
            if occurs_in_tp z n then 
              (* capture avoid *)
              (let z' = A.Prvd (Uid.nextz()) in 
               let t1 = rename_in_tp z' z t1 in
               let t1 = h_sub_tp_in_tp n x t1 in
               let t2 = h_sub_tp_in_tp n x t2 in
               A.Pi(z', t2, t1)
              )
            else A.Pi(z, h_sub_tp_in_tp n x t2, h_sub_tp_in_tp n x t1)
        | A.Atp(h, s) -> 
            if x = h then 
              h_sub_feed_spine_tp s n
            else 
              if occurs_in_spine x s
                then failwith "hs165: type metavar occurs in temrs"
                else A.Atp(h, s)
        )
  )
  ) with Failure r -> raise (Failure (r ^ "\n when substituting tp " ^ A.ds_tp n ^ " for " ^ A.ds_id x ^ " into tp " ^ A.ds_tp m))

(* used only during metavar instantiation *)
and h_sub_feed_spine_tp (s : A.tm list) (into : A.tp)  : A.tp = 
  try
  (match (s, into) with
  | ([], _) -> into (* do not enforce atp here as a metavar may be instantiated with pi's *)
  | ((sh:: st), A.Pi(z, t2, t1)) -> 
      let t1 = h_sub_in_tp sh (A.to_weak t2) z t1 in 
      h_sub_feed_spine_tp st t1
  | _ -> failwith ("hs180 : during metavar instantiation, spine length disagrees")
  ) with Failure r -> raise (Failure (r ^ "\n when attempting to feed " ^ A.ds_spine s ^ " into " ^ A.ds_tp into ))

(* substitutes generated var only*)
(* used only during metavar instantiation *)
let rec h_sub_tp_in_weaktp ( n : A.tp)  (x : A.id) (m : A.weaktp) : A.weaktp = 
  (match x with
    | A.Placeholder -> m
    | A.Prvd _ -> failwith "cannot substitute regular var for types, only metavars can range over types"
    |  A.Gen s ->
        (match m with
        | A.Atom -> A.Atom
        | A.Arr(t2, t1) ->  A.Arr (h_sub_tp_in_weaktp n x t2, h_sub_tp_in_weaktp n x t1)
        | A.WeakTpUnivar(h) -> 
            if s = h then A.to_weak n
            else m
        )
  )


let rec get_head_tm ( tm : A.tm) : A.id = 
  match tm with
  | A.Atm(h, _) -> h
  | A.Lam(x, b) -> let x' = A.Prvd (Uid.nextz())  (* avoids repetition *)
                   in get_head_tm (rename_in_tm x' x b)

  (* hack for apply rec renaming substitution to list of id's *)
let rec_sub_in_id (tm : A.tm) (x : A.id) (id : A.id) : A.id = 
  if id = x then get_head_tm tm else id *)