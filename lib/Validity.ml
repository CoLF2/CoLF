(* module A = Ast
module Ctx = TypeCheckingContext
module HS = HereditarySubstitution



type ind_coind = Inductive of int | Coinductive of int (* int is priority *)



let rec classify_kind (tp : A.tp)  : ind_coind  = 
  match tp with
  | A.Type p -> Inductive p
  | A.CoType p -> Coinductive p
  | A.Atp _ -> failwith "is not kind"
  | A.Pi(_, _, t1) -> classify_kind t1

let rec classify_tp (tp : A.tp) (g : A.dec list) :  ind_coind = 
  match tp with
  | A.Atp(A.Prvd h, _) -> 
    (match Ctx.find_id_sig_local true h (g,g) with
    | None -> failwith "type family not found"
    | Some (tp, _) -> classify_kind tp
    )
  | A.Atp(_, _) -> failwith "gen/placeholder should not be here in validity checking"
  | A.Pi(_, _, t1) -> classify_tp t1 g
  | (A.Type _ | A.CoType _) -> failwith "valid22: is not type"


let check_spine_is_weak (s : A.tm list) : A.id list = 
  let s = List.map (HS.hered_eta_contract) s in
   List.map(fun m -> match m with
  | A.Atm(A.Prvd id, []) -> A.Prvd id
  | _ -> failwith "spine is not weak (not plain)"
  ) s 
  

let check_valid_trace (constructors : string list) (g : A.dec list) : unit = 
  let rec go cur_priority cur_is_coinductive cur_id remaining : unit = 
    match remaining with
    | []  -> if cur_is_coinductive 
      then () else failwith ("the maximum priority constructor is not coinductive, constructor : " ^  cur_id)
    | (r :: rs) -> 
        (match Ctx.find_id_sig_local true r (g,g) with
        | Some(tp, Ctx.IdConstant _) -> 
            (match classify_tp tp g with
            | Inductive p -> if p < cur_priority then go p false r rs else go cur_priority cur_is_coinductive cur_id rs
            | Coinductive p -> if p < cur_priority then go p true r rs else go cur_priority cur_is_coinductive cur_id rs
              )
        | Some _ -> failwith "should be a constructor"
        | None -> failwith "should be a constructor"
        )
  in 
  match constructors with
  | [] -> failwith ("occurrence of is not guarded, did not encounter constructors")
  | (c :: cs) -> (
      (match Ctx.find_id_sig_local true c (g,g) with
        | Some(tp, Ctx.IdConstant _) -> 
            (match classify_tp tp g with
            | Inductive p -> go p false c cs
            | Coinductive p ->go p true c cs 
              )
        | Some _ -> failwith "should be a constructor"
        | None -> failwith "should be a constructor" )
  )


(* will throw exception if names are not guarded by at least one coinductive contructor *)
let rec check_guarded_in_tm (r : A.id) (rec_names : A.id list) 
(constructors : string list) (m : A.tm) (g : A.dec list) : unit = 
  try(
  match m with
  | A.Lam(x, b) -> 
    (* ensure no capture *)
    let z = A.Prvd (Uid.nextz()) in
    let b = HS.rename_in_tm z x b in
    check_guarded_in_tm r rec_names constructors b g
  | A.Atm((A.Prvd h), s) -> 
    (
      match Ctx.find_id_sig_local true h (g,g) with
      | None -> (* assume it's a bound variable*)
          check_guarded_in_spine r rec_names constructors s g
      | Some(_, Ctx.IdConstant _) -> 
          check_guarded_in_spine r rec_names ( constructors @[h]) s g
          (* (match classify_tp tp g with
            | Coinductive p -> () (* guarded *)
            | Inductive p -> check_guarded_in_spine names s g
          ) *)
      | Some(_, Ctx.IdRecConstantInSig (defm, A.CheckedBody _) ) -> 
          (
            (* if not tp_checked 
              then failwith "valid60: attempt to check guardedness for unchecked definitions"
              else *)
                if r = (A.Prvd h)
                  then  check_valid_trace (constructors) g
                  else
                if List.mem (A.Prvd h) rec_names 
                then () (* checked *)
                  (* failwith ("occurrence of " ^ h ^ " is not guarded") *)
                else (let _ = check_spine_is_weak s in
                    check_guarded_in_tm r (rec_names@[A.Prvd h]) constructors defm g
              )
            )
      | Some(_, cls) -> failwith ("find_id_local should only return IdConstant or IdRecConstantInSig, but returned " ^ Ctx.ds_id_cls cls)
    )
  | A.Atm((_), _) ->  failwith "valid15: check_guarded_in should not contain any gen or placeholder at " 
  ) with Failure s ->  raise (Failure (s ^ "\n when checking that " ^ A.ds_id r
  (* "(" ^ String.concat ", " (List.map A.ds_id rec_names) ^ ")"  *)
  ^ " is guarded in " ^ A.ds_tm m ))
  
  
(* must check providing only the global signature*)
and check_guarded_in_spine (r : A.id) (names : A.id list) (constructors : string list)
 (s : A.tm list) (g : A.dec list) : unit = 
  let _ = List.map (fun m -> check_guarded_in_tm r names constructors m g) s in () *)