(* 
module A = Ast
module HS = HereditarySubstitution
let  unify_bnd_generic (t1 : A.id * 'a) (t2 : A.id * 'b)
  (occurs_in_t1 : A.id -> 'a -> bool) (occurs_in_t2 : A.id -> 'b -> bool)
  (rename_in_t1 : A.id -> A.id -> 'a -> 'a ) (rename_in_t2 : A.id -> A.id -> 'b -> 'b)
  : ((A.id * 'a * 'b)) = 
    match (t1, t2) with
    | ((A.Placeholder, b1), (A.Placeholder, b2)) -> (A.Placeholder, b1, b2)
    | ((A.Prvd x1, b1), (A.Placeholder, b2)) -> 
        if occurs_in_t2 (A.Prvd x1) b2 
          then (let x' = A.Prvd (Uid.nextz()) in ((x', rename_in_t1 x' (A.Prvd x1) b1, b2)))
          else ((A.Prvd x1, b1, b2))
    | ( (A.Placeholder, b1), (A.Prvd x2, b2)) -> 
        if occurs_in_t1 (A.Prvd x2) b1 
          then (let x' = A.Prvd (Uid.nextz()) in ((x', b1, rename_in_t2 x' (A.Prvd x2) b2)))
          else ((A.Prvd x2, b1, b2))
    | ((A.Prvd x1, b1), (A.Prvd x2, b2)) -> 
        if x1 = x2 then (A.Prvd x1, b1, b2)
        else (let x' = A.Prvd (Uid.nextz()) in 
                ((x', rename_in_t1 x' (A.Prvd x1) b1, rename_in_t2 x' (A.Prvd x2) b2))
        )
    | _ -> failwith "unif31: binder contains gen, not allowed?"

let  unify_bnd_tp_tm (t1 : A.id * A.tp) (t2 : A.id * A.tm) : (A.id * A.tp  * A.tm) = 
  unify_bnd_generic t1 t2 HS.occurs_in_tp HS.occurs_in_tm HS.rename_in_tp HS.rename_in_tm
let  unify_bnd_tm_tp (t1 : A.id * A.tm) (t2 : A.id * A.tp) : ((A.id * A.tm  * A.tp)) = 
  unify_bnd_generic t1 t2 HS.occurs_in_tm HS.occurs_in_tp HS.rename_in_tm HS.rename_in_tp
let  unify_bnd_tp_tp (t1 : A.id * A.tp) (t2 : A.id * A.tp) : ((A.id * A.tp  * A.tp)) = 
  unify_bnd_generic t1 t2 HS.occurs_in_tp HS.occurs_in_tp HS.rename_in_tp HS.rename_in_tp
let  unify_bnd_tm_tm (t1 : A.id * A.tm) (t2 : A.id * A.tm) : ((A.id * A.tm  * A.tm)) = 
  unify_bnd_generic t1 t2 HS.occurs_in_tm HS.occurs_in_tm HS.rename_in_tm HS.rename_in_tm
 *)
