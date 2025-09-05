type ('a, 'b) map = ('a * 'b) list
module A = CoLFAbt.CoLFAbt
module LP = CoLPSignature.CoLPSignature

type term = 
  | Var of string
  | TmUnit
  | Ap of string * term 
  | TmPair of term * term

type premise = term list * string * term 

type rel_clause = (
  premise list 
  * premise (* conculsion *))

(* type rel_type = {
  inputs : LP.tp list;
  output : LP.tp;
} *)
type rel_type = LP.relational_type

type rel_type_signature = (string, rel_type) map
type rel_clause_signature = (string, rel_clause) map (* the name is the clause name, not relational type name *)

type t = {
  data_sig : LP.data_sig;
  rel_sig : rel_type_signature;
  rel_clause_sig : rel_clause_signature;
}

(* always return a list of all free variables in the term , 
in order, containing duplicates *)
let rec free_vars_in_term (t : term) : string list = 
  match t with
  | Var(name) -> [name]
  | TmUnit -> []
  | Ap(_head, arg) -> free_vars_in_term arg (* head is always treated as a constant for the second order case*)
  | TmPair(t1, t2) -> free_vars_in_term t1 @ free_vars_in_term t2

let free_vars_in_premise (p : premise) : string list = 
  let (i, _, o) = p in
  let i' = List.map free_vars_in_term i in
  let o' = free_vars_in_term o in
  List.flatten i' @ o'

let rec subst_tm (y : term) (x : string) (z : term)  : term = 
  match z with
  | Var(name) -> if name = x then y else z
  | TmUnit -> TmUnit
  | Ap(head, arg) -> Ap(head, subst_tm y x arg)
  | TmPair(t1, t2) -> TmPair(subst_tm y x t1, subst_tm y x t2)

let subst_tm_in_premise (y : term) (x : string) (z : premise) : premise = 
  let (i, n, o) = z in
  let i' = List.map (fun t -> subst_tm y x t) i in
  let o' = subst_tm y x o in
  (i', n, o')

(* only subst at ith occurrence , everything else is left unchanged 
int = -1 indicates successful substitution
*)
let subst_occurrence (y : term) (x : string) (idx : int) (t : term) : term * int = 
  assert (idx >= 0);
  let rec aux (t : term) (idx : int) : term * int = 
    match t with
    | Var(name) -> if name = x 
                   then 
                    (
                      if idx = 0 then 
                        (y, -1)
                      else
                        (t, idx - 1)
                    )
                   else 
                    (t, idx)
    | TmUnit -> (t, idx)
    | Ap(head, arg) -> 
      (
        assert (head <> x);
        let arg', idx' = aux arg idx in
        Ap(head, arg'), idx'
      )
    | TmPair(t1, t2) -> 
      let (t1', idx') = aux t1 idx in
      let (t2', idx'') = aux t2 idx' in
      (TmPair(t1', t2'), idx'')
  in
    (aux t idx)

let subst_occurrence_in_premise (y : term) (x : string) (idx : int) ((inputs, name, output) : premise) : premise * int = 
  assert (idx >= 0);
  let rec aux (inputs_acc : term list) (inputs_rem : term list) (idx : int) = 
    if idx < 0 then
      ((inputs_acc @ inputs_rem, name, output), idx)
    else
      match inputs_rem with
      | [] -> ((inputs_acc, name, fst (subst_occurrence y x idx output)), idx)
      | hd :: tl -> 
        let (hd', idx') = subst_occurrence y x idx hd in
        aux (inputs_acc @ [hd']) tl idx'
  in
  aux [] inputs idx

let subst_occurrence_in_premises (y : term) (x : string) (idx : int) (ps : premise list) : premise list * int = 
  let rec aux (ps_acc : premise list) (ps_rem : premise list) (idx : int) = 
    if idx < 0 then
      (ps_acc @ ps_rem, idx)
    else
      match ps_rem with
      | [] -> (ps_acc, idx)
      | hd :: tl -> 
        let (hd', idx') = subst_occurrence_in_premise y x idx hd in
        aux (ps_acc @ [hd']) tl idx'
  in
  aux [] ps idx
  

let is_tm_var (t : term) : bool = 
  match t with
  | Var(_) -> true
  | _ -> false

let is_tm_shallow (t : term) : bool =
  match t with
  | TmUnit -> true
  | TmPair(Var _, Var _) -> true
  | Ap(_, Var _) -> true
  | Var _ -> true
  | _ -> false

let get_tm_var (t : term) : string = 
  match t with
  | Var(name) -> name
  | _ -> failwith "get_tm_var: not a variable"

let rec show_term (t : term) : string = 
  match t with
  | Var(name) -> name
  | TmUnit -> "()"
  | Ap(head, head_term) -> "(" ^ head ^ " " ^ show_term (head_term) ^ ")"
  | TmPair(t1, t2) -> "(" ^ show_term t1 ^ " , " ^ show_term t2 ^ ")"
and show_term_list (terms : term list) : string = 
  String.concat ", " (List.map show_term terms)
let show_premise (p : premise) : string = 
    let (i, n, o) = p in
    show_term_list i ^ " >= " ^ n ^ " >= " ^ show_term o
    

let show_rel_type (rt : rel_type) : string =
  let inputs_str = String.concat " , " (List.map LP.show_tp rt.inputs) in
  let output_str =  (LP.show_tp rt.output) in
  inputs_str ^ " >=> " ^ output_str

  
let show_rel_clause ((premises, concl) : rel_clause) : string = 
  let premises_str = String.concat "" (List.map (fun p -> show_premise p ^ " ->\n   ") premises) in
  let concl_str = show_premise concl in
  premises_str ^ concl_str

let show_rel_clause_entry ((name, rel_clause) : string * rel_clause) : string = 
  name ^ " : " ^ show_rel_clause rel_clause

let show_signature (sig_ : t) : string = 
  let data_sig_str = LP.CoLFPrint.show_ds sig_.data_sig in
  let rel_type_str = String.concat "" (
    List.map (fun (name, tp) -> 
       name ^ " : " ^ show_rel_type tp ^ ".\n"
    ) sig_.rel_sig
  ) in
  let rel_clause_str = String.concat "" (
    List.map (fun (name, rel_clause) -> 
      show_rel_clause_entry (name, rel_clause)  ^ ".\n"
    ) sig_.rel_clause_sig
  ) in

  data_sig_str ^ "\n" ^ rel_type_str ^ "\n" ^ rel_clause_str
