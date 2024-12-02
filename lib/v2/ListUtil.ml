
let rec remove_duplicates (l : 'a list) : 'a list = 
  match l with
  | [] -> []
  | ( x :: xs) -> if List.mem x xs then remove_duplicates xs else x :: remove_duplicates xs


let is_sublist (a : 'a list) (b : 'a list) : bool = 
  List.for_all (fun a -> List.mem a b) a

let minus (a : 'a list) (b : 'a list) : 'a list = 
  List.filter (fun a -> not (List.mem a b)) a

let intersect (a : 'a list) (b : 'a list) : 'a list = 
  List.filter (fun a -> List.mem a b) a


let equal_as_sets (a : 'a list) (b : 'a list) : bool = 
  is_sublist a b && is_sublist b a

let rec contains_duplicate (l : 'a list) : bool = 
  match l with
  | [] ->false
  | (h :: t) -> if List.mem h t then true else contains_duplicate t

let rec find_duplicates (l : 'a list) : 'a list = 
  match l with
  | [] -> []
  | (h :: t) -> if List.mem h t then h :: find_duplicates t else find_duplicates t
  
let union (a : 'a list) (b : 'a list) : 'a list = 
  remove_duplicates (a @b)


let rec drop_n n lst =
    if n <= 0 then
      lst
    else
      match lst with
      | [] -> []
      | _ :: tl -> drop_n (n - 1) tl
  ;;


let rec find_elem_by_key (lst : (string * 'a) list) (key : string) : 'a option =
  match lst with
  | [] -> None
  | (s, v) :: tl ->
      if s = key then Some v
      else find_elem_by_key tl key

(* Every Element of a list are equal *)
let all_equal lsts =
  match lsts with
  | [] | [_] -> true  (* Empty or single list are trivially equal *)
  | first :: rest -> List.for_all ((=) first) rest


let rec take n lst =
  match (n, lst) with
  | (0, _) | (_, []) -> []
  | (_, x :: xs) -> x :: take (n - 1) xs

let rec drop n lst =
  match (n, lst) with
  | (0, _) -> lst
  | (_, []) -> []
  | (_, _ :: xs) -> drop (n - 1) xs
(* 
let nth lst n =
  if List.length lst <= n then failwith "nth: index out of bounds"
  else List.nth lst n *)

let search_lookup (lst : (string * 'a) list) (key : string) : 'a =
  match find_elem_by_key lst key with
  | Some v -> v
  | None -> failwith ("search_lookup: key not found: " ^ key)

let tabulate f n =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (f i :: acc)
  in
  aux (n - 1) []
;;
let python_range start_idx end_idx =
  let rec aux current acc =
    if current >= end_idx then List.rev acc
    else aux (current + 1) (current :: acc)
  in
  aux start_idx []
;;
   