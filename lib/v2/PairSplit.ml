
type designation =  Left | Right
type t = designation list

let get_left (data : t) : int list = 
  ListUtil.filter_map_i (fun i x -> if x = Left then Some i else None) data

let get_right (data : t) : int list =
  ListUtil.filter_map_i (fun i x -> if x = Right then Some i else None) data


let select_left (data : t) (inputs : 'a list) : 'a list =
  assert (List.length data = List.length inputs);
  ListUtil.filter_map_i (fun i x -> if x = Left then Some (List.nth inputs i) else None) data

let select_right (data : t) (inputs : 'a list) : 'a list =
  assert (List.length data = List.length inputs);
  ListUtil.filter_map_i (fun i x -> if x = Right then Some (List.nth inputs i) else None) data


let from_list_f (data : 'a list) (f : 'a -> designation): t =
  List.map f data

let from_two_lists (left : int list) (right : int list) : t = 
  List.map (fun i -> 
    if List.mem i left then Left
    else if List.mem i right then Right
    else failwith "from_two_lists: index not found in either list"
    ) (ListUtil.range 0 (List.length left + List.length right))

let show (data : t) : string =
  String.concat "" (List.map (fun x -> match x with
    | Left -> "L"
    | Right -> "R") data)