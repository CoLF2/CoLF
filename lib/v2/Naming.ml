let get_fresh_name (cur_name : string) : string = 
  (* if cur_name is ends in _[0-9]+, then increment the number 
    *)
  (* single digit *)
  let default_new_name = cur_name ^ "_1" in
  if String.length cur_name > 2 && String.sub cur_name (String.length cur_name - 2) 1 = "_" then
    let num_str = String.sub cur_name (String.length cur_name - 1) 1 in
    match int_of_string_opt num_str with
    | None -> default_new_name
    | Some num -> 
      let new_num = num + 1 in
      String.sub cur_name 0 (String.length cur_name - 2) ^ "_" ^ string_of_int new_num
  else 
    if String.length cur_name > 3 && String.sub cur_name (String.length cur_name - 3) 1 = "_" then
      let num_str = String.sub cur_name (String.length cur_name - 2) 2 in
      match int_of_string_opt num_str with
      | None -> default_new_name
      | Some num -> 
        let new_num = num + 1 in
        String.sub cur_name 0 (String.length cur_name - 3) ^ "_" ^ string_of_int new_num
    else 
      default_new_name

let new_var_name (guide : string) (exclude : string list) = 
  let new_var_name = ref (guide ) in
  while List.mem !new_var_name exclude do
    (* print_endline ("CLP26: " ^ !new_var_name); *)
    new_var_name := get_fresh_name !new_var_name
  done;
  !new_var_name
