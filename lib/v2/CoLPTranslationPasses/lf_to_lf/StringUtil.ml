let is_str_starting_with_lowercase (s : string) : bool =
  String.length s > 0 && Char.lowercase_ascii s.[0] = s.[0]

let capitalize_first_letter (s : string) : string =
  if String.length s = 0 then s
  else
    let first_char = Char.uppercase_ascii s.[0] in
    let rest = String.sub s 1 (String.length s - 1) in
    Printf.sprintf "%c%s" first_char rest