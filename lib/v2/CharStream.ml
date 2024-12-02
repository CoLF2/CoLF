module type CHAR_STREAM = sig
  type t
  val new_file : string -> t (* file path*)
  val match_string : t -> string -> t option (* returns the remaining stream *)
  val get_row_col : t -> int * int
  val get_file_path : t -> string

  type token = Space of string | Identifier of string | EOF | SpecialChar of string
  val get_next_token : t -> token * t 

  val scan_with_end_and_groups : string -> string list -> (string * string) list -> t -> (string * t) option

  val get_num_chars_read : t -> int
  val is_eof : t -> bool


end

module CharStream : CHAR_STREAM = struct
  type t = {
    file_path : string;
    content : string;
    index : int;
    row : int;
    col : int;
  }

  type token = Space of string | Identifier of string | EOF | SpecialChar of string

  (* Helper function to read a file's content *)
  let read_file path =
    let chan = open_in path in
    let length = in_channel_length chan in
    let content = really_input_string chan length in
    close_in chan;
    content

  let new_file path = {
    file_path = path;
    content = read_file path;
    index = 0;
    row = 1;
    col = 1;
  }

  let get_row_col stream = (stream.row, stream.col)

  let get_file_path stream = stream.file_path

  let is_eof stream = stream.index >= String.length stream.content

  let match_string stream s =
    let len = String.length s in
    if stream.index + len <= String.length stream.content &&
       String.sub stream.content stream.index len = s then
      let rec advance idx r c i =
        if i >= len then (r, c)
        else
          let next_char = stream.content.[idx + i] in
          (* let _ = print_endline ("next char: " ^ Char.escaped next_char ^ " row " ^ string_of_int r ^ " col " ^ string_of_int c) in *)
          if next_char = '\n' then advance idx (r + 1) 1 (i + 1)
          else advance idx r (c + 1) (i + 1)
      in
      let new_row, new_col = advance stream.index stream.row stream.col 0 in
      Some { stream with index = stream.index + len; row = new_row; col = new_col }
    else
      None

  (* this should return a whole sequence of space characters or an identifier [A-Za-z0-9_] *)
  

  let get_num_chars_read stream = stream.index

  let get_next_token stream = (
    if is_eof stream then (EOF, stream)
    else
      (* let is_alphanumeric c = 
        ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || (c = '_')  *)
      let is_key_char c = 
        c = '[' || c = ']' 
        || c = '{' || c = '}' || c = ':' 
        || c = '(' || c = ')' 
        || c = '.' (* This should be implementation specific, but I am making it general here*)
        || c = '='
  
      and is_whitespace c = 
        c = ' ' || c = '\t' || c = '\n'
  
      and is_unicode c =
        Char.code c > 127
      in
  
      let rec collect_whitespace idx row col =
        if idx >= String.length stream.content || not (is_whitespace stream.content.[idx]) then (idx, row, col)
        else
          let c = stream.content.[idx] in
          if c = '\n' then collect_whitespace (idx + 1) (row + 1) 1
          else collect_whitespace (idx + 1) row (col + 1)
  
      and collect_identifier idx =
        if idx >= String.length stream.content || is_key_char stream.content.[idx] || is_whitespace stream.content.[idx] then idx
        else collect_identifier (idx + 1)
      in
  
      let start_idx = stream.index in
      let first_char = stream.content.[start_idx] in
  
      if is_unicode first_char then
        failwith "Unicode characters are not supported"
  
      else if is_whitespace first_char then
        let end_idx, new_row, new_col = collect_whitespace start_idx stream.row stream.col in
        let token = String.sub stream.content start_idx (end_idx - start_idx) in
        (Space token, { stream with index = end_idx; row = new_row; col = new_col })
  
      else if is_key_char first_char then
        let token = String.make 1 first_char in
        (SpecialChar token, { stream with index = start_idx + 1; col = stream.col + 1 })
  
      else
        let end_idx = collect_identifier start_idx in
        let token = String.sub stream.content start_idx (end_idx - start_idx) in
        (Identifier token, { stream with index = end_idx; col = stream.col + (end_idx - start_idx) })
  )


  let scan_with_end_and_groups end_pattern except_end_following escape_groups stream =
    let rec scan idx stack row col =
      if idx >= String.length stream.content then None  (* Reached EOF without finding the end pattern *)
      else
        let current_substr = String.sub stream.content idx (String.length stream.content - idx) in
  
        (* Helper function to check if the substring starts with end_pattern but is not an excepted sequence *)
        let starts_with_end_pattern str idx =
          String.length str >= idx + String.length end_pattern &&
          String.sub str idx (String.length end_pattern) = end_pattern &&
          not (
            List.exists (fun follow ->
              let follow_len = String.length follow in
              idx >= follow_len && 
              String.sub str (idx - follow_len) follow_len = follow
            ) except_end_following
          )
        in
        (* Helper function to update row and column based on end_pattern *)
        let update_position row col pattern =
          let line_breaks = String.fold_left (fun acc c -> if c = '\n' then acc + 1 else acc) 0 pattern in
          if line_breaks > 0 then
            (row + line_breaks, 1)  (* Reset column to 1 after a newline *)
          else
            (row, col + String.length pattern)
        in

       (* Check if we reached end pattern that is not followed by any in except_end_following *)
        if stack = [] && starts_with_end_pattern stream.content idx then
          let result_str = String.sub stream.content stream.index (idx - stream.index) in
          let new_row, new_col = update_position row col end_pattern in
          Some (result_str, { stream with index = idx + String.length end_pattern; row = new_row; col = new_col })
  
        else
          (* Check each escape group to see if we are at the beginning of any nested pattern *)
          let rec check_escape_groups = function
            | [] -> None
            | (start, finish)::rest ->
                if String.length current_substr >= String.length start &&
                    String.sub current_substr 0 (String.length start) = start then
                  Some (start, finish)
                else
                  check_escape_groups rest
          in
  
          match check_escape_groups escape_groups with
          | Some (start, finish) ->
              (* Found a start of an escape group; add it to the stack and continue *)
              scan (idx + String.length start) ((start, finish) :: stack) row (col + String.length start)
          | None ->
              (* No escape group starts here, continue with the normal scanning *)
              let next_char = stream.content.[idx] in
              let new_row, new_col =
                if next_char = '\n' then (row + 1, 1)
                else (row, col + 1)
              in
  
              (* Check if we are at the end of the current top escape group *)
              if stack <> [] &&
                  String.length current_substr >= String.length (snd (List.hd stack)) &&
                  String.sub current_substr 0 (String.length (snd (List.hd stack))) = (snd (List.hd stack)) then
                (* End of escape group; pop from stack and continue *)
                scan (idx + String.length (snd (List.hd stack))) (List.tl stack) new_row new_col
              else
                (* Continue scanning with updated position *)
                scan (idx + 1) stack new_row new_col
    in
    scan stream.index [] stream.row stream.col
        
end