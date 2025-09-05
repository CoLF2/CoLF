(* open Token *)

module T = Token


let non_id_words = " \n\t[](){}:=->.%"

let rec scanUntil acc l =
  match l with 
  | [] -> (acc, [])
  | (h :: t) -> 
      if String.contains non_id_words h
        then (acc, l)
    else scanUntil (acc@[h]) t
(* module T = Token *)
let rec lex (input : char list) : T.tok list = 
  match input with
  | [] -> [T.EOF]
  | ('%' :: '%' :: tail) -> (
    (* drop until \n *)
    let rec dropped l = 
      match l with
      | [] -> [T.EOF]
      | ('\n' :: t) -> lex t
      | (_ :: t) -> dropped t
    in dropped tail
  )
  | (' ' :: tail) -> lex tail
  | ('\n' :: tail ) -> lex tail
  | ('\t' :: tail)  -> lex tail
  | ('[' :: tail) -> T.LSQBRACKET :: lex tail 
  | (']' :: tail) -> T.RSQBRACKET :: lex tail
  | ('(' :: tail) -> T.LPAREN :: lex tail 
  | (')' :: tail) -> T.RPAREN :: lex tail
  | ('{' :: tail) -> T.LCURLYBRACE :: lex tail
  | ('}' :: tail) -> T.RCURLYBRACE :: lex tail
  | (':' :: ':' :: tail) -> T.DOUBLECOLON :: lex tail
  | (':' :: tail) -> T.COLON :: lex tail
  | ('=' :: tail) -> T.EQUAL :: lex tail
  | ('-' :: '>' :: tail) -> T.RIGHTARROW :: lex tail
  | ('.' :: tail) -> T.PERIOD :: lex tail
  | ('%' :: tail) -> (
      let (id, rest) = scanUntil [] tail in
      T.COMMANDHEAD (String.of_seq (List.to_seq id)) :: lex rest
  )
  | (id_hd :: id_tail) -> (
      let (id, rest) = scanUntil [id_hd] id_tail in 
      if id = ['_']
      then T.UNDERSCORE :: (lex rest)
    else T.ID (String.of_seq (List.to_seq id)) :: lex rest
    )
  


let lex_string s = lex (List.of_seq (String.to_seq s))