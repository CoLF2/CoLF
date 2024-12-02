
type tok = LPAREN | RPAREN
          | LCURLYBRACE | RCURLYBRACE
          | LSQBRACKET | RSQBRACKET
          | ID of string
          | COMMANDHEAD of string
          | PERIOD 
          | PERCENT
          | COLON
          | DOUBLECOLON
          | EQUAL
          | UNDERSCORE
          | RIGHTARROW
          | EOF 
          [@@deriving show]


    