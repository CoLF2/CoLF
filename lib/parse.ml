
module P = Parseast
module T = Token

type stackitem = SP of P.parseast | ST of T.tok [@@deriving show]
type parse_state = (stackitem list) * (Token.tok list) [@@deriving show]

let show_ps = [%derive.show : parse_state]
let show_tk = [%derive.show : T.tok]

let shift (ps : parse_state) : parse_state = 
  match ps with
  |((s), (th :: tt))  -> (ST th :: s), tt
  | _ -> failwith ("unable to shift " ^ show_ps ps)

let rec shift_or_reduce ( ps : parse_state) : parse_state =
  match ps with
  | (_, []) -> failwith ("expected EOF at the end " ^ show_ps ps)
  | (stack, ((th:: tt) as tkl)) -> 
    (
      match (stack, th) with
        | ((ST T.PERIOD :: _single :: []), T.EOF) -> ((match ( tt) with
                                    | ([]) -> ps
                                    | _ -> failwith ("unexpected token " ^ [%derive.show : T.tok] th)
                                    ))
        (* ======= error checking  ======= *)
        | (ST (T.ID _) :: _, _) ->  failwith "unexpected T.ID on the stack, please use P.Id"
        (* ======= application reductions ======= *)
        | (SP ((P.Paren _ | P.Id _) as rhs) :: SP ((P.Paren _ | P.Id _ | P.App _) as lhs) :: s', _) -> 
            shift_or_reduce (SP (P.App(lhs, rhs)) :: s', tkl)
        (* ======= sentential endings ========== *)
        (* combine initial and subsequent decs*)
        | ((SP ((P.Dec _ | P.DecDefI _ | P.DecDefC _ | P.Command _) as d2) :: ST T.PERIOD :: SP ((P.Dec _ | P.Dec2 _ | P.DecDefC _ | P.DecDefI _ | P.Command _) as d1) :: []), (T.PERIOD)) -> shift_or_reduce ([SP (P.Dec2 (d1, d2))], tkl) 
        (* shift period when there is only single declaration*)
        | ((SP ((P.Dec2 _) | (P.Dec _) | P.DecDefI _ | P.DecDefC _ | P.Command _) :: []), (T.PERIOD)) -> shift_or_reduce (ST th :: stack , tt) 
        (* --- complete declaration when encountering period ---- *)
        (* c : A *)
        | ((SP ((P.App (_, _) | P.Id _ | P.PiT (_, _, _) | P.PiNT (_, _) | P.PiArr (_, _) | P.Paren _) as tm) :: ST T.COLON 
            :: SP (P.Id c) :: ((ST T.PERIOD :: _  | []) as s')), (T.PERIOD)) -> shift_or_reduce (SP (P.Dec (P.Id c, tm)) :: s', tkl) 
        (* %cmd xxx. *)
        | ((SP ((P.App (_, _) | P.Id _) as tm))
            :: ST (T.COMMANDHEAD c) :: ((ST T.PERIOD :: _  | []) as s'), (T.PERIOD)) -> shift_or_reduce (SP (P.Command (c, tm)) :: s', tkl) 
        (* complete declaration when encountering period *)
        | (SP ((P.App (_, _) | P.Id _ | P.LamT (_, _, _) | P.LamNT (_, _)  | P.Paren _) as tm) :: ST T.EQUAL
          :: (SP ((P.App (_, _) | P.Id _ | P.PiT (_, _, _) | P.PiNT (_, _) | P.PiArr (_, _) | P.Paren _) as tp) 
          :: ST ((T.COLON  | T.DOUBLECOLON) as col)
            :: SP (P.Id c) :: ((ST T.PERIOD :: _  | []) as s')), (T.PERIOD)) -> 
                shift_or_reduce (SP ((match col with |T.COLON -> P.DecDefI (P.Id c, tp, tm)| T.DOUBLECOLON -> P.DecDefC (P.Id c, tp, tm)| _ -> failwith "not possible") 
                  ) :: s', tkl) 
        (* ======= nonsentential endings ========== *)
        (* 1 --- rightarrow --- *)
        | ((SP ((P.App (_, _) | P.PiT (_, _, _) | P.PiNT (_, _) | P.Id _ | P.PiArr(_, _) | P.Paren _) as rhs) :: ST T.RIGHTARROW 
        :: SP ((P.Id _ | P.App (_, _) | P.Paren _) as lhs) 
        :: ((ST (T.PERIOD | T.COLON | T.RIGHTARROW | T.LPAREN | T.RCURLYBRACE) :: _ ) as s')), 
            (T.PERIOD | T.RPAREN | T.RCURLYBRACE | T.RSQBRACKET | T.EQUAL)) -> shift_or_reduce (SP (P.PiArr (lhs, rhs)) :: s', tkl) 
        (* 1 --- lamabs nt --- *)
        | ((SP ((P.App (_, _) | P.Id _ | P.Paren _ | P.LamT _ | P.LamNT _) as rhs) :: ST T.RSQBRACKET
        :: SP ((P.Id _ ) as lhs) :: ST T.LSQBRACKET
        :: ((ST (T.EQUAL | T.LPAREN | T.RSQBRACKET) :: _ ) as s')), 
            (T.PERIOD | T.RPAREN | T.RCURLYBRACE | T.RSQBRACKET)) -> shift_or_reduce (SP (P.LamNT (lhs, rhs)) :: s', tkl) 
        (* 2 --- paren --- *)
        | (SP any :: ST T.LPAREN :: s' , T.RPAREN) -> shift_or_reduce (SP (P.Paren any) :: s', tt)
        (* 3 --- pi t --- *)
        | ((SP ((P.App (_, _) | P.Id _ | P.Paren _ | P.PiArr _ | P.PiNT _ | P.PiT _ ) as tm) :: ST T.RCURLYBRACE
        :: (SP ((P.PiArr _ | P.Id _ | P.Paren _  | P.App _ ) as tp )):: ST T.COLON
        :: SP ((P.Id _ ) as abs) :: ST T.LCURLYBRACE :: s'), 
            (T.PERIOD | T.RPAREN | T.RCURLYBRACE | T.RSQBRACKET  | T.EQUAL)) -> shift_or_reduce (SP (P.PiT (abs, tp, tm)) :: s', tkl) 
        (* 4 --- pi nt --- *)
        | ((SP ((P.App (_, _) | P.Id _ | P.Paren _ | P.PiArr _ | P.PiNT _ | P.PiT _ ) as rhs) :: ST T.RCURLYBRACE
        :: SP ((P.Id _ ) as lhs) :: ST T.LCURLYBRACE
        :: (s')), 
            (T.PERIOD | T.RPAREN | T.RCURLYBRACE | T.RSQBRACKET | T.EQUAL)) -> shift_or_reduce (SP (P.PiNT (lhs, rhs)) :: s', tkl) 
        (* 3 --- lam t --- *)
        | ((SP ((P.App (_, _) | P.Id _ | P.Paren _ | P.LamT _ | P.LamNT _  ) as tm) :: ST T.RSQBRACKET
        :: (SP ((P.PiArr _ | P.Id _ | P.Paren _  | P.PiNT _ | P.PiT _ ) as tp )):: ST T.COLON
        :: SP ((P.Id _ ) as abs) :: ST T.LSQBRACKET :: s'), 
            (T.PERIOD | T.RPAREN | T.RCURLYBRACE | T.RSQBRACKET | T.EQUAL)) -> shift_or_reduce (SP (P.LamT (abs, tp, tm)) :: s', tkl) 
        (* ============= initial  =========== *)
        | ([], T.ID s) -> shift_or_reduce ([SP (P.Id (P.Str s))], tt)
        | ([], T.COMMANDHEAD s) -> shift_or_reduce ([ST (T.COMMANDHEAD s)], tt)
        | ([], _) -> failwith ("unexpected " ^ show_tk th)
        (* =============== regular rules ========== *)
        (* 1 --- shift ids --- *)
          (* plain shift *)
        | ((ST (T.PERIOD | T.COLON | T.RIGHTARROW | T.LCURLYBRACE | T.RCURLYBRACE | T.LPAREN | T.RPAREN 
                | T.LSQBRACKET | T.RSQBRACKET | T.EQUAL | T.COMMANDHEAD _) :: _ ), T.ID s) -> shift_or_reduce (SP (P.Id (P.Str s)) :: stack, tt)
            (* id and % for commands *)
        | ((ST T.PERIOD :: _ ), T.COMMANDHEAD s) -> shift_or_reduce (ST (T.COMMANDHEAD s) :: stack, tt)
          (* plain underscore shift *)
        | ((ST (T.PERIOD | T.COLON | T.RIGHTARROW | T.LCURLYBRACE | T.RCURLYBRACE | T.LPAREN | T.RPAREN 
                | T.LSQBRACKET | T.RSQBRACKET | T.EQUAL) :: _ ), T.UNDERSCORE) -> shift_or_reduce (SP (P.Id (P.Placeholder)) :: stack, tt)
          (* consecutive id shift *)
        | (( ( SP (P.Id _ | P.Paren _ | P.App _))  ::
          ST (T.PERIOD | T.COLON | T.RIGHTARROW | T.LCURLYBRACE | T.RCURLYBRACE | T.LPAREN | T.RPAREN 
                | T.LSQBRACKET | T.RSQBRACKET | T.EQUAL | T.PERCENT | T.COMMANDHEAD _) :: _ ), T.ID s) -> shift_or_reduce (SP (P.Id (P.Str s)) :: stack, tt)
          (* consecutive underscore shift *)
        | (( ( SP (P.Id _ | P.Paren _ | P.App _))  ::
          ST (T.PERIOD | T.COLON | T.RIGHTARROW | T.LCURLYBRACE | T.RCURLYBRACE | T.LPAREN | T.RPAREN 
                | T.LSQBRACKET | T.RSQBRACKET | T.EQUAL) :: _ ), T.UNDERSCORE) -> shift_or_reduce (SP (P.Id (P.Placeholder)) :: stack, tt)
        (* 2 --- shift colon ---*)
        | ((SP (P.Id _) :: _), T.COLON) -> shift_or_reduce ((ST T.COLON :: stack), tt)
        (* 3 --- shift rightarrow --- *)
        | (((SP (P.Id _ | P.Paren _ | P.App _)) :: (ST (T.COLON | T.RIGHTARROW | T.LPAREN | T.RCURLYBRACE) ) :: _)
            , (T.RIGHTARROW)) -> shift_or_reduce (ST th :: stack, tt)
        (* 4 --- shift left curly brace --- *)
        | ((ST (T.RIGHTARROW | T.COLON | T.LPAREN | T.RCURLYBRACE) ::  _), (T.LCURLYBRACE)) -> shift_or_reduce (ST th :: stack, tt)
        | (_, (T.LCURLYBRACE)) -> failwith ("unexpected { at " ^ show_ps ps)
        (* 5 --- shift left paren --- *)
        | (_, (T.LPAREN )) -> shift_or_reduce (ST th :: stack, tt)
        (* 6 --- shift left sqbracket --- *)
        | (_, ( T.LSQBRACKET)) -> shift_or_reduce (ST th :: stack, tt)
        (* 7 --- shift right sqbracket --- *)
        | ((SP (P.Id _ | P.App _) :: ST (T.COLON | T.LSQBRACKET) :: _), (T.RSQBRACKET)) -> shift_or_reduce (ST th :: stack, tt)
        (* 8 --- shift right curly brace --- *)
        | ((SP (P.Id _ | P.App _ | P.PiArr _ ) :: ST (T.COLON | T.LCURLYBRACE) :: _), (T.RCURLYBRACE)) -> shift_or_reduce (ST th :: stack, tt)
        (* 9 --- shift equal --- *)
        | ((SP (P.Id _ | P.App _ | P.Paren _ | P.PiNT _ | P.PiArr _ | P.PiT _ ) 
        :: ST (T.COLON | T.DOUBLECOLON ) :: _), (T.EQUAL)) -> shift_or_reduce (ST th :: stack, tt)
        | _ -> failwith ("Cannot shift/reduce " ^ show_ps ps)
    )

let rawparse (tkl : Token.tok list) : P.parseast = 
  match shift_or_reduce ([], tkl) with
    | ((ST T.PERIOD:: SP decl ::[]), [T.EOF]) -> decl
    | (stack, tkl) -> failwith ("expecting single declaration ending with period and eof , got " ^ [%derive.show: parse_state] (stack, tkl))
