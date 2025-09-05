
type pid = Str of string | Placeholder [@@deriving show]

type parseast =   
  Dec2 of parseast * parseast  (* DECL -> DECL . DEC | DEC *)
  | Dec of parseast * parseast (* DEC -> TM : TM *)
  | DecDefI of parseast * parseast * parseast(* DEC -> TM : TM = TM *)
  | DecDefC of parseast * parseast * parseast(* DEC -> TM :: TM = TM *)
  | PiT of parseast * parseast * parseast (* T -> { T : T } T*)
  | PiNT of parseast * parseast (* T -> { T } T*)
  | PiArr of parseast * parseast (* T -> T -> T*)
  | LamT of parseast * parseast * parseast (* T -> [ T : T ] T*)
  | LamNT of parseast * parseast (* T -> [ T ] T*)
  | Paren of parseast
  | App of parseast * parseast (* T -> T T *)
  | Id of pid
  | Command of string * parseast (* T -> %cmd T *)
  [@@deriving show]


let rec debugshow (past : parseast) : string = 
  let ds = debugshow in
    match past with
    | Dec2(d1, d2) -> ds d1 ^ ".\n" ^ ds d2
    | Dec(c, a) -> ds c ^ " : " ^ ds a
    | DecDefI(c,t,m) -> ds c ^ " : " ^ ds t ^ " = " ^ ds m
    | DecDefC(c,t,m) -> ds c ^ " :: " ^ ds t ^ " = " ^ ds m
    | PiT(x,t2,t1) -> " { " ^ ds x ^ " : " ^ ds t2 ^ " } " ^ ds t1
    | PiNT(x,t1) -> "{" ^ ds x ^ "} " ^ ds t1
    | PiArr(t2,t1) -> ds t2 ^ " -> " ^ ds t1
    | LamT(x,t2,t1) -> " [ " ^ ds x ^ " : " ^ ds t2 ^ " ] " ^ ds t1
    | LamNT(x,t1) -> "[" ^ ds x ^ "] " ^ ds t1
    | Paren(t) -> "(" ^ ds t ^ ")"
    | App(t1, t2) -> ds t1 ^  " " ^ds t2
    | Id(Str s) -> s
    | Id(Placeholder) -> "_"
    | Command(s, t) -> "%" ^ s ^ " " ^ ds t
