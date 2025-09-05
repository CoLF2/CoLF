
module P = Parseast
module A = Ast


let priority_counter = ref 10000
let nextPriority() : int = 
  let _ = priority_counter := !priority_counter - 1 in
   !priority_counter 

let elaborateId (p : P.parseast) : string = 
  match p with
  | P.Id(Str s) -> s
  | P.Id(Placeholder) -> failwith ("Place holder not supported")
  | _ -> failwith ("Cannot elaborate id " ^ P.debugshow p)


let rec elaborateTm ( p : P.parseast) : A.abt = 
  match p with
  | P.App _ -> let hs = (elaborateHeadSpine p) in A.N(A.At, hs)
  | P.Id _ -> A.FreeVar(elaborateId p)
  | P.LamT(_) -> failwith "does not support typed lambda abstraction, please remove types"
  (* | P.LamT(x, t2, m1) -> A.Lam(elaborateId x, elaborateTp t2, elaborateTm m1) *)
  | P.LamNT(x, m1) -> A.N(A.Lam, [A.abstract_over (elaborateId x) (elaborateTm m1)])
  | P.Paren(p) -> elaborateTm p
  | _ -> failwith ("Cannot elaborate tm at " ^ P.debugshow p)
and elaborateHeadSpine ( p : P.parseast) : A.abt list = 
    match p with
    | P.Id _ -> [A.FreeVar(elaborateId p)]
    | P.App(t1, m2) ->  (elaborateHeadSpine t1)@[elaborateTm m2]
    | _ -> failwith ("cannot elaborate headspine " ^ P.debugshow p)

and elaborateTp (p : P.parseast) : A.abt = 
  match p with
  | P.PiT(x, t2, t1) -> A.N(A.Pi, ([elaborateTp t2; (A.abstract_over (elaborateId x) (elaborateTp t1))] : A.abt list))
  (* | P.PiNT(x, t1) ->  failwith "not_supported_notype_abs" *)
    (* A.Pi(elaborateId x, A.Atp(A.Placeholder, []), elaborateTp t1) *)
  | P.PiArr(t2, t1) -> A.N(A.Pi, [elaborateTp t2; A.abstract_over_no_name (elaborateTp t1)])
  | P.Id(P.Str "type")-> A.N(A.Type, [])
  | P.Id(P.Str "cotype")-> A.N(A.CoType, [])
  | P.Id _ -> A.FreeVar(elaborateId p)
  | P.App _ -> let hs = (elaborateHeadSpine p) in A.N(A.At, hs)
  | P.Paren(p) -> elaborateTp p
  | _ -> failwith ("cannot elaborate type " ^ P.debugshow p)





let rec elaborateDec (current: A.ssig) (p : P.parseast) : A.ssig = 
(* let _ = print_string ("elaborating" ^ P.show_parseast p ^ "\n") in *)
  match p with
  | Dec2(d1, d2) -> let e1 = elaborateDec current d1 in  elaborateDec e1 d2 
  | Dec(c, a) -> {current with 
    decls = current.decls @ [(elaborateId c, elaborateTp a)]
  }
  | Command(c, m) -> { current with
    cmds = current.cmds @ [(c, elaborateTm m)]
  }
  (* | DecDefC(c, a, m) ->  failwith ("definitions not yet supported ") *)
    (* [A.Def(elaborateId c, elaborateTp a, elaborateTm m, A.Unchecked)] TODO: separate them is the step after next *)
  (* | DecDefI(c, a, m) ->  failwith ("definitions not yet supported") *)
    (* [A.Def(elaborateId c, elaborateTp a, elaborateTm m, A.Unchecked)] *)
  | _ -> failwith ("Cannot elaborate delcaration at ^ " ^ P.debugshow p)

let elaborateDecTopLevel  (p : P.parseast) : A.ssig = elaborateDec A.empty_ssig p
