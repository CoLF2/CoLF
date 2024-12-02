module A = CoLFAbt.CoLFAbt
module N = CoLFAbt.CoLFNode

module type PRETTY_PRINT = sig
  val show_term : A.t -> string
  val show_terms : A.t list -> string
end

module PrettyPrint : PRETTY_PRINT = struct

  let rec show_term (tm : A.t) : string = 
    match A.view tm with
    | A.FreeVar s -> s
    | A.N(N.Type, []) -> "type"
    | A.N(N.CoType, []) -> "cotype"
    | A.N(N.Ap, hd::spine) -> 
      let hd_str = show_term  (snd hd) in
      let spine_str = String.concat " " (List.map (fun x -> x |> snd |> show_term) spine) in
      "(" ^ hd_str ^ " " ^ spine_str ^ ")"
    | A.N(N.Lam, [([bnd], body)]) ->
      "([" ^ bnd ^ "] " ^ show_term body ^ ")"
    | A.N(N.Pi, [([], tp); ([bnd], body)]) ->
      (* print_endline ("show_term: Pi: " ^ A.show_raw tm); *)
      if A.appears_in_expr bnd body
        then "{" ^ bnd ^ " : " ^ show_term tp ^ "} " ^ show_term body
        else show_term tp ^ " -> " ^ show_term body
    | _ -> A.show_view tm


  let show_terms (tms : A.t list) : string =
    "[" ^ String.concat "; " (List.map show_term tms) ^ "]"
end

