module A = CoLFAbt.CoLFAbt
module Extent = Extent.Extent
  

module type ERRORS = sig
  val raise_error : A.t -> string -> 'a
  val raise_with_explicit_extent : Extent.t option -> string -> 'a
  (* if the first argument raises an error, update error location if none is available, append error message with a new line *)
  val try_with_error : (unit -> 'a) -> A.t option -> string -> 'a 
  exception CoLFError of Extent.t option * string
end

module Errors : ERRORS = struct
  exception CoLFError of Extent.t option * string

  let raise_error (tm : A.t) (msg : string) : 'a = 
    raise (CoLFError (A.get_extent tm, msg))

  let raise_with_explicit_extent (ext : Extent.t option) (msg : string) : 'a = 
    raise (CoLFError (ext, msg))

  let try_with_error (f : unit -> 'a) (tm_opt : A.t option) (msg : string) : 'a =
    try f ()
    with CoLFError (ext, s) -> 
      (let new_msg = s ^ "\n" ^ msg in
        match ext, tm_opt with 
        None, Some tm -> Printexc.raise_with_backtrace (CoLFError (A.get_extent tm, new_msg)) (Printexc.get_raw_backtrace ())
        | _ -> Printexc.raise_with_backtrace (CoLFError (ext, new_msg)) (Printexc.get_raw_backtrace ())
      )

end
