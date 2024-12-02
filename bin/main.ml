open Lftest08

let _ = Printexc.record_backtrace true

let args = Sys.argv

let _ = if Array.length args <= 1
  then print_endline "Expect filename"
else (Start.entry (List.tl (Array.to_list args)));;
