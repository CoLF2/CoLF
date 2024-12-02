
module type EXTENT = sig
  type t = string * (int * int) * (int * int)
  val combine_extent : t -> t -> t
  val show_extent : t -> string
end
module Extent : EXTENT = struct
  type t = string * (int * int) * (int * int)
  type t_extent = t


  let combine_extent (s1 : t_extent) (s2 : t_extent) : t_extent = 
    let (file1, (row1, col1), (_row1', _col1')) = s1 in
    let (_file2, (_row2, _col2), (row2', col2')) = s2 in
    (file1, (row1, col1), (row2', col2'))
  
  let show_extent (s : t_extent) : string = 
    let (file, (row1, col1), (row2, col2)) = s in
    Printf.sprintf "%s:%d:%d-%d:%d" file row1 col1 row2 col2
end