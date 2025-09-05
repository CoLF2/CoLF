
(* https://stackoverflow.com/questions/13410159/how-to-read-one-character-at-a-time-from-user-input-at-each-keystroke-without *)
let get1char () =
  let termio = Unix.tcgetattr Unix.stdin in
  let () =
      Unix.tcsetattr Unix.stdin Unix.TCSADRAIN
          { termio with Unix.c_icanon = false } in
  let res = input_char stdin in
  Unix.tcsetattr Unix.stdin Unix.TCSADRAIN termio;
  res
