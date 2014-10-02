let () =
  let x = [1;2;3;4;5;6;7;8;9;10] in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let x = x @ x in
  let y = List.rev x in
  let z = List.rev y in
  assert(x = z)
;;
