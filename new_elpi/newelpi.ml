open Lprun

(*
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.minor_heap_size = 33554432; (** 4M *)
    Gc.space_overhead = 120;
  } in
  Gc.set tweaked_control
;;
*)

let test_prog prog query =
 List.iter
  (fun (msg,run,_) ->
    prerr_endline (msg query);
    if run prog query then
     prerr_endline "ERROR\n"
    else prerr_endline "success\n") implementations
;;

let run_prog prog query =
 let msg,_,main_loop = List.hd implementations in
 prerr_endline (msg query);
 main_loop prog query
;;

let _ =
  let argv = Sys.argv in
  (* j=1 iff -test is not passed *)
  let j = if argv.(1) = "-test" then 2 else 1 in
  let b = Buffer.create 1024 in
  for i=j to Array.length argv - 1 do
    Printf.eprintf "loading %s\n" argv.(i);
      let ic = open_in argv.(i) in
      try
        while true do Buffer.add_string b (input_line ic^"\n") done;
        assert false
      with End_of_file -> ()
  done;
  let p = Buffer.contents b in
  let p = Parser.parse_program p in
  let g =
   if j = 1 then (
    Printf.printf "goal> %!";
    input_line stdin)
   else "main." in
  let g = Parser.parse_goal g in
  if j=1 then run_prog p g else test_prog p g
;;
