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
 let i = ref 0 in
 List.iter
  (fun (msg,run,_) ->
    Gc.compact();
    incr i;
    prerr_endline ("Implementation #" ^ string_of_int !i);
    prerr_endline (msg query);
    if run prog query then
     prerr_endline "ERROR\n"
    else prerr_endline "success\n") implementations
;;

let run_prog impl prog query =
 let msg,_,main_loop = List.nth implementations (impl-1) in
 prerr_endline (msg query);
 main_loop prog query
;;

let _ =
  let argv = Sys.argv in
  (* j=1 iff -test is not passed *)
  let j,test,impl =
   if argv.(1) = "-test" then 2,true,0
   else if argv.(1) = "-impl" then 3,false,int_of_string (argv.(2))
   else 1,false,1 in
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
   if not test then (
    Printf.printf "goal> %!";
    input_line stdin)
   else "main." in
  let g = Parser.parse_goal g in
  if test then test_prog p g else run_prog impl p g
;;
