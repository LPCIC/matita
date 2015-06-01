let implementations = Lprun2.implementations @ Lprun3.implementations @ Lprun4.implementations @ [ Desperate2.impl ] @ [ Desperate3.impl ] @ [ Patternunif.impl ] @ [ Patternunif2.impl ] @ [ Ct.impl ] @ [ Patternunif3.impl ]

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
  (fun (module Impl : Parser.Implementation) ->
    let query = Impl.query_of_ast query in
    let prog = Impl.program_of_ast prog in
    Gc.compact();
    incr i;
    prerr_endline ("Implementation #" ^ string_of_int !i);
    prerr_endline (Impl.msg query);
    if Impl.execute_once prog query then
     prerr_endline "ERROR\n"
    else prerr_endline "success\n") implementations
;;

let run_prog impl prog query =
 let (module Impl : Parser.Implementation) =
  List.nth implementations (impl-1) in
 let query = Impl.query_of_ast query in
 let prog = Impl.program_of_ast prog in
 prerr_endline (Impl.msg query);
 Impl.execute_loop prog query
;;

let test_impl impl prog query =
 let (module Impl : Parser.Implementation) =
  List.nth implementations (impl-1) in
 let query = Impl.query_of_ast query in
 let prog = Impl.program_of_ast prog in
 let time f p q =
   let t0 = Unix.gettimeofday () in
   let b = f p q in
   let t1 = Unix.gettimeofday () in
   Printf.printf "INTERNAL TIMING %5.3f\n%!" (t1 -. t0);
   b in
 if time Impl.execute_once prog query then exit 1 else exit 0
;;


let print_implementations () =
 List.iteri (
  fun i (module Impl : Parser.Implementation) ->
   prerr_string ("Implementation #" ^ string_of_int (i+1) ^ ": ");
   prerr_endline (Impl.msg (Impl.query_of_ast (Parser.Const Parser.ASTFuncS.truef))) ;
 ) implementations
;;

(* rewrites a lambda-prolog program to first-order prolog *)
let pp_lambda_to_prolog impl prog =
 let (module Impl : Parser.Implementation) =
  List.nth implementations (impl - 1) in
 Printf.printf "\nRewriting λ-prolog to first-order prolog...\n\n%!";
 Impl.pp_prolog prog
;;

let set_terminal_width ?(max_w=
    let ic, _ as p = Unix.open_process "tput cols" in
    let w = int_of_string (input_line ic) in
    let _ = Unix.close_process p in w) () =
  Format.pp_set_margin Format.err_formatter max_w;
  Format.pp_set_ellipsis_text Format.err_formatter "...";
  Format.pp_set_max_boxes Format.err_formatter 30;
;;

let _ =
  let argv = Sys.argv in
  let argn = Array.length argv in
  (* j=1 iff -test is not passed *)
  let j,test =
   if argv.(1) = "-test" then
     if argn = 4 then 3,`OneBatch (int_of_string (argv.(2)))
     else 2,`AllBatch
   else if argv.(1) = "-prolog" then 3,`PPprologBatch (int_of_string (argv.(2)))
   else if argv.(1) = "-impl" then 3,`OneInteractive (int_of_string (argv.(2)))
   else if argv.(1) = "-list" then
    (print_implementations (); exit 0)
   else 1,`OneInteractive 1 in
  let b = Buffer.create 1024 in
  for i=j to argn - 1 do
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
    match test with
    | `AllBatch | `OneBatch _ | `PPprologBatch _ -> "main."
    | _ ->
    Printf.printf "goal> %!";
    input_line stdin in
  let g = Parser.parse_goal g in
  set_terminal_width ();
  match test with
  | `AllBatch -> test_prog p g
  | `OneBatch impl -> test_impl impl p g
  | `OneInteractive impl -> run_prog impl p g
  | `PPprologBatch impl -> pp_lambda_to_prolog impl p  
;;
