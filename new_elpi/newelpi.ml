open Lprun

let run_prog prog query =
 let module FOAtomImplApprox = ApproximatableFOAtom(Variable)(FuncS)(Bindings(Variable)(FuncS)) in
 let module FOProgramApprox = ProgramIndexL(FOAtomImplApprox) in
 let module RunFOApprox = Run(FOAtomImplApprox)(FOProgramApprox) in
 prerr_endline ("Testing with two level inefficient index " ^ FOFormulae.pp query);
 let loadedprog = FOProgramApprox.make (Obj.magic prog) in
 RunFOApprox.main_loop loadedprog (Obj.magic query)

let _ =
  let argv = Sys.argv in
  let b = Buffer.create 1024 in
  for i=1 to Array.length argv - 1 do
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
    Printf.printf "goal> %!";
    input_line stdin in
  let g = Parser.parse_goal g in
  run_prog p g
;;
