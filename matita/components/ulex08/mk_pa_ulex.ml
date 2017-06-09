let s = float_of_string (String.sub (Sys.ocaml_version) 0 4) in
  print_endline "Old camlp4 (loc)";
  Sys.command "sed s/_loc/loc/ < pa_ulex.ml.src > pa_ulex.ml"

