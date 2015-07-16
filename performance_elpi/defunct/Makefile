PP=camlp5o -I . -I +camlp5
PPPARSE=$(PP) pa_extend.cmo pa_lexer.cmo
FLAGS=-I +camlp5
OCAMLOPTIONS= -g
# OCAMLOPTIONS= -g -p    then run the file and use gprof executable to produce the profilation

newelpi: newelpi.cmx lprun2.cmx lprun.cmx parser.cmx
	ocamlopt $(OCAMLOPTIONS) $(FLAGS) -o newelpi camlp5.cmxa unix.cmxa lprun2.cmx lprun.cmx parser.cmx newelpi.cmx

newelpi.cmx: newelpi.ml lprun2.cmx lprun.cmx parser.cmx
	ocamlopt $(OCAMLOPTIONS) -c newelpi.ml

lprun2.cmx lprun2.cmi: lprun2.ml
	ocamlopt $(OCAMLOPTIONS) -c lprun2.ml

lprun.cmx lprun.cmi: lprun.ml lprun2.cmi
	ocamlopt $(OCAMLOPTIONS) -c lprun.ml

parser.cmi: parser.mli lprun2.cmi
	ocamlopt $(OCAMLOPTIONS) -c parser.mli

parser.cmx: parser.ml parser.cmi lprun2.cmx
	ocamlopt $(OCAMLOPTIONS) -pp '$(PPPARSE)' $(FLAGS) -o $@ -c $<
