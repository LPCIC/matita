PP=camlp5o -I . -I +camlp5
PPPARSE=$(PP) pa_extend.cmo pa_lexer.cmo
FLAGS=-I +camlp5

newelpi: newelpi.cmx lprun.cmx parser.cmx
	ocamlopt $(FLAGS) -o newelpi camlp5.cmxa unix.cmxa lprun.cmx parser.cmx newelpi.cmx

newelpi.cmx: newelpi.ml lprun.cmx parser.cmx
	ocamlopt -c newelpi.ml

lprun.cmx lprun.cmi: lprun.ml
	ocamlopt -c lprun.ml

parser.cmi: parser.mli lprun.cmi
	ocamlopt -c parser.mli

parser.cmx: parser.ml parser.cmi lprun.cmx
	ocamlopt -pp '$(PPPARSE)' $(FLAGS) -o $@ -c $<
