PP=camlp5o -I . -I +camlp5
PPPARSE=$(PP) pa_extend.cmo pa_lexer.cmo
FLAGS=-I +camlp5

newelpi: newelpi.cmx parser.cmx
	ocamlopt $(FLAGS) -o newelpi camlp5.cmxa unix.cmxa parser.cmx newelpi.cmx

newelpi.cmx: newelpi.ml parser.cmx parser.cmi
	ocamlopt -c newelpi.ml

parser.cmi: parser.mli
	ocamlopt -c parser.mli

parser.cmx: parser.ml parser.cmi
	ocamlopt -pp '$(PPPARSE)' $(FLAGS) -o $@ -c $<
