PP=camlp5o -I . -I +camlp5
PPPARSE=$(PP) pa_extend.cmo pa_lexer.cmo
FLAGS=-I +camlp5
OCAMLOPTIONS= -g
# OCAMLOPTIONS= -g -p    then run the file and use gprof executable to produce the profilation
CMX=cmx
CMXA=cmxa
OC=ocamlopt
#CMX=cmo
#CMXA=cma
#OC=ocamlc

newelpi: newelpi.$(CMX) lprun2.$(CMX) lprun3.$(CMX) lprun4.$(CMX) patternunif.$(CMX) desperate2.$(CMX) desperate3.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) $(FLAGS) -o newelpi camlp5.$(CMXA) unix.$(CMXA) lprun2.$(CMX) lprun3.$(CMX) lprun4.$(CMX) patternunif.$(CMX) desperate2.$(CMX) desperate3.$(CMX) parser.$(CMX) newelpi.$(CMX)

newelpi.$(CMX): newelpi.ml lprun2.$(CMX) lprun3.$(CMX) lprun4.$(CMX) patternunif.$(CMX) desperate2.$(CMX) desperate3.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c newelpi.ml

lprun2.$(CMX) lprun2.cmi: lprun2.ml
	$(OC) $(OCAMLOPTIONS) -c lprun2.ml

patternunif.$(CMX) patternunif.cmi: patternunif.ml lprun2.cmi
	$(OC) $(OCAMLOPTIONS) -c patternunif.ml

desperate2.$(CMX) desperate2.cmi: desperate2.ml lprun2.cmi
	$(OC) $(OCAMLOPTIONS) -c desperate2.ml

desperate3.$(CMX) desperate3.cmi: desperate3.ml lprun3.cmi
	$(OC) $(OCAMLOPTIONS) -c desperate3.ml

lprun4.$(CMX) lprun4.cmi: lprun4.ml lprun3.cmi lprun2.cmi
	$(OC) $(OCAMLOPTIONS) -c lprun4.ml

lprun3.$(CMX) lprun3.cmi: lprun3.ml lprun2.cmi
	$(OC) $(OCAMLOPTIONS) -c lprun3.ml

parser.cmi: parser.mli lprun2.cmi
	$(OC) $(OCAMLOPTIONS) -c parser.mli

parser.$(CMX): parser.ml parser.cmi lprun2.$(CMX)
	$(OC) $(OCAMLOPTIONS) -pp '$(PPPARSE)' $(FLAGS) -o $@ -c $<
