H=@

PP=camlp5o -I . -I +camlp5
PPPARSE=$(PP) pa_extend.cmo pa_lexer.cmo
FLAGS=-I +camlp5
OCAMLOPTIONS= -g
#OCAMLOPTIONS= -g -p #  then run the file and use gprof
#OCAMLOPTIONS= -g # for byte 
CMX=cmx
CMXA=cmxa
#OC=ocamloptp
OC=ocamlopt
OCP=ocamlopt
#CMX=cmo
#CMXA=cma
#OC=ocamlcp
#OCP=ocamlc

newelpi: newelpi.$(CMX) lprun2.$(CMX) lprun3.$(CMX) lprun4.$(CMX) ct.$(CMX) patternunif.$(CMX) patternunif2.$(CMX) patternunif3.$(CMX) patternunif4.$(CMX) desperate2.$(CMX) desperate3.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) $(FLAGS) -o newelpi camlp5.$(CMXA) unix.$(CMXA) parser.$(CMX) lprun2.$(CMX) lprun3.$(CMX) lprun4.$(CMX) ct.$(CMX) patternunif.$(CMX) patternunif2.$(CMX) patternunif3.$(CMX) ptmap.$(CMX) patternunif4.$(CMX) desperate2.$(CMX) desperate3.$(CMX) newelpi.$(CMX)

newelpi.$(CMX): newelpi.ml lprun2.$(CMX) lprun3.$(CMX) lprun4.$(CMX) ct.$(CMX) patternunif.$(CMX) patternunif2.$(CMX) patternunif3.$(CMX) ptmap.$(CMX) patternunif4.$(CMX) desperate2.$(CMX) desperate3.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c newelpi.ml

lprun2.$(CMX) lprun2.cmi: lprun2.ml parser.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c lprun2.ml

patternunif.$(CMX) patternunif.cmi: patternunif.ml parser.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c patternunif.ml

patternunif4.$(CMX) patternunif4.cmi: patternunif4.ml parser.cmi parser.$(CMX) ptmap.cmi ptmap.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c patternunif4.ml

patternunif3.$(CMX) patternunif3.cmi: patternunif3.ml parser.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c patternunif3.ml

patternunif2.$(CMX) patternunif2.cmi: patternunif2.ml parser.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c patternunif2.ml

ct.$(CMX) ct.cmi: ct.ml parser.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c ct.ml

desperate2.$(CMX) desperate2.cmi: desperate2.ml parser.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c desperate2.ml

desperate3.$(CMX) desperate3.cmi: desperate3.ml lprun3.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c desperate3.ml

lprun4.$(CMX) lprun4.cmi: lprun4.ml lprun3.cmi parser.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c lprun4.ml

lprun3.$(CMX) lprun3.cmi: lprun3.ml parser.cmi parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c lprun3.ml

ptmap.cmi: ptmap.mli
	$(OC) $(OCAMLOPTIONS) -c ptmap.mli

ptmap.$(CMX): ptmap.ml ptmap.cmi
	$(OC) $(OCAMLOPTIONS) -c ptmap.ml

parser.cmi: parser.mli
	$(OC) $(OCAMLOPTIONS) -c parser.mli

parser.$(CMX): parser.ml parser.cmi 
	$(OCP) $(OCAMLOPTIONS) -pp '$(PPPARSE)' $(FLAGS) -o $@ -c $<

clean:
	rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o

test:	newelpi
	./newelpi -impl 19 tests/queens.elpi

profile-grundlagen: TIME = time -p -o ../../grundlagen.time -a

profile-grundlagen: ELPI = ../../newelpi -impl 22 grundlagen.elpi

profile-grundlagen: EXEC = >> ../../grundlagen.txt 2>&1

profile-grundlagen: newelpi
	$(H)$(RM) grundlagen.time grundlagen.txt
	$(H)cd bench/sources && for TMP in `seq 31`; do echo main. | $(TIME) $(ELPI) $(EXEC); done

.PHONY: test clean profile-grundlagen
