all:
	pdflatex lpar2015
	bibtex lpar2015
	pdflatex lpar2015
	pdflatex lpar2015

zip: all
	zip lpar2015.zip \
		lpar2015.bbl \
		lpar2015.blg \
		lpar2015.tex \
		multirow.sty \
		llncs.cls \
		helena.tex \
		reference.bib

