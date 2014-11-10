all: lib.thc copy.thc cic.thc metacic.thc

metacic.thc: metacic.thm cic.thc lib.thc copy.thc
	./abella metacic.thm -c metacic.thc -o metacic.out

cic.thc: cic.thm lib.thc copy.thc
	./abella cic.thm -c cic.thc -o cic.out

lib.thc: lib.thm
	./abella lib.thm -c lib.thc -o lib.out

copy.thc: copy.thm lib.thc
	./abella copy.thm -c copy.thc -o copy.out
