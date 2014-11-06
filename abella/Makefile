all: lib.thc copy.thc cic.thc

cic.thc: cic.thm
	./abella cic.thm -c cic.thc -o cic.out

lib.thc: lib.thm
	./abella lib.thm -c lib.thc -o lib.out

copy.thc: copy.thm
	./abella copy.thm -c copy.thc -o copy.out
